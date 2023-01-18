#include "eager_search.h"

#include "../evaluation_context.h"
#include "../evaluator.h"
#include "../open_list_factory.h"
#include "../option_parser.h"
#include "../pruning_method.h"

#include "../algorithms/ordered_set.h"
#include "../task_utils/successor_generator.h"

#include "../utils/logging.h"

#include "../unsolvability/unsolvabilitymanager.h"

#include <cassert>
#include <cstdlib>
#include <memory>
#include <optional.hh>
#include <set>
#include <map>

using namespace std;

namespace eager_search
{
    EagerSearch::EagerSearch(const Options &opts)
        : SearchEngine(opts),
          reopen_closed_nodes(opts.get<bool>("reopen_closed")),
          unsolv_type(opts.get<UnsolvabilityVerificationType>("unsolv_verification")),
          open_list(opts.get<shared_ptr<OpenListFactory>>("open")->create_state_open_list()),
          f_evaluator(opts.get<shared_ptr<Evaluator>>("f_eval", nullptr)),
          preferred_operator_evaluators(opts.get_list<shared_ptr<Evaluator>>("preferred")),
          lazy_evaluator(opts.get<shared_ptr<Evaluator>>("lazy_evaluator", nullptr)),
          pruning_method(opts.get<shared_ptr<PruningMethod>>("pruning")),
          unsolvability_directory(opts.get<std::string>("unsolv_directory"))
    {
        if (lazy_evaluator && !lazy_evaluator->does_cache_estimates())
        {
            cerr << "lazy_evaluator must cache its estimates" << endl;
            utils::exit_with(utils::ExitCode::SEARCH_INPUT_ERROR);
        }

        if (unsolv_type != UnsolvabilityVerificationType::NONE)
        {
            if (unsolvability_directory.compare(".") == 0)
            {
                unsolvability_directory = "";
            }
            // expand environment variables
            size_t found = unsolvability_directory.find('$');
            while (found != std::string::npos)
            {
                size_t end = unsolvability_directory.find('/');
                std::string envvar;
                if (end == std::string::npos)
                {
                    envvar = unsolvability_directory.substr(found + 1);
                }
                else
                {
                    envvar = unsolvability_directory.substr(found + 1, end - found - 1);
                }
                // to upper case
                for (size_t i = 0; i < envvar.size(); i++)
                {
                    envvar.at(i) = toupper(envvar.at(i));
                }
                std::string expanded = std::getenv(envvar.c_str());
                unsolvability_directory.replace(found, envvar.length() + 1, expanded);
                found = unsolvability_directory.find('$');
            }
            if (!unsolvability_directory.empty() && !(unsolvability_directory.back() == '/'))
            {
                unsolvability_directory += "/";
            }
            std::cout << "Generating unsolvability verification in "
                      << unsolvability_directory << std::endl;
            if (unsolv_type == UnsolvabilityVerificationType::PROOF_DISCARD)
            {
                CuddManager::set_compact_proof(false);
            }
            else if (unsolv_type == UnsolvabilityVerificationType::PROOF || unsolv_type == UnsolvabilityVerificationType::DIMACS)
            {
                CuddManager::set_compact_proof(true);
            }
        }
    }

    void EagerSearch::initialize()
    {
        utils::g_log << "Conducting best first search"
                     << (reopen_closed_nodes ? " with" : " without")
                     << " reopening closed nodes, (real) bound = " << bound
                     << endl;
        assert(open_list);

        set<Evaluator *> evals;
        open_list->get_path_dependent_evaluators(evals);

        /*
          Collect path-dependent evaluators that are used for preferred operators
          (in case they are not also used in the open list).
        */
        for (const shared_ptr<Evaluator> &evaluator : preferred_operator_evaluators)
        {
            evaluator->get_path_dependent_evaluators(evals);
        }

        /*
          Collect path-dependent evaluators that are used in the f_evaluator.
          They are usually also used in the open list and will hence already be
          included, but we want to be sure.
        */
        if (f_evaluator)
        {
            f_evaluator->get_path_dependent_evaluators(evals);
        }

        /*
          Collect path-dependent evaluators that are used in the lazy_evaluator
          (in case they are not already included).
        */
        if (lazy_evaluator)
        {
            lazy_evaluator->get_path_dependent_evaluators(evals);
        }

        path_dependent_evaluators.assign(evals.begin(), evals.end());

        State initial_state = state_registry.get_initial_state();
        for (Evaluator *evaluator : path_dependent_evaluators)
        {
            evaluator->notify_initial_state(initial_state);
        }

        /*
          Note: we consider the initial state as reached by a preferred
          operator.
        */
        EvaluationContext eval_context(initial_state, 0, true, &statistics);

        statistics.inc_evaluated_states();

        if (open_list->is_dead_end(eval_context))
        {
            if (unsolv_type == UnsolvabilityVerificationType::PROOF ||
                unsolv_type == UnsolvabilityVerificationType::PROOF_DISCARD ||
                unsolv_type == UnsolvabilityVerificationType::DIMACS)
            {
                open_list->store_deadend_info(eval_context);
            }
            utils::g_log << "Initial state is a dead end." << endl;
        }
        else
        {
            if (search_progress.check_progress(eval_context))
                statistics.print_checkpoint_line(0);
            start_f_value_statistics(eval_context);
            SearchNode node = search_space.get_node(initial_state);
            node.open_initial();

            open_list->insert(eval_context, initial_state.get_id());
        }

        print_initial_evaluator_values(eval_context);

        pruning_method->initialize(task);
    }

    void EagerSearch::print_statistics() const
    {
        statistics.print_detailed_statistics();
        search_space.print_statistics();
        pruning_method->print_statistics();
    }

    SearchStatus EagerSearch::step()
    {
        tl::optional<SearchNode> node;
        while (true)
        {
            if (open_list->empty())
            {
                if (unsolv_type == UnsolvabilityVerificationType::PROOF ||
                    unsolv_type == UnsolvabilityVerificationType::PROOF_DISCARD ||
                    unsolv_type == UnsolvabilityVerificationType::DIMACS)
                {
                    write_unsolvability_proof();
                }
                utils::g_log << "Completely explored state space -- no solution!" << endl;
                return FAILED;
            }
            StateID id = open_list->remove_min();
            State s = state_registry.lookup_state(id);
            node.emplace(search_space.get_node(s));

            if (node->is_closed())
                continue;

            /*
              We can pass calculate_preferred=false here since preferred
              operators are computed when the state is expanded.
            */
            EvaluationContext eval_context(s, node->get_g(), false, &statistics);

            if (lazy_evaluator)
            {
                /*
                  With lazy evaluators (and only with these) we can have dead nodes
                  in the open list.

                  For example, consider a state s that is reached twice before it is expanded.
                  The first time we insert it into the open list, we compute a finite
                  heuristic value. The second time we insert it, the cached value is reused.

                  During first expansion, the heuristic value is recomputed and might become
                  infinite, for example because the reevaluation uses a stronger heuristic or
                  because the heuristic is path-dependent and we have accumulated more
                  information in the meantime. Then upon second expansion we have a dead-end
                  node which we must ignore.
                */
                if (node->is_dead_end())
                    continue;

                if (lazy_evaluator->is_estimate_cached(s))
                {
                    int old_h = lazy_evaluator->get_cached_estimate(s);
                    int new_h = eval_context.get_evaluator_value_or_infinity(lazy_evaluator.get());
                    if (open_list->is_dead_end(eval_context))
                    {
                        std::cout << "dead end by lazy_eval" << std::endl;
                        node->mark_as_dead_end();
                        statistics.inc_dead_ends();
                        continue;
                    }
                    if (new_h != old_h)
                    {
                        open_list->insert(eval_context, id);
                        continue;
                    }
                }
            }

            node->close();
            assert(!node->is_dead_end());
            update_f_value_statistics(eval_context);
            statistics.inc_expanded();
            break;
        }

        const State &s = node->get_state();
        if (check_goal_and_set_plan(s))
            return SOLVED;

        vector<OperatorID> applicable_ops;
        successor_generator.generate_applicable_ops(s, applicable_ops);

        /*
          TODO: When preferred operators are in use, a preferred operator will be
          considered by the preferred operator queues even when it is pruned.
        */
        pruning_method->prune_operators(s, applicable_ops);

        // This evaluates the expanded state (again) to get preferred ops
        EvaluationContext eval_context(s, node->get_g(), false, &statistics, true);
        ordered_set::OrderedSet<OperatorID> preferred_operators;
        for (const shared_ptr<Evaluator> &preferred_operator_evaluator : preferred_operator_evaluators)
        {
            collect_preferred_operators(eval_context,
                                        preferred_operator_evaluator.get(),
                                        preferred_operators);
        }

        for (OperatorID op_id : applicable_ops)
        {
            OperatorProxy op = task_proxy.get_operators()[op_id];
            if ((node->get_real_g() + op.get_cost()) >= bound)
                continue;

            State succ_state = state_registry.get_successor_state(s, op);
            statistics.inc_generated();
            bool is_preferred = preferred_operators.contains(op_id);

            SearchNode succ_node = search_space.get_node(succ_state);

            for (Evaluator *evaluator : path_dependent_evaluators)
            {
                evaluator->notify_state_transition(s, op_id, succ_state);
            }

            // Previously encountered dead end. Don't re-evaluate.
            if (succ_node.is_dead_end())
                continue;

            if (succ_node.is_new())
            {
                // We have not seen this state before.
                // Evaluate and create a new node.

                // Careful: succ_node.get_g() is not available here yet,
                // hence the stupid computation of succ_g.
                // TODO: Make this less fragile.
                int succ_g = node->get_g() + get_adjusted_cost(op);

                EvaluationContext succ_eval_context(
                    succ_state, succ_g, is_preferred, &statistics);
                statistics.inc_evaluated_states();

                if (open_list->is_dead_end(succ_eval_context))
                {
                    if (unsolv_type == UnsolvabilityVerificationType::PROOF ||
                        unsolv_type == UnsolvabilityVerificationType::PROOF_DISCARD ||
                        unsolv_type == UnsolvabilityVerificationType::DIMACS)
                    {
                        open_list->store_deadend_info(succ_eval_context);
                    }
                    succ_node.mark_as_dead_end();
                    statistics.inc_dead_ends();
                    continue;
                }
                succ_node.open(*node, op, get_adjusted_cost(op));

                open_list->insert(succ_eval_context, succ_state.get_id());
                if (search_progress.check_progress(succ_eval_context))
                {
                    statistics.print_checkpoint_line(succ_node.get_g());
                    reward_progress();
                }
            }
            else if (succ_node.get_g() > node->get_g() + get_adjusted_cost(op))
            {
                // We found a new cheapest path to an open or closed state.
                if (reopen_closed_nodes)
                {
                    if (succ_node.is_closed())
                    {
                        /*
                          TODO: It would be nice if we had a way to test
                          that reopening is expected behaviour, i.e., exit
                          with an error when this is something where
                          reopening should not occur (e.g. A* with a
                          consistent heuristic).
                        */
                        statistics.inc_reopened();
                    }
                    succ_node.reopen(*node, op, get_adjusted_cost(op));

                    EvaluationContext succ_eval_context(
                        succ_state, succ_node.get_g(), is_preferred, &statistics);

                    /*
                      Note: our old code used to retrieve the h value from
                      the search node here. Our new code recomputes it as
                      necessary, thus avoiding the incredible ugliness of
                      the old "set_evaluator_value" approach, which also
                      did not generalize properly to settings with more
                      than one evaluator.

                      Reopening should not happen all that frequently, so
                      the performance impact of this is hopefully not that
                      large. In the medium term, we want the evaluators to
                      remember evaluator values for states themselves if
                      desired by the user, so that such recomputations
                      will just involve a look-up by the Evaluator object
                      rather than a recomputation of the evaluator value
                      from scratch.
                    */
                    open_list->insert(succ_eval_context, succ_state.get_id());
                }
                else
                {
                    // If we do not reopen closed nodes, we just update the parent pointers.
                    // Note that this could cause an incompatibility between
                    // the g-value and the actual path that is traced back.
                    succ_node.update_parent(*node, op, get_adjusted_cost(op));
                }
            }
        }

        return IN_PROGRESS;
    }

    void EagerSearch::reward_progress()
    {
        // Boost the "preferred operator" open lists somewhat whenever
        // one of the heuristics finds a state with a new best h value.
        open_list->boost_preferred();
    }

    void EagerSearch::dump_search_space() const
    {
        search_space.dump(task_proxy);
    }

    void EagerSearch::start_f_value_statistics(EvaluationContext &eval_context)
    {
        if (f_evaluator)
        {
            int f_value = eval_context.get_evaluator_value(f_evaluator.get());
            statistics.report_f_value_progress(f_value);
        }
    }

    /* TODO: HACK! This is very inefficient for simply looking up an h value.
       Also, if h values are not saved it would recompute h for each and every state. */
    void EagerSearch::update_f_value_statistics(EvaluationContext &eval_context)
    {
        if (f_evaluator)
        {
            int f_value = eval_context.get_evaluator_value(f_evaluator.get());
            statistics.report_f_value_progress(f_value);
        }
    }

    void add_options_to_parser(OptionParser &parser)
    {
        SearchEngine::add_pruning_option(parser);
        SearchEngine::add_options_to_parser(parser);
    }

    std::map<StateID, std::vector<int>> EagerSearch::write_formula(std::ofstream &certificate,
                                                                   std::string formula_name,
                                                                   std::vector<int> varorder,
                                                                   std::vector<std::vector<int>> fact_to_var,
                                                                   int offset, std::string inner_separator,
                                                                   std::string outer_separator,
                                                                   std::string primary_sign,
                                                                   std::string secondary_sign,
                                                                   std::map<StateID, std::vector<int>> reachable_facts /*= std::map<StateID, std::vector<int>>()*/)
    {
        bool first;
        size_t state_counter = 0;
        bool get_reachable_facts = reachable_facts.empty();
        for (StateID id : state_registry)
        {
            certificate << formula_name + to_string(state_counter) + ":=";
            certificate << "(";
            State state = state_registry.lookup_state(id);
            EvaluationContext eval_context(state,
                                           0,
                                           false, &statistics);
            state.unpack();
            std::vector<int> vals = state.get_unpacked_values();
            first = true;
            // this part handles dead-ends in hmax()
            if (search_space.get_node(state).is_dead_end() && eval_context.is_evaluator_value_infinite(f_evaluator.get()))
            {
                if (get_reachable_facts)
                {
                    reachable_facts[id] = open_list->get_reachable_facts_open_list(eval_context, state);
                }
                for (size_t i = 0; i < reachable_facts[id].size(); i++)
                {
                    if (reachable_facts[id][i] == 0)
                    {
                        if (!first)
                        {
                            certificate << inner_separator;
                        }
                        certificate << primary_sign + "v" << to_string(i + 1 + offset);
                        first = false;
                    }
                }
            }
            // this part handles regular states
            else
            {
                for (size_t i = 0; i < varorder.size(); ++i)
                {
                    // variables start at 1 for dimacs format
                    int var = varorder[i];
                    for (int j = 0; j < task_proxy.get_variables()[var].get_domain_size(); ++j)
                    {
                        if (vals[i] == j)
                        {
                            certificate << secondary_sign + "v" + to_string((fact_to_var[var][j] + 1 + offset));
                        }
                        else
                        {
                            certificate << primary_sign + "v" + to_string(fact_to_var[var][j] + 1 + offset);
                        }
                        if (j != task_proxy.get_variables()[var].get_domain_size() - 1)
                        {
                            certificate << inner_separator;
                        }
                    }
                    if (i != varorder.size() - 1)
                    {
                        certificate << inner_separator;
                    }
                }
            }
            certificate << ");\n";
            state_counter++;
        }
        certificate << formula_name + ":=(";
        for (size_t i = 0; i < state_counter; i++)
        {
            certificate << formula_name + to_string(i);
            if (i != state_counter - 1)
            {
                certificate << outer_separator;
            }
        }
        certificate << ");\n";
        return reachable_facts;
    }

    std::map<StateID, std::vector<int>> EagerSearch::write_formula_dimacs(std::ofstream &certificate,
                                                                          std::string formula_name,
                                                                          std::vector<int> varorder,
                                                                          std::vector<std::vector<int>> fact_to_var,
                                                                          int offset, std::string inner_separator,
                                                                          std::string outer_separator,
                                                                          std::string primary_sign,
                                                                          std::string secondary_sign,
                                                                          int fact_amount,
                                                                          std::map<StateID, std::vector<int>> reachable_facts /*= std::map<StateID, std::vector<int>>()*/)
    {
        size_t state_counter = 0;
        bool get_reachable_facts = reachable_facts.empty();
        vector<int> facts = vector<int>(fact_amount, 0);
        // setup variables for state-formulas
        int num_states = state_registry.size();
        vector<int> state_formulas = vector<int>(num_states, 0);
        int base = 2 * fact_amount + 1;
        if (offset != 0)
        {
            base = base + num_states;
        }

        for (size_t i = 0; i < num_states; i++)
        {
            state_formulas[i] = i + base;
        }

        for (StateID id : state_registry)
        {
            State state = state_registry.lookup_state(id);
            EvaluationContext eval_context(state,
                                           0,
                                           false, &statistics);
            state.unpack();
            std::vector<int> vals = state.get_unpacked_values();

            // this part handles dead-ends in hmax()
            if (search_space.get_node(state).is_dead_end() && eval_context.is_evaluator_value_infinite(f_evaluator.get()))
            {
                if (get_reachable_facts)
                {
                    reachable_facts[id] = open_list->get_reachable_facts_open_list(eval_context, state);
                }
                for (size_t i = 0; i < reachable_facts[id].size(); i++)
                {
                    if (reachable_facts[id][i] == 0)
                    {
                        certificate << primary_sign + to_string(i + 1 + offset) + inner_separator;
                    }
                }
                certificate << secondary_sign + to_string(state_formulas[state_counter]) + outer_separator;
                for (size_t i = 0; i < reachable_facts[id].size(); i++)
                {
                    if (reachable_facts[id][i] == 0)
                    {
                        certificate << secondary_sign + to_string(i + 1 + offset) + inner_separator + primary_sign + to_string(state_formulas[state_counter]) + outer_separator;
                    }
                }
            }
            // this part handles regular states
            else
            {
                // this part generates the state-formula
                for (size_t i = 0; i < varorder.size(); ++i)
                {
                    // variables start at 1 for dimacs format
                    int var = varorder[i];
                    for (int j = 0; j < task_proxy.get_variables()[var].get_domain_size(); ++j)
                    {
                        if (vals[i] == j)
                        {
                            certificate << secondary_sign + to_string((fact_to_var[var][j] + 1 + offset)) + inner_separator;
                        }
                        else
                        {
                            certificate << primary_sign + to_string(fact_to_var[var][j] + 1 + offset) + inner_separator;
                        }
                    }
                }
                certificate << secondary_sign + to_string(state_formulas[state_counter]);
                certificate << outer_separator;
                // this part generates the formula for each fact with the summarizing state variable
                for (size_t i = 0; i < varorder.size(); ++i)
                {
                    // variables start at 1 for dimacs format
                    int var = varorder[i];
                    for (int j = 0; j < task_proxy.get_variables()[var].get_domain_size(); ++j)
                    {
                        if (vals[i] == j)
                        {
                            certificate << primary_sign;
                        }
                        else
                        {
                            certificate << secondary_sign;
                        }
                        certificate << to_string(fact_to_var[var][j] + 1 + offset) + inner_separator;
                        certificate << primary_sign + to_string(state_formulas[state_counter]);
                        certificate << outer_separator;
                    }
                }
            }
            state_counter++;
        }
        int summarizing_variable = 1 + 2 * fact_amount + 2 * state_counter;
        if (offset != 0)
        {
            summarizing_variable += 1;
        }

        // this part generates the summarizing formula
        for (size_t i = 0; i < state_counter; i++)
        {
            certificate << secondary_sign + to_string(state_formulas[i]);
            certificate << inner_separator;
        }
        certificate << primary_sign + to_string(summarizing_variable);
        certificate << outer_separator;
        for (size_t i = 0; i < state_counter; i++)
        {
            certificate << primary_sign + to_string(state_formulas[i]);
            certificate << inner_separator + secondary_sign + to_string(summarizing_variable);
            certificate << outer_separator;
        }
        // certificate << outer_separator;
        return reachable_facts;
    }

    void EagerSearch::write_init(std::ofstream &certificate, std::vector<std::vector<int>> fact_to_var)
    {
        certificate << "init:=(";
        for (size_t i = 0; i < task_proxy.get_variables().size(); ++i)
        {
            for (int j = 0; j < task_proxy.get_variables()[i].get_domain_size(); ++j)
            {
                if (task_proxy.get_initial_state()[i].get_value() != j)
                {
                    certificate << "!";
                }
                certificate << "v" + to_string((fact_to_var[i][j] + 1));

                if (j != task_proxy.get_variables()[i].get_domain_size() - 1)
                {
                    certificate << "&";
                }
            }
            if (i != task_proxy.get_variables().size() - 1)
            {
                certificate << "&";
            }
        }
        certificate << ");\n";
    }

    void EagerSearch::write_init_dimacs(std::ofstream &certificate, std::vector<std::vector<int>> fact_to_var, int init_formula)
    {
        for (size_t i = 0; i < task_proxy.get_variables().size(); ++i)
        {
            for (int j = 0; j < task_proxy.get_variables()[i].get_domain_size(); ++j)
            {
                if (task_proxy.get_initial_state()[i].get_value() == j)
                {
                    certificate << "-";
                }
                certificate << to_string(fact_to_var[i][j] + 1) << " ";
            }
        }
        certificate << to_string(init_formula) << " 0\n";
        for (size_t i = 0; i < task_proxy.get_variables().size(); ++i)
        {
            for (int j = 0; j < task_proxy.get_variables()[i].get_domain_size(); ++j)
            {
                if (task_proxy.get_initial_state()[i].get_value() != j)
                {
                    certificate << "-";
                }
                certificate << to_string(fact_to_var[i][j] + 1) << " -" << to_string(init_formula) << " 0\n";
            }
        }
    }

    void EagerSearch::write_goal(std::ofstream &certificate, std::vector<std::vector<int>> fact_to_var)
    {
        certificate << "goal:=(";
        for (size_t i = 0; i < task_proxy.get_goals().size(); ++i)
        {
            FactProxy f = task_proxy.get_goals()[i];
            certificate << "v" + to_string(fact_to_var[f.get_variable().get_id()][f.get_value()] + 1);
            if (i != task_proxy.get_goals().size() - 1)
            {
                certificate << "&";
            }
        }
        certificate << ");\n";
    }

    void EagerSearch::write_goal_dimacs(std::ofstream &certificate, std::vector<std::vector<int>> fact_to_var, int goal_formula)
    {
        for (size_t i = 0; i < task_proxy.get_goals().size(); ++i)
        {
            FactProxy f = task_proxy.get_goals()[i];
            certificate << "-" << to_string(fact_to_var[f.get_variable().get_id()][f.get_value()] + 1) << " ";
        }
        certificate << to_string(goal_formula) << " 0\n";
        for (size_t i = 0; i < task_proxy.get_goals().size(); ++i)
        {
            FactProxy f = task_proxy.get_goals()[i];
            certificate << to_string(fact_to_var[f.get_variable().get_id()][f.get_value()] + 1) << " -" << to_string(goal_formula) << " 0\n";
        }
    }

    void EagerSearch::write_transition_formulas(std::ofstream &certificate, std::vector<std::vector<int>> fact_to_var, int fact_amount)
    {
        // write transition formulas
        for (size_t op_index = 0; op_index < task_proxy.get_operators().size(); ++op_index)
        {
            vector<bool> used_vars_in_operator = vector<bool>(fact_amount, false);
            OperatorProxy op = task_proxy.get_operators()[op_index];
            certificate << "a" + to_string(op_index) + ":=(";
            PreconditionsProxy pre = op.get_preconditions();
            EffectsProxy post = op.get_effects();
            for (size_t i = 0; i < pre.size(); ++i)
            {
                FactProxy f = pre[i];
                certificate << "v" + to_string(fact_to_var[f.get_variable().get_id()][f.get_value()] + 1);
                certificate << "&";
            }
            for (size_t i = 0; i < post.size(); ++i)
            {
                if (!post[i].get_conditions().empty())
                {
                    std::cout << "CONDITIONAL EFFECTS, ABORT!";
                    certificate.close();
                    std::remove("satproof.txt");
                    utils::exit_with(utils::ExitCode::SEARCH_CRITICAL_ERROR);
                }
                // add and del facts need to be primed -> add fact_amount
                FactProxy f = post[i].get_fact();
                certificate << "v" + to_string(fact_to_var[f.get_variable().get_id()][f.get_value()] + 1 + fact_amount);
                certificate << "&";
                used_vars_in_operator[fact_to_var[f.get_variable().get_id()][f.get_value()]] = true;

                //  all other facts from this FDR variable are set to false
                //  TODO: can we make this more compact / smarter?
                for (int j = 0; j < f.get_variable().get_domain_size(); j++)
                {
                    if (j == f.get_value())
                    {
                        continue;
                    }
                    certificate << "!v" + to_string(fact_to_var[f.get_variable().get_id()][j] + 1 + fact_amount);
                    certificate << "&";
                    used_vars_in_operator[fact_to_var[f.get_variable().get_id()][j]] = true;
                }
            }
            bool first = true;
            for (size_t j = 0; j < used_vars_in_operator.size(); j++)
            {
                if (used_vars_in_operator[j])
                {
                    continue;
                }
                if (!first)
                {
                    certificate << "&";
                }
                certificate << "(v" + to_string(j + 1 + fact_amount) + "==" + "v" + to_string(j + 1) + ")";
                first = false;
            }
            certificate << ");\n";
        }
    }

    std::tuple<vector<int>, int> EagerSearch::write_transition_formulas_dimacs(std::ofstream &certificate,
                                                                               std::vector<std::vector<int>> fact_to_var,
                                                                               int fact_amount,
                                                                               int current_variable)
    {
        vector<int> operator_formulas = vector<int>(task_proxy.get_operators().size());
        // write transition formulas
        for (size_t op_index = 0; op_index < task_proxy.get_operators().size(); ++op_index)
        {
            vector<bool> used_vars_in_operator = vector<bool>(fact_amount, false);
            current_variable++;
            operator_formulas[op_index] = current_variable;
            OperatorProxy op = task_proxy.get_operators()[op_index];
            PreconditionsProxy pre = op.get_preconditions();
            EffectsProxy post = op.get_effects();
            certificate << to_string(operator_formulas[op_index]) << " ";
            for (size_t i = 0; i < pre.size(); ++i)
            {
                FactProxy f = pre[i];
                certificate << "-" << to_string(fact_to_var[f.get_variable().get_id()][f.get_value()] + 1) << " ";
            }
            for (size_t i = 0; i < post.size(); ++i)
            {
                if (!post[i].get_conditions().empty())
                {
                    std::cout << "CONDITIONAL EFFECTS, ABORT!";
                    certificate.close();
                    std::remove("satproof.txt");
                    utils::exit_with(utils::ExitCode::SEARCH_CRITICAL_ERROR);
                }
                // add and del facts need to be primed -> add fact_amount
                FactProxy f = post[i].get_fact();
                certificate << "-" << to_string(fact_to_var[f.get_variable().get_id()][f.get_value()] + 1 + fact_amount) << " ";
                used_vars_in_operator[fact_to_var[f.get_variable().get_id()][f.get_value()]] = true;

                //  all other facts from this FDR variable are set to false
                //  TODO: can we make this more compact / smarter?
                for (int j = 0; j < f.get_variable().get_domain_size(); j++)
                {
                    if (j == f.get_value())
                    {
                        continue;
                    }
                    certificate << to_string(fact_to_var[f.get_variable().get_id()][j] + 1 + fact_amount) << " ";
                    used_vars_in_operator[fact_to_var[f.get_variable().get_id()][j]] = true;
                }
            }
            vector<int> unused_vars_formulas = vector<int>(used_vars_in_operator.size(), 0);
            for (size_t j = 0; j < used_vars_in_operator.size(); j++)
            {
                if (used_vars_in_operator[j])
                {
                    continue;
                }
                current_variable++;
                unused_vars_formulas[j] = current_variable;
                certificate << "-" << to_string(current_variable) << " ";
            }
            certificate << "0\n";
            used_vars_in_operator = vector<bool>(fact_amount, false);
            for (size_t i = 0; i < pre.size(); ++i)
            {
                FactProxy f = pre[i];
                certificate << to_string(fact_to_var[f.get_variable().get_id()][f.get_value()] + 1) << " -" << to_string(operator_formulas[op_index]) << " 0\n";
            }
            for (size_t i = 0; i < post.size(); ++i)
            {
                if (!post[i].get_conditions().empty())
                {
                    std::cout << "CONDITIONAL EFFECTS, ABORT!";
                    certificate.close();
                    std::remove("satproof.txt");
                    utils::exit_with(utils::ExitCode::SEARCH_CRITICAL_ERROR);
                }
                // add and del facts need to be primed -> add fact_amount
                FactProxy f = post[i].get_fact();
                certificate << to_string(fact_to_var[f.get_variable().get_id()][f.get_value()] + 1 + fact_amount) << " -" << to_string(operator_formulas[op_index]) << " 0\n";
                used_vars_in_operator[fact_to_var[f.get_variable().get_id()][f.get_value()]] = true;

                //  all other facts from this FDR variable are set to false
                //  TODO: can we make this more compact / smarter?
                for (int j = 0; j < f.get_variable().get_domain_size(); j++)
                {
                    if (j == f.get_value())
                    {
                        continue;
                    }
                    certificate << "-" << to_string(fact_to_var[f.get_variable().get_id()][j] + 1 + fact_amount) << " -" << to_string(operator_formulas[op_index]) << " 0\n";
                    used_vars_in_operator[fact_to_var[f.get_variable().get_id()][j]] = true;
                }
            }
            for (size_t j = 0; j < used_vars_in_operator.size(); j++)
            {
                if (used_vars_in_operator[j])
                {
                    continue;
                }
                if (unused_vars_formulas[j] == 0)
                {
                    std::cout << "should never happen";
                }
                certificate << to_string(unused_vars_formulas[j]) << " -" << to_string(operator_formulas[op_index]) << " 0\n";
                certificate << "-" << to_string(j + 1) << " -" << to_string(j + 1 + fact_amount) << " " << to_string(unused_vars_formulas[j]) << " 0\n";
                certificate << to_string(j + 1) << " " << to_string(j + 1 + fact_amount) << " " << to_string(unused_vars_formulas[j]) << " 0\n";
                certificate << "-" << to_string(j + 1) << " " << to_string(j + 1 + fact_amount) << " -" << to_string(unused_vars_formulas[j]) << " 0\n";
                certificate << to_string(j + 1) << " -" << to_string(j + 1 + fact_amount) << " -" << to_string(unused_vars_formulas[j]) << " 0\n";
            }
        }
        return make_tuple(operator_formulas, current_variable);
    }

    void EagerSearch::write_final_formula(std::ofstream &certificate)
    {
        certificate << "f:=(cR&init)|(!cR&goal)|(!cR & cRp&(";
        for (size_t op_index = 0; op_index < task_proxy.get_operators().size(); ++op_index)
        {
            certificate << "a" + to_string(op_index);
            if (op_index != task_proxy.get_operators().size() - 1)
            {
                certificate << "|";
            }
        }
        certificate << "));\n";
        certificate << "ASSIGN f;";
    }

    void EagerSearch::write_final_formula_dimacs(std::ofstream &certificate,
                                                 int init_formula,
                                                 int cR_formula,
                                                 int cRp_formula,
                                                 int goal_formula,
                                                 int current_variable,
                                                 vector<int> operator_formulas)
    {
        current_variable++;
        int static_formula = current_variable;
        certificate << "-" << to_string(init_formula) << " -" << to_string(cR_formula) << " " << to_string(static_formula) << " 0\n";
        certificate << "-" << to_string(goal_formula) << " " << to_string(cR_formula) << " " << to_string(static_formula) << " 0\n";
        certificate << to_string(goal_formula) << " " << to_string(init_formula) << " -" << to_string(static_formula) << " 0\n";
        certificate << to_string(init_formula) << " -" << to_string(cR_formula) << " -" << to_string(static_formula) << " 0\n";
        certificate << to_string(goal_formula) << " " << to_string(cR_formula) << " -" << to_string(static_formula) << " 0\n";

        // then append the dynamic part (depending on operators)
        current_variable++;
        int final_formula = current_variable;

        certificate << "-" << to_string(static_formula) << " " << to_string(final_formula) << " 0\n";
        certificate << to_string(static_formula) << " " << to_string(cRp_formula) << " -" << to_string(final_formula) << " 0\n";
        certificate << to_string(static_formula) << " -" << to_string(cR_formula) << " -" << to_string(final_formula) << " 0\n";

        certificate << to_string(static_formula) << " -" << to_string(final_formula) << " ";
        for (int op : operator_formulas)
        {
            certificate << to_string(op) << " ";
        }
        certificate << "0\n";
        for (int op : operator_formulas)
        {
            certificate << "-" << to_string(op) << " " << to_string(cR_formula) << " -" << to_string(cRp_formula) << " " << to_string(final_formula) << " 0\n";
        }
        certificate << to_string(final_formula) << " 0\n";
    }

    void EagerSearch::write_unsolvability_proof()
    {
        double writing_start = utils::g_timer();
        std::vector<int> varorder(task_proxy.get_variables().size());
        for (size_t i = 0; i < varorder.size(); ++i)
        {
            varorder[i] = i;
        }
        std::vector<std::vector<int>> fact_to_var(varorder.size(), std::vector<int>());
        std::vector<bool> used_vars_in_operator;
        int fact_amount = 0;
        for (size_t i = 0; i < varorder.size(); ++i)
        {
            int var = varorder[i];
            fact_to_var[var].resize(task_proxy.get_variables()[var].get_domain_size());
            for (int j = 0; j < task_proxy.get_variables()[var].get_domain_size(); ++j)
            {
                fact_to_var[var][j] = fact_amount++;
                used_vars_in_operator.push_back(false);
            }
        }

        if (unsolv_type == UnsolvabilityVerificationType::DIMACS)
        {
            std::cout << "write output to dimacs.txt...";
            std::ofstream certificate;
            certificate.open(unsolvability_directory + "dimacs.txt");
            certificate << "p cnf 1 1\n";
            int base = fact_amount * 2 + 2 * state_registry.size();
            int cR_formula = 1 + base;
            int cRp_formula = 2 + base;
            int init_formula = 3 + base;
            int goal_formula = 4 + base;
            map<StateID, vector<int>> reachable_facts = write_formula_dimacs(certificate, "cR", varorder, fact_to_var, 0, " ", " 0\n", "", "-", fact_amount);
            write_formula_dimacs(certificate, "cRp", varorder, fact_to_var, fact_amount, " ", " 0\n", "", "-", fact_amount, reachable_facts);
            write_init_dimacs(certificate, fact_to_var, init_formula);
            write_goal_dimacs(certificate, fact_to_var, goal_formula);
            std::tuple<vector<int>, int> tmp = write_transition_formulas_dimacs(certificate, fact_to_var, fact_amount, goal_formula);
            write_final_formula_dimacs(certificate, init_formula, cR_formula, cRp_formula, goal_formula, std::get<1>(tmp), std::get<0>(tmp));
            std::cout << "done\n";
        }
        if (unsolv_type == UnsolvabilityVerificationType::PROOF)
        {
            std::cout << "start writing to satproof.txt...";
            std::ofstream certificate;
            certificate.open(unsolvability_directory + "satproof.txt");
            // write compR, compR' and R formula
            certificate << "BC1.1\n";
            map<StateID, vector<int>> reachable_facts = write_formula(certificate, "cR", varorder, fact_to_var, 0, "|", "&", "", "!");
            write_formula(certificate, "cRp", varorder, fact_to_var, fact_amount, "|", "&", "", "!", reachable_facts);
            write_init(certificate, fact_to_var);
            write_goal(certificate, fact_to_var);
            write_transition_formulas(certificate, fact_to_var, fact_amount);
            write_final_formula(certificate);
            // write_formula(certificate, "R", varorder, fact_to_var, 0, "&", "|", "!", "", reachable_facts);
            std::cout << "done";
        }
        bool write_inductive = false;
        if (write_inductive)
        {
            std::ofstream certificate;
            certificate.open(unsolvability_directory + "satproof.txt");
            certificate << "c main proof file\n"
                           "c this file contains the backwards inductive certificate\n"
                           "p cnf " +
                               std::to_string(fact_amount) + " " + std::to_string(state_registry.size()) + "\n";

            // certificate should represent complement of all reachable states
            //-> includes the complement of all states reached -> CNF of all states reached

            for (StateID id : state_registry)
            {
                State state = state_registry.lookup_state(id);
                EvaluationContext eval_context(state,
                                               0,
                                               false, &statistics);
                state.unpack();
                std::vector<int> vals = state.get_unpacked_values();
                for (size_t i = 0; i < varorder.size(); ++i)
                {
                    // variables start at 1 for dimacs format
                    int var = varorder[i];
                    for (int j = 0; j < task_proxy.get_variables()[var].get_domain_size(); ++j)
                    {
                        if (vals[i] == j)
                        {
                            certificate << -(fact_to_var[var][j] + 1) << " ";
                        }
                        else
                        {
                            certificate << (fact_to_var[var][j] + 1) << " ";
                        }
                    }
                }
                certificate << "0\n";
            }
            certificate.close();
        }
        /*
          Writing the task file at the end minimizes the chances that both task and
          proof file are there but the planner could not finish writing them.
         */
        write_unsolvability_task_file(varorder);

        double writing_end = utils::g_timer();
        std::cout << "Time for writing unsolvability satproof: "
                  << writing_end - writing_start << std::endl;
    }

    void EagerSearch::write_unsolvability_task_file(const std::vector<int> &varorder)
    {
        assert(varorder.size() == task_proxy.get_variables().size());
        std::vector<std::vector<int>> fact_to_var(varorder.size(), std::vector<int>());
        int fact_amount = 0;
        for (size_t i = 0; i < varorder.size(); ++i)
        {
            int var = varorder[i];
            fact_to_var[var].resize(task_proxy.get_variables()[var].get_domain_size());
            for (int j = 0; j < task_proxy.get_variables()[var].get_domain_size(); ++j)
            {
                fact_to_var[var][j] = fact_amount++;
            }
        }
        std::ofstream task_file;
        task_file.open(unsolvability_directory + "task.txt");
        task_file << "begin_atoms:" << fact_amount << "\n";
        for (size_t i = 0; i < varorder.size(); ++i)
        {
            int var = varorder[i];
            for (int j = 0; j < task_proxy.get_variables()[var].get_domain_size(); ++j)
            {
                task_file << task_proxy.get_variables()[var].get_fact(j).get_name() << "\n";
            }
        }
        task_file << "end_atoms\n";

        task_file << "begin_init\n";
        // variables start at 1 for dimacs format
        for (size_t i = 0; i < task_proxy.get_variables().size(); ++i)
        {
            task_file << fact_to_var[i][task_proxy.get_initial_state()[i].get_value()] + 1 << "\n";
        }
        task_file << "end_init\n";

        // variables start at 1 for dimacs format
        task_file << "begin_goal\n";
        for (size_t i = 0; i < task_proxy.get_goals().size(); ++i)
        {
            FactProxy f = task_proxy.get_goals()[i];
            task_file << fact_to_var[f.get_variable().get_id()][f.get_value()] + 1 << "\n";
        }
        task_file << "end_goal\n";
        // variables start at 1 for dimacs format
        task_file << "begin_actions:" << task_proxy.get_operators().size() << "\n";
        for (size_t op_index = 0; op_index < task_proxy.get_operators().size(); ++op_index)
        {
            OperatorProxy op = task_proxy.get_operators()[op_index];

            task_file << "begin_action\n"
                      << op.get_name() << "\n"
                      << "cost: " << op.get_cost() << "\n";
            PreconditionsProxy pre = op.get_preconditions();
            EffectsProxy post = op.get_effects();

            for (size_t i = 0; i < pre.size(); ++i)
            {
                task_file << "PRE:" << fact_to_var[pre[i].get_variable().get_id()][pre[i].get_value()] + 1 << "\n";
            }
            for (size_t i = 0; i < post.size(); ++i)
            {
                if (!post[i].get_conditions().empty())
                {
                    std::cout << "CONDITIONAL EFFECTS, ABORT!";
                    task_file.close();
                    std::remove("task.txt");
                    utils::exit_with(utils::ExitCode::SEARCH_CRITICAL_ERROR);
                }
                FactProxy f = post[i].get_fact();
                task_file << "ADD:" << fact_to_var[f.get_variable().get_id()][f.get_value()] + 1 << "\n";
                // all other facts from this FDR variable are set to false
                // TODO: can we make this more compact / smarter?
                for (int j = 0; j < f.get_variable().get_domain_size(); j++)
                {
                    if (j == f.get_value())
                    {
                        continue;
                    }
                    task_file << "DEL:" << fact_to_var[f.get_variable().get_id()][j] + 1 << "\n";
                }
            }
            task_file << "end_action\n";
        }
        task_file << "end_actions\n";
        task_file.close();
    }
}
