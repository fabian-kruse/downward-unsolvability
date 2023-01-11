#ifndef SEARCH_ENGINES_EAGER_SEARCH_H
#define SEARCH_ENGINES_EAGER_SEARCH_H

#include "../open_list.h"
#include "../search_engine.h"

#include "../unsolvability/cudd_interface.h"

#include <memory>
#include <vector>
#include <map>

class Evaluator;
class PruningMethod;

namespace options
{
    class OptionParser;
    class Options;
}

namespace eager_search
{
    class EagerSearch : public SearchEngine
    {
        const bool reopen_closed_nodes;
        const UnsolvabilityVerificationType unsolv_type;

        std::unique_ptr<StateOpenList> open_list;
        std::shared_ptr<Evaluator> f_evaluator;

        std::vector<Evaluator *> path_dependent_evaluators;
        std::vector<std::shared_ptr<Evaluator>> preferred_operator_evaluators;
        std::shared_ptr<Evaluator> lazy_evaluator;

        std::shared_ptr<PruningMethod> pruning_method;

        void start_f_value_statistics(EvaluationContext &eval_context);
        void update_f_value_statistics(EvaluationContext &eval_context);
        void reward_progress();

        std::string unsolvability_directory;

    protected:
        virtual void initialize() override;
        virtual SearchStatus step() override;

        std::map<StateID, std::vector<int>> write_formula(std::ofstream &certificate,
                                                          std::string formula_name,
                                                          std::vector<int> varorder,
                                                          std::vector<std::vector<int>> fact_to_var,
                                                          int offset, std::string inner_separator,
                                                          std::string outer_separator,
                                                          std::string primary_sign,
                                                          std::string secondary_sign,
                                                          std::map<StateID, std::vector<int>> reachable_facts = std::map<StateID, std::vector<int>>());

        std::map<StateID, std::vector<int>> write_formula_dimacs(std::ofstream &certificate,
                                                                 std::string formula_name,
                                                                 std::vector<int> varorder,
                                                                 std::vector<std::vector<int>> fact_to_var,
                                                                 int offset, std::string inner_separator,
                                                                 std::string outer_separator,
                                                                 std::string primary_sign,
                                                                 std::string secondary_sign,
                                                                 int fact_amount,
                                                                 std::map<StateID, std::vector<int>> reachable_facts = std::map<StateID, std::vector<int>>());
        void write_init_dimacs(std::ofstream &certificate, std::vector<std::vector<int>> fact_to_var, int init_formula);
        void write_goal_dimacs(std::ofstream &certificate, std::vector<std::vector<int>> fact_to_var, int goal_formula);
        std::tuple<std::vector<int>, int> write_transition_formulas_dimacs(std::ofstream &certificate,
                                                                           std::vector<std::vector<int>> fact_to_var,
                                                                           int fact_amount,
                                                                           int current_variable);
        void write_final_formula_dimacs(std::ofstream &certificate,
                                        int init_formula,
                                        int cR_formula,
                                        int cRp_formula,
                                        int goal_formula,
                                        int current_variable,
                                        std::vector<int> operator_formulas);
        void write_init(std::ofstream &certificate, std::vector<std::vector<int>> fact_to_var);
        void write_goal(std::ofstream &certificate, std::vector<std::vector<int>> fact_to_var);
        void write_transition_formulas(std::ofstream &certificate,
                                       std::vector<std::vector<int>> fact_to_var,
                                       int fact_amount);
        void write_final_formula(std::ofstream &certificate);

    public:
        explicit EagerSearch(const options::Options &opts);
        virtual ~EagerSearch() = default;

        virtual void print_statistics() const override;

        void dump_search_space() const;

        void write_unsolvability_proof();
        void write_unsolvability_task_file(const std::vector<int> &varorder);
    };

    extern void add_options_to_parser(options::OptionParser &parser);
}

#endif
