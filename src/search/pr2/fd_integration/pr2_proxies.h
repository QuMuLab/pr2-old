#ifndef PR2_PROXIES_H
#define PR2_PROXIES_H

#include "../../task_proxy.h"
#include "../../plan_manager.h"
#include "../../search_algorithm.h"
#include "../../plugins/options.h"

class TaskProxy;
class OperatorProxy;
class OperatorsProxy;
class EffectsProxy;
class StateInterface;

using namespace std;

using DeterministicPlan = Plan;


#include "../pr2.h"
#include "partial_state.h"
#include "fsap_penalized_ff_heuristic.h"

namespace fsap_penalized_ff_heuristic {
    class FSAPPenalizedFFHeuristic;
}

class PR2State;
class PR2OperatorProxy;



class PR2OperatorProxy : public OperatorProxy {
    const AbstractTask *task;
    int _index;
    bool _is_an_axiom;

public:
    int nondet_index;
    int nondet_outcome;

    // TODO: https://github.com/QuMuLab/rbp/blob/main/src/search/global_operator.cc#L142
    PR2State *all_fire_context;

    PR2OperatorProxy(const AbstractTask &task, int index, bool is_axiom)
        : OperatorProxy(task, index, is_axiom), task(&task), _index(index), _is_an_axiom(is_axiom) {
        update_nondet_info();
    }

    void update_nondet_info();

    string get_nondet_name() const
    {
        // Split the get_name() string and return everything before _DETDUP
        string name = get_name();
        return name.substr(0, name.find("_DETDUP"));
    }
    void dump() const {
        cout << "Operator: " << get_name() << endl;
        cout << "Nondet index: " << nondet_index << endl;
        cout << "Nondet outcome: " << nondet_outcome << endl;
        cout << "Is axiom: " << _is_an_axiom << endl;
        cout << "Precondition:" << endl;
        for (auto precond : get_preconditions())
        {
            cout << "  " << precond.get_variable().get_id() << " = " << precond.get_value() << endl;
        }
        cout << "Effects:" << endl;
        for (auto effect : get_effects())
        {
            cout << "  Conditions:" << endl;
            for (auto condition : effect.get_conditions())
            {
                cout << "    " << condition.get_variable().get_id() << " = " << condition.get_value() << endl;
            }
            cout << "  Effect: " << effect.get_fact().get_variable().get_id() << " = " << effect.get_fact().get_value() << endl;
        }
    }
    bool is_possibly_applicable(const PR2State &state) const {
        // Iterate over the conditions, and look for something that disagrees with the state
        for (auto pre : get_preconditions())
        {
            if ((state[pre.get_variable().get_id()] != -1) && 
                (state[pre.get_variable().get_id()] != pre.get_value()))
                return false;
        }
        return true;
    }
    int compute_conflict_var(PR2State &state) const {
        for (auto pre : get_preconditions()) {
            if ((state[pre.get_variable().get_id()] != -1) && 
                (state[pre.get_variable().get_id()] != pre.get_value()))
                return pre.get_variable().get_id();
        }
        return -1;
    }
    // TODO: Remove if unececssary
    EffectsProxy get_all_effects() const {
        // cout << "TODO: Implement PR2OperatorProxy::get_all_effects" << endl;
        return get_effects();
    }
};

class PR2OperatorsProxy : public OperatorsProxy {
    const AbstractTask *_task;
public:
    using ItemType = PR2OperatorProxy;
    ~PR2OperatorsProxy() = default;

    explicit PR2OperatorsProxy(const AbstractTask &task) : OperatorsProxy(task), _task(&task) {}

    PR2OperatorsProxy(const OperatorsProxy& ops) : OperatorsProxy(ops) {}

    PR2OperatorProxy operator[](std::size_t index) const {
        assert(index < size());
        // Call the parent [] method and cast the result to a PR2OperatorProxy
        OperatorProxy op = OperatorsProxy::operator[](index);
        return static_cast<PR2OperatorProxy &>(op);
        // return PR2OperatorProxy(*_task, index, false);
    }

    PR2OperatorProxy operator[](OperatorID id) const {
        return (*this)[id.get_index()];
    }
};



class PR2TaskProxy : public TaskProxy {

    // Map from operator id to nondet index
    vector<int>* nondet_index_map;

    const AbstractTask *task;
    PR2State *orig_initial_state;

    // Store the ever-changing goals/initial state
    PR2State *current_initial_state;
    vector<FactPair> *current_goals;

public:

    explicit PR2TaskProxy(const AbstractTask &task, PR2State init) : TaskProxy(task), task(&task), orig_initial_state(&init) {}

    PR2OperatorsProxy get_operators() const {
        return PR2OperatorsProxy(TaskProxy::get_operators());
    }

    void set_nondet_index_map(vector<int> &nmap) {
        nondet_index_map = &nmap;
    }
    int get_nondet_index(int op_id) const {
        return (*nondet_index_map)[op_id];
    }
    int get_nondet_index(OperatorID op) const {
        return get_nondet_index(op.get_index());
    }
    int get_nondet_index(OperatorProxy op) const {
        return get_nondet_index(op.get_id());
    }

    void dump_pddl_state(const State &state) const {
        PR2State(state).dump_pddl();
    }
    void dump_fdr_state(const State &state) const {
        PR2State(state).dump_fdr();
    }

    PR2State * generate_new_init() {
        return new PR2State(*orig_initial_state);
    }

    string get_fact_name(int var, int val) const {
        return task->get_fact_name(FactPair(var, val));
    }

    string get_variable_name(int var) const {
        return task->get_variable_name(var);
    }



    void set_initial_state(PR2State &state) {
        current_initial_state = &state;
    }
    PR2State *get_pr2_initial_state() const {
        return current_initial_state;
    }
    


    void set_goal(vector<FactPair> &goal_facts) {
        current_goals = &goal_facts;
    }
    void set_goal(const PR2State &state) {
        vector<pair<int, int>> goal_facts;
        for (int i = 0; i <= state.size(); i++)
        {
            if (state[i] != -1)
                goal_facts.push_back(make_pair(i, state[i]));
        }
        set_goal(goal_facts);
    }
    void set_goal(const vector<pair<int, int>> &goal_facts) {
        vector<FactPair> goal_facts_;
        for (auto fact : goal_facts)
        {
            goal_facts_.push_back(FactPair(fact.first, fact.second));
        }
        set_goal(goal_facts_);
    }
    vector<FactPair> *get_pr2_goals() const {
        return current_goals;
    }


    fsap_penalized_ff_heuristic::FSAPPenalizedFFHeuristic * new_deadend_heuristic() {
        shared_ptr<AbstractTask> task_ptr = shared_ptr<AbstractTask>(const_cast<AbstractTask*>(task));
        return new fsap_penalized_ff_heuristic::FSAPPenalizedFFHeuristic(task_ptr, false, "FSAP Aware Heuristic", utils::Verbosity::SILENT);
    }
};

#endif