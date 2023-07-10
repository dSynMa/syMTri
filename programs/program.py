from itertools import combinations
from typing import Set

from graphviz import Digraph
from parsing.string_to_methods import parse_dsl, SymexWalker, to_formula
from pysmt.shortcuts import And, Or, Not

from parsing.string_to_prop_logic import string_to_prop
from programs.analysis.nuxmv_model import NuXmvModel
from programs.analysis.smt_checker import SMTChecker
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import stutter_transition, symbol_table_from_program, is_deterministic
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.util import disjunct_formula_set, mutually_exclusive_rules, neg, true, \
    sat, type_constraints_acts, conjunct_formula_set, implies
from prop_lang.variable import Variable


class Program:

    def __init__(self, name, sts, init_st, init_val: [TypedValuation],
                 env_transitions: [Transition], con_transitions: [Transition],
                 env_events: [Variable], con_events: [Variable], out_events: [Variable], debug=True):
        self.name = name
        self.initial_state = init_st
        self.states: Set = set(sts)
        self.valuation = init_val
        self.env_events = env_events
        self.con_events = con_events
        self.out_events = out_events
        self.symbol_table = symbol_table_from_program(self)
        self.local_vars = [Variable(tv.name) for tv in init_val]

        self.env_transitions = env_transitions
        self.con_transitions = con_transitions

        if len(self.con_transitions) == 0:
            self.con_transitions = [Transition(s, true(), [], [], s) for s in self.states]

        unsat_env_trans = []
        for t in self.env_transitions:
            if not sat(t.condition, self.symbol_table, SMTChecker()):
                unsat_env_trans.append(t)

        unsat_con_trans = []
        for t in self.con_transitions:
            if not sat(t.condition, self.symbol_table, SMTChecker()):
                unsat_con_trans.append(t)

        self.env_transitions = [t for t in self.env_transitions if t not in unsat_env_trans]
        if len(unsat_env_trans) > 0:
            print("Removed environment transitions with unsat transitions: " + ",\n".join(map(str, unsat_env_trans)))

        if len(unsat_env_trans) > 0:
            print("Removed controller transitions with unsat transitions: " + ",\n".join(map(str, unsat_con_trans)))
        self.con_transitions = [t for t in self.con_transitions if t not in unsat_con_trans]

        self.state_to_env = {s:[t for t in self.env_transitions if t.src == s] for s in self.states}
        self.state_to_con = {s:[t for t in self.con_transitions if t.src == s] for s in self.states}

        env_otherwise = [t for t in self.env_transitions if str(t.condition) == "otherwise"]
        if len(env_otherwise) > 1:
            raise Exception("Too many environment otherwise transitions")
        elif len(env_otherwise) == 1:
            otherwise_trans = env_otherwise[0]
            condition = neg(disjunct_formula_set([t.condition
                                                                  for t in env_transitions
                                                                  if t.src == otherwise_trans.src
                                                                  and t != otherwise_trans]))
            if sat(condition, self.symbol_table, SMTChecker()):
                concrete_trans = Transition(otherwise_trans.src,
                                                condition,
                                                otherwise_trans.action,
                                                otherwise_trans.output,
                                                otherwise_trans.tgt)
                self.env_transitions.append(concrete_trans)
            self.env_transitions.remove(otherwise_trans)

        con_otherwise = [str(t.condition) == "otherwise" for t in self.con_transitions if str(t.condition) == "otherwise"]
        if len(con_otherwise) > 1:
            raise Exception("Too many controller otherwise transitions")
        elif len(con_otherwise) == 1:
            otherwise_trans = con_otherwise[0]
            condition = neg(disjunct_formula_set([t.condition
                                                                  for t in con_transitions
                                                                  if t.src == otherwise_trans.src
                                                                  and t != otherwise_trans]))
            if sat(condition, self.symbol_table, SMTChecker()):
                concrete_trans = Transition(otherwise_trans.src,
                                            condition,
                                                otherwise_trans.action,
                                                otherwise_trans.output,
                                                otherwise_trans.tgt)
                self.con_transitions.append(concrete_trans)
            self.con_transitions.remove(otherwise_trans)

        self.env_transitions = [self.add_type_constraints_to_guards(t) for t in self.env_transitions]
        self.con_transitions = [self.add_type_constraints_to_guards(t) for t in self.con_transitions]

        if debug:
            # type checking
            for transition in self.env_transitions:
                if not all(v in env_events + self.local_vars for v in transition.condition.variablesin()):
                    raise Exception("Conditions in environment transitions can only refer to environment events and "
                                    "local/internal variables: " + str(transition) + ".")

                if not all(biop.left in self.local_vars for biop in transition.action):
                    raise Exception("Actions in environment transitions can only set "
                                    "local/internal variables: " + str(transition) + ".")
                if not all(v in env_events + self.local_vars for biop in transition.action for v in
                           biop.right.variablesin()):
                    raise Exception("Actions in environment transitions can only refer to environment or "
                                    "local/internal variables: " + str(transition) + ".")
                if not all(v in out_events or (isinstance(v, UniOp) and v.simplify().right in out_events) for v in
                           transition.output):
                    raise Exception(
                        "Outputs of environment transitions can only refer to program output variables: " + str(
                            transition) + ".")

            for transition in self.con_transitions:
                if not all(v in con_events + self.local_vars for v in transition.condition.variablesin()):
                    raise Exception("Conditions in controller transitions can only refer to controller events and "
                                    "local/internal variables: " + str(transition) + ".")

                if not all(biop.left in self.local_vars for biop in transition.action):
                    raise Exception("Actions in controller transitions can only set "
                                    "local/internal variables: " + str(transition) + ".")
                if not all(v in (con_events + self.local_vars)
                           for biop in transition.action for v in biop.right.variablesin()):
                    raise Exception("Actions in controller transitions can only refer to environment or"
                                    "local/internal variables: " + str(transition) + ".")

        self.deterministic = is_deterministic(self)

    def add_type_constraints_to_guards(self, transition: Transition):
        return transition.add_condition(type_constraints_acts(transition.action, self.symbol_table).to_nuxmv())

    def to_dot(self):
        dot = Digraph(name=self.name,
                      graph_attr=[("overlap", "scalexy"), ("splines", "true"), ("ranksep", "0.8"),
                                  ("nodesep", "0.5")],
                      node_attr=[("shape", "rectangle")],
                      edge_attr=[("fontname", "mono")],
                      engine='dot',
                      format='svg')

        to_str = lambda x: ", ".join([str(v) for v in list(x)]) if not isinstance(x, str) and hasattr(x,
                                                                                                      "__iter__") else str(
            x)

        dot.node("init", "", [("shape", "point")])
        for s in self.states:
            dot.node(to_str(s))

        dot.edge("init", to_str(self.initial_state), style="solid")

        for t in self.env_transitions:

            label = str(t.condition)
            if t.action is not None and len(t.action) > 0:
                label = label + " $ " + ', '.join(map(str, t.action))
            if t.output is not None and len(t.output) > 0:
                label = label + " >> " + ', '.join(map(str, t.output))
            dot.edge(to_str(t.src), to_str(t.tgt), label)

        for t in self.con_transitions:
            label = str(t.condition)
            if len(t.action) > 0:
                label = label + " $ " + ', '.join(map(str, t.action))
            dot.edge(to_str(t.src), to_str(t.tgt), label, style="dotted")

        return dot

    def to_nuXmv_with_turns(self,
                            include_mismatches_due_to_nondeterminism=False,
                            prefer_compatibility=False,
                            pred_definitions: dict={}):

        real_acts = []
        guards = []
        acts = []
        for env_transition in self.env_transitions:
            guard = "turn = env & " + env_transition.src + " & " \
                    + str(env_transition.condition.to_nuxmv())

            act = "next(" + env_transition.tgt + ")" \
                  + "".join([" & next(" + str(act.left) + ") = " + str(act.right.to_nuxmv()) for act in
                             self.complete_action_set(env_transition.action)]) \
                  + "".join([" & next(" + str(assignment) + ")" for assignment in
                             env_transition.output]) \
                  + "".join([" & !next(" + str(event) + ")" for event in self.out_events
                             if event not in env_transition.output])
            guards.append(guard)
            acts.append(act)
            real_acts.append((env_transition.action, env_transition.output, env_transition.tgt))

        for con_transition in self.con_transitions:
            guard = "turn = con & " + con_transition.src + " & " \
                    + str(con_transition.condition.to_nuxmv())

            # updated_variables = [str(act.left) for act in con_transition.action]
            act = "next(" + con_transition.tgt + ")" \
                  + "".join([" & next(" + str(act.left) + ") = " + str(act.right.to_nuxmv()) for act in
                             self.complete_action_set(con_transition.action)]) \
                  + "".join([" & !next(" + str(event) + ")"
                             for event in self.out_events])
            guards.append(guard)
            acts.append(act)
            real_acts.append((con_transition.action, con_transition.output, con_transition.tgt))
        real_acts.append(([], [], None)) # for the stutter transition

        define = []
        guard_and_act = []
        guard_ids = []

        i = 0
        while i < len(guards):
            define += ["guard_" + str(i) + " := " + guards[i]]
            define += ["act_" + str(i) + " := " + acts[i]]
            guard_ids.append("guard_" + str(i))
            guard_and_act.append("(guard_" + str(i) + " & " + "act_" + str(i) + ")")
            i += 1

        identity = []
        for typed_val in self.valuation:
            identity.append("next(" + str(typed_val.name) + ") = " + str(typed_val.name))
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))

        identity += ["!next(" + str(event) + ")" for event in self.out_events]

        define += ["identity_" + self.name + " := " + " & ".join(identity)]

        # if no guard holds, then keep the same state and output no program events
        guards.append("!(" + " | ".join(guard_ids) + ")")
        acts.append("identity_" + self.name)
        define += ["guard_" + str(len(guards) - 1) + " := " + guards[len(guards) - 1]]
        define += ["act_" + str(len(guards) - 1) + " := " + acts[len(guards) - 1]]

        guard_and_act.append("(guard_" + str(len(guards) - 1) + " & " + "act_" + str(len(guards) - 1) + ")")

        if not prefer_compatibility:
            transitions = guard_and_act
        else:
            guard_act_and_compatible = []
            guard_and_not_compatible = []
            for i, ga in enumerate(guard_and_act):
                (action, outputs, tgt) = real_acts[i]
                action = [a.to_nuxmv() for a in action]
                compatible_next = conjunct_formula_set([implies(pred,
                                                            defn.replace(action
                                                                         + [BiOp(Variable(str(v) + "_prev"), ":=", v)
                                                                                 for v in defn.variablesin()]))
                                                        for pred, defn in pred_definitions.items()])
                compatible_next = str(compatible_next) + " & " + " & ".join(["mon_" + str(o) for o in outputs if isinstance(o, Variable)] +\
                                                                            ["!mon_" + str(o) for o in self.out_events if o not in outputs] + \
                                                                            (["mon_" + str(tgt)] if tgt is not None else []))
                guard_act_and_compatible.append("(" + ga + " & act_" + str(i) + " & (" + str(compatible_next) + "))")
                guard_and_not_compatible.append("(guard_" + str(i) + " & " + str(compatible_next) + ")")

            transitions = ["(" + " | ".join(guard_act_and_compatible) + ")"] + [
                "(!(" + " | ".join(guard_and_not_compatible) + ") & (" + " | ".join(guard_and_act) + "))"]

        vars = ["turn : {env, mon_env, con, mon_con}"]
        vars += [str(st) + " : boolean" for st in self.states]
        vars += [str(var.name) + " : " + str(var.type).replace("bool", "boolean") for var in self.valuation if
                 var.type not in ("nat", "natural", "int")]
        vars += [str(var.name) + " : integer" for var in self.valuation if var.type in ("nat", "natural", "int")]
        # for transition_predicate checking
        vars += [str(var.name) + "_prev : " + str(var.type.replace("bool", "boolean")) for var in self.valuation if
                var.type not in ("nat", "natural", "int")]
        vars += [str(var.name) + "_prev : integer" for var in self.valuation if
                 var.type in ("nat", "natural", "int")]

        vars += [str(var) + " : boolean" for var in self.env_events]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += [str(var) + " : boolean" for var in self.out_events]

        init = [self.initial_state]
        init += [str(val.name) + " = " + str(val.value.to_nuxmv()) for val in self.valuation]
        init += ["!" + str(event) for event in self.out_events]
        trans = ["\n\t|\t".join(transitions)]
        update_prevs = "(turn = env | turn == con)" + " & " + " & ".join(["next(" + str(var.name) + "_prev) = " + str(var.name) for var in self.valuation])
        maintain_prevs = "!(turn = env | turn == con)" + " & " + " & ".join(["next(" + str(var.name) + "_prev) = " + str(var.name)  + "_prev" for var in self.valuation])
        prev_logic = "((" + update_prevs + ") | (" + maintain_prevs + "))"
        trans += [prev_logic]

        invar = mutually_exclusive_rules(self.states)
        invar += [str(disjunct_formula_set([Variable(s) for s in self.states]))]
        invar += [str(val.name) + " >= 0" for val in self.valuation if (val.type == "nat" or val.type == "natural")]

        # if include_mismatches_due_to_nondeterminism is not None and not include_mismatches_due_to_nondeterminism:
        #     for i in range(len(guards)):
        #         all_others_neg = ["!guard_" + str(j) for j in range(len(guards)) if j != i]
        #         invar += ["guard_" + str(i) + " -> (" + " & ".join(all_others_neg) + ")"]

        return NuXmvModel(self.name, vars, define, init, invar, trans)

    def complete_transitions(self):
        complete_env = []
        complete_con = []

        reachable_states = set(
            [s for t in self.env_transitions for s in [t.tgt, t.src]] + [s for t in self.con_transitions for s in
                                                                         [t.tgt, t.src]])
        for s in reachable_states:
            env_from_s = [t for t in self.env_transitions if t.src == s]
            env_stutter_from_s = stutter_transition(self, s, True)
            if env_stutter_from_s != None:
                env_from_s += [env_stutter_from_s]
            complete_env += env_from_s

            con_from_s = [t for t in self.con_transitions if t.src == s]
            con_stutter_from_s = stutter_transition(self, s, False)
            if con_stutter_from_s != None:
                con_from_s += [con_stutter_from_s]
            complete_con += con_from_s

        return complete_env, complete_con

    def complete_action_set(self, actions: [BiOp]):
        non_updated_vars = [tv.name for tv in self.valuation if tv.name not in [str(act.left) for act in actions]]
        return actions + [BiOp(Variable(var), ":=", Variable(var)) for var in non_updated_vars]

    def __str__(self):
        return str(self.to_dot())
    
    @classmethod
    def of_dsl(cls, file_name: str, code: str) -> "Program":
        """Parse a DSL program and return a Program"""
        
        tree = parse_dsl(code)
        symex_walker = SymexWalker()
        symex_walker.walk(tree)
        table = symex_walker.fp.get_root().table

        # All method parameters are treated as events
        events = {
            kind: [Variable(s.name) for s in table
                   if s.context.is_params and s.ast.parent.kind == kind]
            for kind in ("extern", "intern")}
        events["extern"].extend([Variable(s.symbol_name()) for s in symex_walker.env_choices.values()])  # noqa: E501
        events["intern"].extend([Variable(s.symbol_name()) for s in symex_walker.con_choices.values()])  # noqa: E501

        out_actions = [
            Variable(s.name) for s in table.symbols.values()
            if s.ast.io == "output"]
        init_values = [
            TypedValuation(s.name, str(s.type_).lower(), to_formula(s.init))
            for s in table.symbols.values()
            if s.ast.io != "output"]

        def _conjunct_smt(cond):
            return conjunct_formula_set(to_formula(c) for c in cond)

        def _disjunct_smt(cond):
            return disjunct_formula_set(to_formula(c) for c in cond)

        def triples_to_transitions(s0, triples_dict: dict):

            def _act_to_formula(act: dict):
                return [
                    BiOp(to_formula(lhs), "=", to_formula(rhs))
                    for lhs, rhs in act.items()]

            def _variables(out):
                return [Variable(x.symbol_name()) for x in out]

            transitions = [
                Transition(s0, _conjunct_smt(cond), _act_to_formula(act), _variables(out), s0)
                for method_triples in triples_dict.values()
                for (cond, act, out) in method_triples]
            return transitions

        s0, s_con_wins, s_con_loses = 's0', 's_con_wins', 's_con_loses'

        env_ts = triples_to_transitions(s0, symex_walker.extern_triples)
        con_ts = triples_to_transitions(s0, symex_walker.intern_triples)
        # Environment stutter
        # if symex_walker.extern_assumes:
        #     env_ts.append(Transition(
        #         s0, _conjunct_smt(Not(x) for x in symex_walker.extern_assumes),
        #         [], [], s0
        #     ))
        # # Controller stutter
        # if symex_walker.intern_assumes:
        #     con_ts.append(Transition(
        #         s0, _conjunct_smt(Not(x) for x in symex_walker.intern_assumes),
        #         [], [], s0))

        # Go to winning/losing state if any assertion is violated
        def add_assert_violations(choices, asserts, ts, sink):
            for method in choices:
                if asserts.get(method):
                    assertion = Or(Not(x) for x in asserts[method])
                    ind = symex_walker.one_hot(method, choices)
                    ind.append(assertion)
                    assertion = And(ind)
                    assertion = to_formula(assertion)
                    ts.append(Transition(s0, assertion, [], [], sink))

        add_assert_violations(symex_walker.env_choices, symex_walker.extern_asserts, env_ts, s_con_wins)
        add_assert_violations(symex_walker.con_choices, symex_walker.intern_asserts, con_ts, s_con_loses)

        # Guarantee only one method is chosen
        def add_mutex_guarantee(choices, ts, sink):
            if len(choices) > 1:
                dnf = (And(x, y) for x, y in combinations(choices.values(), 2))
                ts.append(Transition(s0, _disjunct_smt(dnf), [], [], sink))

        add_mutex_guarantee(symex_walker.env_choices, env_ts, s_con_wins)
        add_mutex_guarantee(symex_walker.con_choices, con_ts, s_con_loses)

        prg = Program(
            file_name, [s0, s_con_wins, s_con_loses], s0, init_values,
            env_ts, con_ts,
            env_events=events["extern"], con_events=events["intern"],
            out_events=out_actions)
        return prg
