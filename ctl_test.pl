:- use_module(library(lists)).
:- ensure_loaded(ctl).

:- discontiguous transition/2.
:- discontiguous label/2.

%%% ----------------- Verification Models ----------------- %%%
% Create a set of 2-tiered full and complete binary trees:
%$ v_tree(Id, [V1, V2, V3, V4, V5, V6, V7]).
% all-empty tree
v_tree(empty, [0, 0, 0, 0, 0, 0, 0]).

% all-full tree
v_tree(full, [1, 1, 1, 1, 1, 1, 1]).

% tree with single full state (leaf node 5)
v_tree(one_full, [0, 0, 0, 0, 1, 0, 0]).

% tree with one branch full
v_tree(branch_full, [1, 0, 1, 0, 0, 1, 0]).

% tree with single empty state (leaf node 5)
v_tree(one_empty, [1, 1, 1, 1, 0, 1, 1]).

% tree with one branch empty
v_tree(branch_empty, [0, 1, 0, 1, 1, 0, 1]).

v_transition(S1, S2) :-
	nth1(S1, [[2, 3],[4, 5],[6, 7]], T), member(S2, T);
	S1 = S2, member(S1, [4, 5, 6, 7]).

transition(v_state(Id, S1), v_state(Id, S2)) :- v_transition(S1, S2).

label(v_state(Id, S), proposition(full)) :- v_tree(Id, Vs), nth1(S, Vs, 1).
label(v_state(Id, S), proposition(empty)) :- v_tree(Id, Vs), nth1(S, Vs, 0).


%%% ----------------- Verification Model Testing ----------------- %%%
test_formulae([
	ax(proposition(full)),
	ax(proposition(empty)),
	ex(proposition(full)),
	ex(proposition(empty)),
	ag(proposition(full)),
	ag(proposition(empty)),
	eg(proposition(full)),
	eg(proposition(empty)), %
	af(proposition(full)),
	af(proposition(empty)),
	ef(proposition(full)),
	ef(proposition(empty))
]).

test_all_formulae(_, [], [], []).
test_all_formulae(State, [Expect | Erest], [Formula | Frest], [Result | Rrest]) :-
	test(entails(State, Formula), Expect, Result),
	test_all_formulae(State, Erest, Frest, Rrest).

test(Predicate, true, pass) :- Predicate.
test(Predicate, false, pass) :- not(Predicate).
test(Predicate, true, fail) :- not(Predicate).
test(Predicate, false, fail) :- Predicate.

test_tree(State, Expects, Results) :-
	test_formulae(Formulae), 
	test_all_formulae(State, Expects, Formulae, Results), !.

test_tree(State, Expects) :-
	test_tree(State, Expects, Results),
	not(member(fail, Results)).

% main entry point for testing a given tree.
% ensure that test_vals are set, and provide the desired tree id to test.
% runs all test propositions centered at the root.
test(Id, R) :- test_vals(Id, Vs), test_tree(v_state(Id, 1), Vs, R).
test(Id) :- test_vals(Id, Vs), test_tree(v_state(Id, 1), Vs).

test_vals(empty, [false, true, false, true, false, true, false, true, false, true, false, true]).
test_vals(full, [true, false, true, false, true, false, true, false, true, false, true, false]).
test_vals(one_empty, [true, false, true, false, false, false, true, false, true, false, true, true]).
test_vals(one_full, [false, true, false, true, false, false, false, true, false, true, true, true]).
test_vals(branch_empty, [false, false, true, true, false, false, false, true, false, true, true, true]).
test_vals(branch_full, [false, false, true, true, false, false, true, false, true, false, true, true]).

%% basic operator testing
label(test_state, proposition(test)).

test_proposition :-
	entails(test_state, p(test)).

test_tautology :-
	entails(_, ctl_true),
	not(entails(_, ctl_false)).

test_not :- 
	entails(_, ctl_not(ctl_false)),
	not(entails(_, ctl_not(ctl_true))).

test_and :-
	entails(_, and(ctl_true, ctl_true)),
	not(entails(_, and(ctl_true, ctl_false))),
	not(entails(_, and(ctl_false, ctl_true))),
	not(entails(_, and(ctl_false, ctl_false))).
	
test_or :-
	entails(_, or(ctl_true, ctl_true)),
	entails(_, or(ctl_true, ctl_false)),
	entails(_, or(ctl_false, ctl_true)),
	not(entails(_, or(ctl_false, ctl_false))).
	
test_implies :-
	entails(_, implies(ctl_true, ctl_true)),
	not(entails(_, implies(ctl_true, ctl_false))),
	entails(_, implies(ctl_false, ctl_true)),
	entails(_, implies(ctl_false, ctl_false)).

test_iff :-
	entails(_, iff(ctl_true, ctl_true)),
	not(entails(_, iff(ctl_true, ctl_false))),
	not(entails(_, iff(ctl_false, ctl_true))),
	entails(_, iff(ctl_false, ctl_false)).

test_operators :-
	test_tautology,
	test_proposition,
	test_not,
	test_and,
	test_or,
	test_implies,
	test_iff.

%% global test command
test_suite :-
	test_operators,
	test(empty),
	test(full),
	test(one_empty),
	test(one_full),
	test(branch_empty),
	test(branch_full).


%%% --------------------- Complex Tree Example --------------------- %%%
state(complex, q1, 0, 1).
state(complex, q2, 0, 1).
state(complex, q3, 0, 1).
state(complex, q4, 1, 1).
state(complex, q5, 1, 0).
state(complex, q6, 1, 0).
state(complex, q7, 1, 0).

transition(complex_state(S1), complex_state(S2)) :-
	c_transition(complex, S1, S2).
c_transition(complex, q1, q2).
c_transition(complex, q1, q3).
c_transition(complex, q2, q4).
c_transition(complex, q2, q5).
c_transition(complex, q3, q5).
c_transition(complex, q3, q6).
c_transition(complex, q3, q7).
c_transition(complex, q4, q4).
c_transition(complex, q5, q5).
c_transition(complex, q6, q6).
c_transition(complex, q7, q7).
c_transition(complex, q6, q1).

label(complex_state(State), proposition(red))  :- state(complex, State, 1, _).
label(complex_state(State), proposition(blue))  :- state(complex, State, _, 1).
