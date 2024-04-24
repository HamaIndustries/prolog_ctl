:- use_module(library(lists)).
:- ensure_loaded(ctl).

:- discontiguous state/2.
:- discontiguous transition/2.
:- discontiguous label/2.

%%% ----------------- Example Model ----------------- 
state(ss1, vars(a1, b1, c_unsafe)).
state(ss2_1, vars(a2, b1, c_unsafe)).
state(ss2_2, vars(a2, b1, c_safe)).
state(ss3_1, vars(a1, b2, c_unsafe)).
state(ss3_2, vars(a1, b2, c_safe)).

transition(ss1, ss2_1).
transition(ss1, ss3_1).
transition(ss2_1, ss2_2).
transition(ss3_1, ss3_2).

label(State, stop_ok) :-
	state(State, vars(_, _, c_safe)).

label(State, a2) :-
	state(State, vars(a2, _, _)).

label(State, b2) :-
	state(State, vars(_, b2, _)).

label(State, b1) :-
	state(State, vars(_, b1, _)).


%%% ----------------- Verification Models ----------------- 
% Create a set of 2-tiered full and complete binary trees:
% v_tree(Id, [V1, V2, V3, V4, V5, V6, V7], [S1, S2, S3, S4, S5, S6, S7]). 
state(S, V) :-
	v_tree(_, Vs, Ss),
	nth1(N, Vs, V),
	nth1(N, Ss, S).

transition(S1, S2) :-
	v_tree(_, _, S),
	nth1(N1, S, S1),
	nth1(N2, S, S2),
	vtree_transition(N1, N2).
vtree_transition(1, 2).
vtree_transition(1, 3).
vtree_transition(2, 4).
vtree_transition(2, 5).
vtree_transition(3, 6).
vtree_transition(3, 7).

label(State, full)  :- state(State, 1).
label(State, empty) :- state(State, 0).

entails(Id, N, Formula) :-
	v_tree(Id, _, S),
	nth1(N, S, State),
	entails(State, Formula).
	
%% all-empty tree
v_tree(empty, [0, 0, 0, 0, 0, 0, 0], [se1, se2, se3, se4, se5, se6, se7]).

%% all-full tree
v_tree(full, [1, 1, 1, 1, 1, 1, 1], [sf1, sf2, sf3, sf4, sf5, sf6, sf7]).

%% tree with single full state (leaf node 5)
v_tree(one_full, [0, 0, 0, 0, 1, 0, 0], [so1, so2, so3, so4, so5, so6, so7]).

%% tree with one branch full
v_tree(branch_full, [1, 0, 1, 0, 0, 1, 0], [sb1, sb2, sb3, sb4, sb5, sb6, sb7]).

%% tree with single empty state (leaf node 5)
v_tree(one_empty, [1, 1, 1, 1, 0, 1, 1], [soe1, soe2, soe3, soe4, soe5, soe6, soe7]).

%% tree with one branch empty
v_tree(branch_empty, [0, 1, 0, 1, 1, 0, 1], [sbe1, sbe2, sbe3, sbe4, sbe5, sbe6, sbe7]).


%%% ----------------- Verification Model Testing ----------------- 
test_formulae([
	ctl_AX(proposition(full)),
	ctl_AX(proposition(empty)),
	ctl_EX(proposition(full)),
	ctl_EX(proposition(empty)),
	ctl_AG(proposition(full)),
	ctl_AG(proposition(empty)),
	ctl_EG(proposition(full)),
	ctl_EG(proposition(empty)),
	ctl_AF(proposition(full)),
	ctl_AF(proposition(empty)),
	ctl_EF(proposition(full)),
	ctl_EF(proposition(empty))
]).

test_all_formulae(_, [], [], []).
test_all_formulae(I, [Expect | Erest], [Formula | Frest], [Result | Rrest]) :-
	test(entails(I, 1, Formula), Expect, Result),
	test_all_formulae(I, Erest, Frest, Rrest).

test(Predicate, true, pass) :- Predicate.
test(Predicate, false, pass) :- not(Predicate).
test(Predicate, true, fail) :- not(Predicate).
test(Predicate, false, fail) :- Predicate.

test_tree(Tree, Expects, Results) :-
	test_formulae(Formulae), 
	test_all_formulae(Tree, Expects, Formulae, Results), !.

test_tree(Tree, Expects) :-
	test_tree(Tree, Expects, Results),
	not(member(fail, Results)).

% main entry point for testing a given tree.
% ensure that test_vals are set, and provide the desired tree id to test.
% runs all test propositions centered at the root.
test(Id, R) :- test_vals(Id, Vs), test_tree(Id, Vs, R).
test(Id) :- test_vals(Id, Vs), test_tree(Id, Vs).

test_vals(empty, [false, true, false, true, false, true, false, true, false, true, false, true]).
test_vals(full, [true, false, true, false, true, false, true, false, true, false, true, false]).
test_vals(one_empty, [true, false, true, false, false, false, true, false, true, false, true, true]).
test_vals(one_full, [false, true, false, true, false, false, false, true, false, true, true, true]).
test_vals(branch_empty, [false, false, true, true, false, false, false, true, false, true, true, true]).
test_vals(branch_full, [false, false, true, true, false, false, true, false, true, false, true, true]).

%% basic operator testing

test_tautology :-
	entails(full, 1, ctl_true),
	not(entails(full, 1, ctl_false)).

test_proposition :-
	entails(full, 1, proposition(full)).

test_not :- 
	entails(full, 1, ctl_not(ctl_false)),
	not(entails(full, 1, ctl_not(ctl_true))).

test_and :-
	entails(full, 1, ctl_and(ctl_true, ctl_true)),
	not(entails(full, 1, ctl_and(ctl_true, ctl_false))),
	not(entails(full, 1, ctl_and(ctl_false, ctl_true))),
	not(entails(full, 1, ctl_and(ctl_false, ctl_false))).
	
test_or :-
	entails(full, 1, ctl_or(ctl_true, ctl_true)),
	entails(full, 1, ctl_or(ctl_true, ctl_false)),
	entails(full, 1, ctl_or(ctl_false, ctl_true)),
	not(entails(full, 1, ctl_or(ctl_false, ctl_false))).
	
test_implies :-
	entails(full, 1, ctl_implies(ctl_true, ctl_true)),
	not(entails(full, 1, ctl_implies(ctl_true, ctl_false))),
	entails(full, 1, ctl_implies(ctl_false, ctl_true)),
	entails(full, 1, ctl_implies(ctl_false, ctl_false)).

test_iff :-
	entails(full, 1, ctl_iff(ctl_true, ctl_true)),
	not(entails(full, 1, ctl_iff(ctl_true, ctl_false))),
	not(entails(full, 1, ctl_iff(ctl_false, ctl_true))),
	entails(full, 1, ctl_iff(ctl_false, ctl_false)).

test_operators :-
	test_tautology,
	test_proposition,
	test_not,
	test_and,
	test_or,
	test_implies,
	test_iff.

%% ------  global test command ------
test_suite :-
	test_operators,
	test(empty),
	test(full),
	test(one_empty),
	test(one_full),
	test(branch_empty),
	test(branch_full).
