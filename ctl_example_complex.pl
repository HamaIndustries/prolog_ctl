:- use_module(library(lists)).
:- ensure_loaded(ctl).

state(q1, vars(0, 1)).
state(q2, vars(0, 1)).
state(q3, vars(0, 1)).
state(q4, vars(1, 1)).
state(q5, vars(1, 0)).
state(q6, vars(1, 0)).
state(q7, vars(1, 0)).

transition(S1, S2) :- 
	ls_transitions(S1, L),
	member(S2, L).

ls_transitions(q1, [q2, q3]).
ls_transitions(q2, [q4, q5]).
ls_transitions(q3, [q5, q6, q7]).
transition(q6, q2).

label(State, red) :- 
	state(State, vars(1, _)).
label(State, blue) :-
	state(State, vars(_, 1)).

