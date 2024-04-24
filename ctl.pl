%% A transition system M is a triple M = (S, t*, L) where
%	* S is the set of states
%	* t* \subset S x S is a transition relation between states, where each state has at least one successor
%	* L is a labelling function applying propositional letters to states.
%	* \phi \in F where F is the set of well-formed formulas over M.

% We treat prolog's database as containing the relations defining M. That is, a model is definied by a 
% unique set of states with transitions between them, and a label relationship connecting states to propositions
% wherever the state's properties obey the proposition's requirements.

% Unlike mathematical CTL, this system analyzes models of computation trees represented as finite DAGs.
% Semantic entailment is evaluated starting from the root node specified and expanding forward as needed.

%% definitions required for a model:
% transition(S1, S2).
% label(State, Proposition).
% definitions of state are user-defined.

follows(State, S1) :-
	transition(State, S1);
	transition(State, S0), follows(S0, S1).

end_state(S) :- not(transition(S, _)).

%% Semantic entailment is defined recursively on \phi
% entails(State, Formula)

% 1 tautologies
entails(_, ctl_false) :- false.
entails(_, ctl_true) :- true.

% 2 propositions
entails(State, proposition(P)) :- 
	label(State, P).
entails(State, p(P)) :- entails(State, proposition(P)).

% 3 not
entails(State, ctl_not(F)) :-
	not(entails(State, F)).

% 4 and
entails(State, ctl_and(F1, F2)) :-
	entails(State, F1), entails(State, F2).

% 5 or
entails(State, ctl_or(F1, F2)) :-
	entails(State, F1); entails(State, F2).

% 6 implies
entails(State, ctl_implies(F1, F2)) :-
	entails(State, ctl_not(F1));
	entails(State, F2).

% 7 iff
entails(State, ctl_iff(F1, F2)) :-
	entails(State, ctl_and(F1, F2));
	entails(State, ctl_and(ctl_not(F1), ctl_not(F2))).

% 8 AX
entails(State, ctl_AX(F)) :-
	not(end_state(State)), not(entails(State, ctl_EX(ctl_not(F)))).

% 9 EX
entails(State, ctl_EX(F)) :-
	transition(State, S1), entails(S1, F).

% 10 AG
entails(State, ctl_AG(F)) :-
	entails(State, F), end_state(State);                                   % F is true and this is the end, or
	entails(State, ctl_and(F, ctl_AX(ctl_AG(F)))).                         % F is true and AG(F) for all next states

% 11 EG
entails(State, ctl_EG(F)) :-
	entails(State, F), end_state(State);                                  % F is true and this is the end, or
	entails(State, ctl_and(F, ctl_EX(ctl_EG(F)))).                        % F is true and EG(F) for some next state
 
% 12 AF
entails(State, ctl_AF(F)) :-
	entails(State, ctl_or(F, ctl_AX(ctl_AF(F)))).

% 13 EF
entails(State, ctl_EF(F)) :-
	entails(State, F);                                                   % F is true here, or
	follows(State, S1), entails(S1, F).                                  % There is a state after this where F is true.

% 14 A[ U ]
entails(State, ctl_AU(F1, F2)) :-
	entails(State, ctl_or(F2, ctl_and(F1, ctl_AX(ctl_AU(F1, F2))))).

% 15 E[ U ]
entails(State, ctl_EU(F1, F2)) :-
	entails(State, ctl_or(F2, ctl_and(F1, ctl_EX(ctl_EU(F1, F2))))).

/*
entails(State, ctl_EU(F1, F2)) :-
	entails(State, ctl_and(F1, ctl_or(    % F1 is true at this state and either
		ctl_EX(F2),                   % - F2 is true next, or
		ctl_EX(ctl_EU(F1, F2)         % - F1 is true next until F2
	)))).
*/













