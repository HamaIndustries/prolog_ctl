:- use_module(library(lists)).
% label(State, Proposition)
% transition(S1, S2)
% terminal nodes loop back to themselves

:- discontiguous entails/2.
:- discontiguous entails_/3.

:- multifile label/2.
:- multifile transition/2.

%%% --------------------- Logic --------------------- %%%
%% loop checking
nmem(Element, List) :- not(member(Element, List)).
accumulate(S1, S2, C, [S2|C]) :-
    transition(S1, S2), nmem(S2, C).
follows(S1, S2) :-
    follows_(S1, S2, []).
follows_(S1, S2, C) :-
    transition(S1, S2);
    accumulate(S1, Si, C, C2), follows_(Si, S2, C2).
terminal(S) :-
    transition(S, S2), not(S \== S2).

%% ctl rules
% tautology
entails(_, ctl_true) :- !, true.
entails(_, ctl_false) :- !, false.

% proposition
entails(S, p(P)) :- entails(S, proposition(P)).
entails(S, proposition(P)) :- label(S, proposition(P)).

% negation
entails(S, ctl_not(P)) :- not(entails(S, P)).

% connectives
entails(S, or(P1, P2)) :- entails(S, P1); entails(S, P2).
entails(S, and(P1, P2)) :- entails(S, P1), entails(S, P2).
entails(S, implies(P1, P2)) :- entails(S, or(P2, ctl_not(P1))).
entails(S, iff(P1, P2)) :- entails(S, or(
    and(P1, P2),
    and(ctl_not(P1), ctl_not(P2))
)).

% quantifiers
entails(S, ex(P)) :- transition(S, S2), entails(S2, P).
entails(S, ax(P)) :- not(entails(S, ex(ctl_not(P)))).

% exists
entails(S, ef(P)) :-
    entails(S, P);
    follows(S, S2), entails(S2, P).
entails(S, eg(P)) :- entails_(S, eg(P), []).
entails_(S, eg(P), C) :-
    entails(S, P), (
        terminal(S);
        accumulate(S, S2, C, C2), entails_(S2, eg(P), C2)
    ).
entails(S, eu(P1, P2)) :-
    entails(S, or(P2, and(P1, ex(eu(P1, P2))))).

% all
entails(S, ag(P)) :- entails(S, ctl_not(ef(ctl_not(P)))).
entails(S, af(P)) :- entails(S, ctl_not(eg(ctl_not(P)))).
entails(S, au(P1, P2)) :- entails(S, or(P2, and(P1, ax(au(P1, P2))))).


