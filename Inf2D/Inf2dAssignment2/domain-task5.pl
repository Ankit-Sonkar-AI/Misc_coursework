% ---------------------------------------------------------------------
%  ----- Informatics 2D - 2011/12 - Second Assignment - Planning -----
% ---------------------------------------------------------------------
%
% Write here you matriculation number (only - your name is not needed)
% Matriculation Number: s1024819
%
%
% ------------------------- Domain Definition -------------------------
% This file describes a planning domain: a set of predicates and
% fluents that describe the state of the system, a set of actions and
% the axioms related to them. More than one problem can use the same
% domain definition, and therefore include this file


% --- Cross-file definitions ------------------------------------------
% marks the predicates whose definition is spread across two or more
% files
%
:- multifile adjacent/2, moveable/3, empty/2, at/3, resting/2.

% --- Primitive control actions ---------------------------------------
% this section defines the name and the number of parameters of the
% actions available to the planner
%
% primitive_action( dosomething(_,_) ).	% underscore means `anything'


primitive_action(move(_,_)).
primitive_action(push(_,_,_,_)).
primitive_actio(rest(_)).


% --- Precondition for primitive actions ------------------------------
% describe when an action can be carried out, in a generic situation S
%
% poss( doSomething(...), S ) :- preconditions(..., S).

poss(move(Start, Dest), S) :-
  not(Start==Dest),
  at(agent, Start, S),
  adjacent(Start, Dest),
  empty(Dest,S).

poss( push(AgentPos , CratePos, CrateDest, a), S ) :-
  moveable(AgentPos, CratePos, CrateDest),
  at(agent,AgentPos, S),
  at(a, CratePos, S),
  empty(CrateDest,S).

poss( push(AgentPos , CratePos, CrateDest, b), S ) :-
  moveable(AgentPos, CratePos, CrateDest),
  at(agent,AgentPos, S),
  at(b, CratePos, S),
  empty(CrateDest,S).

poss( push(AgentPos , CratePos, CrateDest, c), S ) :-
  moveable(AgentPos, CratePos, CrateDest),
  at(agent,AgentPos, S),
  at(c, CratePos, S),
  empty(CrateDest,S).

poss( rest(Location), S) :-
  at(Location, S).

% --- Successor state axioms ------------------------------------------
% describe the value of fluent based on the previous situation and the
% action chosen for the plan. 
%
% fluent(..., result(A,S)) :- positive; previous-state, not(negative)

at(agent, Dest, result(A, S)) :-
  A = move(_, Dest);
  A = push(_, Dest, _, _);
  A = rest(Dest);
  at(agent, Dest, S),
  not(A = move(Dest,_)),
  not(A = push(Dest,_, _, _)).

resting(Dest, result(A, S)) :-
  A = push(_, _, Dest, _);
  at(agent,Dest,S),
  not(A = move(Dest, _)),
  not(A = push(_, Dest,_, _)).

at(a, Dest, result(A,S)) :-
  A = push(_, _, Dest, a);
  at(a,Dest,S),
  not(A = push(_,Dest, _, a)),
  not(A = rest(Dest)).

at(b, Dest, result(A,S)) :-
  A = push(_, _, Dest, b);
  at(b,Dest,S),
  not(A = rest(Dest)),
  not(A = push(_,Dest, _, b)).

at(c, Dest, result(A,S)) :-
  A = push(_, _, Dest, c);
  at(c,Dest,S),
  not(A = rest(Dest)),
  not(A = push(_,Dest, _,c)).

empty(Location, result(A,S)) :-
  A = move(Location, _);
  A = push(Location, _,_, _);
  A = rest(Location);
  empty(Location, S), not(A=move(_, Location)), not(A=push(_,_,Location,_)).

% ---------------------------------------------------------------------
% ---------------------------------------------------------------------
