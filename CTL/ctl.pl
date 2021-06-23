use_module(library(lists)).

% Load model, initial state and formula from file.
verify(Input) :- see(Input), read(T), read(L), read(S), read(F), seen, check(T, L, S, [], F).


% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.
%
% Should evaluate to true iff the sequent below is valid.
%
% (T,L), S |- F
% U

% Neg
check(_,L,S,[], neg(X)) :- find(S,L,D), \+member(X,D).

% And
check(T, L, S, [], and(F,G)) :- check(T,L,S,[],F), check(T,L,S,[],G).

% Or
check(T, L, S, [], or(F,G)) :- check(T,L,S,[],F); check(T,L,S,[],G).

% AX
check(T,L,S,[],ax(F)) :-  find(S,T,D), !, checkax(T,L,D,[],F).

% EX
check(T,L,S,[],ex(F)) :- find(S,T,D), !, checkex(T,L,D,[],F).

% AG
check(T,L,S,[],ag(F)) :- check(T,L,S,[],F), find(S,T,D), !, checkag(T,L,D,[S],F).

% EG
check(T,L,S,[],eg(F)) :- check(T,L,S,[],F), find(S,T,D), !, checkeg(T,L,D,[S],F).

% EF
check(T,L,S,[],ef(F)) :- check(T,L,S,[],F) ; find(S,T,D), !, checkef(T,L,D,[S],F).

% AF
check(T,L,S,[],af(F)) :- check(T,L,S,[],F) ;  find(S,T,D), !, checkaf(T,L,D,[S],F).

% Literal
check(_,L,S,[],X) :- find(S,L,P), !, member(X,P).


% Helpers for the rules functions that all use the empty list as a base case with the exception of EX. If we return to a state already visited that state is checked and also stops the recursion.
% AX helper, goes through all adjacent states and verifies that they are true.
checkax(_,_,[],[],_) :- true.
checkax(T,L,[S1|S2],[],X) :- check(T,L,S1,[],X), checkax(T,L,S2,[],X).

% EX helper, goes through all adjacent states and verifies that at least one is true.
checkex(T,L,[S1|S2],[],X) :- (check(T,L,S1,[],X); checkex(T,L,S2,[],X)).

% AG helper, goes through all possible states depth first until reaching one of the base cases then proceeds to the next branch and verifies that all states are true.
checkag(_,_,[],_,_) :- true.
checkag(T,L,[S1|S2],U,X) :- member(S1,U), !, check(T,L,S1,[],X), checkag(T,L,S2,U,X).
checkag(T,L,[S1|S2],U,X) :- check(T,L,S1,[],X), append([S1],U,N), find(S1,T,D), !, checkag(T,L,D,N,X), checkag(T,L,S2,N,X).

% EG helper, goes through all possible states depth first until reaching one of the base cases or until it encouters a false state, then proceeds to the next branch. Verifies that there is a path where all states are true.
checkeg(_,_,[],_,_) :- false.
checkeg(T,L,[S1|S2],U,X) :- member(S1,U), !, check(T,L,S1,[],X); checkeg(T,L,S2,U,X).
checkeg(T,L,[S1|S2],U,X) :- check(T,L,S1,[],X), append([S1],U,N), find(S1,T,D), !, checkeg(T,L,D,N,X); checkeg(T,L,S2,U,X).

% EF helper, goes through all possible states depth first until reaching one of the base cases or until it encouters a false state, then proceeds to the next branch. Verifies that there is a path where one state is true.
checkef(_,_,[],_,_) :- false.
checkef(T,L,[S1|_],U,X) :- checkeflast(T,L,S1,U,X).
checkef(T,L,[S1|_],_,X) :- check(T,L,S1,[],X).
checkef(T,L,[S1|S2],U,X) :- \+member(S1,U), append([S1],U,N), find(S1,T,D), checkef(T,L,D,N,X) ; checkef(T,L,S2,U,X).

checkeflast(T,L,S1,U,X) :- member(S1,U), !, check(T,L,S1,[],X).

% AF helper, goes through all possible states depth first until reaching one of the base cases or until it encouters a false state, then proceeds to the next branch. Verifies that all paths has one state that is true.
checkaf(_,_,[],_,_) :- true.
checkaf(T,L,[S1|S2],U,X) :- member(S1,U), !, check(T,L,S1,[],X), checkaf(T,L,S2,U,X).
checkaf(T,L,[S1|S2],U,X) :- check(T,L,S1,[],X), append([S1],U,N), checkaf(T,L,S2,N,X).
checkaf(T,L,[S1|S2],U,X) :- append([S1],U,N), find(S1,T,D), !, checkaf(T,L,D,N,X), checkaf(T,L,S2,N,X).


% Help function that extracts the relevant list in either labeling or adjacency
find(H,[[H|[T]]|_],T).
find(H,[[_|_]|T],A) :- find(H,T,A).
