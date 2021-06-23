
verify(InputFileName) :- see(InputFileName),
read(Prems), read(Goal), read(Proof), seen,
valid_proof(Prems, Goal, Proof), testGoal(Goal, Proof).

% Check whether the proof actually ends with the goal. 
 lastElement(A,A).
 lastElement(A,[X]) :- nth(2,X,B), nth(3,X,C), C \= assumption, lastElement(A,B).
 lastElement(A,[_|Y]) :- lastElement(A,Y).

testGoal(Goal, Proof) :-
  lastElement(Goal, Proof).

valid_proof(Prems, Goal, Proof) :-
checkProof(Proof, Prems, Proof).

last1([Y],Y).
last1([],Y).
last1([T|V],Y) :- last1(V,Y).


checkProof([], _, _).


checkProof([[[N,P,assumption]|Y]|Y2], Prems, Proof) :-
  checkBox([[N,P,assumption]|Y],Prems,Proof), last1(Y,LastInBox), 
  append(Proof,[LastInBox],Proof1), append(Proof1,[[N,P,assumption]],Proof2),
  checkProof(Y2,Prems,Proof2). 

checkProof([H|T], Prems, Proof) :- nth(3,H,X),
 checkPremise(X,H,Prems, Proof), checkProof(T,Prems, Proof).

checkBox([],_,_).


checkBox([[[N,P,assumption]|Y]|Y2], Prems, Proof) :-
   checkProof([[[N,P,assumption]|Y]|Y2], Prems, Proof).




checkBox([H|T], Prems,Proof) :- nth(3,H,X), 
checkPremise(X,H,Prems,Proof),append(Proof,[H],Proof2),
checkBox(T,Prems,Proof2).


% assumptions are always correct
checkPremise(assumption,H,_,Proof) :- nth(1,H,A), nth(A,Proof,Box).


% check if the neg int is correct 
checkPremise(negint(X,Y),H,_, Proof) :- 
  findLine(X,Proof,N), %  N = p
  nth(2,H,neg(N)), %Negated = neg(p)
  findLine(Y,Proof,M), M == cont.

%andelimination1
checkPremise(andel1(X),H,_, Proof) :- 
  nth(2,H,C),
  findLine(X,Proof,and(C,_)).


%andelimination2
checkPremise(andel2(X),H,_, Proof) :- 
  nth(2,H,Anded), %Anded = p
  nth(X,Proof,A), nth(2,A,and(_,Anded)).

%and introduction
checkPremise(andint(X,Y),H,_, Proof) :-
  nth(1,H,S), S>Y,S>X, 
  findLine(X,Proof,A),
  findLine(Y,Proof,B),
  nth(2,H,and(A,B)).
  


%MT unsure
checkPremise(mt(X,Y),H,_, Proof) :-
  nth(1,H,S), S>Y,S>X,
  nth(2,H,neg(F)),
  findLine(Y,Proof,neg(G)),
  findLine(X,Proof,M), M==imp(F,G).


% Checks if lem is true
checkPremise(lem,H,_, Proof) :-
nth(2,H,or(A,neg(A))).


%pbc
checkPremise(pbc(X,Y),H,_, Proof) :-
nth(1,H,S), S>Y,S>X,
nth(2,H,F),
findLine(X,Proof,neg(F)),
findLine(Y,Proof,M), M==cont.

% Checks if contel is true
checkPremise(contel(X),H,_,Proof):-
  nth(1,H,S), S>X,
  nth(X,Proof,A), nth(2,A,cont).

%Checks if negnegel is true

checkPremise(negnegel(X),H,_,Proof):-
  nth(1,H,S), S>X,
  nth(X,Proof,A),
  nth(2,H,Negneg),
  nth(2,A,neg(neg(Negneg))).

% Checks if negnegint is true
checkPremise(negnegint(X),H,_,Proof):-
  nth(1,H,S), S>X,
  nth(X,Proof,A),
  nth(2,A,Unneg),
  nth(2,H,neg(neg(Unneg))).


%or elimination
checkPremise(orel(A,B,C,D,E),H,_,Proof):-
  nth(1,H,S), S>A,S>B,S>C,S>D,S>E,
  findLine(A,Proof,or(F,G)),
  findLine(B,Proof,F),
  findLine(D,Proof,G),
  nth(2,H,Res),
  findLine(C,Proof,Res),
  findLine(E,Proof,Res).




% Check if the copy is correct
checkPremise(copy(X),H, _, Proof) :- 
  nth(1,H,S), S>X,
  nth(X, Proof, A), 
  nth(2,A,Ori),
  nth(2,H,Cop), Ori==Cop.

% Check if the premise is actually in the premises
checkPremise(premise,H, Prems, _) :- nth0(1,H,Y), member(Y, Prems).

% Checks if impel is correct
checkPremise(impel(X,Y), H, _, Proof) :- nth(2,H,C), 
nth(1,H,S), S>X, S>Y,
findLine(X, Proof, A),
findLine(Y,Proof,B),
(imp(A,C) == B;imp(C,A)==B; imp(C,B) ==A; imp(B,C)==A),!.

% Checks if impint is correct
checkPremise(impint(X,Y),H,_,Proof) :-
  nth(1,H,S), S>X, S>Y,
  findLine(X,Proof,A),
  findLine(Y,Proof,B),
  nth(2,H,imp(A,B)).


% Checks if negel is correct
checkPremise(negel(X,Y),H,_, Proof) :-
  nth(1,H,S), S>X, S>Y, 
  findLine(X,Proof,N), findLine(Y,Proof,neg(N)).
  

imp(A,B).
neg(A) :- not(A).
and(A,B) :- A,B.


% Finds the right line
findLine(I,[[I,B,C]|_],B). 
findLine(I,[_|Y],R) :- findLine(I,Y,R).


