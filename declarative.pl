% This is a quick prototype of the declarative type system,
% as written on the whiteboard June 2.

% Terms and types are represented as Prolog terms like this:
%   Term ::= var(Name)
%          | app(Term,Term)
%          | lam(Name,Body)
%          | let(Name,Binding,Body)
%
%   Type ::= arr(Type,Type)
%          | tyapp(Type,Type)
%          | name               %note I don't bother to tag it.
%
%   Scheme ::= forall([name;...], Type)   %note I omit the constraints for simplicity.
%
%   Gamma ::= [ass(Name,Type); ...] 


% We assume that we know which types count as monads, 
% and what morphisms are available.

isMonad(list).
isMonad(maybe).
isMonad(beh).   % The "behaviour" and
isMonad(prob).  % "probability" monads from the ICFP paper.
isMondad(behProb).

isMorphism(beh, behProb).
isMorphism(prob, behProb).

% Type checking and type synthesis judgements. I omit the  
%  constraints for simplity (they will be just hardcoded in the subtyping judgement).

synth(Gamma, app(E1,E2), M, tyapp(M,T12)) :-
  synth(Gamma, E1, M, T1),
  subtype(T1, tyapp(M, arr(T11, tyapp(M, T12)))),
  check(Gamma, E2, M, tyapp(M, T11)).

% The variable rule is omitted for now, we can hardcode
% the particular things used by the examples...

check(Gamma, E, M, T2) :-
  synth(Gamma,E, M, T1),
  subtype(T1, T2).

% The subtyping judgement. 
% To avoid getting stuck in a loop, this is defined in terms of
% a version with restricted depth of the derivation.
subtype(T1,T2) :- subtype_k(3, T1,T2).


% refl
subtype_k(_K, T, T).
 
% eta
subtype_k(K, arr(T1,T21), arr(T1,T22)) :-
  K > 0, K1 is K-1,
  subtype_k(K1, T21, T22).

% return
subtype_k(K, T1, tyapp(M,T2)) :-
  K > 0, K1 is K-1,
  isMonad(M),
  subtype_k(K1, T1,T2).

% lift 
subtype_k(K, tyapp(N,T1), tyapp(M,T2)) :-
  K > 0, K1 is K-1,
  isMorphism(N,M),
  subtype_k(K1, T1,T2).

% trans. 
% But let's omit this for now, since it is not very algorithmic.
%subtype(T1,T3) :-
%  subtype(T1,T2),
%  subtype(T2,T3).

%% Examples!


% Here are the primitives that were used in the whiteboard example.
synth(_, if, _M, arr(A,arr(A,A))).
synth(_, nothing, _M, tyapp(maybe,_A)).
synth(_, nil, _M, tyapp(list,_A)).

% Here are the primitives that are used in the ICFP paper example.
synth(_, seconds, _M, tyapp(beh, int)).
synth(_, flip, _M, arr(float, tyapp(prob, bool))).
synth(_, fail, _M, tyapp(prob, _A)).

example1(T) :- synth([], app(app(if, nil), nothing), maybe, T).
example2(T) :- synth([], app(app(if, nil), nothing), list, T).
