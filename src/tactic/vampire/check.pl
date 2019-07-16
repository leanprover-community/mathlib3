:- [misc].

subst(Maps, var(Num), var(Num)) :-
  not(member(map(Num, _), Maps)).

subst(Maps, var(Num), Trm) :-
  member(map(Num, Trm), Maps).

subst(_, sym(Num), sym(Num)).

subst(Maps, app(Trm1, Trm2), app(NewTrm1, NewTrm2)) :-
  subst(Maps, Trm1, NewTrm1),
  subst(Maps, Trm2, NewTrm2).

subst(Map, lit(Pol, Trm1), lit(Pol, Trm2)) :-
  subst(Map, Trm1, Trm2).

subst(Maps, Cla, NewCla) :-
  maplist(subst(Maps), Cla, NewCla).

check(Mat, LPrf, success) :-
  string_codes(LPrf, Prf),
  check(Mat, [], Prf).

check(Mat, LPrf, fail(Mat, LPrf)).

check(_, [cla([])], []).

check(Mat, Stk, [110 | Prf]) :-
  check(Mat, [num(0) | Stk], Prf).

check(Mat, [num(Num) | Stk], [48 | Prf]) :-
  NumA is Num * 2,
  check(Mat, [num(NumA) | Stk], Prf).

check(Mat, [num(Num) | Stk], [49 | Prf]) :-
  NumA is ((Num * 2) + 1),
  check(Mat, [num(NumA) | Stk], Prf).

check(Mat, [maps(Maps), num(Num) | Stk], [97 | Prf]) :-
  nth0(Num, Mat, Cla),
  subst(Maps, Cla, Cnc),
  check(Mat, [cla(Cnc) | Stk], Prf).

check(Mat, [cla([lit(pos, Trm) | ClaB]), cla([lit(neg, Trm) | ClaA]) | Stk], [114 | Prf]) :-
  append(ClaA, ClaB, Cnc),
  check(Mat, [cla(Cnc) | Stk], Prf).

check(Mat, [cla(Cla), num(Num) | Stk], [116 | Prf]) :-
  rot(Num, Cla, Cnc),
  check(Mat, [cla(Cnc) | Stk], Prf).

check(Mat, [cla([Lit, Lit | Cla]) | Stk], [99 | Prf]) :-
  check(Mat, [cla([Lit | Cla]) | Stk], Prf).

check(Mat, Stk, [101 | Prf]) :-
  check(Mat, [maps([]) | Stk], Prf).

check(Mat, [num(Num) | Stk], [115 | Prf]) :-
  check(Mat, [trm(sym(Num)) | Stk], Prf).

check(Mat, [trm(TrmB), trm(TrmA) | Stk], [112 | Prf]) :-
  check(Mat, [trm(app(TrmA, TrmB)) | Stk], Prf).

check(Mat, [trm(Trm), num(Num), maps(Maps) | Stk], [109 | Prf]) :-
  check(Mat, [maps([map(Num, Trm) | Maps]) | Stk], Prf).


% check0(Mat, Stk, Infs, [Stk | Trc]) :-
%   check1(Mat, Stk, Infs, Trc).
%
% check1(_, _, [], []).
%
% check1(Mat, Stk, [num(Num) | Infs], Trc) :-
%   check0(Mat, [num(Num) | Stk], Infs, Trc).
%
% check1(Mat, [num(Num) | Stk], [hyp | Infs], Trc) :-
%   nth0(Num, Mat, Cla),
%   check0(Mat, [Cla | Stk], Infs, Trc).
%
% check1(Mat, [[lit(pos, Trm) | ClaB], [lit(neg, Trm) | ClaA] | Stk], [res | Infs], Trc) :-
%   append(ClaA, ClaB, Cla),
%   check0(Mat, [Cla | Stk], Infs, Trc).
%
% check1(Mat, [num(Num), Cla | Stk], [rot | Infs], Trc) :-
%   rot(Num, Cla, Cla1),
%   check0(Mat, [Cla1 | Stk], Infs, Trc).
%
% check1(Mat, [Maps, Cla | Stk], [sub | Infs], Trc) :-
%   subst(Maps, Cla, Cla1),
%   check0(Mat, [Cla1 | Stk], Infs, Trc).
%
% check1(Mat, [[Lit, Lit | Cla] | Stk], [cont | Infs], Trc) :-
%   check0(Mat, [[Lit, Cla] | Stk], Infs, Trc).
%
% check1(Mat, Stk, [nil | Infs], Trc) :-
%   check0(Mat, [[] | Stk], Infs, Trc).
%
% check1(Mat, [num(Num) | Stk], [sym | Infs], Trc) :-
%   check0(Mat, [sym(Num) | Stk], Infs, Trc).
%
% check1(Mat, [num(Num) | Stk], [var | Infs], Trc) :-
%   check0(Mat, [var(Num) | Stk], Infs, Trc).
%
% check1(Mat, [TrmB, TrmA | Stk], [app | Infs], Trc) :-
%   check0(Mat, [app(TrmA, TrmB) | Stk], Infs, Trc).
%
% check1(Mat, [Trm, num(Num), Maps | Stk], [cons | Infs], Trc) :-
%   check0(Mat, [[map(Num, Trm) | Maps] | Stk], Infs, Trc).
