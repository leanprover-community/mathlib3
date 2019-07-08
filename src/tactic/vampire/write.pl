:- [misc].

tptp_trm(app(Trm1, Trm2), Num, Strs) :-
  tptp_trm(Trm1, Num, TmpStrs),
  tptp_trm(Trm2, Str),
  append(TmpStrs, [Str], Strs).

tptp_trm(sym(Num), Num, []).

tptp_trm(var(Num), Str) :-
  number_string(Num, NumStr),
  string_concat("X", NumStr, Str).

tptp_trm(sym(Num), Str) :-
  number_string(Num, NumStr),
  string_concat("s", NumStr, Str).

tptp_trm(app(Trm1, Trm2), Rst) :-
  tptp_trm(Trm1, Num, Strs),
  number_string(Num, NumStr),
  tptp_trm(Trm2, Str),
  append(Strs, [Str], ArgStrs),
  join_string(ArgStrs, ",", ArgsStr),
  join_string(["s", NumStr, "(", ArgsStr, ")"], Rst).

tptp_lit(lit(neg, Trm), Str) :-
  tptp_trm(Trm, Tmp),
  string_concat("~ " , Tmp, Str).

tptp_lit(lit(pos, Trm), Str) :-
  tptp_trm(Trm, Str).

tptp_cla(Cla, Idx, Str) :-
  number_string(Idx, IdxStr),
  maplist(tptp_lit, Cla, Tmp),
  join_string(Tmp, " | ", Bdy),
  join_string(["cnf(c", IdxStr,
    ", negated_conjecture, (", Bdy, "))."], Str).

tptp_mat([Cla], Idx, Str) :-
  tptp_cla(Cla, Idx, Str).

tptp_mat([Cla | Mat], Idx, Str) :-
  tptp_cla(Cla, Idx, ClaStr),
  NewIdx is Idx + 1,
  tptp_mat(Mat, NewIdx, MatStr),
  join_string([ClaStr, " ", MatStr], Str).

write_goal(Loc, Mat) :-
  tptp_mat(Mat, 1, Goal),
  open(Loc, write, Stream),
  write(Stream, Goal),
  close(Stream).
