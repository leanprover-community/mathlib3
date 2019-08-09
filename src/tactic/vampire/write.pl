:- [misc].

tptp_trms(app(Trm1, Trm2), Num, Strs) :-
  tptp_trms(Trm1, Num, TmpStrs),
  tptp_trm(trm, Trm2, Str),
  append(TmpStrs, [Str], Strs).

tptp_trms(sym(Num), Num, []).

header(trm, "f").
header(atm, "r").

tptp_trm(trm, var(Num), Str) :-
  number_string(Num, NumStr),
  string_concat("X", NumStr, Str).

tptp_trm(Typ, sym(Num), Str) :-
  header(Typ, Hdr),
  number_string(Num, NumStr),
  string_concat(Hdr, NumStr, Str).

tptp_trm(Typ, app(Trm1, Trm2), Rst) :-
  header(Typ, Hdr),
  tptp_trms(Trm1, Num, Strs),
  number_string(Num, NumStr),
  tptp_trm(trm, Trm2, Str),
  append(Strs, [Str], ArgStrs),
  join_string(ArgStrs, ",", ArgsStr),
  join_string([Hdr, NumStr, "(", ArgsStr, ")"], Rst).

tptp_lit(lit(neg, Atm), Str) :-
  tptp_trm(atm, Atm, Tmp),
  string_concat("~ " , Tmp, Str).

tptp_lit(lit(pos, Atm), Str) :-
  tptp_trm(atm, Atm, Str).

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
