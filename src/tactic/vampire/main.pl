#!/usr/bin/env swipl

:- initialization(main, main).

:- [write, read, check].

parse_inp([Num | Stk], ["fn" | Tks], Mat) :-
  parse_inp([sym(Num) | Stk], Tks, Mat).

parse_inp([Num | Stk], ["rl" | Tks], Mat) :-
  parse_inp([sym(Num) | Stk], Tks, Mat).

parse_inp([Trm2, Trm1 | Stk], ["tp" | Tks], Mat) :-
  parse_inp([app(Trm1, Trm2) | Stk], Tks, Mat).

parse_inp([Num, Trm | Stk], ["vp" | Tks], Mat) :-
  parse_inp([app(Trm, var(Num)) | Stk], Tks, Mat).

parse_inp(Stk, ["nl" | Tks], Mat) :-
  parse_inp([[] | Stk], Tks, Mat).

parse_inp([Trm | Stk], ["ng" | Tks], Mat) :-
  parse_inp([lit(neg, Trm) | Stk], Tks, Mat).

parse_inp([Trm | Stk], ["ps" | Tks], Mat) :-
  parse_inp([lit(pos, Trm) | Stk], Tks, Mat).

parse_inp([Hd, Tl | Stk], ["cs" | Tks], Mat) :-
  parse_inp([[Hd | Tl] | Stk], Tks, Mat).

parse_inp(Stk, [NumStr | Tks], Mat) :-
  number_string(Num, NumStr),
  parse_inp([Num | Stk], Tks, Mat).

parse_inp([Mat], [], Mat).

compile(Mat, Lns, Num, Prf) :-
  member(line(Num, Tgt, Rul), Lns),
  compile(Mat, Lns, Num, Tgt, Rul, Prf).

fresh_var(sym(_), 0).

fresh_var(app(Trm1, Trm2), Num) :-
  fresh_var(Trm1, Num1),
  fresh_var(Trm2, Num2),
  max(Num1, Num2, Num).

fresh_var(var(NumA), NumB) :-
  NumB is NumA + 1.

fresh_var(lit(_, Trm), Num) :-
  fresh_var(Trm, Num).

fresh_var(Cla, Num) :-
  maplist(fresh_var, Cla, Nums),
  max_list(Nums, Num).

offset(Ofs, Src, map(Src, var(Tgt))) :-
  Tgt is Src + Ofs.

vars(sym(_), []).

vars(app(Trm1, Trm2), Nums) :-
  vars(Trm1, Nums1),
  vars(Trm2, Nums2),
  union(Nums1, Nums2, Nums).

vars(var(Num), [Num]).

vars(lit(_, Trm), Nums) :-
  vars(Trm, Nums).

vars(Cla, Nums) :-
  maplist(vars, Cla, Numss),
  union(Numss, Nums).

disjoiner(Cla1, Cla2, Dsj) :-
  fresh_var(Cla2, Num),
  vars(Cla1, Nums),
  maplist(offset(Num), Nums, Dsj).

map_source(map(Src, _), Src).

domain(Maps, Dom) :-
  maplist(map_source, Maps, Dom).

in_domain(Dom, map(Src, _)) :-
  member(Src, Dom).

compose_maps(FstMaps, SndMaps, Maps) :-
  update_maps(FstMaps, SndMaps, NewFstMaps),
  domain(FstMaps, Dom),
  exclude(in_domain(Dom), SndMaps, NewSndMaps),
  append(NewFstMaps, NewSndMaps, Maps).

update_map(Map, map(Src, Tgt), map(Src, NewTgt)) :-
  subst(Map, Tgt, NewTgt).

update_maps(FstMaps, SndMaps, NewFstMaps) :-
  maplist(update_map(SndMaps), FstMaps, NewFstMaps).

unifier(sym(Num), sym(Num), []).

unifier(app(Trm1, Trm2), app(Trm3, Trm4), Maps) :-
  unifier(Trm2, Trm4, FstMaps),
  subst(FstMaps, Trm1, NewTrm1),
  subst(FstMaps, Trm3, NewTrm3),
  unifier(NewTrm1, NewTrm3, SndMaps),
  compose_maps(FstMaps, SndMaps, Maps).

unifier(var(Num), Trm, [map(Num, Trm)]).

unifier(Trm, var(Num), [map(Num, Trm)]).

range(0, Acc, Acc).

range(Num, Acc, Nums) :-
  0 < Num,
  NewNum is Num - 1,
  range(NewNum, [NewNum | Acc], Nums).

range(Num, Nums) :-
  range(Num, [], Nums).

member_rev(Lst, Elm) :- member(Elm, Lst).

merge_instantiators([], Inst, Inst).

merge_instantiators([map(Idx, Tgt) | Inst1], Inst2, Inst) :-
  member(map(Idx, Tgt), Inst2),
  merge_instantiators(Inst1, Inst2, Inst).

merge_instantiators([map(Idx, Tgt) | Inst1], Inst2, [map(Idx, Tgt) | Inst]) :-
  not(member(map(Idx, _), Inst2)),
  merge_instantiators(Inst1, Inst2, Inst).

instantiator(sym(Num), sym(Num), []).

instantiator(app(Trm1, Trm2), app(Trm3, Trm4), Maps) :-
  instantiator(Trm1, Trm3, Maps1),
  instantiator(Trm2, Trm4, Maps2),
  merge_instantiators(Maps1, Maps2, Maps).

instantiator(var(Num), Trm, [map(Num, Trm)]).

instantiator(lit(Pol, Src), lit(Pol, Tgt), Maps) :-
  instantiator(Src, Tgt, Maps).

choose_map([], _, [], []).

choose_map([Lit | Cla], Tgt, Maps, [LitNum | ClaNums]) :-
  nth0(LitNum, Tgt, TgtLit),
  instantiator(Lit, TgtLit, LitMaps),
  choose_map(Cla, Tgt, ClaMaps, ClaNums),
  merge_instantiators(LitMaps, ClaMaps, Maps).

surjective(Ran, Nums) :-
  length(Ran, Lth),
  range(Lth, Idxs),
  subset(Idxs, Nums).

count(_, [], 0).

count(Elm, [Elm | Lst], Cnt) :-
  count(Elm, Lst, Tmp),
  Cnt is Tmp + 1.

count(Elm, [Hd | Lst], Cnt) :-
  not(Elm = Hd),
  count(Elm, Lst, Cnt).

dup_idxs([Hd | Tl], 0, Idx) :-
  nth1(Idx, Tl, Hd).

dup_idxs([_ | Tl], IdxA, IdxB) :-
  dup_idxs(Tl, SubIdxA, SubIdxB),
  IdxA is SubIdxA + 1,
  IdxB is SubIdxB + 1.

conc(asm(_, Cnc), Cnc).
conc(rsl(_, _, Cnc), Cnc).
conc(rtt(_, _, Cnc), Cnc).
conc(cnt(_, Cnc), Cnc).
conc(sub(_, _, Cnc), Cnc).

compile_cnts(Prf, Dsts, Prf) :-
  not(dup_idxs(Dsts, _, _)).

compile_cnts(SubPrf, Dsts, Prf) :-
  dup_idxs(Dsts, IdxA, IdxB),
  conc(SubPrf, SubCnc),
  tor(SubCnc, IdxA, SubCnc1),
  SubPrf1 = rtt(IdxA, SubPrf, SubCnc1),
  tor(SubCnc1, IdxB, [Lit, Lit | SubCnc2]),
  SubPrf2 = rtt(IdxB, SubPrf1, [Lit, Lit | SubCnc2]),
  SubPrf3 = cnt(SubPrf2, [Lit | SubCnc2]),
  tor(Dsts,  IdxA, Dsts1),
  tor(Dsts1, IdxB, [Dst, Dst | Dsts2]),
  compile_cnts(SubPrf3, [Dst | Dsts2], Prf).

compute_maps(Cla, Tgt, Maps, Nums) :-
  choose_map(Cla, Tgt, Maps, Nums),
  surjective(Tgt, Nums).

compile_map(SubPrf, Tgt, Prf) :-
  conc(SubPrf, SubCnc),
  compute_maps(SubCnc, Tgt, Inst, Nums),
  subst(Inst, SubCnc, SubCnc1),
  compile_cnts(sub(Inst, SubPrf, SubCnc1), Nums, Prf).

compile_rsl(PrfA, PrfB, rsl(PrfA2, PrfB1, Cnc)) :-
  conc(PrfA, CncA),
  CncA = [lit(neg, _) | _],
  conc(PrfB, CncB),
  CncB = [lit(pos, TrmB) | _],
  disjoiner(CncA, CncB, Dsj),
  subst(Dsj, CncA, CncA1),
  CncA1 = [lit(neg, TrmA) | _],
  PrfA1 = sub(Dsj, PrfA, CncA1),
  unifier(TrmA, TrmB, Unf),
  subst(Unf, CncA1, CncA2),
  CncA2 = [lit(neg, Trm) | ClaA2],
  PrfA2 = sub(Unf, PrfA1, CncA2),
  subst(Unf, CncB, CncB1),
  CncB1 = [lit(pos, Trm) | ClaB1],
  PrfB1 = sub(Unf, PrfB, CncB1),
  append(ClaA2, ClaB1, Cnc).

compile(Mat, _, Num, Tgt, asm, Prf) :-
  nth0(Num, Mat, Cla),
  compile_map(asm(Num, Cla), Tgt, Prf).

compile(Mat, Lns, _, Tgt, rsl(NumA, NumB), Prf) :-
  compile(Mat, Lns, NumA, PrfA),
  compile(Mat, Lns, NumB, PrfB),
  conc(PrfA, CncA),
  conc(PrfB, CncB),
  tor(CncA, IdxA, CncA1),
  tor(CncB, IdxB, CncB1),
  PrfA1 = rtt(IdxA, PrfA, CncA1),
  PrfB1 = rtt(IdxB, PrfB, CncB1),
  ( compile_rsl(PrfA1, PrfB1, SubPrf) ;
    compile_rsl(PrfB1, PrfA1, SubPrf) ),
  compile_map(SubPrf, Tgt, Prf).

compile(Mat, Lns, _, Tgt, map(Num), Prf) :-
  compile(Mat, Lns, Num, SubPrf),
  compile_map(SubPrf, Tgt, Prf).

dezerortt(asm(Num, Maps), asm(Num, Maps)).

dezerortt(rtt(0, Prf), CPrf) :-
  dezerortt(Prf, CPrf).

dezerortt(rtt(Num, Prf), rtt(Num, CPrf)) :-
  0 < Num,
  dezerortt(Prf, CPrf).

dezerortt(rsl(PrfA, PrfB), rsl(PrfA1, PrfB1)) :-
  dezerortt(PrfA, PrfA1),
  dezerortt(PrfB, PrfB1).

dezerortt(cnt(Prf), cnt(CPrf)) :-
  dezerortt(Prf, CPrf).

relevant(Vars, map(Num, _)) :-
  member(Num, Vars).

filter_maps(Prf, Maps, NewMaps) :-
  conc(Prf, Cnc),
  vars(Cnc, Vars),
  include(relevant(Vars), Maps, NewMaps).

% pushmaps_debug(Maps, asm(_, Cnc), passed(Cla)) :-
%   vars(Cnc, Vars),
%   include(relevant(Vars), Maps, NewMaps),
%   subst(Maps, Cnc, Cla),
%   subst(NewMaps, Cnc, Cla).
%
% pushmaps_debug(Maps, asm(Num, Cnc), failed(Maps, asm(Num, Cnc))) :-
%   vars(Cnc, Vars),
%   include(relevant(Vars), Maps, NewMaps),
%   subst(Maps, Cnc, ClaA),
%   subst(NewMaps, Cnc, ClaB),
%   not(ClaA = ClaB).
%
% pushmaps_debug(Maps, rsl(PrfA, _, _), failed(X, Y)) :-
%   filter_maps(PrfA, Maps, MapsA),
%   pushmaps_debug(MapsA, PrfA, failed(X, Y)).
%
% pushmaps_debug(Maps, rsl(_, PrfB, _), failed(X, Y)) :-
%   filter_maps(PrfB, Maps, MapsB),
%   pushmaps_debug(MapsB, PrfB, failed(X, Y)).
%
% pushmaps_debug(Maps, rsl(PrfA, PrfB, Cnc), Rst) :-
%   filter_maps(PrfA, Maps, MapsA),
%   filter_maps(PrfB, Maps, MapsB),
%   (
%     pushmaps_debug(MapsA, PrfA, passed([lit(neg, Trm) | ClaA])),
%     pushmaps_debug(MapsB, PrfB, passed([lit(pos, Trm) | ClaB])),
%     subst(Maps, Cnc, Cla),
%     append(ClaA, ClaB, Cla)
%   ) -> Rst = passed(Cla) ; Rst  = failed(Maps, rsl(PrfA, PrfB, Cnc)).
%
% pushmaps_debug(Maps, rtt(_, Prf, _), failed(X, Y)) :-
%   pushmaps_debug(Maps, Prf, failed(X, Y)).
%
% pushmaps_debug(Maps, rtt(Num, PrfA, CncA), passed(Cnc)) :-
%   pushmaps_debug(Maps, PrfA, passed(CncB)),
%   rot(Num, CncB, Cnc),
%   subst(Maps, CncA, Cnc).
%
% pushmaps_debug(MapsA, sub(MapsB, Prf, _), failed(X, Y)) :-
%   compose_maps(MapsB, MapsA, Maps),
%   pushmaps_debug(Maps, Prf, failed(X, Y)).
%
% pushmaps_debug(MapsA, sub(MapsB, Prf, CncB), passed(Cnc)) :-
%   compose_maps(MapsB, MapsA, Maps),
%   pushmaps_debug(Maps, Prf, passed(Cnc)),
%   subst(MapsA, CncB, Cnc).

% pushmaps_debug(Maps, cnt(Prf, _), failed(X, Y)) :-
%   pushmaps_debug(Maps, Prf, failed(X, Y)).
%
% pushmaps_debug(Maps, cnt(PrfA, CncA), passed([Lit | Cla])) :-
%   pushmaps_debug(Maps, PrfA, passed([Lit, Lit | Cla])),
%   subst(Maps, CncA, [Lit | Cla]).
%
pushmaps(Maps, asm(Num, Cnc), asm(Num, NewMaps)) :-
  vars(Cnc, Vars),
  include(relevant(Vars), Maps, NewMaps).

pushmaps(Maps, rsl(PrfA, PrfB, _), rsl(CPrfA, CPrfB)) :-
  filter_maps(PrfA, Maps, MapsA),
  filter_maps(PrfB, Maps, MapsB),
  pushmaps(MapsA, PrfA, CPrfA),
  pushmaps(MapsB, PrfB, CPrfB).

pushmaps(Maps, rtt(Num, Prf, _), rtt(Num, CPrf)) :-
  pushmaps(Maps, Prf, CPrf).

pushmaps(MapsA, sub(MapsB, Prf, _), CPrf) :-
  compose_maps(MapsB, MapsA, Maps),
  pushmaps(Maps, Prf, CPrf).

pushmaps(Maps, cnt(Prf, _), cnt(CPrf)) :-
  pushmaps(Maps, Prf, CPrf).

pushmaps(Prf, CPrf) :-
  pushmaps([], Prf, CPrf).

groundterm(var(_), sym(0)).

groundterm(sym(Num), sym(Num)).

groundterm(app(TrmA, TrmB), app(GndTrmA, GndTrmB)) :-
  groundterm(TrmA, GndTrmA),
  groundterm(TrmB, GndTrmB).

groundmap(map(Num, Trm), map(Num, NewTrm)) :-
  groundterm(Trm, NewTrm).

groundmaps(asm(Num, Maps), asm(Num, NewMaps)) :-
  maplist(groundmap, Maps, NewMaps).

groundmaps(rsl(PrfA, PrfB), rsl(PrfA1, PrfB1)) :-
  groundmaps(PrfA, PrfA1),
  groundmaps(PrfB, PrfB1).

groundmaps(rtt(Num, Prf), rtt(Num, Prf1)) :-
  groundmaps(Prf, Prf1).

groundmaps(cnt(Prf), cnt(Prf1)) :-
  groundmaps(Prf, Prf1).

compress(RawPrf, Prf) :-
  pushmaps(RawPrf, Prf1),
  dezerortt(Prf1, Prf2),
  groundmaps(Prf2, Prf).

compile(Mat, Lns, Prf) :-
  length(Lns, Lth),
  Idx is Lth - 1,
  nth0(Idx, Lns, line(Num, [], Rul)),
  compile(Mat, Lns, Num, [], Rul, Prf).

compile(Mat, Lns, compile_error(Mat, Lns)).

string_block(Str, Blk) :-
  break_string(60, Str, Strs),
  string_codes(Nl, [10]),
  join_string(Strs, Nl, Blk).

trm_string(var(Num), Str) :-
  number_string(Num, NumStr),
  string_concat("X", NumStr, Str).

trm_string(sym(Num), Str) :-
  number_string(Num, NumStr),
  string_concat("s", NumStr, Str).

trm_string(app(TrmA, TrmB), Str) :-
  trm_string(TrmA, StrA),
  trm_string(TrmB, StrB),
  join_string(["(", StrA, " ", StrB, ")"], Str).

lit_string(lit(pos, Trm), Str) :-
  trm_string(Trm, Str).

lit_string(lit(neg, Trm), Str) :-
  trm_string(Trm, Str1),
  string_concat("-", Str1, Str).

map_string(map(Num, Trm), Str) :-
  number_string(Num, NumStr),
  trm_string(Trm, TrmStr),
  join_string([NumStr, " |-> ", TrmStr], Str).

list_string(ItemString, Lst, Str) :-
  maplist(ItemString, Lst, Strs),
  join_string(Strs, ", ", TmpStr),
  join_string(["[", TmpStr, "]"], Str).

cla_string(Cla, Str) :-
  list_string(lit_string, Cla, Str).

maps_string(Maps, Str) :-
  list_string(map_string, Maps, Str).

cproof_string(Mat, Spcs, asm(Num, Maps), Str, Cnc) :-
  string_concat("  ", Spcs, NewSpcs),
  nth0(Num, Mat, Cla),
  subst(Maps, Cla, Cnc),
  cla_string(Cnc, CncStr),
  number_string(Num, NumStr),
  maps_string(Maps, MapsStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "asm ", NumStr, " : ", CncStr, Nl, NewSpcs, MapsStr], Str).

cproof_string(Mat, Spcs, rsl(PrfA, PrfB), Str, Cnc) :-
  string_concat("  ", Spcs, NewSpcs),
  cproof_string(Mat, NewSpcs, PrfA, StrA, [_ | CncA]), !,
  cproof_string(Mat, NewSpcs, PrfB, StrB, [_ | CncB]), !,
  append(CncA, CncB, Cnc),
  cla_string(Cnc, CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "rsl : ", CncStr, Nl, StrA, Nl, StrB], Str).

cproof_string(Mat, Spcs, rtt(Num, PrfA), Str, Cnc) :-
  string_concat("  ", Spcs, NewSpcs),
  number_string(Num, NumStr),
  cproof_string(Mat, NewSpcs, PrfA, StrA, CncA), !,
  rot(Num, CncA, Cnc),
  cla_string(Cnc, CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "rtt ", NumStr, " : ", CncStr, Nl, StrA], Str).

cproof_string(Mat, Spcs, cnt(PrfA), Str, [Lit | Cla]) :-
  string_concat("  ", Spcs, NewSpcs),
  cproof_string(Mat, NewSpcs, PrfA, StrA, [Lit, Lit | Cla]), !,
  cla_string([Lit | Cla], CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "cnt : ", CncStr, Nl, StrA], Str).

cproof_string(Mat, Prf, Str) :-
  cproof_string(Mat, "", Prf, Str, _).

proof_string(Spcs, asm(Num, Cnc), Str) :-
  number_string(Num, NumStr),
  cla_string(Cnc, CncStr),
  join_string([Spcs, "asm ", NumStr, " : ", CncStr], Str).

proof_string(Spcs, rsl(PrfA, PrfB, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  cla_string(Cnc, CncStr),
  proof_string(NewSpcs, PrfA, StrA),
  proof_string(NewSpcs, PrfB, StrB),
  string_codes(Nl, [10]),
  join_string([Spcs, "rsl : ", CncStr, Nl, StrA, Nl, StrB], Str).

proof_string(Spcs, sub(Maps, PrfA, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  maps_string(Maps, MapsStr),
  cla_string(Cnc, CncStr),
  proof_string(NewSpcs, PrfA, StrA),
  string_codes(Nl, [10]),
  join_string([Spcs, "sub : ", CncStr, Nl, NewSpcs, MapsStr, Nl, StrA], Str).

proof_string(Spcs, rtt(Num, PrfA, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  number_string(Num, NumStr),
  proof_string(NewSpcs, PrfA, StrA),
  cla_string(Cnc, CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "rtt ", NumStr, " : ", CncStr, Nl, StrA], Str).

proof_string(Spcs, cnt(PrfA, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  proof_string(NewSpcs, PrfA, StrA),
  cla_string(Cnc, CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "cnt : ", CncStr, Nl, StrA], Str).

proof_string(Prf, Str) :-
  proof_string("", Prf, Str).

proof_string(Prf, print_error(Prf)).

temp_loc("/var/tmp/temp_goal_file").

line_string(line(Num, Cla, Rul), Str) :-
  number_string(Num, NumStr),
  cla_string(Cla, ClaStr),
  term_string(Rul, RulStr),
  join_string([NumStr, ". ", ClaStr, " [", RulStr, "]"], Str).

lines_string(Lns, Str) :-
  maplist(line_string, Lns, Strs),
  string_codes(Nl, [10]),
  join_string(Strs, Nl, Str).

linearize_term(sym(Num), Str) :-
  number_binstr(Num, NumStr),
  join_string(["n", NumStr, "s"], Str).

linearize_term(app(TrmA, TrmB), Str) :-
  linearize_term(TrmA, StrA),
  linearize_term(TrmB, StrB),
  join_string([StrA, StrB, "p"], Str).

linearize_maps([], "e").

linearize_maps([map(Num, Trm) | Maps], Str) :-
  number_binstr(Num, NumStr),
  linearize_term(Trm, TrmStr),
  linearize_maps(Maps, SubStr),
  join_string([SubStr, "n", NumStr, TrmStr, "m"], Str).

linearize_proof(asm(Num, Maps), LPrf) :-
  number_binstr(Num, NumStr),
  linearize_maps(Maps, MapsStr),
  join_string(["n", NumStr, MapsStr, "a"], LPrf).

linearize_proof(rsl(PrfA, PrfB), LPrf) :-
  linearize_proof(PrfA, StrA),
  linearize_proof(PrfB, StrB),
  join_string([StrA, StrB, "r"], LPrf).

linearize_proof(rtt(Num, PrfA), LPrf) :-
  number_binstr(Num, NumStr),
  linearize_proof(PrfA, StrA),
  join_string(["n", NumStr, StrA, "t"], LPrf).

linearize_proof(cnt(PrfA), LPrf) :-
  linearize_proof(PrfA, StrA),
  join_string([StrA, "c"], LPrf).

vcheck(Mat, asm(Num, Cnc)) :-
  nth0(Num, Mat, Cnc).

vcheck(Mat, rsl(PrfA, PrfB, Cnc)) :-
  vcheck(Mat, PrfA),
  vcheck(Mat, PrfB),
  conc(PrfA, [lit(neg, Trm) | CncA]),
  conc(PrfB, [lit(pos, Trm) | CncB]),
  append(CncA, CncB, Cnc).

vcheck(Mat, rtt(Num, PrfA, Cnc)) :-
  vcheck(Mat, PrfA),
  conc(PrfA, CncA),
  rot(Num, CncA, Cnc).

vcheck(Mat, cnt(PrfA, [Lit | Cla])) :-
  vcheck(Mat, PrfA),
  conc(PrfA, [Lit, Lit | Cla]).

vcheck(Mat, sub(Maps, PrfA, Cnc)) :-
  vcheck(Mat, PrfA),
  conc(PrfA, CncA),
  subst(Maps, CncA, Cnc).

main([Argv]) :-
  split_string(Argv, " ", " ", Tks),
  parse_inp([], Tks, Mat),
  temp_loc(Loc),
  write_goal(Loc, Mat),
  read_proof(Loc, Lns),
  compile(Mat, Lns, Prf),
  compress(Prf, CPrf),
  linearize_proof(CPrf, LPrf),
  string_block(LPrf, Str),
  write(Str).
