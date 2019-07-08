#!/usr/bin/env swipl

:- initialization(main, main).

:- [write, read].

parse_inp([Num | Stk], ["y" | Tks], Mat) :-
  parse_inp([sym(Num) | Stk], Tks, Mat).

parse_inp([Trm2, Trm1 | Stk], ["a" | Tks], Mat) :-
  parse_inp([app(Trm1, Trm2) | Stk], Tks, Mat).

parse_inp([Num, Trm | Stk], ["v" | Tks], Mat) :-
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

compile(Mat, Lns, Num, Infs, Rst) :-
  member(line(Num, Tgt, Rul), Lns),
  compile(Mat, Lns, Num, Tgt, Rul, Infs, Rst).

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

rot(0, [Hd | Tl], [Hd | Tl]).

rot(Idx, [Hd | Tl], [NewHd, Hd | NewTl]) :-
  rot(NewIdx, Tl, [NewHd | NewTl]),
  Idx is NewIdx + 1.

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

trm_to_infs(sym(Num), [num(Num), sym]).

trm_to_infs(app(Trm1, Trm2), Infs) :-
  trm_to_infs(Trm1, Infs1),
  trm_to_infs(Trm2, Infs2),
  append([Infs1, Infs2, [app]], Infs).

trm_to_infs(var(Num), [num(Num)]).

map_to_infs(map(Src, Tgt), [num(Src), num(Tgt)]) :-
  number(Tgt).

map_to_infs(map(Num, Trm), [num(Num) | Infs]) :-
  trm_to_infs(Trm, Infs).

maps_to_infs([], [nil]).

maps_to_infs([Map | Maps], Infs) :-
  maps_to_infs(Maps, Infs1),
  map_to_infs(Map, Infs2),
  append([Infs1, Infs2, [cons]], Infs).

substitutee(Src, map(Src, _)).

compose_maps([], Maps, Maps).

compose_maps([map(Src, Tgt) | Maps1], Maps2, [map(Src, NewTgt) | NewMaps]) :-
  subst(Maps2, Tgt, NewTgt),
  exclude(substitutee(Src), Maps2, NewMaps2),
  compose_maps(Maps1, NewMaps2, NewMaps).

unifier(sym(Num), sym(Num), []).

unifier(app(Trm1, Trm2), app(Trm3, Trm4), Maps) :-
  unifier(Trm2, Trm4, Maps2),
  subst(Maps2, Trm1, NewTrm1),
  subst(Maps2, Trm3, NewTrm3),
  unifier(NewTrm1, NewTrm3, Maps1),
  compose_maps(Maps1, Maps2, Maps).

unifier(var(Num), Trm, [map(Num, Trm)]).
unifier(Trm, var(Num), [map(Num, Trm)]).

compile_res(InfsA, [lit(neg, TrmA) | ClaA], InfsB, [lit(pos, TrmB) | ClaB], Infs, Rst) :-
  disjoiner([lit(neg, TrmA) | ClaA], [lit(pos, TrmB) | ClaB], Dsj),
  subst(Dsj, TrmA, TrmA1),
  subst(Dsj, ClaA, ClaA1),
  unifier(TrmA1, TrmB, Unf),
  subst(Unf, ClaA1, ClaA2),
  subst(Unf, ClaB,  ClaB2),
  compose_maps(Dsj, Unf, UnfA),
  maps_to_infs(UnfA, MapInfsA),
  maps_to_infs(Unf,  MapInfsB),
  append([InfsA, MapInfsA, [sub], InfsB, MapInfsB, [sub, res]], Infs),
  append(ClaA2, ClaB2, Rst).

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

compile_cnts_aux(Cla, Idx, Tl, [], Cla, Tl) :-
  not(member(Idx, Tl)).

compile_cnts_aux([Lit | Cla], Idx, Tl, [num(Num), rot, cont | Infs], RstCla, RstTl) :-
  nth0(PredNum, Tl, Idx),
  Num is PredNum + 1,
  rot(PredNum, Tl, [Idx | NewTl]),
  rot(PredNum, Cla, [Lit | NewCla]),
  compile_cnts_aux([Lit | NewCla], Idx, NewTl, Infs, RstCla, RstTl).

compile_cnts(Cla, Idx, Idxs, [], Cla) :-
  not(member(Idx, Idxs)).

compile_cnts(Cla, Idx, Idxs, Infs, Rst) :-
  count(Idx, Idxs, 1),
  NewIdx is Idx + 1,
  compile_cnts(Cla, NewIdx, Idxs, Infs, Rst).

compile_cnts(Cla, Idx, Idxs, [num(Fst), rot | Infs], Rst) :-
  count(Idx, Idxs, Cnt),
  1 < Cnt,
  nth0(Fst, Idxs, Idx),
  rot(Fst, Idxs, [Idx | Idxs1]),
  rot(Fst, Cla, Cla1),
  compile_cnts_aux(Cla1, Idx, Idxs1, Infs1, Cla2, Idxs2),
  SuccIdx is Idx + 1,
  compile_cnts(Cla2, SuccIdx, [Idx | Idxs2], Infs2, Rst),
  append(Infs1, Infs2, Infs).

compile_cnts(Cla, Idxs, Infs, Rst) :-
   compile_cnts(Cla, 0, Idxs, Infs, Rst).

compute_maps(Cla, Tgt, Maps, Nums) :-
  choose_map(Cla, Tgt, Maps, Nums),
  surjective(Tgt, Nums).

compile_map([], [], [], []).

compile_map(Cla, Tgt, Infs, Rst) :-
  compute_maps(Cla, Tgt, Inst, Nums),
  subst(Inst, Cla, Cla1),
  maps_to_infs(Inst, MapInfs),
  compile_cnts(Cla1, Nums, CntInfs, Rst),
  append(MapInfs, [sub | CntInfs], Infs).

compile(Mat, _, Num, Tgt, inp, [num(Num), hyp | Infs], Rst) :-
  nth0(Num, Mat, Cla),
  compile_map(Cla, Tgt, Infs, Rst).

compile(Mat, Lns, _, Tgt, res(Num1, Num2), Infs, Rst) :-
  compile(Mat, Lns, Num1, Tmp1, Rst1),
  compile(Mat, Lns, Num2, Tmp2, Rst2),
  rot(Idx1, Rst1, Cla1),
  rot(Idx2, Rst2, Cla2),
  append(Tmp1, [num(Idx1), rot], Infs1),
  append(Tmp2, [num(Idx2), rot], Infs2),
  ( compile_res(Infs1, Cla1, Infs2, Cla2, ResInfs, Tmp) ;
    compile_res(Infs2, Cla2, Infs1, Cla1, ResInfs, Tmp) ),
  compile_map(Tmp, Tgt, MapInfs, Rst),
  append(ResInfs, MapInfs, Infs).

compile(Mat, Lns, _, Tgt, map(Num), Infs, Rst) :-
  compile(Mat, Lns, Num, Infs1, Tmp),
  compile_map(Tmp, Tgt, Infs2, Rst),
  append(Infs1, Infs2, Infs).

filter_infs([], []).

filter_infs([nil, sub | Infs], Rst) :-
  filter_infs(Infs, Rst).

filter_infs([num(Num), num(Num), cons | Infs], Rst) :-
  filter_infs(Infs, Rst).

filter_infs([num(0), rot | Infs], Rst) :-
  filter_infs(Infs, Rst).

filter_infs([Inf | Infs], [Inf | Rst]) :-
  filter_infs(Infs, Rst).

compile(Mat, Lns, Infs) :-
  length(Lns, Lth),
  Idx is Lth - 1,
  nth0(Idx, Lns, line(Num, [], Rul)),
  compile(Mat, Lns, Num, [], Rul, TmpInfs, _),
  filter_infs(TmpInfs, Infs).

compile(Mat, Lns, error(Mat, Lns)).

format_infs(num(Num), Str) :-
  number_binstr(Num, BinStr),
  string_concat("n", BinStr, Str).

format_infs(hyp, "h").
format_infs(res, "r").
format_infs(rot, "t").
format_infs(cont, "c").
format_infs(sub, "s").
format_infs(nil, "e").
format_infs(cons, "m").
format_infs(sym, "y").
format_infs(app, "a").

print_infs(Infs) :-
  maplist(format_infs, Infs, StrsA),
  join_string(StrsA, StrA),
  break_string(60, StrA, StrsB),
  string_codes(Nl, [10]),
  join_string(StrsB, Nl, StrB),
  write(StrB).

temp_loc("/var/tmp/temp_goal_file").

main([Argv]) :-
  split_string(Argv, " ", " ", Tks),
  parse_inp([], Tks, Mat),
  temp_loc(Loc),
  write_goal(Loc, Mat),
  read_proof(Loc, Lns),
  compile(Mat, Lns, Infs),
  print_infs(Infs).
