#!/usr/bin/env swipl

:- initialization(main, main).

mat(Stk, ["nl" | Tks], Mat) :-
  mat([[] | Stk], Tks, Mat).

mat([Num | Stk], ["y" | Tks], Mat) :-
  mat([sym(Num) | Stk], Tks, Mat).

mat([Trm | Stk], ["ng" | Tks], Mat) :-
  mat([neg(Trm) | Stk], Tks, Mat).

mat([Trm | Stk], ["ps" | Tks], Mat) :-
  mat([pos(Trm) | Stk], Tks, Mat).

mat([Hd, Tl | Stk], ["cs" | Tks], Mat) :-
  mat([[Hd | Tl] | Stk], Tks, Mat).

mat(Stk, [NumStr | Tks], Mat) :-
  number_string(Num, NumStr),
  mat([Num | Stk], Tks, Mat).

mat([Mat], [], Mat).

join_string([], _, "").

join_string([Str], _, Str).

join_string([Str | Strs], Jn, Rst) :-
  string_concat(Str, Jn, Str1),
  join_string(Strs, Jn, Str2),
  string_concat(Str1, Str2, Rst).

join_string(Strs, Str) :-
  join_string(Strs, "", Str).

tptp_trm(sym(Num), Num, []).

tptp_trm(sym(Num), Str) :-
  number_string(Num, NumStr),
  string_concat("s", NumStr, Str).

tptp_trm(app(Trm1, Trm2), Rst) :-
  tptp_trm(Trm1, Num, Strs),
  number_string(Num, NumStr),
  tptp_trm(Trm2, Str),
  append(Strs, [Str], ArgStrs),
  join_string(ArgStrs, ", ", ArgsStr),
  join_string(["s", NumStr, "(", ArgsStr, ")"], Rst).

tptp_lit(neg(Trm), Str) :-
  tptp_trm(Trm, Tmp),
  string_concat("~ " , Tmp, Str).

tptp_lit(pos(Trm), Str) :-
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

temp_loc("/var/tmp/temp_goal_file").

write_goal(Goal) :-
  temp_loc(Loc),
  open(Loc, write, Stream),
  write(Stream, Goal),
  close(Stream).

vampire(Strs) :-
  temp_loc(Loc),
  setup_call_cleanup(
    process_create(
      path(vampire),
      ["--avatar", "off", Loc],
      [stdout(pipe(Out))]
    ),
    read_lines(Out, Strs),
    close(Out)
  ).

read_lines(Out, []) :-
  read_line_to_string(Out, end_of_file), !.

read_lines(Out, Cdss) :-
  read_line_to_codes(Out, Cds),
  read_lines(Cds, Out, Cdss).

read_lines(end_of_file, _, []) :- !.

read_lines(Cds, Out, [Cds | Cdss]) :-
        read_line_to_codes(Out, Tmp),
        read_lines(Tmp, Out, Cdss).

foo('foo') :- true.

is_digit(Cd) :- 47 < Cd, Cd < 58.

head_is_digit([Cd | _]) :- is_digit(Cd).

parse_rul("input", inp).

parse_rul(Str, res(Idx1, Idx2)) :-
  ( string_concat("resolution ", Tmp, Str) ;
    string_concat("subsumption resolution ", Tmp, Str) ),
  split_string(Tmp, ",", "", [NumStr1, NumStr2]),
  number_string(Num1, NumStr1),
  Idx1 is Num1 - 1,
  number_string(Num2, NumStr2),
  Idx2 is Num2 - 1.

split_string_at(Str, Sep, Fst, Snd) :-
  string_concat(Fst, Tmp, Str),
  string_concat(Sep, Snd, Tmp).

parse_num(Acc, [Cd | Cds], Num, Rem) :-
  is_digit(Cd),
  parse_num([Cd | Acc], Cds, Num, Rem).

parse_num(Acc, [Cd | Cds], Num, [Cd | Cds]) :-
  not(is_digit(Cd)),
  reverse(Acc, Tmp),
  number_codes(Num, Tmp).

parse_num(Str, Num, Rem) :-
  string_codes(Str, Cds),
  parse_num([], Cds, Num, Tmp),
  string_codes(Rem, Tmp).

parse_trm(Str, sym(Num), "") :-
  string_concat("s", Tmp, Str),
  number_string(Num, Tmp).

parse_trm(Str, Trm, Rem) :-
  string_concat("s", Tmp, Str),
  split_string_at(Tmp, "(", Fst, Snd),
  number_string(Num, Fst),
  parse_trm(sym(Num), Snd, Trm, Rem).

parse_trm(Trm, Str, Trm, Rem) :-
  string_concat(")", Rem, Str).

parse_trm(Acc, Str, Trm, Rem) :-
  string_concat(", ", Tmp, Str),
  parse_trm(Acc, Tmp, Trm, Rem).

parse_trm(Acc, Str, Trm, Rem) :-
  string_concat("X", Str1, Str),
  parse_num(Str1, Num, Str2),
  parse_trm(vpp(Acc, Num), Str2, Trm, Rem).

parse_trm(Acc, Str, Trm, Rem) :-
  parse_trm(Str, Arg, Tmp),
  parse_trm(app(Acc, Arg), Tmp, Trm, Rem).

parse_lit(Str, neg(Trm)) :-
  string_concat("~", Tmp, Str),
  parse_trm(Tmp, Trm, "").

parse_lit(Str, pos(Trm)) :-
  parse_trm(Str, Trm, "").

parse_cla("$false", []) :- !.

parse_cla(Str, Cla) :-
  split_string(Str, "|", " ", LitStrs),
  maplist(parse_lit, LitStrs, Cla).

parse_line(Cds, line(Idx, Cla, Rul)) :-
  string_codes(Str, Cds),
  split_string(Str, ".[", "] ", [NumStr, ClaStr, RulStr]),
  number_string(Num, NumStr),
  Idx is Num - 1,
  parse_cla(ClaStr, Cla),
  parse_rul(RulStr, Rul).

read_proof(Lns) :-
  vampire(Cds),
  include(head_is_digit, Cds, Tmp),
  maplist(parse_line, Tmp, Lns).

compile(Mat, Lns, Num, Infs, Rst) :-
  member(line(Num, Tgt, Rul), Lns),
  compile(Mat, Lns, Num, Tgt, Rul, Infs, Rst).

max(Num1, Num2, Num1) :- Num1 >= Num2.
max(Num1, Num2, Num2) :- Num1 < Num2.

fresh_var(sym(_), 0).

fresh_var(app(Trm1, Trm2), Num) :-
  fresh_var(Trm1, Num1),
  fresh_var(Trm2, Num2),
  max(Num1, Num2, Num).

fresh_var(vpp(Trm1, Idx), Num) :-
  fresh_var(Trm1, Num1),
  Num2 is Idx + 1,
  max(Num1, Num2, Num).

fresh_var(neg(Trm), Num) :-
  fresh_var(Trm, Num).

fresh_var(pos(Trm), Num) :-
  fresh_var(Trm, Num).

fresh_var(Cla, Num) :-
  maplist(fresh_var, Cla, Nums),
  max_list(Nums, Num).

offset(Ofs, Src, map(Src, Tgt)) :-
  Tgt is Src + Ofs.

union([], []).

union([Lst | Lsts], Un) :-
  union(Lsts, Tmp),
  union(Lst, Tmp, Un).

vars(sym(_), []).

vars(app(Trm1, Trm2), Nums) :-
  vars(Trm1, Nums1),
  vars(Trm2, Nums2),
  union(Nums1, Nums2, Nums).

vars(vpp(Trm, Num), Nums) :-
  vars(Trm, Tmp),
  union([Num], Tmp, Nums).

vars(neg(Trm), Nums) :-
  vars(Trm, Nums).

vars(pos(Trm), Nums) :-
  vars(Trm, Nums).

vars(Cla, Nums) :-
  maplist(vars, Cla, Numss),
  union(Numss, Nums).

disjoiner(Cla1, Cla2, Dsj) :-
  fresh_var(Cla1, Num),
  vars(Cla2, Nums),
  maplist(offset(Num), Nums, Dsj).

rot(0, [Hd | Tl], [Hd | Tl]).

rot(Idx, [Hd | Tl], [NewHd, Hd | NewTl]) :-
  rot(NewIdx, Tl, [NewHd | NewTl]),
  Idx is NewIdx + 1.

% rot_core([Lit | Cla], 0, Lit, Cla).
%
% rot_core([Lit1 | Cla1], Num, Lit2, [Lit1 | Cla2]) :-
%   rot_core(Cla1, Tmp, Lit2, Cla2),
%   Num is Tmp + 1.
%
% rot(Cla, [num(Num), rot], [NewLit | NewCla]) :-
%   rot_core(Cla, Num, NewLit, NewCla).

subst(_, sym(Num), sym(Num)).

subst(Maps, app(Trm1, Trm2), app(NewTrm1, NewTrm2)) :-
  subst(Maps, Trm1, NewTrm1),
  subst(Maps, Trm2, NewTrm2).

subst(Maps, vpp(Trm, Num), vpp(NewTrm, NewNum)) :-
  member(map(Num, NewNum), Maps), !,
  number(NewNum),
  subst(Maps, Trm, NewTrm).

subst(Maps, vpp(Trm, Num), app(NewTrm1, NewTrm2)) :-
  member(map(Num, NewTrm2), Maps), !,
  not(number(NewTrm2)),
  subst(Maps, Trm, NewTrm1).

subst(Map, neg(Trm), neg(NewTrm)) :-
  subst(Map, Trm, NewTrm).

subst(Map, pos(Trm), pos(NewTrm)) :-
  subst(Map, Trm, NewTrm).

subst(Maps, Cla, NewCla) :-
  maplist(subst(Maps), Cla, NewCla).

trm_to_infs(sym(Num), [num(Num), sym]).

trm_to_infs(app(Trm1, Trm2), Infs) :-
  trm_to_infs(Trm1, Infs1),
  trm_to_infs(Trm2, Infs2),
  append([Infs1, Infs2, [app]], Infs).

trm_to_infs(vpp(Trm, Num), Infs) :-
  trm_to_infs(Trm, Tmp),
  append(Tmp, [num(Num), vpp], Infs).

map_to_infs(map(Src, Tgt), [num(Src), num(Tgt)]) :-
  number(Tgt).

map_to_infs(map(Num, Trm), [num(Num) | Infs]) :-
  trm_to_infs(Trm, Infs).

maps_to_infs([], [nil]).

maps_to_infs([Map | Maps], Infs) :-
  maps_to_infs(Maps, Infs1),
  map_to_infs(Map, Infs2),
  append([Infs1, Infs2, [cons]], Infs).

% compose_map(Maps, Src, Tgt, map(Src, NewTgt)) :-
%   member(map(Tgt, NewTgt), Maps), !.
%
% compose_map(Maps, Src, Tgt, map(Src, Tgt)) :-
%   not(member(map(Tgt, _), Maps)).
%

substitutee(Src, map(Src, _)).

compose_maps([], Maps, Maps).

compose_maps([map(Src, Tgt) | Maps1], Maps2, [map(Src, NewTgt) | NewMaps]) :-
  subst(Maps2, Tgt, NewTgt),
  exclude(substitutee(Src), Maps2, NewMaps2),
  compose_maps(Maps1, NewMaps2, NewMaps).

%compose_maps(Maps1, [map(Src, Tgt) | Maps2], [NewMap | NewMaps]) :-
%  compose_map(Maps1, Src, Tgt, NewMap),
%  compose_maps(Maps1, Maps2, NewMaps).

unifier(sym(Num), sym(Num), []).

unifier(app(Trm1, Trm2), app(Trm3, Trm4), Maps) :-
  unifier(Trm2, Trm4, Maps2),
  subst(Maps2, Trm1, NewTrm1),
  subst(Maps2, Trm3, NewTrm3),
  unifier(NewTrm1, NewTrm3, Maps1),
  compose_maps(Maps1, Maps2, Maps).

unifier(app(Trm1, Trm2), vpp(Trm3, Num), Maps) :-
  vars(Trm2, Nums),
  not(member(Num, Nums)),
  subst([map(Num, Trm2)], Trm1, NewTrm1),
  subst([map(Num, Trm2)], Trm3, NewTrm3),
  unifier(NewTrm1, NewTrm3, TmpMaps),
  compose_maps([map(Num, Trm2)], TmpMaps, Maps).

unifier(vpp(Trm1, Num), app(Trm2, Trm3), Maps) :-
  vars(Trm3, Nums),
  not(member(Num, Nums)),
  subst([map(Num, Trm1)], Trm1, NewTrm1),
  subst([map(Num, Trm2)], Trm2, NewTrm2),
  unifier(NewTrm1, NewTrm2, TmpMaps),
  compose_maps([map(Num, Trm3)], TmpMaps, Maps).

unifier(vpp(Trm1, Num1), vpp(Trm2, Num2), Maps) :-
  subst([map(Num2, Num1)], Trm1, NewTrm1),
  subst([map(Num2, Num1)], Trm2, NewTrm2),
  unifier(NewTrm1, NewTrm2, TmpMaps),
  compose_maps([map(Num2, Trm1)], TmpMaps, Maps).

unifiers(Trm1, Trm2, Dsj, Unf1, Unf2) :-
  subst(Dsj, Trm2, NewTrm2),
  unifier(Trm1, NewTrm2, Unf1),
  compose_maps(Dsj, Unf1, Unf2).

compile_res(Infs1, [neg(Trm1) | Cla1], Infs2, [pos(Trm2) | Cla2], Infs, Rst) :-
  disjoiner([neg(Trm1) | Cla1], [pos(Trm2) | Cla2], Dsj),
  unifiers(Trm1, Trm2, Dsj, Unf1, Unf2),
  subst(Unf1, Cla1, NewCla1),
  subst(Unf2, Cla2, NewCla2),
  maps_to_infs(Unf1, MapInfs1),
  maps_to_infs(Unf2, MapInfs2),
  append([Infs1, MapInfs1, [sub], Infs2, MapInfs2, [sub, res]], Infs),
  append(NewCla1, NewCla2, Rst).

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

instantiator(vpp(Trm1, Num), app(Trm2, Trm3), Maps) :-
  instantiator(Trm1, Trm2, Maps1),
  merge_instantiators(Maps1, [map(Num, Trm3)], Maps).

instantiator(vpp(Trm1, Num1), vpp(Trm2, Num2), Maps) :-
  instantiator(Trm1, Trm2, Maps1),
  merge_instantiators(Maps1, [map(Num1, Num2)], Maps).

instantiator(neg(Src), neg(Tgt), Maps) :-
  instantiator(Src, Tgt, Maps).

instantiator(pos(Src), pos(Tgt), Maps) :-
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

% increment(Num, SuccNum) :-
%   SuccNum is Num + 1.

% find_indices(_, [], []).
%
% find_indices(Elm, [Elm | Lst], [0 | Idxs]) :-
%   find_indices(Elm, Lst, Tmp),
%   maplist(increment, Tmp, Idxs).
%
% find_indices(Elm, [Hd | Lst], Idxs) :-
%   not(Elm = Hd),
%   find_indices(Elm, Lst, Tmp),
%   maplist(increment, Tmp, Idxs).

count(_, [], 0).

count(Elm, [Elm | Lst], Cnt) :-
  count(Elm, Lst, Tmp),
  Cnt is Tmp + 1.

count(Elm, [Hd | Lst], Cnt) :-
  not(Elm = Hd),
  count(Elm, Lst, Cnt).

compile_cnts_aux(Cla, Idx, Tl, [], Cla, Tl) :-
  not(member(Idx, Tl)).

compile_cnts_aux(Cla, Idx, Tl, [num(Num), rot, cont | Infs], RstCla, RstTl) :-
  nth0(PredNum, Tl, Idx),
  Num is PredNum + 1,
  rot(PredNum, Tl, [Idx | NewTl]),
  rot(Num, Cla, NewCla),
  compile_cnts_aux(NewCla, Idx, NewTl, Infs, RstCla, RstTl).

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
  disjoiner(Tgt, Cla, Dsj),
  subst(Dsj, Cla, Cla1),
  compute_maps(Cla1, Tgt, Inst, Nums),
  subst(Inst, Cla1, Cla2),
  compose_maps(Dsj, Inst, Maps),
  maps_to_infs(Maps, MapInfs),
  compile_cnts(Cla2, Nums, CntInfs, Rst),
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

compile(_, _, _, _, res(Num1, Num2), resfail(Num1, Num2), _).

compile(Mat, Lns, _, Tgt, map(Num), Infs, Rst) :-
  compile(Mat, Lns, Num, Infs1, Tmp),
  compile_map(Tmp, Tgt, Infs2, Rst),
  append(Infs1, Infs2, Infs).

filter_infs([], []).

filter_infs([nil, sub | Infs], Rst) :-
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

format_infs(num(Num), Str) :-
  number_string(Num, Str).
format_infs(hyp, "h").
format_infs(res, "r").
format_infs(rot, "t").
format_infs(cont, "c").
format_infs(sub, "s").

print_infs(Infs) :-
  maplist(format_infs, Infs, Strs),
  join_string(Strs, " ", Str),
  write(Str).

main([Argv]) :-
  split_string(Argv, " ", " ", Tks),
  mat([], Tks, Mat),
  tptp_mat(Mat, 1, Goal),
  write_goal(Goal),
  read_proof(Lns),
  compile(Mat, Lns, Infs),
  print_infs(Infs).
