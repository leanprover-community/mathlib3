:- [misc].

read_lines(Out, []) :-
  read_line_to_string(Out, end_of_file), !.

read_lines(Out, Cdss) :-
  read_line_to_codes(Out, Cds),
  read_lines(Cds, Out, Cdss).

read_lines(end_of_file, _, []) :- !.

read_lines(Cds, Out, [Cds | Cdss]) :-
        read_line_to_codes(Out, Tmp),
        read_lines(Tmp, Out, Cdss).

vampire(Loc, Cdss) :-
  setup_call_cleanup(
    process_create(
      path(vampire),
      ["--avatar", "off", Loc],
      [stdout(pipe(Out))]
    ),
    read_lines(Out, Cdss),
    close(Out)
  ).

parse_rul("input", inp).

parse_rul(Str, map(Idx)) :-
  ( string_concat("factoring ", NumStr, Str) ;
    string_concat("duplicate literal removal ", NumStr, Str) ),
  number_string(Num, NumStr),
  Idx is Num - 1.

parse_rul(Str, res(Idx1, Idx2)) :-
  ( string_concat("resolution ", Tmp, Str) ;
    string_concat("subsumption resolution ", Tmp, Str) ),
  split_string(Tmp, ",", "", [NumStr1, NumStr2]),
  number_string(Num1, NumStr1),
  Idx1 is Num1 - 1,
  number_string(Num2, NumStr2),
  Idx2 is Num2 - 1.

parse_num(Acc, [Cd | Cds], Num, Rem) :-
  is_digit(Cd),
  parse_num([Cd | Acc], Cds, Num, Rem).

parse_num(Acc, Cds, Num, Cds) :-
  ( ( Cds = [Hd | _],
      not(is_digit(Hd)) ) ;
    ( Cds = [] ) ),
  reverse(Acc, Tmp),
  number_codes(Num, Tmp).

parse_num(Str, Num, Rem) :-
  string_codes(Str, Cds),
  parse_num([], Cds, Num, Tmp),
  string_codes(Rem, Tmp).

parse_args_core(Str, [], Rem) :-
  string_concat(")", Rem, Str).

parse_args_core(Str, Args, Rem) :-
  string_concat(",", Str1, Str),
  parse_args_core(Str1, Args, Rem).

parse_args_core(Str, [Arg | Args], Rem) :-
  parse_trm(Str, Arg, Str1),
  parse_args_core(Str1, Args, Rem).

parse_args(Str, [], Str) :-
  not(string_concat("(", _, Str)).

parse_args(Str, Args, Rem) :-
  string_concat("(", Str1, Str),
  parse_args_core(Str1, Args, Rem).

apply_args(Trm, [], Trm).

apply_args(Trm, [Arg | Args], Rst) :-
  apply_args(app(Trm, Arg), Args, Rst).

parse_trm(Str, Trm, Rem) :-
  string_concat("s", Str1, Str),
  parse_num(Str1, Num, Str2),
  parse_args(Str2, Trms, Rem),
  apply_args(sym(Num), Trms, Trm).

parse_trm(Str, var(Num), Rem) :-
  string_concat("X", Str1, Str),
  parse_num(Str1, Num, Rem).

% parse_trm(Acc, Str, Trm, Rem) :-
%   string_concat("X", Str1, Str),
%   parse_num(Str1, Num, Str2),
%   parse_trm(vpp(Acc, Num), Str2, Trm, Rem).
%
% parse_trm(Acc, Str, Trm, Rem) :-
%   parse_trm(Str, Arg, Tmp),
%   parse_trm(app(Acc, Arg), Tmp, Trm, Rem).

parse_lit(Str, lit(neg, Trm)) :-
  string_concat("~", Tmp, Str),
  parse_trm(Tmp, Trm, "").

parse_lit(Str, lit(pos, Trm)) :-
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

read_proof(Loc, Lns) :-
  vampire(Loc, Cds),
  include(head_is_digit, Cds, Tmp),
  maplist(parse_line, Tmp, Lns).
