#!/usr/bin/env swipl

:- initialization(main, main).

main([Argv]) :-
  split_string(Argv, " ", " ", Tks),
  print(Tks).
