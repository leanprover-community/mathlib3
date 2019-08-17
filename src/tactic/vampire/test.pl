comma(Str1, Str2, Str) :-
  string_concat(Str1, ", ", Tmp),
  string_concat(Tmp, Str2, Str).
