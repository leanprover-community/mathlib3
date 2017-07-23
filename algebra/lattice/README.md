
# Lattice theory

Most here is translated from Isabelle 2016-1.

The idea is to keep the theory constructive and only when instantiating `Prop` with
`boolean_algebra` and `complete_boolean_algebra` should be `classical` needed.

Questions / Notes:

 * is the namespace `lattice` really needed?
   Some names are overlapping like `neg_neg` for `boolean_algebra` and `group`.
   
 * should we keep the names `supr` and `infi`, what's with `Sup` and `Inf`?
   At least `Sup` anf `Inf` violate the namespace conventions.

 * should we introduce syntax for `Inf` and `Sup`?
 
 * maybe introduce `heyting_algebra` and `complete_heyting_algebra`

