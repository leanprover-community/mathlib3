# Maths in Lean : sets {#maths-in-lean-sets .entry-title}


The word `set` in Lean is best explained to a mathematician as meaning
“subset of”. For example `X : set nat` means that X is a subset of the
natural numbers (or “a set of naturals”). The way these are implemented
is that if `Y` is a type, then `X : set Y` actually means that `X` is a
map `Y -> Prop`, to be thought of as sending an object `y` of type `Y`
to the Proposition “I am in `X`” (of course this can be true or false).

Sets are defined in `init/data/set.lean` in the core Lean library. Note
that because of the way things are set up, if `X : set Y` then there is
not a natural map from type `X` to type `Y`! In fact this fails for two
reasons. Firstly I am not sure it even makes sense to have something of
type `X` — `X` is just a function. The other issue is that `Y` itself
does not have type `set Y`; the “set version” of `Y` is called
`univ : set Y` and it corresponds to the function `Y -> Prop` sending
every `y : Y` to `true : Prop`. Here are some examples of sets in
action.

### Examples.

```lean
variable (Y : Type*)
variables (A B : set Y)
variable (y : Y)

-- \subseteq 
#check A ⊆ B 

-- \in
#check y ∈ A

#check -A -- complement of A in Y

example : A ⊆ set.univ := λ y Hy, trivial -- presumably in mathlib

-- \empty
example : ∅ ⊆ A := λ y Hy, false.elim Hy -- result presumably in mathlib

-- \union
example : A ⊆ A ∪ B := λ y Hy,or.inl Hy -- result presumably in mathlib

-- \cap
example : A ∩ B ⊆ A := λ y Hy, and.elim_left Hy -- result presumably in mathlib 
```

TODO : give better proofs 
