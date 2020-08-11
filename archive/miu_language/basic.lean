/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/
import tactic.linarith

/-!
# An MIU Decision Procedure in Lean

The [MIU formal system](https://en.wikipedia.org/wiki/MU_puzzle) was introduced by Douglas
Hofstadter in the first chapter of his 1979 book,
[Gödel, Escher, Bach](https://en.wikipedia.org/wiki/G%C3%B6del,_Escher,_Bach).
The system is defined by four rules of inference, one axiom, and an alphabet of three symbols:
`M`, `I`, and `U`.

Hofstadter's central question is: can the string "MU" be derived?

It transpires that there is a simple decision procedure for this system. A string is derivable if
and only if it starts with `"M"`, contains no other `"M"`s, and the number of `"I"`s in the string
is congruent to 1 or 2 modulo 3.

## The MIU System

An _atom_ is any one of `M`, `I` or `U`. A _string_ is a finite sequence of zero or more symbols.
To simplify notation, we write a sequence `[I,U,U,M]`, for example, as `IUUM`.

The four rules of inference are:

1. xI → xIU,
2. Mx → Mxx,
3. xIIIy → xUy,
4. xUUy → xy,

where the notation α → β is to be interpreted as 'if α is derivable, then β is derivable'.

Additionally, we have an axiom

* `MI` is derivable.

In this file, the set of atoms and the set of derivable strings are represented as inductive types.
-/


namespace miu

/-!
### Basic data types
-/

/--
Each MIU string consists of either an `M`, `I`, or `U`. Such an elementary unit is called an
`miu_atom`. We represent `miu_atom` as an enumerated type.
-/
@[derive decidable_eq]
inductive miu_atom : Type
| M : miu_atom
| I : miu_atom
| U : miu_atom

open miu_atom

/--
We show that the type `miu_atom` is inhabited, giving `M` (for no particular reason) as the default
element.
-/
instance miu_atom_inhabited : inhabited miu_atom :=
inhabited.mk M

/--
A simple function from `miu_atom` to `string`.
-/
def miu_atom.repr : miu_atom → string
| M := "M"
| I := "I"
| U := "U"

/--
A representation of an `miu_atom`.
-/
instance : has_repr miu_atom :=
⟨λ u, u.repr⟩

/--
For simplicity, an `miustr` is just a list of `miu_atom`.
-/
@[derive has_append]
def miustr := list miu_atom

/--
We want to use list membership.
-/
instance : has_mem miu_atom miustr :=
⟨list.mem⟩

/--
For display purposes, an `miustr` can be represented as a `string`.
-/
def miustr.mrepr : miustr → string
| [] := ""
| (c::cs) := c.repr ++ (miustr.mrepr cs)

instance miurepr : has_repr miustr :=
⟨λ u, u.mrepr⟩

/--
In the other direction, we set up a coercion from `string` to `miustr`.
-/
def lchar_to_miustr : (list char) → miustr
| [] := []
| (c::cs) :=
  let ms := lchar_to_miustr cs in
  match c with
  | 'M' := M::ms
  | 'I' := I::ms
  | 'U' := U::ms
  |  _  := []
  end

instance string_coe_miustr : has_coe string miustr :=
⟨λ st, lchar_to_miustr st.data ⟩


/-!
### Derivability
There is exactly one axiom of MIU, namely that `"MI"` is derivable. From this, and the rules of
inference, we define a type `derivable` so that `derivable st` corresonds to the notion that
the `miutr` st is derivable in MIU. We represent `derivable` as an inductive family.
-/

/--
The inductive type derivable has five constructors. The default constructor corresponds to the
axiom that `"MI"` is derivable. Each of the constructors `r1`, `r2`, `r3`, `r4` corresponds to the
one of the rules of inference described above.
-/
inductive derivable : miustr → Prop
| mk : derivable "MI"
| r1 {x} : derivable (x ++ [I]) → derivable (x ++ [I, U])
| r2 {x} : derivable (M :: x) → derivable (M :: x ++ x)
| r3 {x y} : derivable (x ++ [I, I, I] ++ y) → derivable (x ++ U :: y)
| r4 {x y} : derivable (x ++ [U, U] ++ y) → derivable (x ++ y)


/-!
### Rule usage examples
-/

example (h : derivable "UMI") : derivable "UMIU" :=
begin
  change ("UMIU" : miustr) with [U,M] ++ [I,U],
  exact derivable.r1 h, -- Rule 1
end

example (h : derivable "MIIU") : derivable "MIIUIIU" :=
begin
  change ("MIIUIIU" : miustr) with M :: [I,I,U] ++ [I,I,U],
  exact derivable.r2 h, -- Rule 2
end

example (h : derivable "UIUMIIIMMM") : derivable "UIUMUMMM" :=
begin
  change ("UIUMUMMM" : miustr) with [U,I,U,M] ++ U :: [M,M,M],
  exact derivable.r3 h, -- Rule 3
end

example (h : derivable "MIMIMUUIIM") : derivable "MIMIMIIM" :=
begin
  change ("MIMIMIIM" : miustr) with [M,I,M,I,M] ++ [I,I,M],
  exact derivable.r4 h,
end


/-!
### Derivability examples
-/



private lemma MIU_der : derivable "MIU":=
begin
  change ("MIU" :miustr) with [M] ++ [I,U],
  apply derivable.r1, -- "e reduce to deriving "MI",
  constructor, -- which is the base of the inductive construction.
end

example : derivable "MIUIU" :=
begin
  change ("MIUIU" : miustr) with M :: [I,U] ++ [I,U],
  exact derivable.r2 MIU_der, -- `"MIUIU"` can be derived as `"MIU"` can.
end

example : derivable "MUI" :=
begin
  have h₂ : derivable "MII",
    change ("MII" : miustr) with M :: [I] ++ [I],
    exact derivable.r2 derivable.mk,
  have h₃ : derivable "MIIII",
    change ("MIIII" : miustr) with M :: [I,I] ++ [I,I],
    exact derivable.r2 h₂,
  change ("MUI" : miustr) with [M] ++ U :: [I],
  exact derivable.r3 h₃, -- We prove our main goal using rule 3
end

end miu
