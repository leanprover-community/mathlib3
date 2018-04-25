/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

Defines the liminf/limsup of a function taking values in a conditionally complete lattice, with
respect to an arbitrary filter.
-/

import analysis.topology.topological_structures order.conditionally_complete_lattice

local attribute [instance] classical.prop_decidable
open set filter lattice

namespace filter
variables {α : Type} {β : Type} {f: filter α} {u : α → β} {v : α → β} {a : β} {b : β}

/-We define `Limsup f u` where `f` is a filter, and `u` is a function defined on the space
where `f` lives, taking values in a conditionally complete lattice. This is the smallest element `a`
such that, eventually, `u n ≤ a`.

Usually, one defines the Limsup as `Inf (Sup u''s)` where the Inf is taken over all sets in the filter.
for instance, in nat, this is `Inf_n (Sup_{k ≥ n} u k)` (and the latter quantity decreases with
`n`, so this is in fact a limit.) There is however a difficulty: it is well possible
that `u` is not bounded on the whole space, only eventually (think of `Limsup (λx, 1/x)` on real numbers.
Then there is no guarantee that the quantity above really decreases (the value of the `Sup` beforehand
is not really well defined, as one can not use ∞), so that the Inf could be anything. So one can not use this
`Inf Sup ...` definition in conditionally complete lattices, and one has to use the following less tractable
definition.

In complete lattices, however, it coincides with the `Inf Sup` definition.

We use cLimsup in theorems in conditionally complete lattices, and Limsup for the corresponding
theorems in complete lattices (usually with less assumptions). In conditionally complete lattices, the
definition is only useful for functions which are eventually bounded above (otherwise, the limsup would
morally be +infinity, which does not belong to the space) and which are frequently bounded below (otherwise,
the limsup would morally be -infinity, which is not in the space either). We start with definitions of these
concepts for arbitrary filters, before turning to the definitions of Limsup and Liminf.
-/
section conditionally_complete_lattice
variables [conditionally_complete_lattice β]

/--A function `u` is eventually bounded above with respect to a filter `f` if,
there exists an admissible set of `f` on which it is bounded.-/
def eventually_bdd_above (f : filter α) (u : α → β) :=
∃s ∈ f.sets, bdd_above (u '' s)

/--A function is eventually bounded if and only if, eventually, it is bounded by
some uniform bound.-/
lemma eventually_bdd_above_iff_exists_eventually_le : (eventually_bdd_above f u) ↔ (∃t, eventually (λn, u n ≤ t) f) :=
/-Short obfuscated version of the proof below:
⟨λ ⟨su, suf, tu, tuH⟩, ⟨tu, filter.upwards_sets f suf (λ y Hy, tuH _ (mem_image_of_mem _ Hy))⟩,
 λ ⟨t, Ht⟩, ⟨{y | u y ≤ t}, Ht, t, (λy ⟨x, Hx⟩, by simpa [Hx.2] using Hx)⟩⟩-/
have A: eventually_bdd_above f u → (∃a, eventually (λn, u n ≤ a) f) :=
  assume ⟨su, suf, a, Ha⟩,
  have eventually (λn, u n ≤ a) f :=
  begin
    apply filter.upwards_sets f suf,
    assume y Hy,
    apply Ha _ (mem_image_of_mem _ Hy)
  end,
  ⟨a, by assumption⟩,
have B: (∃a, eventually (λn, u n ≤ a) f) → eventually_bdd_above f u :=
  assume ⟨a, Ha⟩,
  have bdd_above (u '' {n | u n ≤ a}) :=
  begin
    apply bdd_above.mk a,
    assume b Hb,
    induction Hb with x Hx,
    simpa [Hx.2] using Hx,
  end,
  ⟨{n | u n ≤ a}, by assumption, by assumption⟩,
⟨A, B⟩

/--A bounded above function is in particular eventually bounded above.-/
lemma eventually_bdd_above_of_bdd_above (f : filter α) (u : α → β) (H : bdd_above (u '' univ)) :
eventually_bdd_above f u := ⟨univ, univ_mem_sets, by assumption⟩


/-There is a subtlety in the next definition: we want the definition
to hold for any sequence in the case of complete lattices (this will be relevant to deduce
theorems on complete lattices from their versions on conditionally complete lattices with
additional assumptions). We have to be careful in the edge case of the trivial filter
containing the empty set: the other natural definition `¬(∀a, eventually (λn, a ≤ u n) f)`
would not work as well in this case.-/
/--A function `u` is frequently bounded above with respect to a filter `f` if it
does not tend to infinity along the filter.-/
def frequently_bdd_above (f : filter α) (u : α → β) :=
bdd_above {a | eventually (λn, a ≤ u n) f}

/-The next lemma is only an implication, as the other direction is wrong for the trivial filter.-/
/--To check that a function is frequently bounded above, it suffices to have a witness
which bounds the value of `u` at some point in every admissible set of the filter.-/
lemma frequently_bdd_above.mk (a : β) (H : ∀s ∈ f.sets, ∃x ∈ s, u x ≤ a) : frequently_bdd_above f u :=
⟨a, λy s, let ⟨x, M⟩ := H _ s in by simp at M; apply le_trans M.1 M.2⟩

/--A function which is eventually bounded above is in particular frequently bounded above, at
least if the filter is not trivial.-/
lemma frequently_bdd_above_of_eventually_bdd_above (hf : f ≠ ⊥) (H : eventually_bdd_above f u) : frequently_bdd_above f u :=
let ⟨su, suf, a, Ha⟩ := ‹eventually_bdd_above f u› in
have ∀b, eventually (λn, b ≤ u n) f → b ≤ a :=
  assume b Hb,
  have I : {n | b ≤ u n} ∩ su ∈ f.sets := inter_mem_sets Hb suf,
  let ⟨x, xf⟩ := inhabited_of_mem_sets hf I in
  calc b ≤ u x : by simp at xf; apply xf.1
  ...    ≤ a   : by apply Ha; apply mem_image_of_mem; simp at *; simp [xf],
⟨a, by simp; assumption⟩

/--The maximum of two functions which are eventually bounded above is still
eventually bounded above.-/
lemma eventually_bdd_above_sup (_ : eventually_bdd_above f u) (_ : eventually_bdd_above f v) :
eventually_bdd_above f (λn, (u n) ⊔ (v n)) :=
let ⟨su, suf, a, Ha⟩ := ‹eventually_bdd_above f u› in
let ⟨sv, svf, b, Hb⟩ := ‹eventually_bdd_above f v› in
have bdd_above ((λn, u n ⊔ v n) '' (su ∩ sv)) :=
begin
  apply bdd_above.mk (a ⊔ b),
  simp,
  assume y x xu xv uvy,
  have: u x ≤ a, from Ha _ (mem_image_of_mem _ ‹x ∈ su›),
  have: v x ≤ b, from Hb _ (mem_image_of_mem _ ‹x ∈ sv›),
  show y ≤ a ⊔ b, by rw[←uvy]; apply sup_le_sup; assumption; assumption,
end,
⟨su ∩ sv, inter_mem_sets suf svf, by assumption⟩


/--A function `u` is eventually bounded below with respect to a filter `f` if,
there exists an admissible set of `f` on which it is bounded below.-/
def eventually_bdd_below (f : filter α) (u : α → β) :=
∃s ∈ f.sets, bdd_below (u '' s)

/--A bounded below function is in particular eventually bounded below.-/
lemma eventually_bdd_below_of_bdd_below (f : filter α) (u : α → β) (H : bdd_below (u '' univ)) :
eventually_bdd_below f u := ⟨univ, univ_mem_sets, by assumption⟩

/--A function is eventually bounded below if and only if, eventually, it is bounded below by
some uniform bound.-/
lemma eventually_bdd_below_iff_exists_eventually_le : (eventually_bdd_below f u) ↔ (∃a, eventually (λn, a ≤ u n) f) :=
have A: eventually_bdd_below f u → (∃a, eventually (λn, a ≤ u n) f) :=
  assume ⟨su, suf, a, Ha⟩,
  have eventually (λn, a ≤ u n) f :=
  begin
    apply filter.upwards_sets f suf,
    assume y Hy,
    apply Ha _ (mem_image_of_mem _ Hy)
  end,
  ⟨a, by assumption⟩,
have B: (∃a, eventually (λn, a ≤ u n) f) → eventually_bdd_below f u :=
  assume ⟨a, Ha⟩,
  have bdd_below (u '' {y : α | a ≤ u y}) :=
  begin
    apply bdd_below.mk a,
    assume y Hy,
    induction Hy with x Hx,
    simpa [Hx.2] using Hx,
  end,
  ⟨{y | a ≤ u y}, by assumption, by assumption⟩,
⟨A, B⟩

/--A function `u` is frequently bounded below with respect to a filter `f` if it
does not tend to infinity along the filter.-/
def frequently_bdd_below (f : filter α) (u : α → β) :=
bdd_below {a | eventually (λn, u n ≤ a) f}

/--To check that a function is frequently bounded below, it suffices to have a witness
which bounds the value of `u` at some point in every admissible set of the filter.-/
lemma frequently_bdd_below.mk (a : β) (H : ∀s ∈ f.sets, ∃x ∈ s, a ≤ u x) : frequently_bdd_below f u :=
⟨a, λy s, let ⟨x, M⟩ := H _ s in by simp at M; apply le_trans M.2 M.1⟩

/--A function which is eventually bounded below is in particular frequently bounded below, at
least if the filter is not trivial.-/
lemma frequently_bdd_below_of_eventually_bdd_below (hf : f ≠ ⊥) (H : eventually_bdd_below f u) : frequently_bdd_below f u :=
let ⟨su, suf, a, Ha⟩ := ‹eventually_bdd_below f u› in
have ∀b, eventually (λn, u n ≤ b) f → a ≤ b :=
  assume b Hb,
  have I : {n | u n ≤ b} ∩ su ∈ f.sets := inter_mem_sets Hb suf,
  let ⟨x, xf⟩ := inhabited_of_mem_sets hf I in
  calc a ≤ u x : by apply Ha; apply mem_image_of_mem; simp at *; simp [xf]
  ...     ≤ b   : by simp at xf; apply xf.1,
⟨a, by simp; assumption⟩

/--The minimum of two functions which are eventually bounded below is still
eventually bounded below.-/
lemma eventually_bdd_below_inf (_ : eventually_bdd_below f u) (_ : eventually_bdd_below f v) :
eventually_bdd_below f (λn, (u n) ⊓ (v n)) :=
let ⟨su, suf, a, Ha⟩ := ‹eventually_bdd_below f u› in
let ⟨sv, svf, b, Hb⟩ := ‹eventually_bdd_below f v› in
have bdd_below ((λn, u n ⊓ v n) '' (su ∩ sv)) :=
begin
  apply bdd_below.mk (a ⊓ b),
  simp,
  assume y x xu xv uvy,
  have: a ≤ u x, from Ha _ (mem_image_of_mem _ ‹x ∈ su›),
  have: b ≤ v x, from Hb _ (mem_image_of_mem _ ‹x ∈ sv›),
  show a ⊓ b ≤ y, by rw[←uvy]; apply inf_le_inf; assumption; assumption,
end,
⟨su ∩ sv, inter_mem_sets suf svf, by assumption⟩


/--`Limsup f u` is the limsup of the function u along the filter f.-/
definition Limsup (f : filter α) (u : α → β) := Inf {a:β | eventually (λn, u n ≤ a) f}

/--If a map is eventually bounded by `a`, then its Limsup is at most `a`
(if it is frequently bounded below, for the Limsup to make sense).-/
theorem cLimsup_le_of_eventually_le (Hb : frequently_bdd_below f u) (L : eventually (λn, u n ≤ a) f) : Limsup f u ≤ a :=
cInf_le Hb L

/--`Liminf f u` is the liminf of the function u along the filter f.-/
definition Liminf (f : filter α) (u : α → β) := Sup {a:β | eventually (λn, a ≤ u n) f}

/--If a map is eventually bounded below by `a`, then its Liminf is at least `a`
(if it is frequently bounded above, for the Liminf to make sense).-/
theorem le_cLiminf_of_eventually_le (Hb : frequently_bdd_above f u) (L : eventually (λn, a ≤ u n) f) : a ≤ Liminf f u :=
le_cSup Hb L

/--The liminf of a function is bounded by its limsup, at least if the map is eventually bounded
above and below.-/
theorem cLiminf_le_cLimsup (Hb : eventually_bdd_below f u) (Ha : eventually_bdd_above f u) (Hf : f ≠ ⊥) :
Liminf f u ≤ Limsup f u :=
have A : ∀a b, eventually (λn, a ≤ u n) f → eventually (λn, u n ≤ b) f → a ≤ b :=
  assume a b Ha Hb,
  have eventually (λn, a ≤ u n ∧ u n ≤ b) f :=
    eventually_and_of_eventually_of_eventually Ha Hb,
  let ⟨x, Hx⟩ := inhabited_of_mem_sets Hf this in
  le_trans Hx.1 Hx.2,
begin
  apply cSup_le (ne_empty_iff_exists_mem.2 (eventually_bdd_below_iff_exists_eventually_le.1 Hb)),
  assume b Hb,
  apply le_cInf (ne_empty_iff_exists_mem.2 (eventually_bdd_above_iff_exists_eventually_le.1 Ha)),
  assume c Hc,
  apply A b c Hb Hc,
end

/--If eventually `u n ≤ v n`, then `Limsup u ≤ Limsup v`-/
theorem cLimsup_le_cLimsup (Hb : frequently_bdd_below f u) (Ha : eventually_bdd_above f v) (H : eventually (λn, u n ≤ v n) f) : Limsup f u ≤ Limsup f v :=
have A : ∀a, eventually (λn, v n ≤ a) f → eventually (λn, u n ≤ a) f :=
  assume a La,
  eventually_of_eventually_of_imp (eventually_and_of_eventually_of_eventually La H) (λn Hn, le_trans Hn.2 Hn.1),
begin
  apply cInf_le_cInf Hb,
  apply ne_empty_iff_exists_mem.2 (eventually_bdd_above_iff_exists_eventually_le.1 Ha),
  apply A
end

/--If eventually `u n ≤ v n`, then `Liminf u ≤ Liminf v`-/
theorem cLiminf_le_cLiminf (Hb : eventually_bdd_below f u) (Ha : frequently_bdd_above f v) (H : eventually (λn, u n ≤ v n) f) : Liminf f u ≤ Liminf f v :=
have A : ∀a, eventually (λn, a ≤ u n) f → eventually (λn, a ≤ v n) f :=
  assume a La,
  eventually_of_eventually_of_imp (eventually_and_of_eventually_of_eventually La H) (λn Hn, le_trans Hn.1 Hn.2),
begin
  apply cSup_le_cSup Ha,
  apply ne_empty_iff_exists_mem.2 (eventually_bdd_below_iff_exists_eventually_le.1 Hb),
  apply A
end

end conditionally_complete_lattice


section complete_lattice
variable [complete_lattice β]

/--In a complete lattice, every function is eventually bounded above.-/
@[simp] lemma eventually_bdd_above_complete_lattice : eventually_bdd_above f u :=
by simp [eventually_bdd_above, f.exists_mem_sets]

/--In a complete lattice, every function is eventually bounded below.-/
@[simp] lemma eventually_bdd_below_complete_lattice : eventually_bdd_below f u :=
by simp [eventually_bdd_below, f.exists_mem_sets]

/--In a complete lattice, every function is frequently bounded above.-/
@[simp] lemma frequently_bdd_above_complete_lattice : frequently_bdd_above f u :=
by simp [frequently_bdd_above]

/--In a complete lattice, every function is frequently bounded below.-/
@[simp] lemma frequently_bdd_below_complete_lattice : frequently_bdd_below f u :=
by simp [frequently_bdd_below]

/--If a map is eventually bounded by `a`, then its Limsup is at most `a` in a complete lattice.-/
theorem Limsup_le_of_eventually_le (L : eventually (λn, u n ≤ a) f) : Limsup f u ≤ a :=
cLimsup_le_of_eventually_le (by simp) L

/--If a map is eventually bounded below by `a`, then its Liminf is at least `a` in a complete lattice.-/
theorem le_Liminf_of_eventually_le (L : eventually (λn, a ≤ u n) f) : a ≤ Liminf f u :=
le_cLiminf_of_eventually_le (by simp) L

/--In a complete lattice, the Limsup of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s`-/
theorem Limsup_eq_Inf_Sup : Limsup f u = Inf ((λs, Sup (u '' s)) '' f.sets) :=
have ∀s ∈ f.sets, eventually (λn, u n ≤ Sup (u '' s)) f :=
begin
  assume S Sf,
  apply f.upwards_sets Sf,
  assume x xS,
  apply le_Sup (mem_image_of_mem _ xS)
end,
have A : Limsup f u ≤ Inf ((λs, Sup (u '' s)) '' f.sets) :=
  Inf_le_Inf (by finish [subset_def]),
have ∀a, eventually (λn, u n ≤ a) f → Inf ((λs, Sup (u '' s)) '' f.sets) ≤ a :=
  assume a Ha,
  calc Inf ((λs, Sup (u '' s)) '' f.sets) ≤ (λs, Sup (u '' s)) {n | u n ≤ a} :
                 by apply Inf_le; finish [eventually]
       ... ≤ a : by finish,
have B : Inf ((λs, Sup (u '' s)) '' f.sets) ≤ Limsup f u :=
  le_Inf (by assumption),
le_antisymm A B

/--In a complete lattice, the Liminf of a function is the supremum over sets `s` in the filter
of the infimum of the function over `s`-/
theorem Liminf_eq_Sup_Inf : Liminf f u = Sup ((λs, Inf (u '' s)) '' f.sets) :=
have ∀s ∈ f.sets, eventually (λn, Inf (u '' s) ≤ u n) f :=
begin
  assume S Sf,
  apply f.upwards_sets Sf,
  assume x xS,
  apply Inf_le (mem_image_of_mem _ xS)
end,
have A : Sup ((λs, Inf (u '' s)) '' f.sets) ≤ Liminf f u :=
  Sup_le_Sup (by finish [subset_def]),
have ∀a, eventually (λn, a ≤ u n) f → a ≤ Sup ((λs, Inf (u '' s)) '' f.sets) :=
  assume a Ha,
  calc a   ≤ (λs, Inf (u '' s)) {n | a ≤ u n}   : by finish
       ... ≤ Sup ((λs, Inf (u '' s)) '' f.sets) : by apply le_Sup; finish [eventually],
have B : Liminf f u ≤ Sup ((λs, Inf (u '' s)) '' f.sets) :=
  Sup_le (by assumption),
le_antisymm B A

/--In a complete lattice, the liminf is bounded by the limsup.-/
theorem Liminf_le_Limsup (H : f ≠ ⊥) : Liminf f u ≤ Limsup f u :=
cLiminf_le_cLimsup (by simp) (by simp) H

/--If eventually `u n ≤ v n`, then `Limsup u ≤ Limsup v`-/
theorem Limsup_le_Limsup (H : eventually (λn, u n ≤ v n) f) : Limsup f u ≤ Limsup f v :=
cLimsup_le_cLimsup (by simp) (by simp) H

/--If eventually `u n ≤ v n`, then `Liminf u ≤ Liminf v`-/
theorem Liminf_le_Liminf (H : eventually (λn, u n ≤ v n) f) : Liminf f u ≤ Liminf f v :=
cLiminf_le_cLiminf (by simp) (by simp) H

end complete_lattice


section conditionally_complete_linear_order
variable [conditionally_complete_linear_order β]

/--If a function which is eventually bounded above has a Limsup which is `< t`, then it
is eventually `< t` in a conditionally complete linear order.-/
theorem eventually_lt_of_cLimsup_lt (H : eventually_bdd_above f u) (L : Limsup f u < a) :
eventually (λn, u n < a) f :=
/-There is a subtlety in this proof: in conditionally complete linear orders, the Limsup
only makes sense for functions which are eventually bounded above and frequently bounded below.
We do not assume that `u` is frequently bounded below, as the conclusion of the theorem is
still obviously true if it is not. This means that we will argue by contradiction, assuming that
the conclusion is wrong, deducing that the function is frequently bounded below, and then
using the definition of the infimum in conditionally complete linear orders.-/
have M: ¬¬(eventually (λn, u n < a) f) :=
  assume: ¬eventually (λn, u n < a) f,
  have frequently_bdd_below f u :=
  begin
    apply bdd_below.mk a,
    assume y Hy,
    by_contradiction tley,
    have: y < a := not_le.1 tley,
    have: eventually (λn, u n < a) f :=
      eventually_of_eventually_of_imp Hy (by assume (n) (L); apply lt_of_le_of_lt L ‹y < a›),
    show false, from absurd this ‹¬eventually (λn, u n < a) f›
  end,
  have A : ∃b∈{r:β | eventually (λn, u n ≤ r) f}, b < a :=
  begin
    apply exists_lt_of_cInf_lt _ L,
    exact let ⟨U, V⟩ := (eventually_bdd_above_iff_exists_eventually_le.1 H) in @ne_empty_of_mem _ _ U V,
  end,
  let ⟨b, b_in, b_le⟩ := A in
  have eventually (λn, u n < a) f :=
    eventually_of_eventually_of_imp b_in (λn N, lt_of_le_of_lt N b_le),
  show false, from absurd this ‹¬eventually (λn, u n < a) f›,
not_not.1 M

/--If a function which is eventually bounded below has a Liminf which is `> t`, then it
is eventually `> t` in a conditionally complete linear order.-/
theorem eventually_lt_of_lt_cLiminf (H : eventually_bdd_below f u) (L : a < Liminf f u) :
eventually (λn, a < u n) f :=
have M: ¬¬(eventually (λn, a < u n) f) :=
  assume: ¬eventually (λn, a < u n) f,
  have frequently_bdd_above f u :=
  begin
    apply bdd_above.mk a,
    assume y Hy,
    by_contradiction tley,
    have: a < y := not_le.1 tley,
    have: eventually (λn, a < u n) f :=
      eventually_of_eventually_of_imp Hy (by assume (n) (L); apply lt_of_lt_of_le ‹a < y› L),
    show false, from absurd this ‹¬eventually (λn, a < u n) f›
  end,
  have A : ∃b∈{r:β | eventually (λn, r ≤ u n) f}, a < b :=
  begin
    apply exists_lt_of_lt_cSup _ L,
    exact let ⟨U, V⟩ := (eventually_bdd_below_iff_exists_eventually_le.1 H) in @ne_empty_of_mem _ _ U V,
  end,
  let ⟨b, b_in, b_le⟩ := A in
  have eventually (λn, a < u n) f :=
    eventually_of_eventually_of_imp b_in (λn N, lt_of_lt_of_le b_le N),
  show false, from absurd this ‹¬eventually (λn, a < u n) f›,
not_not.1 M

end conditionally_complete_linear_order


section complete_linear_order
variable [complete_linear_order β]

/--If a limsup is `< t`, then the function is eventually `< t` in a complete linear order.-/
theorem eventually_lt_of_Limsup_lt (L : Limsup f u < a) : eventually (λn, u n < a) f :=
eventually_lt_of_cLimsup_lt (by simp) L

/--If a liminf is `> t`, then the function is eventually `> t` in a complete linear order.-/
theorem eventually_lt_of_lt_Liminf (L : a < Liminf f u) : eventually (λn, a < u n) f :=
eventually_lt_of_lt_cLiminf (by simp) L

end complete_linear_order


section conditionally_complete_lattice_topology
variables [topological_space β] [conditionally_complete_lattice β] [orderable_topology β]

/--A converging sequence is eventually bounded above.-/
lemma eventually_bdd_above_of_tendsto (H : tendsto u f (nhds a)) :
eventually_bdd_above f u :=
/-Either `a` is maximal, and then everything is trivial. Or it is not, and then a strict
upper bound of `a` is an eventual upper bound for `u`.-/
have A : (∀b, b ≤ a) → eventually_bdd_above f u :=
  assume M,
  eventually_bdd_above_of_bdd_above f u ⟨a, λy Hy, M y⟩,
have B : (∃b, a < b) → eventually_bdd_above f u :=
  assume ⟨b, Hb⟩,
  have eventually (λn, u n < b) f := (tendsto_orderable.1 H).2 b Hb,
  have eventually (λn, u n ≤ b) f :=
    eventually_of_eventually_of_imp this (λn, le_of_lt),
  eventually_bdd_above_iff_exists_eventually_le.2 ⟨b, this⟩,
begin
  cases (forall_le_or_exists_lt a) with I J,
  apply A I,
  apply B J
end

/--A converging sequence is eventually bounded below.-/
lemma eventually_bdd_below_of_tendsto (H : tendsto u f (nhds a)) :
eventually_bdd_below f u :=
have A : (∀b, a ≤ b) → eventually_bdd_below f u :=
  assume M,
  eventually_bdd_below_of_bdd_below f u ⟨a, λy Hy, M y⟩,
have B : (∃b, b < a) → eventually_bdd_below f u :=
  assume ⟨b, Hb⟩,
  have eventually (λn, b < u n) f := (tendsto_orderable.1 H).1 b Hb,
  have eventually (λn, b ≤ u n) f :=
    eventually_of_eventually_of_imp this (λn, le_of_lt),
  eventually_bdd_below_iff_exists_eventually_le.2 ⟨b, this⟩,
begin
  cases (forall_le_or_exists_lt' a) with I J,
  apply A I,
  apply B J
end

end conditionally_complete_lattice_topology


section conditionally_complete_linear_order_topology
variables [topological_space β] [conditionally_complete_linear_order β] [orderable_topology β]

/--If a function is converging, its limsup coincides with its limit.-/
theorem Limsup_of_lim (H : tendsto u f (nhds a)) (_ : f ≠ ⊥) : Limsup f u = a :=
have A : {b | eventually (λ n, u n ≤ b) f} ≠ ∅ :=
  ne_empty_iff_exists_mem.2 (eventually_bdd_above_iff_exists_eventually_le.1 (eventually_bdd_above_of_tendsto H)),
have B : ∀b ∈ {b | eventually (λn, u n ≤ b) f}, a ≤ b :=
  assume b Hb,
  begin
    simp at Hb,
    by_contradiction C,
    simp at C,
    have E : eventually (λ (n : α), b < u n) f := (tendsto_orderable.1 H).1 _ C,
    have I : ∀n, b < u n ∧ u n ≤ b → false :=
      λn H, absurd H.1 (not_lt_of_le H.2),
    apply false_of_eventually_false ‹f ≠ ⊥› (eventually_of_eventually_of_imp (eventually_and_of_eventually_of_eventually E Hb) I),
  end,
have C : ∀w, a < w → (∃b ∈ {b : β | eventually (λ (n : α), u n ≤ b) f}, b < w) :=
  assume w Hw,
  have M : ∀m > a, eventually (λn, u n < m) f :=
    (tendsto_orderable.1 H).2,
  have W1 : (∃c, c < w ∧ a < c) → (∃b ∈ {b : β | eventually (λ (n : α), u n ≤ b) f}, b < w) :=
    assume ⟨c, Hc⟩,
    ⟨c, by simp; apply and.intro (eventually_of_eventually_of_imp (M c (Hc.2)) (λn, le_of_lt)) Hc.1⟩,
  have W2 : (¬∃c, c < w ∧ a < c) → (∃b ∈ {b : β | eventually (λ (n : α), u n ≤ b) f}, b < w) :=
    assume Hc,
    have I : ∀c, c < w → c ≤ a := by simp at Hc; apply Hc,
    ⟨a, by simp; apply and.intro (eventually_of_eventually_of_imp (M w Hw) (λn, I (u n))) Hw⟩,
  begin
    cases (classical.em (∃c, c < w ∧ a < c)) with I J,
    apply W1 I,
    apply W2 J
  end,
show Limsup f u = a, from cInf_intro A B C

/--If a function is converging, its liminf coincides with its limit.-/
theorem Liminf_of_lim (H : tendsto u f (nhds a)) (_ : f ≠ ⊥) : Liminf f u = a :=
have A : {b | eventually (λ n, b ≤ u n) f} ≠ ∅ :=
  ne_empty_iff_exists_mem.2 (eventually_bdd_below_iff_exists_eventually_le.1 (eventually_bdd_below_of_tendsto H)),
have B : ∀b ∈ {b | eventually (λn, b ≤ u n) f}, b ≤ a :=
  assume b Hb,
  begin
    simp at Hb,
    by_contradiction C,
    simp at C,
    have E : eventually (λn, u n < b) f := (tendsto_orderable.1 H).2 _ C,
    have I : ∀n, u n < b ∧ b ≤ u n → false :=
      λn H, absurd H.1 (not_lt_of_le H.2),
    apply false_of_eventually_false ‹f ≠ ⊥› (eventually_of_eventually_of_imp (eventually_and_of_eventually_of_eventually E Hb) I),
  end,
have C : ∀w, w < a → (∃b ∈ {b : β | eventually (λ (n : α), b ≤ u n) f}, w < b) :=
  assume w Hw,
  have M : ∀m < a, eventually (λn, m < u n) f :=
    (tendsto_orderable.1 H).1,
  have W1 : (∃c, w < c ∧ c < a) → (∃b ∈ {b : β | eventually (λ (n : α), b ≤ u n) f}, w < b) :=
    assume ⟨c, Hc⟩,
    ⟨c, by simp; apply and.intro (eventually_of_eventually_of_imp (M c (Hc.2)) (λn, le_of_lt)) Hc.1⟩,
  have W2 : (¬∃c, w < c ∧ c < a) → (∃b ∈ {b : β | eventually (λ (n : α), b ≤ u n) f}, w < b) :=
    assume Hc,
    have I : ∀c, w < c → a ≤ c := by simp at Hc; apply Hc,
    ⟨a, by simp; apply and.intro (eventually_of_eventually_of_imp (M w Hw) (λn, I (u n))) Hw⟩,
  begin
    cases (classical.em (∃c, w < c ∧ c < a)) with I J,
    apply W1 I,
    apply W2 J
  end,
show Liminf f u = a, from cSup_intro A B C

/--If the liminf and the limsup of a function coincide, then this function converges to
their common value, at least if the function is eventually bounded above and below.-/
theorem tendsto_of_cLiminf_eq_cLimsup (H : Liminf f u = Limsup f u) (Hu : eventually_bdd_above f u) (Hl : eventually_bdd_below f u) : tendsto u f (nhds (Limsup f u)) :=
have A : ∀a>Limsup f u, eventually (λn, u n < a) f :=
  assume a Ha, eventually_lt_of_cLimsup_lt Hu Ha,
have B : ∀a<Limsup f u, eventually (λn, a < u n) f :=
  assume a Ha, by rw [← H] at Ha; apply eventually_lt_of_lt_cLiminf Hl Ha ,
tendsto_orderable.2 (and.intro B A)

end conditionally_complete_linear_order_topology

section complete_linear_order_topology
variables [topological_space β] [complete_linear_order β] [orderable_topology β]

/--If the liminf and the limsup of a function coincide, then this function converges to
their common value.-/
theorem tendsto_of_Liminf_eq_Limsup (H : Liminf f u = Limsup f u) : tendsto u f (nhds (Limsup f u)) :=
tendsto_of_cLiminf_eq_cLimsup H (by simp) (by simp)

end complete_linear_order_topology

end filter
