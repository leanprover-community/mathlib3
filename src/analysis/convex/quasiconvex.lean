/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.function

/-!
# Quasiconvex and quasiconcave functions

This file defines quasiconvexity, quasiconcavity and quasilinearity of functions, which are
generalizations of unimodality and monotonicity. Convexity implies quasiconvexity, concavity implies
quasiconcavity, and monotonicity implies quasilinearity.

## Main declarations

* `quasiconvex_on 𝕜 s f`: Quasiconvexity of the function `f` on the set `s` with scalars `𝕜`. This
  means that, for all `r`, `{x ∈ s | f x ≤ r}` is `𝕜`-convex.
* `quasiconcave_on 𝕜 s f`: Quasiconcavity of the function `f` on the set `s` with scalars `𝕜`. This
  means that, for all `r`, `{x ∈ s | r ≤ f x}` is `𝕜`-convex.
* `quasilinear_on 𝕜 s f`: Quasilinearity of the function `f` on the set `s` with scalars `𝕜`. This
  means that `f` is both quasiconvex and quasiconcave.

## TODO

Prove that a quasilinear function between two linear orders is either monotone or antitone. This is
not hard but quite a pain to go about as there are many cases to consider.

## References

* https://en.wikipedia.org/wiki/Quasiconvex_function
-/

open set

variables {𝕜 E F β : Type*}

section ordered_semiring
variables [ordered_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [add_comm_monoid F]

section ordered_add_comm_monoid
variables (𝕜) [ordered_add_comm_monoid β] [has_scalar 𝕜 E] (s : set E) (f : E → β)

/-- A function is quasiconvex if all its sublevels are convex.
This means that, for all `r`, `{x ∈ s | f x ≤ r}` is `𝕜`-convex. -/
def quasiconvex_on : Prop :=
∀ r, convex 𝕜 {x ∈ s | f x ≤ r}

/-- A function is quasiconcave if all its superlevels are convex.
This means that, for all `r`, `{x ∈ s | r ≤ f x}` is `𝕜`-convex. -/
def quasiconcave_on : Prop :=
∀ r, convex 𝕜 {x ∈ s | r ≤ f x}

/-- A function is quasilinear if it is both quasiconvex and quasiconcave.
This means that, for all `r`,
the sets `{x ∈ s | f x ≤ r}` and `{x ∈ s | r ≤ f x}` are `𝕜`-convex. -/
def quasilinear_on : Prop :=
quasiconvex_on 𝕜 s f ∧ quasiconcave_on 𝕜 s f

variables {𝕜 s f}

lemma quasiconvex_on.dual (hf : quasiconvex_on 𝕜 s f) :
  @quasiconcave_on 𝕜 E (order_dual β) _ _ _ _ s f :=
hf

lemma quasiconcave_on.dual (hf : quasiconcave_on 𝕜 s f) :
  @quasiconvex_on 𝕜 E (order_dual β) _ _ _ _ s f :=
hf

lemma quasilinear_on.dual (hf : quasilinear_on 𝕜 s f) :
  @quasilinear_on 𝕜 E (order_dual β) _ _ _ _ s f :=
⟨hf.2, hf.1⟩

lemma convex.quasiconvex_on_of_convex_le (hs : convex 𝕜 s) (h : ∀ r, convex 𝕜 {x | f x ≤ r}) :
  quasiconvex_on 𝕜 s f :=
λ r, hs.inter (h r)

lemma convex.quasiconcave_on_of_convex_ge (hs : convex 𝕜 s) (h : ∀ r, convex 𝕜 {x | r ≤ f x}) :
  quasiconcave_on 𝕜 s f :=
@convex.quasiconvex_on_of_convex_le 𝕜 E (order_dual β) _ _ _ _ _ _ hs h

end ordered_add_comm_monoid

section linear_ordered_add_comm_monoid
variables [linear_ordered_add_comm_monoid β]

section has_scalar
variables [has_scalar 𝕜 E] {s : set E} {f g : E → β}

-- This only requires `directed_order β` but we don't have `directed_ordered_add_comm_monoid`
lemma quasiconvex_on.convex (hf : quasiconvex_on 𝕜 s f) : convex 𝕜 s :=
λ x y hx hy a b ha hb hab,  (hf _ ⟨hx, le_max_left _ _⟩ ⟨hy, le_max_right _ _⟩ ha hb hab).1

lemma quasiconcave_on.convex (hf : quasiconcave_on 𝕜 s f) : convex 𝕜 s :=
hf.dual.convex

lemma quasiconvex_on.sup (hf : quasiconvex_on 𝕜 s f) (hg : quasiconvex_on 𝕜 s g) :
  quasiconvex_on 𝕜 s (f ⊔ g) :=
begin
  intro r,
  simp_rw [pi.sup_def, sup_le_iff, ←set.sep_inter_sep],
  exact (hf r).inter (hg r),
end

lemma quasiconcave_on.inf (hf : quasiconcave_on 𝕜 s f) (hg : quasiconcave_on 𝕜 s g) :
  quasiconcave_on 𝕜 s (f ⊓ g) :=
hf.dual.sup hg

lemma quasiconvex_on_iff_le_max :
  quasiconvex_on 𝕜 s f ↔ convex 𝕜 s ∧
    ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ max (f x) (f y) :=
⟨λ hf, ⟨hf.convex, λ x y hx hy a b ha hb hab,
  (hf _ ⟨hx, le_max_left _ _⟩ ⟨hy, le_max_right _ _⟩ ha hb hab).2⟩,
  λ hf r x y hx hy a b ha hb hab,
  ⟨hf.1 hx.1 hy.1 ha hb hab, (hf.2 hx.1 hy.1 ha hb hab).trans $ max_le hx.2 hy.2⟩⟩

lemma quasiconcave_on_iff_min_le :
  quasiconcave_on 𝕜 s f ↔ convex 𝕜 s ∧
    ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
      min (f x) (f y) ≤ f (a • x + b • y) :=
@quasiconvex_on_iff_le_max 𝕜 E (order_dual β) _ _ _ _ _ _

lemma quasilinear_on_iff_mem_interval :
  quasilinear_on 𝕜 s f ↔ convex 𝕜 s ∧
    ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ∈ interval (f x) (f y) :=
begin
  rw [quasilinear_on, quasiconvex_on_iff_le_max, quasiconcave_on_iff_min_le, and_and_and_comm,
    and_self],
  apply and_congr_right',
  simp_rw [←forall_and_distrib, interval, mem_Icc, and_comm],
end

lemma quasiconvex_on.convex_lt (hf : quasiconvex_on 𝕜 s f) (r : β) : convex 𝕜 {x ∈ s | f x < r} :=
begin
  refine λ x y hx hy a b ha hb hab, _,
  have h := hf _ ⟨hx.1, le_max_left _ _⟩ ⟨hy.1, le_max_right _ _⟩ ha hb hab,
  exact ⟨h.1, h.2.trans_lt $ max_lt hx.2 hy.2⟩,
end

lemma quasiconcave_on.convex_gt (hf : quasiconcave_on 𝕜 s f) (r : β) : convex 𝕜 {x ∈ s | r < f x} :=
hf.dual.convex_lt r

end has_scalar

section ordered_smul
variables [has_scalar 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f : E → β}

lemma convex_on.quasiconvex_on (hf : convex_on 𝕜 s f) : quasiconvex_on 𝕜 s f :=
hf.convex_le

lemma concave_on.quasiconcave_on (hf : concave_on 𝕜 s f) : quasiconcave_on 𝕜 s f :=
hf.convex_ge

end ordered_smul
end linear_ordered_add_comm_monoid
end add_comm_monoid

section linear_ordered_add_comm_monoid
variables [linear_ordered_add_comm_monoid E] [ordered_add_comm_monoid β] [module 𝕜 E]
  [ordered_smul 𝕜 E] {s : set E} {f : E → β}

lemma monotone_on.quasiconvex_on (hf : monotone_on f s) (hs : convex 𝕜 s) : quasiconvex_on 𝕜 s f :=
hf.convex_le hs

lemma monotone_on.quasiconcave_on (hf : monotone_on f s) (hs : convex 𝕜 s) :
  quasiconcave_on 𝕜 s f :=
hf.convex_ge hs

lemma monotone_on.quasilinear_on (hf : monotone_on f s) (hs : convex 𝕜 s) : quasilinear_on 𝕜 s f :=
⟨hf.quasiconvex_on hs, hf.quasiconcave_on hs⟩

lemma antitone_on.quasiconvex_on (hf : antitone_on f s) (hs : convex 𝕜 s) : quasiconvex_on 𝕜 s f :=
hf.convex_le hs

lemma antitone_on.quasiconcave_on (hf : antitone_on f s) (hs : convex 𝕜 s) :
  quasiconcave_on 𝕜 s f :=
hf.convex_ge hs

lemma antitone_on.quasilinear_on (hf : antitone_on f s) (hs : convex 𝕜 s) : quasilinear_on 𝕜 s f :=
⟨hf.quasiconvex_on hs, hf.quasiconcave_on hs⟩

lemma monotone.quasiconvex_on (hf : monotone f) : quasiconvex_on 𝕜 univ f :=
(hf.monotone_on _).quasiconvex_on convex_univ

lemma monotone.quasiconcave_on (hf : monotone f) : quasiconcave_on 𝕜 univ f :=
(hf.monotone_on _).quasiconcave_on convex_univ

lemma monotone.quasilinear_on (hf : monotone f) : quasilinear_on 𝕜 univ f :=
⟨hf.quasiconvex_on, hf.quasiconcave_on⟩

lemma antitone.quasiconvex_on (hf : antitone f) : quasiconvex_on 𝕜 univ f :=
(hf.antitone_on _).quasiconvex_on convex_univ

lemma antitone.quasiconcave_on (hf : antitone f) : quasiconcave_on 𝕜 univ f :=
(hf.antitone_on _).quasiconcave_on convex_univ

lemma antitone.quasilinear_on (hf : antitone f) : quasilinear_on 𝕜 univ f :=
⟨hf.quasiconvex_on, hf.quasiconcave_on⟩

end linear_ordered_add_comm_monoid
end ordered_semiring
