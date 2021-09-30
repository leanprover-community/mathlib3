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


-/

open finset linear_map set
open_locale big_operators classical convex pointwise

lemma and_and_and_comm (a b c d : Prop) : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d :=
by rw [and_assoc, and_assoc, @and.left_comm b]

variables {𝕜 E F β : Type*}

section ordered_semiring
variables [ordered_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [add_comm_monoid F]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β]

section has_scalar
variables (𝕜) [has_scalar 𝕜 E] [has_scalar 𝕜 β] (s : set E) (f : E → β)

/-- Quasiconvexity of functions -/
def quasiconvex_on : Prop :=
∀ r, convex 𝕜 {x ∈ s | f x ≤ r}

/-- Quasiconcavity of functions -/
def quasiconcave_on : Prop :=
∀ r, convex 𝕜 {x ∈ s | r ≤ f x}

/-- Quasilinearity of functions -/
def quasilinear_on : Prop :=
quasiconvex_on 𝕜 s f ∧ quasiconcave_on 𝕜 s f

variables {𝕜}

lemma quasiconvex_on.dual (hf : quasiconvex_on 𝕜 s f) :
  @quasiconcave_on 𝕜 E (order_dual β) _ _ _ _ _ s f :=
hf

lemma quasiconcave_on.dual (hf : quasiconcave_on 𝕜 s f) :
  @quasiconvex_on 𝕜 E (order_dual β) _ _ _ _ _ s f :=
hf

lemma quasilinear_on.dual (hf : quasilinear_on 𝕜 s f) :
  @quasilinear_on 𝕜 E (order_dual β) _ _ _ _ _ s f :=
⟨hf.2, hf.1⟩

end has_scalar
end ordered_add_comm_monoid

section linear_ordered_add_comm_monoid
variables [linear_ordered_add_comm_monoid β]

section has_scalar
variables [has_scalar 𝕜 E] [has_scalar 𝕜 β] {s : set E} {f : E → β}

-- This only requires `directed_order β` but we don't have `directed_ordered_add_comm_monoid`
lemma quasiconvex_on.convex (hf : quasiconvex_on 𝕜 s f) : convex 𝕜 s :=
λ x y hx hy a b ha hb hab,  (hf _ ⟨hx, le_max_left _ _⟩ ⟨hy, le_max_right _ _⟩ ha hb hab).1

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
@quasiconvex_on_iff_le_max 𝕜 E (order_dual β) _ _ _ _ _ _ _

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
@quasiconvex_on.convex_lt 𝕜 E (order_dual β) _ _ _ _ _ _ _ hf r

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
variables [linear_ordered_add_comm_monoid E]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β]

section has_scalar
variables [module 𝕜 E] [ordered_smul 𝕜 E] [has_scalar 𝕜 β] {s : set E} {f : E → β}

lemma monotone.convex_le (hf : monotone f) (r : β) : convex 𝕜 {x | f x ≤ r} :=
begin
  refine λ x y hx hy a b ha hb hab, (hf (convex.combo_le_max x y ha hb hab)).trans _,
  cases le_total x y,
  { rwa max_eq_right h },
  { rwa max_eq_left h }
end

lemma monotone.convex_ge (hf : monotone f) (r : β) : convex 𝕜 {x | r ≤ f x} :=
begin
  refine λ x y hx hy a b ha hb hab, le_trans _ (hf (convex.min_le_combo x y ha hb hab)),
  cases le_total x y,
  { rwa min_eq_left h },
  { rwa min_eq_right h }
end

lemma monotone_on.quasiconvex_on (hf : monotone f) (hs : convex 𝕜 s) : quasiconvex_on 𝕜 s f :=
λ r, hs.inter (hf.convex_le r)

lemma monotone_on.quasiconcave_on (hf : monotone f) (hs : convex 𝕜 s) : quasiconcave_on 𝕜 s f :=
λ r, hs.inter (hf.convex_ge r)

lemma monotone_on.quasilinear_on (hf : monotone f) (hs : convex 𝕜 s) : quasilinear_on 𝕜 s f :=
⟨hf.quasiconvex_on, hf.quasiconcave_on⟩

lemma quasilinear_on.monotone_on_or_antitone_on (hf : quasilinear_on 𝕜 univ f) :
  monotone f ∨ antitone f :=
begin
  rintro x y h,
  sorry
end

end has_scalar
end ordered_add_comm_monoid
end linear_ordered_add_comm_monoid
end ordered_semiring

section whut
variables [ordered_semiring 𝕜] [ordered_add_comm_monoid E]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β]

section has_scalar
variables [module 𝕜 E] [has_scalar 𝕜 β] (s : set E) (f : E → β)

lemma monotone_on.quasiconvex_on (hf : monotone f) (hs : convex 𝕜 s) : quasiconvex_on 𝕜 s f :=
begin
  refine λ r, hs.inter _,
end

lemma monotone_on.quasilinear_on (hf : monotone f) (hs : convex 𝕜 s) : quasilinear_on 𝕜 s f :=
begin
  refine λ r, _,
end

lemma quasilinear_on_iff_monotone_on_or_antitone_on :
  quasilinear_on 𝕜 s f ↔
    monotone f ∨ antitone f :=
begin

end

end whut
