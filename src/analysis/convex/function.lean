/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, François Dupuis
-/
import analysis.convex.basic
import tactic.field_simp
import tactic.linarith
import tactic.ring

/-!
# Convex and concave functions

This file defines convex and concave functions in vector spaces and proves the finite Jensen
inequality. The integral version can be found in `analysis.convex.integral`.

A function `f : E → β` is `convex_on` a set `s` if `s` is itself a convex set, and for any two
points `x y ∈ s`, the segment joining `(x, f x)` to `(y, f y)` is above the graph of `f`.
Equivalently, `convex_on 𝕜 f s` means that the epigraph `{p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}` is
a convex set.

## Main declarations

* `convex_on 𝕜 s f`: The function `f` is convex on `s` with scalars `𝕜`.
* `concave_on 𝕜 s f`: The function `f` is concave on `s` with scalars `𝕜`.
* `strict_convex_on 𝕜 s f`: The function `f` is strictly convex on `s` with scalars `𝕜`.
* `strict_concave_on 𝕜 s f`: The function `f` is strictly concave on `s` with scalars `𝕜`.
-/

open finset linear_map set
open_locale big_operators classical convex pointwise

variables {𝕜 E F β ι : Type*}

section ordered_semiring
variables [ordered_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [add_comm_monoid F]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β]

section has_scalar
variables (𝕜) [has_scalar 𝕜 E] [has_scalar 𝕜 β] (s : set E) (f : E → β)

/-- Convexity of functions -/
def convex_on : Prop :=
convex 𝕜 s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y

/-- Concavity of functions -/
def concave_on : Prop :=
convex 𝕜 s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y ≤ f (a • x + b • y)

/-- Strict convexity of functions -/
def strict_convex_on : Prop :=
convex 𝕜 s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) < a • f x + b • f y

/-- Strict concavity of functions -/
def strict_concave_on : Prop :=
convex 𝕜 s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
    a • f x + b • f y < f (a • x + b • y)

variables {𝕜 s f}

open order_dual (to_dual of_dual)

lemma convex_on.dual (hf : convex_on 𝕜 s f) : concave_on 𝕜 s (to_dual ∘ f) := hf

lemma concave_on.dual (hf : concave_on 𝕜 s f) : convex_on 𝕜 s (to_dual ∘ f) := hf

lemma strict_convex_on.dual (hf : strict_convex_on 𝕜 s f) : strict_concave_on 𝕜 s (to_dual ∘ f) :=
hf

lemma strict_concave_on.dual (hf : strict_concave_on 𝕜 s f) : strict_convex_on 𝕜 s (to_dual ∘ f) :=
hf

lemma convex_on_id {s : set β} (hs : convex 𝕜 s) : convex_on 𝕜 s id := ⟨hs, by { intros, refl }⟩

lemma concave_on_id {s : set β} (hs : convex 𝕜 s) : concave_on 𝕜 s id := ⟨hs, by { intros, refl }⟩

lemma convex_on.subset {t : set E} (hf : convex_on 𝕜 t f) (hst : s ⊆ t) (hs : convex 𝕜 s) :
  convex_on 𝕜 s f :=
⟨hs, λ x y hx hy, hf.2 (hst hx) (hst hy)⟩

lemma concave_on.subset {t : set E} (hf : concave_on 𝕜 t f) (hst : s ⊆ t) (hs : convex 𝕜 s) :
  concave_on 𝕜 s f :=
⟨hs, λ x y hx hy, hf.2 (hst hx) (hst hy)⟩

lemma strict_convex_on.subset {t : set E} (hf : strict_convex_on 𝕜 t f) (hst : s ⊆ t)
  (hs : convex 𝕜 s) :
  strict_convex_on 𝕜 s f :=
⟨hs, λ x y hx hy, hf.2 (hst hx) (hst hy)⟩

lemma strict_concave_on.subset {t : set E} (hf : strict_concave_on 𝕜 t f) (hst : s ⊆ t)
  (hs : convex 𝕜 s) :
  strict_concave_on 𝕜 s f :=
⟨hs, λ x y hx hy, hf.2 (hst hx) (hst hy)⟩

end has_scalar

section distrib_mul_action
variables [has_scalar 𝕜 E] [distrib_mul_action 𝕜 β] {s : set E} {f g : E → β}

lemma convex_on.add (hf : convex_on 𝕜 s f) (hg : convex_on 𝕜 s g) :
  convex_on 𝕜 s (f + g) :=
⟨hf.1, λ x y hx hy a b ha hb hab,
  calc
    f (a • x + b • y) + g (a • x + b • y) ≤ (a • f x + b • f y) + (a • g x + b • g y)
      : add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    ... = a • (f x + g x) + b • (f y + g y) : by rw [smul_add, smul_add, add_add_add_comm]⟩

lemma concave_on.add (hf : concave_on 𝕜 s f) (hg : concave_on 𝕜 s g) :
  concave_on 𝕜 s (f + g) :=
hf.dual.add hg

end distrib_mul_action

section module
variables [has_scalar 𝕜 E] [module 𝕜 β] {s : set E} {f : E → β}

lemma convex_on_const (c : β) (hs : convex 𝕜 s) : convex_on 𝕜 s (λ x:E, c) :=
⟨hs, λ x y _ _ a b _ _ hab, (convex.combo_self hab c).ge⟩

lemma concave_on_const (c : β) (hs : convex 𝕜 s) : concave_on 𝕜 s (λ x:E, c) :=
@convex_on_const _ _ βᵒᵈ _ _ _ _ _ _ c hs

lemma convex_on_of_convex_epigraph (h : convex 𝕜 {p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}) :
  convex_on 𝕜 s f :=
⟨λ x y hx hy a b ha hb hab, (@h (x, f x) (y, f y) ⟨hx, le_rfl⟩ ⟨hy, le_rfl⟩ a b ha hb hab).1,
  λ x y hx hy a b ha hb hab, (@h (x, f x) (y, f y) ⟨hx, le_rfl⟩ ⟨hy, le_rfl⟩ a b ha hb hab).2⟩

lemma concave_on_of_convex_hypograph (h : convex 𝕜 {p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1}) :
  concave_on 𝕜 s f :=
@convex_on_of_convex_epigraph 𝕜  E βᵒᵈ _ _ _ _ _ _ _ h

end module

section ordered_smul
variables [has_scalar 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f : E → β}

lemma convex_on.convex_le (hf : convex_on 𝕜 s f) (r : β) :
  convex 𝕜 {x ∈ s | f x ≤ r} :=
λ x y hx hy a b ha hb hab, ⟨hf.1 hx.1 hy.1 ha hb hab,
  calc
    f (a • x + b • y) ≤ a • f x + b • f y : hf.2 hx.1 hy.1 ha hb hab
                  ... ≤ a • r + b • r     : add_le_add (smul_le_smul_of_nonneg hx.2 ha)
                                              (smul_le_smul_of_nonneg hy.2 hb)
                  ... = r                 : convex.combo_self hab r⟩

lemma concave_on.convex_ge (hf : concave_on 𝕜 s f) (r : β) :
  convex 𝕜 {x ∈ s | r ≤ f x} :=
hf.dual.convex_le r

lemma convex_on.convex_epigraph (hf : convex_on 𝕜 s f) :
  convex 𝕜 {p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  rintro ⟨x, r⟩ ⟨y, t⟩ ⟨hx, hr⟩ ⟨hy, ht⟩ a b ha hb hab,
  refine ⟨hf.1 hx hy ha hb hab, _⟩,
  calc f (a • x + b • y) ≤ a • f x + b • f y : hf.2 hx hy ha hb hab
  ... ≤ a • r + b • t : add_le_add (smul_le_smul_of_nonneg hr ha)
                            (smul_le_smul_of_nonneg ht hb)
end

lemma concave_on.convex_hypograph (hf : concave_on 𝕜 s f) :
  convex 𝕜 {p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
hf.dual.convex_epigraph

lemma convex_on_iff_convex_epigraph :
  convex_on 𝕜 s f ↔ convex 𝕜 {p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
⟨convex_on.convex_epigraph, convex_on_of_convex_epigraph⟩

lemma concave_on_iff_convex_hypograph :
  concave_on 𝕜 s f ↔ convex 𝕜 {p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
@convex_on_iff_convex_epigraph 𝕜 E βᵒᵈ _ _ _ _ _ _ _ f

end ordered_smul

section module
variables [module 𝕜 E] [has_scalar 𝕜 β] {s : set E} {f : E → β}

/-- Right translation preserves convexity. -/
lemma convex_on.translate_right (hf : convex_on 𝕜 s f) (c : E) :
  convex_on 𝕜 ((λ z, c + z) ⁻¹' s) (f ∘ (λ z, c + z)) :=
⟨hf.1.translate_preimage_right _, λ x y hx hy a b ha hb hab,
  calc
    f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y))
        : by rw [smul_add, smul_add, add_add_add_comm, convex.combo_self hab]
    ... ≤ a • f (c + x) + b • f (c + y) : hf.2 hx hy ha hb hab⟩

/-- Right translation preserves concavity. -/
lemma concave_on.translate_right (hf : concave_on 𝕜 s f) (c : E) :
  concave_on 𝕜 ((λ z, c + z) ⁻¹' s) (f ∘ (λ z, c + z)) :=
hf.dual.translate_right _

/-- Left translation preserves convexity. -/
lemma convex_on.translate_left (hf : convex_on 𝕜 s f) (c : E) :
  convex_on 𝕜 ((λ z, c + z) ⁻¹' s) (f ∘ (λ z, z + c)) :=
by simpa only [add_comm] using hf.translate_right _

/-- Left translation preserves concavity. -/
lemma concave_on.translate_left (hf : concave_on 𝕜 s f) (c : E) :
  concave_on 𝕜 ((λ z, c + z) ⁻¹' s) (f ∘ (λ z, z + c)) :=
hf.dual.translate_left _

end module

section module
variables [module 𝕜 E] [module 𝕜 β]

lemma convex_on_iff_forall_pos {s : set E} {f : E → β} :
  convex_on 𝕜 s f ↔ convex 𝕜 s ∧
    ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1
    → f (a • x + b • y) ≤ a • f x + b • f y :=
begin
  refine and_congr_right' ⟨λ h x y hx hy a b ha hb hab, h hx hy ha.le hb.le hab,
    λ h x y hx hy a b ha hb hab, _⟩,
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [zero_add] at hab, subst b, simp_rw [zero_smul, zero_add, one_smul] },
  obtain rfl | hb' := hb.eq_or_lt,
  { rw [add_zero] at hab, subst a, simp_rw [zero_smul, add_zero, one_smul] },
  exact h hx hy ha' hb' hab,
end

lemma concave_on_iff_forall_pos {s : set E} {f : E → β} :
  concave_on 𝕜 s f ↔ convex 𝕜 s ∧
    ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1
    → a • f x + b • f y ≤ f (a • x + b • y) :=
@convex_on_iff_forall_pos 𝕜 E βᵒᵈ _ _ _ _ _ _ _

lemma convex_on_iff_pairwise_pos {s : set E} {f : E → β} :
  convex_on 𝕜 s f ↔ convex 𝕜 s ∧
    s.pairwise (λ x y, ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1
    → f (a • x + b • y) ≤ a • f x + b • f y) :=
begin
  rw convex_on_iff_forall_pos,
  refine and_congr_right' ⟨λ h x hx y hy _ a b ha hb hab, h hx hy ha hb hab,
    λ h x y hx hy a b ha hb hab, _⟩,
  obtain rfl | hxy := eq_or_ne x y,
  { rw [convex.combo_self hab, convex.combo_self hab] },
  exact h hx hy hxy ha hb hab,
end

lemma concave_on_iff_pairwise_pos {s : set E} {f : E → β} :
  concave_on 𝕜 s f ↔ convex 𝕜 s ∧
   s.pairwise (λ x y, ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1
    → a • f x + b • f y ≤ f (a • x + b • y)) :=
@convex_on_iff_pairwise_pos 𝕜 E βᵒᵈ _ _ _ _ _ _ _

/-- A linear map is convex. -/
lemma linear_map.convex_on (f : E →ₗ[𝕜] β) {s : set E} (hs : convex 𝕜 s) : convex_on 𝕜 s f :=
⟨hs, λ _ _ _ _ _ _ _ _ _, by rw [f.map_add, f.map_smul, f.map_smul]⟩

/-- A linear map is concave. -/
lemma linear_map.concave_on (f : E →ₗ[𝕜] β) {s : set E} (hs : convex 𝕜 s) : concave_on 𝕜 s f :=
⟨hs, λ _ _ _ _ _ _ _ _ _, by rw [f.map_add, f.map_smul, f.map_smul]⟩

lemma strict_convex_on.convex_on {s : set E} {f : E → β} (hf : strict_convex_on 𝕜 s f) :
  convex_on 𝕜 s f :=
convex_on_iff_pairwise_pos.mpr ⟨hf.1, λ x hx y hy hxy a b ha hb hab, (hf.2 hx hy hxy ha hb hab).le⟩

lemma strict_concave_on.concave_on {s : set E} {f : E → β} (hf : strict_concave_on 𝕜 s f) :
  concave_on 𝕜 s f :=
hf.dual.convex_on

section ordered_smul
variables [ordered_smul 𝕜 β] {s : set E} {f : E → β}

lemma strict_convex_on.convex_lt (hf : strict_convex_on 𝕜 s f) (r : β) :
  convex 𝕜 {x ∈ s | f x < r} :=
convex_iff_pairwise_pos.2 $ λ x hx y hy hxy a b ha hb hab, ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
  calc
    f (a • x + b • y) < a • f x + b • f y : hf.2 hx.1 hy.1 hxy ha hb hab
                  ... ≤ a • r + b • r     : add_le_add (smul_lt_smul_of_pos hx.2 ha).le
                                              (smul_lt_smul_of_pos hy.2 hb).le
                  ... = r                 : convex.combo_self hab r⟩

lemma strict_concave_on.convex_gt (hf : strict_concave_on 𝕜 s f) (r : β) :
  convex 𝕜 {x ∈ s | r < f x} :=
hf.dual.convex_lt r

end ordered_smul

section linear_order
variables [linear_order E] {s : set E} {f : E → β}

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is convex, it suffices to
verify the inequality `f (a • x + b • y) ≤ a • f x + b • f y` only for `x < y` and positive `a`,
`b`. The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order.
-/
lemma linear_order.convex_on_of_lt (hs : convex 𝕜 s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y) : convex_on 𝕜 s f :=
begin
  refine convex_on_iff_pairwise_pos.2 ⟨hs, λ x hx y hy hxy a b ha hb hab, _⟩,
  wlog h : x ≤ y using [x y a b, y x b a],
  { exact le_total _ _ },
  exact hf hx hy (h.lt_of_ne hxy) ha hb hab,
end

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is concave it suffices to
verify the inequality `a • f x + b • f y ≤ f (a • x + b • y)` for `x < y` and positive `a`, `b`. The
main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with lexicographic order. -/
lemma linear_order.concave_on_of_lt (hs : convex 𝕜 s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
     a • f x + b • f y ≤ f (a • x + b • y)) : concave_on 𝕜 s f :=
@linear_order.convex_on_of_lt _ _ βᵒᵈ _ _ _ _ _ _ s f hs hf

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is convex, it suffices to
verify the inequality `f (a • x + b • y) ≤ a • f x + b • f y` for `x < y` and positive `a`, `b`. The
main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order. -/
lemma linear_order.strict_convex_on_of_lt (hs : convex 𝕜 s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) < a • f x + b • f y) : strict_convex_on 𝕜 s f :=
begin
  refine ⟨hs, λ x y hx hy hxy a b ha hb hab, _⟩,
  wlog h : x ≤ y using [x y a b, y x b a],
  { exact le_total _ _ },
  exact hf hx hy (h.lt_of_ne hxy) ha hb hab,
end

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is concave it suffices to
verify the inequality `a • f x + b • f y ≤ f (a • x + b • y)` for `x < y` and positive `a`, `b`. The
main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order. -/
lemma linear_order.strict_concave_on_of_lt (hs : convex 𝕜 s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
     a • f x + b • f y < f (a • x + b • y)) : strict_concave_on 𝕜 s f :=
@linear_order.strict_convex_on_of_lt _ _ βᵒᵈ _ _ _ _ _ _ _ _ hs hf

end linear_order
end module

section module
variables [module 𝕜 E] [module 𝕜 F] [has_scalar 𝕜 β]

/-- If `g` is convex on `s`, so is `(f ∘ g)` on `f ⁻¹' s` for a linear `f`. -/
lemma convex_on.comp_linear_map {f : F → β} {s : set F} (hf : convex_on 𝕜 s f) (g : E →ₗ[𝕜] F) :
  convex_on 𝕜 (g ⁻¹' s) (f ∘ g) :=
⟨hf.1.linear_preimage _, λ x y hx hy a b ha hb hab,
  calc
    f (g (a • x + b • y)) = f (a • (g x) + b • (g y)) : by rw [g.map_add, g.map_smul, g.map_smul]
                      ... ≤ a • f (g x) + b • f (g y) : hf.2 hx hy ha hb hab⟩

/-- If `g` is concave on `s`, so is `(g ∘ f)` on `f ⁻¹' s` for a linear `f`. -/
lemma concave_on.comp_linear_map {f : F → β} {s : set F} (hf : concave_on 𝕜 s f) (g : E →ₗ[𝕜] F) :
  concave_on 𝕜 (g ⁻¹' s) (f ∘ g) :=
hf.dual.comp_linear_map g

end module
end ordered_add_comm_monoid

section ordered_cancel_add_comm_monoid
variables [ordered_cancel_add_comm_monoid β]

section distrib_mul_action
variables [has_scalar 𝕜 E] [distrib_mul_action 𝕜 β] {s : set E} {f g : E → β}

lemma strict_convex_on.add_convex_on (hf : strict_convex_on 𝕜 s f) (hg : convex_on 𝕜 s g) :
  strict_convex_on 𝕜 s (f + g) :=
⟨hf.1, λ x y hx hy hxy a b ha hb hab,
  calc
    f (a • x + b • y) + g (a • x + b • y) < (a • f x + b • f y) + (a • g x + b • g y)
      : add_lt_add_of_lt_of_le (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy ha.le hb.le hab)
    ... = a • (f x + g x) + b • (f y + g y) : by rw [smul_add, smul_add, add_add_add_comm]⟩

lemma convex_on.add_strict_convex_on (hf : convex_on 𝕜 s f) (hg : strict_convex_on 𝕜 s g) :
  strict_convex_on 𝕜 s (f + g) :=
(add_comm g f) ▸ hg.add_convex_on hf

lemma strict_convex_on.add (hf : strict_convex_on 𝕜 s f) (hg : strict_convex_on 𝕜 s g) :
  strict_convex_on 𝕜 s (f + g) :=
⟨hf.1, λ x y hx hy hxy a b ha hb hab,
  calc
    f (a • x + b • y) + g (a • x + b • y) < (a • f x + b • f y) + (a • g x + b • g y)
      : add_lt_add (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy hxy ha hb hab)
    ... = a • (f x + g x) + b • (f y + g y) : by rw [smul_add, smul_add, add_add_add_comm]⟩

lemma strict_concave_on.add_concave_on (hf : strict_concave_on 𝕜 s f) (hg : concave_on 𝕜 s g) :
  strict_concave_on 𝕜 s (f + g) :=
hf.dual.add_convex_on hg.dual

lemma concave_on.add_strict_concave_on (hf : concave_on 𝕜 s f) (hg : strict_concave_on 𝕜 s g) :
  strict_concave_on 𝕜 s (f + g) :=
hf.dual.add_strict_convex_on hg.dual

lemma strict_concave_on.add (hf : strict_concave_on 𝕜 s f) (hg : strict_concave_on 𝕜 s g) :
  strict_concave_on 𝕜 s (f + g) :=
hf.dual.add hg

end distrib_mul_action

section module
variables [module 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f : E → β}

lemma convex_on.convex_lt (hf : convex_on 𝕜 s f) (r : β) : convex 𝕜 {x ∈ s | f x < r} :=
convex_iff_forall_pos.2 $ λ x y hx hy a b ha hb hab, ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
  calc
    f (a • x + b • y)
        ≤ a • f x + b • f y : hf.2 hx.1 hy.1 ha.le hb.le hab
    ... < a • r + b • r     : add_lt_add_of_lt_of_le (smul_lt_smul_of_pos hx.2 ha)
                                (smul_le_smul_of_nonneg hy.2.le hb.le)
    ... = r                 : convex.combo_self hab _⟩

lemma concave_on.convex_gt (hf : concave_on 𝕜 s f) (r : β) : convex 𝕜 {x ∈ s | r < f x} :=
hf.dual.convex_lt r

lemma convex_on.open_segment_subset_strict_epigraph (hf : convex_on 𝕜 s f) (p q : E × β)
  (hp : p.1 ∈ s ∧ f p.1 < p.2) (hq : q.1 ∈ s ∧ f q.1 ≤ q.2) :
  open_segment 𝕜 p q ⊆ {p : E × β | p.1 ∈ s ∧ f p.1 < p.2} :=
begin
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩,
  refine ⟨hf.1 hp.1 hq.1 ha.le hb.le hab, _⟩,
  calc f (a • p.1 + b • q.1) ≤ a • f p.1 + b • f q.1 : hf.2 hp.1 hq.1 ha.le hb.le hab
  ... < a • p.2 + b • q.2 :
    add_lt_add_of_lt_of_le (smul_lt_smul_of_pos hp.2 ha) (smul_le_smul_of_nonneg hq.2 hb.le)
end

lemma concave_on.open_segment_subset_strict_hypograph (hf : concave_on 𝕜 s f) (p q : E × β)
  (hp : p.1 ∈ s ∧ p.2 < f p.1) (hq : q.1 ∈ s ∧ q.2 ≤ f q.1) :
  open_segment 𝕜 p q ⊆ {p : E × β | p.1 ∈ s ∧ p.2 < f p.1} :=
hf.dual.open_segment_subset_strict_epigraph p q hp hq

lemma convex_on.convex_strict_epigraph (hf : convex_on 𝕜 s f) :
  convex 𝕜 {p : E × β | p.1 ∈ s ∧ f p.1 < p.2} :=
convex_iff_open_segment_subset.mpr $
  λ p q hp hq, hf.open_segment_subset_strict_epigraph p q hp ⟨hq.1, hq.2.le⟩

lemma concave_on.convex_strict_hypograph (hf : concave_on 𝕜 s f) :
  convex 𝕜 {p : E × β | p.1 ∈ s ∧ p.2 < f p.1} :=
hf.dual.convex_strict_epigraph

end module
end ordered_cancel_add_comm_monoid

section linear_ordered_add_comm_monoid
variables [linear_ordered_add_comm_monoid β] [has_scalar 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β]
  {s : set E} {f g : E → β}

/-- The pointwise maximum of convex functions is convex. -/
lemma convex_on.sup (hf : convex_on 𝕜 s f) (hg : convex_on 𝕜 s g) :
  convex_on 𝕜 s (f ⊔ g) :=
begin
  refine ⟨hf.left, λ x y hx hy a b ha hb hab, sup_le _ _⟩,
  { calc f (a • x + b • y) ≤ a • f x + b • f y : hf.right hx hy ha hb hab
     ...                   ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) : add_le_add
     (smul_le_smul_of_nonneg le_sup_left ha)
     (smul_le_smul_of_nonneg le_sup_left hb) },
  { calc g (a • x + b • y) ≤ a • g x + b • g y : hg.right hx hy ha hb hab
     ...                   ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) : add_le_add
     (smul_le_smul_of_nonneg le_sup_right ha)
     (smul_le_smul_of_nonneg le_sup_right hb) }
end

/-- The pointwise minimum of concave functions is concave. -/
lemma concave_on.inf (hf : concave_on 𝕜 s f) (hg : concave_on 𝕜 s g) :
  concave_on 𝕜 s (f ⊓ g) :=
hf.dual.sup hg

/-- The pointwise maximum of strictly convex functions is strictly convex. -/
lemma strict_convex_on.sup (hf : strict_convex_on 𝕜 s f) (hg : strict_convex_on 𝕜 s g) :
  strict_convex_on 𝕜 s (f ⊔ g) :=
⟨hf.left, λ x y hx hy hxy a b ha hb hab, max_lt
  (calc f (a • x + b • y) < a • f x + b • f y : hf.2 hx hy hxy ha hb hab
    ...                   ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) : add_le_add
    (smul_le_smul_of_nonneg le_sup_left ha.le)
    (smul_le_smul_of_nonneg le_sup_left hb.le))
  (calc g (a • x + b • y) < a • g x + b • g y : hg.2 hx hy hxy ha hb hab
    ...                   ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) : add_le_add
    (smul_le_smul_of_nonneg le_sup_right ha.le)
    (smul_le_smul_of_nonneg le_sup_right hb.le))⟩

/-- The pointwise minimum of strictly concave functions is strictly concave. -/
lemma strict_concave_on.inf (hf : strict_concave_on 𝕜 s f) (hg : strict_concave_on 𝕜 s g) :
   strict_concave_on 𝕜 s (f ⊓ g) :=
hf.dual.sup hg

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment' (hf : convex_on 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
  {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  f (a • x + b • y) ≤ max (f x) (f y) :=
calc
  f (a • x + b • y) ≤ a • f x + b • f y : hf.2 hx hy ha hb hab
  ... ≤ a • max (f x) (f y) + b • max (f x) (f y) :
    add_le_add (smul_le_smul_of_nonneg (le_max_left _ _) ha)
      (smul_le_smul_of_nonneg (le_max_right _ _) hb)
  ... = max (f x) (f y) : convex.combo_self hab _

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.ge_on_segment' (hf : concave_on 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
  {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  min (f x) (f y) ≤ f (a • x + b • y) :=
hf.dual.le_on_segment' hx hy ha hb hab

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment (hf : convex_on 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
  (hz : z ∈ [x -[𝕜] y]) :
  f z ≤ max (f x) (f y) :=
let ⟨a, b, ha, hb, hab, hz⟩ := hz in hz ▸ hf.le_on_segment' hx hy ha hb hab

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.ge_on_segment (hf : concave_on 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
  (hz : z ∈ [x -[𝕜] y]) :
  min (f x) (f y) ≤ f z :=
hf.dual.le_on_segment hx hy hz

/-- A strictly convex function on an open segment is strictly upper-bounded by the max of its
endpoints. -/
lemma strict_convex_on.lt_on_open_segment' (hf : strict_convex_on 𝕜 s f) {x y : E} (hx : x ∈ s)
  (hy : y ∈ s) (hxy : x ≠ y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
  f (a • x + b • y) < max (f x) (f y) :=
calc
  f (a • x + b • y) < a • f x + b • f y : hf.2 hx hy hxy ha hb hab
  ... ≤ a • max (f x) (f y) + b • max (f x) (f y) :
    add_le_add (smul_le_smul_of_nonneg (le_max_left _ _) ha.le)
      (smul_le_smul_of_nonneg (le_max_right _ _) hb.le)
  ... = max (f x) (f y) : convex.combo_self hab _

/-- A strictly concave function on an open segment is strictly lower-bounded by the min of its
endpoints. -/
lemma strict_concave_on.lt_on_open_segment' (hf : strict_concave_on 𝕜 s f) {x y : E} (hx : x ∈ s)
  (hy : y ∈ s) (hxy : x ≠ y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
  min (f x) (f y) < f (a • x + b • y) :=
hf.dual.lt_on_open_segment' hx hy hxy ha hb hab

/-- A strictly convex function on an open segment is strictly upper-bounded by the max of its
endpoints. -/
lemma strict_convex_on.lt_on_open_segment (hf : strict_convex_on 𝕜 s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hxy : x ≠ y) (hz : z ∈ open_segment 𝕜 x y) :
  f z < max (f x) (f y) :=
let ⟨a, b, ha, hb, hab, hz⟩ := hz in hz ▸ hf.lt_on_open_segment' hx hy hxy ha hb hab

/-- A strictly concave function on an open segment is strictly lower-bounded by the min of its
endpoints. -/
lemma strict_concave_on.lt_on_open_segment (hf : strict_concave_on 𝕜 s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hxy : x ≠ y) (hz : z ∈ open_segment 𝕜 x y) :
  min (f x) (f y) < f z :=
hf.dual.lt_on_open_segment hx hy hxy hz

end linear_ordered_add_comm_monoid

section linear_ordered_cancel_add_comm_monoid
variables [linear_ordered_cancel_add_comm_monoid β]

section ordered_smul
variables [has_scalar 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f g : E → β}

lemma convex_on.le_left_of_right_le' (hf : convex_on 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
  {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) (hfy : f y ≤ f (a • x + b • y)) :
  f (a • x + b • y) ≤ f x :=
le_of_not_lt $ λ h, lt_irrefl (f (a • x + b • y)) $
  calc
    f (a • x + b • y)
        ≤ a • f x + b • f y : hf.2 hx hy ha.le hb hab
    ... < a • f (a • x + b • y) + b • f (a • x + b • y)
        : add_lt_add_of_lt_of_le (smul_lt_smul_of_pos h ha) (smul_le_smul_of_nonneg hfy hb)
    ... = f (a • x + b • y) : convex.combo_self hab _

lemma concave_on.left_le_of_le_right' (hf : concave_on 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
  {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) (hfy : f (a • x + b • y) ≤ f y) :
  f x ≤ f (a • x + b • y) :=
hf.dual.le_left_of_right_le' hx hy ha hb hab hfy

lemma convex_on.le_right_of_left_le' (hf : convex_on 𝕜 s f) {x y : E} {a b : 𝕜}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1)
  (hfx : f x ≤ f (a • x + b • y)) :
  f (a • x + b • y) ≤ f y :=
begin
  rw add_comm at ⊢ hab hfx,
  exact hf.le_left_of_right_le' hy hx hb ha hab hfx,
end

lemma concave_on.le_right_of_left_le' (hf : concave_on 𝕜 s f) {x y : E} {a b : 𝕜}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1)
  (hfx : f (a • x + b • y) ≤ f x) :
  f y ≤ f (a • x + b • y) :=
hf.dual.le_right_of_left_le' hx hy ha hb hab hfx

lemma convex_on.le_left_of_right_le (hf : convex_on 𝕜 s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment 𝕜 x y) (hyz : f y ≤ f z) :
  f z ≤ f x :=
begin
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz,
  exact hf.le_left_of_right_le' hx hy ha hb.le hab hyz,
end

lemma concave_on.left_le_of_le_right (hf : concave_on 𝕜 s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment 𝕜 x y) (hyz : f z ≤ f y) :
  f x ≤ f z :=
hf.dual.le_left_of_right_le hx hy hz hyz

lemma convex_on.le_right_of_left_le (hf : convex_on 𝕜 s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment 𝕜 x y) (hxz : f x ≤ f z) :
  f z ≤ f y :=
begin
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz,
  exact hf.le_right_of_left_le' hx hy ha.le hb hab hxz,
end

lemma concave_on.le_right_of_left_le (hf : concave_on 𝕜 s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment 𝕜 x y) (hxz : f z ≤ f x) :
  f y ≤ f z :=
hf.dual.le_right_of_left_le hx hy hz hxz

end ordered_smul

section module
variables [module 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f g : E → β}

/- The following lemmas don't require `module 𝕜 E` if you add the hypothesis `x ≠ y`. At the time of
the writing, we decided the resulting lemmas wouldn't be useful. Feel free to reintroduce them. -/
lemma strict_convex_on.lt_left_of_right_lt' (hf : strict_convex_on 𝕜 s f) {x y : E} (hx : x ∈ s)
  (hy : y ∈ s) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  (hfy : f y < f (a • x + b • y)) :
  f (a • x + b • y) < f x :=
not_le.1 $ λ h, lt_irrefl (f (a • x + b • y)) $
  calc
    f (a • x + b • y)
        < a • f x + b • f y : hf.2 hx hy begin
            rintro rfl,
            rw convex.combo_self hab at hfy,
            exact lt_irrefl _ hfy,
          end ha hb hab
    ... < a • f (a • x + b • y) + b • f (a • x + b • y)
        : add_lt_add_of_le_of_lt (smul_le_smul_of_nonneg h ha.le) (smul_lt_smul_of_pos hfy hb)
    ... = f (a • x + b • y) : convex.combo_self hab _

lemma strict_concave_on.left_lt_of_lt_right' (hf : strict_concave_on 𝕜 s f) {x y : E} (hx : x ∈ s)
  (hy : y ∈ s) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  (hfy : f (a • x + b • y) < f y) :
  f x < f (a • x + b • y) :=
hf.dual.lt_left_of_right_lt' hx hy ha hb hab hfy

lemma strict_convex_on.lt_right_of_left_lt' (hf : strict_convex_on 𝕜 s f) {x y : E} {a b : 𝕜}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  (hfx : f x < f (a • x + b • y)) :
  f (a • x + b • y) < f y :=
begin
  rw add_comm at ⊢ hab hfx,
  exact hf.lt_left_of_right_lt' hy hx hb ha hab hfx,
end

lemma strict_concave_on.lt_right_of_left_lt' (hf : strict_concave_on 𝕜 s f) {x y : E} {a b : 𝕜}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  (hfx : f (a • x + b • y) < f x) :
  f y < f (a • x + b • y) :=
hf.dual.lt_right_of_left_lt' hx hy ha hb hab hfx

lemma strict_convex_on.lt_left_of_right_lt (hf : strict_convex_on 𝕜 s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment 𝕜 x y) (hyz : f y < f z) :
  f z < f x :=
begin
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz,
  exact hf.lt_left_of_right_lt' hx hy ha hb hab hyz,
end

lemma strict_concave_on.left_lt_of_lt_right (hf : strict_concave_on 𝕜 s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment 𝕜 x y) (hyz : f z < f y) :
  f x < f z :=
hf.dual.lt_left_of_right_lt hx hy hz hyz

lemma strict_convex_on.lt_right_of_left_lt (hf : strict_convex_on 𝕜 s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment 𝕜 x y) (hxz : f x < f z) :
  f z < f y :=
begin
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz,
  exact hf.lt_right_of_left_lt' hx hy ha hb hab hxz,
end

lemma strict_concave_on.lt_right_of_left_lt (hf : strict_concave_on 𝕜 s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment 𝕜 x y) (hxz : f z < f x) :
  f y < f z :=
hf.dual.lt_right_of_left_lt hx hy hz hxz

end module
end linear_ordered_cancel_add_comm_monoid

section ordered_add_comm_group
variables [ordered_add_comm_group β] [has_scalar 𝕜 E] [module 𝕜 β] {s : set E} {f g : E → β}

/-- A function `-f` is convex iff `f` is concave. -/
@[simp] lemma neg_convex_on_iff : convex_on 𝕜 s (-f) ↔ concave_on 𝕜 s f :=
begin
  split,
  { rintro ⟨hconv, h⟩,
    refine ⟨hconv, λ x y hx hy a b ha hb hab, _⟩,
    simp [neg_apply, neg_le, add_comm] at h,
    exact h hx hy ha hb hab },
  { rintro ⟨hconv, h⟩,
    refine ⟨hconv, λ x y hx hy a b ha hb hab, _⟩,
    rw ←neg_le_neg_iff,
    simp_rw [neg_add, pi.neg_apply, smul_neg, neg_neg],
    exact h hx hy ha hb hab }
end

/-- A function `-f` is concave iff `f` is convex. -/
@[simp] lemma neg_concave_on_iff : concave_on 𝕜 s (-f) ↔ convex_on 𝕜 s f:=
by rw [← neg_convex_on_iff, neg_neg f]

/-- A function `-f` is strictly convex iff `f` is strictly concave. -/
@[simp] lemma neg_strict_convex_on_iff : strict_convex_on 𝕜 s (-f) ↔ strict_concave_on 𝕜 s f :=
begin
  split,
  { rintro ⟨hconv, h⟩,
    refine ⟨hconv, λ x y hx hy hxy a b ha hb hab, _⟩,
    simp [neg_apply, neg_lt, add_comm] at h,
    exact h hx hy hxy ha hb hab },
  { rintro ⟨hconv, h⟩,
    refine ⟨hconv, λ x y hx hy hxy a b ha hb hab, _⟩,
    rw ←neg_lt_neg_iff,
    simp_rw [neg_add, pi.neg_apply, smul_neg, neg_neg],
    exact h hx hy hxy ha hb hab }
end

/-- A function `-f` is strictly concave iff `f` is strictly convex. -/
@[simp] lemma neg_strict_concave_on_iff : strict_concave_on 𝕜 s (-f) ↔ strict_convex_on 𝕜 s f :=
by rw [← neg_strict_convex_on_iff, neg_neg f]

alias neg_convex_on_iff ↔ _ concave_on.neg
alias neg_concave_on_iff ↔ _ convex_on.neg
alias neg_strict_convex_on_iff ↔ _ strict_concave_on.neg
alias neg_strict_concave_on_iff ↔ _ strict_convex_on.neg

lemma convex_on.sub (hf : convex_on 𝕜 s f) (hg : concave_on 𝕜 s g) : convex_on 𝕜 s (f - g) :=
(sub_eq_add_neg f g).symm ▸ hf.add hg.neg

lemma concave_on.sub (hf : concave_on 𝕜 s f) (hg : convex_on 𝕜 s g) : concave_on 𝕜 s (f - g) :=
(sub_eq_add_neg f g).symm ▸ hf.add hg.neg

lemma strict_convex_on.sub (hf : strict_convex_on 𝕜 s f) (hg : strict_concave_on 𝕜 s g) :
  strict_convex_on 𝕜 s (f - g) :=
(sub_eq_add_neg f g).symm ▸ hf.add hg.neg

lemma strict_concave_on.sub (hf : strict_concave_on 𝕜 s f) (hg : strict_convex_on 𝕜 s g) :
  strict_concave_on 𝕜 s (f - g) :=
(sub_eq_add_neg f g).symm ▸ hf.add hg.neg

lemma convex_on.sub_strict_concave_on (hf : convex_on 𝕜 s f) (hg : strict_concave_on 𝕜 s g) :
  strict_convex_on 𝕜 s (f - g) :=
(sub_eq_add_neg f g).symm ▸ hf.add_strict_convex_on hg.neg

lemma concave_on.sub_strict_convex_on (hf : concave_on 𝕜 s f) (hg : strict_convex_on 𝕜 s g) :
  strict_concave_on 𝕜 s (f - g) :=
(sub_eq_add_neg f g).symm ▸ hf.add_strict_concave_on hg.neg

lemma strict_convex_on.sub_concave_on (hf : strict_convex_on 𝕜 s f) (hg : concave_on 𝕜 s g) :
  strict_convex_on 𝕜 s (f - g) :=
(sub_eq_add_neg f g).symm ▸ hf.add_convex_on hg.neg

lemma strict_concave_on.sub_convex_on (hf : strict_concave_on 𝕜 s f) (hg : convex_on 𝕜 s g) :
  strict_concave_on 𝕜 s (f - g) :=
(sub_eq_add_neg f g).symm ▸ hf.add_concave_on hg.neg

end ordered_add_comm_group
end add_comm_monoid

section add_cancel_comm_monoid
variables [add_cancel_comm_monoid E] [ordered_add_comm_monoid β] [module 𝕜 E] [has_scalar 𝕜 β]
  {s : set E} {f : E → β}

/-- Right translation preserves strict convexity. -/
lemma strict_convex_on.translate_right (hf : strict_convex_on 𝕜 s f) (c : E) :
  strict_convex_on 𝕜 ((λ z, c + z) ⁻¹' s) (f ∘ (λ z, c + z)) :=
⟨hf.1.translate_preimage_right _, λ x y hx hy hxy a b ha hb hab,
  calc
    f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y))
        : by rw [smul_add, smul_add, add_add_add_comm, convex.combo_self hab]
    ... < a • f (c + x) + b • f (c + y) : hf.2 hx hy ((add_right_injective c).ne hxy) ha hb hab⟩

/-- Right translation preserves strict concavity. -/
lemma strict_concave_on.translate_right (hf : strict_concave_on 𝕜 s f) (c : E) :
  strict_concave_on 𝕜 ((λ z, c + z) ⁻¹' s) (f ∘ (λ z, c + z)) :=
hf.dual.translate_right _

/-- Left translation preserves strict convexity. -/
lemma strict_convex_on.translate_left (hf : strict_convex_on 𝕜 s f) (c : E) :
  strict_convex_on 𝕜 ((λ z, c + z) ⁻¹' s) (f ∘ (λ z, z + c)) :=
by simpa only [add_comm] using hf.translate_right _

/-- Left translation preserves strict concavity. -/
lemma strict_concave_on.translate_left (hf : strict_concave_on 𝕜 s f) (c : E) :
  strict_concave_on 𝕜 ((λ z, c + z) ⁻¹' s) (f ∘ (λ z, z + c)) :=
by simpa only [add_comm] using hf.translate_right _

end add_cancel_comm_monoid
end ordered_semiring

section ordered_comm_semiring
variables [ordered_comm_semiring 𝕜] [add_comm_monoid E]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β]

section module
variables [has_scalar 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f : E → β}

lemma convex_on.smul {c : 𝕜} (hc : 0 ≤ c) (hf : convex_on 𝕜 s f) : convex_on 𝕜 s (λ x, c • f x) :=
⟨hf.1, λ x y hx hy a b ha hb hab,
  calc
    c • f (a • x + b • y) ≤ c • (a • f x + b • f y)
      : smul_le_smul_of_nonneg (hf.2 hx hy ha hb hab) hc
    ... = a • (c • f x) + b • (c • f y)
      : by rw [smul_add, smul_comm c, smul_comm c]; apply_instance⟩

lemma concave_on.smul {c : 𝕜} (hc : 0 ≤ c) (hf : concave_on 𝕜 s f) :
  concave_on 𝕜 s (λ x, c • f x) :=
hf.dual.smul hc

end module
end ordered_add_comm_monoid
end ordered_comm_semiring

section ordered_ring
variables [linear_ordered_field 𝕜] [add_comm_group E] [add_comm_group F]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β]

section module
variables [module 𝕜 E] [module 𝕜 F] [has_scalar 𝕜 β]

/-- If a function is convex on `s`, it remains convex when precomposed by an affine map. -/
lemma convex_on.comp_affine_map {f : F → β} (g : E →ᵃ[𝕜] F) {s : set F} (hf : convex_on 𝕜 s f) :
  convex_on 𝕜 (g ⁻¹' s) (f ∘ g) :=
⟨hf.1.affine_preimage _, λ x y hx hy a b ha hb hab,
  calc
    (f ∘ g) (a • x + b • y) = f (g (a • x + b • y))         : rfl
                       ...  = f (a • (g x) + b • (g y))     : by rw [convex.combo_affine_apply hab]
                       ...  ≤ a • f (g x) + b • f (g y)     : hf.2 hx hy ha hb hab⟩

/-- If a function is concave on `s`, it remains concave when precomposed by an affine map. -/
lemma concave_on.comp_affine_map {f : F → β} (g : E →ᵃ[𝕜] F) {s : set F} (hf : concave_on 𝕜 s f) :
  concave_on 𝕜 (g ⁻¹' s) (f ∘ g) :=
hf.dual.comp_affine_map g

end module
end ordered_add_comm_monoid
end ordered_ring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_monoid E]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β]

section has_scalar
variables [has_scalar 𝕜 E] [has_scalar 𝕜 β] {s : set E}

lemma convex_on_iff_div {f : E → β} :
  convex_on 𝕜 s f ↔ convex 𝕜 s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b
  → f ((a/(a+b)) • x + (b/(a+b)) • y) ≤ (a/(a+b)) • f x + (b/(a+b)) • f y :=
and_congr iff.rfl
⟨begin
  intros h x y hx hy a b ha hb hab,
  apply h hx hy (div_nonneg ha hab.le) (div_nonneg hb hab.le),
  rw [←add_div, div_self hab.ne'],
end,
begin
  intros h x y hx hy a b ha hb hab,
  simpa [hab, zero_lt_one] using h hx hy ha hb,
end⟩

lemma concave_on_iff_div {f : E → β} :
  concave_on 𝕜 s f ↔ convex 𝕜 s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b
  → 0 < a + b → (a/(a+b)) • f x + (b/(a+b)) • f y ≤ f ((a/(a+b)) • x + (b/(a+b)) • y) :=
@convex_on_iff_div _ _ βᵒᵈ _ _ _ _ _ _ _

lemma strict_convex_on_iff_div {f : E → β} :
  strict_convex_on 𝕜 s f ↔ convex 𝕜 s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a
    → 0 < b → f ((a/(a+b)) • x + (b/(a+b)) • y) < (a/(a+b)) • f x + (b/(a+b)) • f y :=
and_congr iff.rfl
⟨begin
  intros h x y hx hy hxy a b ha hb,
  have hab := add_pos ha hb,
  apply h hx hy hxy (div_pos ha hab) (div_pos hb hab),
  rw [←add_div, div_self hab.ne'],
end,
begin
  intros h x y hx hy hxy a b ha hb hab,
  simpa [hab, zero_lt_one] using h hx hy hxy ha hb,
end⟩

lemma strict_concave_on_iff_div {f : E → β} :
  strict_concave_on 𝕜 s f ↔ convex 𝕜 s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a
    → 0 < b → (a/(a+b)) • f x + (b/(a+b)) • f y < f ((a/(a+b)) • x + (b/(a+b)) • y) :=
@strict_convex_on_iff_div _ _ βᵒᵈ _ _ _ _ _ _ _

end has_scalar
end ordered_add_comm_monoid
end linear_ordered_field
