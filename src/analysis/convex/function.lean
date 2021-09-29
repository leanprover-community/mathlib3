/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, François Dupuis
-/
import analysis.convex.combination
import data.real.basic
import algebra.module.ordered

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
* `convex_on.map_center_mass_le` `convex_on.map_sum_le`: Convex Jensen's inequality.
-/

open finset linear_map set
open_locale big_operators classical convex pointwise

variables {𝕜 E F β ι : Type*}

section ordered_semiring
variables [ordered_semiring 𝕜] [add_comm_monoid E] [add_comm_monoid F]

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

lemma convex_on_id {s : set 𝕜} (hs : convex 𝕜 s) : convex_on 𝕜 s id := ⟨hs, by { intros, refl }⟩

lemma concave_on_id {s : set 𝕜} (hs : convex 𝕜 s) : concave_on 𝕜 s id := ⟨hs, by { intros, refl }⟩

lemma convex_on.subset {f : E → β} {t : set E} (hf : convex_on 𝕜 t f) (hst : s ⊆ t)
  (hs : convex 𝕜 s) : convex_on 𝕜 s f :=
⟨hs, λ x y hx hy, hf.2 (hst hx) (hst hy)⟩

lemma concave_on.subset {f : E → β} {t : set E} (hf : concave_on 𝕜 t f) (hst : s ⊆ t)
  (hs : convex 𝕜 s) : concave_on 𝕜 s f :=
⟨hs, λ x y hx hy, hf.2 (hst hx) (hst hy)⟩

end has_scalar

section distrib_mul_action
variables [has_scalar 𝕜 E] [distrib_mul_action 𝕜 β] {s : set E}

lemma convex_on.add {f g : E → β} (hf : convex_on 𝕜 s f) (hg : convex_on 𝕜 s g) :
  convex_on 𝕜 s (λ x, f x + g x) :=
⟨hf.1, λ x y hx hy a b ha hb hab,
  calc
    f (a • x + b • y) + g (a • x + b • y) ≤ (a • f x + b • f y) + (a • g x + b • g y)
      : add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    ... = a • f x + a • g x + b • f y + b • g y : by abel
    ... = a • (f x + g x) + b • (f y + g y) : by simp only [smul_add, add_assoc]⟩

lemma concave_on.add {f g : E → β} (hf : concave_on 𝕜 s f) (hg : concave_on 𝕜 s g) :
  concave_on 𝕜 s (λ x, f x + g x) :=
@convex_on.add _ _ (order_dual β) _ _ _ _ _ _ f g hf hg

end distrib_mul_action

section module
variables [has_scalar 𝕜 E] [module 𝕜 β] {s : set E}

lemma convex_on_const (c : β) (hs : convex 𝕜 s) : convex_on 𝕜 s (λ x:E, c) :=
⟨hs, λ x y _ _ a b _ _ hab, (convex.combo_self hab c).ge⟩

lemma concave_on_const (c : β) (hs : convex 𝕜 s) : concave_on 𝕜 s (λ x:E, c) :=
@convex_on_const _ _ (order_dual β) _ _ _ _ _ _ c hs

end module

section ordered_smul
variables [has_scalar 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f : E → β}

lemma convex_on.convex_le (hf : convex_on 𝕜 s f) (r : β) :
  convex 𝕜 {x ∈ s | f x ≤ r} :=
λ x y hx hy a b ha hb hab, ⟨hf.1 hx.1 hy.1 ha hb hab,
  calc
    f (a • x + b • y) ≤ a • (f x) + b • (f y) : hf.2 hx.1 hy.1 ha hb hab
                  ... ≤ a • r + b • r         : add_le_add (smul_le_smul_of_nonneg hx.2 ha)
                                                  (smul_le_smul_of_nonneg hy.2 hb)
                  ... = r                     : convex.combo_self hab r⟩

lemma concave_on.concave_ge (hf : concave_on 𝕜 s f) (r : β) :
  convex 𝕜 {x ∈ s | r ≤ f x} :=
@convex_on.convex_le 𝕜 E (order_dual β) _ _ _ _ _ _ _ f hf r

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
@convex_on.convex_epigraph 𝕜 E (order_dual β) _ _ _ _ _ _ _ f hf

lemma convex_on_iff_convex_epigraph :
  convex_on 𝕜 s f ↔ convex 𝕜 {p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
⟨convex_on.convex_epigraph, λ h,
  ⟨λ x y hx hy a b ha hb hab, (@h (x, f x) (y, f y) ⟨hx, le_rfl⟩ ⟨hy, le_rfl⟩ a b ha hb hab).1,
  λ x y hx hy a b ha hb hab, (@h (x, f x) (y, f y) ⟨hx, le_rfl⟩ ⟨hy, le_rfl⟩ a b ha hb hab).2⟩⟩

lemma concave_on_iff_convex_hypograph :
  concave_on 𝕜 s f ↔ convex 𝕜 {p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
@convex_on_iff_convex_epigraph 𝕜 E (order_dual β) _ _ _ _ _ _ _ f

end ordered_smul

section module
variables [module 𝕜 E] [module 𝕜 β]

/-- A linear map is convex. -/
lemma linear_map.convex_on (f : E →ₗ[𝕜] β) {s : set E} (hs : convex 𝕜 s) : convex_on 𝕜 s f :=
⟨hs, λ _ _ _ _ _ _ _ _ _, by rw [f.map_add, f.map_smul, f.map_smul]⟩

/-- A linear map is concave. -/
lemma linear_map.concave_on (f : E →ₗ[𝕜] β) {s : set E} (hs : convex 𝕜 s) : concave_on 𝕜 s f :=
⟨hs, λ _ _ _ _ _ _ _ _ _, by rw [f.map_add, f.map_smul, f.map_smul]⟩

/-- If a function is convex on `s`, it remains convex after a translation. -/
lemma convex_on.translate_right {f : E → β} {s : set E} {c : E} (hf : convex_on 𝕜 s f) :
  convex_on 𝕜 ((λ z, c + z) ⁻¹' s) (f ∘ (λ z, c + z)) :=
⟨hf.1.translate_preimage_right _, λ x y hx hy a b ha hb hab,
  calc
    f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y))
        : by rw [smul_add, smul_add, add_add_add_comm, convex.combo_self hab]
    ... ≤ a • f (c + x) + b • f (c + y) : hf.2 hx hy ha hb hab⟩

/-- If a function is concave on `s`, it remains concave after a translation. -/
lemma concave_on.translate_right {f : E → β} {s : set E} {a : E} (hf : concave_on 𝕜 s f) :
  concave_on 𝕜 ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, a + z)) :=
@convex_on.translate_right 𝕜 E (order_dual β) _ _ _ _ _ _ _ _ hf

/-- If a function is convex on `s`, it remains convex after a translation. -/
lemma convex_on.translate_left {f : E → β} {s : set E} {a : E} (hf : convex_on 𝕜 s f) :
  convex_on 𝕜 ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, z + a)) :=
by simpa only [add_comm] using hf.translate_right

/-- If a function is concave on `s`, it remains concave after a translation. -/
lemma concave_on.translate_left {f : E → β} {s : set E} {a : E} (hf : concave_on 𝕜 s f) :
  concave_on 𝕜 ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, z + a)) :=
by simpa only [add_comm] using hf.translate_right

variables [linear_order E] {s : set E} {f : E → β}

/-- For a function on a convex set in a linear ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is convex, it suffices to
verify the inequality `f (a • x + b • y) ≤ a • f x + b • f y` only for `x < y` and positive `a`,
`b`. The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order.
-/
lemma linear_order.convex_on_of_lt (hs : convex 𝕜 s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y) : convex_on 𝕜 s f :=
begin
  refine ⟨hs, λ x y hx hy a b ha hb hab, _⟩,
  wlog hxy : x ≤ y using [x y a b, y x b a],
  { exact le_total _ _ },
  obtain rfl | hxy := hxy.eq_or_lt,
  { rw [convex.combo_self hab, convex.combo_self hab] },
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [zero_add] at hab, subst b, simp_rw [zero_smul, zero_add, one_smul] },
  obtain rfl | hb' := hb.eq_or_lt,
  { rw [add_zero] at hab, subst a, simp_rw [zero_smul, add_zero, one_smul] },
  exact hf hx hy hxy ha' hb' hab,
end

/-- For a function on a convex set in a linear ordered space, in order to prove that it is concave
it suffices to verify the inequality `a • f x + b • f y ≤ f (a • x + b • y)` only for `x < y`
and positive `a`, `b`. The main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with
lexicographic order. -/
lemma linear_order.concave_on_of_lt (hs : convex 𝕜 s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
     a • f x + b • f y ≤ f (a • x + b • y)) : concave_on 𝕜 s f :=
@linear_order.convex_on_of_lt _ _ (order_dual β) _ _ _ _ _ _ s f hs hf

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
@convex_on.comp_linear_map 𝕜 E F (order_dual β) _ _ _ _ _ _ _ f s hf g

end module
end ordered_add_comm_monoid

section ordered_cancel_add_comm_monoid
variables [ordered_cancel_add_comm_monoid β]

section module
variables [module 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f g : E → β}

lemma convex_on.convex_lt (hf : convex_on 𝕜 s f) (r : β) : convex 𝕜 {x ∈ s | f x < r} :=
begin
  refine λ x y hx hy a b ha hb hab, ⟨hf.1 hx.1 hy.1 ha hb hab, _⟩,
  obtain rfl | ha' := ha.eq_or_lt,
  { rw zero_add at hab,
    rw [hab, zero_smul, one_smul, zero_add],
    exact hy.2 },
  { calc
      f (a • x + b • y)
          ≤ a • f x + b • f y : hf.2 hx.1 hy.1 ha hb hab
      ... < a • r + b • r     : add_lt_add_of_lt_of_le (smul_lt_smul_of_pos hx.2 ha')
                                  (smul_le_smul_of_nonneg hy.2.le hb)
      ... = r                 : convex.combo_self hab _ }
end

lemma concave_on.convex_lt (hf : concave_on 𝕜 s f) (r : β) : convex 𝕜 {x ∈ s | r < f x} :=
@convex_on.convex_lt 𝕜 E (order_dual β) _ _ _ _ _ _ _ f hf r

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
@convex_on.sup 𝕜 E (order_dual β) _ _ _ _ _ _ _ f g hf hg

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment' (hf : convex_on 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
  {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  f (a • x + b • y) ≤ max (f x) (f y) :=
calc
  f (a • x + b • y) ≤ a • f x + b • f y : hf.2 hx hy ha hb hab
  ... ≤ a • max (f x) (f y) + b • max (f x) (f y) :
    add_le_add (smul_le_smul_of_nonneg (le_max_left _ _) ha)
      (smul_le_smul_of_nonneg (le_max_right _ _) hb)
  ... = max (f x) (f y) : by rw [←add_smul, hab, one_smul]

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.le_on_segment' (hf : concave_on 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
 {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  min (f x) (f y) ≤ f (a • x + b • y) :=
@convex_on.le_on_segment' 𝕜 E (order_dual β) _ _ _ _ _ _ _ f hf x y hx hy a b ha hb hab

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment (hf : convex_on 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
  (hz : z ∈ [x -[𝕜] y]) :
  f z ≤ max (f x) (f y) :=
let ⟨a, b, ha, hb, hab, hz⟩ := hz in hz ▸ hf.le_on_segment' hx hy ha hb hab

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.le_on_segment (hf : concave_on 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
  (hz : z ∈ [x -[𝕜] y]) :
  min (f x) (f y) ≤ f z :=
@convex_on.le_on_segment 𝕜 E (order_dual β) _ _ _ _ _ _ _ f hf x y z hx hy hz

end linear_ordered_add_comm_monoid

section linear_ordered_cancel_add_comm_monoid
variables [linear_ordered_cancel_add_comm_monoid β]

section ordered_smul
variables [has_scalar 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f g : E → β}

lemma convex_on.le_left_of_right_le' (hf : convex_on 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
 {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) (hxy : f y ≤ f (a • x + b • y)) :
  f (a • x + b • y) ≤ f x :=
le_of_not_lt $ λ h, lt_irrefl (f (a • x + b • y)) $
  calc
    f (a • x + b • y)
        ≤ a • f x + b • f y : hf.2 hx hy ha.le hb hab
    ... < a • f (a • x + b • y) + b • f (a • x + b • y)
        : add_lt_add_of_lt_of_le (smul_lt_smul_of_pos h ha) (smul_le_smul_of_nonneg hxy hb)
    ... = f (a • x + b • y) : by rw [←add_smul, hab, one_smul]

lemma concave_on.left_le_of_le_right' (hf : concave_on 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
  {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) (hxy : f (a • x + b • y) ≤ f y) :
  f x ≤ f (a • x + b • y) :=
@convex_on.le_left_of_right_le' 𝕜 E (order_dual β) _ _ _ _ _ _ _ f hf x y hx hy a b ha hb hab hxy

lemma convex_on.le_right_of_left_le' (hf : convex_on 𝕜 s f) {x y : E} {a b : 𝕜}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1)
  (hxy : f x ≤ f (a • x + b • y)) :
  f (a • x + b • y) ≤ f y :=
begin
  rw add_comm at ⊢ hab hxy,
  exact hf.le_left_of_right_le' hy hx hb ha hab hxy,
end

lemma concave_on.le_right_of_left_le' (hf : concave_on 𝕜 s f) {x y : E} {a b : 𝕜}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1)
  (hxy : f (a • x + b • y) ≤ f x) :
  f y ≤ f (a • x + b • y) :=
@convex_on.le_right_of_left_le' 𝕜 E (order_dual β) _ _ _ _ _ _ _ f hf x y a b hx hy ha hb hab hxy

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
@convex_on.le_left_of_right_le 𝕜 E (order_dual β) _ _ _ _ _ _ _ f hf x y z hx hy hz hyz

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
@convex_on.le_right_of_left_le 𝕜 E (order_dual β) _ _ _ _ _ _ _ f hf x y z hx hy hz hxz

end ordered_smul
end linear_ordered_cancel_add_comm_monoid

section ordered_add_comm_group
variables [ordered_add_comm_group β] [has_scalar 𝕜 E] [module 𝕜 β] {s : set E} {f : E → β}

/-- A function `-f` is convex iff `f` is concave. -/
@[simp] lemma neg_convex_on_iff :
  convex_on 𝕜 s (-f) ↔ concave_on 𝕜 s f :=
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

alias neg_convex_on_iff ↔ _ concave_on.neg
alias neg_concave_on_iff ↔ _ convex_on.neg

end ordered_add_comm_group
end ordered_semiring

section ordered_comm_semiring
variables [ordered_comm_semiring 𝕜] [add_comm_monoid E]

section ordered_add_comm_monoid
variables [ordered_add_comm_monoid β]

section module
variables [has_scalar 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f : E → β}

lemma convex_on.smul {c : 𝕜} (hc : 0 ≤ c)
  (hf : convex_on 𝕜 s f) : convex_on 𝕜 s (λ x, c • f x) :=
⟨hf.1, λ x y hx hy a b ha hb hab,
  calc
    c • f (a • x + b • y) ≤ c • (a • f x + b • f y)
      : smul_le_smul_of_nonneg (hf.2 hx hy ha hb hab) hc
    ... = a • (c • f x) + b • (c • f y)
      : by rw [smul_add, smul_comm c, smul_comm c]; apply_instance⟩

lemma concave_on.smul {c : 𝕜} (hc : 0 ≤ c)
  (hf : concave_on 𝕜 s f) : concave_on 𝕜 s (λ x, c • f x) :=
@convex_on.smul _ _ (order_dual β) _ _ _ _ _ _ _ f c hc hf

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
@convex_on.comp_affine_map _ _ _ (order_dual β) _ _ _ _ _ _ _ f g s hf

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
@convex_on_iff_div _ _ (order_dual β) _ _ _ _ _ _ _

/-- For a function `f` defined on a convex subset `D` of `𝕜`, if for any three points `x < y < z`
the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is convex on `D`. This way of proving convexity
of a function is used in the proof of convexity of a function with a monotone derivative. -/
lemma convex_on_of_slope_mono_adjacent {s : set 𝕜} (hs : convex 𝕜 s) {f : 𝕜 → 𝕜}
  (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :
  convex_on 𝕜 s f :=
linear_order.convex_on_of_lt hs
begin
  assume x z hx hz hxz a b ha hb hab,
  let y := a * x + b * z,
  have hxy : x < y,
  { rw [← one_mul x, ← hab, add_mul],
    exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _ },
  have hyz : y < z,
  { rw [← one_mul z, ← hab, add_mul],
    exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _ },
  have : (f y - f x) * (z - y) ≤ (f z - f y) * (y - x),
    from (div_le_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz),
  have hxz : 0 < z - x, from sub_pos.2 (hxy.trans hyz),
  have ha : (z - y) / (z - x) = a,
  { rw [eq_comm, ← sub_eq_iff_eq_add'] at hab,
    simp_rw [div_eq_iff hxz.ne', y, ←hab], ring },
  have hb : (y - x) / (z - x) = b,
  { rw [eq_comm, ← sub_eq_iff_eq_add] at hab,
    simp_rw [div_eq_iff hxz.ne', y, ←hab], ring },
  rwa [sub_mul, sub_mul, sub_le_iff_le_add', ← add_sub_assoc, le_sub_iff_add_le, ← mul_add,
    sub_add_sub_cancel, ← le_div_iff hxz, add_div, mul_div_assoc, mul_div_assoc, mul_comm (f x),
    mul_comm (f z), ha, hb] at this,
end

/-- For a function `f` defined on a subset `D` of `𝕜`, if `f` is convex on `D`, then for any three
points `x < y < z`, the slope of the secant line of `f` on `[x, y]` is less than or equal to the
slope of the secant line of `f` on `[x, z]`. -/
lemma convex_on.slope_mono_adjacent {s : set 𝕜} {f : 𝕜 → 𝕜} (hf : convex_on 𝕜 s f)
  {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
begin
  have h₁ : 0 < y - x := by linarith,
  have h₂ : 0 < z - y := by linarith,
  have h₃ : 0 < z - x := by linarith,
  suffices : f y / (y - x) + f y / (z - y) ≤ f x / (y - x) + f z / (z - y),
  { ring_nf at this ⊢, linarith },
  set a := (z - y) / (z - x),
  set b := (y - x) / (z - x),
  have heqz : a • x + b • z = y, by { field_simp, rw div_eq_iff; [ring, linarith] },
  have key, from
    hf.2 hx hz
      (show 0 ≤ a, by apply div_nonneg; linarith)
      (show 0 ≤ b, by apply div_nonneg; linarith)
      (show a + b = 1, by { field_simp, rw div_eq_iff; [ring, linarith] }),
  rw heqz at key,
  replace key := mul_le_mul_of_nonneg_left key h₃.le,
  field_simp [h₁.ne', h₂.ne', h₃.ne', mul_comm (z - x) _] at key ⊢,
  rw div_le_div_right,
  { linarith },
  { nlinarith }
end

/-- For a function `f` defined on a convex subset `D` of `𝕜`, `f` is convex on `D` iff, for any
three points `x < y < z` the slope of the secant line of `f` on `[x, y]` is less than or equal to
the slope,of the secant line of `f` on `[x, z]`. -/
lemma convex_on_iff_slope_mono_adjacent {s : set 𝕜} (hs : convex 𝕜 s) {f : 𝕜 → 𝕜} :
  convex_on 𝕜 s f ↔
  (∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :=
⟨convex_on.slope_mono_adjacent, convex_on_of_slope_mono_adjacent hs⟩

/-- For a function `f` defined on a convex subset `D` of `𝕜`, if for any three points `x < y < z`
the slope of the secant line of `f` on `[x, y]` is greater than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is concave on `D`. -/
lemma concave_on_of_slope_mono_adjacent {s : set 𝕜} (hs : convex 𝕜 s) {f : 𝕜 → 𝕜}
  (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) : concave_on 𝕜 s f :=
begin
  rw ←neg_convex_on_iff,
  refine convex_on_of_slope_mono_adjacent hs (λ x y z hx hz hxy hyz, _),
  rw ←neg_le_neg_iff,
  simp_rw [←neg_div, neg_sub, pi.neg_apply, neg_sub_neg],
  exact hf hx hz hxy hyz,
end

/-- For a function `f` defined on a subset `D` of `𝕜`, if `f` is concave on `D`, then for any three
points `x < y < z`, the slope of the secant line of `f` on `[x, y]` is greater than or equal to the
slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on.slope_mono_adjacent {s : set 𝕜} {f : 𝕜 → 𝕜} (hf : concave_on 𝕜 s f)
  {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
begin
  rw [←neg_le_neg_iff, ←neg_sub_neg (f x), ←neg_sub_neg (f y)],
  simp_rw [←pi.neg_apply, ←neg_div, neg_sub],
  exact convex_on.slope_mono_adjacent hf.neg hx hz hxy hyz,
end

/-- For a function `f` defined on a convex subset `D` of `𝕜`, `f` is concave on `D` iff for any
three points `x < y < z` the slope of the secant line of `f` on `[x, y]` is greater than or equal to
the slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on_iff_slope_mono_adjacent {s : set 𝕜} (hs : convex 𝕜 s) {f : 𝕜 → 𝕜} :
  concave_on 𝕜 s f ↔
  (∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) :=
⟨concave_on.slope_mono_adjacent, concave_on_of_slope_mono_adjacent hs⟩

end has_scalar
end ordered_add_comm_monoid
end linear_ordered_field







/-! ### Jensen's inequality -/

section jensen
variables [linear_ordered_field 𝕜] [add_comm_group E] [ordered_add_comm_group β] [module 𝕜 E]
  [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f : E → β} {t : finset ι} {w : ι → 𝕜} {p : ι → E}

/-- Convex **Jensen's inequality**, `finset.center_mass` version. -/
lemma convex_on.map_center_mass_le (hf : convex_on 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
  (h₁ : 0 < ∑ i in t, w i) (hmem : ∀ i ∈ t, p i ∈ s) :
  f (t.center_mass w p) ≤ t.center_mass w (f ∘ p) :=
begin
  have hmem' : ∀ i ∈ t, (p i, (f ∘ p) i) ∈ {p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2},
    from λ i hi, ⟨hmem i hi, le_rfl⟩,
  convert (hf.convex_epigraph.center_mass_mem h₀ h₁ hmem').2;
    simp only [center_mass, function.comp, prod.smul_fst, prod.fst_sum,
      prod.smul_snd, prod.snd_sum],
end

/-- Concave **Jensen's inequality**, `finset.center_mass` version. -/
lemma concave_on.le_map_center_mass (hf : concave_on 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
  (h₁ : 0 < ∑ i in t, w i) (hmem : ∀ i ∈ t, p i ∈ s) :
  t.center_mass w (f ∘ p) ≤ f (t.center_mass w p) :=
@convex_on.map_center_mass_le 𝕜 E (order_dual β) _ _ _ _ _ _ _ _ _ _ _ _ hf h₀ h₁ hmem

/-- Convex **Jensen's inequality**, `finset.sum` version. -/
lemma convex_on.map_sum_le (hf : convex_on 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hmem : ∀ i ∈ t, p i ∈ s) :
  f (∑ i in t, w i • p i) ≤ ∑ i in t, w i • f (p i) :=
by simpa only [center_mass, h₁, inv_one, one_smul]
  using hf.map_center_mass_le h₀ (h₁.symm ▸ zero_lt_one) hmem

/-- Concave **Jensen's inequality**, `finset.sum` version. -/
lemma concave_on.le_map_sum (hf : concave_on 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hmem : ∀ i ∈ t, p i ∈ s) :
  ∑ i in t, w i • f (p i) ≤ f (∑ i in t, w i • p i) :=
@convex_on.map_sum_le 𝕜 E (order_dual β) _ _ _ _ _ _ _ _ _ _ _ _ hf h₀ h₁ hmem

end jensen

/-! ### Maximum principle -/

section maximum_principle
variables [linear_ordered_field 𝕜] [add_comm_group E] [linear_ordered_add_comm_group β]
  [module 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f : E → β} {t : finset ι} {w : ι → 𝕜}
  {p : ι → E}

/-- If a function `f` is convex on `s`, then the value it takes at some center of mass of points of
`s` is less than the value it takes on one of those points. -/
lemma convex_on.exists_ge_of_center_mass (h : convex_on 𝕜 s f)
  (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : 0 < ∑ i in t, w i) (hp : ∀ i ∈ t, p i ∈ s) :
  ∃ i ∈ t, f (t.center_mass w p) ≤ f (p i) :=
begin
  set y := t.center_mass w p,
  suffices h : ∃ i ∈ t.filter (λ i, w i ≠ 0), w i • f y ≤ w i • (f ∘ p) i,
  { obtain ⟨i, hi, hfi⟩ := h,
    rw mem_filter at hi,
    exact ⟨i, hi.1, (smul_le_smul_iff_of_pos $ (hw₀ i hi.1).lt_of_ne hi.2.symm).1 hfi⟩ },
  have hw' : (0 : 𝕜) < ∑ i in filter (λ i, w i ≠ 0) t, w i := by rwa sum_filter_ne_zero,
  refine exists_le_of_sum_le (nonempty_of_sum_ne_zero hw'.ne') _,
  rw [←sum_smul, ←smul_le_smul_iff_of_pos (inv_pos.2 hw'), inv_smul_smul' hw'.ne',
    ←finset.center_mass, finset.center_mass_filter_ne_zero],
  exact h.map_center_mass_le hw₀ hw₁ hp,
  apply_instance,
end

/-- If a function `f` is concave on `s`, then the value it takes at some center of mass of points of
`s` is greater than the value it takes on one of those points. -/
lemma concave_on.exists_le_of_center_mass (h : concave_on 𝕜 s f)
  (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : 0 < ∑ i in t, w i) (hp : ∀ i ∈ t, p i ∈ s) :
  ∃ i ∈ t, f (p i) ≤ f (t.center_mass w p) :=
@convex_on.exists_ge_of_center_mass 𝕜 E (order_dual β) _ _ _ _ _ _ _ _ _ _ _ _ h hw₀ hw₁ hp

/-- Maximum principle for convex functions. If a function `f` is convex on the convex hull of `s`,
then the eventual maximum of `f` on `convex_hull 𝕜 s` lies in `s`. -/
lemma convex_on.exists_ge_of_mem_convex_hull (hf : convex_on 𝕜 (convex_hull 𝕜 s) f) {x}
  (hx : x ∈ convex_hull 𝕜 s) : ∃ y ∈ s, f x ≤ f y :=
begin
  rw _root_.convex_hull_eq at hx,
  obtain ⟨α, t, w, p, hw₀, hw₁, hp, rfl⟩ := hx,
  rcases hf.exists_ge_of_center_mass hw₀ (hw₁.symm ▸ zero_lt_one)
    (λ i hi, subset_convex_hull 𝕜 s (hp i hi)) with ⟨i, hit, Hi⟩,
  exact ⟨p i, hp i hit, Hi⟩
end

/-- Minimum principle for concave functions. If a function `f` is concave on the convex hull of `s`,
then the eventual minimum of `f` on `convex_hull 𝕜 s` lies in `s`. -/
lemma concave_on.exists_le_of_mem_convex_hull (hf : concave_on 𝕜 (convex_hull 𝕜 s) f) {x}
  (hx : x ∈ convex_hull 𝕜 s) : ∃ y ∈ s, f y ≤ f x :=
@convex_on.exists_ge_of_mem_convex_hull 𝕜 E (order_dual β) _ _ _ _ _ _ _ _ hf _ hx

end maximum_principle
