/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import data.set.intervals.ord_connected
import data.set.intervals.image_preimage
import data.complex.module
import linear_algebra.affine_space.basic
import algebra.module.ordered

/-!
# Convex sets and functions on real vector spaces

In a real vector space, we define the following objects and properties.

* `segment x y` is the closed segment joining `x` and `y`.
* A set `s` is `convex` if for any two points `x y ∈ s` it includes `segment x y`;
* A function `f : E → β` is `convex_on` a set `s` if `s` is itself a convex set, and for any two
  points `x y ∈ s` the segment joining `(x, f x)` to `(y, f y)` is (non-strictly) above the graph
  of `f`; equivalently, `convex_on f s` means that the epigraph
  `{p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}` is a convex set;
* Center mass of a finite set of points with prescribed weights.
* Convex hull of a set `s` is the minimal convex set that includes `s`.
* Standard simplex `std_simplex ι [fintype ι]` is the intersection of the positive quadrant with
  the hyperplane `s.sum = 1` in the space `ι → ℝ`.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex, and prove Jensen's inequality.

Note: To define convexity for functions `f : E → β`, we need `β` to be an ordered vector space,
defined using the instance `ordered_semimodule ℝ β`.

## Notations

We use the following local notations:

* `I = Icc (0:ℝ) 1`;
* `[x, y] = segment x y`.

They are defined using `local notation`, so they are not available outside of this file.
-/

variables {E F PE PF ι ι' α : Type*}
  [add_comm_group E] [vector_space ℝ E] [add_torsor E PE]
  [add_comm_group F] [vector_space ℝ F] [add_torsor F PF]
  [linear_ordered_field α]
  {s : set PE}

include E

open set linear_map
open_locale classical big_operators

local notation `I` := (Icc 0 1 : set ℝ)

section sets

/-! ### Segment -/

open affine_map

/-- Segments in a vector space -/
def segment (x y : PE) : set PE := line_map x y '' I
local notation `[`x `, ` y `]` := segment x y

omit E

lemma segment_eq_interval (a b : ℝ) : segment a b = interval a b :=
by rw [segment, ← interval_of_le (@zero_le_one ℝ _), image_interval, line_map_apply_zero,
  line_map_apply_one]

lemma segment_eq_Icc {a b : ℝ} (h : a ≤ b) : [a, b] = Icc a b :=
by rw [segment_eq_interval, interval_of_le h]

include E

lemma segment_symm (x y : PE) : [x, y] = [y, x] :=
by rw [segment, segment, line_map_symm, coe_comp, image_comp, ← segment, segment_eq_interval,
  interval_of_ge (@zero_le_one ℝ _)]

lemma left_mem_segment (x y : PE) : x ∈ [x, y] :=
⟨0, ⟨le_refl 0, zero_le_one⟩, line_map_apply_zero _ _⟩

lemma right_mem_segment (x y : PE) : y ∈ [x, y] :=
segment_symm y x ▸ left_mem_segment y x

lemma segment_same (x : PE) : [x, x] = {x} :=
by { rw [segment, line_map_same, coe_const], exact (nonempty_Icc.2 zero_le_one).image_const _ }

lemma segment_eq_image (x y : PE) : segment x y = (λ θ, θ • (y -ᵥ x) +ᵥ x) '' I := rfl

include F

lemma affine_map.image_segment (f : affine_map ℝ PE PF) (x y : PE) :
  f '' [x, y] = [f x, f y] :=
by rw [segment, segment, ← image_comp, ← coe_comp, comp_line_map]

omit F

lemma segment_translate_image (a : E) (b c : PE) : (λx, a +ᵥ x) '' [b, c] = [a +ᵥ b, a +ᵥ c] :=
(const ℝ PE a +ᵥ affine_map.id ℝ PE).image_segment b c

lemma segment_translate_preimage (a : E) (b c : PE) :
  (λ x, a +ᵥ x) ⁻¹' [a +ᵥ b, a +ᵥ c] = [b, c] :=
segment_translate_image a b c ▸ preimage_image_eq _ (equiv.const_vadd PE a).injective

lemma mem_segment_translate (a : E) {x b c : PE} : a +ᵥ x ∈ [a +ᵥ b, a +ᵥ c] ↔ x ∈ [b, c] :=
by rw [← segment_translate_preimage a b c, mem_preimage]

/-! ### Convexity of sets -/
/-- Convexity of sets -/
def convex (s : set PE) := ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), maps_to (line_map x y) I s

lemma convex.segment_subset {s : set PE} (hs : convex s) {x y} (hx : x ∈ s) (hy : y ∈ s) :
  [x, y] ⊆ s :=
(hs hx hy).image_subset

lemma convex_iff_open_segment_subset :
  convex s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), maps_to (line_map x y) (Ioo (0:ℝ) 1) s :=
begin
  refine ⟨λ h x hx y hy, (h hx hy).mono Ioo_subset_Icc_self (subset.refl _), _⟩,
  intros h x hx y hy θ hθ,
  rcases mem_Ioo_or_eq_endpoints_of_mem_Icc hθ with rfl|rfl|hθ;
    [simpa only [line_map_apply_zero], simpa [line_map], exact h hx hy hθ]
end

lemma convex_iff_segment_subset : convex s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), [x, y] ⊆ s :=
by simp only [convex, maps_to', segment]

/-
/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
lemma convex_iff_pointwise_add_subset:
  convex s ↔ ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • s + b • s ⊆ s :=
iff.intro
  begin
    rintros hA a b ha hb hab w ⟨au, bv, ⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, rfl⟩,
    exact hA hu hv ha hb hab
  end
  (λ h x y hx hy a b ha hb hab,
    (h ha hb hab) (set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩))

/-- Alternative definition of set convexity, using division -/
lemma convex_iff_div:
  convex s ↔ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄,
    0 ≤ a → 0 ≤ b → 0 < a + b → (a/(a+b)) • x + (b/(a+b)) • y ∈ s :=
⟨begin
  assume h x y hx hy a b ha hb hab,
  apply h hx hy,
  have ha', from mul_le_mul_of_nonneg_left ha (le_of_lt (inv_pos.2 hab)),
  rwa [mul_zero, ←div_eq_inv_mul] at ha',
  have hb', from mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.2 hab)),
  rwa [mul_zero, ←div_eq_inv_mul] at hb',
  rw [←add_div],
  exact div_self (ne_of_lt hab).symm
end,
begin
  assume h x y hx hy a b ha hb hab,
  have h', from h hx hy ha hb,
  rw [hab, div_one, div_one] at h',
  exact h' zero_lt_one
end⟩
-/

/-! ### Examples of convex sets -/

lemma convex_empty : convex (∅ : set PE) :=  by finish

lemma convex_singleton (c : PE) : convex ({c} : set PE) :=
begin
  rintros x (rfl|_) y (rfl|_) a ha,
  simp
end

lemma convex_univ : convex (set.univ : set PE) := λ _ _ _ _, maps_to_univ _ _

lemma convex.inter {t : set PE} (hs: convex s) (ht: convex t) : convex (s ∩ t) :=
λ x hx y hy, (hs hx.left hy.left).inter (ht hx.right hy.right)

lemma convex_sInter {S : set (set PE)} (h : ∀ s ∈ S, convex s) : convex (⋂₀ S) :=
assume x hx y hy, maps_to_sInter $ λ s hs, h s hs (hx s hs) (hy s hs)

lemma convex_Inter {ι : Sort*} {s: ι → set PE} (h: ∀ i : ι, convex (s i)) : convex (⋂ i, s i) :=
(sInter_range s) ▸ convex_sInter $ forall_range_iff.2 h

include F

lemma convex.prod {s : set PE} {t : set PF} (hs : convex s) (ht : convex t) :
  convex (s.prod t) :=
λ x hx y hy a ha, ⟨hs hx.1 hy.1 ha, ht hx.2 hy.2 ha⟩

/-- The preimage of a convex set under an affine map is convex. -/
lemma convex.affine_preimage (f : affine_map ℝ PE PF) {s : set PF} (hs : convex s) :
  convex (f ⁻¹' s) :=
begin
  intros x hx y hy a ha,
  rw [mem_preimage, f.apply_line_map],
  exact hs hx hy ha
end

/-- The image of a convex set under an affine map is convex. -/
lemma convex.affine_image (f : affine_map ℝ PE PF) (hs : convex s) :
  convex (f '' s) :=
begin
  rintros _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩,
  rw [← comp_line_map, coe_comp],
  exact (maps_to_image f s).comp (hs hx hy)
end

lemma convex.linear_image {s : set E} (hs : convex s) (f : E →ₗ[ℝ] F) : convex (image f s) :=
hs.affine_image f.to_affine_map

lemma convex.is_linear_image {s : set E} (hs : convex s) {f : E → F} (hf : is_linear_map ℝ f) :
  convex (f '' s) :=
hs.linear_image $ hf.mk' f

lemma convex.linear_preimage {s : set F} (hs : convex s) (f : E →ₗ[ℝ] F) :
  convex (preimage f s) :=
hs.affine_preimage f.to_affine_map

lemma convex.is_linear_preimage {s : set F} (hs : convex s) {f : E → F} (hf : is_linear_map ℝ f) :
  convex (preimage f s) :=
hs.linear_preimage $ hf.mk' f

omit F

lemma convex.image_neg {s : set E} (hs : convex s) : convex ((λ z, -z) '' s) :=
hs.linear_image (-linear_map.id)

lemma convex.neg {s : set E} (hs : convex s) : convex (-s) :=
hs.linear_preimage (-linear_map.id)

lemma convex.smul {s : set E} (c : ℝ) (hs : convex s) : convex (c • s) :=
hs.linear_image (linear_map.lsmul _ _ c)

lemma convex.smul_preimage {s : set E} (c : ℝ) (hs : convex s) : convex ((λ z, c • z) ⁻¹' s) :=
hs.linear_preimage (linear_map.lsmul _ _ c)

lemma convex.image_const_vadd (hs : convex s) (z : E) : convex ((λ x, z +ᵥ x) '' s) :=
hs.affine_image $ const ℝ PE z +ᵥ affine_map.id ℝ PE

lemma convex.image_const_add {s : set E} (hs : convex s) (z : E) : convex ((λ x, z + x) '' s) :=
hs.image_const_vadd z

lemma convex.image_vadd_const {s : set E} (hs : convex s) (z : PE) : convex ((λ x, x +ᵥ z) '' s) :=
hs.affine_image $ affine_map.id ℝ E +ᵥ const ℝ E z

lemma convex.image_add_const {s : set E} (hs : convex s) (z : E) : convex ((λ x, x + z) '' s) :=
hs.image_vadd_const z

lemma convex.image_const_vsub (hs : convex s) (z : PE) : convex ((λ x, z -ᵥ x) '' s) :=
hs.affine_image $ const ℝ PE z -ᵥ affine_map.id ℝ PE

lemma convex.image_const_sub {s : set E} (hs : convex s) (z : E) : convex ((λ x, z - x) '' s) :=
hs.image_const_vsub z

lemma convex.image_vsub_const (hs : convex s) (z : PE) : convex ((λ x, x -ᵥ z) '' s) :=
hs.affine_image $ affine_map.id ℝ PE -ᵥ const ℝ PE z

lemma convex.image_sub_const {s : set E} (hs : convex s) (z : E) : convex ((λ x, x - z) '' s) :=
hs.image_vsub_const z

lemma convex.vadd {s : set E} {t : set PE} (hs : convex s) (ht : convex t) :
  convex (image2 (+ᵥ) s t) :=
begin
  rw ← image_prod,
  -- This instance fails defeq for `affine_space ? (E × PE)`. Why?
  letI : affine_space (E × E) (E × PE) := prod.add_torsor,
  exact (hs.prod ht).affine_image ((affine_map.fst : affine_map ℝ (E × PE) E) +ᵥ snd)
end

lemma convex.add {s t : set E} (hs : convex s) (ht : convex t) : convex (s + t) :=
hs.vadd ht

lemma convex.vsub {s t : set PE} (hs : convex s) (ht : convex t) : convex (image2 (-ᵥ) s t) :=
begin
  rw ← image_prod,
  -- This instance fails defeq for `affine_space ? (PE × PE)`. Why?
  letI : affine_space (E × E) (PE × PE) := prod.add_torsor,
  exact (hs.prod ht).affine_image ((affine_map.fst : affine_map ℝ (PE × PE) PE) -ᵥ snd)
end

lemma convex.sub {s t : set E} (hs : convex s) (ht : convex t) :
  convex (image2 (has_sub.sub) s t) :=
hs.vsub ht

omit E

lemma real.convex_iff_ord_connected {s : set ℝ} : convex s ↔ ord_connected s :=
by simp only [convex_iff_segment_subset, segment_eq_interval, ord_connected_iff_interval_subset]

alias real.convex_iff_ord_connected ↔ convex.ord_connected set.ord_connected.convex

lemma convex_Iio (r : ℝ) : convex (Iio r) := ord_connected_Iio.convex
lemma convex_Ioi (r : ℝ) : convex (Ioi r) := ord_connected_Ioi.convex
lemma convex_Iic (r : ℝ) : convex (Iic r) := ord_connected_Iic.convex
lemma convex_Ici (r : ℝ) : convex (Ici r) := ord_connected_Ici.convex
lemma convex_Ioo (r s : ℝ) : convex (Ioo r s) := ord_connected_Ioo.convex
lemma convex_Ico (r s : ℝ) : convex (Ico r s) := ord_connected_Ico.convex
lemma convex_Ioc (r : ℝ) (s : ℝ) : convex (Ioc r s) := ord_connected_Ioc.convex
lemma convex_Icc (r : ℝ) (s : ℝ) : convex (Icc r s) := ord_connected_Icc.convex
lemma convex_interval (r : ℝ) (s : ℝ) : convex (interval r s) := ord_connected_interval.convex

include E

lemma convex_segment (a b : PE) : convex [a, b] := (convex_Icc 0 1).affine_image _

lemma affine_map.convex_lt (f : affine_map ℝ PE ℝ) (r : ℝ) :
  convex {w | f w < r} :=
(convex_Iio r).affine_preimage f

lemma affine_map.convex_le (f : affine_map ℝ PE ℝ) (r : ℝ) :
  convex {w | f w ≤ r} :=
(convex_Iic r).affine_preimage f

lemma affine_map.convex_gt (f : affine_map ℝ PE ℝ) (r : ℝ) :
  convex {w | r < f w} :=
(convex_Ioi r).affine_preimage f

lemma affine_map.convex_ge (f : affine_map ℝ E ℝ) (r : ℝ) :
  convex {w | r ≤ f w} :=
(convex_Ici r).affine_preimage f

lemma affine_map.convex_eq (f : affine_map ℝ E ℝ) (r : ℝ) :
  convex {w | f w = r} :=
(convex_singleton r).affine_preimage f

lemma linear_map.convex_lt (f : E →ₗ[ℝ] ℝ) (r : ℝ) :
  convex {w | f w < r} :=
f.to_affine_map.convex_lt r

lemma linear_map.convex_le (f : E →ₗ[ℝ] ℝ) (r : ℝ) :
  convex {w | f w ≤ r} :=
f.to_affine_map.convex_le r

lemma linear_map.convex_gt (f : E →ₗ[ℝ] ℝ) (r : ℝ) :
  convex {w | r < f w} :=
f.to_affine_map.convex_gt r

lemma linear_map.convex_ge (f : E →ₗ[ℝ] ℝ) (r : ℝ) :
  convex {w | r ≤ f w} :=
f.to_affine_map.convex_ge r

lemma linear_map.convex_eq (f : E →ₗ[ℝ] ℝ) (r : ℝ) :
  convex {w | f w = r} :=
f.to_affine_map.convex_eq r

omit E

lemma convex_halfspace_re_lt (r : ℝ) : convex {c : ℂ | c.re < r} :=
complex.linear_map.re.convex_lt r

lemma convex_halfspace_re_le (r : ℝ) : convex {c : ℂ | c.re ≤ r} :=
complex.linear_map.re.convex_le r

lemma convex_halfspace_re_gt (r : ℝ) : convex {c : ℂ | r < c.re } :=
complex.linear_map.re.convex_gt r

lemma convex_halfspace_re_ge (r : ℝ) : convex {c : ℂ | r ≤ c.re} :=
complex.linear_map.re.convex_ge r

lemma convex_halfspace_im_lt (r : ℝ) : convex {c : ℂ | c.im < r} :=
complex.linear_map.im.convex_lt r

lemma convex_halfspace_im_le (r : ℝ) : convex {c : ℂ | c.im ≤ r} :=
complex.linear_map.im.convex_le r

lemma convex_halfspace_im_gt (r : ℝ) : convex {c : ℂ | r < c.im } :=
complex.linear_map.im.convex_gt r

lemma convex_halfspace_im_ge (r : ℝ) : convex {c : ℂ | r ≤ c.im} :=
complex.linear_map.im.convex_ge r

include E

lemma affine_subspace.convex (K : affine_subspace ℝ PE) : convex (↑K : set PE) :=
λ x hx y hy a ha, K.smul_vsub_vadd_mem a hy hx hx

lemma submodule.convex (K : submodule ℝ E) : convex (↑K : set E) :=
K.to_affine_subspace.convex

end sets

section functions

variables {β : Type*} [ordered_add_comm_group β] [ordered_semimodule ℝ β]

local notation `[`x `, ` y `]` := segment x y
open affine_map (line_map line_map_apply)

/-! ### Convex functions -/

/-- Convexity of functions -/
def convex_on (s : set PE) (f : PE → β) : Prop :=
  convex s ∧
  ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) ⦃a : ℝ⦄ (ha : a ∈ I),
    f (line_map x y a) ≤ (1 - a) • f x + a • f y

/-- Concavity of functions -/
def concave_on (s : set E) (f : E → β) : Prop :=
  convex s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y ≤ f (a • x + b • y)

/-- A function f is concave iff -f is convex -/
@[simp] lemma neg_convex_on_iff {γ : Type*} [ordered_add_comm_group γ] [ordered_semimodule ℝ γ]
  (s : set E) (f : E → γ) : convex_on s (-f) ↔ concave_on s f :=
begin
  split,
  { rintros ⟨hconv, h⟩,
    refine ⟨hconv, _⟩,
    intros x y xs ys a b ha hb hab,
    specialize h xs ys ha hb hab,
    simp [neg_apply, neg_le, add_comm] at h,
    exact h },
  { rintros ⟨hconv, h⟩,
    refine ⟨hconv, _⟩,
    intros x y xs ys a b ha hb hab,
    specialize h xs ys ha hb hab,
    simp [neg_apply, neg_le, add_comm, h] }
end

/-- A function f is concave iff -f is convex -/
@[simp] lemma neg_concave_on_iff {γ : Type*} [ordered_add_comm_group γ] [ordered_semimodule ℝ γ]
  (s : set E) (f : E → γ) : concave_on s (-f) ↔ convex_on s f:=
by rw [← neg_convex_on_iff s (-f), neg_neg f]

lemma convex_on_id {s : set ℝ} (hs : convex s) : convex_on s id := ⟨hs, by { intros, refl }⟩

lemma concave_on_id {s : set ℝ} (hs : convex s) : concave_on s id := ⟨hs, by { intros, refl }⟩

lemma convex_on_const (c : β) (hs : convex s) : convex_on s (λ x:E, c) :=
⟨hs, by { intros, simp only [← add_smul, *, one_smul] }⟩

lemma concave_on_const (c : β) (hs : convex s) : concave_on s (λ x:E, c) :=
  @convex_on_const _ _ _ _ (order_dual β) _ _ c hs

variables {t : set E}

lemma convex_on_iff_div {f : E → β} :
  convex_on s f ↔ convex s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀  ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → 0 < a + b →
    f ((a/(a+b)) • x + (b/(a+b)) • y) ≤ (a/(a+b)) • f x + (b/(a+b)) • f y :=
and_congr iff.rfl
⟨begin
  intros h x y hx hy a b ha hb hab,
  apply h hx hy (div_nonneg ha $ le_of_lt hab) (div_nonneg hb $ le_of_lt hab),
  rw [←add_div],
  exact div_self (ne_of_gt hab)
end,
begin
  intros h x y hx hy a b ha hb hab,
  simpa [hab, zero_lt_one] using h hx hy ha hb,
end⟩

lemma concave_on_iff_div {f : E → β} :
  concave_on s f ↔ convex s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀  ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → 0 < a + b →
    (a/(a+b)) • f x + (b/(a+b)) • f y ≤ f ((a/(a+b)) • x + (b/(a+b)) • y) :=
  @convex_on_iff_div _ _ _ _ (order_dual β) _ _ _

/-- For a function on a convex set in a linear ordered space, in order to prove that it is convex
it suffices to verify the inequality `f (a • x + b • y) ≤ a • f x + b • f y` only for `x < y`
and positive `a`, `b`. The main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with
lexicographic order. -/
lemma linear_order.convex_on_of_lt {f : PE → β} [linear_order PE] (hs : convex s)
  (hf : ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) (hlt : x < y) ⦃a : ℝ⦄ (ha : a ∈ Ioo (0:ℝ) 1),
    f (line_map x y a) ≤ (1 - a) • f x + a • f y) : convex_on s f :=
begin
  use hs,
  intros x hx y hy a ha,
  generalize hb : 1 - a = b,
  wlog hxy : x<=y := le_total x y using [x y a b, y x b a] tactic.skip,
  { subst b,
    rcases hxy.eq_or_lt with rfl|hxy, { simp [← add_smul, function.const] },
    rcases ha.1.eq_or_lt with rfl|h₀, { simp },
    rcases ha.2.eq_or_lt with rfl|h₁, { simp },
    exact hf hx hy hxy ⟨h₀, h₁⟩ },
  { rintros hx hy ha rfl,
    rw [affine_map.line_map_symm, affine_map.comp_apply, add_comm],
    convert this hy hx ⟨sub_nonneg.2 ha.2, sub_le_self _ ha.1⟩ (sub_sub_cancel _ _),
    simp [line_map_apply, sub_eq_neg_add] }
end

omit E

/-- For a function on a convex set in a linear ordered space, in order to prove that it is concave
it suffices to verify the inequality `a • f x + b • f y ≤ f (a • x + b • y)` only for `x < y`
and positive `a`, `b`. The main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with
lexicographic order. -/
lemma linear_order.concave_on_of_lt {f : E → β} [linear_order E] (hs : convex s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
     a • f x + b • f y ≤ f (a • x + b • y)) : concave_on s f :=
  @linear_order.convex_on_of_lt _ _ _ _ (order_dual β) _ _ f _ hs hf

/-- For a function `f` defined on a convex subset `D` of `ℝ`, if for any three points `x<y<z`
the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is convex on `D`. This way of proving convexity
of a function is used in the proof of convexity of a function with a monotone derivative. -/
lemma convex_on_real_of_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ}
  (hf : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :
  convex_on s f :=
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
  have A : z - y + (y - x) = z - x, by abel,
  have B : 0 < z - x, from sub_pos.2 (lt_trans hxy hyz),
  rw [sub_mul, sub_mul, sub_le_iff_le_add', ← add_sub_assoc, le_sub_iff_add_le, ← mul_add, A,
    ← le_div_iff B, add_div, mul_div_assoc, mul_div_assoc,
    mul_comm (f x), mul_comm (f z)] at this,
  rw [eq_comm, ← sub_eq_iff_eq_add] at hab; subst a,
  convert this; symmetry; simp only [div_eq_iff (ne_of_gt B), y]; ring
end

/-- For a function `f` defined on a subset `D` of `ℝ`, if `f` is convex on `D`, then for any three
points `x<y<z`, the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`. -/
lemma convex_on.slope_mono_adjacent {s : set ℝ} {f : ℝ → ℝ} (hf : convex_on s f)
  {x y z : ℝ} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
begin
  have h₁ : 0 < y - x := by linarith,
  have h₂ : 0 < z - y := by linarith,
  have h₃ : 0 < z - x := by linarith,
  suffices : f y / (y - x) + f y / (z - y) ≤ f x / (y - x) + f z / (z - y),
    by { ring at this ⊢, linarith },
  set a := (z - y) / (z - x),
  set b := (y - x) / (z - x),
  have heqz : a • x + b • z = y, by { field_simp, rw div_eq_iff; [ring, linarith], },
  have key, from
    hf.2 hx hz
      (show 0 ≤ a, by apply div_nonneg; linarith)
      (show 0 ≤ b, by apply div_nonneg; linarith)
      (show a + b = 1, by { field_simp, rw div_eq_iff; [ring, linarith], }),
  rw heqz at key,
  replace key := mul_le_mul_of_nonneg_left key (le_of_lt h₃),
  field_simp [ne_of_gt h₁, ne_of_gt h₂, ne_of_gt h₃, mul_comm (z - x) _] at key ⊢,
  rw div_le_div_right,
  { linarith, },
  { nlinarith, },
end

/-- For a function `f` defined on a convex subset `D` of `ℝ`, `f` is convex on `D` iff for any three
points `x<y<z` the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`. -/
lemma convex_on_real_iff_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ} :
  convex_on s f ↔
  (∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :=
⟨convex_on.slope_mono_adjacent, convex_on_real_of_slope_mono_adjacent hs⟩

/-- For a function `f` defined on a convex subset `D` of `ℝ`, if for any three points `x<y<z`
the slope of the secant line of `f` on `[x, y]` is greater than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is concave on `D`. -/
lemma concave_on_real_of_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ}
  (hf : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) : concave_on s f :=
begin
  rw [←neg_convex_on_iff],
  apply convex_on_real_of_slope_mono_adjacent hs,
  intros x y z xs zs xy yz,
  rw [←neg_le_neg_iff, ←neg_div, ←neg_div, neg_sub, neg_sub],
  simp only [hf xs zs xy yz, neg_sub_neg, pi.neg_apply],
end

/-- For a function `f` defined on a subset `D` of `ℝ`, if `f` is concave on `D`, then for any three
points `x<y<z`, the slope of the secant line of `f` on `[x, y]` is greater than or equal to the
slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on.slope_mono_adjacent {s : set ℝ} {f : ℝ → ℝ} (hf : concave_on s f)
  {x y z : ℝ} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
begin
  rw [←neg_le_neg_iff, ←neg_div, ←neg_div, neg_sub, neg_sub],
  rw [←neg_sub_neg (f y), ←neg_sub_neg (f z)],
  simp_rw [←pi.neg_apply],
  rw [←neg_convex_on_iff] at hf,
  apply convex_on.slope_mono_adjacent hf; assumption,
end

/-- For a function `f` defined on a convex subset `D` of `ℝ`, `f` is concave on `D` iff for any
three points `x<y<z` the slope of the secant line of `f` on `[x, y]` is greater than or equal to
the slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on_real_iff_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ} :
  concave_on s f ↔
  (∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) :=
⟨concave_on.slope_mono_adjacent, concave_on_real_of_slope_mono_adjacent hs⟩

lemma convex_on.subset {f : E → β} (h_convex_on : convex_on t f)
  (h_subset : s ⊆ t) (h_convex : convex s) : convex_on s f :=
⟨h_convex, λ x hx y hy, h_convex_on.2 (h_subset hx) (h_subset hy)⟩

lemma concave_on.subset {f : E → β}
  (h_concave_on : concave_on t f) (h_subset : s ⊆ t) (h_convex : convex s) : concave_on s f :=
@convex_on.subset _ _ _ _ (order_dual β) _ _ t f h_concave_on h_subset h_convex

lemma convex_on.add {f g : E → β} (hf : convex_on s f) (hg : convex_on s g) :
  convex_on s (λx, f x + g x) :=
and.intro hf.1 $ assume x hx y hy a ha,
calc _ ≤ ((1 - a) • f x + a • f y) + ((1 - a) • g x + a • g y) :
  add_le_add (hf.2 hx hy ha) (hg.2 hx hy ha)
... = (1 - a) • (f x + g x) + a • (f y + g y) : by { rw [smul_add, smul_add], abel }

lemma concave_on.add {f g : E → β} (hf : concave_on s f) (hg : concave_on s g) :
  concave_on s (λx, f x + g x) :=
@convex_on.add _ _ _ _ (order_dual β) _ _ f g hf hg

lemma convex_on.smul {f : E → β} {c : ℝ} (hc : 0 ≤ c) (hf : convex_on s f) :
  convex_on s (λx, c • f x) :=
and.intro hf.1 $ assume x hx y hy a ha,
calc c • f (line_map x y a) ≤ c • ((1 - a) • f x + a • f y) :
  smul_le_smul_of_nonneg (hf.2 hx hy ha) hc
... = (1 - a) • (c • f x) + a • (c • f y) : by simp only [smul_add, smul_comm]

/--
If `f x ≤ c`, `f y ≤ c`, and `f : PE → β` is convex on a set `s ⊇ {x, y}`, then `f` is bounded
above by `c` on `[x, y]`. For a function `f : PE → ℝ` we can use `a = max (f x) (f y)`.
This version takes an argument `a ∈ [0, 1]` and proves `f (a • (y -ᵥ x) +ᵥ x) ≤ c`.
-/
lemma convex_on.le_on_segment_of_le' {f : PE → β} {c : β} {x y : PE} {a : ℝ} (hf : convex_on s f)
  (hx : x ∈ s) (hy : y ∈ s) (hfx : f x ≤ c) (hfy : f y ≤ c) (ha : a ∈ I) :
  f (line_map x y a) ≤ c :=
calc f (line_map x y a) ≤ (1 - a) • f x + a • f y : hf.2 hx hy ha
... ≤ (1 - a) • c + a • c :
  add_le_add (smul_le_smul_of_nonneg hfx $ sub_nonneg.2 ha.2) (smul_le_smul_of_nonneg hfy ha.1)
... = c : by rw [← add_smul, sub_add_cancel, one_smul]

/--
If `f x ≤ c`, `f y ≤ c`, and `f : PE → β` is convex on a set `s ⊇ {x, y}`, then `f` is bounded
above by `c` on `[x, y]`. For a function `f : PE → ℝ` we can use `a = max (f x) (f y)`.
-/
lemma convex_on.le_on_segment_of_le {f : PE → β} {c : β} {x y z : PE} (hf : convex_on s f)
  (hx : x ∈ s) (hy : y ∈ s) (hfx : f x ≤ c) (hfy : f y ≤ c) (hz : z ∈ [x, y]) :
  f z ≤ c :=
let ⟨a, ha, hz⟩ := hz in hz ▸ hf.le_on_segment_of_le' hx hy hfx hfy ha

/--
If `f x < c`, `f y < c`, and `f : PE → β` is convex on a set `s ⊇ {x, y}`, then `f z < c`
on `[x, y]`. This version takes an argument `a ∈ [0, 1]` and proves `f (a • (y -ᵥ x) +ᵥ x) < c`.
-/
lemma convex_on.lt_on_segment_of_lt' {f : PE → β} {c : β} {x y : PE} {a : ℝ} (hf : convex_on s f)
  (hx : x ∈ s) (hy : y ∈ s) (hfx : f x < c) (hfy : f y < c) (ha : a ∈ I) :
  f (line_map x y a) < c :=
begin
  rcases ha.1.eq_or_lt with rfl|hlt, { simpa },
  calc f (line_map x y a) ≤ (1 - a) • f x + a • f y : hf.2 hx hy ha
  ... < (1 - a) • c + a • c :
    add_lt_add_of_le_of_lt (smul_le_smul_of_nonneg hfx.le (sub_nonneg.2 ha.2))
      (smul_lt_smul_of_pos hfy hlt)
  ... = c : by rw [← add_smul, sub_add_cancel, one_smul]
end

lemma concave_on.smul {f : E → β} {c : ℝ} (hc : 0 ≤ c) (hf : concave_on s f) :
  concave_on s (λx, c • f x) :=
@convex_on.smul _ _ _ _ (order_dual β) _ _ f c hc hf

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment' {γ : Type*}
  [decidable_linear_ordered_add_comm_group γ] [ordered_semimodule ℝ γ]
  {f : E → γ} {x y : E} {a b : ℝ}
  (hf : convex_on s f) (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  f (a • x + b • y) ≤ max (f x) (f y) :=
calc
  f (a • x + b • y) ≤ a • f x + b • f y : hf.2 hx hy ha hb hab
  ... ≤ a • max (f x) (f y) + b • max (f x) (f y) :
    add_le_add (smul_le_smul_of_nonneg (le_max_left _ _) ha) (smul_le_smul_of_nonneg (le_max_right _ _) hb)
  ... ≤ max (f x) (f y) : by rw [←add_smul, hab, one_smul]

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.le_on_segment' {γ : Type*}
  [decidable_linear_ordered_add_comm_group γ] [ordered_semimodule ℝ γ]
  {f : E → γ} {x y : E} {a b : ℝ}
  (hf : concave_on s f) (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  min (f x) (f y) ≤ f (a • x + b • y) :=
@convex_on.le_on_segment' _ _ _ _ (order_dual γ) _ _ f x y a b hf hx hy ha hb hab

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment {γ : Type*}
  [decidable_linear_ordered_add_comm_group γ] [ordered_semimodule ℝ γ]
  {f : E → γ} (hf : convex_on s f) {x y z : E}
  (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x, y]) :
  f z ≤ max (f x) (f y) :=
let ⟨a, b, ha, hb, hab, hz⟩ := hz in hz ▸ hf.le_on_segment' hx hy ha hb hab

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.le_on_segment {γ : Type*}
  [decidable_linear_ordered_add_comm_group γ] [ordered_semimodule ℝ γ]
  {f : E → γ} (hf : concave_on s f) {x y z : E}
  (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x, y]) :
    min (f x) (f y) ≤ f z :=
@convex_on.le_on_segment _ _ _ _ (order_dual γ) _ _ f hf x y z hx hy hz

lemma convex_on.convex_le {f : E → β} (hf : convex_on s f) (r : β) : convex {x ∈ s | f x ≤ r} :=
convex_iff_segment_subset.2 $ λ x y hx hy z hz,
begin
  refine ⟨hf.1.segment_subset hx.1 hy.1 hz,_⟩,
  rcases hz with ⟨za,zb,hza,hzb,hzazb,H⟩,
  rw ←H,
  calc
    f (za • x + zb • y) ≤ za • (f x) + zb • (f y)   : hf.2 hx.1 hy.1 hza hzb hzazb
                    ... ≤ za • r + zb • r
                      : add_le_add (smul_le_smul_of_nonneg hx.2 hza)
                                    (smul_le_smul_of_nonneg hy.2 hzb)
                    ... ≤ r                         : by simp [←add_smul, hzazb]
end

lemma concave_on.concave_le {f : E → β} (hf : concave_on s f) (r : β) : convex {x ∈ s | r ≤ f x} :=
  @convex_on.convex_le _ _ _ _ (order_dual β) _ _ f hf r


lemma convex_on.convex_lt {γ : Type*} [ordered_cancel_add_comm_monoid γ] [ordered_semimodule ℝ γ]
  {f : E → γ} (hf : convex_on s f) (r : γ) : convex {x ∈ s | f x < r} :=
begin
  intros a b as bs xa xb hxa hxb hxaxb,
  refine ⟨hf.1 as.1 bs.1 hxa hxb hxaxb,_⟩,
  dsimp,
  by_cases H : xa = 0,
  { have H' : xb = 1 := by rwa [H, zero_add] at hxaxb,
    rw [H, H', zero_smul, one_smul, zero_add],
    exact bs.2 },
  { calc
      f (xa • a + xb • b) ≤ xa • (f a) + xb • (f b)       : hf.2 as.1 bs.1 hxa hxb hxaxb
                      ... < xa • r + xb • (f b)
                        : (add_lt_add_iff_right (xb • (f b))).mpr
                          (smul_lt_smul_of_pos as.2
                            (lt_of_le_of_ne hxa (ne.symm H)))
                      ... ≤ xa • r + xb • r
                        : (add_le_add_iff_left (xa • r)).mpr
                          (smul_le_smul_of_nonneg (le_of_lt bs.2) hxb)
                      ... = r
                        : by simp only [←add_smul, hxaxb, one_smul] }
end

lemma concave_on.convex_lt {γ : Type*} [ordered_cancel_add_comm_monoid γ] [ordered_semimodule ℝ γ]
  {f : E → γ} (hf : concave_on s f) (r : γ) : convex {x ∈ s | r < f x} :=
@convex_on.convex_lt _ _ _ _ (order_dual γ) _ _ f hf r

lemma convex_on.convex_epigraph {γ : Type*} [ordered_add_comm_group γ] [ordered_semimodule ℝ γ]
  {f : E → γ} (hf : convex_on s f) :
  convex {p : E × γ | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  rintros ⟨x, r⟩ ⟨y, t⟩ ⟨hx, hr⟩ ⟨hy, ht⟩ a b ha hb hab,
  refine ⟨hf.1 hx hy ha hb hab, _⟩,
  calc f (a • x + b • y) ≤ a • f x + b • f y : hf.2 hx hy ha hb hab
  ... ≤ a • r + b • t : add_le_add (smul_le_smul_of_nonneg hr ha)
                            (smul_le_smul_of_nonneg ht hb)
end

lemma concave_on.convex_hypograph {γ : Type*} [ordered_add_comm_group γ] [ordered_semimodule ℝ γ]
  {f : E → γ} (hf : concave_on s f) :
  convex {p : E × γ | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
@convex_on.convex_epigraph _ _ _ _ (order_dual γ) _ _ f hf

lemma convex_on_iff_convex_epigraph {γ : Type*} [ordered_add_comm_group γ] [ordered_semimodule ℝ γ]
  {f : E → γ} :
  convex_on s f ↔ convex {p : E × γ | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  refine ⟨convex_on.convex_epigraph, λ h, ⟨_, _⟩⟩,
  { assume x y hx hy a b ha hb hab,
    exact (@h (x, f x) (y, f y) ⟨hx, le_refl _⟩ ⟨hy, le_refl _⟩ a b ha hb hab).1 },
  { assume x y hx hy a b ha hb hab,
    exact (@h (x, f x) (y, f y) ⟨hx, le_refl _⟩ ⟨hy, le_refl _⟩ a b ha hb hab).2 }
end

lemma concave_on_iff_convex_hypograph {γ : Type*} [ordered_add_comm_group γ] [ordered_semimodule ℝ γ]
  {f : E → γ} :
  concave_on s f ↔ convex {p : E × γ | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
@convex_on_iff_convex_epigraph _ _ _ _ (order_dual γ) _ _ f

/-- If a function is convex on s, it remains convex when precomposed by an affine map -/
lemma convex_on.comp_affine_map {f : F → β} (g : affine_map ℝ E F) {s : set F}
  (hf : convex_on s f) : convex_on (g ⁻¹' s) (f ∘ g) :=
begin
  refine ⟨hf.1.affine_preimage  _,_⟩,
  intros x y xs ys a b ha hb hab,
  calc
    (f ∘ g) (a • x + b • y) = f (g (a • x + b • y))         : rfl
                       ...  = f (a • (g x) + b • (g y))     : by rw [convex.combo_affine_apply hab]
                       ...  ≤ a • f (g x) + b • f (g y)     : hf.2 xs ys ha hb hab
                       ...  = a • (f ∘ g) x + b • (f ∘ g) y  : rfl
end

/-- If a function is concave on s, it remains concave when precomposed by an affine map -/
lemma concave_on.comp_affine_map {f : F → β} (g : affine_map ℝ E F) {s : set F}
  (hf : concave_on s f) : concave_on (g ⁻¹' s) (f ∘ g) :=
@convex_on.comp_affine_map _ _ _ _ _ _ (order_dual β) _ _ f g s hf

/-- If g is convex on s, so is (g ∘ f) on f ⁻¹' s for a linear f. -/
lemma convex_on.comp_linear_map {g : F → β} {s : set F} (hg : convex_on s g) (f : E →ₗ[ℝ] F) :
  convex_on (f ⁻¹' s) (g ∘ f) :=
hg.comp_affine_map f.to_affine_map

/-- If g is concave on s, so is (g ∘ f) on f ⁻¹' s for a linear f. -/
lemma concave_on.comp_linear_map {g : F → β} {s : set F} (hg : concave_on s g) (f : E →ₗ[ℝ] F) :
  concave_on (f ⁻¹' s) (g ∘ f) :=
hg.comp_affine_map f.to_affine_map

/-- If a function is convex on s, it remains convex after a translation. -/
lemma convex_on.translate_right {f : E → β} {s : set E} {a : E} (hf : convex_on s f) :
  convex_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, a + z)) :=
hf.comp_affine_map $ affine_map.const ℝ E a +ᵥ affine_map.id ℝ E

/-- If a function is concave on s, it remains concave after a translation. -/
lemma concave_on.translate_right {f : E → β} {s : set E} {a : E} (hf : concave_on s f) :
  concave_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, a + z)) :=
hf.comp_affine_map $ affine_map.const ℝ E a +ᵥ affine_map.id ℝ E

/-- If a function is convex on s, it remains convex after a translation. -/
lemma convex_on.translate_left {f : E → β} {s : set E} {a : E} (hf : convex_on s f) :
  convex_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, z + a)) :=
by simpa only [add_comm] using  hf.translate_right

/-- If a function is concave on s, it remains concave after a translation. -/
lemma concave_on.translate_left {f : E → β} {s : set E} {a : E} (hf : concave_on s f) :
  concave_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, z + a)) :=
by simpa only [add_comm] using  hf.translate_right

end functions

section center_mass

/-- Center mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
noncomputable def finset.center_mass (t : finset ι) (w : ι → ℝ) (z : ι → E) : E :=
(∑ i in t, w i)⁻¹ • (∑ i in t, w i • z i)

variables (i j : ι) (c : ℝ) (t : finset ι) (w : ι → ℝ) (z : ι → E)

open finset

lemma finset.center_mass_empty : (∅ : finset ι).center_mass w z = 0 :=
by simp only [center_mass, sum_empty, smul_zero]

lemma finset.center_mass_pair (hne : i ≠ j) :
  ({i, j} : finset ι).center_mass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j :=
by simp only [center_mass, sum_pair hne, smul_add, (mul_smul _ _ _).symm, div_eq_inv_mul]

variable {w}

lemma finset.center_mass_insert (ha : i ∉ t) (hw : ∑ j in t, w j ≠ 0) :
  (insert i t).center_mass w z = (w i / (w i + ∑ j in t, w j)) • z i +
    ((∑ j in t, w j) / (w i + ∑ j in t, w j)) • t.center_mass w z :=
begin
  simp only [center_mass, sum_insert ha, smul_add, (mul_smul _ _ _).symm],
  congr' 2,
  { apply mul_comm },
  { rw [div_mul_eq_mul_div, mul_inv_cancel hw, one_div] }
end

lemma finset.center_mass_singleton (hw : w i ≠ 0) : ({i} : finset ι).center_mass w z = z i :=
by rw [center_mass, sum_singleton, sum_singleton, ← mul_smul, inv_mul_cancel hw, one_smul]

lemma finset.center_mass_eq_of_sum_1 (hw : ∑ i in t, w i = 1) :
  t.center_mass w z = ∑ i in t, w i • z i :=
by simp only [finset.center_mass, hw, inv_one, one_smul]

lemma finset.center_mass_smul : t.center_mass w (λ i, c • z i) = c • t.center_mass w z :=
by simp only [finset.center_mass, finset.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
lemma finset.center_mass_segment'
  (s : finset ι) (t : finset ι') (ws : ι → ℝ) (zs : ι → E) (wt : ι' → ℝ) (zt : ι' → E)
  (hws : ∑ i in s, ws i = 1) (hwt : ∑ i in t, wt i = 1) (a b : ℝ) (hab : a + b = 1):
  a • s.center_mass ws zs + b • t.center_mass wt zt =
    (s.image sum.inl ∪ t.image sum.inr).center_mass
      (sum.elim (λ i, a * ws i) (λ j, b * wt j))
      (sum.elim zs zt) :=
begin
  rw [s.center_mass_eq_of_sum_1 _ hws, t.center_mass_eq_of_sum_1 _ hwt,
    smul_sum, smul_sum, ← finset.sum_sum_elim, finset.center_mass_eq_of_sum_1],
  { congr' with ⟨⟩; simp only [sum.elim_inl, sum.elim_inr, mul_smul] },
  { rw [sum_sum_elim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab] }
end

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
lemma finset.center_mass_segment
  (s : finset ι) (w₁ w₂ : ι → ℝ) (z : ι → E)
  (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) (a b : ℝ) (hab : a + b = 1):
  a • s.center_mass w₁ z + b • s.center_mass w₂ z =
    s.center_mass (λ i, a * w₁ i + b * w₂ i) z :=
have hw : ∑ i in s, (a * w₁ i + b * w₂ i) = 1,
  by simp only [mul_sum.symm, sum_add_distrib, mul_one, *],
by simp only [finset.center_mass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]

lemma finset.center_mass_ite_eq (hi : i ∈ t) :
  t.center_mass (λ j, if (i = j) then 1 else 0) z = z i :=
begin
  rw [finset.center_mass_eq_of_sum_1],
  transitivity ∑ j in t, if (i = j) then z i else 0,
  { congr' with i, split_ifs, exacts [h ▸ one_smul _ _, zero_smul _ _] },
  { rw [sum_ite_eq, if_pos hi] },
  { rw [sum_ite_eq, if_pos hi] }
end

variables {t w}

lemma finset.center_mass_subset {t' : finset ι} (ht : t ⊆ t')
  (h : ∀ i ∈ t', i ∉ t → w i = 0) :
  t.center_mass w z = t'.center_mass w z :=
begin
  rw [center_mass, sum_subset ht h, smul_sum, center_mass, smul_sum],
  apply sum_subset ht,
  assume i hit' hit,
  rw [h i hit' hit, zero_smul, smul_zero]
end

lemma finset.center_mass_filter_ne_zero :
  (t.filter (λ i, w i ≠ 0)).center_mass w z = t.center_mass w z :=
finset.center_mass_subset z (filter_subset _) $ λ i hit hit',
by simpa only [hit, mem_filter, true_and, ne.def, not_not] using hit'

variable {z}

/-- Center mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
lemma convex.center_mass_mem (hs : convex s) :
  (∀ i ∈ t, 0 ≤ w i) → (0 < ∑ i in t, w i) → (∀ i ∈ t, z i ∈ s) → t.center_mass w z ∈ s :=
begin
  induction t using finset.induction with i t hi ht, { simp [lt_irrefl] },
  intros h₀ hpos hmem,
  have zi : z i ∈ s, from hmem _ (mem_insert_self _ _),
  have hs₀ : ∀ j ∈ t, 0 ≤ w j, from λ j hj, h₀ j $ mem_insert_of_mem hj,
  rw [sum_insert hi] at hpos,
  by_cases hsum_t : ∑ j in t, w j = 0,
  { have ws : ∀ j ∈ t, w j = 0, from (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t,
    have wz : ∑ j in t, w j • z j = 0, from sum_eq_zero (λ i hi, by simp [ws i hi]),
    simp only [center_mass, sum_insert hi, wz, hsum_t, add_zero],
    simp only [hsum_t, add_zero] at hpos,
    rw [← mul_smul, inv_mul_cancel (ne_of_gt hpos), one_smul],
    exact zi },
  { rw [finset.center_mass_insert _ _ _ hi hsum_t],
    refine convex_iff_div.1 hs zi (ht hs₀ _ _) _ (sum_nonneg hs₀) hpos,
    { exact lt_of_le_of_ne (sum_nonneg hs₀) (ne.symm hsum_t) },
    { intros j hj, exact hmem j (mem_insert_of_mem hj) },
    { exact h₀ _ (mem_insert_self _ _) } }
end

lemma convex.sum_mem (hs : convex s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hz : ∀ i ∈ t, z i ∈ s) :
  ∑ i in t, w i • z i ∈ s :=
by simpa only [h₁, center_mass, inv_one, one_smul] using
  hs.center_mass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

lemma convex_iff_sum_mem :
  convex s ↔
    (∀ (t : finset E) (w : E → ℝ),
      (∀ i ∈ t, 0 ≤ w i) → ∑ i in t, w i = 1 → (∀ x ∈ t, x ∈ s) → ∑ x in t, w x • x ∈ s ) :=
begin
  refine ⟨λ hs t w hw₀ hw₁ hts, hs.sum_mem hw₀ hw₁ hts, _⟩,
  intros h x y hx hy a b ha hb hab,
  by_cases h_cases: x = y,
  { rw [h_cases, ←add_smul, hab, one_smul], exact hy },
  { convert h {x, y} (λ z, if z = y then b else a) _ _ _,
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl] },
    { simp_intros i hi,
      cases hi; subst i; simp [ha, hb, if_neg h_cases] },
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl, hab] },
    { simp_intros i hi,
      cases hi; subst i; simp [hx, hy, if_neg h_cases] } }
end

/-- Jensen's inequality, `finset.center_mass` version. -/
lemma convex_on.map_center_mass_le {f : E → ℝ} (hf : convex_on s f)
  (h₀ : ∀ i ∈ t, 0 ≤ w i) (hpos : 0 < ∑ i in t, w i)
  (hmem : ∀ i ∈ t, z i ∈ s) : f (t.center_mass w z) ≤ t.center_mass w (f ∘ z) :=
begin
  have hmem' : ∀ i ∈ t, (z i, (f ∘ z) i) ∈ {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2},
    from λ i hi, ⟨hmem i hi, le_refl _⟩,
  convert (hf.convex_epigraph.center_mass_mem h₀ hpos hmem').2;
    simp only [center_mass, function.comp, prod.smul_fst, prod.fst_sum, prod.smul_snd, prod.snd_sum]
end

/-- Jensen's inequality, `finset.sum` version. -/
lemma convex_on.map_sum_le {f : E → ℝ} (hf : convex_on s f)
  (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hmem : ∀ i ∈ t, z i ∈ s) : f (∑ i in t, w i • z i) ≤ ∑ i in t, w i * (f (z i)) :=
by simpa only [center_mass, h₁, inv_one, one_smul]
  using hf.map_center_mass_le h₀ (h₁.symm ▸ zero_lt_one) hmem

/-- If a function `f` is convex on `s` takes value `y` at the center mass of some points
`z i ∈ s`, then for some `i` we have `y ≤ f (z i)`. -/
lemma convex_on.exists_ge_of_center_mass {f : E → ℝ} (h : convex_on s f)
  (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hws : 0 < ∑ i in t, w i) (hz : ∀ i ∈ t, z i ∈ s) :
  ∃ i ∈ t, f (t.center_mass w z) ≤ f (z i) :=
begin
  set y := t.center_mass w z,
  have : f y ≤ t.center_mass w (f ∘ z) := h.map_center_mass_le hw₀ hws hz,
  rw ← sum_filter_ne_zero at hws,
  rw [← finset.center_mass_filter_ne_zero (f ∘ z), center_mass, smul_eq_mul,
    ← div_eq_inv_mul, le_div_iff hws, mul_sum] at this,
  replace : ∃ i ∈ t.filter (λ i, w i ≠ 0), f y * w i ≤ w i • (f ∘ z) i :=
    exists_le_of_sum_le (nonempty_of_sum_ne_zero (ne_of_gt hws)) this,
  rcases this with ⟨i, hi, H⟩,
  rw [mem_filter] at hi,
  use [i, hi.1],
  simp only [smul_eq_mul, mul_comm (w i)] at H,
  refine (mul_le_mul_right _).1 H,
  exact lt_of_le_of_ne (hw₀ i hi.1) hi.2.symm
end

end center_mass

section convex_hull

variable {t : set E}

/-- Convex hull of a set `s` is the minimal convex set that includes `s` -/
def convex_hull (s : set E) : set E :=
⋂ (t : set E) (hst : s ⊆ t) (ht : convex t), t

variable (s)

lemma subset_convex_hull : s ⊆ convex_hull s :=
set.subset_Inter $ λ t, set.subset_Inter $ λ hst, set.subset_Inter $ λ ht, hst

lemma convex_convex_hull : convex (convex_hull s) :=
convex_Inter $ λ t, convex_Inter $ λ ht, convex_Inter id

variable {s}

lemma convex_hull_min (hst : s ⊆ t) (ht : convex t) : convex_hull s ⊆ t :=
set.Inter_subset_of_subset t $ set.Inter_subset_of_subset hst $ set.Inter_subset _ ht

lemma convex_hull_mono (hst : s ⊆ t) : convex_hull s ⊆ convex_hull t :=
convex_hull_min (set.subset.trans hst $ subset_convex_hull t) (convex_convex_hull t)

lemma convex.convex_hull_eq {s : set E} (hs : convex s) : convex_hull s = s :=
set.subset.antisymm (convex_hull_min (set.subset.refl _) hs) (subset_convex_hull s)

@[simp]
lemma convex_hull_singleton {x : E} : convex_hull ({x} : set E) = {x} :=
(convex_singleton x).convex_hull_eq

lemma is_linear_map.image_convex_hull {f : E → F} (hf : is_linear_map ℝ f) :
  f '' (convex_hull s) = convex_hull (f '' s) :=
begin
  refine set.subset.antisymm _ _,
  { rw [set.image_subset_iff],
    exact convex_hull_min (set.image_subset_iff.1 $ subset_convex_hull $ f '' s)
      ((convex_convex_hull (f '' s)).is_linear_preimage hf) },
  { exact convex_hull_min (set.image_subset _ $ subset_convex_hull s)
     ((convex_convex_hull s).is_linear_image hf) }
end

lemma linear_map.image_convex_hull (f : E →ₗ[ℝ] F) :
  f '' (convex_hull s) = convex_hull (f '' s) :=
f.is_linear.image_convex_hull

lemma finset.center_mass_mem_convex_hull (t : finset ι) {w : ι → ℝ} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
  (hws : 0 < ∑ i in t, w i) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) :
  t.center_mass w z ∈ convex_hull s :=
(convex_convex_hull s).center_mass_mem hw₀ hws (λ i hi, subset_convex_hull s $ hz i hi)

-- TODO : Do we need other versions of the next lemma?

/-- Convex hull of `s` is equal to the set of all centers of masses of `finset`s `t`, `z '' t ⊆ s`.
This version allows finsets in any type in any universe. -/
lemma convex_hull_eq (s : set E) :
  convex_hull s = {x : E | ∃ (ι : Type u') (t : finset ι) (w : ι → ℝ) (z : ι → E)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i in t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s) , t.center_mass w z = x} :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    use [punit, {punit.star}, λ _, 1, λ _, x, λ _ _, zero_le_one,
      finset.sum_singleton, λ _ _, hx],
    simp only [finset.center_mass, finset.sum_singleton, inv_one, one_smul] },
  { rintros x y ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩
      a b ha hb hab,
    rw [finset.center_mass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab],
    refine ⟨_, _, _, _, _, _, _, rfl⟩,
    { rintros i hi,
      rw [finset.mem_union, finset.mem_image, finset.mem_image] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩;
        simp only [sum.elim_inl, sum.elim_inr];
        apply_rules [mul_nonneg, hwx₀, hwy₀] },
    { simp [finset.sum_sum_elim, finset.mul_sum.symm, *] },
    { intros i hi,
      rw [finset.mem_union, finset.mem_image, finset.mem_image] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩;
        simp only [sum.elim_inl, sum.elim_inr]; apply_rules [hzx, hzy] } },
  { rintros _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩,
    exact t.center_mass_mem_convex_hull hw₀ (hw₁.symm ▸ zero_lt_one) hz }
end

/-- Maximum principle for convex functions. If a function `f` is convex on the convex hull of `s`,
then `f` can't have a maximum on `convex_hull s` outside of `s`. -/
lemma convex_on.exists_ge_of_mem_convex_hull {f : E → ℝ} (hf : convex_on (convex_hull s) f)
  {x} (hx : x ∈ convex_hull s) : ∃ y ∈ s, f x ≤ f y :=
begin
  rw convex_hull_eq at hx,
  rcases hx with ⟨α, t, w, z, hw₀, hw₁, hz, rfl⟩,
  rcases hf.exists_ge_of_center_mass hw₀ (hw₁.symm ▸ zero_lt_one)
    (λ i hi, subset_convex_hull s (hz i hi)) with ⟨i, hit, Hi⟩,
  exact ⟨z i, hz i hit, Hi⟩
end

lemma finset.convex_hull_eq (s : finset E) :
  convex_hull ↑s = {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : ∑ y in s, w y = 1),
    s.center_mass w id = x} :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    rw [finset.mem_coe] at hx,
    refine ⟨_, _, _, finset.center_mass_ite_eq _ _ _ hx⟩,
    { intros, split_ifs, exacts [zero_le_one, le_refl 0] },
    { rw [finset.sum_ite_eq, if_pos hx] } },
  { rintros x y ⟨wx, hwx₀, hwx₁, rfl⟩ ⟨wy, hwy₀, hwy₁, rfl⟩
      a b ha hb hab,
    rw [finset.center_mass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab],
    refine ⟨_, _, _, rfl⟩,
    { rintros i hi,
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀], },
    { simp only [finset.sum_add_distrib, finset.mul_sum.symm, mul_one, *] } },
  { rintros _ ⟨w, hw₀, hw₁, rfl⟩,
    exact s.center_mass_mem_convex_hull (λ x hx, hw₀ _  hx)
      (hw₁.symm ▸ zero_lt_one) (λ x hx, hx) }
end

lemma set.finite.convex_hull_eq {s : set E} (hs : finite s) :
  convex_hull s = {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : ∑ y in hs.to_finset, w y = 1),
    hs.to_finset.center_mass w id = x} :=
by simpa only [set.finite.coe_to_finset, set.finite.mem_to_finset, exists_prop]
  using hs.to_finset.convex_hull_eq

lemma convex_hull_eq_union_convex_hull_finite_subsets (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s), convex_hull ↑t :=
begin
  refine subset.antisymm _ _,
  { rw [convex_hull_eq.{u}],
    rintros x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩,
    simp only [mem_Union],
    refine ⟨t.image z, _, _⟩,
    { rw [finset.coe_image, image_subset_iff],
      exact hz },
    { apply t.center_mass_mem_convex_hull hw₀,
      { simp only [hw₁, zero_lt_one] },
      { exact λ i hi, finset.mem_coe.2 (finset.mem_image_of_mem _ hi) } } },
   { exact Union_subset (λ i, Union_subset convex_hull_mono), },
end

lemma is_linear_map.convex_hull_image {f : E → F} (hf : is_linear_map ℝ f) (s : set E) :
  convex_hull (f '' s) = f '' convex_hull s :=
set.subset.antisymm (convex_hull_min (image_subset _ (subset_convex_hull s)) $
  (convex_convex_hull s).is_linear_image hf)
  (image_subset_iff.2 $ convex_hull_min
    (image_subset_iff.1 $ subset_convex_hull _)
    ((convex_convex_hull _).is_linear_preimage hf))

lemma linear_map.convex_hull_image (f : E →ₗ[ℝ] F) (s : set E) :
  convex_hull (f '' s) = f '' convex_hull s :=
f.is_linear.convex_hull_image s

end convex_hull

/-! ### Simplex -/

section simplex

variables (ι) [fintype ι] {f : ι → ℝ}

/-- Standard simplex in the space of functions `ι → ℝ` is the set
of vectors with non-negative coordinates with total sum `1`. -/
def std_simplex (ι : Type*) [fintype ι] : set (ι → ℝ) :=
{ f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 }

lemma std_simplex_eq_inter :
  std_simplex ι = (⋂ x, {f | 0 ≤ f x}) ∩ {f | ∑ x, f x = 1} :=
by { ext f, simp only [std_simplex, set.mem_inter_eq, set.mem_Inter, set.mem_set_of_eq] }

lemma convex_std_simplex : convex (std_simplex ι) :=
begin
  refine λ f g hf hg a b ha hb hab, ⟨λ x, _, _⟩,
  { apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1] },
  { erw [finset.sum_add_distrib, ← finset.smul_sum, ← finset.smul_sum, hf.2, hg.2,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one],
    exact hab }
end

variable {ι}

lemma ite_eq_mem_std_simplex (i : ι) : (λ j, ite (i = j) (1:ℝ) 0) ∈ std_simplex ι :=
⟨λ j, by simp only; split_ifs; norm_num, by rw [finset.sum_ite_eq, if_pos (finset.mem_univ _)] ⟩

/-- `std_simplex ι` is the convex hull of the canonical basis in `ι → ℝ`. -/
lemma convex_hull_basis_eq_std_simplex :
  convex_hull (range $ λ(i j:ι), if i = j then (1:ℝ) else 0) = std_simplex ι :=
begin
  refine subset.antisymm (convex_hull_min _ (convex_std_simplex ι)) _,
  { rintros _ ⟨i, rfl⟩,
    exact ite_eq_mem_std_simplex i },
  { rintros w ⟨hw₀, hw₁⟩,
    rw [pi_eq_sum_univ w, ← finset.univ.center_mass_eq_of_sum_1 _ hw₁],
    exact finset.univ.center_mass_mem_convex_hull (λ i hi, hw₀ i)
      (hw₁.symm ▸ zero_lt_one) (λ i hi, mem_range_self i) }
end

variable {ι}

/-- Convex hull of a finite set is the image of the standard simplex in `s → ℝ`
under the linear map sending each function `w` to `∑ x in s, w x • x`.

Since we have no sums over finite sets, we use sum over `@finset.univ _ hs.fintype`.
The map is defined in terms of operations on `(s → ℝ) →ₗ[ℝ] ℝ` so that later we will not need
to prove that this map is linear. -/
lemma set.finite.convex_hull_eq_image {s : set E} (hs : finite s) :
  convex_hull s = by haveI := hs.fintype; exact
    (⇑(∑ x : s, (@linear_map.proj ℝ s _ (λ i, ℝ) _ _ x).smul_right x.1)) '' (std_simplex s) :=
begin
  rw [← convex_hull_basis_eq_std_simplex, ← linear_map.convex_hull_image, ← set.range_comp, (∘)],
  apply congr_arg,
  convert subtype.range_coe.symm,
  ext x,
  simp [linear_map.sum_apply, ite_smul, finset.filter_eq]
end

/-- All values of a function `f ∈ std_simplex ι` belong to `[0, 1]`. -/
lemma mem_Icc_of_mem_std_simplex (hf : f ∈ std_simplex ι) (x) :
  f x ∈ I :=
⟨hf.1 x, hf.2 ▸ finset.single_le_sum (λ y hy, hf.1 y) (finset.mem_univ x)⟩

end simplex
