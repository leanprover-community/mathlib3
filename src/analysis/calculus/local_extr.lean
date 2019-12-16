/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import analysis.calculus.deriv

/-! # Local extrema of smooth functions

## Main definitions

* `is_local_min f a` : `f a ≤ f x` in some neighborhood of `a`;
* `is_local_max f a` : `f x ≤ f a` in some neighborhood of `a`;
* `is_local_extr f a` : one of the above.

## Main statements

Rolle's Theorem, Lagrange's and Cauchy's Mean Value Theorems.

TODO:

* if `deriv f` is positive on an interval, then `f` is strictly increasing;
* similarly for negative/nonpositive/nonnegative;
* in particular, if `∀ x, deriv f x = 0`, then `f = const`.
* possibly move some lemmas to other file(s)
-/

universes u v

open filter set
open_locale topological_space classical

section defs

variables {α : Type u} {β : Type v} [topological_space α] [preorder β]
  (f : α → β) (a : α)

/-- `a` is a local minimum of `f` if `f a ≤ f x` in a neighborhood of `a`. -/
def is_local_min : Prop := {x | f a ≤ f x} ∈ 𝓝 a

/-- `a` is a local maximum of `f` if `f x ≤ f a` in a neighborhood of `a`. -/
def is_local_max : Prop := {x | f x ≤ f a} ∈ 𝓝 a

/-- `a` is a local extremum of `f` if it is either a local minimum, or a local maximum. -/
def is_local_extr : Prop := is_local_min f a ∨ is_local_max f a

variables {f a}

lemma is_local_min_const {b : β} : is_local_min (λ _, b) a :=
univ_mem_sets' $ λ _, le_refl _

lemma is_local_max_const {b : β} : is_local_max (λ _, b) a :=
univ_mem_sets' $ λ _, le_refl _

end defs

section ordered_comm_monoid

variables {α : Type u} {G : Type v} [topological_space α] [ordered_comm_monoid G]
  {f g : α → G} {a : α}

lemma is_local_min.add (hf : is_local_min f a) (hg : is_local_min g a) : is_local_min (f + g) a :=
mem_sets_of_superset (inter_mem_sets hf hg) $ λ x ⟨hfx, hgx⟩, add_le_add' hfx hgx

lemma is_local_max.add (hf : is_local_max f a) (hg : is_local_max g a) : is_local_max (f + g) a :=
mem_sets_of_superset (inter_mem_sets hf hg) $ λ x ⟨hfx, hgx⟩, add_le_add' hfx hgx

lemma is_local_min.add_left (hf : is_local_min f a) (b : G) :
  is_local_min (λ x, b + f x) a :=
is_local_min_const.add hf

lemma is_local_min.add_right (hf : is_local_min f a) (b : G) :
  is_local_min (λ x, f x + b) a :=
hf.add is_local_min_const

lemma is_local_max.add_left (hf : is_local_max f a) (b : G) :
  is_local_max (λ x, b + f x) a :=
is_local_max_const.add hf

lemma is_local_max.add_right (hf : is_local_max f a) (b : G) :
  is_local_max (λ x, f x + b) a :=
hf.add is_local_max_const

end ordered_comm_monoid

section ordered_comm_group

variables {α : Type u} {G : Type v} [topological_space α] [ordered_comm_group G]
  {f g : α → G} {a : α}

lemma is_local_min.neg (hf : is_local_min f a) : is_local_max (-f) a :=
mem_sets_of_superset hf $ λ x, neg_le_neg

lemma is_local_max.neg (hf : is_local_max f a) : is_local_min (-f) a :=
mem_sets_of_superset hf $ λ x, neg_le_neg

lemma is_local_min.sub (hf : is_local_min f a) (hg : is_local_max g a) :
  is_local_min (f - g) a :=
hf.add hg.neg

lemma is_local_max.sub (hf : is_local_max f a) (hg : is_local_min g a) :
  is_local_max (f - g) a :=
hf.add hg.neg

end ordered_comm_group

section vector_space

variables {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E}
  {f' : E →L[ℝ] ℝ}

lemma is_local_min.has_fderiv_at_eq_zero (h : is_local_min f a) (hf : has_fderiv_at f f' a) :
  f' = 0 :=
begin
  suffices : ∀ v : E, (0:ℝ) ≤ f' v,
  { ext v,
    exact le_antisymm (by simpa using this (-v)) (this v) },
  refine λ v, ge_of_tendsto at_top_ne_bot (hf.lim_real v) _,
  apply mp_sets (mem_at_top (1:ℝ)),
  have : tendsto (λ b:ℝ, a + b⁻¹ • v) at_top (𝓝 (a + (0:ℝ) • v)),
    from tendsto_const_nhds.add (tendsto_smul tendsto_inverse_at_top_nhds_0 tendsto_const_nhds),
  rw [zero_smul, add_zero] at this,
  apply mem_sets_of_superset (mem_map.1 $ this h),
  simp only [mem_set_of_eq, smul_eq_mul, mem_preimage],
  assume c hfc hc,
  exact mul_nonneg (le_trans zero_le_one hc) (sub_nonneg.2 hfc)
end

/-- The derivative at a local minimum equals zero. -/
lemma is_local_min.fderiv_eq_zero (h : is_local_min f a) : fderiv ℝ f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_fderiv_at_eq_zero hf.has_fderiv_at
else fderiv_zero_of_not_differentiable_at hf

lemma is_local_max.has_fderiv_at_eq_zero (h : is_local_max f a) (hf : has_fderiv_at f f' a) :
  f' = 0 :=
neg_eq_zero.1 $ h.neg.has_fderiv_at_eq_zero hf.neg

lemma is_local_max.fderiv_eq_zero (h : is_local_max f a) : fderiv ℝ f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_fderiv_at_eq_zero hf.has_fderiv_at
else fderiv_zero_of_not_differentiable_at hf

lemma is_local_extr.has_fderiv_at_eq_zero (h : is_local_extr f a) :
  has_fderiv_at f f' a → f' = 0 :=
h.elim is_local_min.has_fderiv_at_eq_zero is_local_max.has_fderiv_at_eq_zero

lemma is_local_extr.fderiv_eq_zero (h : is_local_extr f a) : fderiv ℝ f a = 0 :=
h.elim is_local_min.fderiv_eq_zero is_local_max.fderiv_eq_zero

end vector_space

section real

variables {f : ℝ → ℝ} {f' : ℝ} {a b : ℝ}

lemma is_local_min.has_deriv_at_eq_zero (h : is_local_min f a) (hf : has_deriv_at f f' a) :
  f' = 0 :=
by simpa using continuous_linear_map.ext_iff.1
  (h.has_fderiv_at_eq_zero (has_deriv_at_iff_has_fderiv_at.1 hf)) 1

lemma is_local_min.deriv_eq_zero (h : is_local_min f a) : deriv f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_deriv_at_eq_zero hf.has_deriv_at
else deriv_zero_of_not_differentiable_at hf

lemma is_local_max.has_deriv_at_eq_zero (h : is_local_max f a) (hf : has_deriv_at f f' a) :
  f' = 0 :=
neg_eq_zero.1 $ h.neg.has_deriv_at_eq_zero hf.neg

lemma is_local_max.deriv_eq_zero (h : is_local_max f a) : deriv f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_deriv_at_eq_zero hf.has_deriv_at
else deriv_zero_of_not_differentiable_at hf

lemma is_local_extr.has_deriv_at_eq_zero (h : is_local_extr f a) :
  has_deriv_at f f' a → f' = 0 :=
h.elim is_local_min.has_deriv_at_eq_zero is_local_max.has_deriv_at_eq_zero

lemma is_local_extr.deriv_eq_zero (h : is_local_extr f a) : deriv f a = 0 :=
h.elim is_local_min.deriv_eq_zero is_local_max.deriv_eq_zero

end real

section MVT

variables (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hfc : continuous f) (hfI : f a = f b)

include hab hfc hfI

lemma exists_global_extr_Ioo :
  ∃ c ∈ Ioo a b, (∀ x ∈ Icc a b, f c ≤ f x) ∨ (∀ x ∈ Icc a b, f x ≤ f c) :=
begin
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : ∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f c ≤ f x,
    from exists_forall_le_of_compact_of_continuous f hfc (Icc a b) compact_Icc
      (ne_empty_of_mem $ left_mem_Icc.2 $ le_of_lt hab),
  obtain ⟨C, Cmem, Cge⟩ : ∃ C ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f C,
    from exists_forall_ge_of_compact_of_continuous f hfc (Icc a b) compact_Icc
      (ne_empty_of_mem $ left_mem_Icc.2 $ le_of_lt hab),
  by_cases hc : f c = f a,
  { by_cases hC : f C = f a,
    { have : ∀ x ∈ Icc a b, f x = f a,
        from λ x hx, le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx),
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases dense hab with ⟨c', hc'⟩,
      refine ⟨c', hc', or.inl _⟩,
      assume x hx,
      rw [this x hx, ← hC],
      exact Cge c' ⟨le_of_lt hc'.1, le_of_lt hc'.2⟩ },

    { refine ⟨C, ⟨lt_of_le_of_ne Cmem.1 $ mt _ hC, lt_of_le_of_ne Cmem.2 $ mt _ hC⟩, or.inr Cge⟩,
      exacts [λ h, by rw h, λ h, by rw [h, hfI]] } },
  { refine ⟨c, ⟨lt_of_le_of_ne cmem.1 $ mt _ hc, lt_of_le_of_ne cmem.2 $ mt _ hc⟩, or.inl cle⟩,
      exacts [λ h, by rw h, λ h, by rw [h, hfI]] }
end

lemma exists_local_extr_Ioo : ∃ c ∈ Ioo a b, is_local_extr f c :=
by rcases exists_global_extr_Ioo f hab hfc hfI with ⟨c, cmem, hc | hc⟩; use [c, cmem]; [left,right];
  exact mem_nhds_iff_exists_Ioo_subset.2 ⟨a, b, cmem, λ x hx, hc _ ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩

variable (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x)

include hff'

/-- Rolle's Theorem `has_deriv_at` version -/
lemma exists_has_deriv_at_eq_zero :
  ∃ c ∈ Ioo a b, f' c = 0 :=
let ⟨c, cmem, hc⟩ := exists_local_extr_Ioo f hab hfc hfI in
  ⟨c, cmem, hc.has_deriv_at_eq_zero $ hff' c cmem⟩

omit hfI

/-- Cauchy version of the Mean Value Theorem -/
lemma exists_ratio_has_deriv_at_eq_ratio_slope
  (g g' : ℝ → ℝ) (hgc : continuous g) (hgg' : ∀ x ∈ Ioo a b, has_deriv_at g (g' x) x) :
  ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c :=
begin
  let h := λ x, (g b - g a) * f x - (f b - f a) * g x,
  have hI : h a = h b,
  { simp only [h], ring },
  let h' := λ x, (g b - g a) * f' x - (f b - f a) * g' x,
  have hhh' : ∀ x ∈ Ioo a b, has_deriv_at h (h' x) x,
  { assume x hx,
    convert ((has_deriv_at_const x (g b - g a)).mul (hff' x hx)).sub
      ((has_deriv_at_const x (f b - f a)).mul (hgg' x hx)),
    simp only [h', mul_zero, add_zero] },
  have hhc : continuous h,
    from (continuous_const.mul hfc).sub (continuous_const.mul hgc),
  rcases exists_has_deriv_at_eq_zero h h' hab hhc hI hhh' with ⟨c, cmem, hc⟩,
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩
end

lemma exists_has_deriv_at_eq_slope : ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) :=
begin
  rcases exists_ratio_has_deriv_at_eq_ratio_slope f f' hab hfc hff' id 1 continuous_id (λ x hx, has_deriv_at_id x) with ⟨c, cmem, hc⟩,
  use [c, cmem],
  simp only [id, pi.one_apply, mul_one] at hc,
  rw [← hc, mul_div_cancel_left],
  exact ne_of_gt (sub_pos.2 hab)
end

omit hff'

lemma exists_deriv_eq_zero : ∃ c ∈ Ioo a b, deriv f c = 0 :=
let ⟨c, cmem, hc⟩ := exists_local_extr_Ioo f hab hfc hfI in
  ⟨c, cmem, hc.deriv_eq_zero⟩

lemma exists_ratio_deriv_eq_ratio_slope (hfd : ∀ x ∈ Ioo a b, differentiable_at ℝ f x)
  (g : ℝ → ℝ) (hgc : continuous g) (hgd : ∀ x ∈ Ioo a b, differentiable_at ℝ g x):
  ∃ c ∈ Ioo a b, (g b - g a) * (deriv f c) = (f b - f a) * (deriv g c) :=
exists_ratio_has_deriv_at_eq_ratio_slope f (deriv f) hab hfc
  (λ x hx, (hfd x hx).has_deriv_at) g (deriv g) hgc (λ x hx, (hgd x hx).has_deriv_at)

lemma exists_deriv_eq_slope (hfd : ∀ x ∈ Ioo a b, differentiable_at ℝ f x) :
  ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
exists_has_deriv_at_eq_slope f (deriv f) hab hfc (λ x hx, (hfd x hx).has_deriv_at)

end MVT
