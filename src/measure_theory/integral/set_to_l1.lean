/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
import measure_theory.function.simple_func_dense

/-!
# Extension of a linear function from indicators to L1

Let `T : set α → E →L[ℝ] F` be additive for measurable sets with finite measure, in the sense that
for `s, t` two such sets, `s ∩ t = ∅ → T (s ∪ t) = T s + T t`. `T` is akin to a bilinear map on
`set α × E`, or a linear map on indicator functions.

This file constructs an extension of `T` to integrable simple functions, which are finite sums of
indicators of measurable sets with finite measure, then to integrable functions, which are limits of
integrable simple functions.

The main result is a continuous linear map `(α →₁[μ] E) →L[ℝ] F`. This extension process is used to
define the Bochner integral in the `measure_theory.integral.bochner` file and the conditional
expectation of an integrable function in `measure_theory.function.conditional_expectation`.

## Main Definitions

- `fin_meas_additive μ T`: the property that `T` is additive on measurable sets with finite measure.
  For two such sets, `s ∩ t = ∅ → T (s ∪ t) = T s + T t`.
- `dominated_fin_meas_additive μ T C`: `fin_meas_additive μ T ∧ ∀ s, ∥T s∥ ≤ C * (μ s).to_real`.
  This is the property needed to perform the extension from indicators to L1.
- `set_to_L1 (hT : dominated_fin_meas_additive μ T C) : (α →₁[μ] E) →L[ℝ] F`: the extension of `T`
  from indicators to L1.
- `set_to_fun μ T (hT : dominated_fin_meas_additive μ T C) (f : α → E) : F`: a version of the
  extension which applies to functions (with value 0 if the function is not integrable).

## Implementation notes

The starting object `T : set α → E →L[ℝ] F` matters only through its restriction on measurable sets
with finite measure. Its value on other sets is ignored.

The extension step from integrable simple functions to L1 relies on a `second_countable_topology`
assumption. Without it, we could only extend to `ae_fin_strongly_measurable` functions. (TODO: this
might be worth doing?)

-/

noncomputable theory
open_locale classical topological_space big_operators nnreal ennreal measure_theory pointwise
open set filter topological_space ennreal emetric

local attribute [instance] fact_one_le_one_ennreal

namespace measure_theory

variables {α E F F' G 𝕜 : Type*} {p : ℝ≥0∞}
  [normed_group E] [measurable_space E] [normed_space ℝ E]
  [normed_group F] [normed_space ℝ F]
  [normed_group F'] [normed_space ℝ F']
  [normed_group G] [measurable_space G]
  {m : measurable_space α} {μ : measure α}

local infixr ` →ₛ `:25 := simple_func

open finset

section fin_meas_additive

/-- A set function is `fin_meas_additive` if its value on the union of two disjoint measurable
sets with finite measure is the sum of its values on each set. -/
def fin_meas_additive {β} [add_monoid β] {m : measurable_space α}
  (μ : measure α) (T : set α → β) : Prop :=
∀ s t, measurable_set s → measurable_set t → μ s ≠ ∞ → μ t ≠ ∞ → s ∩ t = ∅ → T (s ∪ t) = T s + T t

namespace fin_meas_additive

variables {β : Type*} [add_comm_monoid β] {T T' : set α → β}

lemma zero : fin_meas_additive μ (0 : set α → β) := λ s t hs ht hμs hμt hst, by simp

lemma add (hT : fin_meas_additive μ T) (hT' : fin_meas_additive μ T') :
  fin_meas_additive μ (T + T') :=
begin
  intros s t hs ht hμs hμt hst,
  simp only [hT s t hs ht hμs hμt hst, hT' s t hs ht hμs hμt hst, pi.add_apply],
  abel,
end

lemma smul [monoid 𝕜] [distrib_mul_action 𝕜 β] (hT : fin_meas_additive μ T) (c : 𝕜) :
  fin_meas_additive μ (λ s, c • (T s)) :=
λ s t hs ht hμs hμt hst, by simp [hT s t hs ht hμs hμt hst]

lemma of_eq_top_imp_eq_top {μ' : measure α}
  (h : ∀ s, measurable_set s → μ s = ∞ → μ' s = ∞) (hT : fin_meas_additive μ T) :
  fin_meas_additive μ' T :=
λ s t hs ht hμ's hμ't hst, hT s t hs ht (mt (h s hs) hμ's) (mt (h t ht) hμ't) hst

lemma of_smul_measure (c : ℝ≥0∞) (hc_ne_top : c ≠ ∞) (hT : fin_meas_additive (c • μ) T) :
  fin_meas_additive μ T :=
begin
  refine of_eq_top_imp_eq_top (λ s hs hμs, _) hT,
  rw [measure.smul_apply, with_top.mul_eq_top_iff] at hμs,
  simp only [hc_ne_top, or_false, ne.def, false_and] at hμs,
  exact hμs.2,
end

lemma smul_measure (c : ℝ≥0∞) (hc_ne_zero : c ≠ 0) (hT : fin_meas_additive μ T) :
  fin_meas_additive (c • μ) T :=
begin
  refine of_eq_top_imp_eq_top (λ s hs hμs, _) hT,
  rw [measure.smul_apply, with_top.mul_eq_top_iff],
  simp only [hc_ne_zero, true_and, ne.def, not_false_iff],
  exact or.inl hμs,
end

lemma smul_measure_iff (c : ℝ≥0∞) (hc_ne_zero : c ≠ 0) (hc_ne_top : c ≠ ∞) :
  fin_meas_additive (c • μ) T ↔ fin_meas_additive μ T :=
⟨λ hT, of_smul_measure c hc_ne_top hT, λ hT, smul_measure c hc_ne_zero hT⟩

lemma map_empty_eq_zero {β} [add_cancel_monoid β] {T : set α → β} (hT : fin_meas_additive μ T) :
  T ∅ = 0 :=
begin
  have h_empty : μ ∅ ≠ ∞, from (measure_empty.le.trans_lt ennreal.coe_lt_top).ne,
  specialize hT ∅ ∅ measurable_set.empty measurable_set.empty h_empty h_empty
    (set.inter_empty ∅),
  rw set.union_empty at hT,
  nth_rewrite 0 ← add_zero (T ∅) at hT,
  exact (add_left_cancel hT).symm,
end

lemma map_Union_fin_meas_set_eq_sum (T : set α → β) (T_empty : T ∅ = 0)
  (h_add : fin_meas_additive μ T)
  {ι} (S : ι → set α) (sι : finset ι) (hS_meas : ∀ i, measurable_set (S i))
  (hSp : ∀ i ∈ sι, μ (S i) ≠ ∞) (h_disj : ∀ i j ∈ sι, i ≠ j → disjoint (S i) (S j)) :
  T (⋃ i ∈ sι, S i) = ∑ i in sι, T (S i) :=
begin
  revert hSp h_disj,
  refine finset.induction_on sι _ _,
  { simp only [finset.not_mem_empty, forall_false_left, Union_false, Union_empty, sum_empty,
    forall_2_true_iff, implies_true_iff, forall_true_left, not_false_iff, T_empty], },
  intros a s has h hps h_disj,
  rw [finset.sum_insert has, ← h],
  swap, { exact λ i hi, hps i (finset.mem_insert_of_mem hi), },
  swap, { exact λ i j hi hj hij,
    h_disj i j (finset.mem_insert_of_mem hi) (finset.mem_insert_of_mem hj) hij, },
  rw ← h_add (S a) (⋃ i ∈ s, S i) (hS_meas a) (measurable_set_bUnion _ (λ i _, hS_meas i))
    (hps a (finset.mem_insert_self a s)),
  { congr, convert finset.supr_insert a s S, },
  { exact ((measure_bUnion_finset_le _ _).trans_lt $
      ennreal.sum_lt_top $ λ i hi, hps i $ finset.mem_insert_of_mem hi).ne, },
  { simp_rw set.inter_Union,
    refine Union_eq_empty.mpr (λ i, Union_eq_empty.mpr (λ hi, _)),
    rw ← set.disjoint_iff_inter_eq_empty,
    refine h_disj a i (finset.mem_insert_self a s) (finset.mem_insert_of_mem hi) (λ hai, _),
    rw ← hai at hi,
    exact has hi, },
end

end fin_meas_additive

/-- A `fin_meas_additive` set function whose norm on every set is less than the measure of the
set (up to a multiplicative constant). -/
def dominated_fin_meas_additive {β} [semi_normed_group β] {m : measurable_space α}
  (μ : measure α) (T : set α → β) (C : ℝ) : Prop :=
fin_meas_additive μ T ∧ ∀ s, measurable_set s → μ s < ∞ → ∥T s∥ ≤ C * (μ s).to_real

namespace dominated_fin_meas_additive

variables {β : Type*} [semi_normed_group β] {T T' : set α → β} {C C' : ℝ}

lemma zero {m : measurable_space α} (μ : measure α) (hC : 0 ≤ C) :
  dominated_fin_meas_additive μ (0 : set α → β) C :=
begin
  refine ⟨fin_meas_additive.zero, λ s hs hμs, _⟩,
  rw [pi.zero_apply, norm_zero],
  exact mul_nonneg hC to_real_nonneg,
end

lemma eq_zero_of_measure_zero {β : Type*} [normed_group β] {T : set α → β} {C : ℝ}
  (hT : dominated_fin_meas_additive μ T C) {s : set α}
  (hs : measurable_set s) (hs_zero : μ s = 0) :
  T s = 0 :=
begin
  refine norm_eq_zero.mp _,
  refine ((hT.2 s hs (by simp [hs_zero])).trans (le_of_eq _)).antisymm (norm_nonneg _),
  rw [hs_zero, ennreal.zero_to_real, mul_zero],
end

lemma eq_zero {β : Type*} [normed_group β] {T : set α → β} {C : ℝ}
  {m : measurable_space α} (hT : dominated_fin_meas_additive (0 : measure α) T C)
  {s : set α} (hs : measurable_set s) :
  T s = 0 :=
eq_zero_of_measure_zero hT hs (by simp only [measure.coe_zero, pi.zero_apply])

lemma add (hT : dominated_fin_meas_additive μ T C) (hT' : dominated_fin_meas_additive μ T' C') :
  dominated_fin_meas_additive μ (T + T') (C + C') :=
begin
  refine ⟨hT.1.add hT'.1, λ s hs hμs, _⟩,
  rw [pi.add_apply, add_mul],
  exact (norm_add_le _ _).trans (add_le_add (hT.2 s hs hμs) (hT'.2 s hs hμs)),
end

lemma smul [normed_field 𝕜] [semi_normed_space 𝕜 β] (hT : dominated_fin_meas_additive μ T C)
  (c : 𝕜) :
  dominated_fin_meas_additive μ (λ s, c • (T s)) (∥c∥ * C) :=
begin
  refine ⟨hT.1.smul c, λ s hs hμs, _⟩,
  dsimp only,
  rw [norm_smul, mul_assoc],
  exact mul_le_mul le_rfl (hT.2 s hs hμs) (norm_nonneg _) (norm_nonneg _),
end

lemma of_measure_le {μ' : measure α} (h : μ ≤ μ') (hT : dominated_fin_meas_additive μ T C)
  (hC : 0 ≤ C) :
  dominated_fin_meas_additive μ' T C :=
begin
  have h' : ∀ s, measurable_set s → μ s = ∞ → μ' s = ∞,
  { intros s hs hμs, rw [eq_top_iff, ← hμs], exact h s hs, },
  refine ⟨hT.1.of_eq_top_imp_eq_top h', λ s hs hμ's, _⟩,
  have hμs : μ s < ∞, from (h s hs).trans_lt hμ's,
  refine (hT.2 s hs hμs).trans (mul_le_mul le_rfl _ ennreal.to_real_nonneg hC),
  rw to_real_le_to_real hμs.ne hμ's.ne,
  exact h s hs,
end

lemma add_measure_right {m : measurable_space α}
  (μ ν : measure α) (hT : dominated_fin_meas_additive μ T C) (hC : 0 ≤ C) :
  dominated_fin_meas_additive (μ + ν) T C :=
 of_measure_le (measure.le_add_right le_rfl) hT hC

lemma add_measure_left {m : measurable_space α}
  (μ ν : measure α) (hT : dominated_fin_meas_additive ν T C) (hC : 0 ≤ C) :
  dominated_fin_meas_additive (μ + ν) T C :=
 of_measure_le (measure.le_add_left le_rfl) hT hC

lemma of_smul_measure (c : ℝ≥0∞) (hc_ne_top : c ≠ ∞)
  (hT : dominated_fin_meas_additive (c • μ) T C) :
  dominated_fin_meas_additive μ T (c.to_real * C) :=
begin
  have h : ∀ s, measurable_set s → c • μ s = ∞ → μ s = ∞,
  { intros s hs hcμs,
    simp only [hc_ne_top, algebra.id.smul_eq_mul, with_top.mul_eq_top_iff, or_false, ne.def,
      false_and] at hcμs,
    exact hcμs.2, },
  refine ⟨hT.1.of_eq_top_imp_eq_top h, λ s hs hμs, _⟩,
  have hcμs : c • μ s ≠ ∞, from mt (h s hs) hμs.ne,
  rw smul_eq_mul at hcμs,
  simp_rw [dominated_fin_meas_additive, measure.smul_apply, to_real_mul] at hT,
  refine (hT.2 s hs hcμs.lt_top).trans (le_of_eq _),
  ring,
end

lemma of_measure_le_smul {μ' : measure α} (c : ℝ≥0∞) (hc : c ≠ ∞) (h : μ ≤ c • μ')
  (hT : dominated_fin_meas_additive μ T C) (hC : 0 ≤ C) :
  dominated_fin_meas_additive μ' T (c.to_real * C) :=
(hT.of_measure_le h hC).of_smul_measure c hc

end dominated_fin_meas_additive

end fin_meas_additive

namespace simple_func

/-- Extend `set α → (F →L[ℝ] F')` to `(α →ₛ F) → F'`. -/
def set_to_simple_func {m : measurable_space α} (T : set α → F →L[ℝ] F') (f : α →ₛ F) : F' :=
∑ x in f.range, T (f ⁻¹' {x}) x

@[simp] lemma set_to_simple_func_zero {m : measurable_space α} (f : α →ₛ F) :
  set_to_simple_func (0 : set α → F →L[ℝ] F') f = 0 :=
by simp [set_to_simple_func]

@[simp] lemma set_to_simple_func_zero_apply {m : measurable_space α} (T : set α → F →L[ℝ] F') :
  set_to_simple_func T (0 : α →ₛ F) = 0 :=
by casesI is_empty_or_nonempty α; simp [set_to_simple_func]

lemma set_to_simple_func_eq_sum_filter {m : measurable_space α}
  (T : set α → F →L[ℝ] F') (f : α →ₛ F) :
  set_to_simple_func T f = ∑ x in f.range.filter (λ x, x ≠ 0), (T (f ⁻¹' {x})) x :=
begin
  symmetry,
  refine sum_filter_of_ne (λ x hx, mt (λ hx0, _)),
  rw hx0,
  exact continuous_linear_map.map_zero _,
end

lemma set_to_simple_func_mono {G} [normed_linear_ordered_group G] [normed_space ℝ G]
  {m : measurable_space α}
  (T : set α → F →L[ℝ] G) (T' : set α → F →L[ℝ] G) (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →ₛ F) :
  set_to_simple_func T f ≤ set_to_simple_func T' f :=
by { simp_rw set_to_simple_func, exact sum_le_sum (λ i hi, hTT' _ i), }

lemma map_set_to_simple_func (T : set α → F →L[ℝ] F') (h_add : fin_meas_additive μ T)
  {f : α →ₛ G} (hf : integrable f μ) {g : G → F} (hg : g 0 = 0) :
  (f.map g).set_to_simple_func T = ∑ x in f.range, T (f ⁻¹' {x}) (g x) :=
begin
  have T_empty : T ∅ = 0, from h_add.map_empty_eq_zero,
  have hfp : ∀ x ∈ f.range, x ≠ 0 → μ (f ⁻¹' {x}) ≠ ∞,
    from λ x hx hx0, (measure_preimage_lt_top_of_integrable f hf hx0).ne,
  simp only [set_to_simple_func, range_map],
  refine finset.sum_image' _ (assume b hb, _),
  rcases mem_range.1 hb with ⟨a, rfl⟩,
  by_cases h0 : g (f a) = 0,
  { simp_rw h0,
    rw [continuous_linear_map.map_zero, finset.sum_eq_zero (λ x hx, _)],
    rw mem_filter at hx,
    rw [hx.2, continuous_linear_map.map_zero], },
  have h_left_eq : T ((map g f) ⁻¹' {g (f a)}) (g (f a))
    = T (f ⁻¹' ↑(f.range.filter (λ b, g b = g (f a)))) (g (f a)),
  { congr, rw map_preimage_singleton, },
  rw h_left_eq,
  have h_left_eq' : T (f ⁻¹' ↑(filter (λ (b : G), g b = g (f a)) f.range)) (g (f a))
    = T (⋃ y ∈ (filter (λ (b : G), g b = g (f a)) f.range), f ⁻¹' {y}) (g (f a)),
  { congr, rw ← finset.set_bUnion_preimage_singleton, },
  rw h_left_eq',
  rw h_add.map_Union_fin_meas_set_eq_sum T T_empty,
  { simp only [filter_congr_decidable, sum_apply, continuous_linear_map.coe_sum'],
    refine finset.sum_congr rfl (λ x hx, _),
    rw mem_filter at hx,
    rw hx.2, },
  { exact λ i, measurable_set_fiber _ _, },
  { intros i hi,
    rw mem_filter at hi,
    refine hfp i hi.1 (λ hi0, _),
    rw [hi0, hg] at hi,
    exact h0 hi.2.symm, },
  { intros i j hi hj hij,
    rw set.disjoint_iff,
    intros x hx,
    rw [set.mem_inter_iff, set.mem_preimage, set.mem_preimage, set.mem_singleton_iff,
      set.mem_singleton_iff] at hx,
    rw [← hx.1, ← hx.2] at hij,
    exact absurd rfl hij, },
end

lemma set_to_simple_func_congr' (T : set α → E →L[ℝ] F) (h_add : fin_meas_additive μ T)
  {f g : α →ₛ E} (hf : integrable f μ) (hg : integrable g μ)
  (h : ∀ x y, x ≠ y → T ((f ⁻¹' {x}) ∩ (g ⁻¹' {y})) = 0) :
  f.set_to_simple_func T = g.set_to_simple_func T :=
show ((pair f g).map prod.fst).set_to_simple_func T
  = ((pair f g).map prod.snd).set_to_simple_func T, from
begin
  have h_pair : integrable (f.pair g) μ, from integrable_pair hf hg,
  rw map_set_to_simple_func T h_add h_pair prod.fst_zero,
  rw map_set_to_simple_func T h_add h_pair prod.snd_zero,
  refine finset.sum_congr rfl (λ p hp, _),
  rcases mem_range.1 hp with ⟨a, rfl⟩,
  by_cases eq : f a = g a,
  { dsimp only [pair_apply], rw eq },
  { have : T ((pair f g) ⁻¹' {(f a, g a)}) = 0,
    { have h_eq : T (⇑(f.pair g) ⁻¹' {(f a, g a)}) = T ((f ⁻¹' {f a}) ∩ (g ⁻¹' {g a})),
      { congr, rw pair_preimage_singleton f g, },
      rw h_eq,
      exact h (f a) (g a) eq, },
    simp only [this, continuous_linear_map.zero_apply, pair_apply], },
end

lemma set_to_simple_func_congr (T : set α → (E →L[ℝ] F))
  (h_zero : ∀ s, measurable_set s → μ s = 0 → T s = 0) (h_add : fin_meas_additive μ T)
  {f g : α →ₛ E} (hf : integrable f μ) (h : f =ᵐ[μ] g) :
  f.set_to_simple_func T = g.set_to_simple_func T :=
begin
  refine set_to_simple_func_congr' T h_add hf ((integrable_congr h).mp hf) _,
  refine λ x y hxy, h_zero _ ((measurable_set_fiber f x).inter (measurable_set_fiber g y)) _,
  rw [eventually_eq, ae_iff] at h,
  refine measure_mono_null (λ z, _) h,
  simp_rw [set.mem_inter_iff, set.mem_set_of_eq, set.mem_preimage, set.mem_singleton_iff],
  intro h,
  rwa [h.1, h.2],
end

lemma set_to_simple_func_add_left {m : measurable_space α} (T T' : set α → F →L[ℝ] F')
  {f : α →ₛ F} :
  set_to_simple_func (T + T') f = set_to_simple_func T f + set_to_simple_func T' f :=
begin
  simp_rw [set_to_simple_func, pi.add_apply],
  push_cast,
  simp_rw [pi.add_apply, sum_add_distrib],
end

lemma set_to_simple_func_add_left' (T T' T'' : set α → E →L[ℝ] F)
  (h_add : ∀ s, measurable_set s → μ s ≠ ∞ → T'' s = T s + T' s) {f : α →ₛ E}
  (hf : integrable f μ) :
  set_to_simple_func (T'') f = set_to_simple_func T f + set_to_simple_func T' f :=
begin
  simp_rw [set_to_simple_func_eq_sum_filter],
  suffices : ∀ x ∈ filter (λ (x : E), x ≠ 0) f.range,
    T'' (f ⁻¹' {x}) = T (f ⁻¹' {x}) + T' (f ⁻¹' {x}),
  { rw ← sum_add_distrib,
    refine finset.sum_congr rfl (λ x hx, _),
    rw this x hx,
    push_cast,
    rw pi.add_apply, },
  intros x hx,
  refine h_add (f ⁻¹' {x}) (measurable_set_preimage _ _)
    (measure_preimage_lt_top_of_integrable _ hf _).ne,
  rw mem_filter at hx,
  exact hx.2,
end

lemma set_to_simple_func_add (T : set α → E →L[ℝ] F) (h_add : fin_meas_additive μ T)
  {f g : α →ₛ E} (hf : integrable f μ) (hg : integrable g μ) :
  set_to_simple_func T (f + g) = set_to_simple_func T f + set_to_simple_func T g :=
have hp_pair : integrable (f.pair g) μ, from integrable_pair hf hg,
calc set_to_simple_func T (f + g) = ∑ x in (pair f g).range,
       T ((pair f g) ⁻¹' {x}) (x.fst + x.snd) :
  by { rw [add_eq_map₂, map_set_to_simple_func T h_add hp_pair], simp, }
... = ∑ x in (pair f g).range, (T ((pair f g) ⁻¹' {x}) x.fst + T ((pair f g) ⁻¹' {x}) x.snd) :
  finset.sum_congr rfl $ assume a ha, continuous_linear_map.map_add _ _ _
... = ∑ x in (pair f g).range, T ((pair f g) ⁻¹' {x}) x.fst +
      ∑ x in (pair f g).range, T ((pair f g) ⁻¹' {x}) x.snd :
  by rw finset.sum_add_distrib
... = ((pair f g).map prod.fst).set_to_simple_func T
    + ((pair f g).map prod.snd).set_to_simple_func T :
  by rw [map_set_to_simple_func T h_add hp_pair prod.snd_zero,
    map_set_to_simple_func T h_add hp_pair prod.fst_zero]

lemma set_to_simple_func_neg (T : set α → E →L[ℝ] F) (h_add : fin_meas_additive μ T)
  {f : α →ₛ E} (hf : integrable f μ) :
  set_to_simple_func T (-f) = - set_to_simple_func T f :=
calc set_to_simple_func T (-f) = set_to_simple_func T (f.map (has_neg.neg)) : rfl
  ... = - set_to_simple_func T f :
  begin
    rw [map_set_to_simple_func T h_add hf neg_zero, set_to_simple_func,
      ← sum_neg_distrib],
    exact finset.sum_congr rfl (λ x h, continuous_linear_map.map_neg _ _),
  end

lemma set_to_simple_func_sub (T : set α → E →L[ℝ] F) (h_add : fin_meas_additive μ T)
  {f g : α →ₛ E} (hf : integrable f μ) (hg : integrable g μ) :
  set_to_simple_func T (f - g) = set_to_simple_func T f - set_to_simple_func T g :=
begin
  rw [sub_eq_add_neg, set_to_simple_func_add T h_add hf,
    set_to_simple_func_neg T h_add hg, sub_eq_add_neg],
  rw integrable_iff at hg ⊢,
  intros x hx_ne,
  change μ ((has_neg.neg ∘ g) ⁻¹' {x}) < ∞,
  rw [preimage_comp, neg_preimage, neg_singleton],
  refine hg (-x) _,
  simp [hx_ne],
end

lemma set_to_simple_func_smul_real (T : set α → E →L[ℝ] F) (h_add : fin_meas_additive μ T)
  (c : ℝ) {f : α →ₛ E} (hf : integrable f μ) :
  set_to_simple_func T (c • f) = c • set_to_simple_func T f :=
calc set_to_simple_func T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) :
  by { rw [smul_eq_map c f, map_set_to_simple_func T h_add hf], rw smul_zero, }
... = ∑ x in f.range, c • (T (f ⁻¹' {x}) x) :
  finset.sum_congr rfl $ λ b hb, by { rw continuous_linear_map.map_smul (T (f ⁻¹' {b})) c b, }
... = c • set_to_simple_func T f :
by simp only [set_to_simple_func, smul_sum, smul_smul, mul_comm]

lemma set_to_simple_func_smul {E} [measurable_space E] [normed_group E] [normed_field 𝕜]
  [normed_space 𝕜 E] [normed_space ℝ E] [normed_space 𝕜 F] (T : set α → E →L[ℝ] F)
  (h_add : fin_meas_additive μ T) (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x)
  (c : 𝕜) {f : α →ₛ E} (hf : integrable f μ) :
  set_to_simple_func T (c • f) = c • set_to_simple_func T f :=
calc set_to_simple_func T (c • f) = ∑ x in f.range, T (f ⁻¹' {x}) (c • x) :
  by { rw [smul_eq_map c f, map_set_to_simple_func T h_add hf],
    rw smul_zero, }
... = ∑ x in f.range, c • (T (f ⁻¹' {x}) x) : finset.sum_congr rfl $ λ b hb, by { rw h_smul, }
... = c • set_to_simple_func T f : by simp only [set_to_simple_func, smul_sum, smul_smul, mul_comm]

lemma norm_set_to_simple_func_le_sum_op_norm {m : measurable_space α}
  (T : set α → F' →L[ℝ] F) (f : α →ₛ F') :
  ∥f.set_to_simple_func T∥ ≤ ∑ x in f.range, ∥T (f ⁻¹' {x})∥ * ∥x∥ :=
calc ∥∑ x in f.range, T (f ⁻¹' {x}) x∥
    ≤ ∑ x in f.range, ∥T (f ⁻¹' {x}) x∥ : norm_sum_le _ _
... ≤ ∑ x in f.range, ∥T (f ⁻¹' {x})∥ * ∥x∥ :
  by { refine finset.sum_le_sum (λb hb, _), simp_rw continuous_linear_map.le_op_norm, }

lemma norm_set_to_simple_func_le_sum_mul_norm_of_integrable (T : set α → E →L[ℝ] F') {C : ℝ}
  (hT_norm : ∀ s, measurable_set s → μ s < ∞ → ∥T s∥ ≤ C * (μ s).to_real) (f : α →ₛ E)
  (hf : integrable f μ) :
  ∥f.set_to_simple_func T∥ ≤ C * ∑ x in f.range, (μ (f ⁻¹' {x})).to_real * ∥x∥ :=
calc ∥f.set_to_simple_func T∥
    ≤ ∑ x in f.range, ∥T (f ⁻¹' {x})∥ * ∥x∥ : norm_set_to_simple_func_le_sum_op_norm T f
... ≤ ∑ x in f.range, C * (μ (f ⁻¹' {x})).to_real * ∥x∥ :
  begin
    refine finset.sum_le_sum (λ b hb, _),
    by_cases hb : ∥b∥ = 0,
    { rw hb, simp, },
    rw _root_.mul_le_mul_right _,
    { refine hT_norm _ (simple_func.measurable_set_fiber _ _)
        (simple_func.measure_preimage_lt_top_of_integrable _ hf _),
      rwa norm_eq_zero at hb, },
    { exact lt_of_le_of_ne (norm_nonneg _) (ne.symm hb), },
  end
... ≤ C * ∑ x in f.range, (μ (f ⁻¹' {x})).to_real * ∥x∥ : by simp_rw [mul_sum, ← mul_assoc]

lemma set_to_simple_func_indicator (T : set α → F →L[ℝ] F') (hT_empty : T ∅ = 0)
  {m : measurable_space α} {s : set α} (hs : measurable_set s) (x : F) :
  simple_func.set_to_simple_func T
    (simple_func.piecewise s hs (simple_func.const α x) (simple_func.const α 0))
  = T s x :=
begin
  by_cases hs_empty : s = ∅,
  { simp only [hs_empty, hT_empty, continuous_linear_map.zero_apply, piecewise_empty, const_zero,
    set_to_simple_func_zero_apply], },
  by_cases hs_univ : s = univ,
  { casesI hα : is_empty_or_nonempty α,
    { refine absurd _ hs_empty,
      haveI : subsingleton (set α), by { unfold set, apply_instance, },
      exact subsingleton.elim s ∅, },
    simp [hs_univ, set_to_simple_func], },
  simp_rw set_to_simple_func,
  rw [← ne.def, set.ne_empty_iff_nonempty] at hs_empty,
  rw range_indicator hs hs_empty hs_univ,
  by_cases hx0 : x = 0,
  { simp_rw hx0, simp, },
  rw sum_insert,
  swap, { rw finset.mem_singleton, exact hx0, },
  rw [sum_singleton, (T _).map_zero, add_zero],
  congr,
  simp only [coe_piecewise, piecewise_eq_indicator, coe_const, pi.const_zero,
    piecewise_eq_indicator],
  rw [indicator_preimage, preimage_const_of_mem],
  swap, { exact set.mem_singleton x, },
  rw [← pi.const_zero, preimage_const_of_not_mem],
  swap, { rw set.mem_singleton_iff, exact ne.symm hx0, },
  simp,
end

end simple_func

namespace L1

open ae_eq_fun Lp.simple_func Lp

variables {α E μ}

namespace simple_func

lemma norm_eq_sum_mul [second_countable_topology G] [borel_space G] (f : α →₁ₛ[μ] G) :
  ∥f∥ = ∑ x in (to_simple_func f).range, (μ ((to_simple_func f) ⁻¹' {x})).to_real * ∥x∥ :=
begin
  rw [norm_to_simple_func, snorm_one_eq_lintegral_nnnorm],
  have h_eq := simple_func.map_apply (λ x, (nnnorm x : ℝ≥0∞)) (to_simple_func f),
  dsimp only at h_eq,
  simp_rw ← h_eq,
  rw [simple_func.lintegral_eq_lintegral, simple_func.map_lintegral, ennreal.to_real_sum],
  { congr,
    ext1 x,
    rw [ennreal.to_real_mul, mul_comm, ← of_real_norm_eq_coe_nnnorm,
      ennreal.to_real_of_real (norm_nonneg _)], },
  { intros x hx,
    by_cases hx0 : x = 0,
    { rw hx0, simp, },
    { exact ennreal.mul_ne_top ennreal.coe_ne_top
        (simple_func.measure_preimage_lt_top_of_integrable _ (simple_func.integrable f) hx0).ne } }
end

section set_to_L1s

variables [second_countable_topology E] [borel_space E] [normed_field 𝕜] [normed_space 𝕜 E]

local attribute [instance] Lp.simple_func.module
local attribute [instance] Lp.simple_func.normed_space

/-- Extend `set α → (E →L[ℝ] F')` to `(α →₁ₛ[μ] E) → F'`. -/
def set_to_L1s (T : set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) : F :=
(to_simple_func f).set_to_simple_func T

lemma set_to_L1s_eq_set_to_simple_func (T : set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) :
  set_to_L1s T f = (to_simple_func f).set_to_simple_func T :=
rfl

lemma set_to_L1s_congr (T : set α → E →L[ℝ] F) (h_zero : ∀ s, measurable_set s → μ s = 0 → T s = 0)
  (h_add : fin_meas_additive μ T)
  {f g : α →₁ₛ[μ] E} (h : to_simple_func f =ᵐ[μ] to_simple_func g) :
  set_to_L1s T f = set_to_L1s T g :=
simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable f) h

lemma set_to_L1s_add (T : set α → E →L[ℝ] F) (h_zero : ∀ s, measurable_set s → μ s = 0 → T s = 0)
  (h_add : fin_meas_additive μ T) (f g : α →₁ₛ[μ] E) :
  set_to_L1s T (f + g) = set_to_L1s T f + set_to_L1s T g :=
begin
  simp_rw set_to_L1s,
  rw ← simple_func.set_to_simple_func_add T h_add
    (simple_func.integrable f) (simple_func.integrable g),
  exact simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable _)
    (add_to_simple_func f g),
end

lemma set_to_L1s_smul_real (T : set α → E →L[ℝ] F)
  (h_zero : ∀ s, measurable_set s → μ s = 0 → T s = 0) (h_add : fin_meas_additive μ T)
  (c : ℝ) (f : α →₁ₛ[μ] E) :
  set_to_L1s T (c • f) = c • set_to_L1s T f :=
begin
  simp_rw set_to_L1s,
  rw ← simple_func.set_to_simple_func_smul_real T h_add c (simple_func.integrable f),
  refine simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable _) _,
  exact smul_to_simple_func c f,
end

lemma set_to_L1s_smul {E} [normed_group E] [measurable_space E] [normed_space ℝ E]
  [normed_space 𝕜 E] [second_countable_topology E] [borel_space E] [normed_space 𝕜 F]
  [measurable_space 𝕜] [opens_measurable_space 𝕜]
  (T : set α → E →L[ℝ] F) (h_zero : ∀ s, measurable_set s → μ s = 0 → T s = 0)
  (h_add : fin_meas_additive μ T)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) (f : α →₁ₛ[μ] E) :
  set_to_L1s T (c • f) = c • set_to_L1s T f :=
begin
  simp_rw set_to_L1s,
  rw ← simple_func.set_to_simple_func_smul T h_add h_smul c (simple_func.integrable f),
  refine simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable _) _,
  exact smul_to_simple_func c f,
end

lemma norm_set_to_L1s_le (T : set α → E →L[ℝ] F) {C : ℝ}
  (hT_norm : ∀ s, measurable_set s → μ s < ∞ → ∥T s∥ ≤ C * (μ s).to_real) (f : α →₁ₛ[μ] E) :
  ∥set_to_L1s T f∥ ≤ C * ∥f∥ :=
begin
  rw [set_to_L1s, norm_eq_sum_mul f],
  exact simple_func.norm_set_to_simple_func_le_sum_mul_norm_of_integrable T hT_norm _
    (simple_func.integrable f),
end

lemma set_to_L1s_indicator_const {T : set α → E →L[ℝ] F} {C : ℝ} {s : set α}
  (hT : dominated_fin_meas_additive μ T C) (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : E) :
  set_to_L1s T (simple_func.indicator_const 1 hs hμs x) = T s x :=
begin
  have h_empty : T ∅ = 0, from hT.eq_zero_of_measure_zero measurable_set.empty measure_empty,
  rw set_to_L1s_eq_set_to_simple_func,
  refine eq.trans _ (simple_func.set_to_simple_func_indicator T h_empty hs x),
  refine simple_func.set_to_simple_func_congr T (λ _, hT.eq_zero_of_measure_zero) hT.1
    (simple_func.integrable _) _,
  exact Lp.simple_func.to_simple_func_indicator_const hs hμs x,
end

variables [normed_space 𝕜 F] [measurable_space 𝕜] [opens_measurable_space 𝕜]

variables (α E μ 𝕜)
/-- Extend `set α → E →L[ℝ] F` to `(α →₁ₛ[μ] E) →L[𝕜] F`. -/
def set_to_L1s_clm' {T : set α → E →L[ℝ] F} {C : ℝ} (hT : dominated_fin_meas_additive μ T C)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) :
  (α →₁ₛ[μ] E) →L[𝕜] F :=
linear_map.mk_continuous ⟨set_to_L1s T, set_to_L1s_add T (λ _, hT.eq_zero_of_measure_zero) hT.1,
  set_to_L1s_smul T (λ _, hT.eq_zero_of_measure_zero) hT.1 h_smul⟩ C
  (λ f, norm_set_to_L1s_le T hT.2 f)

/-- Extend `set α → E →L[ℝ] F` to `(α →₁ₛ[μ] E) →L[ℝ] F`. -/
def set_to_L1s_clm {T : set α → E →L[ℝ] F} {C : ℝ} (hT : dominated_fin_meas_additive μ T C) :
  (α →₁ₛ[μ] E) →L[ℝ] F :=
linear_map.mk_continuous ⟨set_to_L1s T, set_to_L1s_add T (λ _, hT.eq_zero_of_measure_zero) hT.1,
  set_to_L1s_smul_real T (λ _, hT.eq_zero_of_measure_zero) hT.1⟩ C
  (λ f, norm_set_to_L1s_le T hT.2 f)

variables {α E μ 𝕜}

lemma norm_set_to_L1s_clm_le {T : set α → E →L[ℝ] F} {C : ℝ}
  (hT : dominated_fin_meas_additive μ T C) (hC : 0 ≤ C) :
  ∥set_to_L1s_clm α E μ hT∥ ≤ C :=
linear_map.mk_continuous_norm_le _ hC _

lemma norm_set_to_L1s_clm_le' {T : set α → E →L[ℝ] F} {C : ℝ}
  (hT : dominated_fin_meas_additive μ T C) :
  ∥set_to_L1s_clm α E μ hT∥ ≤ max C 0 :=
linear_map.mk_continuous_norm_le' _ _

end set_to_L1s

end simple_func

open simple_func

section set_to_L1

local attribute [instance] Lp.simple_func.module
local attribute [instance] Lp.simple_func.normed_space

variables (𝕜) [nondiscrete_normed_field 𝕜] [measurable_space 𝕜] [opens_measurable_space 𝕜]
  [second_countable_topology E] [borel_space E] [normed_space 𝕜 E]
  [normed_space 𝕜 F] [complete_space F]
  {T : set α → E →L[ℝ] F} {C : ℝ}

/-- Extend `set α → (E →L[ℝ] F)` to `(α →₁[μ] E) →L[𝕜] F`. -/
def set_to_L1' (hT : dominated_fin_meas_additive μ T C)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) :
  (α →₁[μ] E) →L[𝕜] F :=
(set_to_L1s_clm' α E 𝕜 μ hT h_smul).extend
  (coe_to_Lp α E 𝕜) (simple_func.dense_range one_ne_top) simple_func.uniform_inducing

variables {𝕜}

/-- Extend `set α → E →L[ℝ] F` to `(α →₁[μ] E) →L[ℝ] F`. -/
def set_to_L1 (hT : dominated_fin_meas_additive μ T C) : (α →₁[μ] E) →L[ℝ] F :=
(set_to_L1s_clm α E μ hT).extend
  (coe_to_Lp α E ℝ) (simple_func.dense_range one_ne_top) simple_func.uniform_inducing

lemma set_to_L1_eq_set_to_L1s_clm (hT : dominated_fin_meas_additive μ T C) (f : α →₁ₛ[μ] E) :
  set_to_L1 hT f = set_to_L1s_clm α E μ hT f :=
uniformly_extend_of_ind simple_func.uniform_inducing (simple_func.dense_range one_ne_top)
  (set_to_L1s_clm α E μ hT).uniform_continuous _

lemma set_to_L1_eq_set_to_L1' (hT : dominated_fin_meas_additive μ T C)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : α →₁[μ] E) :
  set_to_L1 hT f = set_to_L1' 𝕜 hT h_smul f :=
rfl

lemma set_to_L1_smul (hT : dominated_fin_meas_additive μ T C)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) (f : α →₁[μ] E) :
  set_to_L1 hT (c • f) = c • set_to_L1 hT f :=
begin
  rw [set_to_L1_eq_set_to_L1' hT h_smul, set_to_L1_eq_set_to_L1' hT h_smul],
  exact continuous_linear_map.map_smul _ _ _,
end

lemma set_to_L1_indicator_const_Lp (hT : dominated_fin_meas_additive μ T C) {s : set α}
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : E) :
  set_to_L1 hT (indicator_const_Lp 1 hs hμs x) = T s x :=
begin
  rw [← Lp.simple_func.coe_indicator_const hs hμs x, set_to_L1_eq_set_to_L1s_clm],
  exact set_to_L1s_indicator_const hT hs hμs x,
end

lemma norm_set_to_L1_le_norm_set_to_L1s_clm (hT : dominated_fin_meas_additive μ T C) :
  ∥set_to_L1 hT∥ ≤ ∥set_to_L1s_clm α E μ hT∥ :=
calc ∥set_to_L1 hT∥
    ≤ (1 : ℝ≥0) * ∥set_to_L1s_clm α E μ hT∥ : begin
      refine continuous_linear_map.op_norm_extend_le (set_to_L1s_clm α E μ hT) (coe_to_Lp α E ℝ)
        (simple_func.dense_range one_ne_top) (λ x, le_of_eq _),
      rw [nnreal.coe_one, one_mul],
      refl,
    end
... = ∥set_to_L1s_clm α E μ hT∥ : by rw [nnreal.coe_one, one_mul]

lemma norm_set_to_L1_le_mul_norm (hT : dominated_fin_meas_additive μ T C) (hC : 0 ≤ C)
  (f : α →₁[μ] E) :
  ∥set_to_L1 hT f∥ ≤ C * ∥f∥ :=
calc ∥set_to_L1 hT f∥
    ≤ ∥set_to_L1s_clm α E μ hT∥ * ∥f∥ :
  continuous_linear_map.le_of_op_norm_le _ (norm_set_to_L1_le_norm_set_to_L1s_clm hT) _
... ≤ C * ∥f∥ : mul_le_mul (norm_set_to_L1s_clm_le hT hC) le_rfl (norm_nonneg _) hC

lemma norm_set_to_L1_le_mul_norm' (hT : dominated_fin_meas_additive μ T C) (f : α →₁[μ] E) :
  ∥set_to_L1 hT f∥ ≤ max C 0 * ∥f∥ :=
calc ∥set_to_L1 hT f∥
    ≤ ∥set_to_L1s_clm α E μ hT∥ * ∥f∥ :
  continuous_linear_map.le_of_op_norm_le _ (norm_set_to_L1_le_norm_set_to_L1s_clm hT) _
... ≤ max C 0 * ∥f∥ :
  mul_le_mul (norm_set_to_L1s_clm_le' hT) le_rfl (norm_nonneg _) (le_max_right _ _)

lemma norm_set_to_L1_le (hT : dominated_fin_meas_additive μ T C) (hC : 0 ≤ C) :
  ∥set_to_L1 hT∥ ≤ C :=
continuous_linear_map.op_norm_le_bound _ hC (norm_set_to_L1_le_mul_norm hT hC)

lemma norm_set_to_L1_le' (hT : dominated_fin_meas_additive μ T C) :
  ∥set_to_L1 hT∥ ≤ max C 0 :=
continuous_linear_map.op_norm_le_bound _ (le_max_right _ _) (norm_set_to_L1_le_mul_norm' hT)

lemma set_to_L1_lipschitz (hT : dominated_fin_meas_additive μ T C) :
  lipschitz_with (real.to_nnreal C) (set_to_L1 hT) :=
(set_to_L1 hT).lipschitz.weaken (norm_set_to_L1_le' hT)

/-- If `fs i → f` in `L1`, then `set_to_L1 hT (fs i) → set_to_L1 hT f`. -/
lemma tendsto_set_to_L1 (hT : dominated_fin_meas_additive μ T C) (f : α →₁[μ] E)
  {ι} (fs : ι → α →₁[μ] E) {l : filter ι} (hfs : tendsto fs l (𝓝 f)) :
  tendsto (λ i, set_to_L1 hT (fs i)) l (𝓝 $ set_to_L1 hT f) :=
((set_to_L1 hT).continuous.tendsto _).comp hfs

end set_to_L1

end L1

section function

variables [second_countable_topology E] [borel_space E] [complete_space F]
  {T : set α → E →L[ℝ] F} {C : ℝ} {f g : α → E}

variables (μ T)
/-- Extend `T : set α → E →L[ℝ] F` to `(α → E) → F` (for integrable functions `α → E`). We set it to
0 if the function is not integrable. -/
def set_to_fun (hT : dominated_fin_meas_additive μ T C) (f : α → E) : F :=
if hf : integrable f μ then L1.set_to_L1 hT (hf.to_L1 f) else 0

variables {μ T}

lemma set_to_fun_eq (hT : dominated_fin_meas_additive μ T C) (hf : integrable f μ) :
  set_to_fun μ T hT f = L1.set_to_L1 hT (hf.to_L1 f) :=
dif_pos hf

lemma L1.set_to_fun_eq_set_to_L1 (hT : dominated_fin_meas_additive μ T C) (f : α →₁[μ] E) :
  set_to_fun μ T hT f = L1.set_to_L1 hT f :=
by rw [set_to_fun_eq hT (L1.integrable_coe_fn f), integrable.to_L1_coe_fn]

lemma set_to_fun_undef (hT : dominated_fin_meas_additive μ T C) (hf : ¬ integrable f μ) :
  set_to_fun μ T hT f = 0 :=
dif_neg hf

lemma set_to_fun_non_ae_measurable (hT : dominated_fin_meas_additive μ T C)
  (hf : ¬ ae_measurable f μ) :
  set_to_fun μ T hT f = 0 :=
set_to_fun_undef hT (not_and_of_not_left _ hf)

@[simp] lemma set_to_fun_zero (hT : dominated_fin_meas_additive μ T C) :
  set_to_fun μ T hT (0 : α → E) = 0 :=
begin
  rw set_to_fun_eq hT,
  { simp only [integrable.to_L1_zero, continuous_linear_map.map_zero], },
  { exact integrable_zero _ _ _, },
end

lemma set_to_fun_add (hT : dominated_fin_meas_additive μ T C)
  (hf : integrable f μ) (hg : integrable g μ) :
  set_to_fun μ T hT (f + g) = set_to_fun μ T hT f + set_to_fun μ T hT g :=
by rw [set_to_fun_eq hT (hf.add hg), set_to_fun_eq hT hf, set_to_fun_eq hT hg, integrable.to_L1_add,
  (L1.set_to_L1 hT).map_add]

lemma set_to_fun_neg (hT : dominated_fin_meas_additive μ T C) (f : α → E) :
  set_to_fun μ T hT (-f) = - set_to_fun μ T hT f :=
begin
  by_cases hf : integrable f μ,
  { rw [set_to_fun_eq hT hf, set_to_fun_eq hT hf.neg,
      integrable.to_L1_neg, (L1.set_to_L1 hT).map_neg], },
  { rw [set_to_fun_undef hT hf, set_to_fun_undef hT, neg_zero],
    rwa [← integrable_neg_iff] at hf, }
end

lemma set_to_fun_sub (hT : dominated_fin_meas_additive μ T C)
  (hf : integrable f μ) (hg : integrable g μ) :
  set_to_fun μ T hT (f - g) = set_to_fun μ T hT f - set_to_fun μ T hT g :=
by rw [sub_eq_add_neg, sub_eq_add_neg, set_to_fun_add hT hf hg.neg, set_to_fun_neg hT g]

lemma set_to_fun_smul [nondiscrete_normed_field 𝕜] [measurable_space 𝕜] [opens_measurable_space 𝕜]
  [normed_space 𝕜 E] [normed_space 𝕜 F] (hT : dominated_fin_meas_additive μ T C)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) (f : α → E) :
  set_to_fun μ T hT (c • f) = c • set_to_fun μ T hT f :=
begin
  by_cases hf : integrable f μ,
  { rw [set_to_fun_eq hT hf, set_to_fun_eq hT, integrable.to_L1_smul',
      L1.set_to_L1_smul hT h_smul c _], },
  { by_cases hr : c = 0,
    { rw hr, simp, },
    { have hf' : ¬ integrable (c • f) μ, by rwa [integrable_smul_iff hr f],
      rw [set_to_fun_undef hT hf, set_to_fun_undef hT hf',
        smul_zero], }, },
end

lemma set_to_fun_congr_ae (hT : dominated_fin_meas_additive μ T C) (h : f =ᵐ[μ] g) :
  set_to_fun μ T hT f = set_to_fun μ T hT g :=
begin
  by_cases hfi : integrable f μ,
  { have hgi : integrable g μ := hfi.congr h,
    rw [set_to_fun_eq hT hfi, set_to_fun_eq hT hgi,
      (integrable.to_L1_eq_to_L1_iff f g hfi hgi).2 h] },
  { have hgi : ¬ integrable g μ, { rw integrable_congr h at hfi, exact hfi },
    rw [set_to_fun_undef hT hfi, set_to_fun_undef hT hgi] },
end

lemma set_to_fun_to_L1 (hT : dominated_fin_meas_additive μ T C) (hf : integrable f μ) :
  set_to_fun μ T hT (hf.to_L1 f) = set_to_fun μ T hT f :=
set_to_fun_congr_ae hT hf.coe_fn_to_L1

lemma set_to_fun_indicator_const (hT : dominated_fin_meas_additive μ T C) {s : set α}
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (x : E) :
  set_to_fun μ T hT (s.indicator (λ _, x)) = T s x :=
begin
  rw set_to_fun_congr_ae hT (@indicator_const_Lp_coe_fn _ _ _ 1 _ _ _ _ hs hμs x _ _).symm,
  rw L1.set_to_fun_eq_set_to_L1 hT,
  exact L1.set_to_L1_indicator_const_Lp hT hs hμs x,
end

@[continuity]
lemma continuous_set_to_fun (hT : dominated_fin_meas_additive μ T C) :
  continuous (λ (f : α →₁[μ] E), set_to_fun μ T hT f) :=
by { simp_rw L1.set_to_fun_eq_set_to_L1 hT, exact continuous_linear_map.continuous _, }

lemma norm_set_to_fun_le_mul_norm (hT : dominated_fin_meas_additive μ T C) (f : α →₁[μ] E)
  (hC : 0 ≤ C) :
  ∥set_to_fun μ T hT f∥ ≤ C * ∥f∥ :=
by { rw L1.set_to_fun_eq_set_to_L1, exact L1.norm_set_to_L1_le_mul_norm hT hC f, }

lemma norm_set_to_fun_le_mul_norm' (hT : dominated_fin_meas_additive μ T C) (f : α →₁[μ] E) :
  ∥set_to_fun μ T hT f∥ ≤ max C 0 * ∥f∥ :=
by { rw L1.set_to_fun_eq_set_to_L1, exact L1.norm_set_to_L1_le_mul_norm' hT f, }

lemma norm_set_to_fun_le (hT : dominated_fin_meas_additive μ T C) (hf : integrable f μ)
  (hC : 0 ≤ C) :
  ∥set_to_fun μ T hT f∥ ≤ C * ∥hf.to_L1 f∥ :=
by { rw set_to_fun_eq hT hf, exact L1.norm_set_to_L1_le_mul_norm hT hC _, }

lemma norm_set_to_fun_le' (hT : dominated_fin_meas_additive μ T C) (hf : integrable f μ) :
  ∥set_to_fun μ T hT f∥ ≤ max C 0 * ∥hf.to_L1 f∥ :=
by { rw set_to_fun_eq hT hf, exact L1.norm_set_to_L1_le_mul_norm' hT _, }

/-- Lebesgue dominated convergence theorem provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `set_to_fun`.
  We could weaken the condition `bound_integrable` to require `has_finite_integral bound μ` instead
  (i.e. not requiring that `bound` is measurable), but in all applications proving integrability
  is easier. -/
theorem tendsto_set_to_fun_of_dominated_convergence (hT : dominated_fin_meas_additive μ T C)
  {fs : ℕ → α → E} {f : α → E} (bound : α → ℝ) (fs_measurable : ∀ n, ae_measurable (fs n) μ)
  (bound_integrable : integrable bound μ) (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥fs n a∥ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, fs n a) at_top (𝓝 (f a))) :
  tendsto (λ n, set_to_fun μ T hT (fs n)) at_top (𝓝 $ set_to_fun μ T hT f) :=
begin
  /- `f` is a.e.-measurable, since it is the a.e.-pointwise limit of a.e.-measurable functions. -/
  have f_measurable : ae_measurable f μ := ae_measurable_of_tendsto_metric_ae fs_measurable h_lim,
  /- all functions we consider are integrable -/
  have fs_int : ∀ n, integrable (fs n) μ :=
    λ n, bound_integrable.mono' (fs_measurable n) (h_bound _),
  have f_int : integrable f μ :=
  ⟨f_measurable, has_finite_integral_of_dominated_convergence
    bound_integrable.has_finite_integral h_bound h_lim⟩,
  /- it suffices to prove the result for the corresponding L1 functions -/
  suffices : tendsto (λ n, L1.set_to_L1 hT ((fs_int n).to_L1 (fs n))) at_top
    (𝓝 (L1.set_to_L1 hT (f_int.to_L1 f))),
  { convert this,
    { ext1 n, exact set_to_fun_eq hT (fs_int n), },
    { exact set_to_fun_eq hT f_int, }, },
  /- the convergence of set_to_L1 follows from the convergence of the L1 functions -/
  refine L1.tendsto_set_to_L1 hT _ _ _,
  /- up to some rewriting, what we need to prove is `h_lim` -/
  rw tendsto_iff_norm_tendsto_zero,
  have lintegral_norm_tendsto_zero :
    tendsto (λn, ennreal.to_real $ ∫⁻ a, (ennreal.of_real ∥fs n a - f a∥) ∂μ) at_top (𝓝 0) :=
  (tendsto_to_real zero_ne_top).comp
    (tendsto_lintegral_norm_of_dominated_convergence
      fs_measurable bound_integrable.has_finite_integral h_bound h_lim),
  convert lintegral_norm_tendsto_zero,
  ext1 n,
  rw L1.norm_def,
  congr' 1,
  refine lintegral_congr_ae _,
  rw ← integrable.to_L1_sub,
  refine ((fs_int n).sub f_int).coe_fn_to_L1.mono (λ x hx, _),
  dsimp only,
  rw [hx, of_real_norm_eq_coe_nnnorm, pi.sub_apply],
end

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
lemma tendsto_set_to_fun_filter_of_dominated_convergence (hT : dominated_fin_meas_additive μ T C)
  {ι} {l : _root_.filter ι} [l.is_countably_generated]
  {fs : ι → α → E} {f : α → E} (bound : α → ℝ)
  (hfs_meas : ∀ᶠ n in l, ae_measurable (fs n) μ)
  (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ∥fs n a∥ ≤ bound a)
  (bound_integrable : integrable bound μ)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, fs n a) l (𝓝 (f a))) :
  tendsto (λ n, set_to_fun μ T hT (fs n)) l (𝓝 $ set_to_fun μ T hT f) :=
begin
  rw tendsto_iff_seq_tendsto,
  intros x xl,
  have hxl : ∀ s ∈ l, ∃ a, ∀ b ≥ a, x b ∈ s, by { rwa tendsto_at_top' at xl, },
  have h : {x : ι | (λ n, ae_measurable (fs n) μ) x}
      ∩ {x : ι | (λ n, ∀ᵐ a ∂μ, ∥fs n a∥ ≤ bound a) x} ∈ l,
    from inter_mem hfs_meas h_bound,
  obtain ⟨k, h⟩ := hxl _ h,
  rw ← tendsto_add_at_top_iff_nat k,
  refine tendsto_set_to_fun_of_dominated_convergence hT bound _ bound_integrable _ _,
  { exact λ n, (h _ (self_le_add_left _ _)).1, },
  { exact λ n, (h _ (self_le_add_left _ _)).2, },
  { filter_upwards [h_lim],
    refine λ a h_lin, @tendsto.comp _ _ _ (λ n, x (n + k)) (λ n, fs n a) _ _ _ h_lin _,
    rw tendsto_add_at_top_iff_nat,
    assumption }
end

variables {X : Type*} [topological_space X] [first_countable_topology X]

lemma continuous_at_set_to_fun_of_dominated (hT : dominated_fin_meas_additive μ T C)
  {fs : X → α → E} {x₀ : X} {bound : α → ℝ} (hfs_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (fs x) μ)
  (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ∥fs x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐ a ∂μ, continuous_at (λ x, fs x a) x₀) :
  continuous_at (λ x, set_to_fun μ T hT (fs x)) x₀ :=
tendsto_set_to_fun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›

lemma continuous_set_to_fun_of_dominated (hT : dominated_fin_meas_additive μ T C)
  {fs : X → α → E} {bound : α → ℝ}
  (hfs_meas : ∀ x, ae_measurable (fs x) μ) (h_bound : ∀ x, ∀ᵐ a ∂μ, ∥fs x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐ a ∂μ, continuous (λ x, fs x a)) :
  continuous (λ x, set_to_fun μ T hT (fs x)) :=
continuous_iff_continuous_at.mpr (λ x₀, continuous_at_set_to_fun_of_dominated hT
  (eventually_of_forall hfs_meas) (eventually_of_forall h_bound) ‹_› $ h_cont.mono $
    λ _, continuous.continuous_at)

end function

end measure_theory
