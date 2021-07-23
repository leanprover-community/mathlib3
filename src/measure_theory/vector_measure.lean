/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.integration

/-!

# Vector valued measures

This file defines vector valued measures, which are σ-additive functions from a set to a add monoid
`M` such that it maps the empty set and non-measurable sets to zero. In the case
that `M = ℝ`, we called the vector measure a signed measure and write `signed_measure α`.
Similarly, when `M = ℂ`, we call the measure a complex measure and write `complex_measure α`.

## Main definitions

* `vector_measure` is a vector valued, σ-additive function that maps the empty
  and non-measurable set to zero.

## Implementation notes

We require all non-measurable sets to be mapped to zero in order for the extensionality lemma
to only compare the underlying functions for measurable sets.

We use `has_sum` instead of `tsum` in the definition of vector measures in comparison to `measure`
since this provides summablity.

## Tags

vector measure, signed measure, complex measure
-/

noncomputable theory

open_locale classical big_operators nnreal ennreal

namespace measure_theory

variables {α β : Type*} [measurable_space α]

/-- A vector measure on a measurable space `α` is a σ-additive `M`-valued function (for some `M`
an add monoid) such that the empty set and non-measurable sets are mapped to zero. -/
structure vector_measure (α : Type*) [measurable_space α]
  (M : Type*) [add_comm_monoid M] [topological_space M] :=
(measure_of' : set α → M)
(empty' : measure_of' ∅ = 0)
(not_measurable' ⦃i : set α⦄ : ¬ measurable_set i → measure_of' i = 0)
(m_Union' ⦃f : ℕ → set α⦄ :
  (∀ i, measurable_set (f i)) → pairwise (disjoint on f) →
  has_sum (λ i, measure_of' (f i)) (measure_of' (⋃ i, f i)))

/-- A `signed_measure` is a `ℝ`-vector measure. -/
abbreviation signed_measure (α : Type*) [measurable_space α] := vector_measure α ℝ
/-- A `complex_measure` is a `ℂ`-vector_measure. -/
abbreviation complex_measure (α : Type*) [measurable_space α] := vector_measure α ℂ

open set measure_theory

namespace vector_measure

section

variables {M : Type*} [add_comm_monoid M] [topological_space M]

instance : has_coe_to_fun (vector_measure α M) :=
⟨λ _, set α → M, vector_measure.measure_of'⟩

initialize_simps_projections vector_measure (measure_of' → apply)

@[simp]
lemma measure_of_eq_coe (v : vector_measure α M) : v.measure_of' = v := rfl

@[simp]
lemma empty (v : vector_measure α M) : v ∅ = 0 := v.empty'

lemma not_measurable (v : vector_measure α M)
  {i : set α} (hi : ¬ measurable_set i) : v i = 0 := v.not_measurable' hi

lemma m_Union (v : vector_measure α M) {f : ℕ → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  has_sum (λ i, v (f i)) (v (⋃ i, f i)) :=
v.m_Union' hf₁ hf₂

lemma of_disjoint_Union_nat [t2_space M] (v : vector_measure α M) {f : ℕ → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  v (⋃ i, f i) = ∑' i, v (f i) :=
(v.m_Union hf₁ hf₂).tsum_eq.symm

lemma coe_injective : @function.injective (vector_measure α M) (set α → M) coe_fn :=
λ v w h, by { cases v, cases w, congr' }

lemma ext_iff' (v w : vector_measure α M) :
  v = w ↔ ∀ i : set α, v i = w i :=
by rw [← coe_injective.eq_iff, function.funext_iff]

lemma ext_iff (v w : vector_measure α M) :
  v = w ↔ ∀ i : set α, measurable_set i → v i = w i :=
begin
  split,
  { rintro rfl _ _, refl },
  { rw ext_iff',
    intros h i,
    by_cases hi : measurable_set i,
    { exact h i hi },
    { simp_rw [not_measurable _ hi] } }
end

@[ext] lemma ext {s t : vector_measure α M}
  (h : ∀ i : set α, measurable_set i → s i = t i) : s = t :=
(ext_iff s t).2 h

variables [t2_space M] {v : vector_measure α M} {f : ℕ → set α}

lemma has_sum_of_disjoint_Union [encodable β] {f : β → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  has_sum (λ i, v (f i)) (v (⋃ i, f i)) :=
begin
  set g := λ i : ℕ, ⋃ (b : β) (H : b ∈ encodable.decode₂ β i), f b with hg,
  have hg₁ : ∀ i, measurable_set (g i),
  { exact λ _, measurable_set.Union (λ b, measurable_set.Union_Prop $ λ _, hf₁ b) },
  have hg₂ : pairwise (disjoint on g),
  { exact encodable.Union_decode₂_disjoint_on hf₂ },
  have := v.of_disjoint_Union_nat hg₁ hg₂,
  rw [hg, encodable.Union_decode₂] at this,

  have hg₃ : (λ (i : β), v (f i)) = (λ i, v (g (encodable.encode i))),
  { ext, rw hg, simp only,
    congr, ext y, simp only [exists_prop, mem_Union, option.mem_def],
    split,
    { intro hy,
      refine ⟨x, (encodable.decode₂_is_partial_inv _ _).2 rfl, hy⟩ },
    { rintro ⟨b, hb₁, hb₂⟩,
      rw (encodable.decode₂_is_partial_inv _ _) at hb₁,
      rwa ← encodable.encode_injective hb₁ } },

  rw [summable.has_sum_iff, this, ← tsum_Union_decode₂],
  { exact v.empty },
  { rw hg₃, change summable ((λ i, v (g i)) ∘ encodable.encode),
    rw function.injective.summable_iff encodable.encode_injective,
    { exact (v.m_Union hg₁ hg₂).summable },
    { intros x hx,
      convert v.empty,
      simp only [Union_eq_empty, option.mem_def, not_exists, mem_range] at ⊢ hx,
      intros i hi,
      exact false.elim ((hx i) ((encodable.decode₂_is_partial_inv _ _).1 hi)) } }
end

lemma of_disjoint_Union [encodable β] {f : β → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  v (⋃ i, f i) = ∑' i, v (f i) :=
(has_sum_of_disjoint_Union hf₁ hf₂).tsum_eq.symm

lemma of_union {A B : set α}
  (h : disjoint A B) (hA : measurable_set A) (hB : measurable_set B) :
  v (A ∪ B) = v A + v B :=
begin
  rw [union_eq_Union, of_disjoint_Union, tsum_fintype, fintype.sum_bool, cond, cond],
  exacts [λ b, bool.cases_on b hB hA, pairwise_disjoint_on_bool.2 h]
end

lemma of_add_of_diff {A B : set α} (hA : measurable_set A) (hB : measurable_set B)
  (h : A ⊆ B) : v A + v (B \ A) = v B :=
begin
  rw [← of_union disjoint_diff hA (hB.diff hA), union_diff_cancel h],
  apply_instance,
end

lemma of_diff {M : Type*} [add_comm_group M]
  [topological_space M] [t2_space M] {v : vector_measure α M}
  {A B : set α} (hA : measurable_set A) (hB : measurable_set B)
  (h : A ⊆ B) : v (B \ A) = v B - (v A) :=
begin
  rw [← of_add_of_diff hA hB h, add_sub_cancel'],
  apply_instance,
end

lemma of_Union_nonneg {M : Type*} [topological_space M]
  [ordered_add_comm_monoid M] [order_closed_topology M]
  {v : vector_measure α M} (hf₁ : ∀ i, measurable_set (f i))
  (hf₂ : pairwise (disjoint on f)) (hf₃ : ∀ i, 0 ≤ v (f i)) :
  0 ≤ v (⋃ i, f i) :=
(v.of_disjoint_Union_nat hf₁ hf₂).symm ▸ tsum_nonneg hf₃

lemma of_Union_nonpos {M : Type*} [topological_space M]
  [ordered_add_comm_monoid M] [order_closed_topology M]
  {v : vector_measure α M} (hf₁ : ∀ i, measurable_set (f i))
  (hf₂ : pairwise (disjoint on f)) (hf₃ : ∀ i, v (f i) ≤ 0) :
  v (⋃ i, f i) ≤ 0 :=
(v.of_disjoint_Union_nat hf₁ hf₂).symm ▸ tsum_nonpos hf₃

lemma of_nonneg_disjoint_union_eq_zero {s : signed_measure α} {A B : set α}
  (h : disjoint A B) (hA₁ : measurable_set A) (hB₁ : measurable_set B)
  (hA₂ : 0 ≤ s A) (hB₂ : 0 ≤ s B)
  (hAB : s (A ∪ B) = 0) : s A = 0 :=
begin
  rw of_union h hA₁ hB₁ at hAB,
  linarith,
  apply_instance,
end

lemma of_nonpos_disjoint_union_eq_zero {s : signed_measure α} {A B : set α}
  (h : disjoint A B) (hA₁ : measurable_set A) (hB₁ : measurable_set B)
  (hA₂ : s A ≤ 0) (hB₂ : s B ≤ 0)
  (hAB : s (A ∪ B) = 0) : s A = 0 :=
begin
  rw of_union h hA₁ hB₁ at hAB,
  linarith,
  apply_instance,
end

end

section add_comm_monoid

variables {M : Type*} [add_comm_monoid M] [topological_space M]

instance : has_zero (vector_measure α M) :=
⟨⟨0, rfl, λ _ _, rfl, λ _ _ _, has_sum_zero⟩⟩

instance : inhabited (vector_measure α M) := ⟨0⟩

@[simp] lemma coe_zero : ⇑(0 : vector_measure α M) = 0 := rfl
lemma zero_apply (i : set α) : (0 : vector_measure α M) i = 0 := rfl

variables [has_continuous_add M]

/-- The sum of two vector measure is a vector measure. -/
def add (v w : vector_measure α M) : vector_measure α M :=
{ measure_of' := v + w,
  empty' := by simp,
  not_measurable' := λ _ hi,
    by simp [v.not_measurable hi, w.not_measurable hi],
  m_Union' := λ f hf₁ hf₂,
    has_sum.add (v.m_Union hf₁ hf₂) (w.m_Union hf₁ hf₂) }

instance : has_add (vector_measure α M) := ⟨add⟩

@[simp] lemma coe_add (v w : vector_measure α M) : ⇑(v + w) = v + w := rfl
lemma add_apply (v w : vector_measure α M) (i : set α) :(v + w) i = v i + w i := rfl

instance : add_comm_monoid (vector_measure α M) :=
function.injective.add_comm_monoid _ coe_injective coe_zero coe_add

/-- `coe_fn` is an `add_monoid_hom`. -/
@[simps]
def coe_fn_add_monoid_hom : vector_measure α M →+ (set α → M) :=
{ to_fun := coe_fn, map_zero' := coe_zero, map_add' := coe_add }

end add_comm_monoid

section add_comm_group

variables {M : Type*} [add_comm_group M] [topological_space M]

variables [topological_add_group M]

/-- The negative of a vector measure is a vector measure. -/
def neg (v : vector_measure α M) : vector_measure α M :=
{ measure_of' := -v,
  empty' := by simp,
  not_measurable' := λ _ hi, by simp [v.not_measurable hi],
  m_Union' := λ f hf₁ hf₂, has_sum.neg $ v.m_Union hf₁ hf₂ }

instance : has_neg (vector_measure α M) := ⟨neg⟩

@[simp] lemma coe_neg (v : vector_measure α M) : ⇑(-v) = - v := rfl
lemma neg_apply (v : vector_measure α M) (i : set α) :(-v) i = - v i := rfl

/-- The difference of two vector measure is a vector measure. -/
def sub (v w : vector_measure α M) : vector_measure α M :=
{ measure_of' := v - w,
  empty' := by simp,
  not_measurable' := λ _ hi,
    by simp [v.not_measurable hi, w.not_measurable hi],
  m_Union' := λ f hf₁ hf₂,
    has_sum.sub (v.m_Union hf₁ hf₂)
      (w.m_Union hf₁ hf₂) }

instance : has_sub (vector_measure α M) := ⟨sub⟩

@[simp] lemma coe_sub (v w : vector_measure α M) : ⇑(v - w) = v - w := rfl
lemma sub_apply (v w : vector_measure α M) (i : set α) : (v - w) i = v i - w i := rfl

instance : add_comm_group (vector_measure α M) :=
function.injective.add_comm_group _ coe_injective coe_zero coe_add coe_neg coe_sub

end add_comm_group

section distrib_mul_action

variables {M : Type*} [add_comm_monoid M] [topological_space M]
variables {R : Type*} [semiring R] [distrib_mul_action R M]
variables [topological_space R] [has_continuous_smul R M]

/-- Given a real number `r` and a signed measure `s`, `smul r s` is the signed
measure corresponding to the function `r • s`. -/
def smul (r : R) (v : vector_measure α M) : vector_measure α M :=
{ measure_of' := r • v,
  empty' := by rw [pi.smul_apply, empty, smul_zero],
  not_measurable' := λ _ hi, by rw [pi.smul_apply, v.not_measurable hi, smul_zero],
  m_Union' := λ _ hf₁ hf₂, has_sum.smul (v.m_Union hf₁ hf₂) }

instance : has_scalar R (vector_measure α M) := ⟨smul⟩

@[simp] lemma coe_smul (r : R) (v : vector_measure α M) : ⇑(r • v) = r • v := rfl
lemma smul_apply (r : R) (v : vector_measure α M) (i : set α) :
  (r • v) i = r • v i := rfl

instance [has_continuous_add M] : distrib_mul_action R (vector_measure α M) :=
function.injective.distrib_mul_action coe_fn_add_monoid_hom coe_injective coe_smul

end distrib_mul_action

section module

variables {M : Type*} [add_comm_monoid M] [topological_space M]
variables {R : Type*} [semiring R] [module R M]
variables [topological_space R] [has_continuous_smul R M]

instance [has_continuous_add M] : module R (vector_measure α M) :=
function.injective.module R coe_fn_add_monoid_hom coe_injective coe_smul

end module

end vector_measure

namespace measure

/-- A finite measure coerced into a real function is a signed measure. -/
@[simps]
def to_signed_measure (μ : measure α) [hμ : finite_measure μ] : signed_measure α :=
{ measure_of' := λ i : set α, if measurable_set i then (μ.measure_of i).to_real else 0,
  empty' := by simp [μ.empty],
  not_measurable' := λ _ hi, if_neg hi,
  m_Union' :=
  begin
    intros _ hf₁ hf₂,
    rw [μ.m_Union hf₁ hf₂, ennreal.tsum_to_real_eq, if_pos (measurable_set.Union hf₁),
        summable.has_sum_iff],
    { congr, ext n, rw if_pos (hf₁ n) },
    { refine @summable_of_nonneg_of_le _ (ennreal.to_real ∘ μ ∘ f) _ _ _ _,
      { intro, split_ifs,
        exacts [ennreal.to_real_nonneg, le_refl _] },
      { intro, split_ifs,
        exacts [le_refl _, ennreal.to_real_nonneg] },
        exact summable_measure_to_real hf₁ hf₂ },
    { intros a ha,
      apply ne_of_lt hμ.measure_univ_lt_top,
      rw [eq_top_iff, ← ha, outer_measure.measure_of_eq_coe, coe_to_outer_measure],
      exact measure_mono (set.subset_univ _) }
  end }

lemma to_signed_measure_apply_measurable {μ : measure α} [finite_measure μ]
  {i : set α} (hi : measurable_set i) :
  μ.to_signed_measure i = (μ i).to_real :=
if_pos hi

@[simp] lemma to_signed_measure_zero :
  (0 : measure α).to_signed_measure = 0 :=
by { ext i hi, simp }

@[simp] lemma to_signed_measure_add (μ ν : measure α) [finite_measure μ] [finite_measure ν] :
  (μ + ν).to_signed_measure = μ.to_signed_measure + ν.to_signed_measure :=
begin
  ext i hi,
  rw [to_signed_measure_apply_measurable hi, add_apply,
      ennreal.to_real_add (ne_of_lt (measure_lt_top _ _ )) (ne_of_lt (measure_lt_top _ _)),
      vector_measure.add_apply, to_signed_measure_apply_measurable hi,
      to_signed_measure_apply_measurable hi],
  all_goals { apply_instance }
end

@[simp] lemma to_signed_measure_smul (μ : measure α) [finite_measure μ] (r : ℝ≥0) :
  (r • μ).to_signed_measure = r • μ.to_signed_measure :=
begin
  ext i hi,
  rw [to_signed_measure_apply_measurable hi, vector_measure.smul_apply,
      to_signed_measure_apply_measurable hi, coe_nnreal_smul, pi.smul_apply,
      ennreal.to_real_smul],
end

/-- A measure is a vector measure over `ℝ≥0∞`. -/
@[simps]
def to_ennreal_vector_measure (μ : measure α) : vector_measure α ℝ≥0∞ :=
{ measure_of' := λ i : set α, if measurable_set i then μ i else 0,
  empty' := by simp [μ.empty],
  not_measurable' := λ _ hi, if_neg hi,
  m_Union' := λ _ hf₁ hf₂,
  begin
    rw summable.has_sum_iff ennreal.summable,
    { rw [if_pos (measurable_set.Union hf₁), measure_theory.measure_Union hf₂ hf₁],
      exact tsum_congr (λ n, if_pos (hf₁ n)) },
  end }

lemma to_ennreal_vector_measure_apply_measurable
  {μ : measure α} {i : set α} (hi : measurable_set i) :
  μ.to_ennreal_vector_measure i = μ i :=
if_pos hi

@[simp] lemma to_ennreal_vector_measure_zero :
  (0 : measure α).to_ennreal_vector_measure = 0 :=
by { ext i hi, simp }

@[simp] lemma to_ennreal_vector_measure_add (μ ν : measure α) :
  (μ + ν).to_ennreal_vector_measure = μ.to_ennreal_vector_measure + ν.to_ennreal_vector_measure :=
begin
  refine measure_theory.vector_measure.ext (λ i hi, _),
  rw [to_ennreal_vector_measure_apply_measurable hi, add_apply, vector_measure.add_apply,
      to_ennreal_vector_measure_apply_measurable hi, to_ennreal_vector_measure_apply_measurable hi]
end

/-- Given two finite measures `μ, ν`, `sub_to_signed_measure μ ν` is the signed measure
corresponding to the function `μ - ν`. -/
def sub_to_signed_measure (μ ν : measure α) [hμ : finite_measure μ] [hν : finite_measure ν] :
  signed_measure α :=
μ.to_signed_measure - ν.to_signed_measure

lemma sub_to_signed_measure_apply {μ ν : measure α} [finite_measure μ] [finite_measure ν]
  {i : set α} (hi : measurable_set i) :
  μ.sub_to_signed_measure ν i = (μ i).to_real - (ν i).to_real :=
begin
  rw [sub_to_signed_measure, vector_measure.sub_apply, to_signed_measure_apply_measurable hi,
      measure.to_signed_measure_apply_measurable hi, sub_eq_add_neg]
end

end measure

namespace vector_measure

section

variables {M : Type*} [topological_space M] [add_comm_monoid M] [partial_order M]

instance : partial_order (vector_measure α M) :=
{ le          := λ v w, ∀ i, measurable_set i → v i ≤ w i,
  le_refl     := λ v i hi, le_refl _,
  le_trans    := λ u v w h₁ h₂ i hi, le_trans (h₁ i hi) (h₂ i hi),
  le_antisymm := λ v w h₁ h₂, ext (λ i hi, le_antisymm (h₁ i hi) (h₂ i hi)) }

variables {u v w : vector_measure α M}

lemma le_iff : v ≤ w ↔ ∀ i, measurable_set i → v i ≤ w i :=
iff.rfl

lemma le_iff' : v ≤ w ↔ ∀ i, v i ≤ w i :=
begin
  refine ⟨λ h i, _, λ h i hi, h i⟩,
  by_cases hi : measurable_set i,
  { exact h i hi },
  { rw [v.not_measurable hi, w.not_measurable hi] }
end

end

section

variables {M : Type*} [topological_space M] [add_comm_monoid M] [partial_order M]
  [covariant_class M M (+) (≤)] [has_continuous_add M]

instance covariant_add_le :
  covariant_class (vector_measure α M) (vector_measure α M) (+) (≤) :=
⟨λ u v w h i hi, add_le_add_left (h i hi) _⟩

end

end vector_measure

end measure_theory
