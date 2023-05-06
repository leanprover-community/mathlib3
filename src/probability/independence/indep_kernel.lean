/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.notation
import measure_theory.constructions.pi
import probability.kernel.basic

/-!
# Independence with respect to a kernel and a measure


This file does not contain a notion of independence of a kernel with respect to another. This is
independence of sets or random variables with respect to a kernel and a measure. This is a minimal
generalization of both independence and conditional independence.

Independence: `κ = kernel.const unit μ`, with measure `(measure.dirac () : measure unit)`
Conditional independence: `κ` is the yet to be defined conditional kernel and `μ` is the ambiant
measure.

## Main definitions

* `foo_bar`



## Main statements

* `foo_bar_unique`

## Notation


-/

open measure_theory measurable_space
open_locale big_operators measure_theory ennreal

namespace probability_theory

variables {Ω α ι : Type*}

section definitions

variables {mα : measurable_space α}
include mα

/-- A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a kernel `κ` and
a measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `∀ᵐ a ∂μ, κ a (⋂ i in s, f i) = ∏ i in s, κ a (f i) `.
It will be used for families of pi_systems. -/
def Indep_setsₖ {mΩ : measurable_space Ω} (π : ι → set (set Ω)) (κ : kernel α Ω)
  (μ : measure α . volume_tac) :
  Prop :=
∀ (s : finset ι) {f : ι → set Ω} (H : ∀ i, i ∈ s → f i ∈ π i),
  ∀ᵐ a ∂μ, κ a (⋂ i ∈ s, f i) = ∏ i in s, κ a (f i)

/-- Two sets of sets `s₁, s₂` are independent with respect to a kernel `κ` and a measure `μ` if for
any sets `t₁ ∈ p₁, t₂ ∈ s₂`, then `∀ᵐ a ∂μ, κ a (t₁ ∩ t₂) = κ a (t₁) * κ a (t₂)` -/
def indep_setsₖ {mΩ : measurable_space Ω} (s1 s2 : set (set Ω)) (κ : kernel α Ω)
  (μ : measure α . volume_tac) : Prop :=
∀ t1 t2 : set Ω, t1 ∈ s1 → t2 ∈ s2 → (∀ᵐ a ∂μ, κ a (t1 ∩ t2) = κ a t1 * κ a t2)

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
kernel `κ` and a measure `μ` if the family of sets of measurable sets they define is independent. -/
def Indepₖ (m : ι → measurable_space Ω) {mΩ : measurable_space Ω} (κ : kernel α Ω)
  (μ : measure α . volume_tac) :
  Prop :=
Indep_setsₖ (λ x, {s | measurable_set[m x] s}) κ μ

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
kernel `κ` and a measure `μ` if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`∀ᵐ a ∂μ, κ a (t₁ ∩ t₂) = κ a (t₁) * κ a (t₂)` -/
def indepₖ (m₁ m₂ : measurable_space Ω) {mΩ : measurable_space Ω} (κ : kernel α Ω)
  (μ : measure α . volume_tac) :
  Prop :=
indep_setsₖ {s | measurable_set[m₁] s} {s | measurable_set[m₂] s} κ μ

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def Indep_setₖ {mΩ : measurable_space Ω} (s : ι → set Ω) (κ : kernel α Ω)
  (μ : measure α . volume_tac) : Prop :=
Indepₖ (λ i, generate_from {s i}) κ μ

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def indep_setₖ {mΩ : measurable_space Ω} (s t : set Ω) (κ : kernel α Ω)
  (μ : measure α . volume_tac) : Prop :=
indepₖ (generate_from {s}) (generate_from {t}) κ μ

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def Indep_funₖ {mΩ : measurable_space Ω} {β : ι → Type*} (m : Π (x : ι), measurable_space (β x))
  (f : Π (x : ι), Ω → β x) (κ : kernel α Ω)
  (μ : measure α . volume_tac) : Prop :=
Indepₖ (λ x, measurable_space.comap (f x) (m x)) κ μ

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def indep_funₖ {β γ} {mΩ : measurable_space Ω} [mβ : measurable_space β] [mγ : measurable_space γ]
  (f : Ω → β) (g : Ω → γ) (κ : kernel α Ω)
  (μ : measure α . volume_tac) : Prop :=
indepₖ (measurable_space.comap f mβ) (measurable_space.comap g mγ) κ μ

end definitions

section indep

variables {mα : measurable_space α} {m₁ m₂ m₃ m : measurable_space Ω} {κ : kernel α Ω}
  {μ : measure α} {s₁ s₂ s₃ : set (set Ω)}

@[symm] lemma indep_setsₖ.symm (h : indep_setsₖ s₁ s₂ κ μ) :
  indep_setsₖ s₂ s₁ κ μ :=
begin
  intros t1 t2 ht1 ht2,
  filter_upwards [h t2 t1 ht2 ht1] with a ha,
  rwa [set.inter_comm, mul_comm],
end

@[symm] lemma indepₖ.symm (h : indepₖ m₁ m₂ κ μ) :
  indepₖ m₂ m₁ κ μ :=
indep_setsₖ.symm h

lemma indepₖ_bot_right (m' : measurable_space Ω) {mα : measurable_space α} {m : measurable_space Ω}
  {κ : kernel α Ω} {μ : measure α} [∀ a, is_probability_measure (κ a)] :
  indepₖ m' ⊥ κ μ :=
begin
  intros s t hs ht,
  rw [set.mem_set_of_eq, measurable_space.measurable_set_bot_iff] at ht,
  refine filter.eventually_of_forall (λ a, _),
  cases ht,
  { rw [ht, set.inter_empty, measure_empty, mul_zero], },
  { rw [ht, set.inter_univ, measure_univ, mul_one], },
end

lemma indepₖ_bot_left (m' : measurable_space Ω) {mα : measurable_space α} {m : measurable_space Ω}
  {κ : kernel α Ω} {μ : measure α} [∀ a, is_probability_measure (κ a)] :
  indepₖ ⊥ m' κ μ :=
(indepₖ_bot_right m').symm

lemma indep_setₖ_empty_right [∀ a, is_probability_measure (κ a)] (s : set Ω) :
  indep_setₖ s ∅ κ μ :=
by { simp only [indep_setₖ, generate_from_singleton_empty], exact indepₖ_bot_right _, }

lemma indep_setₖ_empty_left [∀ a, is_probability_measure (κ a)] (s : set Ω) :
  indep_setₖ ∅ s κ μ :=
(indep_setₖ_empty_right s).symm

lemma indep_setsₖ_of_indep_setsₖ_of_le_left (h_indep : indep_setsₖ s₁ s₂ κ μ) (h31 : s₃ ⊆ s₁) :
  indep_setsₖ s₃ s₂ κ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (set.mem_of_subset_of_mem h31 ht1) ht2

lemma indep_setsₖ_of_indep_setsₖ_of_le_right (h_indep : indep_setsₖ s₁ s₂ κ μ) (h32 : s₃ ⊆ s₂) :
  indep_setsₖ s₁ s₃ κ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (set.mem_of_subset_of_mem h32 ht2)

lemma indepₖ_of_indepₖ_of_le_left (h_indep : indepₖ m₁ m₂ κ μ) (h31 : m₃ ≤ m₁) :
  indepₖ m₃ m₂ κ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (h31 _ ht1) ht2

lemma indepₖ_of_indepₖ_of_le_right (h_indep : indepₖ m₁ m₂ κ μ) (h32 : m₃ ≤ m₂) :
  indepₖ m₁ m₃ κ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (h32 _ ht2)

lemma indep_setsₖ.union (h₁ : indep_setsₖ s₁ s₃ κ μ) (h₂ : indep_setsₖ s₂ s₃ κ μ) :
  indep_setsₖ (s₁ ∪ s₂) s₃ κ μ :=
begin
  intros t1 t2 ht1 ht2,
  cases (set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂,
  { exact h₁ t1 t2 ht1₁ ht2, },
  { exact h₂ t1 t2 ht1₂ ht2, },
end

@[simp] lemma indep_setsₖ.union_iff :
  indep_setsₖ (s₁ ∪ s₂) s₃ κ μ ↔ indep_setsₖ s₁ s₃ κ μ ∧ indep_setsₖ s₂ s₃ κ μ :=
⟨λ h, ⟨indep_setsₖ_of_indep_setsₖ_of_le_left h (set.subset_union_left s₁ s₂),
    indep_setsₖ_of_indep_setsₖ_of_le_left h (set.subset_union_right s₁ s₂)⟩,
  λ h, indep_setsₖ.union h.left h.right⟩

lemma indep_setsₖ.Union {s : ι → set (set Ω)} (hyp : ∀ n, indep_setsₖ (s n) s₂ κ μ) :
  indep_setsₖ (⋃ n, s n) s₂ κ μ :=
begin
  intros t1 t2 ht1 ht2,
  rw set.mem_Union at ht1,
  cases ht1 with n ht1,
  exact hyp n t1 t2 ht1 ht2,
end

lemma indep_setsₖ.bUnion {s : ι → set (set Ω)} {u : set ι}
  (hyp : ∀ n ∈ u, indep_setsₖ (s n) s₂ κ μ) :
  indep_setsₖ (⋃ n ∈ u, s n) s₂ κ μ :=
begin
  intros t1 t2 ht1 ht2,
  simp_rw set.mem_Union at ht1,
  rcases ht1 with ⟨n, hpn, ht1⟩,
  exact hyp n hpn t1 t2 ht1 ht2,
end

lemma indep_setsₖ.inter  (s₂ : set (set Ω)) (h₁ : indep_setsₖ s₁ s₃ κ μ) :
  indep_setsₖ (s₁ ∩ s₂) s₃ κ μ :=
λ t1 t2 ht1 ht2, h₁ t1 t2 ((set.mem_inter_iff _ _ _).mp ht1).left ht2

lemma indep_setsₖ.Inter {s : ι → set (set Ω)} (h : ∃ n, indep_setsₖ (s n) s₂ κ μ) :
  indep_setsₖ (⋂ n, s n) s₂ κ μ :=
by {intros t1 t2 ht1 ht2, cases h with n h, exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2 }

lemma indep_setsₖ.bInter {s : ι → set (set Ω)} {u : set ι} (h : ∃ n ∈ u, indep_setsₖ (s n) s₂ κ μ) :
  indep_setsₖ (⋂ n ∈ u, s n) s₂ κ μ :=
begin
  intros t1 t2 ht1 ht2,
  rcases h with ⟨n, hn, h⟩,
  exact h t1 t2 (set.bInter_subset_of_mem hn ht1) ht2,
end

lemma indep_setsₖ_singleton_iff {s t : set Ω} :
  indep_setsₖ {s} {t} κ μ ↔ ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t :=
⟨λ h, h s t rfl rfl,
  λ h s1 t1 hs1 ht1, by rwa [set.mem_singleton_iff.mp hs1, set.mem_singleton_iff.mp ht1]⟩

end indep

/-! ### Deducing `indep` from `Indep` -/
section from_Indep_to_indep

variables {mα : measurable_space α} {m₀ : measurable_space Ω} {κ : kernel α Ω} {μ : measure α}

lemma Indep_setsₖ.indep_setsₖ {s : ι → set (set Ω)} (h_indep : Indep_setsₖ s κ μ)
  {i j : ι} (hij : i ≠ j) :
  indep_setsₖ (s i) (s j) κ μ :=
begin
  classical,
  intros t₁ t₂ ht₁ ht₂,
  have hf_m : ∀ (x : ι), x ∈ {i, j} → (ite (x=i) t₁ t₂) ∈ s x,
  { intros x hx,
    cases finset.mem_insert.mp hx with hx hx,
    { simp [hx, ht₁], },
    { simp [finset.mem_singleton.mp hx, hij.symm, ht₂], }, },
  have h1 : t₁ = ite (i = i) t₁ t₂, by simp only [if_true, eq_self_iff_true],
  have h2 : t₂ = ite (j = i) t₁ t₂, by simp only [hij.symm, if_false],
  have h_inter : (⋂ (t : ι) (H : t ∈ ({i, j} : finset ι)), ite (t = i) t₁ t₂)
      = (ite (i = i) t₁ t₂) ∩ (ite (j = i) t₁ t₂),
    by simp only [finset.set_bInter_singleton, finset.set_bInter_insert],
  filter_upwards [h_indep {i, j} hf_m] with a h_indep',
  have h_prod : (∏ (t : ι) in ({i, j} : finset ι), κ a (ite (t = i) t₁ t₂))
      = κ a (ite (i = i) t₁ t₂) * κ a (ite (j = i) t₁ t₂),
    by simp only [hij, finset.prod_singleton, finset.prod_insert, not_false_iff,
      finset.mem_singleton],
  rw h1,
  nth_rewrite 1 h2,
  nth_rewrite 3 h2,
  rw [← h_inter, ← h_prod, h_indep'],
end

lemma Indepₖ.indepₖ {m : ι → measurable_space Ω} (h_indep : Indepₖ m κ μ) {i j : ι} (hij : i ≠ j) :
  indepₖ (m i) (m j) κ μ :=
begin
  change indep_setsₖ ((λ x, measurable_set[m x]) i) ((λ x, measurable_set[m x]) j) κ μ,
  exact Indep_setsₖ.indep_setsₖ h_indep hij,
end

lemma Indep_funₖ.indep_funₖ  {β : ι → Type*}
  {m : Π x, measurable_space (β x)} {f : Π i, Ω → β i} (hf_Indep : Indep_funₖ m f κ μ)
  {i j : ι} (hij : i ≠ j) :
  indep_funₖ (f i) (f j) κ μ :=
hf_Indep.indepₖ hij

end from_Indep_to_indep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/

section from_measurable_spaces_to_sets_of_sets
/-! ### Independence of measurable space structures implies independence of generating π-systems -/

variables {mα : measurable_space α} {m₀ : measurable_space Ω} {κ : kernel α Ω} {μ : measure α}

lemma Indepₖ.Indep_setsₖ {m : ι → measurable_space Ω}
  {s : ι → set (set Ω)} (hms : ∀ n, m n = generate_from (s n))
  (h_indep : Indepₖ m κ μ) :
  Indep_setsₖ s κ μ :=
λ S f hfs, h_indep S $ λ x hxS,
  ((hms x).symm ▸ measurable_set_generate_from (hfs x hxS) : measurable_set[m x] (f x))

lemma indepₖ.indep_setsₖ {s1 s2 : set (set Ω)}
  (h_indep : indepₖ (generate_from s1) (generate_from s2) κ μ) :
  indep_setsₖ s1 s2 κ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (measurable_set_generate_from ht1) (measurable_set_generate_from ht2)

end from_measurable_spaces_to_sets_of_sets

section from_pi_systems_to_measurable_spaces
/-! ### Independence of generating π-systems implies independence of measurable space structures -/

variables {mα : measurable_space α} {m₁ m₂ m₀ : measurable_space Ω} {κ : kernel α Ω}
  {μ : measure α}

private lemma indep_setsₖ.indepₖ_aux [∀ a, is_probability_measure (κ a)] {p1 p2 : set (set Ω)}
  (h2 : m₂ ≤ m₀) (hp2 : is_pi_system p2) (hpm2 : m₂ = generate_from p2)
  (hyp : indep_setsₖ p1 p2 κ μ) {t1 t2 : set Ω} (ht1 : t1 ∈ p1) (ht1m : measurable_set[m₀] t1)
  (ht2m : measurable_set[m₂] t2) :
  ∀ᵐ a ∂μ, κ a (t1 ∩ t2) = κ a t1 * κ a t2 :=
begin
  refine @induction_on_inter _ _ _ m₂ hpm2 hp2 _ _ _ _ _ ht2m,
  { simp only [set.inter_empty, measure_empty, mul_zero, eq_self_iff_true,
      filter.eventually_true], },
  { exact λ t ht_mem_p2, hyp t1 t ht1 ht_mem_p2, },
  { intros t ht h,
    filter_upwards [h] with a ha,
    have : t1 ∩ tᶜ = t1 \ (t1 ∩ t),
    { rw [set.diff_self_inter, set.diff_eq_compl_inter, set.inter_comm], },
    rw [this,
      measure_diff (set.inter_subset_left _ _) (ht1m.inter (h2 _ ht)) (measure_ne_top (κ a) _),
      ha, measure_compl (h2 _ ht) (measure_ne_top (κ a) t), measure_univ,
      ennreal.mul_sub (λ _ _ , measure_ne_top (κ a) _), mul_one], },
  { intros f hf_disj hf_meas h,
    rw ← ae_all_iff at h,
    filter_upwards [h] with a ha,
    rw [set.inter_Union, measure_Union],
    rotate,
    { intros i j hij,
      rw [function.on_fun, set.inter_comm t1, set.inter_comm t1],
      exact disjoint.inter_left _ (disjoint.inter_right _ (hf_disj hij)), },
    { exact λ i, ht1m.inter (h2 _ (hf_meas i)), },
    rw measure_Union hf_disj (λ i, h2 _ (hf_meas i)),
    rw ← ennreal.tsum_mul_left,
    congr' with i,
    rw ha i, },
end

lemma indep_setsₖ.indepₖ [∀ a, is_probability_measure (κ a)] {p1 p2 : set (set Ω)}
  (h1 : m₁ ≤ m₀) (h2 : m₂ ≤ m₀)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hpm1 : m₁ = generate_from p1)
  (hpm2 : m₂ = generate_from p2) (hyp : indep_setsₖ p1 p2 κ μ) :
  indepₖ m₁ m₂ κ μ :=
begin
  intros t1 t2 ht1 ht2,
  refine @induction_on_inter _ _ _ m₁ hpm1 hp1 _ _ _ _ _ ht1,
  { simp only [set.empty_inter, measure_empty, zero_mul, eq_self_iff_true,
      filter.eventually_true], },
  { intros t ht_mem_p1,
    have ht1 : measurable_set[m₀] t,
    { refine h1 _ _,
      rw hpm1,
      exact measurable_set_generate_from ht_mem_p1, },
    exact indep_setsₖ.indepₖ_aux h2 hp2 hpm2 hyp ht_mem_p1 ht1 ht2, },
  { intros t ht h,
    filter_upwards [h] with a ha,
    have : tᶜ ∩ t2 = t2 \ (t ∩ t2),
    { rw [set.inter_comm t, set.diff_self_inter, set.diff_eq_compl_inter], },
    rw [this, set.inter_comm t t2,
      measure_diff (set.inter_subset_left _ _) ((h2 _ ht2).inter (h1 _ ht))
        (measure_ne_top (κ a) _),
      set.inter_comm, ha, measure_compl (h1 _ ht) (measure_ne_top (κ a) t), measure_univ,
      mul_comm (1 - κ a t), ennreal.mul_sub (λ _ _ , measure_ne_top (κ a) _), mul_one, mul_comm], },
  { intros f hf_disj hf_meas h,
    rw ← ae_all_iff at h,
    filter_upwards [h] with a ha,
    rw [set.inter_comm, set.inter_Union, measure_Union],
    rotate,
    { intros i j hij,
      rw [function.on_fun, set.inter_comm t2, set.inter_comm t2],
      exact disjoint.inter_left _ (disjoint.inter_right _ (hf_disj hij)), },
    { exact λ i, (h2 _ ht2).inter (h1 _ (hf_meas i)), },
    rw measure_Union hf_disj (λ i, h1 _ (hf_meas i)),
    rw ← ennreal.tsum_mul_right,
    congr' 1 with i,
    rw [set.inter_comm t2, ha i], },
end

lemma indep_setsₖ.indepₖ' [∀ a, is_probability_measure (κ a)] {p1 p2 : set (set Ω)}
  (hp1m : ∀ s ∈ p1, measurable_set s) (hp2m : ∀ s ∈ p2, measurable_set s)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hyp : indep_setsₖ p1 p2 κ μ) :
  indepₖ (generate_from p1) (generate_from p2) κ μ :=
hyp.indepₖ (generate_from_le hp1m) (generate_from_le hp2m) hp1 hp2 rfl rfl

lemma indep_setsₖ_pi_Union_Inter_of_disjoint [∀ a, is_probability_measure (κ a)]
  {s : ι → set (set Ω)} {S T : set ι}
  (h_indep : Indep_setsₖ s κ μ) (hST : disjoint S T) :
  indep_setsₖ (pi_Union_Inter s S) (pi_Union_Inter s T) κ μ :=
begin
  rintros t1 t2 ⟨p1, hp1, f1, ht1_m, ht1_eq⟩ ⟨p2, hp2, f2, ht2_m, ht2_eq⟩,
  classical,
  let g := λ i, ite (i ∈ p1) (f1 i) set.univ ∩ ite (i ∈ p2) (f2 i) set.univ,
  have h_P_inter : ∀ᵐ a ∂μ, κ a (t1 ∩ t2) = ∏ n in p1 ∪ p2, κ a (g n),
  { have hgm : ∀ i ∈ p1 ∪ p2, g i ∈ s i,
    { intros i hi_mem_union,
      rw finset.mem_union at hi_mem_union,
      cases hi_mem_union with hi1 hi2,
      { have hi2 : i ∉ p2 := λ hip2, set.disjoint_left.mp hST (hp1 hi1) (hp2 hip2),
        simp_rw [g, if_pos hi1, if_neg hi2, set.inter_univ],
        exact ht1_m i hi1, },
      { have hi1 : i ∉ p1 := λ hip1, set.disjoint_right.mp hST (hp2 hi2) (hp1 hip1),
        simp_rw [g, if_neg hi1, if_pos hi2, set.univ_inter],
        exact ht2_m i hi2, }, },
    have h_p1_inter_p2 : ((⋂ x ∈ p1, f1 x) ∩ ⋂ x ∈ p2, f2 x)
      = ⋂ i ∈ p1 ∪ p2, (ite (i ∈ p1) (f1 i) set.univ ∩ ite (i ∈ p2) (f2 i) set.univ),
    { ext1 x,
      simp only [set.mem_ite_univ_right, set.mem_inter_iff, set.mem_Inter, finset.mem_union],
      exact ⟨λ h i _, ⟨h.1 i, h.2 i⟩,
        λ h, ⟨λ i hi, (h i (or.inl hi)).1 hi, λ i hi, (h i (or.inr hi)).2 hi⟩⟩, },
    filter_upwards [h_indep _ hgm] with a ha,
    rw [ht1_eq, ht2_eq, h_p1_inter_p2, ← ha], },
  filter_upwards [h_P_inter, h_indep p1 ht1_m, h_indep p2 ht2_m] with a h_P_inter ha1 ha2,
  have h_μg : ∀ n, κ a (g n) = (ite (n ∈ p1) (κ a (f1 n)) 1) * (ite (n ∈ p2) (κ a (f2 n)) 1),
  { intro n,
    simp_rw g,
    split_ifs,
    { exact absurd rfl (set.disjoint_iff_forall_ne.mp hST _ (hp1 h) _ (hp2 h_1)), },
    all_goals { simp only [measure_univ, one_mul, mul_one, set.inter_univ, set.univ_inter], }, },
  simp_rw [h_P_inter, h_μg, finset.prod_mul_distrib,
    finset.prod_ite_mem (p1 ∪ p2) p1 (λ x, κ a (f1 x)),
    finset.union_inter_cancel_left, finset.prod_ite_mem (p1 ∪ p2) p2 (λ x, κ a (f2 x)),
    finset.union_inter_cancel_right, ht1_eq, ← ha1, ht2_eq, ← ha2],
end

lemma Indep_setₖ.indepₖ_generate_from_of_disjoint [∀ a, is_probability_measure (κ a)] {s : ι → set Ω}
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_setₖ s κ μ) (S T : set ι) (hST : disjoint S T) :
  indepₖ (generate_from {t | ∃ n ∈ S, s n = t}) (generate_from {t | ∃ k ∈ T, s k = t}) κ μ :=
begin
  rw [← generate_from_pi_Union_Inter_singleton_left,
    ← generate_from_pi_Union_Inter_singleton_left],
  refine indep_setsₖ.indepₖ'
    (λ t ht, generate_from_pi_Union_Inter_le _ _ _ _ (measurable_set_generate_from ht))
    (λ t ht, generate_from_pi_Union_Inter_le _ _ _ _ (measurable_set_generate_from ht))
    _ _ _,
  { exact λ k, generate_from_le $ λ t ht, (set.mem_singleton_iff.1 ht).symm ▸ hsm k, },
  { exact λ k, generate_from_le $ λ t ht, (set.mem_singleton_iff.1 ht).symm ▸ hsm k, },
  { exact is_pi_system_pi_Union_Inter _ (λ k, is_pi_system.singleton _) _, },
  { exact is_pi_system_pi_Union_Inter _ (λ k, is_pi_system.singleton _) _, },
  { classical,
    exact indep_setsₖ_pi_Union_Inter_of_disjoint (Indepₖ.Indep_setsₖ (λ n, rfl) hs) hST, },
end

lemma indepₖ_supr_of_disjoint [∀ a, is_probability_measure (κ a)] {m : ι → measurable_space Ω}
  (h_le : ∀ i, m i ≤ m₀) (h_indep : Indepₖ m κ μ) {S T : set ι} (hST : disjoint S T) :
  indepₖ (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) κ μ :=
begin
  refine indep_setsₖ.indepₖ (supr₂_le (λ i _, h_le i)) (supr₂_le (λ i _, h_le i)) _ _
    (generate_from_pi_Union_Inter_measurable_set m S).symm
    (generate_from_pi_Union_Inter_measurable_set m T).symm _,
  { exact is_pi_system_pi_Union_Inter _ (λ n, @is_pi_system_measurable_set Ω (m n)) _, },
  { exact is_pi_system_pi_Union_Inter _ (λ n, @is_pi_system_measurable_set Ω (m n)) _ , },
  { classical,
    exact indep_setsₖ_pi_Union_Inter_of_disjoint h_indep hST, },
end

lemma indepₖ_supr_of_directed_le {m : ι → measurable_space Ω}
  [∀ a, is_probability_measure (κ a)]
  (h_indep : ∀ i, indepₖ (m i) m₂ κ μ) (h_le : ∀ i, m i ≤ m₀) (h_le' : m₂ ≤ m₀)
  (hm : directed (≤) m) :
  indepₖ (⨆ i, m i) m₂ κ μ :=
begin
  let p : ι → set (set Ω) := λ n, {t | measurable_set[m n] t},
  have hp : ∀ n, is_pi_system (p n) := λ n, @is_pi_system_measurable_set Ω (m n),
  have h_gen_n : ∀ n, m n = generate_from (p n),
    from λ n, (@generate_from_measurable_set Ω (m n)).symm,
  have hp_supr_pi : is_pi_system (⋃ n, p n) := is_pi_system_Union_of_directed_le p hp hm,
  let p' := {t : set Ω | measurable_set[m₂] t},
  have hp'_pi : is_pi_system p' := @is_pi_system_measurable_set Ω m₂,
  have h_gen' : m₂ = generate_from p' := (@generate_from_measurable_set Ω m₂).symm,
  -- the π-systems defined are independent
  have h_pi_system_indep : indep_setsₖ (⋃ n, p n) p' κ μ,
  { refine indep_setsₖ.Union _,
    simp_rw [h_gen_n, h_gen'] at h_indep,
    exact λ n, (h_indep n).indep_setsₖ, },
  -- now go from π-systems to σ-algebras
  refine indep_setsₖ.indepₖ (supr_le h_le) h_le' hp_supr_pi hp'_pi _ h_gen' h_pi_system_indep,
  exact (generate_from_Union_measurable_set _).symm,
end

lemma Indep_setₖ.indepₖ_generate_from_lt [preorder ι] [∀ a, is_probability_measure (κ a)]
  {s : ι → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : Indep_setₖ s κ μ) (i : ι) :
  indepₖ (generate_from {s i}) (generate_from {t | ∃ j < i, s j = t}) κ μ :=
begin
  convert hs.indepₖ_generate_from_of_disjoint hsm {i} {j | j < i}
    (set.disjoint_singleton_left.mpr (lt_irrefl _)),
  simp only [set.mem_singleton_iff, exists_prop, exists_eq_left, set.set_of_eq_eq_singleton'],
end

lemma Indep_setₖ.indepₖ_generate_from_le [linear_order ι] [∀ a, is_probability_measure (κ a)]
  {s : ι → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : Indep_setₖ s κ μ)
  (i : ι) {k : ι} (hk : i < k) :
  indepₖ (generate_from {s k}) (generate_from {t | ∃ j ≤ i, s j = t}) κ μ :=
begin
  convert hs.indepₖ_generate_from_of_disjoint hsm {k} {j | j ≤ i}
    (set.disjoint_singleton_left.mpr hk.not_le),
  simp only [set.mem_singleton_iff, exists_prop, exists_eq_left, set.set_of_eq_eq_singleton'],
end

lemma Indep_setₖ.indepₖ_generate_from_le_nat [∀ a, is_probability_measure (κ a)]
  {s : ℕ → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : Indep_setₖ s κ μ) (n : ℕ):
  indepₖ (generate_from {s (n + 1)}) (generate_from {t | ∃ k ≤ n, s k = t}) κ μ :=
hs.indepₖ_generate_from_le hsm _ n.lt_succ_self

lemma indepₖ_supr_of_monotone [semilattice_sup ι] {m : ι → measurable_space Ω}
  [∀ a, is_probability_measure (κ a)]
  (h_indep : ∀ i, indepₖ (m i) m₂ κ μ) (h_le : ∀ i, m i ≤ m₀) (h_le' : m₂ ≤ m₀) (hm : monotone m) :
  indepₖ (⨆ i, m i) m₂ κ μ :=
indepₖ_supr_of_directed_le h_indep h_le h_le' (monotone.directed_le hm)

lemma indepₖ_supr_of_antitone [semilattice_inf ι] {m : ι → measurable_space Ω}
  [∀ a, is_probability_measure (κ a)]
  (h_indep : ∀ i, indepₖ (m i) m₂ κ μ) (h_le : ∀ i, m i ≤ m₀) (h_le' : m₂ ≤ m₀) (hm : antitone m) :
  indepₖ (⨆ i, m i) m₂ κ μ :=
indepₖ_supr_of_directed_le h_indep h_le h_le' (directed_of_inf hm)

lemma Indep_setsₖ.pi_Union_Inter_of_not_mem {π : ι → set (set Ω)} {a : ι} {S : finset ι}
  (hp_ind : Indep_setsₖ π κ μ) (haS : a ∉ S) :
  indep_setsₖ (pi_Union_Inter π S) (π a) κ μ :=
begin
  rintros t1 t2 ⟨s, hs_mem, ft1, hft1_mem, ht1_eq⟩ ht2_mem_pia,
  rw [finset.coe_subset] at hs_mem,
  classical,
  let f := λ n, ite (n = a) t2 (ite (n ∈ s) (ft1 n) set.univ),
  have h_f_mem : ∀ n ∈ insert a s, f n ∈ π n,
  { intros n hn_mem_insert,
    simp_rw f,
    cases (finset.mem_insert.mp hn_mem_insert) with hn_mem hn_mem,
    { simp [hn_mem, ht2_mem_pia], },
    { have hn_ne_a : n ≠ a, by { rintro rfl, exact haS (hs_mem hn_mem), },
      simp [hn_ne_a, hn_mem, hft1_mem n hn_mem], }, },
  have h_f_mem_pi : ∀ n ∈ s, f n ∈ π n, from λ x hxS, h_f_mem x (by simp [hxS]),
  have h_t1 : t1 = ⋂ n ∈ s, f n,
  { suffices h_forall : ∀ n ∈ s, f n = ft1 n,
    { rw ht1_eq,
      congr' with n x,
      congr' with hns y,
      simp only [(h_forall n hns).symm], },
    intros n hnS,
    have hn_ne_a : n ≠ a, by { rintro rfl, exact haS (hs_mem hnS), },
    simp_rw [f, if_pos hnS, if_neg hn_ne_a], },
  have h_μ_t1 : ∀ᵐ a' ∂μ, κ a' t1 = ∏ n in s, κ a' (f n),
  { filter_upwards [hp_ind s h_f_mem_pi] with a' ha',
    rw [h_t1, ← ha'], },
  have h_t2 : t2 = f a, by { simp_rw [f], simp, },
  have h_μ_inter : ∀ᵐ a' ∂μ, κ a' (t1 ∩ t2) = ∏ n in insert a s, κ a' (f n),
  { have h_t1_inter_t2 : t1 ∩ t2 = ⋂ n ∈ insert a s, f n,
      by rw [h_t1, h_t2, finset.set_bInter_insert, set.inter_comm],
    filter_upwards [hp_ind (insert a s) h_f_mem] with a' ha',
    rw [h_t1_inter_t2, ← ha'], },
  have has : a ∉ s := λ has_mem, haS (hs_mem has_mem),
  filter_upwards [h_μ_t1, h_μ_inter] with a' ha1 ha2,
  rw [ha2, finset.prod_insert has, h_t2, mul_comm, ha1],
end

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem Indep_setsₖ.Indepₖ [∀ a, is_probability_measure (κ a)] (m : ι → measurable_space Ω)
  (h_le : ∀ i, m i ≤ m₀) (π : ι → set (set Ω)) (h_pi : ∀ n, is_pi_system (π n))
  (h_generate : ∀ i, m i = generate_from (π i)) (h_ind : Indep_setsₖ π κ μ) :
  Indepₖ m κ μ :=
begin
  classical,
  refine finset.induction _ _,
  { simp only [finset.not_mem_empty, set.Inter_of_empty, set.Inter_univ, measure_univ,
    finset.prod_empty, eq_self_iff_true, filter.eventually_true, forall_const], },
  intros a S ha_notin_S h_rec f hf_m,
  have hf_m_S : ∀ x ∈ S, measurable_set[m x] (f x) := λ x hx, hf_m x (by simp [hx]),
  let p := pi_Union_Inter π S,
  set m_p := generate_from p with hS_eq_generate,
  have h_indep : indepₖ m_p (m a) κ μ,
  { have hp : is_pi_system p := is_pi_system_pi_Union_Inter π h_pi S,
    have h_le' : ∀ i, generate_from (π i) ≤ m₀ := λ i, (h_generate i).symm.trans_le (h_le i),
    have hm_p : m_p ≤ m₀ := generate_from_pi_Union_Inter_le π h_le' S,
    exact indep_setsₖ.indepₖ hm_p (h_le a) hp (h_pi a) hS_eq_generate (h_generate a)
      (h_ind.pi_Union_Inter_of_not_mem ha_notin_S), },
  have h := h_indep.symm (f a) (⋂ n ∈ S, f n) (hf_m a (finset.mem_insert_self a S)) _,
  { filter_upwards [h_rec hf_m_S, h] with a' ha' h',
    rwa [finset.set_bInter_insert, finset.prod_insert ha_notin_S, ← ha'], },
  { have h_le_p : ∀ i ∈ S, m i ≤ m_p,
    { intros n hn,
      rw [hS_eq_generate, h_generate n],
      exact le_generate_from_pi_Union_Inter S hn, },
    have h_S_f : ∀ i ∈ S, measurable_set[m_p] (f i) := λ i hi, (h_le_p i hi) (f i) (hf_m_S i hi),
    exact S.measurable_set_bInter h_S_f, },
end

end from_pi_systems_to_measurable_spaces

section indep_set
/-! ### Independence of measurable sets

We prove the following equivalences on `indep_setₖ`, for measurable sets `s, t`.
* `indep_setₖ s t κ μ ↔ ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t`,
* `indep_setₖ s t κ μ ↔ indep_setsₖ {s} {t} κ μ`.
-/

variables {mα : measurable_space α} {m₁ m₂ m₀ : measurable_space Ω} {κ : kernel α Ω}
  {μ : measure α} {s t : set Ω} (S T : set (set Ω))

lemma indep_setₖ_iff_indep_setsₖ_singleton (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  [∀ a, is_probability_measure (κ a)] :
  indep_setₖ s t κ μ ↔ indep_setsₖ {s} {t} κ μ :=
⟨indepₖ.indep_setsₖ, λ h, indep_setsₖ.indepₖ
  (generate_from_le (λ u hu, by rwa set.mem_singleton_iff.mp hu))
  (generate_from_le (λ u hu, by rwa set.mem_singleton_iff.mp hu)) (is_pi_system.singleton s)
  (is_pi_system.singleton t) rfl rfl h⟩

lemma indep_setₖ_iff_measure_inter_eq_mul (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  [∀ a, is_probability_measure (κ a)] :
  indep_setₖ s t κ μ ↔ ∀ᵐ a ∂μ, κ a (s ∩ t) = κ a s * κ a t :=
(indep_setₖ_iff_indep_setsₖ_singleton hs_meas ht_meas).trans indep_setsₖ_singleton_iff

lemma indep_setsₖ.indep_setₖ_of_mem (hs : s ∈ S) (ht : t ∈ T)
  (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  [∀ a, is_probability_measure (κ a)]
  (h_indep : indep_setsₖ S T κ μ) :
  indep_setₖ s t κ μ :=
(indep_setₖ_iff_measure_inter_eq_mul hs_meas ht_meas).mpr (h_indep s t hs ht)

lemma indepₖ.indep_setₖ_of_measurable_set (h_indep : indepₖ m₁ m₂ κ μ) {s t : set Ω}
  (hs : measurable_set[m₁] s) (ht : measurable_set[m₂] t) :
  indep_setₖ s t κ μ :=
begin
  refine λ s' t' hs' ht', h_indep s' t' _ _,
  { refine generate_from_induction (λ u, measurable_set[m₁] u) {s} _ _ _ _ hs',
    { simp only [hs, set.mem_singleton_iff, set.mem_set_of_eq, forall_eq], },
    { exact @measurable_set.empty _ m₁, },
    { exact λ u hu, hu.compl, },
    { exact λ f hf, measurable_set.Union hf, }, },
  { refine generate_from_induction (λ u, measurable_set[m₂] u) {t} _ _ _ _ ht',
    { simp only [ht, set.mem_singleton_iff, set.mem_set_of_eq, forall_eq], },
    { exact @measurable_set.empty _ m₂, },
    { exact λ u hu, hu.compl, },
    { exact λ f hf, measurable_set.Union hf, }, },
end

lemma indepₖ_iff_forall_indep_setₖ (m₁ m₂ : measurable_space Ω) {m0 : measurable_space Ω}
  {mα : measurable_space α} {κ : kernel α Ω} {μ : measure α} :
  indepₖ m₁ m₂ κ μ ↔ ∀ s t, measurable_set[m₁] s → measurable_set[m₂] t → indep_setₖ s t κ μ :=
⟨λ h, λ s t hs ht, h.indep_setₖ_of_measurable_set hs ht,
  λ h s t hs ht, h s t hs ht s t (measurable_set_generate_from (set.mem_singleton s))
    (measurable_set_generate_from (set.mem_singleton t))⟩

end indep_set

section indep_fun

/-! ### Independence of random variables

-/

variables {β β' γ γ' : Type*} {mα : measurable_space α} {mΩ : measurable_space Ω}
  {κ : kernel α Ω} {μ : measure α} {f : Ω → β} {g : Ω → β'}

lemma indep_funₖ_iff_measure_inter_preimage_eq_mul
  {mβ : measurable_space β} {mβ' : measurable_space β'} :
  indep_funₖ f g κ μ
    ↔ ∀ s t, measurable_set s → measurable_set t
      → ∀ᵐ a ∂μ, κ a (f ⁻¹' s ∩ g ⁻¹' t) = κ a (f ⁻¹' s) * κ a (g ⁻¹' t) :=
begin
  split; intro h,
  { refine λ s t hs ht, h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩, },
  { rintros _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩, exact h s t hs ht, },
end

lemma Indep_funₖ_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι → Type*}
  (m : Π x, measurable_space (β x)) (f : Π i, Ω → β i) :
  Indep_funₖ m f κ μ
    ↔ ∀ (S : finset ι) {sets : Π i : ι, set (β i)} (H : ∀ i, i ∈ S → measurable_set[m i] (sets i)),
      ∀ᵐ a ∂μ, κ a (⋂ i ∈ S, (f i) ⁻¹' (sets i)) = ∏ i in S, κ a ((f i) ⁻¹' (sets i)) :=
begin
  refine ⟨λ h S sets h_meas, h _ (λ i hi_mem, ⟨sets i, h_meas i hi_mem, rfl⟩), _⟩,
  intros h S setsΩ h_meas,
  classical,
  let setsβ : (Π i : ι, set (β i)) := λ i,
    dite (i ∈ S) (λ hi_mem, (h_meas i hi_mem).some) (λ _, set.univ),
  have h_measβ : ∀ i ∈ S, measurable_set[m i] (setsβ i),
  { intros i hi_mem,
    simp_rw [setsβ, dif_pos hi_mem],
    exact (h_meas i hi_mem).some_spec.1, },
  have h_preim : ∀ i ∈ S, setsΩ i = (f i) ⁻¹' (setsβ i),
  { intros i hi_mem,
    simp_rw [setsβ, dif_pos hi_mem],
    exact (h_meas i hi_mem).some_spec.2.symm, },
  have h_left_eq : ∀ a, κ a (⋂ i ∈ S, setsΩ i) = κ a (⋂ i ∈ S, (f i) ⁻¹' (setsβ i)),
  { intros a,
    congr' with i x,
    simp only [set.mem_Inter],
    split; intros h hi_mem; specialize h hi_mem,
    { rwa h_preim i hi_mem at h, },
    { rwa h_preim i hi_mem, }, },
  have h_right_eq : ∀ a, (∏ i in S, κ a (setsΩ i)) = ∏ i in S, κ a ((f i) ⁻¹' (setsβ i)),
  { refine λ a, finset.prod_congr rfl (λ i hi_mem, _),
    rw h_preim i hi_mem, },
  filter_upwards [h S h_measβ] with a ha,
  rw [h_left_eq a, h_right_eq a, ha],
end

lemma indep_funₖ_iff_indep_setₖ_preimage {mβ : measurable_space β} {mβ' : measurable_space β'}
  [∀ a, is_probability_measure (κ a)] (hf : measurable f) (hg : measurable g) :
  indep_funₖ f g κ μ ↔
    ∀ s t, measurable_set s → measurable_set t → indep_setₖ (f ⁻¹' s) (g ⁻¹' t) κ μ :=
begin
  refine indep_funₖ_iff_measure_inter_preimage_eq_mul.trans _,
  split; intros h s t hs ht; specialize h s t hs ht,
  { rwa indep_setₖ_iff_measure_inter_eq_mul (hf hs) (hg ht), apply_instance, },
  { rwa ← indep_setₖ_iff_measure_inter_eq_mul (hf hs) (hg ht), apply_instance, },
end

@[symm] lemma indep_funₖ.symm {mβ : measurable_space β} {f g : Ω → β} (hfg : indep_funₖ f g κ μ) :
  indep_funₖ g f κ μ :=
hfg.symm

lemma indep_funₖ.ae_eq {mβ : measurable_space β} {f g f' g' : Ω → β}
  (hfg : indep_funₖ f g κ μ) (hf : ∀ᵐ a ∂μ, f =ᵐ[κ a] f') (hg : ∀ᵐ a ∂μ, g =ᵐ[κ a] g') :
  indep_funₖ f' g' κ μ :=
begin
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩,
  filter_upwards [hf, hg, hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩] with a hf' hg' hfg',
  have h1 : f ⁻¹' A =ᵐ[κ a] f' ⁻¹' A := hf'.fun_comp A,
  have h2 : g ⁻¹' B =ᵐ[κ a] g' ⁻¹' B := hg'.fun_comp B,
  rwa [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)],
end

lemma indep_funₖ.comp {mβ : measurable_space β} {mβ' : measurable_space β'}
  {mγ : measurable_space γ} {mγ' : measurable_space γ'} {φ : β → γ} {ψ : β' → γ'}
  (hfg : indep_funₖ f g κ μ) (hφ : measurable φ) (hψ : measurable ψ) :
  indep_funₖ (φ ∘ f) (ψ ∘ g) κ μ :=
begin
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩,
  apply hfg,
  { exact ⟨φ ⁻¹' A, hφ hA, set.preimage_comp.symm⟩ },
  { exact ⟨ψ ⁻¹' B, hψ hB, set.preimage_comp.symm⟩ }
end

/-- If `f` is a family of mutually independent random variables (`Indep_funₖ m f κ μ`) and `S, T`
are two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
lemma Indep_funₖ.indep_funₖ_finset [∀ a, is_probability_measure (κ a)]
  {ι : Type*} {β : ι → Type*} {m : Π i, measurable_space (β i)}
  {f : Π i, Ω → β i} (S T : finset ι) (hST : disjoint S T) (hf_Indep : Indep_funₖ m f κ μ)
  (hf_meas : ∀ i, measurable (f i)) :
  indep_funₖ (λ a (i : S), f i a) (λ a (i : T), f i a) κ μ :=
begin
  -- We introduce π-systems, build from the π-system of boxes which generates `measurable_space.pi`.
  let πSβ := (set.pi (set.univ : set S) ''
    (set.pi (set.univ : set S) (λ i, {s : set (β i) | measurable_set[m i] s}))),
  let πS := {s : set Ω | ∃ t ∈ πSβ, (λ a (i : S), f i a) ⁻¹' t = s},
  have hπS_pi : is_pi_system πS := is_pi_system_pi.comap (λ a i, f i a),
  have hπS_gen : measurable_space.pi.comap (λ a (i : S), f i a) = generate_from πS,
  { rw [generate_from_pi.symm, comap_generate_from],
    { congr' with s,
      simp only [set.mem_image, set.mem_set_of_eq, exists_prop], },
    { apply_instance } },
  let πTβ := (set.pi (set.univ : set T) ''
    (set.pi (set.univ : set T) (λ i, {s : set (β i) | measurable_set[m i] s}))),
  let πT := {s : set Ω | ∃ t ∈ πTβ, (λ a (i : T), f i a) ⁻¹' t = s},
  have hπT_pi : is_pi_system πT := is_pi_system_pi.comap (λ a i, f i a),
  have hπT_gen : measurable_space.pi.comap (λ a (i : T), f i a) = generate_from πT,
  { rw [generate_from_pi.symm, comap_generate_from],
    { congr' with s,
      simp only [set.mem_image, set.mem_set_of_eq, exists_prop], },
    { apply_instance } },

  -- To prove independence, we prove independence of the generating π-systems.
  refine indep_setsₖ.indepₖ (measurable.comap_le (measurable_pi_iff.mpr (λ i, hf_meas i)))
    (measurable.comap_le (measurable_pi_iff.mpr (λ i, hf_meas i))) hπS_pi hπT_pi hπS_gen hπT_gen _,

  rintros _ _ ⟨s, ⟨sets_s, hs1, hs2⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2⟩, rfl⟩,
  simp only [set.mem_univ_pi, set.mem_set_of_eq] at hs1 ht1,
  rw [← hs2, ← ht2],
  classical,
  let sets_s' : (Π i : ι, set (β i)) := λ i, dite (i ∈ S) (λ hi, sets_s ⟨i, hi⟩) (λ _, set.univ),
  have h_sets_s'_eq : ∀ {i} (hi : i ∈ S), sets_s' i = sets_s ⟨i, hi⟩,
  { intros i hi, simp_rw [sets_s', dif_pos hi], },
  have h_sets_s'_univ : ∀ {i} (hi : i ∈ T), sets_s' i = set.univ,
  { intros i hi, simp_rw [sets_s', dif_neg (finset.disjoint_right.mp hST hi)], },
  let sets_t' : (Π i : ι, set (β i)) := λ i, dite (i ∈ T) (λ hi, sets_t ⟨i, hi⟩) (λ _, set.univ),
  have h_sets_t'_univ : ∀ {i} (hi : i ∈ S), sets_t' i = set.univ,
  { intros i hi, simp_rw [sets_t', dif_neg (finset.disjoint_left.mp hST hi)], },
  have h_meas_s' : ∀ i ∈ S, measurable_set (sets_s' i),
  { intros i hi, rw h_sets_s'_eq hi, exact hs1 _, },
  have h_meas_t' : ∀ i ∈ T, measurable_set (sets_t' i),
  { intros i hi, simp_rw [sets_t', dif_pos hi], exact ht1 _, },
  have h_eq_inter_S : (λ (ω : Ω) (i : ↥S), f ↑i ω) ⁻¹' set.pi set.univ sets_s
    = ⋂ i ∈ S, (f i) ⁻¹' (sets_s' i),
  { ext1 x,
    simp only [set.mem_preimage, set.mem_univ_pi, set.mem_Inter],
    split; intro h,
    { intros i hi, rw [h_sets_s'_eq hi], exact h ⟨i, hi⟩, },
    { rintros ⟨i, hi⟩, specialize h i hi, rw [h_sets_s'_eq hi] at h, exact h, }, },
  have h_eq_inter_T : (λ (ω : Ω) (i : ↥T), f ↑i ω) ⁻¹' set.pi set.univ sets_t
    = ⋂ i ∈ T, (f i) ⁻¹' (sets_t' i),
  { ext1 x,
    simp only [set.mem_preimage, set.mem_univ_pi, set.mem_Inter],
    split; intro h,
    { intros i hi, simp_rw [sets_t', dif_pos hi], exact h ⟨i, hi⟩, },
    { rintros ⟨i, hi⟩, specialize h i hi, simp_rw [sets_t', dif_pos hi] at h, exact h, }, },
  rw Indep_funₖ_iff_measure_inter_preimage_eq_mul at hf_Indep,
  have h_Inter_inter : (⋂ i ∈ S, (f i) ⁻¹' (sets_s' i)) ∩ (⋂ i ∈ T, (f i) ⁻¹' (sets_t' i))
    = ⋂ i ∈ (S ∪ T), (f i) ⁻¹' (sets_s' i ∩ sets_t' i),
  { ext1 x,
    simp only [set.mem_inter_iff, set.mem_Inter, set.mem_preimage, finset.mem_union],
    split; intro h,
    { intros i hi,
      cases hi,
      { rw h_sets_t'_univ hi, exact ⟨h.1 i hi, set.mem_univ _⟩, },
      { rw h_sets_s'_univ hi, exact ⟨set.mem_univ _, h.2 i hi⟩, }, },
    { exact ⟨λ i hi, (h i (or.inl hi)).1, λ i hi, (h i (or.inr hi)).2⟩, }, },
  have h_meas_inter : ∀ i ∈ S ∪ T, measurable_set (sets_s' i ∩ sets_t' i),
  { intros i hi_mem,
    rw finset.mem_union at hi_mem,
    cases hi_mem,
    { rw [h_sets_t'_univ hi_mem, set.inter_univ], exact h_meas_s' i hi_mem, },
    { rw [h_sets_s'_univ hi_mem, set.univ_inter], exact h_meas_t' i hi_mem, }, },
  filter_upwards [hf_Indep S h_meas_s', hf_Indep T h_meas_t', hf_Indep (S ∪ T) h_meas_inter]
    with a h_indepS h_indepT h_indepST,
  rw [h_eq_inter_S, h_eq_inter_T, h_indepS, h_indepT, h_Inter_inter, h_indepST,
    finset.prod_union hST],
  congr' 1,
  { refine finset.prod_congr rfl (λ i hi, _),
    rw [h_sets_t'_univ hi, set.inter_univ], },
  { refine finset.prod_congr rfl (λ i hi, _),
    rw [h_sets_s'_univ hi, set.univ_inter], },
end

lemma Indep_funₖ.indep_funₖ_prod [∀ a, is_probability_measure (κ a)]
  {ι : Type*} {β : ι → Type*} {m : Π i, measurable_space (β i)}
  {f : Π i, Ω → β i} (hf_Indep : Indep_funₖ m f κ μ) (hf_meas : ∀ i, measurable (f i))
  (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
  indep_funₖ (λ a, (f i a, f j a)) (f k) κ μ :=
begin
  classical,
  have h_right : f k = (λ p : (Π j : ({k} : finset ι), β j), p ⟨k, finset.mem_singleton_self k⟩)
    ∘ (λ a (j : ({k} : finset ι)), f j a) := rfl,
  have h_meas_right : measurable
      (λ p : (Π j : ({k} : finset ι), β j), p ⟨k, finset.mem_singleton_self k⟩),
    from measurable_pi_apply ⟨k, finset.mem_singleton_self k⟩,
  let s : finset ι := {i, j},
  have h_left : (λ ω, (f i ω, f j ω))
    = (λ p : (Π l : s, β l), (p ⟨i, finset.mem_insert_self i _⟩,
        p ⟨j, finset.mem_insert_of_mem (finset.mem_singleton_self _)⟩))
      ∘ (λ a (j : s), f j a),
  { ext1 a,
    simp only [prod.mk.inj_iff],
    split; refl, },
  have h_meas_left : measurable (λ p : (Π l : s, β l), (p ⟨i, finset.mem_insert_self i _⟩,
      p ⟨j, finset.mem_insert_of_mem (finset.mem_singleton_self _)⟩)),
    from measurable.prod (measurable_pi_apply ⟨i, finset.mem_insert_self i {j}⟩)
      (measurable_pi_apply ⟨j, finset.mem_insert_of_mem (finset.mem_singleton_self j)⟩),
  rw [h_left, h_right],
  refine (hf_Indep.indep_funₖ_finset s {k} _ hf_meas).comp h_meas_left h_meas_right,
  rw finset.disjoint_singleton_right,
  simp only [finset.mem_insert, finset.mem_singleton, not_or_distrib],
  exact ⟨hik.symm, hjk.symm⟩,
end

@[to_additive]
lemma Indep_funₖ.mul [∀ a, is_probability_measure (κ a)]
  {ι : Type*} {β : Type*} {m : measurable_space β} [has_mul β] [has_measurable_mul₂ β]
  {f : ι → Ω → β} (hf_Indep : Indep_funₖ (λ _, m) f κ μ) (hf_meas : ∀ i, measurable (f i))
  (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
  indep_funₖ (f i * f j) (f k) κ μ :=
begin
  have : indep_funₖ (λ ω, (f i ω, f j ω)) (f k) κ μ := hf_Indep.indep_funₖ_prod hf_meas i j k hik hjk,
  change indep_funₖ ((λ p : β × β, p.fst * p.snd) ∘ (λ ω, (f i ω, f j ω))) (id ∘ (f k)) κ μ,
  exact indep_funₖ.comp this (measurable_fst.mul measurable_snd) measurable_id,
end

@[to_additive]
lemma Indep_funₖ.indep_funₖ_finset_prod_of_not_mem [∀ a, is_probability_measure (κ a)]
  {ι : Type*} {β : Type*} {m : measurable_space β} [comm_monoid β] [has_measurable_mul₂ β]
  {f : ι → Ω → β} (hf_Indep : Indep_funₖ (λ _, m) f κ μ) (hf_meas : ∀ i, measurable (f i))
  {s : finset ι} {i : ι} (hi : i ∉ s) :
  indep_funₖ (∏ j in s, f j) (f i) κ μ :=
begin
  classical,
  have h_right : f i = (λ p : (Π j : ({i} : finset ι), β), p ⟨i, finset.mem_singleton_self i⟩)
    ∘ (λ a (j : ({i} : finset ι)), f j a) := rfl,
  have h_meas_right : measurable
      (λ p : (Π j : ({i} : finset ι), β), p ⟨i, finset.mem_singleton_self i⟩),
    from measurable_pi_apply ⟨i, finset.mem_singleton_self i⟩,
  have h_left : (∏ j in s, f j) = (λ p : (Π j : s, β), ∏ j, p j) ∘ (λ a (j : s), f j a),
  { ext1 a,
    simp only [function.comp_app],
    have : (∏ (j : ↥s), f ↑j a) = (∏ (j : ↥s), f ↑j) a, by rw finset.prod_apply,
    rw [this, finset.prod_coe_sort], },
  have h_meas_left : measurable (λ p : (Π j : s, β), ∏ j, p j),
    from finset.univ.measurable_prod (λ (j : ↥s) (H : j ∈ finset.univ), measurable_pi_apply j),
  rw [h_left, h_right],
  exact (hf_Indep.indep_funₖ_finset s {i} (finset.disjoint_singleton_left.mpr hi).symm hf_meas).comp
    h_meas_left h_meas_right,
end

@[to_additive]
lemma Indep_funₖ.indep_funₖ_prod_range_succ [∀ a, is_probability_measure (κ a)]
  {β : Type*} {m : measurable_space β} [comm_monoid β] [has_measurable_mul₂ β]
  {f : ℕ → Ω → β} (hf_Indep : Indep_funₖ (λ _, m) f κ μ) (hf_meas : ∀ i, measurable (f i))
  (n : ℕ) :
  indep_funₖ (∏ j in finset.range n, f j) (f n) κ μ :=
hf_Indep.indep_funₖ_finset_prod_of_not_mem hf_meas finset.not_mem_range_self

lemma Indep_setₖ.Indep_funₖ_indicator [has_zero β] [has_one β] {m : measurable_space β}
  {s : ι → set Ω} (hs : Indep_setₖ s κ μ) :
  Indep_funₖ (λ n, m) (λ n, (s n).indicator (λ ω, 1)) κ μ :=
begin
  classical,
  rw Indep_funₖ_iff_measure_inter_preimage_eq_mul,
  rintro S π hπ,
  simp_rw set.indicator_const_preimage_eq_union,
  refine @hs S (λ i, ite (1 ∈ π i) (s i) ∅ ∪ ite ((0 : β) ∈ π i) (s i)ᶜ ∅) (λ i hi, _),
  have hsi : measurable_set[generate_from {s i}] (s i),
    from measurable_set_generate_from (set.mem_singleton _),
  refine measurable_set.union (measurable_set.ite' (λ _, hsi) (λ _, _))
    (measurable_set.ite' (λ _, hsi.compl) (λ _, _)),
  { exact @measurable_set.empty _ (generate_from {s i}), },
  { exact @measurable_set.empty _ (generate_from {s i}), },
end

end indep_fun

end probability_theory
