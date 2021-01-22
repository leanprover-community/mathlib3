/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne
-/
import measure_theory.measure_space
import algebra.big_operators.intervals
import data.finset.intervals

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → set (set α)` is independent with respect to measure `μ` if for
any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. It will be used
for families of pi_systems.
* A family of measurable spaces (or σ-algebras) is independent if the family of sets of measurable
sets they define is independent. `m : ι → measurable_space α` is independent with
respect to measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
measurable spaces they generate: a set `s` generates the measurable space with measurable sets
`∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
spaces they generate : a function `f` for which we have a measurable space `m` on the codomain
generates `measurable_space.comap f m`.

## Main statements

* TODO: `indep_of_indep_sets`: if π-systems are independent as sets of sets, then the
measurable spaces they generate are independent.
* `indep2_of_indep2_sets`: variant with two π-systems.

## Implementation notes

We provide one main definition of independence:
* `indep_sets`: independence of a family of sets of sets `pi : ι → set (set α)`,
Three other independence notions are defined using `indep_sets`:
* `indep`: independence of a family of measurable spaces `m : ι → measurable_space α`,
* `indep_set`: independence of a family of sets `s : ι → set α`,
* `indep_fun`: independence of a family of functions. For measurable spaces
  `m : Π (x : ι), measurable_space (β x)`, we consider functions `f : Π (x : ι), α → β x`.

Additionally, we provide four corresponding statements for two measurable spaces (resp. sets of
sets, sets, functions) instead of a family.

The definition of independence for `indep_sets` uses finite sets (`finset`): it is a statement of
the form "for all finite sets...". An alternative and equivalent way of defining independence
would have been to use countable sets.
TODO: prove that equivalence.

Most of the definitions and lemma in this file list all variables instead of using the `variables`
keyword at the beginning of a section, for example
`lemma indep2.symm {α} {m₁ m₂ : measurable_space α} [measurable_space α] {μ : measure α} ...` .
This is intentional, to be able to control the order of the `measurable_space` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`[measurable_space α]`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
Part A, Chapter 4.
-/

open measure_theory measurable_space
open_locale big_operators classical

section definitions

/-- A family of sets of sets `π : ι → set (set α)` is independent with respect to measure `μ` if for
any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def indep_sets {α ι} [measurable_space α] (π : ι → set (set α)) (μ : measure α) : Prop :=
∀ (s : finset ι) {f : ι → set α} (H : ∀ i, i ∈ s → f i ∈ π i),
  μ (⋂ i ∈ s, f i) = ∏ i in s, μ (f i)

/-- Two sets of sets `s₁, s₂` are independent with respect to
measure `μ` if for any sets `t₁ ∈ p₁, t₂ ∈ s₂`, `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep2_sets {α} [measurable_space α] (s1 s2 : set (set α)) (μ : measure α) : Prop :=
∀ t1 t2 : set α, t1 ∈ s1 → t2 ∈ s2 → μ (t1 ∩ t2) = μ t1 * μ t2

/-- A family of measurable spaces (or σ-algebras) `m : ι → measurable_space α` is independent with
respect to measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def indep {α ι} (m : ι → measurable_space α) [measurable_space α] (μ : measure α) : Prop :=
indep_sets (λ x, (m x).is_measurable') μ

/-- Two measurable spaces (or σ-algebras) `m₁, m₂` are independent with respect to
measure `μ` if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`, `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep2 {α} (m₁ : measurable_space α) (m₂ : measurable_space α) [measurable_space α]
  (μ : measure α) :
  Prop :=
indep2_sets (m₁.is_measurable') (m₂.is_measurable') μ

/-- A family of sets is independent if the family of measurable spaces they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def indep_set {α ι} [measurable_space α] (s : ι → set α) (μ : measure α) : Prop :=
indep (λ i, generate_from {s i}) μ

/-- Two sets are independent if the two measurable spaces they generate are independent.
For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def indep2_set {α} [measurable_space α] {s t : set α} (μ : measure α) : Prop :=
indep2 (generate_from {s}) (generate_from {t}) μ

/-- A family of functions is independent if the family of measurable spaces they generate is
independent. For a function `f` with codomain having measurable space `m`, the generated measurable
space is `measurable_space.comap f m`. -/
def indep_fun {α ι} [measurable_space α] {β : ι → Type*} (m : Π (x : ι), measurable_space (β x))
  (f : Π (x : ι), α → β x) (μ : measure α) : Prop :=
indep (λ x, measurable_space.comap (f x) (m x)) μ

/-- Two functions are independent if the two measurable spaces they generate are independent.
For a function `f` with codomain having measurable space `m`, the generated measurable
space is `measurable_space.comap f m`. -/
def indep2_fun {α β γ} [measurable_space α] (mβ : measurable_space β) (mγ : measurable_space γ)
  {f : α → β} {g : α → γ} (μ : measure α) : Prop :=
indep2 (measurable_space.comap f mβ) (measurable_space.comap g mγ) μ

end definitions

section indep2

lemma indep2_sets.symm {α} {s₁ s₂ : set (set α)} [measurable_space α] {μ : measure α}
  (h : indep2_sets s₁ s₂ μ) :
  indep2_sets s₂ s₁ μ :=
by {intros t1 t2 ht1 ht2, rw [set.inter_comm, mul_comm], exact h t2 t1 ht2 ht1, }

lemma indep2.symm {α} {m₁ m₂ : measurable_space α} [measurable_space α] {μ : measure α}
  (h : indep2 m₁ m₂ μ) :
  indep2 m₂ m₁ μ :=
indep2_sets.symm h

lemma indep2_sets_of_indep2_sets_of_le_left {α} {s₁ s₂ s₃: set (set α)} [measurable_space α]
  {μ : measure α} (h_indep : indep2_sets s₁ s₂ μ) (h31 : s₃ ⊆ s₁) :
  indep2_sets s₃ s₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (set.mem_of_subset_of_mem h31 ht1) ht2

lemma indep2_sets_of_indep2_sets_of_le_right {α} {s₁ s₂ s₃: set (set α)} [measurable_space α]
  {μ : measure α} (h_indep : indep2_sets s₁ s₂ μ) (h32 : s₃ ⊆ s₂) :
  indep2_sets s₁ s₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (set.mem_of_subset_of_mem h32 ht2)

lemma indep2_of_indep2_of_le_left {α} {m₁ m₂ m₃: measurable_space α} [measurable_space α]
  {μ : measure α} (h_indep : indep2 m₁ m₂ μ) (h31 : m₃ ≤ m₁) :
  indep2 m₃ m₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (h31 _ ht1) ht2

lemma indep2_of_indep2_of_le_right {α} {m₁ m₂ m₃: measurable_space α} [measurable_space α]
  {μ : measure α} (h_indep : indep2 m₁ m₂ μ) (h32 : m₃ ≤ m₂) :
  indep2 m₁ m₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (h32 _ ht2)

lemma indep2_sets.union {α} [measurable_space α] {s₁ s₂ s' : set (set α)} {μ : measure α}
  (h₁ : indep2_sets s₁ s' μ) (h₂ : indep2_sets s₂ s' μ) :
  indep2_sets (s₁ ∪ s₂) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  cases (set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂,
  { exact h₁ t1 t2 ht1₁ ht2, },
  { exact h₂ t1 t2 ht1₂ ht2, },
end

lemma indep2_sets.union_iff {α} [measurable_space α] {s₁ s₂ s' : set (set α)} {μ : measure α} :
  indep2_sets (s₁ ∪ s₂) s' μ ↔ indep2_sets s₁ s' μ ∧ indep2_sets s₂ s' μ :=
⟨λ h, ⟨indep2_sets_of_indep2_sets_of_le_left h (set.subset_union_left s₁ s₂),
    indep2_sets_of_indep2_sets_of_le_left h (set.subset_union_right s₁ s₂)⟩,
  λ h, indep2_sets.union h.left h.right⟩

lemma indep2_sets.Union {α ι} [measurable_space α] {s : ι → set (set α)} {s' : set (set α)}
  {μ : measure α} (hyp : ∀ n, indep2_sets (s n) s' μ) :
  indep2_sets (⋃ n, s n) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  rw set.mem_Union at ht1,
  cases ht1 with n ht1,
  exact hyp n t1 t2 ht1 ht2,
end

lemma indep2_sets.inter {α} [measurable_space α] {s₁ s' : set (set α)} (s₂ : set (set α))
  {μ : measure α} (h₁ : indep2_sets s₁ s' μ) :
  indep2_sets (s₁ ∩ s₂) s' μ :=
λ t1 t2 ht1 ht2, h₁ t1 t2 ((set.mem_inter_iff _ _ _).mp ht1).left ht2

lemma indep2_sets.Inter {α ι} [measurable_space α] {s : ι → set (set α)} {s' : set (set α)}
  {μ : measure α} (h : ∃ n, indep2_sets (s n) s' μ) :
  indep2_sets (⋂ n, s n) s' μ :=
by {intros t1 t2 ht1 ht2, cases h with n h, exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2 }

end indep2

section from_indep_to_indep2

lemma indep2_sets_of_indep_sets {α ι} {m : ι → set (set α)} [measurable_space α] {μ : measure α}
  (h_indep : indep_sets m μ) {i j : ι} (hij : i ≠ j) :
  indep2_sets (m i) (m j) μ :=
begin
  intros t₁ t₂ ht₁ ht₂,
  have hf_m : ∀ (x : ι), x ∈ {i, j} → (ite (x=i) t₁ t₂) ∈ m x,
  { intros x hx,
    cases finset.mem_insert.mp hx with hx hx,
    { simp [hx, ht₁], },
    { simp [finset.mem_singleton.mp hx, hij.symm, ht₂], }, },
  have h1 : t₁ = ite (i = i) t₁ t₂, by simp only [if_true, eq_self_iff_true],
  have h2 : t₂ = ite (j = i) t₁ t₂, by simp only [hij.symm, if_false],
  have h_inter : (⋂ (t : ι) (H : t ∈ ({i, j} : finset ι)), ite (t = i) t₁ t₂)
      = (ite (i = i) t₁ t₂) ∩ (ite (j = i) t₁ t₂),
    by simp only [finset.bInter_singleton, finset.bInter_insert],
  have h_prod : (∏ (t : ι) in ({i, j} : finset ι), μ (ite (t = i) t₁ t₂))
      = μ (ite (i = i) t₁ t₂) * μ (ite (j = i) t₁ t₂),
    by simp only [hij, finset.prod_singleton, finset.prod_insert, not_false_iff,
      finset.mem_singleton],
  rw h1,
  nth_rewrite 1 h2,
  nth_rewrite 3 h2,
  rw [←h_inter, ←h_prod, h_indep {i, j} hf_m],
end

lemma indep2_of_indep {α ι} {m : ι → measurable_space α} [measurable_space α] {μ : measure α}
  (h_indep : indep m μ) {i j : ι} (hij : i ≠ j) :
  indep2 (m i) (m j) μ :=
begin
  change indep2_sets ((λ x, (m x).is_measurable') i) ((λ x, (m x).is_measurable') j) μ,
  exact indep2_sets_of_indep_sets h_indep hij,
end

end from_indep_to_indep2

/-!
### π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/

section from_measurable_spaces_to_sets_of_sets

lemma indep_sets_of_indep {α ι} [measurable_space α] {μ : measure α} {m : ι → measurable_space α}
  {s : ι → set (set α)} (hms : ∀ n, m n = measurable_space.generate_from (s n))
  (h_indep : indep m μ) :
  indep_sets s μ :=
begin
  refine (λ S f hfs, h_indep S (λ x hxS, _)),
  simp_rw hms x,
  exact is_measurable_generate_from (hfs x hxS),
end

lemma indep2_sets_of_indep2 {α} [measurable_space α] {μ : measure α} {s1 s2 : set (set α)}
  (h_indep : indep2 (generate_from s1) (generate_from s2) μ) :
  indep2_sets s1 s2 μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (is_measurable_generate_from ht1) (is_measurable_generate_from ht2)

end from_measurable_spaces_to_sets_of_sets

section from_pi_systems_to_measurable_spaces

private lemma indep2_of_indep2_sets_aux {α} {m2 : measurable_space α}
  {m : measurable_space α} {μ : measure α} [probability_measure μ] {p1 p2 : set (set α)}
  (h2 : m2 ≤ m) (hp2 : is_pi_system p2) (hpm2 : m2 = generate_from p2)
  (hyp : indep2_sets p1 p2 μ) {t1 t2 : set α} (ht1 : t1 ∈ p1) (ht2m : m2.is_measurable' t2) :
  μ (t1 ∩ t2) = μ t1 * μ t2 :=
begin
  let μ_inter := μ.restrict t1,
  let ν := (μ t1) • μ,
  have h_univ : μ_inter set.univ = ν set.univ,
  by rw [measure.restrict_apply_univ, measure.smul_apply, measure_univ, mul_one],
  haveI : finite_measure μ_inter := @restrict.finite_measure α _ t1 μ (measure_lt_top μ t1),
  haveI : finite_measure ν := μ.smul_finite (measure_lt_top μ t1),
  have h_agree : ∀ (t : set α), t ∈ p2 → μ_inter t = ν t,
  { intros t ht,
    have ht2 : m.is_measurable' t,
    { refine h2 _ _,
      rw hpm2,
      exact is_measurable_generate_from ht, },
    rw [measure.restrict_apply ht2, measure.smul_apply, set.inter_comm],
    exact hyp t1 t ht1 ht, },
  have hμν : ∀ (t : set α), m2.is_measurable' t → μ_inter t = ν t,
  from λ t ht, ext_on_measurable_space_of_generate_finite m p2 h_agree h2 hpm2 hp2 h_univ ht,
  rw [set.inter_comm, ←@measure.restrict_apply α _ μ t1 t2 (h2 t2 ht2m)],
  exact hμν t2 ht2m,
end

lemma indep2_of_indep2_sets {α} {m1 m2 : measurable_space α} {m : measurable_space α}
  {μ : measure α} [probability_measure μ] {p1 p2 : set (set α)} (h1 : m1 ≤ m) (h2 : m2 ≤ m)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hpm1 : m1 = generate_from p1)
  (hpm2 : m2 = generate_from p2) (hyp : indep2_sets p1 p2 μ) :
  indep2 m1 m2 μ :=
begin
  intros t1 t2 ht1 ht2,
  let μ_inter := μ.restrict t2,
  let ν := (μ t2) • μ,
  have h_univ : μ_inter set.univ = ν set.univ,
  by rw [measure.restrict_apply_univ, measure.smul_apply, measure_univ, mul_one],
  haveI : finite_measure μ_inter := @restrict.finite_measure α _ t2 μ (measure_lt_top μ t2),
  haveI : finite_measure ν := μ.smul_finite (measure_lt_top μ t2),
  have h_agree : ∀ (t : set α), t ∈ p1 → μ_inter t = ν t,
  { intros t ht,
    have ht1 : m.is_measurable' t,
    { refine h1 _ _,
      rw hpm1,
      exact is_measurable_generate_from ht, },
    rw [measure.restrict_apply ht1, measure.smul_apply, mul_comm],
    exact indep2_of_indep2_sets_aux h2 hp2 hpm2 hyp ht ht2, },
  have hμν : ∀ (t : set α), m1.is_measurable' t → μ_inter t = ν t,
  from λ t ht, ext_on_measurable_space_of_generate_finite m p1 h_agree h1 hpm1 hp1 h_univ ht,
  rw [mul_comm, ←@measure.restrict_apply α _ μ t2 t1 (h1 t1 ht1)],
  exact hμν t1 ht1,
end

end from_pi_systems_to_measurable_spaces
