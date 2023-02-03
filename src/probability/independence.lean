/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.constructions.pi

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → measurable_space Ω` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `measurable_space.comap f m`.

## Main statements

* `Indep_sets.Indep`: if π-systems are independent as sets of sets, then the
  measurable space structures they generate are independent.
* `indep_sets.indep`: variant with two π-systems.
* `measure_zero_or_one_of_measurable_set_limsup_at_top`: Kolmogorov's 0-1 law. Any set which is
  measurable with respect to the tail σ-algebra `limsup s at_top` of an independent sequence of
  σ-algebras `s` has probability 0 or 1.

## Implementation notes

We provide one main definition of independence:
* `Indep_sets`: independence of a family of sets of sets `pi : ι → set (set Ω)`.
Three other independence notions are defined using `Indep_sets`:
* `Indep`: independence of a family of measurable space structures `m : ι → measurable_space Ω`,
* `Indep_set`: independence of a family of sets `s : ι → set Ω`,
* `Indep_fun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), measurable_space (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without a capital letter, for example `indep_fun` is the version of `Indep_fun`
for two functions.

The definition of independence for `Indep_sets` uses finite sets (`finset`). An alternative and
equivalent way of defining independence would have been to use countable sets.
TODO: prove that equivalence.

Most of the definitions and lemma in this file list all variables instead of using the `variables`
keyword at the beginning of a section, for example
`lemma indep.symm {Ω} {m₁ m₂ : measurable_space Ω} [measurable_space Ω] {μ : measure Ω} ...` .
This is intentional, to be able to control the order of the `measurable_space` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`[measurable_space Ω]`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
Part A, Chapter 4.
-/

open measure_theory measurable_space
open_locale big_operators measure_theory ennreal

namespace probability_theory

variables {Ω ι : Type*}

section definitions

/-- A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def Indep_sets [measurable_space Ω] (π : ι → set (set Ω)) (μ : measure Ω . volume_tac) :
  Prop :=
∀ (s : finset ι) {f : ι → set Ω} (H : ∀ i, i ∈ s → f i ∈ π i), μ (⋂ i ∈ s, f i) = ∏ i in s, μ (f i)

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep_sets [measurable_space Ω] (s1 s2 : set (set Ω)) (μ : measure Ω . volume_tac) : Prop :=
∀ t1 t2 : set Ω, t1 ∈ s1 → t2 ∈ s2 → μ (t1 ∩ t2) = μ t1 * μ t2

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → measurable_space Ω` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def Indep (m : ι → measurable_space Ω) [measurable_space Ω] (μ : measure Ω . volume_tac) :
  Prop :=
Indep_sets (λ x, {s | measurable_set[m x] s}) μ

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep (m₁ m₂ : measurable_space Ω) [measurable_space Ω] (μ : measure Ω . volume_tac) :
  Prop :=
indep_sets {s | measurable_set[m₁] s} {s | measurable_set[m₂] s} μ

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def Indep_set [measurable_space Ω] (s : ι → set Ω) (μ : measure Ω . volume_tac) : Prop :=
Indep (λ i, generate_from {s i}) μ

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def indep_set [measurable_space Ω] (s t : set Ω) (μ : measure Ω . volume_tac) : Prop :=
indep (generate_from {s}) (generate_from {t}) μ

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def Indep_fun [measurable_space Ω] {β : ι → Type*} (m : Π (x : ι), measurable_space (β x))
  (f : Π (x : ι), Ω → β x) (μ : measure Ω . volume_tac) : Prop :=
Indep (λ x, measurable_space.comap (f x) (m x)) μ

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def indep_fun {β γ} [measurable_space Ω] [mβ : measurable_space β] [mγ : measurable_space γ]
  (f : Ω → β) (g : Ω → γ) (μ : measure Ω . volume_tac) : Prop :=
indep (measurable_space.comap f mβ) (measurable_space.comap g mγ) μ

end definitions

section indep

@[symm] lemma indep_sets.symm {s₁ s₂ : set (set Ω)} [measurable_space Ω] {μ : measure Ω}
  (h : indep_sets s₁ s₂ μ) :
  indep_sets s₂ s₁ μ :=
by { intros t1 t2 ht1 ht2, rw [set.inter_comm, mul_comm], exact h t2 t1 ht2 ht1, }

@[symm] lemma indep.symm {m₁ m₂ : measurable_space Ω} [measurable_space Ω] {μ : measure Ω}
  (h : indep m₁ m₂ μ) :
  indep m₂ m₁ μ :=
indep_sets.symm h

lemma indep_bot_right (m' : measurable_space Ω) {m : measurable_space Ω}
  {μ : measure Ω} [is_probability_measure μ] :
  indep m' ⊥ μ :=
begin
  intros s t hs ht,
  rw [set.mem_set_of_eq, measurable_space.measurable_set_bot_iff] at ht,
  cases ht,
  { rw [ht, set.inter_empty, measure_empty, mul_zero], },
  { rw [ht, set.inter_univ, measure_univ, mul_one], },
end

lemma indep_bot_left (m' : measurable_space Ω) {m : measurable_space Ω}
  {μ : measure Ω} [is_probability_measure μ] :
  indep ⊥ m' μ :=
(indep_bot_right m').symm

lemma indep_set_empty_right {m : measurable_space Ω} {μ : measure Ω} [is_probability_measure μ]
  (s : set Ω) :
  indep_set s ∅ μ :=
by { simp only [indep_set, generate_from_singleton_empty], exact indep_bot_right _, }

lemma indep_set_empty_left {m : measurable_space Ω} {μ : measure Ω} [is_probability_measure μ]
  (s : set Ω) :
  indep_set ∅ s μ :=
(indep_set_empty_right s).symm

lemma indep_sets_of_indep_sets_of_le_left {s₁ s₂ s₃: set (set Ω)} [measurable_space Ω]
  {μ : measure Ω} (h_indep : indep_sets s₁ s₂ μ) (h31 : s₃ ⊆ s₁) :
  indep_sets s₃ s₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (set.mem_of_subset_of_mem h31 ht1) ht2

lemma indep_sets_of_indep_sets_of_le_right {s₁ s₂ s₃: set (set Ω)} [measurable_space Ω]
  {μ : measure Ω} (h_indep : indep_sets s₁ s₂ μ) (h32 : s₃ ⊆ s₂) :
  indep_sets s₁ s₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (set.mem_of_subset_of_mem h32 ht2)

lemma indep_of_indep_of_le_left {m₁ m₂ m₃: measurable_space Ω} [measurable_space Ω]
  {μ : measure Ω} (h_indep : indep m₁ m₂ μ) (h31 : m₃ ≤ m₁) :
  indep m₃ m₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (h31 _ ht1) ht2

lemma indep_of_indep_of_le_right {m₁ m₂ m₃: measurable_space Ω} [measurable_space Ω]
  {μ : measure Ω} (h_indep : indep m₁ m₂ μ) (h32 : m₃ ≤ m₂) :
  indep m₁ m₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (h32 _ ht2)

lemma indep_sets.union [measurable_space Ω] {s₁ s₂ s' : set (set Ω)} {μ : measure Ω}
  (h₁ : indep_sets s₁ s' μ) (h₂ : indep_sets s₂ s' μ) :
  indep_sets (s₁ ∪ s₂) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  cases (set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂,
  { exact h₁ t1 t2 ht1₁ ht2, },
  { exact h₂ t1 t2 ht1₂ ht2, },
end

@[simp] lemma indep_sets.union_iff [measurable_space Ω] {s₁ s₂ s' : set (set Ω)}
  {μ : measure Ω} :
  indep_sets (s₁ ∪ s₂) s' μ ↔ indep_sets s₁ s' μ ∧ indep_sets s₂ s' μ :=
⟨λ h, ⟨indep_sets_of_indep_sets_of_le_left h (set.subset_union_left s₁ s₂),
    indep_sets_of_indep_sets_of_le_left h (set.subset_union_right s₁ s₂)⟩,
  λ h, indep_sets.union h.left h.right⟩

lemma indep_sets.Union [measurable_space Ω] {s : ι → set (set Ω)} {s' : set (set Ω)}
  {μ : measure Ω} (hyp : ∀ n, indep_sets (s n) s' μ) :
  indep_sets (⋃ n, s n) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  rw set.mem_Union at ht1,
  cases ht1 with n ht1,
  exact hyp n t1 t2 ht1 ht2,
end

lemma indep_sets.bUnion [measurable_space Ω] {s : ι → set (set Ω)} {s' : set (set Ω)}
  {μ : measure Ω} {u : set ι} (hyp : ∀ n ∈ u, indep_sets (s n) s' μ) :
  indep_sets (⋃ n ∈ u, s n) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  simp_rw set.mem_Union at ht1,
  rcases ht1 with ⟨n, hpn, ht1⟩,
  exact hyp n hpn t1 t2 ht1 ht2,
end

lemma indep_sets.inter [measurable_space Ω] {s₁ s' : set (set Ω)} (s₂ : set (set Ω))
  {μ : measure Ω} (h₁ : indep_sets s₁ s' μ) :
  indep_sets (s₁ ∩ s₂) s' μ :=
λ t1 t2 ht1 ht2, h₁ t1 t2 ((set.mem_inter_iff _ _ _).mp ht1).left ht2

lemma indep_sets.Inter [measurable_space Ω] {s : ι → set (set Ω)} {s' : set (set Ω)}
  {μ : measure Ω} (h : ∃ n, indep_sets (s n) s' μ) :
  indep_sets (⋂ n, s n) s' μ :=
by {intros t1 t2 ht1 ht2, cases h with n h, exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2 }

lemma indep_sets.bInter [measurable_space Ω] {s : ι → set (set Ω)} {s' : set (set Ω)}
  {μ : measure Ω} {u : set ι} (h : ∃ n ∈ u, indep_sets (s n) s' μ) :
  indep_sets (⋂ n ∈ u, s n) s' μ :=
begin
  intros t1 t2 ht1 ht2,
  rcases h with ⟨n, hn, h⟩,
  exact h t1 t2 (set.bInter_subset_of_mem hn ht1) ht2,
end

lemma indep_sets_singleton_iff [measurable_space Ω] {s t : set Ω} {μ : measure Ω} :
  indep_sets {s} {t} μ ↔ μ (s ∩ t) = μ s * μ t :=
⟨λ h, h s t rfl rfl,
  λ h s1 t1 hs1 ht1, by rwa [set.mem_singleton_iff.mp hs1, set.mem_singleton_iff.mp ht1]⟩

end indep

/-! ### Deducing `indep` from `Indep` -/
section from_Indep_to_indep

lemma Indep_sets.indep_sets {s : ι → set (set Ω)} [measurable_space Ω] {μ : measure Ω}
  (h_indep : Indep_sets s μ) {i j : ι} (hij : i ≠ j) :
  indep_sets (s i) (s j) μ :=
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
  have h_prod : (∏ (t : ι) in ({i, j} : finset ι), μ (ite (t = i) t₁ t₂))
      = μ (ite (i = i) t₁ t₂) * μ (ite (j = i) t₁ t₂),
    by simp only [hij, finset.prod_singleton, finset.prod_insert, not_false_iff,
      finset.mem_singleton],
  rw h1,
  nth_rewrite 1 h2,
  nth_rewrite 3 h2,
  rw [← h_inter, ← h_prod, h_indep {i, j} hf_m],
end

lemma Indep.indep {m : ι → measurable_space Ω} [measurable_space Ω] {μ : measure Ω}
  (h_indep : Indep m μ) {i j : ι} (hij : i ≠ j) :
  indep (m i) (m j) μ :=
begin
  change indep_sets ((λ x, measurable_set[m x]) i) ((λ x, measurable_set[m x]) j) μ,
  exact Indep_sets.indep_sets h_indep hij,
end

lemma Indep_fun.indep_fun {m₀ : measurable_space Ω} {μ : measure Ω} {β : ι → Type*}
  {m : Π x, measurable_space (β x)} {f : Π i, Ω → β i} (hf_Indep : Indep_fun m f μ)
  {i j : ι} (hij : i ≠ j) :
  indep_fun (f i) (f j) μ :=
hf_Indep.indep hij

end from_Indep_to_indep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/

section from_measurable_spaces_to_sets_of_sets
/-! ### Independence of measurable space structures implies independence of generating π-systems -/

lemma Indep.Indep_sets [measurable_space Ω] {μ : measure Ω} {m : ι → measurable_space Ω}
  {s : ι → set (set Ω)} (hms : ∀ n, m n = generate_from (s n))
  (h_indep : Indep m μ) :
  Indep_sets s μ :=
λ S f hfs, h_indep S $ λ x hxS,
  ((hms x).symm ▸ measurable_set_generate_from (hfs x hxS) : measurable_set[m x] (f x))

lemma indep.indep_sets [measurable_space Ω] {μ : measure Ω} {s1 s2 : set (set Ω)}
  (h_indep : indep (generate_from s1) (generate_from s2) μ) :
  indep_sets s1 s2 μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (measurable_set_generate_from ht1) (measurable_set_generate_from ht2)

end from_measurable_spaces_to_sets_of_sets

section from_pi_systems_to_measurable_spaces
/-! ### Independence of generating π-systems implies independence of measurable space structures -/

private lemma indep_sets.indep_aux {m2 : measurable_space Ω}
  {m : measurable_space Ω} {μ : measure Ω} [is_probability_measure μ] {p1 p2 : set (set Ω)}
  (h2 : m2 ≤ m) (hp2 : is_pi_system p2) (hpm2 : m2 = generate_from p2)
  (hyp : indep_sets p1 p2 μ) {t1 t2 : set Ω} (ht1 : t1 ∈ p1) (ht2m : measurable_set[m2] t2) :
  μ (t1 ∩ t2) = μ t1 * μ t2 :=
begin
  let μ_inter := μ.restrict t1,
  let ν := (μ t1) • μ,
  have h_univ : μ_inter set.univ = ν set.univ,
  by rw [measure.restrict_apply_univ, measure.smul_apply, smul_eq_mul, measure_univ, mul_one],
  haveI : is_finite_measure μ_inter := @restrict.is_finite_measure Ω _ t1 μ ⟨measure_lt_top μ t1⟩,
  rw [set.inter_comm, ← measure.restrict_apply (h2 t2 ht2m)],
  refine ext_on_measurable_space_of_generate_finite m p2 (λ t ht, _) h2 hpm2 hp2 h_univ ht2m,
  have ht2 : measurable_set[m] t,
  { refine h2 _ _,
    rw hpm2,
    exact measurable_set_generate_from ht, },
  rw [measure.restrict_apply ht2, measure.smul_apply, set.inter_comm],
  exact hyp t1 t ht1 ht,
end

lemma indep_sets.indep {m1 m2 : measurable_space Ω} {m : measurable_space Ω}
  {μ : measure Ω} [is_probability_measure μ] {p1 p2 : set (set Ω)} (h1 : m1 ≤ m) (h2 : m2 ≤ m)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hpm1 : m1 = generate_from p1)
  (hpm2 : m2 = generate_from p2) (hyp : indep_sets p1 p2 μ) :
  indep m1 m2 μ :=
begin
  intros t1 t2 ht1 ht2,
  let μ_inter := μ.restrict t2,
  let ν := (μ t2) • μ,
  have h_univ : μ_inter set.univ = ν set.univ,
  by rw [measure.restrict_apply_univ, measure.smul_apply, smul_eq_mul, measure_univ, mul_one],
  haveI : is_finite_measure μ_inter := @restrict.is_finite_measure Ω _ t2 μ ⟨measure_lt_top μ t2⟩,
  rw [mul_comm, ← measure.restrict_apply (h1 t1 ht1)],
  refine ext_on_measurable_space_of_generate_finite m p1 (λ t ht, _) h1 hpm1 hp1 h_univ ht1,
  have ht1 : measurable_set[m] t,
  { refine h1 _ _,
    rw hpm1,
    exact measurable_set_generate_from ht, },
  rw [measure.restrict_apply ht1, measure.smul_apply, smul_eq_mul, mul_comm],
  exact indep_sets.indep_aux h2 hp2 hpm2 hyp ht ht2,
end

lemma indep_sets.indep' {m : measurable_space Ω}
  {μ : measure Ω} [is_probability_measure μ] {p1 p2 : set (set Ω)}
  (hp1m : ∀ s ∈ p1, measurable_set s) (hp2m : ∀ s ∈ p2, measurable_set s)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hyp : indep_sets p1 p2 μ) :
  indep (generate_from p1) (generate_from p2) μ :=
hyp.indep (generate_from_le hp1m) (generate_from_le hp2m) hp1 hp2 rfl rfl

variables {m0 : measurable_space Ω} {μ : measure Ω}

lemma indep_sets_pi_Union_Inter_of_disjoint [is_probability_measure μ]
  {s : ι → set (set Ω)} {S T : set ι}
  (h_indep : Indep_sets s μ) (hST : disjoint S T) :
  indep_sets (pi_Union_Inter s S) (pi_Union_Inter s T) μ :=
begin
  rintros t1 t2 ⟨p1, hp1, f1, ht1_m, ht1_eq⟩ ⟨p2, hp2, f2, ht2_m, ht2_eq⟩,
  classical,
  let g := λ i, ite (i ∈ p1) (f1 i) set.univ ∩ ite (i ∈ p2) (f2 i) set.univ,
  have h_P_inter : μ (t1 ∩ t2) = ∏ n in p1 ∪ p2, μ (g n),
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
    rw [ht1_eq, ht2_eq, h_p1_inter_p2, ← h_indep _ hgm], },
  have h_μg : ∀ n, μ (g n) = (ite (n ∈ p1) (μ (f1 n)) 1) * (ite (n ∈ p2) (μ (f2 n)) 1),
  { intro n,
    simp_rw g,
    split_ifs,
    { exact absurd rfl (set.disjoint_iff_forall_ne.mp hST _ (hp1 h) _ (hp2 h_1)), },
    all_goals { simp only [measure_univ, one_mul, mul_one, set.inter_univ, set.univ_inter], }, },
  simp_rw [h_P_inter, h_μg, finset.prod_mul_distrib,
    finset.prod_ite_mem (p1 ∪ p2) p1 (λ x, μ (f1 x)),
    finset.union_inter_cancel_left, finset.prod_ite_mem (p1 ∪ p2) p2 (λ x, μ (f2 x)),
    finset.union_inter_cancel_right, ht1_eq, ← h_indep p1 ht1_m, ht2_eq, ← h_indep p2 ht2_m],
end

lemma Indep_set.indep_generate_from_of_disjoint [is_probability_measure μ] {s : ι → set Ω}
  (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (S T : set ι) (hST : disjoint S T) :
  indep (generate_from {t | ∃ n ∈ S, s n = t}) (generate_from {t | ∃ k ∈ T, s k = t}) μ :=
begin
  rw [← generate_from_pi_Union_Inter_singleton_left,
    ← generate_from_pi_Union_Inter_singleton_left],
  refine indep_sets.indep'
    (λ t ht, generate_from_pi_Union_Inter_le _ _ _ _ (measurable_set_generate_from ht))
    (λ t ht, generate_from_pi_Union_Inter_le _ _ _ _ (measurable_set_generate_from ht))
    _ _ _,
  { exact λ k, generate_from_le $ λ t ht, (set.mem_singleton_iff.1 ht).symm ▸ hsm k, },
  { exact λ k, generate_from_le $ λ t ht, (set.mem_singleton_iff.1 ht).symm ▸ hsm k, },
  { exact is_pi_system_pi_Union_Inter _ (λ k, is_pi_system.singleton _) _, },
  { exact is_pi_system_pi_Union_Inter _ (λ k, is_pi_system.singleton _) _, },
  { classical,
    exact indep_sets_pi_Union_Inter_of_disjoint (Indep.Indep_sets (λ n, rfl) hs) hST, },
end

lemma indep_supr_of_disjoint [is_probability_measure μ] {m : ι → measurable_space Ω}
  (h_le : ∀ i, m i ≤ m0) (h_indep : Indep m μ) {S T : set ι} (hST : disjoint S T) :
  indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ :=
begin
  refine indep_sets.indep (supr₂_le (λ i _, h_le i)) (supr₂_le (λ i _, h_le i)) _ _
    (generate_from_pi_Union_Inter_measurable_set m S).symm
    (generate_from_pi_Union_Inter_measurable_set m T).symm _,
  { exact is_pi_system_pi_Union_Inter _ (λ n, @is_pi_system_measurable_set Ω (m n)) _, },
  { exact is_pi_system_pi_Union_Inter _ (λ n, @is_pi_system_measurable_set Ω (m n)) _ , },
  { classical,
    exact indep_sets_pi_Union_Inter_of_disjoint h_indep hST, },
end

lemma indep_supr_of_directed_le {Ω} {m : ι → measurable_space Ω}
  {m' m0 : measurable_space Ω} {μ : measure Ω} [is_probability_measure μ]
  (h_indep : ∀ i, indep (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
  (hm : directed (≤) m) :
  indep (⨆ i, m i) m' μ :=
begin
  let p : ι → set (set Ω) := λ n, {t | measurable_set[m n] t},
  have hp : ∀ n, is_pi_system (p n) := λ n, @is_pi_system_measurable_set Ω (m n),
  have h_gen_n : ∀ n, m n = generate_from (p n),
    from λ n, (@generate_from_measurable_set Ω (m n)).symm,
  have hp_supr_pi : is_pi_system (⋃ n, p n) := is_pi_system_Union_of_directed_le p hp hm,
  let p' := {t : set Ω | measurable_set[m'] t},
  have hp'_pi : is_pi_system p' := @is_pi_system_measurable_set Ω m',
  have h_gen' : m' = generate_from p' := (@generate_from_measurable_set Ω m').symm,
  -- the π-systems defined are independent
  have h_pi_system_indep : indep_sets (⋃ n, p n) p' μ,
  { refine indep_sets.Union _,
    simp_rw [h_gen_n, h_gen'] at h_indep,
    exact λ n, (h_indep n).indep_sets, },
  -- now go from π-systems to σ-algebras
  refine indep_sets.indep (supr_le h_le) h_le' hp_supr_pi hp'_pi _ h_gen' h_pi_system_indep,
  exact (generate_from_Union_measurable_set _).symm,
end

lemma Indep_set.indep_generate_from_lt [preorder ι] [is_probability_measure μ]
  {s : ι → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (i : ι) :
  indep (generate_from {s i}) (generate_from {t | ∃ j < i, s j = t}) μ :=
begin
  convert hs.indep_generate_from_of_disjoint hsm {i} {j | j < i}
    (set.disjoint_singleton_left.mpr (lt_irrefl _)),
  simp only [set.mem_singleton_iff, exists_prop, exists_eq_left, set.set_of_eq_eq_singleton'],
end

lemma Indep_set.indep_generate_from_le [linear_order ι] [is_probability_measure μ]
  {s : ι → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ)
  (i : ι) {k : ι} (hk : i < k) :
  indep (generate_from {s k}) (generate_from {t | ∃ j ≤ i, s j = t}) μ :=
begin
  convert hs.indep_generate_from_of_disjoint hsm {k} {j | j ≤ i}
    (set.disjoint_singleton_left.mpr hk.not_le),
  simp only [set.mem_singleton_iff, exists_prop, exists_eq_left, set.set_of_eq_eq_singleton'],
end

lemma Indep_set.indep_generate_from_le_nat [is_probability_measure μ]
  {s : ℕ → set Ω} (hsm : ∀ n, measurable_set (s n)) (hs : Indep_set s μ) (n : ℕ):
  indep (generate_from {s (n + 1)}) (generate_from {t | ∃ k ≤ n, s k = t}) μ :=
hs.indep_generate_from_le hsm _ n.lt_succ_self

lemma indep_supr_of_monotone [semilattice_sup ι] {Ω} {m : ι → measurable_space Ω}
  {m' m0 : measurable_space Ω} {μ : measure Ω} [is_probability_measure μ]
  (h_indep : ∀ i, indep (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0) (hm : monotone m) :
  indep (⨆ i, m i) m' μ :=
indep_supr_of_directed_le h_indep h_le h_le' (monotone.directed_le hm)

lemma indep_supr_of_antitone [semilattice_inf ι] {Ω} {m : ι → measurable_space Ω}
  {m' m0 : measurable_space Ω} {μ : measure Ω} [is_probability_measure μ]
  (h_indep : ∀ i, indep (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0) (hm : antitone m) :
  indep (⨆ i, m i) m' μ :=
indep_supr_of_directed_le h_indep h_le h_le' (directed_of_inf hm)

lemma Indep_sets.pi_Union_Inter_of_not_mem {π : ι → set (set Ω)} {a : ι} {S : finset ι}
  (hp_ind : Indep_sets π μ) (haS : a ∉ S) :
  indep_sets (pi_Union_Inter π S) (π a) μ :=
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
  have h_μ_t1 : μ t1 = ∏ n in s, μ (f n), by rw [h_t1, ← hp_ind s h_f_mem_pi],
  have h_t2 : t2 = f a, by { simp_rw [f], simp, },
  have h_μ_inter : μ (t1 ∩ t2) = ∏ n in insert a s, μ (f n),
  { have h_t1_inter_t2 : t1 ∩ t2 = ⋂ n ∈ insert a s, f n,
      by rw [h_t1, h_t2, finset.set_bInter_insert, set.inter_comm],
    rw [h_t1_inter_t2, ← hp_ind (insert a s) h_f_mem], },
  have has : a ∉ s := λ has_mem, haS (hs_mem has_mem),
  rw [h_μ_inter, finset.prod_insert has, h_t2, mul_comm, h_μ_t1],
end

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem Indep_sets.Indep [is_probability_measure μ] (m : ι → measurable_space Ω)
  (h_le : ∀ i, m i ≤ m0) (π : ι → set (set Ω)) (h_pi : ∀ n, is_pi_system (π n))
  (h_generate : ∀ i, m i = generate_from (π i)) (h_ind : Indep_sets π μ) :
  Indep m μ :=
begin
  classical,
  refine finset.induction _ _,
  { simp only [measure_univ, implies_true_iff, set.Inter_false, set.Inter_univ, finset.prod_empty,
      eq_self_iff_true], },
  intros a S ha_notin_S h_rec f hf_m,
  have hf_m_S : ∀ x ∈ S, measurable_set[m x] (f x) := λ x hx, hf_m x (by simp [hx]),
  rw [finset.set_bInter_insert, finset.prod_insert ha_notin_S, ← h_rec hf_m_S],
  let p := pi_Union_Inter π S,
  set m_p := generate_from p with hS_eq_generate,
  have h_indep : indep m_p (m a) μ,
  { have hp : is_pi_system p := is_pi_system_pi_Union_Inter π h_pi S,
    have h_le' : ∀ i, generate_from (π i) ≤ m0 := λ i, (h_generate i).symm.trans_le (h_le i),
    have hm_p : m_p ≤ m0 := generate_from_pi_Union_Inter_le π h_le' S,
    exact indep_sets.indep hm_p (h_le a) hp (h_pi a) hS_eq_generate (h_generate a)
      (h_ind.pi_Union_Inter_of_not_mem ha_notin_S), },
  refine h_indep.symm (f a) (⋂ n ∈ S, f n) (hf_m a (finset.mem_insert_self a S)) _,
  have h_le_p : ∀ i ∈ S, m i ≤ m_p,
  { intros n hn,
    rw [hS_eq_generate, h_generate n],
    exact le_generate_from_pi_Union_Inter S hn, },
  have h_S_f : ∀ i ∈ S, measurable_set[m_p] (f i) := λ i hi, (h_le_p i hi) (f i) (hf_m_S i hi),
  exact S.measurable_set_bInter h_S_f,
end

end from_pi_systems_to_measurable_spaces

section indep_set
/-! ### Independence of measurable sets

We prove the following equivalences on `indep_set`, for measurable sets `s, t`.
* `indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `indep_set s t μ ↔ indep_sets {s} {t} μ`.
-/

variables {s t : set Ω} (S T : set (set Ω))

lemma indep_set_iff_indep_sets_singleton {m0 : measurable_space Ω}
  (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  (μ : measure Ω . volume_tac) [is_probability_measure μ] :
  indep_set s t μ ↔ indep_sets {s} {t} μ :=
⟨indep.indep_sets, λ h, indep_sets.indep
  (generate_from_le (λ u hu, by rwa set.mem_singleton_iff.mp hu))
  (generate_from_le (λ u hu, by rwa set.mem_singleton_iff.mp hu)) (is_pi_system.singleton s)
  (is_pi_system.singleton t) rfl rfl h⟩

lemma indep_set_iff_measure_inter_eq_mul {m0 : measurable_space Ω}
  (hs_meas : measurable_set s) (ht_meas : measurable_set t)
  (μ : measure Ω . volume_tac) [is_probability_measure μ] :
  indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t :=
(indep_set_iff_indep_sets_singleton hs_meas ht_meas μ).trans indep_sets_singleton_iff

lemma indep_sets.indep_set_of_mem {m0 : measurable_space Ω} (hs : s ∈ S) (ht : t ∈ T)
  (hs_meas : measurable_set s) (ht_meas : measurable_set t) (μ : measure Ω . volume_tac)
  [is_probability_measure μ] (h_indep : indep_sets S T μ) :
  indep_set s t μ :=
(indep_set_iff_measure_inter_eq_mul hs_meas ht_meas μ).mpr (h_indep s t hs ht)

lemma indep.indep_set_of_measurable_set {m₁ m₂ m0 : measurable_space Ω} {μ : measure Ω}
  (h_indep : indep m₁ m₂ μ) {s t : set Ω} (hs : measurable_set[m₁] s) (ht : measurable_set[m₂] t) :
  indep_set s t μ :=
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
    { exact λ f hf, measurable_set.Union hf, },},
end

lemma indep_iff_forall_indep_set (m₁ m₂ : measurable_space Ω) {m0 : measurable_space Ω}
  (μ : measure Ω) :
  indep m₁ m₂ μ ↔ ∀ s t, measurable_set[m₁] s → measurable_set[m₂] t → indep_set s t μ :=
⟨λ h, λ s t hs ht, h.indep_set_of_measurable_set hs ht,
  λ h s t hs ht, h s t hs ht s t (measurable_set_generate_from (set.mem_singleton s))
    (measurable_set_generate_from (set.mem_singleton t))⟩

end indep_set

section indep_fun

/-! ### Independence of random variables

-/

variables {β β' γ γ' : Type*} {mΩ : measurable_space Ω} {μ : measure Ω} {f : Ω → β} {g : Ω → β'}

lemma indep_fun_iff_measure_inter_preimage_eq_mul
  {mβ : measurable_space β} {mβ' : measurable_space β'} :
  indep_fun f g μ
    ↔ ∀ s t, measurable_set s → measurable_set t
      → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) :=
begin
  split; intro h,
  { refine λ s t hs ht, h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩, },
  { rintros _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩, exact h s t hs ht, },
end

lemma Indep_fun_iff_measure_inter_preimage_eq_mul {ι : Type*} {β : ι → Type*}
  (m : Π x, measurable_space (β x)) (f : Π i, Ω → β i) :
  Indep_fun m f μ
    ↔ ∀ (S : finset ι) {sets : Π i : ι, set (β i)} (H : ∀ i, i ∈ S → measurable_set[m i] (sets i)),
      μ (⋂ i ∈ S, (f i) ⁻¹' (sets i)) = ∏ i in S, μ ((f i) ⁻¹' (sets i)) :=
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
  have h_left_eq : μ (⋂ i ∈ S, setsΩ i) = μ (⋂ i ∈ S, (f i) ⁻¹' (setsβ i)),
  { congr' with i x,
    simp only [set.mem_Inter],
    split; intros h hi_mem; specialize h hi_mem,
    { rwa h_preim i hi_mem at h, },
    { rwa h_preim i hi_mem, }, },
  have h_right_eq : (∏ i in S, μ (setsΩ i)) = ∏ i in S, μ ((f i) ⁻¹' (setsβ i)),
  { refine finset.prod_congr rfl (λ i hi_mem, _),
    rw h_preim i hi_mem, },
  rw [h_left_eq, h_right_eq],
  exact h S h_measβ,
end

lemma indep_fun_iff_indep_set_preimage {mβ : measurable_space β} {mβ' : measurable_space β'}
  [is_probability_measure μ] (hf : measurable f) (hg : measurable g) :
  indep_fun f g μ ↔ ∀ s t, measurable_set s → measurable_set t → indep_set (f ⁻¹' s) (g ⁻¹' t) μ :=
begin
  refine indep_fun_iff_measure_inter_preimage_eq_mul.trans _,
  split; intros h s t hs ht; specialize h s t hs ht,
  { rwa indep_set_iff_measure_inter_eq_mul (hf hs) (hg ht) μ, },
  { rwa ← indep_set_iff_measure_inter_eq_mul (hf hs) (hg ht) μ, },
end

@[symm] lemma indep_fun.symm {mβ : measurable_space β} {f g : Ω → β} (hfg : indep_fun f g μ) :
  indep_fun g f μ :=
hfg.symm

lemma indep_fun.ae_eq {mβ : measurable_space β} {f g f' g' : Ω → β}
  (hfg : indep_fun f g μ) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
  indep_fun f' g' μ :=
begin
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩,
  have h1 : f ⁻¹' A =ᵐ[μ] f' ⁻¹' A := hf.fun_comp A,
  have h2 : g ⁻¹' B =ᵐ[μ] g' ⁻¹' B := hg.fun_comp B,
  rw [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)],
  exact hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩
end

lemma indep_fun.comp {mβ : measurable_space β} {mβ' : measurable_space β'}
  {mγ : measurable_space γ} {mγ' : measurable_space γ'} {φ : β → γ} {ψ : β' → γ'}
  (hfg : indep_fun f g μ) (hφ : measurable φ) (hψ : measurable ψ) :
  indep_fun (φ ∘ f) (ψ ∘ g) μ :=
begin
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩,
  apply hfg,
  { exact ⟨φ ⁻¹' A, hφ hA, set.preimage_comp.symm⟩ },
  { exact ⟨ψ ⁻¹' B, hψ hB, set.preimage_comp.symm⟩ }
end

/-- If `f` is a family of mutually independent random variables (`Indep_fun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
lemma Indep_fun.indep_fun_finset [is_probability_measure μ]
  {ι : Type*} {β : ι → Type*} {m : Π i, measurable_space (β i)}
  {f : Π i, Ω → β i} (S T : finset ι) (hST : disjoint S T) (hf_Indep : Indep_fun m f μ)
  (hf_meas : ∀ i, measurable (f i)) :
  indep_fun (λ a (i : S), f i a) (λ a (i : T), f i a) μ :=
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
  refine indep_sets.indep (measurable.comap_le (measurable_pi_iff.mpr (λ i, hf_meas i)))
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
  rw Indep_fun_iff_measure_inter_preimage_eq_mul at hf_Indep,
  rw [h_eq_inter_S, h_eq_inter_T, hf_Indep S h_meas_s', hf_Indep T h_meas_t'],
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
  rw [h_Inter_inter, hf_Indep (S ∪ T)],
  swap, { intros i hi_mem,
    rw finset.mem_union at hi_mem,
    cases hi_mem,
    { rw [h_sets_t'_univ hi_mem, set.inter_univ], exact h_meas_s' i hi_mem, },
    { rw [h_sets_s'_univ hi_mem, set.univ_inter], exact h_meas_t' i hi_mem, }, },
  rw finset.prod_union hST,
  congr' 1,
  { refine finset.prod_congr rfl (λ i hi, _),
    rw [h_sets_t'_univ hi, set.inter_univ], },
  { refine finset.prod_congr rfl (λ i hi, _),
    rw [h_sets_s'_univ hi, set.univ_inter], },
end

lemma Indep_fun.indep_fun_prod [is_probability_measure μ]
  {ι : Type*} {β : ι → Type*} {m : Π i, measurable_space (β i)}
  {f : Π i, Ω → β i} (hf_Indep : Indep_fun m f μ) (hf_meas : ∀ i, measurable (f i))
  (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
  indep_fun (λ a, (f i a, f j a)) (f k) μ :=
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
  refine (hf_Indep.indep_fun_finset s {k} _ hf_meas).comp h_meas_left h_meas_right,
  rw finset.disjoint_singleton_right,
  simp only [finset.mem_insert, finset.mem_singleton, not_or_distrib],
  exact ⟨hik.symm, hjk.symm⟩,
end

@[to_additive]
lemma Indep_fun.mul [is_probability_measure μ]
  {ι : Type*} {β : Type*} {m : measurable_space β} [has_mul β] [has_measurable_mul₂ β]
  {f : ι → Ω → β} (hf_Indep : Indep_fun (λ _, m) f μ) (hf_meas : ∀ i, measurable (f i))
  (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
  indep_fun (f i * f j) (f k) μ :=
begin
  have : indep_fun (λ ω, (f i ω, f j ω)) (f k) μ := hf_Indep.indep_fun_prod hf_meas i j k hik hjk,
  change indep_fun ((λ p : β × β, p.fst * p.snd) ∘ (λ ω, (f i ω, f j ω))) (id ∘ (f k)) μ,
  exact indep_fun.comp this (measurable_fst.mul measurable_snd) measurable_id,
end

@[to_additive]
lemma Indep_fun.indep_fun_finset_prod_of_not_mem [is_probability_measure μ]
  {ι : Type*} {β : Type*} {m : measurable_space β} [comm_monoid β] [has_measurable_mul₂ β]
  {f : ι → Ω → β} (hf_Indep : Indep_fun (λ _, m) f μ) (hf_meas : ∀ i, measurable (f i))
  {s : finset ι} {i : ι} (hi : i ∉ s) :
  indep_fun (∏ j in s, f j) (f i) μ :=
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
  exact (hf_Indep.indep_fun_finset s {i} (finset.disjoint_singleton_left.mpr hi).symm hf_meas).comp
    h_meas_left h_meas_right,
end

@[to_additive]
lemma Indep_fun.indep_fun_prod_range_succ [is_probability_measure μ]
  {β : Type*} {m : measurable_space β} [comm_monoid β] [has_measurable_mul₂ β]
  {f : ℕ → Ω → β} (hf_Indep : Indep_fun (λ _, m) f μ) (hf_meas : ∀ i, measurable (f i))
  (n : ℕ) :
  indep_fun (∏ j in finset.range n, f j) (f n) μ :=
hf_Indep.indep_fun_finset_prod_of_not_mem hf_meas finset.not_mem_range_self

lemma Indep_set.Indep_fun_indicator [has_zero β] [has_one β] {m : measurable_space β}
  {s : ι → set Ω} (hs : Indep_set s μ) :
  Indep_fun (λ n, m) (λ n, (s n).indicator (λ ω, 1)) μ :=
begin
  classical,
  rw Indep_fun_iff_measure_inter_preimage_eq_mul,
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


/-! ### Kolmogorov's 0-1 law

Let `s : ι → measurable_space Ω` be an independent sequence of sub-σ-algebras. Then any set which
is measurable with respect to the tail σ-algebra `limsup s at_top` has probability 0 or 1.
-/

section zero_one_law

variables {m m0 : measurable_space Ω} {μ : measure Ω}

lemma measure_eq_zero_or_one_or_top_of_indep_set_self {t : set Ω} (h_indep : indep_set t t μ) :
  μ t = 0 ∨ μ t = 1 ∨ μ t = ∞ :=
begin
  specialize h_indep t t (measurable_set_generate_from (set.mem_singleton t))
    (measurable_set_generate_from (set.mem_singleton t)),
  by_cases h0 : μ t = 0,
  { exact or.inl h0, },
  by_cases h_top : μ t = ∞,
  { exact or.inr (or.inr h_top), },
  rw [← one_mul (μ (t ∩ t)), set.inter_self, ennreal.mul_eq_mul_right h0 h_top] at h_indep,
  exact or.inr (or.inl h_indep.symm),
end

lemma measure_eq_zero_or_one_of_indep_set_self [is_finite_measure μ] {t : set Ω}
  (h_indep : indep_set t t μ) :
  μ t = 0 ∨ μ t = 1 :=
begin
  have h_0_1_top := measure_eq_zero_or_one_or_top_of_indep_set_self h_indep,
  simpa [measure_ne_top μ] using h_0_1_top,
end

variables [is_probability_measure μ] {s : ι → measurable_space Ω}

open filter

lemma indep_bsupr_compl (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) (t : set ι) :
  indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) μ :=
indep_supr_of_disjoint h_le h_indep disjoint_compl_right

section abstract
variables {α : Type*} {p : set ι → Prop} {f : filter ι} {ns : α → set ι}

/-! We prove a version of Kolmogorov's 0-1 law for the σ-algebra `limsup s f` where `f` is a filter
for which we can define the following two functions:
* `p : set ι → Prop` such that for a set `t`, `p t → tᶜ ∈ f`,
* `ns : α → set ι` a directed sequence of sets which all verify `p` and such that
  `⋃ a, ns a = set.univ`.

For the example of `f = at_top`, we can take `p = bdd_above` and `ns : ι → set ι := λ i, set.Iic i`.
-/

lemma indep_bsupr_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ)
  (hf : ∀ t, p t → tᶜ ∈ f) {t : set ι} (ht : p t) :
  indep (⨆ n ∈ t, s n) (limsup s f) μ :=
begin
  refine indep_of_indep_of_le_right (indep_bsupr_compl h_le h_indep t) _,
  refine Limsup_le_of_le (by is_bounded_default) _,
  simp only [set.mem_compl_iff, eventually_map],
  exact eventually_of_mem (hf t ht) le_supr₂,
end

lemma indep_supr_directed_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ)
  (hf : ∀ t, p t → tᶜ ∈ f) (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) :
  indep (⨆ a, ⨆ n ∈ (ns a), s n) (limsup s f) μ :=
begin
  refine indep_supr_of_directed_le _ _ _ _,
  { exact λ a, indep_bsupr_limsup h_le h_indep hf (hnsp a), },
  { exact λ a, supr₂_le (λ n hn, h_le n), },
  { exact limsup_le_supr.trans (supr_le h_le), },
  { intros a b,
    obtain ⟨c, hc⟩ := hns a b,
    refine ⟨c, _, _⟩; refine supr_mono (λ n, supr_mono' (λ hn, ⟨_, le_rfl⟩)),
    { exact hc.1 hn, },
    { exact hc.2 hn, }, },
end

lemma indep_supr_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
  (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
  indep (⨆ n, s n) (limsup s f) μ :=
begin
  suffices : (⨆ a, ⨆ n ∈ (ns a), s n) = ⨆ n, s n,
  { rw ← this,
    exact indep_supr_directed_limsup h_le h_indep hf hns hnsp, },
  rw supr_comm,
  refine supr_congr (λ n, _),
  have : (⨆ (i : α) (H : n ∈ ns i), s n) = (⨆ (h : ∃ i, n ∈ ns i), s n), by rw supr_exists,
  haveI : nonempty (∃ (i : α), n ∈ ns i) := ⟨hns_univ n⟩,
  rw [this, supr_const],
end

lemma indep_limsup_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
  (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
  indep (limsup s f) (limsup s f) μ :=
indep_of_indep_of_le_left (indep_supr_limsup h_le h_indep hf hns hnsp hns_univ) limsup_le_supr

theorem measure_zero_or_one_of_measurable_set_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ)
  (hf : ∀ t, p t → tᶜ ∈ f) (hns : directed (≤) ns) (hnsp : ∀ a, p (ns a))
  (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : set Ω} (ht_tail : measurable_set[limsup s f] t) :
  μ t = 0 ∨ μ t = 1 :=
measure_eq_zero_or_one_of_indep_set_self
  ((indep_limsup_self h_le h_indep hf hns hnsp hns_univ).indep_set_of_measurable_set
    ht_tail ht_tail)

end abstract

section at_top
variables [semilattice_sup ι] [no_max_order ι] [nonempty ι]

lemma indep_limsup_at_top_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) :
  indep (limsup s at_top) (limsup s at_top) μ :=
begin
  let ns : ι → set ι := set.Iic,
  have hnsp : ∀ i, bdd_above (ns i) := λ i, bdd_above_Iic,
  refine indep_limsup_self h_le h_indep _ _ hnsp _,
  { simp only [mem_at_top_sets, ge_iff_le, set.mem_compl_iff, bdd_above, upper_bounds,
      set.nonempty],
    rintros t ⟨a, ha⟩,
    obtain ⟨b, hb⟩ : ∃ b, a < b := exists_gt a,
    refine ⟨b, λ c hc hct, _⟩,
    suffices : ∀ i ∈ t, i < c, from lt_irrefl c (this c hct),
    exact λ i hi, (ha hi).trans_lt (hb.trans_le hc), },
  { exact monotone.directed_le (λ i j hij k hki, le_trans hki hij), },
  { exact λ n, ⟨n, le_rfl⟩, },
end

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1.
The tail σ-algebra `limsup s at_top` is the same as `⋂ n, ⋃ i ≥ n, s i`. -/
theorem measure_zero_or_one_of_measurable_set_limsup_at_top (h_le : ∀ n, s n ≤ m0)
  (h_indep : Indep s μ) {t : set Ω} (ht_tail : measurable_set[limsup s at_top] t) :
  μ t = 0 ∨ μ t = 1 :=
measure_eq_zero_or_one_of_indep_set_self
  ((indep_limsup_at_top_self h_le h_indep).indep_set_of_measurable_set ht_tail ht_tail)

end at_top

section at_bot
variables [semilattice_inf ι] [no_min_order ι] [nonempty ι]

lemma indep_limsup_at_bot_self (h_le : ∀ n, s n ≤ m0) (h_indep : Indep s μ) :
  indep (limsup s at_bot) (limsup s at_bot) μ :=
begin
  let ns : ι → set ι := set.Ici,
  have hnsp : ∀ i, bdd_below (ns i) := λ i, bdd_below_Ici,
  refine indep_limsup_self h_le h_indep _ _ hnsp _,
  { simp only [mem_at_bot_sets, ge_iff_le, set.mem_compl_iff, bdd_below, lower_bounds,
      set.nonempty],
    rintros t ⟨a, ha⟩,
    obtain ⟨b, hb⟩ : ∃ b, b < a := exists_lt a,
    refine ⟨b, λ c hc hct, _⟩,
    suffices : ∀ i ∈ t, c < i, from lt_irrefl c (this c hct),
    exact λ i hi, hc.trans_lt (hb.trans_le (ha hi)), },
  { exact directed_of_inf (λ i j hij k hki, hij.trans hki), },
  { exact λ n, ⟨n, le_rfl⟩, },
end

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1. -/
theorem measure_zero_or_one_of_measurable_set_limsup_at_bot (h_le : ∀ n, s n ≤ m0)
  (h_indep : Indep s μ) {t : set Ω} (ht_tail : measurable_set[limsup s at_bot] t) :
  μ t = 0 ∨ μ t = 1 :=
measure_eq_zero_or_one_of_indep_set_self
  ((indep_limsup_at_bot_self h_le h_indep).indep_set_of_measurable_set ht_tail ht_tail)

end at_bot

end zero_one_law

end probability_theory
