/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import analysis.specific_limits.basic
import measure_theory.pi_system
import data.countable.basic
import data.fin.vec_notation

/-!
# Outer Measures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An outer measure is a function `μ : set α → ℝ≥0∞`, from the powerset of a type to the extended
nonnegative real numbers that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is monotone;
3. `μ` is countably subadditive. This means that the outer measure of a countable union is at most
   the sum of the outer measure on the individual sets.

Note that we do not need `α` to be measurable to define an outer measure.

The outer measures on a type `α` form a complete lattice.

Given an arbitrary function `m : set α → ℝ≥0∞` that sends `∅` to `0` we can define an outer
measure on `α` that on `s` is defined to be the infimum of `∑ᵢ, m (sᵢ)` for all collections of sets
`sᵢ` that cover `s`. This is the unique maximal outer measure that is at most the given function.
We also define this for functions `m` defined on a subset of `set α`, by treating the function as
having value `∞` outside its domain.

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `outer_measure.bounded_by` is the greatest outer measure that is at most the given function.
  If you know that the given functions sends `∅` to `0`, then `outer_measure.of_function` is a
  special case.
* `caratheodory` is the Carathéodory-measurable space of an outer measure.
* `Inf_eq_of_function_Inf_gen` is a characterization of the infimum of outer measures.
* `induced_outer_measure` is the measure induced by a function on a subset of `set α`

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

outer measure, Carathéodory-measurable, Carathéodory's criterion
-/

noncomputable theory

open set function filter topological_space (second_countable_topology)
open_locale classical big_operators nnreal topology ennreal measure_theory

namespace measure_theory

/-- An outer measure is a countably subadditive monotone function that sends `∅` to `0`. -/
structure outer_measure (α : Type*) :=
(measure_of : set α → ℝ≥0∞)
(empty : measure_of ∅ = 0)
(mono : ∀{s₁ s₂}, s₁ ⊆ s₂ → measure_of s₁ ≤ measure_of s₂)
(Union_nat : ∀(s:ℕ → set α), measure_of (⋃i, s i) ≤ ∑'i, measure_of (s i))

namespace outer_measure

section basic

variables {α β R R' : Type*} {ms : set (outer_measure α)} {m : outer_measure α}

instance : has_coe_to_fun (outer_measure α) (λ _, set α → ℝ≥0∞) := ⟨λ m, m.measure_of⟩

@[simp] lemma measure_of_eq_coe (m : outer_measure α) : m.measure_of = m := rfl

@[simp] theorem empty' (m : outer_measure α) : m ∅ = 0 := m.empty

theorem mono' (m : outer_measure α) {s₁ s₂}
  (h : s₁ ⊆ s₂) : m s₁ ≤ m s₂ := m.mono h

theorem mono_null (m : outer_measure α) {s t} (h : s ⊆ t) (ht : m t = 0) : m s = 0 :=
nonpos_iff_eq_zero.mp $ ht ▸ m.mono' h

lemma pos_of_subset_ne_zero (m : outer_measure α) {a b : set α} (hs : a ⊆ b) (hnz : m a ≠ 0) :
  0 < m b :=
(lt_of_lt_of_le (pos_iff_ne_zero.mpr hnz) (m.mono hs))

protected theorem Union (m : outer_measure α) {β} [countable β] (s : β → set α) :
  m (⋃ i, s i) ≤ ∑' i, m (s i) :=
rel_supr_tsum m m.empty (≤) m.Union_nat s

lemma Union_null [countable β] (m : outer_measure α) {s : β → set α} (h : ∀ i, m (s i) = 0) :
  m (⋃ i, s i) = 0 :=
by simpa [h] using m.Union s

@[simp] lemma Union_null_iff [countable β] (m : outer_measure α) {s : β → set α} :
  m (⋃ i, s i) = 0 ↔ ∀ i, m (s i) = 0 :=
⟨λ h i, m.mono_null (subset_Union _ _) h, m.Union_null⟩

/-- A version of `Union_null_iff` for unions indexed by Props.
TODO: in the long run it would be better to combine this with `Union_null_iff` by
generalising to `Sort`. -/
@[simp] lemma Union_null_iff' (m : outer_measure α) {ι : Prop} {s : ι → set α} :
  m (⋃ i, s i) = 0 ↔ ∀ i, m (s i) = 0 :=
by by_cases i : ι; simp [i]

lemma bUnion_null_iff (m : outer_measure α) {s : set β} (hs : s.countable) {t : β → set α} :
  m (⋃ i ∈ s, t i) = 0 ↔ ∀ i ∈ s, m (t i) = 0 :=
by { haveI := hs.to_encodable, rw [bUnion_eq_Union, Union_null_iff, set_coe.forall'] }

lemma sUnion_null_iff (m : outer_measure α) {S : set (set α)} (hS : S.countable) :
  m (⋃₀ S) = 0 ↔ ∀ s ∈ S, m s = 0 :=
by rw [sUnion_eq_bUnion, m.bUnion_null_iff hS]

protected lemma Union_finset (m : outer_measure α) (s : β → set α) (t : finset β) :
  m (⋃i ∈ t, s i) ≤ ∑ i in t, m (s i) :=
rel_supr_sum m m.empty (≤) m.Union_nat s t

protected lemma union (m : outer_measure α) (s₁ s₂ : set α) :
  m (s₁ ∪ s₂) ≤ m s₁ + m s₂ :=
rel_sup_add m m.empty (≤) m.Union_nat s₁ s₂

/-- If a set has zero measure in a neighborhood of each of its points, then it has zero measure
in a second-countable space. -/
lemma null_of_locally_null [topological_space α] [second_countable_topology α] (m : outer_measure α)
  (s : set α) (hs : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, m u = 0) :
  m s = 0 :=
begin
  choose! u hxu hu₀ using hs,
  obtain ⟨t, ts, t_count, ht⟩ : ∃ t ⊆ s, t.countable ∧ s ⊆ ⋃ x ∈ t, u x :=
    topological_space.countable_cover_nhds_within hxu,
  apply m.mono_null ht,
  exact (m.bUnion_null_iff t_count).2 (λ x hx, hu₀ x (ts hx))
end

/-- If `m s ≠ 0`, then for some point `x ∈ s` and any `t ∈ 𝓝[s] x` we have `0 < m t`. -/
lemma exists_mem_forall_mem_nhds_within_pos [topological_space α] [second_countable_topology α]
  (m : outer_measure α) {s : set α} (hs : m s ≠ 0) :
  ∃ x ∈ s, ∀ t ∈ 𝓝[s] x, 0 < m t :=
begin
  contrapose! hs,
  simp only [nonpos_iff_eq_zero, ← exists_prop] at hs,
  exact m.null_of_locally_null s hs
end

/-- If `s : ι → set α` is a sequence of sets, `S = ⋃ n, s n`, and `m (S \ s n)` tends to zero along
some nontrivial filter (usually `at_top` on `ι = ℕ`), then `m S = ⨆ n, m (s n)`. -/
lemma Union_of_tendsto_zero {ι} (m : outer_measure α) {s : ι → set α}
  (l : filter ι) [ne_bot l] (h0 : tendsto (λ k, m ((⋃ n, s n) \ s k)) l (𝓝 0)) :
  m (⋃ n, s n) = ⨆ n, m (s n) :=
begin
  set S := ⋃ n, s n,
  set M := ⨆ n, m (s n),
  have hsS : ∀ {k}, s k ⊆ S, from λ k, subset_Union _ _,
  refine le_antisymm _ (supr_le $ λ n, m.mono hsS),
  have A : ∀ k, m S ≤ M + m (S \ s k), from λ k,
  calc m S = m (s k ∪ S \ s k) : by rw [union_diff_self, union_eq_self_of_subset_left hsS]
  ... ≤ m (s k) + m (S \ s k) : m.union _ _
  ... ≤ M + m (S \ s k) : add_le_add_right (le_supr _ k) _,
  have B : tendsto (λ k, M + m (S \ s k)) l (𝓝 (M + 0)), from tendsto_const_nhds.add h0,
  rw add_zero at B,
  exact ge_of_tendsto' B A
end

/-- If `s : ℕ → set α` is a monotone sequence of sets such that `∑' k, m (s (k + 1) \ s k) ≠ ∞`,
then `m (⋃ n, s n) = ⨆ n, m (s n)`. -/
lemma Union_nat_of_monotone_of_tsum_ne_top (m : outer_measure α) {s : ℕ → set α}
  (h_mono : ∀ n, s n ⊆ s (n + 1)) (h0 : ∑' k, m (s (k + 1) \ s k) ≠ ∞) :
  m (⋃ n, s n) = ⨆ n, m (s n) :=
begin
  refine m.Union_of_tendsto_zero at_top _,
  refine tendsto_nhds_bot_mono' (ennreal.tendsto_sum_nat_add _ h0) (λ n, _),
  refine (m.mono _).trans (m.Union _),
  /- Current goal: `(⋃ k, s k) \ s n ⊆ ⋃ k, s (k + n + 1) \ s (k + n)` -/
  have h' : monotone s := @monotone_nat_of_le_succ (set α) _ _ h_mono,
  simp only [diff_subset_iff, Union_subset_iff],
  intros i x hx,
  rcases nat.find_x ⟨i, hx⟩ with ⟨j, hj, hlt⟩, clear hx i,
  cases le_or_lt j n with hjn hnj, { exact or.inl (h' hjn hj) },
  have : j - (n + 1) + n + 1 = j,
    by rw [add_assoc, tsub_add_cancel_of_le hnj.nat_succ_le],
  refine or.inr (mem_Union.2 ⟨j - (n + 1), _, hlt _ _⟩),
  { rwa this },
  { rw [← nat.succ_le_iff, nat.succ_eq_add_one, this] }
end

lemma le_inter_add_diff {m : outer_measure α} {t : set α} (s : set α) :
  m t ≤ m (t ∩ s) + m (t \ s) :=
by { convert m.union _ _, rw inter_union_diff t s }

lemma diff_null (m : outer_measure α) (s : set α) {t : set α} (ht : m t = 0) :
  m (s \ t) = m s :=
begin
  refine le_antisymm (m.mono $ diff_subset _ _) _,
  calc m s ≤ m (s ∩ t) + m (s \ t) : le_inter_add_diff _
       ... ≤ m t + m (s \ t)       : add_le_add_right (m.mono $ inter_subset_right _ _) _
       ... = m (s \ t)             : by rw [ht, zero_add]
end

lemma union_null (m : outer_measure α) {s₁ s₂ : set α}
  (h₁ : m s₁ = 0) (h₂ : m s₂ = 0) : m (s₁ ∪ s₂) = 0 :=
by simpa [h₁, h₂] using m.union s₁ s₂

lemma coe_fn_injective : injective (λ (μ : outer_measure α) (s : set α), μ s) :=
λ μ₁ μ₂ h, by { cases μ₁, cases μ₂, congr, exact h }

@[ext] lemma ext {μ₁ μ₂ : outer_measure α} (h : ∀ s, μ₁ s = μ₂ s) : μ₁ = μ₂ :=
coe_fn_injective $ funext h

/-- A version of `measure_theory.outer_measure.ext` that assumes `μ₁ s = μ₂ s` on all *nonempty*
sets `s`, and gets `μ₁ ∅ = μ₂ ∅` from `measure_theory.outer_measure.empty'`. -/
lemma ext_nonempty {μ₁ μ₂ : outer_measure α} (h : ∀ s : set α, s.nonempty → μ₁ s = μ₂ s) :
  μ₁ = μ₂ :=
ext $ λ s, s.eq_empty_or_nonempty.elim (λ he, by rw [he, empty', empty']) (h s)

instance : has_zero (outer_measure α) :=
⟨{ measure_of := λ_, 0,
   empty      := rfl,
   mono       := assume _ _ _, le_refl 0,
   Union_nat  := assume s, zero_le _ }⟩

@[simp] theorem coe_zero : ⇑(0 : outer_measure α) = 0 := rfl

instance : inhabited (outer_measure α) := ⟨0⟩

instance : has_add (outer_measure α) :=
⟨λm₁ m₂,
  { measure_of := λs, m₁ s + m₂ s,
    empty      := show m₁ ∅ + m₂ ∅ = 0, by simp [outer_measure.empty],
    mono       := assume s₁ s₂ h, add_le_add (m₁.mono h) (m₂.mono h),
    Union_nat  := assume s,
      calc m₁ (⋃i, s i) + m₂ (⋃i, s i) ≤
          (∑'i, m₁ (s i)) + (∑'i, m₂ (s i)) :
          add_le_add (m₁.Union_nat s) (m₂.Union_nat s)
        ... = _ : ennreal.tsum_add.symm}⟩

@[simp] theorem coe_add (m₁ m₂ : outer_measure α) : ⇑(m₁ + m₂) = m₁ + m₂ := rfl

theorem add_apply (m₁ m₂ : outer_measure α) (s : set α) : (m₁ + m₂) s = m₁ s + m₂ s := rfl

section has_smul
variables [has_smul R ℝ≥0∞] [is_scalar_tower R ℝ≥0∞ ℝ≥0∞]
variables [has_smul R' ℝ≥0∞] [is_scalar_tower R' ℝ≥0∞ ℝ≥0∞]

instance : has_smul R (outer_measure α) :=
⟨λ c m,
  { measure_of := λ s, c • m s,
    empty      := by rw [←smul_one_mul c (_ : ℝ≥0∞), empty', mul_zero],
    mono       := λ s t h, begin
      rw [←smul_one_mul c (m s), ←smul_one_mul c (m t)],
      exact ennreal.mul_left_mono (m.mono h),
    end,
    Union_nat  := λ s, begin
      simp_rw [←smul_one_mul c (m _), ennreal.tsum_mul_left],
      exact ennreal.mul_left_mono (m.Union _)
    end }⟩

@[simp] lemma coe_smul (c : R) (m : outer_measure α) : ⇑(c • m) = c • m := rfl

lemma smul_apply (c : R) (m : outer_measure α) (s : set α) : (c • m) s = c • m s := rfl

instance [smul_comm_class R R' ℝ≥0∞] : smul_comm_class R R' (outer_measure α) :=
⟨λ _ _ _, ext $ λ _, smul_comm _ _ _⟩

instance [has_smul R R'] [is_scalar_tower R R' ℝ≥0∞] : is_scalar_tower R R' (outer_measure α) :=
⟨λ _ _ _, ext $ λ _, smul_assoc _ _ _⟩

instance [has_smul Rᵐᵒᵖ ℝ≥0∞] [is_central_scalar R ℝ≥0∞] :
  is_central_scalar R (outer_measure α) :=
⟨λ _ _, ext $ λ _, op_smul_eq_smul _ _⟩

end has_smul

instance [monoid R] [mul_action R ℝ≥0∞] [is_scalar_tower R ℝ≥0∞ ℝ≥0∞] :
  mul_action R (outer_measure α) :=
injective.mul_action _ coe_fn_injective coe_smul

instance add_comm_monoid : add_comm_monoid (outer_measure α) :=
injective.add_comm_monoid (show outer_measure α → set α → ℝ≥0∞, from coe_fn)
    coe_fn_injective rfl (λ _ _, rfl) (λ _ _, rfl)

/-- `coe_fn` as an `add_monoid_hom`. -/
@[simps] def coe_fn_add_monoid_hom : outer_measure α →+ (set α → ℝ≥0∞) :=
⟨coe_fn, coe_zero, coe_add⟩

instance [monoid R] [distrib_mul_action R ℝ≥0∞] [is_scalar_tower R ℝ≥0∞ ℝ≥0∞] :
  distrib_mul_action R (outer_measure α) :=
injective.distrib_mul_action coe_fn_add_monoid_hom coe_fn_injective coe_smul

instance [semiring R] [module R ℝ≥0∞] [is_scalar_tower R ℝ≥0∞ ℝ≥0∞] : module R (outer_measure α) :=
injective.module R coe_fn_add_monoid_hom coe_fn_injective coe_smul

instance : has_bot (outer_measure α) := ⟨0⟩

@[simp] theorem coe_bot : (⊥ : outer_measure α) = 0 := rfl

instance outer_measure.partial_order : partial_order (outer_measure α) :=
{ le          := λm₁ m₂, ∀s, m₁ s ≤ m₂ s,
  le_refl     := assume a s, le_rfl,
  le_trans    := assume a b c hab hbc s, le_trans (hab s) (hbc s),
  le_antisymm := assume a b hab hba, ext $ assume s, le_antisymm (hab s) (hba s) }

instance outer_measure.order_bot : order_bot (outer_measure α) :=
{ bot_le      := assume a s, by simp only [coe_zero, pi.zero_apply, coe_bot, zero_le],
  ..outer_measure.has_bot }

lemma univ_eq_zero_iff (m : outer_measure α) : m univ = 0 ↔ m = 0 :=
⟨λ h, bot_unique $ λ s, (m.mono' $ subset_univ s).trans_eq h, λ h, h.symm ▸ rfl⟩

section supremum

instance : has_Sup (outer_measure α) :=
⟨λms,
{ measure_of := λs, ⨆ m ∈ ms, (m : outer_measure α) s,
  empty      := nonpos_iff_eq_zero.1 $ supr₂_le $ λ m h, le_of_eq m.empty,
  mono       := assume s₁ s₂ hs, supr₂_mono $ assume m hm, m.mono hs,
  Union_nat  := assume f, supr₂_le $ assume m hm,
    calc m (⋃i, f i) ≤ ∑' (i : ℕ), m (f i) : m.Union_nat _
      ... ≤ ∑'i, (⨆ m ∈ ms, (m : outer_measure α) (f i)) :
        ennreal.tsum_le_tsum $ λ i, le_supr₂ m hm }⟩

instance : complete_lattice (outer_measure α) :=
{ .. outer_measure.order_bot, .. complete_lattice_of_Sup (outer_measure α)
    (λ ms, ⟨λ m hm s, le_supr₂ m hm, λ m hm s, supr₂_le (λ m' hm', hm hm' s)⟩) }

@[simp] theorem Sup_apply (ms : set (outer_measure α)) (s : set α) :
  (Sup ms) s = ⨆ m ∈ ms, (m : outer_measure α) s := rfl

@[simp] theorem supr_apply {ι} (f : ι → outer_measure α) (s : set α) :
  (⨆ i : ι, f i) s = ⨆ i, f i s :=
by rw [supr, Sup_apply, supr_range, supr]

@[norm_cast] theorem coe_supr {ι} (f : ι → outer_measure α) :
  ⇑(⨆ i, f i) = ⨆ i, f i :=
funext $ λ s, by rw [supr_apply, _root_.supr_apply]

@[simp] theorem sup_apply (m₁ m₂ : outer_measure α) (s : set α) :
  (m₁ ⊔ m₂) s = m₁ s ⊔ m₂ s :=
by have := supr_apply (λ b, cond b m₁ m₂) s;
  rwa [supr_bool_eq, supr_bool_eq] at this

theorem smul_supr [has_smul R ℝ≥0∞] [is_scalar_tower R ℝ≥0∞ ℝ≥0∞] {ι}
  (f : ι → outer_measure α) (c : R) :
  c • (⨆ i, f i) = ⨆ i, c • f i :=
ext $ λ s, by simp only [smul_apply, supr_apply, ←smul_one_mul c (f _ _),
  ←smul_one_mul c (supr _), ennreal.mul_supr]

end supremum

@[mono] lemma mono'' {m₁ m₂ : outer_measure α} {s₁ s₂ : set α} (hm : m₁ ≤ m₂) (hs : s₁ ⊆ s₂) :
  m₁ s₁ ≤ m₂ s₂ :=
(hm s₁).trans (m₂.mono hs)

/-- The pushforward of `m` along `f`. The outer measure on `s` is defined to be `m (f ⁻¹' s)`. -/
def map {β} (f : α → β) : outer_measure α →ₗ[ℝ≥0∞] outer_measure β :=
{ to_fun := λ m,
    { measure_of := λs, m (f ⁻¹' s),
      empty := m.empty,
      mono := λ s t h, m.mono (preimage_mono h),
      Union_nat := λ s, by rw [preimage_Union]; exact
        m.Union_nat (λ i, f ⁻¹' s i) },
  map_add' := λ m₁ m₂, coe_fn_injective rfl,
  map_smul' := λ c m, coe_fn_injective rfl }

@[simp] theorem map_apply {β} (f : α → β)
  (m : outer_measure α) (s : set β) : map f m s = m (f ⁻¹' s) := rfl

@[simp] theorem map_id (m : outer_measure α) : map id m = m :=
ext $ λ s, rfl

@[simp] theorem map_map {β γ} (f : α → β) (g : β → γ)
  (m : outer_measure α) : map g (map f m) = map (g ∘ f) m :=
ext $ λ s, rfl

@[mono] theorem map_mono {β} (f : α → β) : monotone (map f) :=
λ m m' h s, h _

@[simp] theorem map_sup {β} (f : α → β) (m m' : outer_measure α) :
  map f (m ⊔ m') = map f m ⊔ map f m' :=
ext $ λ s, by simp only [map_apply, sup_apply]

@[simp] theorem map_supr {β ι} (f : α → β) (m : ι → outer_measure α) :
  map f (⨆ i, m i) = ⨆ i, map f (m i) :=
ext $ λ s, by simp only [map_apply, supr_apply]

instance : functor outer_measure := {map := λ α β f, map f}

instance : is_lawful_functor outer_measure :=
{ id_map := λ α, map_id,
  comp_map := λ α β γ f g m, (map_map f g m).symm }

/-- The dirac outer measure. -/
def dirac (a : α) : outer_measure α :=
{ measure_of := λs, indicator s (λ _, 1) a,
  empty := by simp,
  mono := λ s t h, indicator_le_indicator_of_subset h (λ _, zero_le _) a,
  Union_nat := λ s,
    if hs : a ∈ ⋃ n, s n then let ⟨i, hi⟩ := mem_Union.1 hs in
      calc indicator (⋃ n, s n) (λ _, (1 : ℝ≥0∞)) a = 1 : indicator_of_mem hs _
      ... = indicator (s i) (λ _, 1) a : (indicator_of_mem hi _).symm
      ... ≤ ∑' n, indicator (s n) (λ _, 1) a : ennreal.le_tsum _
    else by simp only [indicator_of_not_mem hs, zero_le]}

@[simp] theorem dirac_apply (a : α) (s : set α) :
  dirac a s = indicator s (λ _, 1) a := rfl

/-- The sum of an (arbitrary) collection of outer measures. -/
def sum {ι} (f : ι → outer_measure α) : outer_measure α :=
{ measure_of := λs, ∑' i, f i s,
  empty := by simp,
  mono := λ s t h, ennreal.tsum_le_tsum (λ i, (f i).mono' h),
  Union_nat := λ s, by rw ennreal.tsum_comm; exact
    ennreal.tsum_le_tsum (λ i, (f i).Union_nat _) }

@[simp] theorem sum_apply {ι} (f : ι → outer_measure α) (s : set α) :
  sum f s = ∑' i, f i s := rfl

theorem smul_dirac_apply (a : ℝ≥0∞) (b : α) (s : set α) :
  (a • dirac b) s = indicator s (λ _, a) b :=
by simp only [smul_apply, smul_eq_mul, dirac_apply, ← indicator_mul_right _ (λ _, a), mul_one]

/-- Pullback of an `outer_measure`: `comap f μ s = μ (f '' s)`. -/
def comap {β} (f : α → β) : outer_measure β →ₗ[ℝ≥0∞] outer_measure α :=
{ to_fun := λ m,
    { measure_of := λ s, m (f '' s),
      empty := by simp,
      mono := λ s t h, m.mono $ image_subset f h,
      Union_nat := λ s, by { rw [image_Union], apply m.Union_nat } },
  map_add' := λ m₁ m₂, rfl,
  map_smul' := λ c m, rfl }

@[simp] lemma comap_apply {β} (f : α → β) (m : outer_measure β) (s : set α) :
  comap f m s = m (f '' s) :=
rfl

@[mono] lemma comap_mono {β} (f : α → β) :
  monotone (comap f) :=
λ m m' h s, h _

@[simp] theorem comap_supr {β ι} (f : α → β) (m : ι → outer_measure β) :
  comap f (⨆ i, m i) = ⨆ i, comap f (m i) :=
ext $ λ s, by simp only [comap_apply, supr_apply]

/-- Restrict an `outer_measure` to a set. -/
def restrict (s : set α) : outer_measure α →ₗ[ℝ≥0∞] outer_measure α :=
(map coe).comp (comap (coe : s → α))

@[simp] lemma restrict_apply (s t : set α) (m : outer_measure α) :
  restrict s m t = m (t ∩ s) :=
by simp [restrict]

@[mono] lemma restrict_mono {s t : set α} (h : s ⊆ t) {m m' : outer_measure α} (hm : m ≤ m') :
  restrict s m ≤ restrict t m' :=
λ u, by { simp only [restrict_apply], exact (hm _).trans (m'.mono $ inter_subset_inter_right _ h) }

@[simp] lemma restrict_univ (m : outer_measure α) : restrict univ m = m := ext $ λ s, by simp

@[simp] lemma restrict_empty (m : outer_measure α) : restrict ∅ m = 0 := ext $ λ s, by simp

@[simp] lemma restrict_supr {ι} (s : set α) (m : ι → outer_measure α) :
  restrict s (⨆ i, m i) = ⨆ i, restrict s (m i) :=
by simp [restrict]

lemma map_comap {β} (f : α → β) (m : outer_measure β) :
  map f (comap f m) = restrict (range f) m :=
ext $ λ s, congr_arg m $ by simp only [image_preimage_eq_inter_range, subtype.range_coe]

lemma map_comap_le {β} (f : α → β) (m : outer_measure β) :
  map f (comap f m) ≤ m :=
λ s, m.mono $ image_preimage_subset _ _

lemma restrict_le_self (m : outer_measure α) (s : set α) :
  restrict s m ≤ m :=
map_comap_le _ _

@[simp] lemma map_le_restrict_range {β} {ma : outer_measure α} {mb : outer_measure β} {f : α → β} :
  map f ma ≤ restrict (range f) mb ↔ map f ma ≤ mb :=
⟨λ h, h.trans (restrict_le_self _ _), λ h s, by simpa using h (s ∩ range f)⟩

lemma map_comap_of_surjective {β} {f : α → β} (hf : surjective f) (m : outer_measure β) :
  map f (comap f m) = m :=
ext $ λ s, by rw [map_apply, comap_apply, hf.image_preimage]

lemma le_comap_map {β} (f : α → β) (m : outer_measure α) :
  m ≤ comap f (map f m) :=
λ s, m.mono $ subset_preimage_image _ _

lemma comap_map {β} {f : α → β} (hf : injective f) (m : outer_measure α) :
  comap f (map f m) = m :=
ext $ λ s, by rw [comap_apply, map_apply, hf.preimage_image]

@[simp] theorem top_apply {s : set α} (h : s.nonempty) : (⊤ : outer_measure α) s = ∞ :=
let ⟨a, as⟩ := h in
top_unique $ le_trans (by simp [smul_dirac_apply, as]) (le_supr₂ (∞ • dirac a) trivial)

theorem top_apply' (s : set α) : (⊤ : outer_measure α) s = ⨅ (h : s = ∅), 0 :=
s.eq_empty_or_nonempty.elim (λ h, by simp [h]) (λ h, by simp [h, h.ne_empty])

@[simp] theorem comap_top (f : α → β) : comap f ⊤ = ⊤ :=
ext_nonempty $ λ s hs, by rw [comap_apply, top_apply hs, top_apply (hs.image _)]

theorem map_top (f : α → β) : map f ⊤ = restrict (range f) ⊤ :=
ext $ λ s, by rw [map_apply, restrict_apply, ← image_preimage_eq_inter_range,
  top_apply', top_apply', set.image_eq_empty]

theorem map_top_of_surjective (f : α → β) (hf : surjective f) : map f ⊤ = ⊤ :=
by rw [map_top, hf.range_eq, restrict_univ]

end basic

section of_function
set_option eqn_compiler.zeta true

variables {α : Type*} (m : set α → ℝ≥0∞) (m_empty : m ∅ = 0)
include m_empty

/-- Given any function `m` assigning measures to sets satisying `m ∅ = 0`, there is
  a unique maximal outer measure `μ` satisfying `μ s ≤ m s` for all `s : set α`. -/
protected def of_function : outer_measure α :=
let μ := λs, ⨅{f : ℕ → set α} (h : s ⊆ ⋃i, f i), ∑'i, m (f i) in
{ measure_of := μ,
  empty      := le_antisymm
    (infi_le_of_le (λ_, ∅) $ infi_le_of_le (empty_subset _) $ by simp [m_empty])
    (zero_le _),
  mono       := assume s₁ s₂ hs, infi_mono $ assume f,
    infi_mono' $ assume hb, ⟨hs.trans hb, le_rfl⟩,
  Union_nat := assume s, ennreal.le_of_forall_pos_le_add $ begin
    assume ε hε (hb : ∑'i, μ (s i) < ∞),
    rcases ennreal.exists_pos_sum_of_countable (ennreal.coe_pos.2 hε).ne' ℕ with ⟨ε', hε', hl⟩,
    refine le_trans _ (add_le_add_left (le_of_lt hl) _),
    rw ← ennreal.tsum_add,
    choose f hf using show
      ∀i, ∃f:ℕ → set α, s i ⊆ (⋃i, f i) ∧ ∑'i, m (f i) < μ (s i) + ε' i,
    { intro,
      have : μ (s i) < μ (s i) + ε' i :=
        ennreal.lt_add_right
          (ne_top_of_le_ne_top hb.ne $ ennreal.le_tsum _)
          (by simpa using (hε' i).ne'),
      simpa [μ, infi_lt_iff] },
    refine le_trans _ (ennreal.tsum_le_tsum $ λ i, le_of_lt (hf i).2),
    rw [← ennreal.tsum_prod, ← nat.mkpair_equiv.symm.tsum_eq],
    swap, {apply_instance},
    refine infi_le_of_le _ (infi_le _ _),
    exact Union_subset (λ i, subset.trans (hf i).1 $
      Union_subset $ λ j, subset.trans (by simp) $
      subset_Union _ $ nat.mkpair_equiv (i, j)),
  end }

lemma of_function_apply (s : set α) :
  outer_measure.of_function m m_empty s =
  (⨅ (t : ℕ → set α) (h : s ⊆ Union t), ∑' n, m (t n)) := rfl

variables {m m_empty}
theorem of_function_le (s : set α) : outer_measure.of_function m m_empty s ≤ m s :=
let f : ℕ → set α := λi, nat.cases_on i s (λ _, ∅) in
infi_le_of_le f $ infi_le_of_le (subset_Union f 0) $ le_of_eq $
tsum_eq_single 0 $ by rintro (_|i); simp [f, m_empty]

theorem of_function_eq (s : set α) (m_mono : ∀ ⦃t : set α⦄, s ⊆ t → m s ≤ m t)
  (m_subadd : ∀ (s : ℕ → set α), m (⋃i, s i) ≤ ∑'i, m (s i)) :
  outer_measure.of_function m m_empty s = m s :=
le_antisymm (of_function_le s) $ le_infi $ λ f, le_infi $ λ hf, le_trans (m_mono hf) (m_subadd f)

theorem le_of_function {μ : outer_measure α} :
  μ ≤ outer_measure.of_function m m_empty ↔ ∀ s, μ s ≤ m s :=
⟨λ H s, le_trans (H s) (of_function_le s),
 λ H s, le_infi $ λ f, le_infi $ λ hs,
  le_trans (μ.mono hs) $ le_trans (μ.Union f) $
  ennreal.tsum_le_tsum $ λ i, H _⟩

lemma is_greatest_of_function :
  is_greatest {μ : outer_measure α | ∀ s, μ s ≤ m s} (outer_measure.of_function m m_empty) :=
⟨λ s, of_function_le _, λ μ, le_of_function.2⟩

lemma of_function_eq_Sup : outer_measure.of_function m m_empty = Sup {μ | ∀ s, μ s ≤ m s} :=
(@is_greatest_of_function α m m_empty).is_lub.Sup_eq.symm

/-- If `m u = ∞` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = measure_theory.outer_measure.of_function m m_empty`.

E.g., if `α` is an (e)metric space and `m u = ∞` on any set of diameter `≥ r`, then this lemma
implies that `μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s`
and `y ∈ t`.  -/
lemma of_function_union_of_top_of_nonempty_inter {s t : set α}
  (h : ∀ u, (s ∩ u).nonempty → (t ∩ u).nonempty → m u = ∞) :
  outer_measure.of_function m m_empty (s ∪ t) =
    outer_measure.of_function m m_empty s + outer_measure.of_function m m_empty t :=
begin
  refine le_antisymm (outer_measure.union _ _ _) (le_infi $ λ f, le_infi $ λ hf, _),
  set μ := outer_measure.of_function m m_empty,
  rcases em (∃ i, (s ∩ f i).nonempty ∧ (t ∩ f i).nonempty) with ⟨i, hs, ht⟩|he,
  { calc μ s + μ t ≤ ∞ : le_top
    ... = m (f i) : (h (f i) hs ht).symm
    ... ≤ ∑' i, m (f i) : ennreal.le_tsum i },
  set I := λ s, {i : ℕ | (s ∩ f i).nonempty},
  have hd : disjoint (I s) (I t), from disjoint_iff_inf_le.mpr (λ i hi, he ⟨i, hi⟩),
  have hI : ∀ u ⊆ s ∪ t, μ u ≤ ∑'  i : I u, μ (f i), from λ u hu,
  calc μ u ≤ μ (⋃ i : I u, f i) :
    μ.mono (λ x hx, let ⟨i, hi⟩ := mem_Union.1 (hf (hu hx)) in mem_Union.2 ⟨⟨i, ⟨x, hx, hi⟩⟩, hi⟩)
  ... ≤ ∑' i : I u, μ (f i) : μ.Union _,
  calc μ s + μ t ≤ (∑' i : I s, μ (f i)) + (∑' i : I t, μ (f i)) :
    add_le_add (hI _ $ subset_union_left _ _) (hI _ $ subset_union_right _ _)
  ... = ∑' i : I s ∪ I t, μ (f i) :
    (@tsum_union_disjoint _ _ _ _ _ (λ i, μ (f i)) _ _ _ hd ennreal.summable ennreal.summable).symm
  ... ≤ ∑' i, μ (f i) :
    tsum_le_tsum_of_inj coe subtype.coe_injective (λ _ _, zero_le _) (λ _, le_rfl)
      ennreal.summable ennreal.summable
  ... ≤ ∑' i, m (f i) : ennreal.tsum_le_tsum (λ i, of_function_le _)
end

lemma comap_of_function {β} (f : β → α) (h : monotone m ∨ surjective f) :
  comap f (outer_measure.of_function m m_empty) =
    outer_measure.of_function (λ s, m (f '' s)) (by rwa set.image_empty) :=
begin
  refine le_antisymm (le_of_function.2 $ λ s, _) (λ s, _),
  { rw comap_apply, apply of_function_le },
  { rw [comap_apply, of_function_apply, of_function_apply],
    refine infi_mono' (λ t, ⟨λ k, f ⁻¹' (t k), _⟩),
    refine infi_mono' (λ ht, _),
    rw [set.image_subset_iff, preimage_Union] at ht,
    refine ⟨ht, ennreal.tsum_le_tsum $ λ n, _⟩,
    cases h,
    exacts [h (image_preimage_subset _ _), (congr_arg m (h.image_preimage (t n))).le] }
end

lemma map_of_function_le {β} (f : α → β) :
  map f (outer_measure.of_function m m_empty) ≤
    outer_measure.of_function (λ s, m (f ⁻¹' s)) m_empty :=
le_of_function.2 $ λ s, by { rw map_apply, apply of_function_le }

lemma map_of_function {β} {f : α → β} (hf : injective f) :
  map f (outer_measure.of_function m m_empty) =
    outer_measure.of_function (λ s, m (f ⁻¹' s)) m_empty :=
begin
  refine (map_of_function_le _).antisymm (λ s, _),
  simp only [of_function_apply, map_apply, le_infi_iff],
  intros t ht,
  refine infi_le_of_le (λ n, (range f)ᶜ ∪ f '' (t n)) (infi_le_of_le _ _),
  { rw [← union_Union, ← inter_subset, ← image_preimage_eq_inter_range, ← image_Union],
    exact image_subset _ ht },
  { refine ennreal.tsum_le_tsum (λ n, le_of_eq _),
    simp [hf.preimage_image] }
end

lemma restrict_of_function (s : set α) (hm : monotone m) :
  restrict s (outer_measure.of_function m m_empty) =
    outer_measure.of_function (λ t, m (t ∩ s)) (by rwa set.empty_inter) :=
by simp only [restrict, linear_map.comp_apply, comap_of_function _ (or.inl hm),
  map_of_function subtype.coe_injective, subtype.image_preimage_coe]

lemma smul_of_function {c : ℝ≥0∞} (hc : c ≠ ∞) :
  c • outer_measure.of_function m m_empty = outer_measure.of_function (c • m) (by simp [m_empty]) :=
begin
  ext1 s,
  haveI : nonempty {t : ℕ → set α // s ⊆ ⋃ i, t i} := ⟨⟨λ _, s, subset_Union (λ _, s) 0⟩⟩,
  simp only [smul_apply, of_function_apply, ennreal.tsum_mul_left, pi.smul_apply, smul_eq_mul,
    infi_subtype', ennreal.infi_mul_left (λ h, (hc h).elim)],
end

end of_function

section bounded_by

variables {α : Type*} (m : set α → ℝ≥0∞)

/-- Given any function `m` assigning measures to sets, there is a unique maximal outer measure `μ`
  satisfying `μ s ≤ m s` for all `s : set α`. This is the same as `outer_measure.of_function`,
  except that it doesn't require `m ∅ = 0`. -/
def bounded_by : outer_measure α :=
outer_measure.of_function (λ s, ⨆ (h : s.nonempty), m s) (by simp [not_nonempty_empty])

variables {m}
theorem bounded_by_le (s : set α) : bounded_by m s ≤ m s :=
(of_function_le _).trans supr_const_le

theorem bounded_by_eq_of_function (m_empty : m ∅ = 0) (s : set α) :
  bounded_by m s = outer_measure.of_function m m_empty s :=
begin
  have : (λ s : set α, ⨆ (h : s.nonempty), m s) = m,
  { ext1 t, cases t.eq_empty_or_nonempty with h h; simp [h, not_nonempty_empty, m_empty] },
  simp [bounded_by, this]
end
theorem bounded_by_apply (s : set α) :
  bounded_by m s = ⨅ (t : ℕ → set α) (h : s ⊆ Union t), ∑' n, ⨆ (h : (t n).nonempty), m (t n) :=
by simp [bounded_by, of_function_apply]

theorem bounded_by_eq (s : set α) (m_empty : m ∅ = 0) (m_mono : ∀ ⦃t : set α⦄, s ⊆ t → m s ≤ m t)
  (m_subadd : ∀ (s : ℕ → set α), m (⋃i, s i) ≤ ∑'i, m (s i)) : bounded_by m s = m s :=
by rw [bounded_by_eq_of_function m_empty, of_function_eq s m_mono m_subadd]

@[simp] theorem bounded_by_eq_self (m : outer_measure α) : bounded_by m = m :=
ext $ λ s, bounded_by_eq _ m.empty' (λ t ht, m.mono' ht) m.Union

theorem le_bounded_by {μ : outer_measure α} : μ ≤ bounded_by m ↔ ∀ s, μ s ≤ m s :=
begin
  rw [bounded_by, le_of_function, forall_congr], intro s,
  cases s.eq_empty_or_nonempty with h h; simp [h, not_nonempty_empty]
end

theorem le_bounded_by' {μ : outer_measure α} :
  μ ≤ bounded_by m ↔ ∀ s : set α, s.nonempty → μ s ≤ m s :=
by { rw [le_bounded_by, forall_congr], intro s, cases s.eq_empty_or_nonempty with h h; simp [h] }

lemma smul_bounded_by {c : ℝ≥0∞} (hc : c ≠ ∞) : c • bounded_by m = bounded_by (c • m) :=
begin
  simp only [bounded_by, smul_of_function hc],
  congr' 1 with s : 1,
  rcases s.eq_empty_or_nonempty with rfl|hs; simp *
end

lemma comap_bounded_by {β} (f : β → α)
  (h : monotone (λ s : {s : set α // s.nonempty}, m s) ∨ surjective f) :
  comap f (bounded_by m) = bounded_by (λ s, m (f '' s)) :=
begin
  refine (comap_of_function _ _).trans _,
  { refine h.imp (λ H s t hst, supr_le $ λ hs, _) id,
    have ht : t.nonempty := hs.mono hst,
    exact (@H ⟨s, hs⟩ ⟨t, ht⟩ hst).trans (le_supr (λ h : t.nonempty, m t) ht) },
  { dunfold bounded_by,
    congr' with s : 1,
    rw nonempty_image_iff }
end

/-- If `m u = ∞` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = measure_theory.outer_measure.bounded_by m`.

E.g., if `α` is an (e)metric space and `m u = ∞` on any set of diameter `≥ r`, then this lemma
implies that `μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s`
and `y ∈ t`.  -/
lemma bounded_by_union_of_top_of_nonempty_inter {s t : set α}
  (h : ∀ u, (s ∩ u).nonempty → (t ∩ u).nonempty → m u = ∞) :
  bounded_by m (s ∪ t) = bounded_by m s + bounded_by m t :=
of_function_union_of_top_of_nonempty_inter $ λ u hs ht,
  top_unique $ (h u hs ht).ge.trans $ le_supr (λ h, m u) (hs.mono $ inter_subset_right s u)

end bounded_by

section caratheodory_measurable
universe u
parameters {α : Type u} (m : outer_measure α)
include m

local attribute [simp] set.inter_comm set.inter_left_comm set.inter_assoc

variables {s s₁ s₂ : set α}

/-- A set `s` is Carathéodory-measurable for an outer measure `m` if for all sets `t` we have
  `m t = m (t ∩ s) + m (t \ s)`. -/
def is_caratheodory (s : set α) : Prop := ∀t, m t = m (t ∩ s) + m (t \ s)

lemma is_caratheodory_iff_le' {s : set α} : is_caratheodory s ↔ ∀t, m (t ∩ s) + m (t \ s) ≤ m t :=
forall_congr $ λ t, le_antisymm_iff.trans $ and_iff_right $ le_inter_add_diff _

@[simp] lemma is_caratheodory_empty : is_caratheodory ∅ :=
by simp [is_caratheodory, m.empty, diff_empty]

lemma is_caratheodory_compl : is_caratheodory s₁ → is_caratheodory s₁ᶜ :=
by simp [is_caratheodory, diff_eq, add_comm]

@[simp] lemma is_caratheodory_compl_iff : is_caratheodory sᶜ ↔ is_caratheodory s :=
⟨λ h, by simpa using is_caratheodory_compl m h, is_caratheodory_compl⟩

lemma is_caratheodory_union (h₁ : is_caratheodory s₁) (h₂ : is_caratheodory s₂) :
  is_caratheodory (s₁ ∪ s₂) :=
λ t, begin
  rw [h₁ t, h₂ (t ∩ s₁), h₂ (t \ s₁), h₁ (t ∩ (s₁ ∪ s₂)),
    inter_diff_assoc _ _ s₁, set.inter_assoc _ _ s₁,
    inter_eq_self_of_subset_right (set.subset_union_left _ _),
    union_diff_left, h₂ (t ∩ s₁)],
  simp [diff_eq, add_assoc]
end

lemma measure_inter_union (h : s₁ ∩ s₂ ⊆ ∅) (h₁ : is_caratheodory s₁) {t : set α} :
  m (t ∩ (s₁ ∪ s₂)) = m (t ∩ s₁) + m (t ∩ s₂) :=
by rw [h₁, set.inter_assoc, set.union_inter_cancel_left,
  inter_diff_assoc, union_diff_cancel_left h]

lemma is_caratheodory_Union_lt {s : ℕ → set α} :
  ∀{n:ℕ}, (∀i<n, is_caratheodory (s i)) → is_caratheodory (⋃i<n, s i)
| 0       h := by simp [nat.not_lt_zero]
| (n + 1) h := by rw bUnion_lt_succ; exact is_caratheodory_union m
    (is_caratheodory_Union_lt $ assume i hi, h i $ lt_of_lt_of_le hi $ nat.le_succ _)
    (h n (le_refl (n + 1)))

lemma is_caratheodory_inter (h₁ : is_caratheodory s₁) (h₂ : is_caratheodory s₂) :
  is_caratheodory (s₁ ∩ s₂) :=
by { rw [← is_caratheodory_compl_iff, set.compl_inter],
  exact is_caratheodory_union _ (is_caratheodory_compl _ h₁) (is_caratheodory_compl _ h₂) }

lemma is_caratheodory_sum {s : ℕ → set α} (h : ∀i, is_caratheodory (s i))
  (hd : pairwise (disjoint on s)) {t : set α} :
  ∀ {n}, ∑ i in finset.range n, m (t ∩ s i) = m (t ∩ ⋃i<n, s i)
| 0            := by simp [nat.not_lt_zero, m.empty]
| (nat.succ n) := begin
  rw [bUnion_lt_succ, finset.sum_range_succ, set.union_comm, is_caratheodory_sum,
    m.measure_inter_union _ (h n), add_comm],
  intro a,
  simpa using λ (h₁ : a ∈ s n) i (hi : i < n) h₂, (hd (ne_of_gt hi)).le_bot ⟨h₁, h₂⟩
end

lemma is_caratheodory_Union_nat {s : ℕ → set α} (h : ∀i, is_caratheodory (s i))
  (hd : pairwise (disjoint on s)) : is_caratheodory (⋃i, s i) :=
is_caratheodory_iff_le'.2 $ λ t, begin
  have hp : m (t ∩ ⋃i, s i) ≤ (⨆n, m (t ∩ ⋃i<n, s i)),
  { convert m.Union (λ i, t ∩ s i),
    { rw inter_Union },
    { simp [ennreal.tsum_eq_supr_nat, is_caratheodory_sum m h hd] } },
  refine le_trans (add_le_add_right hp _) _,
  rw ennreal.supr_add,
  refine supr_le (λ n, le_trans (add_le_add_left _ _)
    (ge_of_eq (is_caratheodory_Union_lt m (λ i _, h i) _))),
  refine m.mono (diff_subset_diff_right _),
  exact Union₂_subset (λ i _, subset_Union _ i),
end

lemma f_Union {s : ℕ → set α} (h : ∀i, is_caratheodory (s i))
  (hd : pairwise (disjoint on s)) : m (⋃i, s i) = ∑'i, m (s i) :=
begin
  refine le_antisymm (m.Union_nat s) _,
  rw ennreal.tsum_eq_supr_nat,
  refine supr_le (λ n, _),
  have := @is_caratheodory_sum _ m _ h hd univ n,
  simp at this, simp [this],
  exact m.mono (Union₂_subset (λ i _, subset_Union _ i)),
end

/-- The Carathéodory-measurable sets for an outer measure `m` form a Dynkin system.  -/
def caratheodory_dynkin : measurable_space.dynkin_system α :=
{ has := is_caratheodory,
  has_empty := is_caratheodory_empty,
  has_compl := assume s, is_caratheodory_compl,
  has_Union_nat := assume f hf hn, is_caratheodory_Union_nat hn hf }

/-- Given an outer measure `μ`, the Carathéodory-measurable space is
  defined such that `s` is measurable if `∀t, μ t = μ (t ∩ s) + μ (t \ s)`. -/
protected def caratheodory : measurable_space α :=
caratheodory_dynkin.to_measurable_space $ assume s₁ s₂, is_caratheodory_inter

lemma is_caratheodory_iff {s : set α} :
  measurable_set[caratheodory] s ↔ ∀t, m t = m (t ∩ s) + m (t \ s) :=
iff.rfl

lemma is_caratheodory_iff_le {s : set α} :
  measurable_set[caratheodory] s ↔ ∀t, m (t ∩ s) + m (t \ s) ≤ m t :=
is_caratheodory_iff_le'

protected lemma Union_eq_of_caratheodory {s : ℕ → set α}
  (h : ∀i, measurable_set[caratheodory] (s i)) (hd : pairwise (disjoint on s)) :
  m (⋃i, s i) = ∑'i, m (s i) :=
f_Union h hd

end caratheodory_measurable

variables {α : Type*}

lemma of_function_caratheodory {m : set α → ℝ≥0∞} {s : set α}
  {h₀ : m ∅ = 0} (hs : ∀t, m (t ∩ s) + m (t \ s) ≤ m t) :
  measurable_set[(outer_measure.of_function m h₀).caratheodory] s :=
begin
  apply (is_caratheodory_iff_le _).mpr,
  refine λ t, le_infi (λ f, le_infi $ λ hf, _),
  refine le_trans (add_le_add
    (infi_le_of_le (λi, f i ∩ s) $ infi_le _ _)
    (infi_le_of_le (λi, f i \ s) $ infi_le _ _)) _,
  { rw ← Union_inter, exact inter_subset_inter_left _ hf },
  { rw ← Union_diff, exact diff_subset_diff_left hf },
  { rw ← ennreal.tsum_add, exact ennreal.tsum_le_tsum (λ i, hs _) }
end

lemma bounded_by_caratheodory {m : set α → ℝ≥0∞} {s : set α}
  (hs : ∀t, m (t ∩ s) + m (t \ s) ≤ m t) : measurable_set[(bounded_by m).caratheodory] s :=
begin
  apply of_function_caratheodory, intro t,
  cases t.eq_empty_or_nonempty with h h,
  { simp [h, not_nonempty_empty] },
  { convert le_trans _ (hs t), { simp [h] }, exact add_le_add supr_const_le supr_const_le }
end

@[simp] theorem zero_caratheodory : (0 : outer_measure α).caratheodory = ⊤ :=
top_unique $ λ s _ t, (add_zero _).symm

theorem top_caratheodory : (⊤ : outer_measure α).caratheodory = ⊤ :=
top_unique $ assume s hs, (is_caratheodory_iff_le _).2 $ assume t,
  t.eq_empty_or_nonempty.elim (λ ht, by simp [ht])
    (λ ht, by simp only [ht, top_apply, le_top])

theorem le_add_caratheodory (m₁ m₂ : outer_measure α) :
  m₁.caratheodory ⊓ m₂.caratheodory ≤ (m₁ + m₂ : outer_measure α).caratheodory :=
λ s ⟨hs₁, hs₂⟩ t, by simp [hs₁ t, hs₂ t, add_left_comm, add_assoc]

theorem le_sum_caratheodory {ι} (m : ι → outer_measure α) :
  (⨅ i, (m i).caratheodory) ≤ (sum m).caratheodory :=
λ s h t, by simp [λ i,
  measurable_space.measurable_set_infi.1 h i t, ennreal.tsum_add]

theorem le_smul_caratheodory (a : ℝ≥0∞) (m : outer_measure α) :
  m.caratheodory ≤ (a • m).caratheodory :=
λ s h t, by simp [h t, mul_add]

@[simp] theorem dirac_caratheodory (a : α) : (dirac a).caratheodory = ⊤ :=
top_unique $ λ s _ t, begin
  by_cases ht : a ∈ t, swap, by simp [ht],
  by_cases hs : a ∈ s; simp*
end

section Inf_gen

/-- Given a set of outer measures, we define a new function that on a set `s` is defined to be the
  infimum of `μ(s)` for the outer measures `μ` in the collection. We ensure that this
  function is defined to be `0` on `∅`, even if the collection of outer measures is empty.
  The outer measure generated by this function is the infimum of the given outer measures. -/
def Inf_gen (m : set (outer_measure α)) (s : set α) : ℝ≥0∞ :=
⨅ (μ : outer_measure α) (h : μ ∈ m), μ s

lemma Inf_gen_def (m : set (outer_measure α)) (t : set α) :
  Inf_gen m t = (⨅ (μ : outer_measure α) (h : μ ∈ m), μ t) :=
rfl

lemma Inf_eq_bounded_by_Inf_gen (m : set (outer_measure α)) :
  Inf m = outer_measure.bounded_by (Inf_gen m) :=
begin
  refine le_antisymm _ _,
  { refine (le_bounded_by.2 $ λ s, le_infi₂ $ λ μ hμ, _),
    exact (show Inf m ≤ μ, from Inf_le hμ) s },
  { refine le_Inf _, intros μ hμ t, refine le_trans (bounded_by_le t) (infi₂_le μ hμ) }
end

lemma supr_Inf_gen_nonempty {m : set (outer_measure α)} (h : m.nonempty) (t : set α) :
  (⨆ (h : t.nonempty), Inf_gen m t) = (⨅ (μ : outer_measure α) (h : μ ∈ m), μ t) :=
begin
  rcases t.eq_empty_or_nonempty with rfl|ht,
  { rcases h with ⟨μ, hμ⟩,
    rw [eq_false_intro not_nonempty_empty, supr_false, eq_comm],
    simp_rw [empty'],
    apply bot_unique,
    refine infi_le_of_le μ (infi_le _ hμ) },
  { simp [ht, Inf_gen_def] }
end

/-- The value of the Infimum of a nonempty set of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
lemma Inf_apply {m : set (outer_measure α)} {s : set α} (h : m.nonempty) :
  Inf m s = ⨅ (t : ℕ → set α) (h2 : s ⊆ Union t),
    ∑' n, ⨅ (μ : outer_measure α) (h3 : μ ∈ m), μ (t n) :=
by simp_rw [Inf_eq_bounded_by_Inf_gen, bounded_by_apply, supr_Inf_gen_nonempty h]

/-- The value of the Infimum of a set of outer measures on a nonempty set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
lemma Inf_apply' {m : set (outer_measure α)} {s : set α} (h : s.nonempty) :
  Inf m s = ⨅ (t : ℕ → set α) (h2 : s ⊆ Union t),
    ∑' n, ⨅ (μ : outer_measure α) (h3 : μ ∈ m), μ (t n) :=
m.eq_empty_or_nonempty.elim (λ hm, by simp [hm, h]) Inf_apply

/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
lemma infi_apply {ι} [nonempty ι] (m : ι → outer_measure α) (s : set α) :
  (⨅ i, m i) s = ⨅ (t : ℕ → set α) (h2 : s ⊆ Union t), ∑' n, ⨅ i, m i (t n) :=
by { rw [infi, Inf_apply (range_nonempty m)], simp only [infi_range] }

/-- The value of the Infimum of a family of outer measures on a nonempty set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
lemma infi_apply' {ι} (m : ι → outer_measure α) {s : set α} (hs : s.nonempty) :
  (⨅ i, m i) s = ⨅ (t : ℕ → set α) (h2 : s ⊆ Union t), ∑' n, ⨅ i, m i (t n) :=
by { rw [infi, Inf_apply' hs], simp only [infi_range] }

/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
lemma binfi_apply {ι} {I : set ι} (hI : I.nonempty) (m : ι → outer_measure α) (s : set α) :
  (⨅ i ∈ I, m i) s = ⨅ (t : ℕ → set α) (h2 : s ⊆ Union t), ∑' n, ⨅ i ∈ I, m i (t n) :=
by { haveI := hI.to_subtype, simp only [← infi_subtype'', infi_apply] }

/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
lemma binfi_apply' {ι} (I : set ι) (m : ι → outer_measure α) {s : set α} (hs : s.nonempty) :
  (⨅ i ∈ I, m i) s = ⨅ (t : ℕ → set α) (h2 : s ⊆ Union t), ∑' n, ⨅ i ∈ I, m i (t n) :=
by { simp only [← infi_subtype'', infi_apply' _ hs] }

lemma map_infi_le {ι β} (f : α → β) (m : ι → outer_measure α) :
  map f (⨅ i, m i) ≤ ⨅ i, map f (m i) :=
(map_mono f).map_infi_le

lemma comap_infi {ι β} (f : α → β) (m : ι → outer_measure β) :
  comap f (⨅ i, m i) = ⨅ i, comap f (m i) :=
begin
  refine ext_nonempty (λ s hs, _),
  refine ((comap_mono f).map_infi_le s).antisymm _,
  simp only [comap_apply, infi_apply' _ hs, infi_apply' _ (hs.image _),
    le_infi_iff, set.image_subset_iff, preimage_Union],
  refine λ t ht, infi_le_of_le _ (infi_le_of_le ht $ ennreal.tsum_le_tsum $ λ k, _),
  exact infi_mono (λ i, (m i).mono (image_preimage_subset _ _))
end

lemma map_infi {ι β} {f : α → β} (hf : injective f) (m : ι → outer_measure α) :
  map f (⨅ i, m i) = restrict (range f) (⨅ i, map f (m i)) :=
begin
  refine eq.trans _ (map_comap _ _),
  simp only [comap_infi, comap_map hf]
end

lemma map_infi_comap {ι β} [nonempty ι] {f : α → β} (m : ι → outer_measure β) :
  map f (⨅ i, comap f (m i)) = ⨅ i, map f (comap f (m i)) :=
begin
  refine (map_infi_le _ _).antisymm (λ s, _),
  simp only [map_apply, comap_apply, infi_apply, le_infi_iff],
  refine λ t ht, infi_le_of_le (λ n, f '' (t n) ∪ (range f)ᶜ) (infi_le_of_le _ _),
  { rw [← Union_union, set.union_comm, ← inter_subset, ← image_Union,
      ← image_preimage_eq_inter_range],
    exact image_subset _ ht },
  { refine ennreal.tsum_le_tsum (λ n, infi_mono $ λ i, (m i).mono _),
    simp }
end

lemma map_binfi_comap {ι β} {I : set ι} (hI : I.nonempty) {f : α → β} (m : ι → outer_measure β) :
  map f (⨅ i ∈ I, comap f (m i)) = ⨅ i ∈ I, map f (comap f (m i)) :=
by { haveI := hI.to_subtype, rw [← infi_subtype'', ← infi_subtype''], exact map_infi_comap _ }

lemma restrict_infi_restrict {ι} (s : set α) (m : ι → outer_measure α) :
  restrict s (⨅ i, restrict s (m i)) = restrict s (⨅ i, m i) :=
calc restrict s (⨅ i, restrict s (m i)) = restrict (range (coe : s → α)) (⨅ i, restrict s (m i)) :
  by rw [subtype.range_coe]
... = map (coe : s → α) (⨅ i, comap coe (m i)) : (map_infi subtype.coe_injective _).symm
... = restrict s (⨅ i, m i) : congr_arg (map coe) (comap_infi _ _).symm

lemma restrict_infi {ι} [nonempty ι] (s : set α) (m : ι → outer_measure α) :
  restrict s (⨅ i, m i) = ⨅ i, restrict s (m i) :=
(congr_arg (map coe) (comap_infi _ _)).trans (map_infi_comap _)

lemma restrict_binfi {ι} {I : set ι} (hI : I.nonempty) (s : set α) (m : ι → outer_measure α) :
  restrict s (⨅ i ∈ I, m i) = ⨅ i ∈ I, restrict s (m i) :=
by { haveI := hI.to_subtype, rw [← infi_subtype'', ← infi_subtype''], exact restrict_infi _ _ }

/-- This proves that Inf and restrict commute for outer measures, so long as the set of
outer measures is nonempty. -/
lemma restrict_Inf_eq_Inf_restrict
  (m : set (outer_measure α)) {s : set α} (hm : m.nonempty) :
  restrict s (Inf m) = Inf ((restrict s) '' m) :=
by simp only [Inf_eq_infi, restrict_binfi, hm, infi_image]

end Inf_gen

end outer_measure
open outer_measure

/-! ### Induced Outer Measure

  We can extend a function defined on a subset of `set α` to an outer measure.
  The underlying function is called `extend`, and the measure it induces is called
  `induced_outer_measure`.

  Some lemmas below are proven twice, once in the general case, and one where the function `m`
  is only defined on measurable sets (i.e. when `P = measurable_set`). In the latter cases, we can
  remove some hypotheses in the statement. The general version has the same name, but with a prime
  at the end. -/
section extend
variables {α : Type*} {P : α → Prop}
variables (m : Π (s : α), P s → ℝ≥0∞)

/-- We can trivially extend a function defined on a subclass of objects (with codomain `ℝ≥0∞`)
  to all objects by defining it to be `∞` on the objects not in the class. -/
def extend (s : α) : ℝ≥0∞ := ⨅ h : P s, m s h

lemma extend_eq {s : α} (h : P s) : extend m s = m s h :=
by simp [extend, h]

lemma extend_eq_top {s : α} (h : ¬P s) : extend m s = ∞ :=
by simp [extend, h]

lemma le_extend {s : α} (h : P s) : m s h ≤ extend m s :=
by { simp only [extend, le_infi_iff], intro, refl' }

-- TODO: why this is a bad `congr` lemma?
lemma extend_congr {β : Type*} {Pb : β → Prop} {mb : Π s : β, Pb s → ℝ≥0∞}
  {sa : α} {sb : β} (hP : P sa ↔ Pb sb) (hm : ∀ (ha : P sa) (hb : Pb sb), m sa ha = mb sb hb) :
  extend m sa = extend mb sb :=
infi_congr_Prop hP (λ h, hm _ _)

end extend

section extend_set

variables {α : Type*} {P : set α → Prop}
variables {m : Π (s : set α), P s → ℝ≥0∞}
variables (P0 : P ∅) (m0 : m ∅ P0 = 0)
variables (PU : ∀{{f : ℕ → set α}} (hm : ∀i, P (f i)), P (⋃i, f i))
variables (mU : ∀ {{f : ℕ → set α}} (hm : ∀i, P (f i)), pairwise (disjoint on f) →
  m (⋃i, f i) (PU hm) = ∑'i, m (f i) (hm i))
variables (msU : ∀ {{f : ℕ → set α}} (hm : ∀i, P (f i)),
  m (⋃i, f i) (PU hm) ≤ ∑'i, m (f i) (hm i))
variables (m_mono : ∀⦃s₁ s₂ : set α⦄ (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)

lemma extend_empty : extend m ∅ = 0 :=
(extend_eq _ P0).trans m0

lemma extend_Union_nat
  {f : ℕ → set α} (hm : ∀i, P (f i))
  (mU : m (⋃i, f i) (PU hm) = ∑'i, m (f i) (hm i)) :
  extend m (⋃i, f i) = ∑'i, extend m (f i) :=
(extend_eq _ _).trans $ mU.trans $ by { congr' with i, rw extend_eq }

section subadditive
include PU msU
lemma extend_Union_le_tsum_nat'
  (s : ℕ → set α) : extend m (⋃i, s i) ≤ ∑'i, extend m (s i) :=
begin
  by_cases h : ∀i, P (s i),
  { rw [extend_eq _ (PU h), congr_arg tsum _],
    { apply msU h },
    funext i, apply extend_eq _ (h i) },
  { cases not_forall.1 h with i hi,
    exact le_trans (le_infi $ λ h, hi.elim h) (ennreal.le_tsum i) }
end
end subadditive

section mono
include m_mono
lemma extend_mono'
  ⦃s₁ s₂ : set α⦄ (h₁ : P s₁) (hs : s₁ ⊆ s₂) : extend m s₁ ≤ extend m s₂ :=
by { refine le_infi _, intro h₂, rw [extend_eq m h₁], exact m_mono h₁ h₂ hs }
end mono

section unions
include P0 m0 PU mU
lemma extend_Union {β} [countable β] {f : β → set α} (hd : pairwise (disjoint on f))
  (hm : ∀ i, P (f i)) :
  extend m (⋃i, f i) = ∑'i, extend m (f i) :=
begin
  casesI nonempty_encodable β,
  rw [← encodable.Union_decode₂, ← tsum_Union_decode₂],
  { exact extend_Union_nat PU
      (λ n, encodable.Union_decode₂_cases P0 hm)
      (mU _ (encodable.Union_decode₂_disjoint_on hd)) },
  { exact extend_empty P0 m0 }
end

lemma extend_union {s₁ s₂ : set α} (hd : disjoint s₁ s₂) (h₁ : P s₁) (h₂ : P s₂) :
  extend m (s₁ ∪ s₂) = extend m s₁ + extend m s₂ :=
begin
  rw [union_eq_Union, extend_Union P0 m0 PU mU
      (pairwise_disjoint_on_bool.2 hd) (bool.forall_bool.2 ⟨h₂, h₁⟩), tsum_fintype],
  simp
end

end unions

variable (m)
/-- Given an arbitrary function on a subset of sets, we can define the outer measure corresponding
  to it (this is the unique maximal outer measure that is at most `m` on the domain of `m`). -/
def induced_outer_measure : outer_measure α :=
outer_measure.of_function (extend m) (extend_empty P0 m0)
variables {m P0 m0}

lemma le_induced_outer_measure {μ : outer_measure α} :
  μ ≤ induced_outer_measure m P0 m0 ↔ ∀ s (hs : P s), μ s ≤ m s hs :=
le_of_function.trans $ forall_congr $ λ s, le_infi_iff

/-- If `P u` is `false` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = induced_outer_measure m P0 m0`.

E.g., if `α` is an (e)metric space and `P u = diam u < r`, then this lemma implies that
`μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s` and `y ∈ t`. -/
lemma induced_outer_measure_union_of_false_of_nonempty_inter {s t : set α}
  (h : ∀ u, (s ∩ u).nonempty → (t ∩ u).nonempty → ¬P u) :
  induced_outer_measure m P0 m0 (s ∪ t) =
     induced_outer_measure m P0 m0 s + induced_outer_measure m P0 m0 t :=
of_function_union_of_top_of_nonempty_inter $ λ u hsu htu, @infi_of_empty _ _ _ ⟨h u hsu htu⟩ _

include msU m_mono
lemma induced_outer_measure_eq_extend' {s : set α} (hs : P s) :
  induced_outer_measure m P0 m0 s = extend m s :=
of_function_eq s (λ t, extend_mono' m_mono hs) (extend_Union_le_tsum_nat' PU msU)

lemma induced_outer_measure_eq' {s : set α} (hs : P s) :
  induced_outer_measure m P0 m0 s = m s hs :=
(induced_outer_measure_eq_extend' PU msU m_mono hs).trans $ extend_eq _ _

lemma induced_outer_measure_eq_infi (s : set α) :
  induced_outer_measure m P0 m0 s = ⨅ (t : set α) (ht : P t) (h : s ⊆ t), m t ht :=
begin
  apply le_antisymm,
  { simp only [le_infi_iff], intros t ht hs,
    refine le_trans (mono' _ hs) _,
    exact le_of_eq (induced_outer_measure_eq' _ msU m_mono _) },
  { refine le_infi _, intro f, refine le_infi _, intro hf,
    refine le_trans _ (extend_Union_le_tsum_nat' _ msU _),
    refine le_infi _, intro h2f,
    refine infi_le_of_le _ (infi_le_of_le h2f $ infi_le _ hf) }
end

lemma induced_outer_measure_preimage (f : α ≃ α) (Pm : ∀ (s : set α), P (f ⁻¹' s) ↔ P s)
  (mm : ∀ (s : set α) (hs : P s), m (f ⁻¹' s) ((Pm _).mpr hs) = m s hs)
  {A : set α} : induced_outer_measure m P0 m0 (f ⁻¹' A) = induced_outer_measure m P0 m0 A :=
begin
  simp only [induced_outer_measure_eq_infi _ msU m_mono], symmetry,
  refine f.injective.preimage_surjective.infi_congr (preimage f) (λ s, _),
  refine infi_congr_Prop (Pm s) _, intro hs,
  refine infi_congr_Prop f.surjective.preimage_subset_preimage_iff _,
  intro h2s, exact mm s hs
end

lemma induced_outer_measure_exists_set {s : set α}
  (hs : induced_outer_measure m P0 m0 s ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ (t : set α) (ht : P t), s ⊆ t ∧
    induced_outer_measure m P0 m0 t ≤ induced_outer_measure m P0 m0 s + ε :=
begin
  have := ennreal.lt_add_right hs hε,
  conv at this {to_lhs, rw induced_outer_measure_eq_infi _ msU m_mono },
  simp only [infi_lt_iff] at this,
  rcases this with ⟨t, h1t, h2t, h3t⟩,
  exact ⟨t, h1t, h2t,
    le_trans (le_of_eq $ induced_outer_measure_eq' _ msU m_mono h1t) (le_of_lt h3t)⟩
end

/-- To test whether `s` is Carathéodory-measurable we only need to check the sets `t` for which
  `P t` holds. See `of_function_caratheodory` for another way to show the Carathéodory-measurability
  of `s`.
-/
lemma induced_outer_measure_caratheodory (s : set α) :
  measurable_set[(induced_outer_measure m P0 m0).caratheodory] s ↔ ∀ (t : set α), P t →
  induced_outer_measure m P0 m0 (t ∩ s) + induced_outer_measure m P0 m0 (t \ s) ≤
    induced_outer_measure m P0 m0 t :=
begin
  rw is_caratheodory_iff_le,
  split,
  { intros h t ht, exact h t },
  { intros h u, conv_rhs { rw induced_outer_measure_eq_infi _ msU m_mono },
    refine le_infi _, intro t, refine le_infi _, intro ht, refine le_infi _, intro h2t,
    refine le_trans _ (le_trans (h t ht) $ le_of_eq $ induced_outer_measure_eq' _ msU m_mono ht),
    refine add_le_add (mono' _ $ set.inter_subset_inter_left _ h2t)
      (mono' _  $ diff_subset_diff_left h2t) }
end

end extend_set

/-! If `P` is `measurable_set` for some measurable space, then we can remove some hypotheses of the
  above lemmas. -/
section measurable_space

variables {α : Type*} [measurable_space α]
variables {m : Π (s : set α), measurable_set s → ℝ≥0∞}
variables (m0 : m ∅ measurable_set.empty = 0)
variable (mU : ∀ {{f : ℕ → set α}} (hm : ∀i, measurable_set (f i)), pairwise (disjoint on f) →
  m (⋃i, f i) (measurable_set.Union hm) = ∑'i, m (f i) (hm i))
include m0 mU

lemma extend_mono {s₁ s₂ : set α} (h₁ : measurable_set s₁) (hs : s₁ ⊆ s₂) :
  extend m s₁ ≤ extend m s₂ :=
begin
  refine le_infi _, intro h₂,
  have := extend_union measurable_set.empty m0 measurable_set.Union mU disjoint_sdiff_self_right
    h₁ (h₂.diff h₁),
  rw union_diff_cancel hs at this,
  rw ← extend_eq m,
  exact le_iff_exists_add.2 ⟨_, this⟩,
end

lemma extend_Union_le_tsum_nat : ∀ (s : ℕ → set α), extend m (⋃i, s i) ≤ ∑'i, extend m (s i) :=
begin
  refine extend_Union_le_tsum_nat' measurable_set.Union _, intros f h,
  simp [Union_disjointed.symm] {single_pass := tt},
  rw [mU (measurable_set.disjointed h) (disjoint_disjointed _)],
  refine ennreal.tsum_le_tsum (λ i, _),
  rw [← extend_eq m, ← extend_eq m],
  exact extend_mono m0 mU (measurable_set.disjointed h _) (disjointed_le f _),
end

lemma induced_outer_measure_eq_extend {s : set α} (hs : measurable_set s) :
  induced_outer_measure m measurable_set.empty m0 s = extend m s :=
of_function_eq s (λ t, extend_mono m0 mU hs) (extend_Union_le_tsum_nat m0 mU)

lemma induced_outer_measure_eq {s : set α} (hs : measurable_set s) :
  induced_outer_measure m measurable_set.empty m0 s = m s hs :=
(induced_outer_measure_eq_extend m0 mU hs).trans $ extend_eq _ _

end measurable_space

namespace outer_measure
variables {α : Type*} [measurable_space α] (m : outer_measure α)

/-- Given an outer measure `m` we can forget its value on non-measurable sets, and then consider
  `m.trim`, the unique maximal outer measure less than that function. -/
def trim : outer_measure α :=
induced_outer_measure (λ s _, m s) measurable_set.empty m.empty

theorem le_trim : m ≤ m.trim :=
le_of_function.mpr $ λ s, le_infi $ λ _, le_rfl

theorem trim_eq {s : set α} (hs : measurable_set s) : m.trim s = m s :=
induced_outer_measure_eq' measurable_set.Union (λ f hf, m.Union_nat f) (λ _ _ _ _ h, m.mono h) hs

theorem trim_congr {m₁ m₂ : outer_measure α}
  (H : ∀ {s : set α}, measurable_set s → m₁ s = m₂ s) :
  m₁.trim = m₂.trim :=
by { unfold trim, congr, funext s hs, exact H hs }

@[mono] theorem trim_mono : monotone (trim : outer_measure α → outer_measure α) :=
λ m₁ m₂ H s, infi₂_mono $ λ f hs, ennreal.tsum_le_tsum $ λ b, infi_mono $ λ hf, H _

theorem le_trim_iff {m₁ m₂ : outer_measure α} :
  m₁ ≤ m₂.trim ↔ ∀ s, measurable_set s → m₁ s ≤ m₂ s :=
le_of_function.trans $ forall_congr $ λ s, le_infi_iff

theorem trim_le_trim_iff {m₁ m₂ : outer_measure α} :
  m₁.trim ≤ m₂.trim ↔ ∀ s, measurable_set s → m₁ s ≤ m₂ s :=
le_trim_iff.trans $ forall₂_congr $ λ s hs, by rw [trim_eq _ hs]

theorem trim_eq_trim_iff {m₁ m₂ : outer_measure α} :
  m₁.trim = m₂.trim ↔ ∀ s, measurable_set s → m₁ s = m₂ s :=
by simp only [le_antisymm_iff, trim_le_trim_iff, forall_and_distrib]

theorem trim_eq_infi (s : set α) : m.trim s = ⨅ t (st : s ⊆ t) (ht : measurable_set t), m t :=
by { simp only [infi_comm] {single_pass := tt}, exact induced_outer_measure_eq_infi
    measurable_set.Union (λ f _, m.Union_nat f) (λ _ _ _ _ h, m.mono h) s }

theorem trim_eq_infi' (s : set α) : m.trim s = ⨅ t : {t // s ⊆ t ∧ measurable_set t}, m t :=
by simp [infi_subtype, infi_and, trim_eq_infi]

theorem trim_trim (m : outer_measure α) : m.trim.trim = m.trim :=
trim_eq_trim_iff.2 $ λ s, m.trim_eq

@[simp] theorem trim_zero : (0 : outer_measure α).trim = 0 :=
ext $ λ s, le_antisymm
  (le_trans ((trim 0).mono (subset_univ s)) $
    le_of_eq $ trim_eq _ measurable_set.univ)
  (zero_le _)

theorem trim_sum_ge {ι} (m : ι → outer_measure α) : sum (λ i, (m i).trim) ≤ (sum m).trim :=
λ s, by simp [trim_eq_infi]; exact
λ t st ht, ennreal.tsum_le_tsum (λ i,
  infi_le_of_le t $ infi_le_of_le st $ infi_le _ ht)

lemma exists_measurable_superset_eq_trim (m : outer_measure α) (s : set α) :
  ∃ t, s ⊆ t ∧ measurable_set t ∧ m t = m.trim s :=
begin
  simp only [trim_eq_infi], set ms := ⨅ (t : set α) (st : s ⊆ t) (ht : measurable_set t), m t,
  by_cases hs : ms = ∞,
  { simp only [hs],
    simp only [infi_eq_top] at hs,
    exact ⟨univ, subset_univ s, measurable_set.univ, hs _ (subset_univ s) measurable_set.univ⟩ },
  { have : ∀ r > ms, ∃ t, s ⊆ t ∧ measurable_set t ∧ m t < r,
    { intros r hs,
      simpa [infi_lt_iff] using hs },
    have : ∀ n : ℕ, ∃ t, s ⊆ t ∧ measurable_set t ∧ m t < ms + n⁻¹,
    { assume n,
      refine this _ (ennreal.lt_add_right hs _),
      simp },
    choose t hsub hm hm',
    refine ⟨⋂ n, t n, subset_Inter hsub, measurable_set.Inter hm, _⟩,
    have : tendsto (λ n : ℕ, ms + n⁻¹) at_top (𝓝 (ms + 0)),
      from tendsto_const_nhds.add ennreal.tendsto_inv_nat_nhds_zero,
    rw add_zero at this,
    refine le_antisymm (ge_of_tendsto' this $ λ n, _) _,
    { exact le_trans (m.mono' $ Inter_subset t n) (hm' n).le },
    { refine infi_le_of_le (⋂ n, t n) _,
      refine infi_le_of_le (subset_Inter hsub) _,
      refine infi_le _ (measurable_set.Inter hm) } }
end

lemma exists_measurable_superset_of_trim_eq_zero
  {m : outer_measure α} {s : set α} (h : m.trim s = 0) :
  ∃t, s ⊆ t ∧ measurable_set t ∧ m t = 0 :=
begin
  rcases exists_measurable_superset_eq_trim m s with ⟨t, hst, ht, hm⟩,
  exact ⟨t, hst, ht, h ▸ hm⟩
end

/-- If `μ i` is a countable family of outer measures, then for every set `s` there exists
a measurable set `t ⊇ s` such that `μ i t = (μ i).trim s` for all `i`. -/
lemma exists_measurable_superset_forall_eq_trim {ι} [countable ι] (μ : ι → outer_measure α)
  (s : set α) : ∃ t, s ⊆ t ∧ measurable_set t ∧ ∀ i, μ i t = (μ i).trim s :=
begin
  choose t hst ht hμt using λ i, (μ i).exists_measurable_superset_eq_trim s,
  replace hst := subset_Inter hst,
  replace ht := measurable_set.Inter ht,
  refine ⟨⋂ i, t i, hst, ht, λ i, le_antisymm _ _⟩,
  exacts [hμt i ▸ (μ i).mono (Inter_subset _ _),
    (mono' _ hst).trans_eq ((μ i).trim_eq ht)]
end

/-- If `m₁ s = op (m₂ s) (m₃ s)` for all `s`, then the same is true for `m₁.trim`, `m₂.trim`,
and `m₃ s`. -/
theorem trim_binop {m₁ m₂ m₃ : outer_measure α} {op : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}
  (h : ∀ s, m₁ s = op (m₂ s) (m₃ s)) (s : set α) :
  m₁.trim s = op (m₂.trim s) (m₃.trim s) :=
begin
  rcases exists_measurable_superset_forall_eq_trim (![m₁, m₂, m₃]) s
    with ⟨t, hst, ht, htm⟩,
  simp only [fin.forall_fin_succ, matrix.cons_val_zero, matrix.cons_val_succ] at htm,
  rw [← htm.1, ← htm.2.1, ← htm.2.2.1, h]
end

/-- If `m₁ s = op (m₂ s)` for all `s`, then the same is true for `m₁.trim` and `m₂.trim`. -/
theorem trim_op {m₁ m₂ : outer_measure α} {op : ℝ≥0∞ → ℝ≥0∞}
  (h : ∀ s, m₁ s = op (m₂ s)) (s : set α) :
  m₁.trim s = op (m₂.trim s) :=
@trim_binop α _ m₁ m₂ 0 (λ a b, op a) h s

/-- `trim` is additive. -/
theorem trim_add (m₁ m₂ : outer_measure α) : (m₁ + m₂).trim = m₁.trim + m₂.trim :=
ext $ trim_binop (add_apply m₁ m₂)

/-- `trim` respects scalar multiplication. -/
theorem trim_smul {R : Type*} [has_smul R ℝ≥0∞] [is_scalar_tower R ℝ≥0∞ ℝ≥0∞]
  (c : R) (m : outer_measure α) :
  (c • m).trim = c • m.trim :=
ext $ trim_op (smul_apply c m)

/-- `trim` sends the supremum of two outer measures to the supremum of the trimmed measures. -/
theorem trim_sup (m₁ m₂ : outer_measure α) : (m₁ ⊔ m₂).trim = m₁.trim ⊔ m₂.trim :=
ext $ λ s, (trim_binop (sup_apply m₁ m₂) s).trans (sup_apply _ _ _).symm

/-- `trim` sends the supremum of a countable family of outer measures to the supremum
of the trimmed measures. -/
lemma trim_supr {ι} [countable ι] (μ : ι → outer_measure α) : trim (⨆ i, μ i) = ⨆ i, trim (μ i) :=
begin
  simp_rw [←@supr_plift_down _ ι],
  ext1 s,
  haveI : countable (option $ plift ι) := @option.countable (plift ι) _,
  obtain ⟨t, hst, ht, hμt⟩ := exists_measurable_superset_forall_eq_trim
    (option.elim (⨆ i, μ (plift.down i)) (μ ∘ plift.down)) s,
  simp only [option.forall, option.elim] at hμt,
  simp only [supr_apply, ← hμt.1, ← hμt.2]
end

/-- The trimmed property of a measure μ states that `μ.to_outer_measure.trim = μ.to_outer_measure`.
This theorem shows that a restricted trimmed outer measure is a trimmed outer measure. -/
lemma restrict_trim {μ : outer_measure α} {s : set α} (hs : measurable_set s) :
  (restrict s μ).trim = restrict s μ.trim :=
begin
  refine le_antisymm (λ t, _) (le_trim_iff.2 $ λ t ht, _),
  { rw restrict_apply,
    rcases μ.exists_measurable_superset_eq_trim (t ∩ s) with ⟨t', htt', ht', hμt'⟩,
    rw [← hμt'], rw inter_subset at htt',
    refine (mono' _ htt').trans _,
    rw [trim_eq _ (hs.compl.union ht'), restrict_apply, union_inter_distrib_right,
      compl_inter_self, set.empty_union],
    exact μ.mono' (inter_subset_left _ _) },
  { rw [restrict_apply, trim_eq _ (ht.inter hs), restrict_apply],
    exact le_rfl }
end

end outer_measure

end measure_theory
