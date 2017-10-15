/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Outer measures -- overapproximations of measures
-/

import data.set order.galois_connection algebra.big_operators
       analysis.ennreal analysis.limits
       analysis.measure_theory.measurable_space

noncomputable theory

open classical set lattice finset function filter
open ennreal (of_real)
local attribute [instance] decidable_inhabited prop_decidable

open classical

namespace measure_theory

structure outer_measure (α : Type*) :=
(measure_of : set α → ennreal)
(empty : measure_of ∅ = 0)
(mono : ∀{s₁ s₂}, s₁ ⊆ s₂ → measure_of s₁ ≤ measure_of s₂)
(Union_nat : ∀{s:ℕ → set α}, measure_of (⋃i, s i) ≤ (∑i, measure_of (s i)))

namespace outer_measure
section
parameters {α : Type*} (m : outer_measure α)
include m

variables {s s₁ s₂ : set α}

local notation `μ` := m.measure_of

lemma subadditive : μ (s₁ ∪ s₂) ≤ μ s₁ + μ s₂ :=
let s := λi, ([s₁, s₂].nth i).get_or_else ∅ in
calc μ (s₁ ∪ s₂) ≤ μ (⋃i, s i) :
    m.mono $ union_subset (subset_Union s 0) (subset_Union s 1)
  ... ≤ (∑i, μ (s i)) : @outer_measure.Union_nat α m s
  ... = (insert 0 {1} : finset ℕ).sum (μ ∘ s) : tsum_eq_sum $ assume n h,
    match n, h with
    | 0, h := by simp at h; contradiction
    | 1, h := by simp at h; contradiction
    | nat.succ (nat.succ n), h := m.empty
    end
  ... = μ s₁ + μ s₂ : by simp [-add_comm]; refl

end

section of_function
set_option eqn_compiler.zeta true

-- TODO: if we move this proof into the definition of inf it does not terminate anymore
private lemma aux {ε : ℝ} (hε : 0 < ε) : (∑i, of_real ((ε / 2) * 2⁻¹ ^ i)) = of_real ε :=
let ε' := λi, (ε / 2) * 2⁻¹ ^ i in
have hε' : ∀i, 0 < ε' i,
  from assume i, mul_pos (div_pos_of_pos_of_pos hε two_pos) $ pow_pos (inv_pos two_pos) _,
have is_sum (λi, 2⁻¹ ^ i : ℕ → ℝ) (1 / (1 - 2⁻¹)),
  from is_sum_geometric (le_of_lt $ inv_pos two_pos) $ inv_lt_one one_lt_two,
have is_sum (λi, ε' i) ((ε / 2) * (1 / (1 - 2⁻¹))),
  from is_sum_mul_left this,
have eq : ((ε / 2) * (1 / (1 - 2⁻¹))) = ε,
begin
  have ne_two : (2:ℝ) ≠ 0, from (ne_of_lt two_pos).symm,
  rw [inv_eq_one_div, sub_eq_add_neg, ←neg_div, add_div_eq_mul_add_div _ _ ne_two],
  simp [bit0, bit1] at ne_two,
  simp [bit0, bit1, mul_div_cancel' _ ne_two]
end,
have is_sum (λi, ε' i) ε, begin rw [eq] at this, exact this end,
ennreal.tsum_of_real this (assume i, le_of_lt $ hε' i)

protected def of_function {α : Type*} (m : set α → ennreal) (m_empty : m ∅ = 0) :
  outer_measure α :=
let μ := λs, ⨅{f : ℕ → set α} (h : s ⊆ ⋃i, f i), ∑i, m (f i) in
{ measure_of := μ,
  empty      := le_antisymm
    (infi_le_of_le (λ_, ∅) $ infi_le_of_le (empty_subset _) $ by simp [m_empty])
    zero_le,
  mono       := assume s₁ s₂ hs, infi_le_infi $ assume f,
    infi_le_infi2 $ assume hb, ⟨subset.trans hs hb, le_refl _⟩,
  Union_nat := assume s, ennreal.le_of_forall_epsilon_le $
    assume ε hε (hb : (∑i, μ (s i)) < ⊤),
    let ε' := λi, (ε / 2) * 2⁻¹ ^ i in
    have hε' : ∀i, 0 < ε' i,
      from assume i, mul_pos (div_pos_of_pos_of_pos hε two_pos) $ pow_pos (inv_pos two_pos) _,
    have ∀i, ∃f:ℕ → set α, s i ⊆ (⋃i, f i) ∧ (∑i, m (f i)) < μ (s i) + of_real (ε' i),
      from assume i,
      have μ (s i) < μ (s i) + of_real (ε' i),
        from ennreal.lt_add_right
          (calc μ (s i) ≤ (∑i, μ (s i)) : ennreal.le_tsum
            ... < ⊤ : hb)
          (by simp; exact hε' _),
      by simpa [μ, infi_lt_iff] using this,
    let ⟨f, hf⟩ := axiom_of_choice this in
    let f' := λi, f (nat.unpair i).1 (nat.unpair i).2 in
    have hf' : (⋃ (i : ℕ), s i) ⊆ (⋃i, f' i),
      from Union_subset $ assume i, subset.trans (hf i).left $ Union_subset_Union2 $ assume j,
      ⟨nat.mkpair i j, begin simp [f'], simp [nat.unpair_mkpair], exact subset.refl _ end⟩,
    have (∑i, of_real (ε' i)) = of_real ε, from aux hε,
    have (∑i, m (f' i)) ≤ (∑i, μ (s i)) + of_real ε,
      from calc (∑i, m (f' i)) = (∑p:ℕ×ℕ, m (f' (nat.mkpair p.1 p.2))) :
          (tsum_eq_tsum_of_iso (λp:ℕ×ℕ, nat.mkpair p.1 p.2) nat.unpair
            (assume ⟨a, b⟩, nat.unpair_mkpair a b) nat.mkpair_unpair).symm
        ... = (∑i, ∑j, m (f i j)) :
          by dsimp [f']; rw [←ennreal.tsum_prod]; simp [nat.unpair_mkpair]
        ... ≤ (∑i, μ (s i) + of_real (ε' i)) :
          ennreal.tsum_le_tsum $ assume i, le_of_lt $ (hf i).right
        ... ≤ (∑i, μ (s i)) + (∑i, of_real (ε' i)) : by rw [tsum_add]; exact ennreal.has_sum
        ... = (∑i, μ (s i)) + of_real ε : by rw [this],
    show μ (⋃ (i : ℕ), s i) ≤ (∑ (i : ℕ), μ (s i)) + of_real ε,
      from infi_le_of_le f' $ infi_le_of_le hf' $ this }

end of_function

section caratheodory_measurable
universe u
parameters {α : Type u} (m : outer_measure α)
include m

local notation `μ` := m.measure_of

variables {s s₁ s₂ : set α}

private def C (s : set α) := ∀t, μ t = μ (t ∩ s) + μ (t \ s)

@[simp] private lemma C_empty : C ∅ := by simp [C, m.empty, sdiff_empty]

private lemma C_compl : C s₁ → C (- s₁) := by simp [C, sdiff_eq]

@[simp] private lemma C_compl_iff : C (- s) ↔ C s :=
⟨assume h, let h' := C_compl h in by simp at h'; assumption, C_compl⟩

private lemma C_union (h₁ : C s₁) (h₂ : C s₂) : C (s₁ ∪ s₂) :=
assume t,
have e₁ : (s₁ ∪ s₂) ∩ s₁ ∩ s₂ = s₁ ∩ s₂,
  from set.ext $ assume x, by simp [iff_def] {contextual := tt},
have e₂ : (s₁ ∪ s₂) ∩ s₁ ∩ -s₂ = s₁ ∩ -s₂,
  from set.ext $ assume x, by simp [iff_def] {contextual := tt},
calc μ t = μ (t ∩ s₁ ∩ s₂) + μ (t ∩ s₁ ∩ -s₂) + μ (t ∩ -s₁ ∩ s₂) + μ (t ∩ -s₁ ∩ -s₂) :
    by rw [h₁ t, h₂ (t ∩ s₁), h₂ (t \ s₁)]; simp [sdiff_eq]
  ... = μ (t ∩ ((s₁ ∪ s₂) ∩ s₁ ∩ s₂)) + μ (t ∩ ((s₁ ∪ s₂) ∩ s₁ ∩ -s₂)) +
      μ (t ∩ s₂ ∩ -s₁) + μ (t ∩ -s₁ ∩ -s₂) :
    by rw [e₁, e₂]; simp
  ... = ((μ (t ∩ (s₁ ∪ s₂) ∩ s₁ ∩ s₂) + μ ((t ∩ (s₁ ∪ s₂) ∩ s₁) \ s₂)) +
      μ (t ∩ ((s₁ ∪ s₂) \ s₁))) + μ (t \ (s₁ ∪ s₂)) :
    by rw [union_sdiff_right]; simp [sdiff_eq]
  ... = μ (t ∩ (s₁ ∪ s₂)) + μ (t \ (s₁ ∪ s₂)) :
    by rw [h₁ (t ∩ (s₁ ∪ s₂)), h₂ ((t ∩ (s₁ ∪ s₂)) ∩ s₁)]; simp [sdiff_eq]

private lemma C_Union_lt {s : ℕ → set α} : ∀{n:ℕ}, (∀i<n, C (s i)) → C (⋃i<n, s i)
| 0       h := by simp [nat.not_lt_zero]
| (n + 1) h := show C (⨆i < nat.succ n, s i),
  begin
    simp [nat.lt_succ_iff_lt_or_eq, supr_or, supr_sup_eq],
    exact C_union m (h n (le_refl (n + 1)))
      (C_Union_lt $ assume i hi, h i $ lt_of_lt_of_le hi $ nat.le_succ _)
  end

private lemma C_inter (h₁ : C s₁) (h₂ : C s₂) : C (s₁ ∩ s₂) :=
by rw [←C_compl_iff, compl_inter]; from C_union _ (C_compl _ h₁) (C_compl _ h₂)

private lemma C_sum {s : ℕ → set α} (h : ∀i, C (s i)) (hd : pairwise (disjoint on s)) {n} {t : set α} :
  (finset.range n).sum (λi, μ (t ∩ s i)) = μ (t ∩ ⋃i<n, s i) :=
begin
  induction n,
  case nat.zero { simp [nat.not_lt_zero, m.empty] },
  case nat.succ n ih {
    have disj : ∀x i, x ∈ s n → i < n → x ∉ s i,
      from assume x i hn h hi,
      have hx : x ∈ s i ∩ s n, from ⟨hi, hn⟩,
      have s i ∩ s n = ∅, from hd _ _ (ne_of_lt h),
      by rwa [this] at hx,
    have : (⋃i<n+1, s i) \ (⋃i<n, s i) = s n,
    { apply set.ext, intro x, simp,
      constructor,
      from assume ⟨hx, i, hi, hin⟩, (nat.lt_succ_iff_lt_or_eq.mp hin).elim
        (assume h, (hx i h hi).elim)
        (assume h, h ▸ hi),
      from assume hx, ⟨assume i, disj x i hx, ⟨n, hx, nat.lt_succ_self _⟩⟩ },
    have e₁ : t ∩ s n = (t ∩ ⋃i<n+1, s i) \ ⋃i<n, s i,
      from calc t ∩ s n = t ∩ ((⋃i<n+1, s i) \ (⋃i<n, s i)) : by rw [this]
        ... = (t ∩ ⋃i<n+1, s i) \ ⋃i<n, s i : by simp [sdiff_eq],
    have : (⋃i<n+1, s i) ∩ (⋃i<n, s i) = (⋃i<n, s i),
      from (inf_of_le_right $ supr_le_supr $ assume i, supr_le_supr_const $
        assume hin, lt_trans hin (nat.lt_succ_self n)),
    have e₂ : t ∩ (⋃i<n, s i) = (t ∩ ⋃i<n+1, s i) ∩ ⋃i<n, s i,
      from calc t ∩ (⋃i<n, s i) = t ∩ ((⋃i<n+1, s i) ∩ (⋃i<n, s i)) : by rw [this]
        ... = _ : by simp,
    have : C _ (⋃i<n, s i),
      from C_Union_lt m (assume i _, h i),
    from calc (range (nat.succ n)).sum (λi, μ (t ∩ s i)) = μ (t ∩ s n) + μ (t ∩ ⋃i < n, s i) :
        by simp [range_succ, sum_insert, lt_irrefl, ih]
      ... = μ ((t ∩ ⋃i<n+1, s i) ∩ ⋃i<n, s i) + μ ((t ∩ ⋃i<n+1, s i) \ ⋃i<n, s i) :
        by rw [e₁, e₂]; simp
      ... = μ (t ∩ ⋃i<n+1, s i) : (this $ t ∩ ⋃i<n+1, s i).symm }
end

private lemma C_Union_nat {s : ℕ → set α} (h : ∀i, C (s i)) (hd : pairwise (disjoint on s)) :
  C (⋃i, s i) :=
assume t,
suffices μ t ≥ μ (t ∩ (⋃i, s i)) + μ (t \ (⋃i, s i)),
  from le_antisymm
    (calc μ t ≤ μ (t ∩ (⋃i, s i) ∪ t \ (⋃i, s i)) :
      m.mono $ assume x ht, by by_cases x ∈ (⋃i, s i); simp [*] at *
      ... ≤ μ (t ∩ (⋃i, s i)) + μ (t \ (⋃i, s i)) : m.subadditive)
    this,
have hp : μ (t ∩ ⋃i, s i) ≤ (⨆n, μ (t ∩ ⋃i<n, s i)),
  from calc μ (t ∩ ⋃i, s i) = μ (⋃i, t ∩ s i) : by rw [inter_distrib_Union_left]
    ... ≤ ∑i, μ (t ∩ s i) : @outer_measure.Union_nat α m _
    ... = ⨆n, (finset.range n).sum (λi, μ (t ∩ s i)) : ennreal.tsum_eq_supr_nat
    ... = ⨆n, μ (t ∩ ⋃i<n, s i) : congr_arg _ $ funext $ assume n, C_sum h hd,
have hn : ∀n, μ (t \ (⋃i<n, s i)) ≥ μ (t \ (⋃i, s i)),
  from assume n,
    m.mono $ sdiff_subset_sdiff (subset.refl t) $ bUnion_subset $ assume i _, le_supr s i,
calc μ (t ∩ (⋃i, s i)) + μ (t \ (⋃i, s i)) ≤ (⨆n, μ (t ∩ ⋃i<n, s i)) + μ (t \ (⋃i, s i)) :
    add_le_add' hp (le_refl _)
  ... = (⨆n, μ (t ∩ ⋃i<n, s i) + μ (t \ (⋃i, s i))) :
    ennreal.supr_add
  ... ≤ (⨆n, μ (t ∩ ⋃i<n, s i) + μ (t \ (⋃i<n, s i))) :
    supr_le_supr $ assume i, add_le_add' (le_refl _) (hn _)
  ... ≤ μ t : supr_le $ assume n, le_of_eq (C_Union_lt (assume i _, h i) t).symm

private lemma f_Union {s : ℕ → set α} (h : ∀i, C (s i)) (hd : pairwise (disjoint on s)) :
  μ (⋃i, s i) = ∑i, μ (s i) :=
have ∀n, (finset.range n).sum (λ (i : ℕ), μ (s i)) ≤ μ (⋃ (i : ℕ), s i),
  from assume n,
  calc (finset.range n).sum (λi, μ (s i)) = (finset.range n).sum (λi, μ (univ ∩ s i)) :
      by simp [univ_inter]
    ... = μ (⋃i<n, s i) :
      by rw [C_sum _ h hd, univ_inter]
    ... ≤ μ (⋃ (i : ℕ), s i) : m.mono $ bUnion_subset $ assume i _, le_supr s i,
suffices μ (⋃i, s i) ≥ ∑i, μ (s i),
  from le_antisymm (@outer_measure.Union_nat α m s) this,
calc (∑i, μ (s i)) = (⨆n, (finset.range n).sum (λi, μ (s i))) : ennreal.tsum_eq_supr_nat
  ... ≤ _ : supr_le this

private def caratheodory_dynkin : measurable_space.dynkin_system α :=
{ has := C,
  has_empty := C_empty,
  has_compl := assume s, C_compl,
  has_Union := assume f hf hn, C_Union_nat hn hf }

protected def caratheodory : measurable_space α :=
caratheodory_dynkin.to_measurable_space $ assume s₁ s₂, C_inter

lemma caratheodory_is_measurable_eq {s : set α} :
  caratheodory.is_measurable s = ∀t, μ t = μ (t ∩ s) + μ (t \ s) :=
rfl

protected lemma Union_eq_of_caratheodory {s : ℕ → set α}
  (h : ∀i, caratheodory.is_measurable (s i)) (hd : pairwise (disjoint on s)) :
  μ (⋃i, s i) = ∑i, μ (s i) :=
f_Union h hd

lemma caratheodory_is_measurable {m : set α → ennreal} {s : set α}
  {h₀ : m ∅ = 0} (hs : ∀t, m (t ∩ s) + m (t \ s) ≤ m t) :
  (outer_measure.of_function m h₀).caratheodory.is_measurable s :=
let o := (outer_measure.of_function m h₀), om := o.measure_of in
assume t,
le_antisymm
  (calc om t = om ((t ∩ s) ∪ (t \ s)) :
      congr_arg om (set.ext $ assume x, by by_cases x ∈ s; simp [iff_def, *])
    ... ≤ om (t ∩ s) + om (t \ s) :
      o.subadditive)
  (le_infi $ assume f, le_infi $ assume hf,
    have h₁ : t ∩ s ⊆ ⋃i, f i ∩ s,
      by rw [←inter_distrib_Union_right]; from inter_subset_inter hf (subset.refl s),
    have h₂ : t \ s ⊆ ⋃i, f i \ s,
      from subset.trans (sdiff_subset_sdiff hf (subset.refl s)) $
        by simp [subset_def] {contextual := tt},
    calc om (t ∩ s) + om (t \ s) ≤ (∑i, m (f i ∩ s)) + (∑i, m (f i \ s)) :
        add_le_add'
          (infi_le_of_le (λi, f i ∩ s) $ infi_le_of_le h₁ $ le_refl _)
          (infi_le_of_le (λi, f i \ s) $ infi_le_of_le h₂ $ le_refl _)
      ... = (∑i, m (f i ∩ s) + m (f i \ s)) :
        by rw [tsum_add]; exact ennreal.has_sum
      ... ≤ (∑i, m (f i)) :
        ennreal.tsum_le_tsum $ assume i, hs _)

end caratheodory_measurable

end outer_measure

end measure_theory
