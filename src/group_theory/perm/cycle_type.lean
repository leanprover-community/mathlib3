import group_theory.perm.cycles
import combinatorics.partition
import data.multiset.gcd

namespace equiv.perm
open equiv

variables {α : Type*} [fintype α] [decidable_eq α]

lemma thm0
  (σ τ : perm α)
  (h : disjoint σ τ)
  (a : α) (ha : τ a = a) :
  (σ * τ).cycle_of a = σ.cycle_of a :=
begin
  ext b,
  simp_rw [cycle_of_apply, same_cycle, commute.mul_gpow h.mul_comm, mul_apply,
    gpow_apply_eq_self_of_apply_eq_self ha],
  by_cases h : ∃ i : ℤ, (σ ^ i) a = b,
  { rw [if_pos, if_pos],
    { obtain ⟨i, rfl⟩ := h,
      rw [←mul_apply, ←mul_apply, mul_assoc],
      simp_rw show τ * σ ^ i = σ ^ i * τ, from commute.gpow_right h.mul_comm.symm i,
      rw [mul_apply, mul_apply, ha] },
    { exact h },
    { exact h} },
  { rw [if_neg, if_neg],
    { exact h },
    { exact h } },
end

lemma thm1
  (σ τ : perm α)
  (h : disjoint σ τ)
  (c : perm α)
  (a : α)
  (hc : c a ≠ a) :
  (σ * τ).cycle_of a = c ↔ (σ.cycle_of a = c ∨ τ.cycle_of a = c) :=
begin
  have hc' : c ≠ 1 := λ h, hc (ext_iff.mp h a),
  cases (h a) with ha ha,
  { rw [σ.cycle_of_eq_one_iff.mpr ha, or_iff_right_of_imp (λ h, false.elim (hc'.symm h))],
    rw [h.mul_comm, thm0 τ σ h.symm a ha] },
  { rw [τ.cycle_of_eq_one_iff.mpr ha, or_iff_left_of_imp (λ h, false.elim (hc'.symm h))],
    rw [thm0 σ τ h a ha] },
end

lemma thm2
  (σ : perm α)
  (hσ : σ.is_cycle)
  (c : perm α)
  (a : α)
  (hc : c a ≠ a) :
  σ.cycle_of a = c ↔ c = σ :=
begin
  split,
  { rintro rfl,
    rw [hσ.cycle_of, ite_eq_right_iff],
    intro h,
    rw [hσ.cycle_of, if_pos h] at hc,
    exact (hc rfl).elim },
  { rintro rfl,
    rw [hσ.cycle_of, if_neg hc] },
end

lemma thm3
  (l : list (perm α))
  (h1 : ∀ σ : perm α, σ ∈ l → σ.is_cycle)
  (h2 : l.pairwise disjoint)
  (c : perm α) (a : α) (hc : c a ≠ a) :
  c ∈ l ↔ l.prod.cycle_of a = c :=
begin
  induction l with σ l ih,
  { exact ⟨false.elim, λ h, hc (ext_iff.mp (h.symm.trans (cycle_of_one a)) a)⟩ },
  { have x := ih (λ τ hτ, h1 τ (list.mem_cons_of_mem σ hτ)) (list.pairwise_of_pairwise_cons h2),
    have y := thm1 σ l.prod (disjoint_prod_list_of_disjoint (list.pairwise_cons.mp h2).1) c a hc,
    have z := thm2 σ (h1 σ (l.mem_cons_self σ)) c a hc,
    rw [list.mem_cons_iff, list.prod_cons, x, y, z] },
end

lemma thm4
  (l : list (perm α))
  (h1 : (1 : perm α) ∉ l)
  (h2 : l.pairwise disjoint) :
  l.nodup :=
begin
  refine list.pairwise.imp_of_mem _ h2,
  rintros σ - h_mem - h_disjoint rfl,
  suffices : σ = 1,
  { rw this at h_mem,
    exact h1 h_mem },
  exact ext (λ a, (or_self _).mp (h_disjoint a)),
end

lemma thm5
  (l₁ l₂ : list (perm α))
  (h₀ : l₁.prod = l₂.prod)
  (h₁l₁ : ∀ σ : perm α, σ ∈ l₁ → σ.is_cycle)
  (h₁l₂ : ∀ σ : perm α, σ ∈ l₂ → σ.is_cycle)
  (h₂l₁ : l₁.pairwise disjoint)
  (h₂l₂ : l₂.pairwise disjoint) :
l₁ ~ l₂ :=
begin
  have h₃l₁ : (1 : perm α) ∉ l₁ := λ h, (h₁l₁ 1 h).ne_one rfl,
  have h₃l₂ : (1 : perm α) ∉ l₂ := λ h, (h₁l₂ 1 h).ne_one rfl,
  refine (list.perm_ext (thm4 l₁ h₃l₁ h₂l₁) (thm4 l₂ h₃l₂ h₂l₂)).mpr (λ c, _),
  by_cases hc : c = 1,
  { rw hc,
    exact iff_of_false h₃l₁ h₃l₂ },
  { obtain ⟨a, hc⟩ := not_forall.mp (mt ext hc),
    rw [thm3 l₁ h₁l₁ h₂l₁ c a hc, thm3 l₂ h₁l₂ h₂l₂ c a hc, h₀] },
end

def cycle_type (σ : perm α) : multiset ℕ :=
σ.trunc_cycle_factors.lift (λ l, l.1.map (finset.card ∘ support)) (λ l₁ l₂, multiset.coe_eq_coe.mpr
(list.perm.map _ (thm5 l₁.1 l₂.1 (l₁.2.1.trans l₂.2.1.symm) l₁.2.2.1 l₂.2.2.1 l₁.2.2.2 l₂.2.2.2)))

lemma cycle_type_eq
  (σ : perm α)
  (l : list (perm α))
  (h0 : l.prod = σ)
  (h1 : ∀ σ : perm α, σ ∈ l → σ.is_cycle)
  (h2 : l.pairwise disjoint) :
  σ.cycle_type = l.map (finset.card ∘ support) :=
by rw [cycle_type, trunc.eq σ.trunc_cycle_factors (trunc.mk ⟨l, h0, h1, h2⟩), trunc.lift_mk]

lemma cycle_type_one : (1 : perm α).cycle_type = 0 :=
cycle_type_eq (1 : perm α) [] rfl (λ _, false.elim) list.pairwise.nil

lemma is_cycle.cycle_type {σ : perm α} (hσ : is_cycle σ) : σ.cycle_type = [σ.support.card] :=
cycle_type_eq σ [σ] (mul_one σ) (λ τ hτ, (congr_arg is_cycle (list.mem_singleton.mp hτ)).mpr hσ)
  (list.pairwise_singleton disjoint σ)

lemma disjoint.cycle_type {σ τ : perm α} (h : disjoint σ τ) :
  (σ * τ).cycle_type = σ.cycle_type + τ.cycle_type :=
begin
  let x := σ.trunc_cycle_factors.out,
  let y := τ.trunc_cycle_factors.out,
  rw [cycle_type_eq σ x.1 x.2.1 x.2.2.1 x.2.2.2, cycle_type_eq τ y.1 y.2.1 y.2.2.1 y.2.2.2],
  rw [cycle_type_eq (σ * τ) (x.1 ++ y.1) _ _ _, list.map_append, ←multiset.coe_add],
  { rw [list.prod_append, x.2.1, y.2.1] },
  { exact λ f hf, (list.mem_append.mp hf).elim (x.2.2.1 f) (y.2.2.1 f) },
  { refine list.pairwise_append.mpr ⟨x.2.2.2, y.2.2.2, λ f hf g hg, _⟩,
    rw [←x.2.1, ←y.2.1] at h,
    sorry },
end

lemma two_le_of_mem_cycle_type (σ : perm α) {n : ℕ} (h : n ∈ σ.cycle_type) : 2 ≤ n :=
begin
  rw [cycle_type, ←σ.trunc_cycle_factors.out_eq] at h,
  obtain ⟨τ, hτ, rfl⟩ := list.mem_map.mp h,
  exact (σ.trunc_cycle_factors.out.2.2.1 τ hτ).two_le_card_support,
end

lemma one_lt_of_mem_cycle_type (σ : perm α) {n : ℕ} (h : n ∈ σ.cycle_type) : 1 < n :=
σ.two_le_of_mem_cycle_type h

lemma sum_cycle_type (σ : perm α) : σ.cycle_type.sum = σ.support.card :=
begin
  apply induction_on_cycles (λ τ : perm α, τ.cycle_type.sum = τ.support.card),
  { rw [cycle_type_one, multiset.sum_zero, support_one, finset.card_empty] },
  { intros σ hσ,
    rw [hσ.cycle_type, multiset.coe_sum, list.sum_singleton] },
  { intros σ τ hστ hσ hτ,
    rw [hστ.cycle_type, multiset.sum_add, hστ.card_support_mul, hσ, hτ] },
end

instance : gcd_monoid ℕ :=
{ gcd            := nat.gcd,
  lcm            := nat.lcm,
  gcd_dvd_left   := nat.gcd_dvd_left,
  gcd_dvd_right  := nat.gcd_dvd_right,
  dvd_gcd        := λ _ _ _, nat.dvd_gcd,
  normalize_gcd  := λ a b, nat.mul_one (a.gcd b),
  gcd_mul_lcm    := λ a b, (a.gcd_mul_lcm b).trans (mul_one (a * b)).symm,
  lcm_zero_left  := nat.lcm_zero_left,
  lcm_zero_right := nat.lcm_zero_right,
  norm_unit := λ _, 1,
  norm_unit_zero := rfl,
  norm_unit_mul := λ _ _ _ _, rfl,
  norm_unit_coe_units := λ u,
    by rw [(show u = 1, from units.ext (nat.is_unit_iff.mp u.is_unit)), one_inv] }

lemma lcm_cycle_type (σ : perm α) : σ.cycle_type.lcm = order_of σ :=
begin
  apply induction_on_cycles (λ τ : perm α, τ.cycle_type.lcm = order_of τ),
  { rw [cycle_type_one, multiset.lcm_zero, order_of_one] },
  { intros σ hσ,
    rw [hσ.cycle_type, ←multiset.singleton_coe, multiset.lcm_singleton, order_of_is_cycle hσ],
    exact mul_one _ },--hacky normalize stuff
  { intros σ τ hστ hσ hτ,
    rw [hστ.cycle_type, multiset.lcm_add],
    sorry, },
end

lemma dvd_of_mem_cycle_type (σ : perm α) {n : ℕ} (h : n ∈ σ.cycle_type) : n ∣ order_of σ :=
begin
  rw ← lcm_cycle_type,
  exact multiset.dvd_lcm h,
end

def partition (σ : perm α) : partition (fintype.card α) :=
{ parts := sorry,
  parts_pos := sorry,
  parts_sum := sorry }

end equiv.perm
