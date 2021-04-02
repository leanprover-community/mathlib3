import group_theory.perm.cycles

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
  (h₁l₁ : ∀ σ : perm α, σ ∈ l₁ → σ.is_cycle)
  (h₁l₂ : ∀ σ : perm α, σ ∈ l₂ → σ.is_cycle)
  (h₂l₁ : l₁.pairwise disjoint)
  (h₂l₂ : l₂.pairwise disjoint)
  (h₃ : l₁.prod = l₂.prod) :
l₁ ~ l₂ :=
begin
  have h₃l₁ : (1 : perm α) ∉ l₁ := λ h, (h₁l₁ 1 h).ne_one rfl,
  have h₃l₂ : (1 : perm α) ∉ l₂ := λ h, (h₁l₂ 1 h).ne_one rfl,
  refine (list.perm_ext (thm4 l₁ h₃l₁ h₂l₁) (thm4 l₂ h₃l₂ h₂l₂)).mpr (λ c, _),
  by_cases hc : c = 1,
  { rw hc,
    exact iff_of_false h₃l₁ h₃l₂ },
  { obtain ⟨a, hc⟩ := not_forall.mp (mt ext hc),
    rw [thm3 l₁ h₁l₁ h₂l₁ c a hc, thm3 l₂ h₁l₂ h₂l₂ c a hc, h₃] },
end

def cycle_type (σ : perm α) : multiset ℕ :=
σ.trunc_cycle_factors.lift (λ l, l.1.map (finset.card ∘ support)) (λ l₁ l₂, multiset.coe_eq_coe.mpr
(list.perm.map _ (thm5 l₁.1 l₂.1 l₁.2.2.1 l₂.2.2.1 l₁.2.2.2 l₂.2.2.2 (l₁.2.1.trans l₂.2.1.symm))))

end equiv.perm
