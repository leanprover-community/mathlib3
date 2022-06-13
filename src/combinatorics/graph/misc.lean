import tactic
import algebra.big_operators.finprod
import data.fintype.card
import set_theory.cardinal.finite
import logic.equiv.fin

open_locale classical big_operators
noncomputable theory


@[simp] lemma finsum_ones_eq_card(α : Type*):
  ∑ᶠ (x : α), 1 = nat.card α :=
begin
  by_cases (nonempty (fintype α)),
  swap,
  { simp only [not_nonempty_iff, is_empty_fintype] at h,
    rw [←finsum_mem_univ, @nat.card_eq_zero_of_infinite _ h, finsum_mem_eq_zero_of_infinite],
    rw [set.univ_inter, function.support_const (nat.one_ne_zero)],
    exact set.infinite_univ_iff.mpr h},
  cases h,
  haveI : fintype α := h,
  rw [finsum_eq_sum_of_fintype, nat.card_eq_fintype_card, ←finset.card_univ],
  simp,
end


@[simp] lemma finsum_mem_ones_eq_card {α : Type*} (S : set α):
  ∑ᶠ (x ∈ S), 1 = nat.card S :=
by {rw [←finsum_ones_eq_card, ←finsum_subtype_eq_finsum_cond], refl}


lemma fin.fin_two_eq_zero_or_one (u : fin 2):
  u = 0 ∨ u = 1 :=
fin.exists_fin_two.mp ⟨u, rfl⟩

lemma fin_two_of_one_zero {P : fin 2 → Prop}(x : fin 2):
  P 0 → P 1 → P x :=
λ h0 h1, or.elim (fin.exists_fin_two.mp ⟨x, rfl⟩)
  (λ hx, eq.subst hx.symm h0) (λ hx, eq.subst hx.symm h1)

lemma fin.fin_two_eq_or_eq_add_one (u v : fin 2):
  u = v ∨ u = v + 1 :=
or.elim (fin.exists_fin_two.mp ⟨u-v, rfl⟩)
  (λ h, or.inl (sub_eq_zero.mp h))
  (λ h, or.inr (eq_add_of_sub_eq' h))

@[simp] lemma fin.fin_two_one_add_one:
  (1 : fin 2) + 1  = 0 :=
rfl

lemma equiv.eq_add_of_equiv_fin_two (φ : fin 2 ≃ fin 2):
  ∃ j, ∀ i, φ i = i + j :=
begin
   simp_rw add_comm,
   exact ⟨φ 0, fin.forall_fin_two.mpr
    ⟨by {rw add_zero}, or.elim (fin.fin_two_eq_or_eq_add_one (φ 1) (φ 0))
    (λ h, false.elim (fin.zero_ne_one ((φ.injective h).symm))) id⟩⟩,
end

lemma fin.Union_fin_two {α : Type*} (s : fin 2 → set α):
  (⋃ (i : fin 2), s i) = (s 0 ∪ s 1) :=
set.ext (λ x, by rw [set.mem_Union, fin.exists_fin_two, set.mem_union])

lemma fin.Inter_fin_two {α : Type*} (s : fin 2 → set α):
  (⋂ (i : fin 2), s i) = (s 0 ∩ s 1) :=
set.ext (λ x, by rw [set.mem_Inter, fin.forall_fin_two, set.mem_inter_iff])
