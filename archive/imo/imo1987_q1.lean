import data.fintype.card
import dynamics.fixed_points.basic

variables (α : Type*) [fintype α] [decidable_eq α]

open_locale big_operators nat
open equiv fintype function finset (range sum_const) set (Iic)

namespace imo_1987_q1

def fixed_points_equiv : {σx : α × perm α | σx.2 σx.1 = σx.1} ≃ Σ x : α, perm ({x}ᶜ : set α) :=
calc {σx : α × perm α | σx.2 σx.1 = σx.1} ≃ Σ x : α, {σ : perm α | σ x = x} : set_prod_equiv_sigma _
... ≃ Σ x : α, {σ : perm α | ∀ y : ({x} : set α), σ y = equiv.refl ↥({x} : set α) y} :
  sigma_congr_right (λ x, equiv.set.of_eq $ by { simp only [set_coe.forall], dsimp, simp })
... ≃ Σ x : α, perm ({x}ᶜ : set α) :
  sigma_congr_right (λ x, by apply equiv.set.compl)

theorem card_fixed_points (h : 0 < card α) :
  card {σx : α × perm α | σx.2 σx.1 = σx.1} = (card α)! :=
begin
  rw [card_congr (fixed_points_equiv α)],
  simp [card_perm, finset.filter_not, finset.card_sdiff, finset.filter_eq', finset.card_univ,
    nat.mul_factorial_pred h]
end

@[derive fintype]
def fiber (k : ℕ) : set (perm α) := {σ : perm α | card (fixed_points σ) = k}

def p (k : ℕ) := card (fiber α k)

def fixed_points_equiv' : (Σ (k : fin (card α + 1)) (σ : fiber α k), fixed_points σ.1) ≃
  {σx : α × perm α | σx.2 σx.1 = σx.1} :=
calc (Σ (k : fin (card α + 1)) (σ : fiber α k), fixed_points σ.1) ≃
  (Σ (k : Iic (card α)) (σ : fiber α k), fixed_points σ.1) :
  sigma_congr ((fin_equiv_subtype _).trans $ set.of_eq $ set.ext $ λ m, nat.lt_succ_iff)
    (λ _, equiv.refl _)
... ≃   Σ k : Iic (card α), {σx : Σ σ : perm α, fixed_points σ // card (fixed_points σx.1) = k} :
  sigma_congr_right $ λ k, (subtype_sigma_equiv (λ σ : perm α, fixed_points σ) _).symm
... ≃ Σ σ : perm α, fixed_points σ :
  sigma_subtype_preimage_equiv _ _ (λ σ, fintype.card_subtype_le _)
... ≃ {σx : perm α × α | σx.1 σx.2 = σx.2} : equiv.symm (set_prod_equiv_sigma _)
... ≃ _ : (equiv.prod_comm _ _).subtype_equiv_of_subtype'

theorem main' (h : 0 < card α) : ∑ k in range (card α + 1), k * p α k = (card α)! :=
have ∀ k (σ : fiber α k), card {x | σ.1 x = x} = k := λ k σ, σ.2,
calc ∑ k in range (card α + 1), k * p α k =
  ∑ k in range (card α + 1), card (Σ σ : fiber α k, {x | σ.1 x = x}) :
  by simp_rw [fintype.card_sigma, this, sum_const, p, nat.nsmul_eq_mul, fintype.card, mul_comm]
... = ∑ k : fin (card α + 1), card (Σ σ : fiber α k, {x | σ.1 x = x}) :
  by rw [← fin.sum_univ_eq_sum_range]
... = card (Σ (k : fin (card α + 1)) (σ : fiber α k), {x | σ.1 x = x}) : (card_sigma _).symm
... = card {σx : α × perm α | σx.2 σx.1 = σx.1} : card_congr (fixed_points_equiv' _)
... = (card α)! : card_fixed_points _ h


theorem main {n : ℕ} (hn : 1 ≤ n) : ∑ k in range (n + 1), k * p (fin n) k = n! :=
by simpa using main' (fin n) (zero_lt_one.trans_le $ by simpa)

end imo_1987_q1
