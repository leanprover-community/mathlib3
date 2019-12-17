import algebra.big_operators
import data.matrix.basic
import linear_algebra.determinant
import tactic.fin_cases
import tactic.linarith
import tactic.omega
import tactic.ring

/-!
  In this file, we define an inverse for square matrices of full rank.
  This inverse is defined, but doesn't have nice properties,
  if the matrix is not square or not of full rank.
  In that case, a pseudoinverse might be a better choice.
  Unfortunately, defining and proving properties of pseudoinverses takes
  a bit more work, so it isn't implemented yet.

  To make computations easier, we use `fin n.succ` to index the matrices in definitions.
  Conversion from and to an arbitrary `fintype m` can be done by the user if needed.
  (Or just define and use the pseudoinverse!)
-/

namespace matrix
universes u v
variables {n : ℕ} {α : Type v} [field α]
open_locale matrix

def row_col_minor (A : matrix (fin n.succ) (fin n.succ) α) (i j : fin n.succ) : matrix (fin n) (fin n) α :=
A.minor (λ i', if ↑i' < i then i' else i'.succ) (λ j', if ↑j' < j then j' else j'.succ)

def cofactor_matrix (A : matrix (fin n.succ) (fin n.succ) α) : matrix (fin n.succ) (fin n.succ) α :=
λ i j, (A.row_col_minor i j).det

def adjugate (A : matrix (fin n.succ) (fin n.succ) α) : matrix (fin n.succ) (fin n.succ) α :=
(A.cofactor_matrix)ᵀ

def fin.pred_except {n : ℕ} (i j : fin n.succ) (h : j ≠ i) : fin n :=
if lt : i.1 < j.1
then j.pred (λ e, (ne_of_lt (lt_of_le_of_lt (nat.zero_le _) lt)) (by finish))
else ⟨j.1, have this : i.1 < nat.succ n := i.2, sorry⟩

def insert {n : ℕ} (i j : fin n.succ) (σ : equiv.perm (fin n)) : equiv.perm (fin n.succ) :=
⟨ λ k, if h : k = i then j else fin.succ_above j (σ (fin.pred_except i k h))
, λ k, if h : k = j then i else fin.succ_above i (σ (fin.pred_except j k h))
, sorry
, sorry⟩

@[simp]
lemma insert_val_self {n : ℕ} (i j : fin n.succ) (σ : equiv.perm (fin n)) : (insert i j σ) i = j := sorry

lemma insert_inj {n : ℕ} (i j : fin n.succ) (σ τ : equiv.perm (fin n)) : insert i j σ = insert i j τ → σ = τ := sorry

lemma insert_surj {n : ℕ} (i : fin n.succ) (σ : equiv.perm (fin n.succ)) : ∃ τ, σ = insert i (σ i) τ := sorry

lemma mul_adjugate (A : matrix (fin n.succ) (fin n.succ) α) : A ⬝adjugate A = A.det • 1 := begin
  ext,
  have perm_image : finset.univ = finset.univ.image(λ (σ : equiv.perm (fin n.succ)), σ j),
  { ext,
    split; intro h,
    { rw finset.mem_image,
      use equiv.swap j a,
      use finset.mem_univ _,
      calc (equiv.swap j a) j
            = if j = j then a else if j = a then j else j : rfl
        ... = a : by simp },
    { apply finset.mem_univ } },
  rw [mul_val, smul_val, adjugate, cofactor_matrix],
  by_cases i = j,
  { rw [h, one_val_eq, mul_one, det, perm_image, finset.sum_image'],
    intros σ _,
    rw [transpose_val, det, finset.mul_sum],
    apply finset.sum_bij (λ τ _, insert j (σ j) τ),
    { intros τ _, simp },
    { intros τ _, simp, rw [←perm_image], simp [insert], sorry },
    { intros τ τ' _ _ h, apply insert_inj, exact h },
    { intros τ hτ,
      rw [finset.mem_filter] at hτ,
      cases insert_surj j τ with τ' hτ',
      use τ',
      use finset.mem_univ _,
      rw [hτ', hτ.2] } },

  { rw [one_val_ne h, mul_zero], sorry }
end

def cramer (A : matrix (fin n.succ) (fin n.succ) α) : matrix (fin n.succ) (fin n.succ) α :=
A.det⁻¹ • A.adjugate

theorem mul_cramer (A : matrix (fin n.succ) (fin n.succ) α) (nonsing : A.det ≠ 0) : A ⬝ cramer A = 1 :=
begin
  rw [cramer, mul_smul, mul_adjugate, smul_smul, inv_mul_cancel nonsing],
  ext i j,
  simp
end

end matrix
