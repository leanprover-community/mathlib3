import ring_theory.witt_vector.identities
import tactic.induction

lemma nat.iterate_succ' {α} (n : ℕ) (op : α → α) (a : α) :
  nat.iterate op n.succ a = op (nat.iterate op n a) :=
begin
  induction n with k ih generalizing a,
  { refl },
  { apply ih }
end


namespace witt_vector
open mv_polynomial


variables {p : ℕ} {R S : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]
include hp
local notation `𝕎` := witt_vector p -- type as `\bbW`

noncomputable theory

open_locale classical


def shift (x : 𝕎 R) (n : ℕ) : 𝕎 R := mk p (λ i, x.coeff (n + i))

lemma shift_coeff (x : 𝕎 R) (n k : ℕ) : (x.shift n).coeff k = x.coeff (n + k) :=
rfl

lemma iterate_verschiebung_coeff (x : 𝕎 R) (n k : ℕ) :
  (nat.iterate verschiebung n x).coeff (k + n) = x.coeff k :=
begin
  induction n with k ih,
  { simp },
  { rw [nat.iterate_succ', nat.add_succ, verschiebung_coeff_succ],
    exact ih }
end

lemma verschiebung_shift (x : 𝕎 R) (k : ℕ) (h : ∀ i < k+1, x.coeff i = 0) :
  verschiebung (x.shift k.succ) = x.shift k :=
begin
  ext ⟨j⟩,
  { rw [verschiebung_coeff_zero, shift_coeff, h],
    apply nat.lt_succ_self },
  { simp only [verschiebung_coeff_succ, shift],
    congr' 1,
    rw [nat.add_succ, add_comm, nat.add_succ, add_comm] }
end

lemma eq_iterate_verschiebung {x : 𝕎 R} {n : ℕ} (h : ∀ i < n, x.coeff i = 0) :
  x = nat.iterate verschiebung n (x.shift n) :=
begin
  induction n with k ih,
  { cases x; simp [shift] },
  { dsimp, rw verschiebung_shift,
    { exact ih (λ i hi, h _ (hi.trans (nat.lt_succ_self _))), },
    { exact h } }
end


lemma verschiebung_nonzero {x : 𝕎 R} (hx : x ≠ 0) :
  ∃ n : ℕ, ∃ x' : 𝕎 R, x'.coeff 0 ≠ 0 ∧ x = nat.iterate verschiebung n x' :=
begin
  have hex : ∃ k : ℕ, x.coeff k ≠ 0,
  { by_contradiction hall,
    push_neg at hall,
    apply hx,
    ext i,
    simp only [hall, zero_coeff] },
  let n := nat.find hex,
  use [n, x.shift n],
  refine ⟨nat.find_spec hex, eq_iterate_verschiebung (λ i hi, not_not.mp _)⟩,
  exact nat.find_min hex hi,
end

variable [char_p R p]

lemma nontrivial : nontrivial (𝕎 R) :=
{ exists_pair_ne := ⟨0, 1,
  begin
    haveI : nontrivial R := char_p.nontrivial_of_char_ne_one hp.1.ne_one,
    intro h,
    have : (0 : 𝕎 R).coeff 0 = (1 : 𝕎 R).coeff 0 := by rw h,
    simpa using this,
  end⟩ }

variable  [is_domain R]


-- 6.1.1
#check coeff_frobenius_char_p

-- 6.1.2
#check mul_char_p_coeff_zero
#check mul_char_p_coeff_succ

-- 6.1.3
#check coeff_p_pow
#check coeff_p_pow_eq_zero

-- 6.1.4
#check frobenius_verschiebung
#check verschiebung_frobenius
#check verschiebung_frobenius_comm

-- a specialization of hw 6.1.5
-- "follows from 6.1.2, 6.1.4, and repeated application of product formula"
lemma iterate_verschiebung_mul (x y : 𝕎 R) (i j : ℕ) :
  (nat.iterate verschiebung i x * nat.iterate verschiebung j y).coeff (i + j) =
    (x.coeff 0)^(p ^ i) * (y.coeff 0)^(p ^ j) :=
begin
  sorry
end

lemma nonzeros (x y : 𝕎 R) : x * y = 0 → x = 0 ∨ y = 0 :=
begin
  contrapose!,
  rintros ⟨ha, hb⟩,
  rcases verschiebung_nonzero ha with ⟨na, wa, hwa0, hwaeq⟩,
  rcases verschiebung_nonzero hb with ⟨nb, wb, hwb0, hwbeq⟩,
  have : (x * y).coeff (na + nb) = (wa.coeff 0) ^ (p ^ na) * (wb.coeff 0) ^ (p ^ nb),
  { rw [← iterate_verschiebung_mul, hwaeq, hwbeq], },
  have : (x * y).coeff (na + nb) ≠ 0,
  { rw this,
    apply mul_ne_zero; apply pow_ne_zero; assumption },
  contrapose! this,
  simp [this]
end


instance : is_domain (𝕎 R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := nonzeros,
  exists_pair_ne := witt_vector.nontrivial.exists_pair_ne }



-- 6.1.1
#check coeff_frobenius_char_p

-- 6.1.2
#check mul_char_p_coeff_zero
#check mul_char_p_coeff_succ

-- 6.1.3
#check coeff_p_pow
#check coeff_p_pow_eq_zero

-- 6.1.4
#check frobenius_verschiebung
#check verschiebung_frobenius
#check verschiebung_frobenius_comm


end witt_vector
