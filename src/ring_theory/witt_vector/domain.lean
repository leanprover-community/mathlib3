import ring_theory.witt_vector.identities
import tactic.induction

lemma nat.iterate_succ {α} (n : ℕ) (op : α → α) (a : α) :
  nat.iterate op n.succ a = nat.iterate op n (op a) :=
rfl

lemma nat.iterate_succ' {α} (n : ℕ) (op : α → α) (a : α) :
  nat.iterate op n.succ a = op (nat.iterate op n a) :=
begin
  induction n with k ih generalizing a,
  { refl },
  { apply ih }
end

lemma nat.iterate_add {α} (op : α → α) (a : α) (i j : ℕ) :
  nat.iterate op i (nat.iterate op j a) = nat.iterate op (i+j) a :=
begin
  induction j with j ih generalizing a,
  { refl },
  { rw [nat.iterate_succ, ih], refl }
end

lemma nat.iterate_comm_aux {α} (op1 op2 : α → α) (h_comm : ∀ v, op1 (op2 v) = op2 (op1 v)) (a : α) (j : ℕ) :
  op1 (nat.iterate op2 j a) = nat.iterate op2 j (op1 a) :=
begin
  induction j with j jh,
  { refl },
  { rw [nat.iterate_succ', h_comm, jh, nat.iterate_succ'], }
end

lemma nat.iterate_comm {α} (op1 op2 : α → α) (h_comm : ∀ v, op1 (op2 v) = op2 (op1 v)) (a : α) (i j : ℕ) :
  nat.iterate op1 i (nat.iterate op2 j a) = nat.iterate op2 j (nat.iterate op1 i a) :=
begin
  induction i with i ih generalizing a,
  { refl },
  { rw [nat.iterate_succ', ih, nat.iterate_comm_aux op1 op2 h_comm, nat.iterate_succ'], }
end

namespace witt_vector

variables {p : ℕ} {R : Type*}

local notation `𝕎` := witt_vector p -- type as `\bbW`

def shift (x : 𝕎 R) (n : ℕ) : 𝕎 R := mk p (λ i, x.coeff (n + i))


variables [hp : fact p.prime] [comm_ring R]
include hp


noncomputable theory

open_locale classical



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

lemma coeff_mul_zero (x y : 𝕎 R) : (x * y).coeff 0 = x.coeff 0 * y.coeff 0 :=
begin
  simp [mul_coeff, peval],
end


lemma iterate_verschiebung_mul_aux1 (x y : 𝕎 R) (i : ℕ) :
  nat.iterate verschiebung i x * y = nat.iterate verschiebung i (x * nat.iterate frobenius i y) :=
begin
  induction i with i ih generalizing y,
  { simp },
  { rw [nat.iterate_succ', ← verschiebung_mul_frobenius, ih, nat.iterate_succ'], refl }
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



lemma iterate_verschiebung_mul_frobenius (x : 𝕎 R) (i j : ℕ) :
  nat.iterate frobenius i (nat.iterate verschiebung j x) =
    nat.iterate verschiebung j (nat.iterate frobenius i x) :=
nat.iterate_comm _ _ (λ _, (verschiebung_frobenius_comm _).symm) _ _ _



lemma iterate_verschiebung_mul_aux (x y : 𝕎 R) (i j : ℕ) :
  nat.iterate verschiebung i x * nat.iterate verschiebung j y =
    nat.iterate verschiebung (i + j) (nat.iterate frobenius j x * nat.iterate frobenius i y) :=
begin
  calc
  _ = nat.iterate verschiebung i (x * nat.iterate frobenius i (nat.iterate verschiebung j y)) : _
... = nat.iterate verschiebung i (x * nat.iterate verschiebung j (nat.iterate frobenius i y)) : _
... = nat.iterate verschiebung i (nat.iterate verschiebung j (nat.iterate frobenius i y) * x) : _
... = nat.iterate verschiebung i (nat.iterate verschiebung j (nat.iterate frobenius i y * nat.iterate frobenius j x)) : _
... = nat.iterate verschiebung (i + j) (nat.iterate frobenius i y * nat.iterate frobenius j x) : _
... = _ : _,
  { apply iterate_verschiebung_mul_aux1 },
  { rw iterate_verschiebung_mul_frobenius },
  { rw mul_comm },
  { rw iterate_verschiebung_mul_aux1 },
  { apply nat.iterate_add },
  { rw mul_comm }
end


lemma iter_frobenius_coeff (x : 𝕎 R) (i k : ℕ) :
  (nat.iterate frobenius i x).coeff k = (x.coeff k)^(p^i) :=
begin
  induction i with i ih,
  { simp },
  { rw [nat.iterate_succ', coeff_frobenius_char_p, ih], ring_exp }
end

-- a specialization of hw 6.1.5
-- "follows from 6.1.2, 6.1.4, and repeated application of product formula"
lemma iterate_verschiebung_mul (x y : 𝕎 R) (i j : ℕ) :
  (nat.iterate verschiebung i x * nat.iterate verschiebung j y).coeff (i + j) =
    (x.coeff 0)^(p ^ j) * (y.coeff 0)^(p ^ i) :=
begin
  calc
  _ = (nat.iterate verschiebung (i + j) (nat.iterate frobenius j x * nat.iterate frobenius i y)).coeff (i + j) : _
... = (nat.iterate frobenius j x * nat.iterate frobenius i y).coeff 0 : _
... = (nat.iterate frobenius j x).coeff 0 * (nat.iterate frobenius i y).coeff 0 : _
... = _ : _,
  { rw iterate_verschiebung_mul_aux },
  { convert iterate_verschiebung_coeff _ _ _ using 2,
    rw zero_add },
  { apply coeff_mul_zero },
  { simp only [iter_frobenius_coeff] }
end

variable  [is_domain R]

lemma nonzeros (x y : 𝕎 R) : x * y = 0 → x = 0 ∨ y = 0 :=
begin
  contrapose!,
  rintros ⟨ha, hb⟩,
  rcases verschiebung_nonzero ha with ⟨na, wa, hwa0, hwaeq⟩,
  rcases verschiebung_nonzero hb with ⟨nb, wb, hwb0, hwbeq⟩,
  have : (x * y).coeff (na + nb) = (wa.coeff 0) ^ (p ^ nb) * (wb.coeff 0) ^ (p ^ na),
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

end witt_vector
