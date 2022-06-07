import algebra.ring
import data.real.basic
import data.matrix.basic


/-noncomputable theory-/

/-universes u-/
/-variables {I : Type} [fintype I]-/
/-variables {A : matrix I I ℤ}-/


namespace transition_matrices


variables {I : Type} [fintype I] [decidable_eq I] (A : matrix I I ℤ)


/- Three type of transition matrices.
  Written as classes : first condition says that coefficient are 0 or 1 (transition matrices).
  Second condition is increasingly stringent.
  Basic : any state has at least one output (next possible state). Ensures the subshifts are not empty.
  Irreducible : we can travel from any state to any other state. Ensures the subshifts are topologically transitive.
  Primitive : we can travel from any state to any other state at the same time. Ensures the subshifts are topologically mixing. -/

class basic_trans_mat :
  Prop :=
  ( boolean : ∀ (i j : I), (A i j = 0) ∨ (A i j = 1) )
  ( has_outputs : ∀ (i : I), ∃ (j : I), A i j = 1 )


class irred_trans_mat :
  Prop :=
  ( boolean : ∀ (i j : I), (A i j = 0) ∨ (A i j = 1) )
  ( irred : ∀ (i j : I), ∃ n ≥ 1, (A^n) i j ≥ 1 )


class prime_trans_mat :
  Prop :=
  ( boolean : ∀ (i j : I), (A i j = 0) ∨ (A i j = 1) )
  ( prime : ∃ n ≥ 1, ∀ (i j : I), (A^n) i j ≥ 1 )


lemma basic_trans_mat_is_boolean [basic_A : basic_trans_mat A] :
  ∀ (i j : I), (A i j = 0) ∨ (A i j = 1) :=
basic_A.boolean


lemma basic_trans_mat_has_outputs [basic_A : basic_trans_mat A] :
  ∀ (i : I), ∃ (j : I), A i j = 1 :=
basic_A.has_outputs


lemma irred_trans_mat_is_boolean [irred_A : irred_trans_mat A] :
  ∀ (i j : I), (A i j = 0) ∨ (A i j = 1) :=
irred_A.boolean


lemma irred_trans_mat_is_irred [irred_A : irred_trans_mat A] :
  ∀ (i : I), ∀ (j : I), ∃ n ≥ 1, (A^n) i j ≥ 1 :=
irred_A.irred


lemma prime_trans_mat_is_boolean [prime_A : prime_trans_mat A] :
  ∀ (i j : I), (A i j = 0) ∨ (A i j = 1) :=
prime_A.boolean


lemma prime_trans_mat_is_prime [prime_A : prime_trans_mat A] :
  ∃ n ≥ 1, ∀ (i j : I), (A^n) i j ≥ 1 :=
prime_A.prime


/-- A trivial lemma which let us split powers of a matrix A^(n+m).
  Easy, but used quite often, and makes the next proofs cleaner. -/
lemma mat_power_split (n m : ℕ) (i j : I) :
  (A^(n+m)) i j = finset.univ.sum (λ (k : I), (A^n) i k * (A^m) k j) :=
begin
  calc (A^(n+m)) i j
        = ( (A^n) * (A^m) ) i j                              : by rw pow_add
    ... = ( (A^n).mul (A^m) ) i j                            : by rw matrix.mul_eq_mul (A^n) (A^m)
    ... = finset.univ.sum (λ (k : I), (A^n) i k * (A^m) k j) : by rw matrix.mul_apply,
end


lemma basic_power_nonneg [basic_trans_mat A] :
  ∀ (n : ℕ) (i j : I), (A^n) i j ≥ 0 :=
begin
  intro n,
  induction n,
  { intros i j,
    by_cases diag : i = j,
    { simp [diag] },
    { simp [diag] } },
  { intros i k,
    rw [nat.succ_eq_one_add n_n, mat_power_split A 1 n_n i k],
    apply finset.sum_nonneg',
    intro j,
    have := basic_trans_mat_is_boolean A,
    specialize this i j,
    cases this with no_path one_path,
    { simp [no_path] },
    { simp [one_path], exact n_ih j k } }
end


lemma basic_power_split_domination [is_basic_A : basic_trans_mat A] (n m : ℕ) (i j k : I)
  (path_i_to_j : (A^n) i j ≥ 1) (path_j_to_k : (A^m) j k ≥ 1) :
  (A^(n+m)) i k ≥ 1 :=
begin
  rw mat_power_split A n m i k,
  let f : I → ℤ := λ x, ((A^n) i x) * (A^m) x k,
  have f_j_ge_1 : 1 ≤ f j := by
  { simp [f], exact one_le_mul_of_one_le_of_one_le path_i_to_j path_j_to_k },
  apply le_trans f_j_ge_1,
  apply finset.single_le_sum,
  { simp [f],
    intro x,
    exact decidable.mul_nonneg (basic_power_nonneg A n i x) (basic_power_nonneg A m x k) },
  { simp }
end


/- I didn't cheat : primitive is stronger than irreducible... -/

instance prime_to_irred [prime_trans_mat A] :
  irred_trans_mat A :=
{ boolean := prime_trans_mat_is_boolean A,
  irred :=
  begin
    intros i j,
    rcases (prime_trans_mat_is_prime A) with ⟨ n, n_spos, A_n_spos ⟩,
    use [n, n_spos],
    exact A_n_spos i j,
  end }


/- ...and irreducible is stronger than basic.
  Note that we use here the hypothesis n_spos, which tells us that there exists a path of positive length from i to j.
  If relaxed to n ≥ 0, and if I is a singleton, then A = [0] would be irreducible (take n = 0) but not basic! -/

instance irred_to_basic [irred_trans_mat A] :
  basic_trans_mat A :=
{ boolean := irred_trans_mat_is_boolean A,
  has_outputs :=
  begin
    by_contra no_output,
    push_neg at no_output,
    cases no_output with i i_no_output,
    replace i_no_output : ∀ (j : I), A i j = 0 := by {
      intro j,
      specialize i_no_output j,
      have this := (irred_trans_mat_is_boolean A),
      specialize this i j,
      exact or_iff_not_imp_right.1 this i_no_output },
    have this := irred_trans_mat_is_irred A,
    specialize this i i,
    rcases this with ⟨ n, n_spos, A_n_spos ⟩,
    have this : ∃ (m : ℕ), n = m+1 := by { apply nat.exists_eq_succ_of_ne_zero, linarith },
    cases this with m m_succ_n,
    rw nat.add_comm at m_succ_n,
    rw m_succ_n at A_n_spos,
    rw (mat_power_split A 1 m i i) at A_n_spos,
    simp [i_no_output] at A_n_spos,
    linarith,
  end }


/-- Not surprisingly, primitive is stronger than basic. -/
instance prime_to_basic [prime_trans_mat A] :
  basic_trans_mat A :=
{ boolean := prime_trans_mat_is_boolean A,
  has_outputs := basic_trans_mat_has_outputs A }


/- I think the next lemmas may be useful, still have to decide. -/

lemma basic_powers_have_outputs [basic_trans_mat A] :
  ∀ (n : ℕ) (i : I), ∃ (j : I), (A^n) i j ≥ 1 :=
begin
  intro n,
  induction n,
  { intro i,
    use i,
    simp },
  { intro i,
    have this := basic_trans_mat_has_outputs A,
    specialize this i,
    cases this with j path_i_to_j,
    specialize n_ih j,
    cases n_ih with k path_j_to_k,
    use k,
    rw [nat.succ_eq_one_add n_n],
    apply basic_power_split_domination A 1 n_n i j k,
    { simp, rw path_i_to_j },
    { exact path_j_to_k } },
end


lemma irred_mat_have_inputs [irred_trans_mat A] :
  ∀ (j : I), ∃ (i : I), A i j = 1 :=
begin
  by_contra no_input,
  push_neg at no_input,
  cases no_input with j j_no_input,
  replace j_no_input : ∀ (i : I), A i j = 0 := by
  { intro i,
    specialize j_no_input i,
    have this := irred_trans_mat_is_boolean A,
    specialize this i j,
    exact or_iff_not_imp_right.1 this j_no_input },
  have this := irred_trans_mat_is_irred A,
  specialize this j j,
  rcases this with ⟨ n, n_spos, A_n_j_j_spos ⟩,
  have this : ∃ (m : ℕ), n = m+1 := by { apply nat.exists_eq_succ_of_ne_zero, linarith },
  cases this with m m_succ_n,
  rw [m_succ_n, mat_power_split A m 1 j j] at A_n_j_j_spos,
  simp [j_no_input] at A_n_j_j_spos,
  linarith,
end


lemma irred_mat_powers_have_inputs [irred_trans_mat A] :
  ∀ (j : I) (n : ℕ), ∃ (i : I), (A^n) i j ≥ 1 :=
begin
  intros j n,
  induction n,
  { use j,
    simp },
  { cases n_ih with k path_k_to_j,
    have := irred_mat_have_inputs A,
    specialize this k,
    cases this with i path_i_to_k,
    use i,
    rw [nat.succ_eq_one_add n_n],
    apply basic_power_split_domination A 1 n_n i k j,
    { simp [path_i_to_k] },
    { exact path_k_to_j } },
end


lemma prime_powers_are_positive [prime_trans_mat A] :
  ∃ (N : ℕ), ∀ (n ≥ N) (i j : I), (A^n) i j ≥ 1 :=
begin
  rcases (prime_trans_mat_is_prime A) with ⟨ N, N_spos, A_pow_N_spos ⟩,
  use N,
  intros n n_ge_N i j,
  cases (nat.exists_eq_add_of_le n_ge_N) with m n_eq_N_plus_m,
  rw n_eq_N_plus_m,
  clear N_spos n_ge_N n_eq_N_plus_m n,
  cases (irred_mat_powers_have_inputs A j m) with k path_k_to_j,
  specialize A_pow_N_spos i k,
  exact basic_power_split_domination A N m i k j A_pow_N_spos path_k_to_j,
end


end transition_matrices
