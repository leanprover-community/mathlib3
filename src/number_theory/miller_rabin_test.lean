import number_theory.miller_rabin

def binpow {M} [has_one M] [has_mul M] (m : M) : ℕ → M :=
nat.binary_rec 1 (λ b _ ih, let ih2 := ih * ih in cond b (m * ih2) ih2)

def fast_strong_probable_prime (n : nat) (a : zmod n) : Prop :=
binpow a (odd_part (n-1)) = 1
∨ (∃ r : ℕ, r < padic_val_nat 2 (n-1) ∧ binpow a (2^r * odd_part(n-1)) = -1)

instance {n : ℕ} {a : zmod n} : decidable (fast_strong_probable_prime n a) := or.decidable

lemma strong_probable_prime_iff_fast_strong_probable_prime (n : nat) (a : zmod n) :
  strong_probable_prime n a ↔ fast_strong_probable_prime n a :=
begin
  unfold strong_probable_prime,
  unfold fast_strong_probable_prime,
  sorry,
end

--TODO(Bolton): Find a way of making modular exponentiation faster
--set_option profiler true
--#eval to_bool (fast_strong_probable_prime 100003 2)
--#eval to_bool (fast_strong_probable_prime 1000003 2)
--#eval to_bool (nat.prime 1000003)
--#eval to_bool (fast_strong_probable_prime 99999997 4)
--#eval (multiplicity 2 99999997)
--#eval to_bool (nat.prime 104)
