import number_theory.prime_counting

namespace nat

def primes_le (n : ℕ) : list ℕ := (list.range (n + 1)).filter nat.prime

lemma mem_primes_le {n p : ℕ} : p ∈ primes_le n ↔ p ≤ n ∧ nat.prime p :=
by simp only [primes_le, nat.lt_add_one_iff, list.mem_filter, list.mem_range]

lemma primes_le_card {n : ℕ} : (primes_le n).length = prime_counting n :=
by { rw [prime_counting, prime_counting', count_eq_card_filter_range, primes_le], refl }

lemma primes_le_sorted {n : ℕ} : (primes_le n).sorted (<) :=
list.pairwise.sublist (list.filter_sublist _) (list.pairwise_lt_range (n + 1))

lemma primes_le_reverse_sorted {n : ℕ} : (primes_le n).reverse.sorted (>) :=
list.pairwise_reverse.2 primes_le_sorted

lemma primes_le_nodup {n : ℕ} : (primes_le n).nodup := primes_le_sorted.nodup

lemma primes_le_10 : primes_le 10 = [2,3,5,7] :=
begin
  simp only [primes_le, list.range_succ, list.filter_append, list.filter_singleton, list.range_zero,
    list.filter_nil],
  norm_num
end

-- lemma primes_le_100 : primes_le 100 =
--   [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97] :=
-- begin
--   simp only [primes_le, list.range_succ, list.filter_append, list.filter_singleton, list.range_zero,
--     list.filter_nil],
--   norm_num,
-- end

-- lemma primes_le_447 : primes_le 447 =
--   [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
--    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
--    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
--    311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
--    431, 433, 439, 443] :=
-- begin
--   rw [primes_le],
--   simp only [list.range_succ],
--   simp only [list.filter_append],
--   simp only [list.filter_singleton],
--   simp only [list.range_zero],
--   simp only [list.filter_nil],
--   -- simp only [primes_le, list.range_succ, list.filter_append, list.filter_singleton, list.range_zero,
--   --   list.filter_nil],
--   norm_num,
-- end.

end nat
