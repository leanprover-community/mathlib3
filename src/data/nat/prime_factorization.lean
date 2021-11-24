import data.nat.prime
import data.nat.mul_ind

open nat
open finset

open_locale big_operators  -- to enable ∏ notation
open_locale nat  -- to enable φ notation

namespace list
open list
variables {α : Type*} [decidable_eq α]


/-! # Census of a list -/

def census (l : list α) := (l.to_finset).image (λ a, (a, l.count a))

@[simp]
lemma census_nil : census (list.nil : list α) = ∅ :=
by { unfold census, simp }

lemma mem_census {an : α × ℕ} (l : list α) :
  an ∈ census l ↔ an.1 ∈ l ∧ an.2 = list.count an.1 l :=
begin
  unfold census, simp,
  split,
  { rintros ⟨q, hq1, hq2⟩, simp only [←hq2, and_true, eq_self_iff_true, hq1] },
  { rintros ⟨h1, h2⟩,
    use an.1,
    split,
    { simp only [list.mem_to_finset, h1] },
    { ext; simp only [h2] } }
end


@[simp]
lemma census_repeat (a : α) {k : ℕ} (hk : 0 < k) : census (list.repeat a k) = {(a, k)} :=
begin
  ext x,
  rw mem_census,
  rw finset.mem_singleton,
  rw list.mem_repeat,
  split,
  { rintros ⟨⟨-, h2⟩, h3⟩, rw [h2, list.count_repeat] at h3, rw [←h2, ←h3], simp },
  { intros h, rw h, simp, exact hk.ne' }
end

end list



/-! # Prime factorizations
TODO: Factor out more of the following lemmas into lemmas about `census`
TODO: Eliminate terminology `prime_factorization` and just use `n.factors.census`?
TODO: Delete some of the following if they're trivial
-/

namespace nat
open list

/-- `prime_factorization n` is the set of prime factors of `n:ℕ` paired with their multiplicities.
For example, 1200 = 2^4 * 3^1 * 5^2 so `(prime_factorization 1200)` is `{(2, 4), (3, 1), (5, 2)}`-/
def prime_factorization (n:ℕ) := n.factors.census

lemma prime_factorization_zero : prime_factorization 0 = ∅ :=
by { unfold prime_factorization, rw factors_zero, simp }

lemma prime_factorization_one : prime_factorization 1 = ∅ :=
by { unfold prime_factorization, rw factors_one, simp }

lemma prime_factorization_prime_pos_pow {p k : ℕ} (hp : prime p) (hk : 0 < k) :
  prime_factorization (p^k) = {(p,k)} :=
by { unfold prime_factorization, rw prime.factors_pow hp k, exact census_repeat p hk }

/-- Unfolding the definition of `pk ∈ n.prime_factorization` -/
lemma mem_prime_factorization {n : ℕ} {pk : ℕ × ℕ}:
  pk ∈ n.prime_factorization ↔ pk.1 ∈ n.factors ∧ pk.2 = n.factors.count pk.1 :=
by { unfold prime_factorization, rw mem_census }


/-- For `⟨p,k⟩ ∈ n.prime_factorization`, `p` is a prime factor of `n` -/
lemma factor_of_mem_factorization {n:ℕ} {pk : ℕ × ℕ} (hpk : pk ∈ prime_factorization n) :
  pk.1 ∈ n.factors := (mem_prime_factorization.mp hpk).1

/-- For `⟨p,k⟩ ∈ n.prime_factorization`, `p` is prime -/
lemma prime_of_mem_factorization {n:ℕ} {pk : ℕ × ℕ} (hpk : pk ∈ prime_factorization n) :
  prime pk.1 := prime_of_mem_factors (factor_of_mem_factorization hpk)

/-- For `⟨p,k⟩ ∈ n.prime_factorization`, `p ∣ n` -/
lemma dvd_of_mem_factorization {n:ℕ} {pk : ℕ × ℕ} (hpk : pk ∈ prime_factorization n) :
  pk.1 ∣ n := dvd_of_mem_factors (factor_of_mem_factorization hpk)

/-- For `⟨p,k⟩ ∈ n.prime_factorization`, `k` is the multiplicity of `p` in `n` -/
lemma prime_factorization_snd_count {n:ℕ} {pk : ℕ × ℕ} (hpk : pk ∈ prime_factorization n) :
  pk.2 = n.factors.count pk.1 := (mem_prime_factorization.mp hpk).2

/-- For `⟨p,k⟩ ∈ n.prime_factorization`, `k` is positive -/
lemma pos_of_prime_factorization_count {n:ℕ} {pk : ℕ × ℕ} (hpk : pk ∈ prime_factorization n) :
  0 < pk.2 :=
begin
  rw [prime_factorization_snd_count hpk, list.count_pos], exact factor_of_mem_factorization hpk,
end

/-- The image of `n.prime_factorization` under `prod.fst` is `n.factors.to_finset` -/
lemma prime_factorization_projection {n : ℕ} :
  image prod.fst n.prime_factorization = n.factors.to_finset :=
begin
  ext q, rw [mem_image, list.mem_to_finset],
  split,
  { rintros ⟨pk, hpk1, hpk2⟩, rw ←hpk2, exact factor_of_mem_factorization hpk1 },
  { intros h,
    use ⟨q, n.factors.count q⟩,
    simp only [and_true, eq_self_iff_true, mem_prime_factorization, h] },
end

/-- Each prime factor of `n` occurs exactly once in `n.prime_factorization` -/
lemma factor_occurs_once_in_factorization {n p : ℕ} (hp : p ∈ n.factors.to_finset) (a : ℕ × ℕ) :
a ∈ n.prime_factorization ∧ a.fst = p ↔ a = (p, list.count p n.factors) :=
begin
  simp_rw mem_prime_factorization,
  split,
  { rintros ⟨⟨_, h1⟩, h2⟩, ext, use h2, simp only [h1, h2] },
  { intros h, simp only [h, and_true, eq_self_iff_true, list.mem_to_finset.mp hp] }
end

/-- The prime factorizations of coprime `a` and `b` are disjoint -/
lemma prime_factorization_disjoint_of_coprime {a b : ℕ} (hab : coprime a b) :
  disjoint a.prime_factorization b.prime_factorization :=
begin
  rw finset.disjoint_iff_ne,
  intros pka ha pkb hb H,
  replace ha := factor_of_mem_factorization ha,
  rw H at ha,
  exact coprime_factors_disjoint hab ha (factor_of_mem_factorization hb),
end

/-- For coprime `a` and `b` the prime factorization `a * b` is the union of those of `a` and `b` -/
lemma prime_factorization_union_of_coprime {a b : ℕ} (hab : coprime a b) :
  (a*b).prime_factorization = a.prime_factorization ∪ b.prime_factorization :=
begin
  rcases a.eq_zero_or_pos with rfl | ha,
  { rw [(nat.coprime_zero_left b).mp hab, zero_mul, prime_factorization_one], simp },
  rcases b.eq_zero_or_pos with rfl | hb,
  { rw [(nat.coprime_zero_right a).mp hab, mul_zero, prime_factorization_one], simp },
  ext ⟨p,k⟩,
  simp only [finset.mem_union, mem_prime_factorization, mem_factors_mul_of_pos ha hb p, or_and_distrib_right],
  split,
  repeat {
    intros h, rcases h,
    { left,  use h.1, simp only [h.2, factors_count_eq_of_coprime_left  hab h.1] },
    { right, use h.1, simp only [h.2, factors_count_eq_of_coprime_right hab h.1] } }
end

/-- If `f : ℕ → ℕ` is multiplicative and `f 1 = 1` then for all `n > 0`,
`f n` is the product of `f (p_i ^ k_i)` over `(p_i, k_i) ∈ prime_factorization n` -/
theorem multiplicative_factorization {n : ℕ} {β : Type*} [comm_monoid β] {f : ℕ → β}
  (hn : 0 < n)
  (h_mult : ∀ x y : ℕ, coprime x y → f(x * y) = f x * f y)
  (hf : f 1 = 1) :
f n = ∏ pk in prime_factorization n, f(pk.1 ^ pk.2) :=
begin
  apply @nat.rec_on_pos_prime_coprime
    (λ n, (0 < n) → f n = ∏ pk in prime_factorization n, f(pk.1 ^ pk.2)),
  { intros p k hp hk hpk, -- Case for positive prime power p^k
    rw [prime_factorization_prime_pos_pow hp hk, finset.prod_singleton] },
  { simp }, -- Case for 0, trivially
  { rintros -, rw [prime_factorization_one, hf], simp }, -- Case for 1
  { intros a b hab ha hb hab_pos,
    rw [h_mult a b hab,
        ha (pos_of_mul_pos_right hab_pos (b.zero_le)),
        hb (pos_of_mul_pos_left hab_pos (a.zero_le)),
        prime_factorization_union_of_coprime hab,
        eq_comm],
    exact prod_union (prime_factorization_disjoint_of_coprime hab) }, -- Case for coprime a and b
  exact hn,
end

/-- For `n > 0`, the product of `p_i ^ k_i` over the prime factorization of `n` equals `n` -/
lemma prime_factorization_prod_eq {n:ℕ} (hn : 0 < n) :
  n = ∏ pk in prime_factorization n, pk.1 ^ pk.2 :=
by { refine (multiplicative_factorization hn _ _), simp }

lemma prime_factorization_injective_on_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
  a.prime_factorization = b.prime_factorization → a = b :=
by {intros H, rw [prime_factorization_prod_eq ha, prime_factorization_prod_eq hb, H]}

/-- Every positive natural number has a unique prime factorization -/
lemma prime_factorization_unique_of_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a ≠ b) :
  a.prime_factorization ≠ b.prime_factorization :=
mt (prime_factorization_injective_on_pos ha hb) h

/--If a product over `n.prime_factorization` doesn't use the multiplicities of the prime factors
then it's equal to the corresponding product over `n.factors.to_finset` -/
lemma prod_pf_to_prod_pd {n : ℕ} {β : Type*} [comm_monoid β] (f : ℕ → β) :
∏ (pk : ℕ × ℕ) in n.prime_factorization, (f pk.1) = ∏ p in n.factors.to_finset, (f p) :=
begin
  rw [prod_comp f (@prod.fst ℕ ℕ), prime_factorization_projection, prod_congr rfl],
  intros p hp,
  suffices : (filter (λ (a : ℕ × ℕ), a.fst = p) n.prime_factorization).card = 1,
    { simp only [this, pow_one] },
  rw card_eq_one,
  use ⟨p, n.factors.count p⟩,
  ext,
  simp only [finset.mem_singleton, finset.mem_filter, factor_occurs_once_in_factorization hp a],
end


end nat
