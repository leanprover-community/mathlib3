import order.partition.finpartition
import topology.instances.complex
import combinatorics.additive.salem_spencer
import data.real.pi.bounds

noncomputable theory

-- lemma exists_half_partition_small {α : Type*} [decidable_eq α] (t : ℝ) (s : finset α) (ht : 0 ≤ t)
--   (hs : t / 2 < s.card) (hs' : ↑s.card ≤ 3 * t / 2) :
--   ∃ P : finpartition s, ∀ p : finset α, p ∈ P.parts → t / 2 < p.card ∧ ↑p.card ≤ t :=
-- begin
--   have : ∀ n : ℕ, ↑n ≤ t ↔ n ≤ ⌊t⌋₊,
--   { intro n,
--     rw nat.le_floor_iff ht },

-- end

-- lemma exists_half_partition {α : Type*} [decidable_eq α] (t : ℝ) (s : finset α)
--   (hs : t / 2 < s.card) :
--   ∃ P : finpartition s, ∀ p : finset α, p ∈ P.parts → t / 2 < p.card ∧ ↑p.card ≤ t :=
-- begin

-- end

-- N / d ≤ ε t / 2 π

-- t = √ N
-- √ N ≤ ε d / 2 π

def finset.expect {α : Type*} (s : finset α) (f : α → ℂ) : ℂ := (s.sum f) / s.card

localized "notation `𝔼` binders `, ` r:(scoped:67 f, finset.expect finset.univ f) := r" in big_operators

localized "notation `𝔼` binders ` in ` s `, ` r:(scoped:67 f, finset.expect s f) := r" in big_operators

open_locale big_operators real complex_conjugate

lemma expect_sum {α β : Type*} {s : finset α} {t : finset β} (f : α → β → ℂ) :
  𝔼 x in s, ∑ y in t, f x y = ∑ y in t, 𝔼 x in s, f x y :=
begin
  rw [finset.expect, finset.sum_comm, finset.sum_div],
  refl
end

lemma expect_comm {α β : Type*} {s : finset α} {t : finset β} (f : α → β → ℂ) :
  𝔼 x in s, 𝔼 y in t, f x y = 𝔼 y in t, 𝔼 x in s, f x y :=
by rw [finset.expect, finset.expect, ←expect_sum, ←expect_sum, finset.expect, finset.expect,
  div_div, mul_comm, div_div, finset.sum_comm]

lemma expect_mul {α : Type*} {s : finset α} (f : α → ℂ) (x : ℂ) :
  (𝔼 i in s, f i) * x = 𝔼 i in s, f i * x :=
by { rw [finset.expect, div_mul_eq_mul_div, finset.sum_mul], refl }

lemma mul_expect {α : Type*} {s : finset α} (f : α → ℂ) (x : ℂ) :
  x * (𝔼 i in s, f i) = 𝔼 i in s, x * f i :=
by simp_rw [mul_comm x, expect_mul]

variables {N : ℕ} {A : finset (zmod N)} {x : zmod N} {f g : zmod N → ℂ}

def e (r : ℝ) : ℂ := complex.exp (r * (2 * π * complex.I))

lemma e_add {r s : ℝ} : e (r + s) = e r * e s :=
by rw [e, complex.of_real_add, add_mul, complex.exp_add, e, e]

lemma e_int (z : ℤ) : e z = 1 :=
by rw [e, complex.of_real_int_cast, complex.exp_int_mul_two_pi_mul_I]

lemma e_zero : e 0 = 1 := by simpa using e_int 0

lemma e_add_int {r : ℝ} {z : ℤ} : e (r + z) = e r :=
by rw [e_add, e_int, mul_one]

lemma conj_e {r : ℝ} : conj (e r) = e (-r) := by { rw [e, e, ←complex.exp_conj], simp }

lemma conj_expect [ne_zero N] : conj (𝔼 i, f i) = 𝔼 i, conj (f i) :=
by simp only [finset.expect, map_div₀, map_nat_cast, map_sum]

def inner {α : Type*} [fintype α] (f g : α → ℂ) : ℂ := 𝔼 x, f x * conj (g x)
def inner' {α : Type*} [fintype α] (f g : α → ℂ) : ℂ := ∑ x, f x * conj (g x)

def omega (r x : zmod N) : ℂ := e ((r * x) / N)
def hat [ne_zero N] (f : zmod N → ℂ) (r : zmod N) : ℂ := inner f (omega r)

localized "notation (name := hat) n `̂`:10000 := hat n" in nat

lemma hat_eq_expect [ne_zero N] : f̂ x = 𝔼 i, f i * e (- ((x * i) / N)) :=
begin
  rw [hat, inner],
  simp only [omega, conj_e],
end

lemma hat_eq_sum [ne_zero N] : f̂ x = (∑ i, f i * e (- ((x * i) / N))) / N :=
by rw [hat_eq_expect, finset.expect, finset.card_univ, zmod.card]

lemma orthogonal [ne_zero N] (x y : zmod N) :
  ∑ (i : zmod N), e (-(i * x / N) + - -(i * y / N)) = N * if x = y then 1 else 0 :=
begin
end

lemma parseval [ne_zero N] : inner' (hat f) (hat g) = inner f g :=
begin
  simp_rw [inner, inner', hat_eq_expect, conj_expect, expect_mul, mul_expect, ←expect_sum, map_mul,
    mul_mul_mul_comm, conj_e, ←e_add, ←finset.mul_sum],
  have : ∀ x y : zmod N,
    ∑ (i : zmod N), e (-(i * x / N) + - -(i * y / N)) = N * if x = y then 1 else 0,
  { intros x y,
    split_ifs,
    { cases h,
      simp [e_zero, finset.card_univ] },


  },

end

#exit

def as_function (A : finset (zmod N)) (x : zmod N) : ℂ := if x ∈ A then 1 else 0

lemma one_five {N : ℕ} {A B C : finset (zmod N)} {α β γ : ℝ}
  (hα : α * N = A.card) (hβ : β * N = B.card) (hβ : γ * N = C.card)
  (hN : odd N)
