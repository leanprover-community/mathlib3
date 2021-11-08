/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import number_theory.quadratic_reciprocity

.

section -- move this

variables {R : Type*} [semiring R] (a b : R)

lemma odd_iff_exists_bit1 : odd a ↔ ∃ r, a = bit1 r :=
by simp only [odd, bit1, bit0, add_mul, one_mul]

lemma bit0_mul' : bit0 a * b = bit0 (a * b) :=
by simp only [bit0, add_mul]

lemma mul_bit0' : a * bit0 b = bit0 (a * b) :=
by simp only [bit0, mul_add]

lemma bit1_mul' : bit1 a * b = bit0 (a * b) + b :=
by simp only [bit0, bit1, add_mul, one_mul]

lemma mul_bit1' : a * bit1 b = bit0 (a * b) + a :=
by simp only [bit0, bit1, mul_add, mul_one]

@[simp] lemma zmod_four_bit0_bit0 : ∀ m : zmod 4, bit0 (bit0 m) = 0 := dec_trivial
@[simp] lemma zmod_four_bit1_bit0 : ∀ m : zmod 4, bit1 (bit0 m) = 1 := dec_trivial
@[simp] lemma zmod_four_bit0_bit1 : ∀ m : zmod 4, bit0 (bit1 m) = 2 := dec_trivial
@[simp] lemma zmod_four_bit1_bit1 : ∀ m : zmod 4, bit1 (bit1 m) = 3 := dec_trivial

@[simp] lemma list.zip_with_self {α β : Sort*} (f : α → α → β) : ∀ (L : list α),
  list.zip_with f L L = L.map (λ a, f a a)
| []     := rfl
| (a::L) := by rw [list.zip_with_cons_cons, list.map_cons, list.zip_with_self]

instance zmod.nontrivial' (n : ℕ) : nontrivial (zmod (n + 2)) :=
have fact (1 < n + 2), from ⟨dec_trivial⟩, by exactI zmod.nontrivial _

end -- move this

namespace nat

/-- The Kronecker index of `n` is
* `4 * n` if `(n : zmod 4) = 2`; in other words: if `n` is divisible by `2` precisely once
* `n` otherwise

This index computes the periodicity of the Legendre and Kronecker symbols in base `n`. -/
def kronecker_index (n : ℕ) : ℕ :=
if (n : zmod 4) = 2 then 4 * n else n

namespace kronecker_index

@[simp] lemma zero : kronecker_index 0 = 0 := rfl
@[simp] lemma one : kronecker_index 1 = 1 := rfl
lemma two : kronecker_index 2 = 8 := rfl

lemma mod_four_eq_two (n : ℕ) (hn : (n : zmod 4) = 2) :
  kronecker_index n = 4 * n := if_pos hn

lemma mod_four_ne_two (n : ℕ) (hn : (n : zmod 4) ≠ 2) :
  kronecker_index n = n := if_neg hn

@[simp] lemma bit0_bit0 (n : ℕ) : kronecker_index (bit0 (bit0 n)) = bit0 (bit0 n) :=
mod_four_ne_two _ $ by simp only [nat.cast_bit0, zmod_four_bit0_bit0]; dec_trivial

@[simp] lemma bit0_bit1 (n : ℕ) : kronecker_index (bit0 (bit1 n)) = bit0 (bit0 (bit0 (bit1 n))) :=
begin
  rw [mod_four_eq_two, bit0_mul', bit0_mul', one_mul],
  simp only [nat.cast_bit0, nat.cast_bit1, zmod_four_bit0_bit1],
end

@[simp] lemma bit1_bit0 (n : ℕ) : kronecker_index (bit1 (bit0 n)) = bit1 (bit0 n) :=
mod_four_ne_two _ $ by simp only [nat.cast_bit0, nat.cast_bit1, zmod_four_bit1_bit0]; dec_trivial

@[simp] lemma bit1_bit1 (n : ℕ) : kronecker_index (bit1 (bit1 n)) = bit1 (bit1 n) :=
mod_four_ne_two _ $ by simp only [nat.cast_bit0, nat.cast_bit1, zmod_four_bit1_bit1]; dec_trivial

lemma prime_ne_two (p : ℕ) (hp2 : p ≠ 2) [hp : fact p.prime] : p.kronecker_index = p :=
begin
  have hp4 : (p : zmod 4) ≠ 2,
  { obtain ⟨r, hr⟩ : ∃ r, p = bit1 r,
    { rw [← odd_iff_exists_bit1, nat.odd_iff, hp.1.eq_two_or_odd.resolve_left hp2] },
    rw [hr, nat.cast_bit1], generalize : (r : zmod 4) = x, dec_trivial! },
  rw [nat.kronecker_index.mod_four_ne_two p hp4],
end

lemma dvd (n : ℕ) : n ∣ n.kronecker_index :=
by { delta kronecker_index, split_ifs, exacts [dvd_mul_left n 4, dvd_rfl] }

end kronecker_index

/-- Auxiliary definition for the Legendre symbol.
if `p ≠ 2` this is the usual Legedre symbol, and for `p = 2` it is defined to be
* `0` if `a ≡ 0 (mod 2)`
* `1` if `a ≡ ±1 (mod 8)`
* `-1` otherwise, i.e. if `a ≡ ±3 (mod 8)`.

Warning: because of dependent types, the arguments `a` and `p` occur in the "opposite" order
compared to the "usual" order. -/
def legendre_sym' (p : ℕ) (a : zmod p.kronecker_index) : zmod 3 :=
if zmod.cast_hom (nat.kronecker_index.dvd p) (zmod p) a = 0 then 0 else
if p = 2
  then (if a = -1 ∨ a = 1  then 1 else -1)
  else (if a ^ (p / 2) = 1 then 1 else -1)

lemma legendre_sym'_zero (p : ℕ) : legendre_sym' p 0 = 0 :=
by rw [legendre_sym', ring_hom.map_zero, if_pos rfl]

lemma legendre_sym'_one (p : ℕ) [fact (1 < p)] : legendre_sym' p 1 = 1 :=
begin
  rw [legendre_sym', ring_hom.map_one, if_neg (one_ne_zero : (1 : zmod p) ≠ 0)],
  simp only [one_pow, eq_self_iff_true, if_true, or_true, if_t_t],
end

lemma legendre_sym'_mul (p : ℕ) [hp : fact p.prime] (a b : zmod p.kronecker_index) :
  legendre_sym' p (a * b) = legendre_sym' p a * legendre_sym' p b :=
begin
  delta legendre_sym',
  rw [ring_hom.map_mul, zmod.cast_hom_apply, zmod.cast_hom_apply],
  by_cases ha0 : ((a : zmod p.kronecker_index) : zmod p) = 0,
  { rw [ha0, zero_mul, if_pos rfl, if_pos rfl, zero_mul] },
  by_cases hb0 : ((b : zmod p.kronecker_index) : zmod p) = 0,
  { rw [hb0, mul_zero, if_pos rfl, if_pos rfl, mul_zero] },
  rw [if_neg ha0, if_neg hb0, if_neg], swap, { exact mul_ne_zero ha0 hb0 },
  by_cases hp2 : p = 2,
  { unfreezingI { subst p },
    simp only [if_pos rfl],
    revert a b, rw [nat.kronecker_index.two],
    dec_trivial, },
  { simp only [if_neg hp2],
    rw [ite_eq_iff, mul_pow],
    have hp4 : (p : zmod 4) ≠ 2,
    { obtain ⟨r, hr⟩ : ∃ r, p = bit1 r,
      { rw [← odd_iff_exists_bit1, nat.odd_iff, hp.1.eq_two_or_odd.resolve_left hp2] },
      rw [hr, nat.cast_bit1], generalize : (r : zmod 4) = x, dec_trivial! },
    revert a b,
    rw [nat.kronecker_index.mod_four_ne_two p hp4],
    simp only [neg_mul_eq_neg_mul_symm, zmod.cast_id', id.def, ite_mul, one_mul],
    intros a b ha0 hb0,
    haveI : fact (2 < p) := ⟨lt_of_le_of_ne hp.1.two_le (ne.symm hp2)⟩,
    obtain (ha|ha) := zmod.pow_div_two_eq_neg_one_or_one p ha0;
    obtain (hb|hb) := zmod.pow_div_two_eq_neg_one_or_one p hb0;
    simp only [ha, hb, zmod.neg_one_ne_one, if_true, if_false, eq_self_iff_true, not_false_iff,
      one_mul, mul_one, mul_neg_eq_neg_mul_symm, neg_neg, true_and, true_or, and_true, or_true] },
end

/-- The Legendre symbol in base `p`, packaged as a morphism between monoids with zero.
This is not the primary definition, because it depends on primality of `p`.
But this primality assumption is annoying in the definition of the Kronecker symbol. -/
@[simps] def legendre_sym_hom (p : ℕ) [fact p.prime] :
  monoid_with_zero_hom (zmod p.kronecker_index) (zmod 3) :=
{ to_fun := legendre_sym' p,
  map_zero' := legendre_sym'_zero p,
  map_one' := legendre_sym'_one p,
  map_mul' := legendre_sym'_mul p }

lemma legendre_sym'_eq_zero_iff (p : ℕ) [fact p.prime] (a : zmod p.kronecker_index) :
  legendre_sym' p a = 0 ↔ (a : zmod p) = 0 :=
begin
  dsimp [legendre_sym'],
  by_cases hp2 : p = 2,
  { unfreezingI { subst p },
    simp only [if_true, eq_self_iff_true, ite_eq_left_iff],
    rw not_imp_eq_of_eq_false_right,
    apply propext, split_ifs; dec_trivial },
  { rw [if_neg hp2, ite_eq_left_iff, not_imp_eq_of_eq_false_right],
    apply propext, rw [iff_false], split_ifs,
    { exact one_ne_zero },
    { rw [neg_eq_zero], exact one_ne_zero } }
end

/-- `legendre_sym a p` is the extended Legendre symbol of `a` and `p`:
if `p ≠ 2` this is the usual Legedre symbol, and for `p = 2` it is defined to be
* `0` if `a ≡ 0 (mod 2)`
* `1` if `a ≡ ±1 (mod 8)`
* `-1` otherwise, i.e. if `a ≡ ±3 (mod 8)`.
-/
def legendre_sym (a p : ℕ) : zmod 3 :=
legendre_sym' p a

lemma legendre_sym_zero_left (p : ℕ) : legendre_sym 0 p = 0 :=
by rw [legendre_sym, nat.cast_zero, legendre_sym'_zero]

@[simp] lemma legendre_sym_zero : legendre_sym 0 = 0 :=
by { ext1 p, rw [legendre_sym_zero_left, pi.zero_apply] }

@[simp] lemma legendre_sym_one_left (p : ℕ) [fact (1 < p)] : legendre_sym 1 p = 1 :=
by rw [legendre_sym, nat.cast_one, legendre_sym'_one]

@[simp] lemma legendre_sym_mul_left (a b p : ℕ) [fact p.prime] :
  (a * b).legendre_sym p = a.legendre_sym p * b.legendre_sym p :=
by { delta legendre_sym, rw [nat.cast_mul, legendre_sym'_mul] }

/- lemma mem_pm_three_of_ne_zero_of_not_mem_pm_one' : -/
/-   ∀ a : zmod 8, (a : zmod 2) ≠ 0 → a ∉ ({1, -1} : finset (zmod 8)) → -/
/-   a ∈ ({3, -3} : finset (zmod 8)) := -/
/- dec_trivial -/

/- lemma mem_pm_three_of_ne_zero_of_not_mem_pm_one -/
/-   (a : ℕ) (ha2 : (a : zmod 2) ≠ 0) (ha8 : (a : zmod 8) ∉ ({1, -1} : finset (zmod 8))) : -/
/-   (a : zmod 8) ∈ ({3, -3} : finset (zmod 8)) := -/
/- begin -/
/-   refine mem_pm_three_of_ne_zero_of_not_mem_pm_one' a (mt (λ h, _) ha2) ha8, -/
/-   let q := zmod.cast_hom (dec_trivial : 2 ∣ 8) (zmod 2), -/
/-   exact (q.map_nat_cast a).symm.trans h -/
/- end -/

/- lemma legendre_sym_two (a : ℕ) : legendre_sym 2 a = -/
/-   if (a : zmod 2) = 0 -/
/-     then 0 -/
/-     else if (a : zmod 8) ∈ ({1, -1} : finset (zmod 8)) then 1 else -1 := -/
/- if_pos rfl -/

/- lemma legendre_sym'_ne_two {a p : ℕ} (hp : p ≠ 2) : -/
/-   a.legendre_sym' p = zmod.legendre_sym a p := -/
/- if_neg hp -/

/- lemma legendre_sym'_bit1 (a p : ℕ) : -/
/-   a.legendre_sym' (bit1 p) = zmod.legendre_sym a (bit1 p) := -/
/- legendre_sym'_ne_two $ nat.bit1_ne_bit0 p 1 -/

lemma legendre_sym_eq_zero_iff (a p : ℕ) [fact p.prime] :
  legendre_sym a p = 0 ↔ (a : zmod p) = 0 :=
begin
  rw [legendre_sym, legendre_sym'_eq_zero_iff],
  show zmod.cast_hom (kronecker_index.dvd p) (zmod p) a = 0 ↔ (a : zmod p) = 0,
  rw ring_hom.map_nat_cast,
end

lemma legendre_sym_eq_zero_iff_dvd (a p : ℕ) [fact p.prime] :
  legendre_sym a p = 0 ↔ p ∣ a :=
by rw [legendre_sym_eq_zero_iff, ← zmod.nat_coe_zmod_eq_zero_iff_dvd]

/-- The Kronecker symbol of two natural numbers `a` and `n` is defined to be
the product `legendre_sym a p₁ * ... * legendre_sym a pₖ`,
where `n = p₁ * ... * pₖ` is the prime factorization of `n`.

For `n = 0`, the symbol is defined to be `1` if `a = 1` and `0` otherwise. -/
def kronecker_sym' (a n : ℕ) : zmod 3 :=
if n = 0
then if a = 1 then 1 else 0
else (n.factors.map a.legendre_sym).prod

lemma kronecker_sym'_def (a n : ℕ) :
  a.kronecker_sym' n = if n = 0
    then if a = 1 then 1 else 0
    else (n.factors.map a.legendre_sym).prod := rfl

lemma kronecker_sym'_def' {a n : ℕ} (hn : n ≠ 0) :
  a.kronecker_sym' n = (n.factors.map a.legendre_sym).prod := if_neg hn

lemma kronecker_sym'_zero_left (n : ℕ) (h1 : n ≠ 1) : kronecker_sym' 0 n = 0 :=
begin
  rw [kronecker_sym'_def, if_neg (zero_ne_one : 0 ≠ 1)],
  split_ifs with hn, { refl },
  replace hn : 0 < n := nat.pos_of_ne_zero hn,
  haveI : fact (prime 3) := ⟨prime_three⟩,
  simp only [legendre_sym_zero, list.prod_eq_zero_iff, list.mem_map, mem_factors hn,
      and_true, pi.zero_apply, eq_self_iff_true],
  exact ⟨n.min_fac, min_fac_prime h1, min_fac_dvd _⟩,
end

@[simp] lemma kronecker_sym'_zero_right (a : ℕ) :
  a.kronecker_sym' 0 = if a = 1 then 1 else 0 := if_pos rfl

@[simp] lemma kronecker_sym'_one_left (n : ℕ) : kronecker_sym' 1 n = 1 :=
begin
  by_cases hn : n = 0, { rw [hn, kronecker_sym'_zero_right, if_pos rfl], },
  change n ≠ 0 at hn,
  suffices : n.factors.map (legendre_sym 1) = list.repeat 1 n.factors.length,
  { rw [kronecker_sym'_def' hn, this, list.prod_repeat, one_pow] },
  simp only [list.eq_repeat, list.length_map, eq_self_iff_true, true_and,
    list.mem_map, mem_factors hn.bot_lt],
  rintro _ ⟨p, ⟨hp, hpn⟩, rfl⟩,
  haveI : fact p.prime := ⟨hp⟩,
  exact legendre_sym_one_left p,
end

@[simp] lemma kronecker_sym'_one_right (a : ℕ) : a.kronecker_sym' 1 = 1 :=
by rw [kronecker_sym'_def' one_ne_zero, factors_one, list.map_nil, list.prod_nil]

lemma kronecker_sym'_mul_left (a b n : ℕ) :
  (a * b).kronecker_sym' n = a.kronecker_sym' n * b.kronecker_sym' n :=
begin
  by_cases hn : n = 0,
  { simp only [hn, kronecker_sym'_zero_right, nat.mul_eq_one_iff, ← ite_and, boole_mul,
      mul_boole, and_comm], congr, },
  have aux : (n.factors.map a.legendre_sym).length = (n.factors.map b.legendre_sym).length,
  { simp only [list.length_map] },
  simp only [kronecker_sym'_def' hn, list.prod_mul_prod_eq_prod_zip_with_of_length_eq _ _ aux,
    list.zip_with_map, list.zip_with_self],
  congr' 1,
  apply list.ext_le, { simp only [list.length_map] },
  intros i hi1 hi2,
  simp only [list.nth_le_map'],
  rw @legendre_sym_mul_left _ _ _ ⟨prime_of_mem_factors (list.nth_le_mem _ _ _)⟩,
end

lemma kronecker_sym'_mul_right (a m n : ℕ) :
  a.kronecker_sym' (m * n) = a.kronecker_sym' m * a.kronecker_sym' n :=
begin
  by_cases hm : m = 0,
  { simp only [hm, kronecker_sym'_zero_right, boole_mul, one_mul, zero_mul],
    split_ifs with ha; simp only [ha, kronecker_sym'_one_left, eq_self_iff_true], },
  by_cases hn : n = 0, { simp only [hn, kronecker_sym'_zero_right, mul_boole, mul_one, mul_zero],
    split_ifs with ha; simp only [ha, kronecker_sym'_one_left, eq_self_iff_true], },
  rw [kronecker_sym'_def' hm, kronecker_sym'_def' hn,
      kronecker_sym'_def' (mul_ne_zero hm hn)],
  simp only [← multiset.coe_prod, ← multiset.coe_map, ← factors_eq, ← multiset.prod_add,
    ← multiset.map_add, unique_factorization_monoid.normalized_factors_mul hm hn],
end

/-- The Kronecker symbol of two natural numbers `a` and `n` is defined to be
the product `legendre_sym a p₁ * ... * legendre_sym a pₖ`,
where `n = p₁ * ... * pₖ` is the prime factorization of `n`.

For `n = 0`, the symbol is defined to be `1` if `a = 1` and `0` otherwise. -/
def kronecker_sym : ℕ →* ℕ →* (zmod 3) :=
{ to_fun := λ a,
  { to_fun := a.kronecker_sym',
    map_one' := kronecker_sym'_one_right a,
    map_mul' := kronecker_sym'_mul_right a },
  map_one' := by { ext1 n, exact kronecker_sym'_one_left n },
  map_mul' := λ a b, by { ext1 n, exact kronecker_sym'_mul_left a b n } }

lemma kronecker_sym_def (a n : ℕ) :
  kronecker_sym a n = if n = 0
    then if a = 1 then 1 else 0
    else (n.factors.map a.legendre_sym).prod := rfl

lemma kronecker_sym_def' {a n : ℕ} (hn : n ≠ 0) :
  kronecker_sym a n = (n.factors.map a.legendre_sym).prod := if_neg hn

lemma kronecker_sym_zero_left (n : ℕ) (h1 : n ≠ 1) : kronecker_sym 0 n = 0 :=
kronecker_sym'_zero_left n h1

@[simp] lemma kronecker_sym_zero_right (a : ℕ) :
  kronecker_sym a 0 = if a = 1 then 1 else 0 :=
kronecker_sym'_zero_right a

lemma legendre_sym_eq_kronecker_sym (a p : ℕ) [hp : fact p.prime] :
  a.legendre_sym p = kronecker_sym a p :=
by rw [kronecker_sym_def' hp.1.ne_zero, factors_prime hp.1, list.map_singleton, list.prod_singleton]

lemma kronecker_sym_eq_zero (a n : ℕ) :
  kronecker_sym a n = 0 ↔ ¬ a.coprime n :=
begin
  by_cases hn : n = 0,
  { simp only [hn, coprime_zero_right, kronecker_sym_zero_right, true_iff, eq_self_iff_true,
      ite_eq_right_iff, one_ne_zero, imp_false], },
  change n ≠ 0 at hn,
  haveI : fact (prime 3) := ⟨prime_three⟩,
  simp only [kronecker_sym_def' hn, list.prod_eq_zero_iff, list.mem_map, mem_factors hn.bot_lt,
    prime.not_coprime_iff_dvd, and_assoc],
  refine exists_congr (λ p, _),
  simp only [← @exists_prop p.prime, and_comm _ (p ∣ n)],
  refine exists_congr (λ hp, and_congr iff.rfl _),
  haveI : fact p.prime := ⟨hp⟩,
  exact legendre_sym_eq_zero_iff_dvd a p
end

-- move this
lemma eq_two_pow_mul_odd (n : ℕ) (hn : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ odd m :=
begin
  have hk : multiplicity.finite 2 n,
  { rw multiplicity.finite_nat_iff, exact ⟨dec_trivial, hn⟩ },
  let k := (multiplicity 2 n).get hk,
  let m := n / (2 ^ k),
  refine ⟨k, m, _, _⟩,
  { rw nat.mul_div_cancel', exact multiplicity.pow_multiplicity_dvd hk },
  { rw [odd_iff_not_even, even_iff_two_dvd],
    rintro ⟨l, hl⟩,
    refine multiplicity.is_greatest' hk (lt_add_one _) _,
    refine ⟨l, _⟩,
    rw [pow_succ', mul_assoc, ← hl, nat.mul_div_cancel'],
    exact multiplicity.pow_multiplicity_dvd hk },
end

lemma kronecker_sym_congr_left (a b n : ℕ)
  (h : (a : zmod n.kronecker_index) = (b : zmod n.kronecker_index)) :
  kronecker_sym a n = kronecker_sym b n :=
begin
  by_cases hn : n = 0,
  { subst n, simp only [int.coe_nat_inj', int.nat_cast_eq_coe_nat] at h, subst h },
  replace hn : 0 < n := nat.pos_of_ne_zero hn,
  obtain ⟨l, m, rfl, hm⟩ := eq_two_pow_mul_odd n hn,
  simp only [monoid_hom.map_mul],
  congr' 1,
  { haveI : fact (prime 2) := ⟨prime_two⟩,
    cases l, { simp only [pow_zero, monoid_hom.map_one] },
    cases l,
    { suffices : (a : zmod (kronecker_index 2)) = b,
      { simp only [pow_one, ← legendre_sym_eq_kronecker_sym, legendre_sym, this] },
      suffices h8k : kronecker_index 2 ∣ kronecker_index (2 ^ 1 * m),
      { convert congr_arg (zmod.cast_hom h8k (zmod (kronecker_index 2))) h using 1;
        rw [ring_hom.map_nat_cast] },
      simp only [kronecker_index, cast_one, cast_bit0, if_true, cast_mul, eq_self_iff_true, pow_one,
        ← mul_assoc],
      rw if_pos,
      { exact ⟨m, rfl⟩ },
      { rw odd_iff_exists_bit1 at hm, rcases hm with ⟨m, rfl⟩,
        simp only [cast_one, cast_bit0, cast_bit1, cast_mul, pow_one, bit0_mul', one_mul,
          zmod_four_bit0_bit1], } },
    revert h,
    simp only [cast_bit0, pow_succ, bit0_mul', one_mul, zmod_four_bit0_bit0] at hk,
    rw if_neg at hk, swap, { dec_trivial },
    cases l,
    { have hab : (a : zmod  4) = b,
      { sorry },
      have aux : ∀ n : ℕ, (n : zmod 2) = (n : zmod 4),
      { exact λ n, ((zmod.cast_hom (dec_trivial : 2 ∣ 4) (zmod 2)).map_nat_cast n).symm },
      simp only [aux, h, pow_two, kronecker_sym_mul_right, ← legendre_sym_eq_kronecker_sym,
        legendre_sym'_two, neg_mul_eq_neg_mul_symm, if_t_t, mul_one, zero_mul, finset.mem_insert,
        mul_neg_eq_neg_mul_symm, ite_mul, mul_ite, finset.mem_singleton, mul_zero, neg_zero],

       },
    sorry },
  { have h0m : 0 < m := odd_gt_zero hm,
    simp only [kronecker_sym_def' h0m.ne'],
    congr' 1,
    apply list.ext_le, { simp only [list.length_map] },
    intros i hi1 hi2,
    simp only [list.nth_le_map'],
    let l : ℕ := _,
    refine @legendre_sym'_congr_left a b _ l ⟨prime_of_mem_factors (list.nth_le_mem _ _ _)⟩ rfl _,
    have hlk : l ∣ k,
    { dsimp only [l],
      split_ifs with hl,
      { exfalso, rw [odd_iff_not_even, even_iff_two_dvd, ← hl] at hm,
        exact hm ((mem_factors h0m).mp (list.nth_le_mem _ _ _)).2, },
      { rw hk, split_ifs; [apply dvd_mul_of_dvd_right, skip]; apply dvd_mul_of_dvd_right;
        exact ((mem_factors h0m).mp (list.nth_le_mem _ _ _)).2, } },
    convert congr_arg (zmod.cast_hom hlk (zmod l)) h using 1;
    rw [ring_hom.map_nat_cast] },
end

/-
/-- The Kronecker symbol of two natural numbers `a` and `n` is defined to be
the product `legendre_sym a p₁ * ... * legendre_sym a pₖ`,
where `n = p₁ * ... * pₖ` is the prime factorization of `n`.

For `n = 0`, the symbol is defined to be `1` if `a = 1` and `0` otherwise.

Warning: because of dependent types, the arguments `a` and `n` occur in the "opposite" order
compared to the "usual" order. -/
def kronecker_sym_zmod_hom (n : ℕ) : zmod n.kronecker_index →* zmod 3 :=
if hn : n = 0 then
{ to_fun := λ a, if a = -1 ∨ a = 1 then 1 else 0,
  map_one' := by { subst n, rw [nat.kronecker_index.mod_four_ne_two 0 dec_trivial], dec_trivial },
  map_mul' := begin
    subst n, rw [nat.kronecker_index.mod_four_ne_two 0 dec_trivial], dsimp [zmod],
    intros x y, rw [boole_mul, ← ite_and, ← int.coe_nat_one],
    congr' 1, apply propext,
    simp only [or_comm (_ = -_), ← int.nat_abs_eq_iff, int.nat_abs_mul, nat.mul_eq_one_iff],
  end }
else
{ to_fun := λ a, (n.factors.map (λ p, legendre_sym' p a)).prod,
  map_one' := begin
    change n ≠ 0 at hn,
    calc (n.factors.map (λ p, legendre_sym' p (1 : zmod n.kronecker_index))).prod
        = (list.repeat 1 n.factors.length).prod : _
    ... = 1 : by rw [list.prod_repeat, one_pow],
    congr' 1,
    simp only [list.eq_repeat, list.length_map, eq_self_iff_true, true_and,
      list.mem_map, mem_factors hn.bot_lt],
    rintro _ ⟨p, ⟨hp, hpn⟩, rfl⟩,
    haveI : fact p.prime := ⟨hp⟩,
    rw [zmod.cast_one],
    exact legendre_sym'_one p,

  end,
  map_mul' := _ }
-/

end nat
