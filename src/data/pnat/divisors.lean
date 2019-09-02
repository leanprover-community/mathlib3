/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import data.fintype data.pnat.basic tactic.alias

/-!
# Divisors of a positive natural number

Given a number `n : ℕ+`, `divisors n` is the set of all positive
numbers `d` such that `d ∣ n`.

We prove a few equivalences involving this type:

* `divisors n ≃ { d : fin (n + 1) // d ∣ n }`;
* `divisors n ≃ { d : ℕ // d ∣ n }`;
* given two coprime numbers `m` and `n`, `divisors (m * n) ≃ divisors m × divisors n`;
* `rev_equiv : equiv.perm (divisors n)`, `rev_equiv d = n / d`.
-/

namespace pnat

/-- Divisors of a positive natural number -/
def divisors (n : ℕ+) : Type := { d : ℕ+ // d ∣ n }

instance divisors.has_coe (n : ℕ+) : has_coe (divisors n) ℕ+ := ⟨subtype.val⟩

/-- A natural divisor of a positive number is positive -/
def divisors.of_dvd {n : ℕ+} {d : ℕ} (h : d ∣ n) : divisors n :=
⟨⟨d, nat.pos_of_dvd_of_pos h n.2⟩, h⟩

alias divisors.of_dvd ← has_dvd.dvd.to_pnat_divisors

def divisors_equiv_subtype_nat (n : ℕ+) : divisors n ≃ { m : ℕ // m ∣ n } :=
@equiv.subtype_subtype_equiv_subtype ℕ ((<) 0) (λ m, m ∣ n) (λ m h, nat.pos_of_dvd_of_pos h n.2)

def divisors_equiv_subtype_fin (n : ℕ+) : divisors n ≃ { m : fin (n + 1) // (m : ℕ) ∣ n } :=
calc divisors n ≃ { m : ℕ // m ∣ n } : n.divisors_equiv_subtype_nat
            ... ≃ { m : {m : ℕ // m < n+1} // (m : ℕ) ∣ n } :
  (@equiv.subtype_subtype_equiv_subtype ℕ ((>) (n+1)) (λ m, (m : ℕ) ∣ n) $
    λ m h, nat.lt_succ_of_le $ nat.le_of_dvd n.2 h).symm
            ... ≃ { m : fin (n + 1) // (m : ℕ) ∣ n } :
  equiv.subtype_congr (equiv.fin_equiv_subtype _).symm $ λ m, iff.rfl

namespace divisors

instance (n : ℕ+) : fintype (divisors n) := fintype.of_equiv _ n.divisors_equiv_subtype_fin.symm

/-- The equivalence that reverses the divisors of `n` sending each `d` to `n / d`. -/
def rev_equiv (n : ℕ+) : equiv.perm (divisors n) :=
{ to_fun := λ d, of_dvd $ nat.div_dvd_of_dvd d.property,
  inv_fun := λ d, of_dvd $ nat.div_dvd_of_dvd d.property,
  right_inv := λ d, subtype.ext.2 $ subtype.ext.2 $ nat.div_div_self d.property n.property,
  left_inv := λ d, subtype.ext.2 $ subtype.ext.2 $ nat.div_div_self d.property n.property }

abbreviation rev {n : ℕ+} : divisors n → divisors n := rev_equiv n

lemma rev_involutive {n : ℕ+} (d : divisors n) : rev (rev d) = d := (rev_equiv n).left_inv d

@[simp] lemma mul_rev {n : ℕ+} (d : divisors n) : (d : ℕ+) * d.rev = n :=
subtype.ext.2 $ nat.mul_div_cancel' d.2
@[simp] lemma rev_mul {n : ℕ+} (d : divisors n) : (d.rev : ℕ+) * d = n :=
subtype.ext.2 $ nat.div_mul_cancel d.2

@[simp] lemma mul_rev_nat {n : ℕ+} (d : divisors n) : (d : ℕ) * d.rev = n :=
congr_arg subtype.val d.mul_rev
@[simp] lemma rev_mul_nat {n : ℕ+} (d : divisors n) : (d.rev : ℕ) * d = n :=
congr_arg subtype.val d.rev_mul

def fin_rev_mul {n : ℕ+} (d : divisors n) (k : fin d) : fin n :=
by refine ⟨(d.rev : ℕ) * k, _⟩;
calc (d.rev : ℕ) * k < d.rev * d : nat.mul_lt_mul_of_pos_left k.2 (pos _)
                 ... = n         : rev_mul_nat d

def fin_rev_div {n : ℕ+} (d : divisors n) (k : fin n) : fin d :=
⟨(k : ℕ) / d.rev, nat.div_lt_of_lt_mul $ d.rev_mul_nat.symm ▸ k.2⟩

lemma fin_rev_div_mul_eq {n : ℕ+} (d : divisors n) (k : fin d) :
  d.fin_rev_div (d.fin_rev_mul k) = k :=
fin.eq_of_veq $ nat.mul_div_right _ (pos _)

lemma fin_rev_mul_div_eq_of_dvd {n : ℕ+} (d : divisors n) (k : fin n) (h : (d.rev : ℕ) ∣ k) :
  d.fin_rev_mul (d.fin_rev_div k) = k :=
fin.eq_of_veq $ nat.mul_div_cancel' h

def of_mul_of_coprime_equiv_prod {k l : ℕ+} (h : nat.coprime k l) :
  divisors (k * l) ≃ divisors k × divisors l :=
{ to_fun := λ x, ⟨⟨gcd (x : ℕ+) k, gcd_dvd_right _ _⟩, ⟨gcd (x : ℕ+) l, gcd_dvd_right _ _⟩⟩,
  inv_fun := λ x, ⟨(x.fst : ℕ+) * x.snd, mul_dvd_mul x.fst.property x.snd.property⟩,
  right_inv :=
  begin
  rintros ⟨⟨x, hx⟩, ⟨y, hy⟩⟩,
  ext1; apply subtype.eq,
    { calc gcd (x * y) k = gcd x k : subtype.eq $ (h.symm.coprime_dvd_left hy).gcd_mul_right_cancel x 
                     ... = x       : subtype.eq $ nat.gcd_eq_left_iff_dvd.1 hx },
    { calc gcd (x * y) l = gcd y l : subtype.eq $ (h.coprime_dvd_left hx).gcd_mul_left_cancel y
                     ... = y       : subtype.eq $ nat.gcd_eq_left_iff_dvd.1 hy }
  end,
  left_inv :=
  begin
  rintros ⟨x, hx⟩,
  apply subtype.eq,
  calc (gcd x k) * (gcd x l) = gcd x (k * l) : subtype.eq $ (h.gcd_mul x).symm
                         ... = x             : subtype.eq $ nat.gcd_eq_left_iff_dvd.1 hx
  end }

alias of_mul_of_coprime_equiv_prod ← nat.coprime.divisors_mul_equiv_prod_divisors

end divisors
end pnat
