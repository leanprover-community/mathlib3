/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

This is about the ideal of nilpotent elements in a commutative ring.

It is written in a somewhat constructive style, to allow us to keep
track of nilpotence exponents:

* `is_nilpotent a` is the proposition that `a` is nilpotent.

* `as_nilpotent a` is the type of pairs `⟨n,h⟩` where `h` is a proof
   that `a ^ n = 0`.  This type is nonempty iff `a` is nilpotent.
   Note that we allow `n = 0`, but `a ^ 0 = 0` only holds if the
   whole ring is trivial.

* `w_nilradical A` is the type of triples `⟨a,⟨n,h⟩⟩`, where `h` is
  a proof that `a ^ n = 0`.  The prefix `w_` is for "witnessed".

* `nilradical A` is the ideal of nilpotent elements in `A`.  This
  is represented as a structure with
  `(nilradical A).carrier = is_nilpotent : A → Prop`.  There are
  additional fields in the structure, which contain proofs that
  this carrier contains zero and is closed under addition and
  scalar multiplication.

* Lifting this, we can introduce a zero element and addition and
  scalar multiplication operations for `w_nilradical A`.  These
  satisfy most of the usual identities except that
  `0 • ⟨a,n,h⟩ = ⟨0,n,_⟩`, and this can be different from
  `0 = ⟨0,1,_⟩`,
-/

import algebra.ring
import algebra.group_power
import ring_theory.ideals
import data.nat.choose

universe u
variables {A : Type u} [comm_ring A]

namespace ring_theory

def as_nilpotent (a : A) := {n : ℕ // a ^ n = 0}

def as_nilpotent_congr {a b : A} (e : a = b)
 (ha : as_nilpotent a) : as_nilpotent b :=
  ⟨ha.val, e ▸ ha.property⟩

lemma as_nilpotent_congr_exp {a b : A} (e : a = b)
 (ha : as_nilpotent a) :
  (as_nilpotent_congr e ha).1 = ha.1 := rfl

inductive is_nilpotent (a : A) : Prop
| mk : (as_nilpotent a) → is_nilpotent

def as_nilpotent_zero : as_nilpotent (0 : A) := ⟨1, pow_one 0⟩
lemma is_nilpotent_zero : is_nilpotent (0 : A) := ⟨as_nilpotent_zero⟩

/-- The meaning of the exp_mul function is as follows:
 if x ^ n = y ^ m = 0, then (x + y) ^ (exp_mul n m) = 0.
 Usually we just have (exp_mul n m) = n + m - 1, but if
 n or m is zero then the whole ring is necessarily trivial
 and so it is natural to take exp_mul n m = 0.  With this
 definition, it works out that the exp_mul operation gives
 a commutative monoid structure on ℕ, with 1 as the identity
 element.  We prove the commutative monoid laws but we do
 not define a comm_monoid instance, to avoid interfering
 with the standard multiplicative monoid structure on ℕ.
-/

def exp_mul : ℕ → ℕ → ℕ
| 0 m := 0
| (n + 1) 0 := 0
| (n + 1) (m + 1) := n + m + 1

namespace exp_mul

lemma zero_mul (m : ℕ) : exp_mul 0 m = 0 := rfl
lemma mul_zero (n : ℕ) : exp_mul n 0 = 0 := by { cases n; refl }
lemma one_mul (m : ℕ) : exp_mul 1 m = m :=
by { cases m, refl, change 0 + m + 1 = m + 1, rw [nat.zero_add] }
lemma mul_one (n : ℕ) : exp_mul n 1 = n :=
by { cases n; refl }

lemma mul_comm (n m : ℕ) : exp_mul n m = exp_mul m n :=
 by { cases n; cases m; dsimp[exp_mul]; try {refl}, rw [add_comm n m] }

lemma mul_assoc (n m p : ℕ) :
 exp_mul (exp_mul n m) p = exp_mul n (exp_mul m p) :=
by { cases n; cases m; cases p; dsimp[exp_mul]; try {refl},
     repeat{ rw [add_assoc] } }

end exp_mul

/-- Sum of nilpotent elements is nilpotent -/
lemma nilpotent_add_aux {a b : A} {n m : ℕ}
(ea : a ^ n = 0) (eb : b ^ m = 0) : (a + b) ^ (exp_mul n m) = 0 :=
begin
  have hz : (1 : A) = 0 → (∀ (x : A), x = 0) :=
    λ h x, by { rw [← mul_one x, h, mul_zero] },
  rcases n with ⟨_|n⟩,
  { rw [pow_zero] at ea, exact hz ea _ },
  rcases m with ⟨_|m⟩,
  { rw [pow_zero] at eb, exact hz eb _ },
  have : exp_mul n.succ m.succ = n + m + 1 := rfl,
  rw [this, add_pow],
  rw [← @finset.sum_const_zero ℕ A (finset.range (n + m + 1).succ)],
  congr, ext i,
  by_cases hi : i ≥ n + 1,
  { rw [← nat.add_sub_of_le hi , pow_add , ea],
    repeat {rw [zero_mul]} },
  { replace hi := le_of_not_gt hi,
    have := nat.add_sub_of_le hi,
    have : n + m + 1 - i = (m + 1) + (n - i) :=
      by rw [← this, add_comm i, add_assoc, nat.add_sub_cancel,
             add_assoc, add_comm i, ← add_assoc,
             nat.add_sub_cancel, add_comm],
    rw [this, pow_add, eb, zero_mul, mul_zero, zero_mul] }
end

def as_nilpotent_add {a b : A}
 (ha : as_nilpotent a) (hb : as_nilpotent b) : as_nilpotent (a + b) :=
⟨exp_mul ha.val hb.val, nilpotent_add_aux ha.property hb.property⟩

lemma as_nilpotent_add_exp {a b : A}
(ha : as_nilpotent a) (hb : as_nilpotent b) :
(as_nilpotent_add ha hb).1 = exp_mul ha.1 hb.1 := rfl

lemma is_nilpotent_add {a b : A} :
  is_nilpotent a → is_nilpotent b → is_nilpotent (a + b) :=
λ ⟨ha⟩ ⟨hb⟩, ⟨as_nilpotent_add ha hb⟩

/-- Product of an arbitrary element and a nilpotent element is nilpotent -/
def as_nilpotent_smul (a : A) {b : A}
  (hb : as_nilpotent b) : as_nilpotent (a * b) :=
⟨hb.1 , by { rw [mul_pow, hb.2, mul_zero] }⟩

lemma as_nilpotent_smul_exp (a : A) {b : A} (hb : as_nilpotent b) :
  (as_nilpotent_smul a hb).1 = hb.1 := rfl

lemma is_nilpotent_smul (a : A) {b : A} :
  is_nilpotent b → is_nilpotent (a * b) :=
λ ⟨hb⟩, ⟨as_nilpotent_smul a hb⟩

/-- Negative of a nilpotent element is nilpotent -/
def as_nilpotent_neg {b : A} :
  as_nilpotent b → as_nilpotent (-b) :=
λ h, as_nilpotent_congr (neg_eq_neg_one_mul b).symm (as_nilpotent_smul (-1) h)

lemma as_nilpotent_neg_exp {a : A} (ha : as_nilpotent a) :
  (as_nilpotent_neg ha).1 = ha.1 :=
by { dsimp[as_nilpotent_neg],
     rw [as_nilpotent_congr_exp, as_nilpotent_smul_exp] }

lemma is_nilpotent_neg {b : A} :
  is_nilpotent b → is_nilpotent (-b) :=
λ ⟨hb⟩, ⟨as_nilpotent_neg hb⟩

/-- Difference of two nilpotent elements is nilpotent -/
def as_nilpotent_sub {a b : A}
  (ha : as_nilpotent a) (hb : as_nilpotent b) : as_nilpotent (a - b) :=
as_nilpotent_congr (sub_eq_add_neg a b) (as_nilpotent_add ha (as_nilpotent_neg hb))

lemma as_nilpotent_sub_exp {a b : A}
  (ha : as_nilpotent a) (hb : as_nilpotent b) :
  (as_nilpotent_sub ha hb).1 = exp_mul ha.1 hb.1 :=
by { dsimp[as_nilpotent_sub],
     rw [as_nilpotent_congr_exp, as_nilpotent_add_exp, as_nilpotent_neg_exp] }

lemma is_nilpotent_sub {a b : A} :
  is_nilpotent a → is_nilpotent b → is_nilpotent (a - b) :=
λ ⟨ha⟩ ⟨hb⟩, ⟨as_nilpotent_sub ha hb⟩

/-- If a power of a is nilpotent, then so is a -/
def as_nilpotent_chain {a : A} {n : ℕ} :
  as_nilpotent (a ^ n) → as_nilpotent a
| ⟨m , ha⟩ := ⟨n * m , (pow_mul a n m).symm ▸ ha⟩

lemma is_nilpotent_chain {a : A} {n : ℕ} :
  is_nilpotent (a ^ n) → is_nilpotent a :=
λ ⟨ha⟩, ⟨as_nilpotent_chain ha⟩

/-- The type of elements with a specified nilpotence exponent.
 This has a natural structure that almost makes it an A-module,
 but the relations 0 • a = 0 and (u + v) • a = u • a + v • a
 are not generally satisfied.
-/
variable (A)
def w_nilradical := Σ (a : A), as_nilpotent a
variable {A}

namespace w_nilradical

variables (a b c : w_nilradical A)

instance : has_coe (w_nilradical A) A := ⟨λ a, a.1⟩

def exp : ℕ := a.2.val

def prop : (a : A) ^ a.exp = 0 := a.2.property

@[extensionality]
lemma ext : ∀ {a b : w_nilradical A},
  (a : A) = (b : A) → a.exp = b.exp → a = b :=
begin
  rintro ⟨a,⟨n,ha⟩⟩ ⟨b,⟨m,hb⟩⟩ hv he,
  change a = b at hv, dsimp[exp] at he, rw [hv] at ha,
  cases hv , cases he , refl,
end

instance : has_zero (w_nilradical A) := ⟨⟨(0 : A) , as_nilpotent_zero⟩⟩

lemma zero_coe : ((0 : w_nilradical A) : A) = 0 := rfl
lemma zero_exp : (0 : w_nilradical A).exp = 1 := rfl

instance : has_add (w_nilradical A) :=
⟨λ a b, ⟨a.1 + b.1, as_nilpotent_add a.2 b.2⟩⟩

lemma add_coe : ((a + b : w_nilradical A) : A) = a + b := rfl
lemma add_exp : (a + b).exp = exp_mul a.exp b.exp := rfl

instance : has_scalar A (w_nilradical A) :=
⟨λ a b, ⟨a * b.1, as_nilpotent_smul a b.2⟩⟩

lemma smul_coe (a : A) : ((a • b : w_nilradical A) : A) = a * b := rfl
lemma smul_exp (a : A) : (a • b).exp = b.exp := rfl

instance : has_neg (w_nilradical A) :=
⟨λ a, ⟨-a.1, as_nilpotent_neg a.2⟩⟩

lemma neg_coe : ((- a : w_nilradical A) : A) = - a := rfl
lemma neg_exp : (- a).exp = a.exp := rfl

instance : has_sub (w_nilradical A) :=
⟨λ a b, ⟨a.1 - b.1, as_nilpotent_sub a.2 b.2⟩⟩

lemma sub_coe : ((a - b : w_nilradical A) : A) = a - b := rfl
lemma sub_exp (a b : w_nilradical A) : (a - b).exp = exp_mul a.exp b.exp :=
as_nilpotent_sub_exp a.2 b.2

instance : add_comm_monoid (w_nilradical A) :=
{ zero := has_zero.zero _,
  add := (+),
  zero_add := λ a,
   by { ext, rw [add_coe, zero_coe, zero_add],
            rw [add_exp, zero_exp, exp_mul.one_mul] },
  add_zero := λ a,
   by { ext, rw [add_coe, zero_coe, add_zero],
            rw [add_exp, zero_exp, exp_mul.mul_one] },
  add_comm := λ a b,
   by { ext, rw [add_coe, add_coe, add_comm],
            rw [add_exp, add_exp, exp_mul.mul_comm] },
  add_assoc := λ a b c,
   by { ext,
       { repeat { rw [add_coe] }, rw [add_assoc] },
       { repeat { rw [add_exp] }, rw [exp_mul.mul_assoc] }
      } }

lemma smul_zero (a : A) : a • (0 : w_nilradical A) = 0 :=
 by { ext, rw [smul_coe, zero_coe, mul_zero], rw [smul_exp] }

lemma smul_add (a : A) (b c : w_nilradical A) : a • (b + c) = (a • b) + (a • c) :=
 by { ext,
      rw [smul_coe, add_coe, add_coe, smul_coe, smul_coe, mul_add],
      rw [smul_exp, add_exp, add_exp, smul_exp, smul_exp] }

lemma one_smul (b : w_nilradical A) : (1 : A) • b = b :=
 by { ext, rw [smul_coe, one_mul], rw [smul_exp] }

lemma mul_smul (a b : A) (c : w_nilradical A) : (a * b) • c = a • (b • c) :=
 by { ext,
      rw [smul_coe, smul_coe, smul_coe, mul_assoc],
      rw [smul_exp, smul_exp, smul_exp] }

/- Neither zero_smul nor add_smul are satisfied in this context -/

end w_nilradical

variable (A)

/-- A ring is reduced if the only nilpotent element is zero -/
def is_reduced: Prop := ∀ (x : A), (is_nilpotent x) → (x = 0)

/-- The set of nilpotent elements, as an ideal -/
def nilradical : ideal A :=
{ carrier := is_nilpotent,
  zero := is_nilpotent_zero,
  add := λ _ _, is_nilpotent_add,
  smul := λ (a : A) {b : A} (hb : is_nilpotent b), is_nilpotent_smul a hb }

lemma mem_nilradical (x : A) : x ∈ nilradical A ↔ is_nilpotent x :=
by {refl}

/-- The quotient by the ideal of nilpotent elements -/
def reduced_quotient := (nilradical A).quotient

namespace reduced_quotient

instance : comm_ring (reduced_quotient A) :=
by { dsimp[reduced_quotient]; apply_instance }

variable {A}

def mk : A → reduced_quotient A := ideal.quotient.mk (nilradical A)

instance : is_ring_hom mk := ideal.quotient.is_ring_hom_mk (nilradical A)

lemma mk_eq_zero_iff {x : A} : mk x = 0 ↔ (is_nilpotent x) :=
 ideal.quotient.eq_zero_iff_mem

/-- The reduced quotient is reduced -/
lemma is_reduced : is_reduced (reduced_quotient A) :=
begin
 rintros ⟨x0⟩ ⟨n,e0⟩,
 apply mk_eq_zero_iff.mpr,
 have := (is_semiring_hom.map_pow mk x0 n).trans e0,
 have := mk_eq_zero_iff.mp this,
 exact is_nilpotent_chain this
end

end reduced_quotient

variable {A}

/-- Units are not nilpotent (unless the whole ring is trivial) -/
lemma unit_not_nilpotent (a b : A) :
  (a * b = 1) → ((1 : A) ≠ 0) →  ¬ is_nilpotent a :=
λ hab hz ⟨⟨m,ha⟩⟩,
  hz (by { rw [← _root_.one_pow m, ← hab, mul_pow, ha, zero_mul] })

/-- If a is nilpotent, then 1 - a is a unit -/
lemma one_sub_nilpotent_aux {a : A} {n : ℕ} (ha : a ^ n = 0) :
  (1 - a) * (geom_series a n) = 1 :=
by rw [mul_comm, geom_sum_mul_neg, ha, sub_zero]

/-- If u is a unit and a is nilpotent then u + a is a unit -/
lemma unit_add_nilpotent_aux {u v a : A} {n : ℕ}
  (hu : u * v = 1) (ha : a ^ n = 0) :
  (u + a) * (v * (geom_series (- v * a) n)) = 1 :=
begin
  rw [← mul_assoc, add_mul, hu, mul_comm a v,
      ← sub_neg_eq_add 1 (v * a), neg_mul_eq_neg_mul],
  let h₀ : (- v * a) ^ n = 0 := by { rw [mul_pow, ha, mul_zero] },
  exact one_sub_nilpotent_aux h₀
end

def unit_add_nilpotent (u : units A) (a : w_nilradical A) : units A :=
{ val := u + a,
  inv := u.inv * (finset.range a.exp).sum (λ i, (- u.inv * a) ^ i),
  val_inv := unit_add_nilpotent_aux u.val_inv a.prop,
  inv_val := (mul_comm _ _).trans (unit_add_nilpotent_aux u.val_inv a.prop) }

lemma unit_add_nilpotent_coe (u : units A) (a : w_nilradical A) :
((unit_add_nilpotent u a) : A) = u + a := rfl

end ring_theory
