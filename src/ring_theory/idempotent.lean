/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

An element `a` in a commutative ring is idempotent if `a * a = a`,
or equivalently `a * (1 - a) = 0`.  The set of idempotent elements
has a natural structure as a boolean algebra.  Idempotents are equal
if their difference is nilpotent.  If e * (1 - e) is nilpotent, then
there is a unique idempotent that is congruent to e mod nilpotents.
Every idempotent in `A` gives rise to a splitting `A ≃ B × C`.

-/

import algebra.ring algebra.group_power group_theory.submonoid order.boolean_algebra
import ring_theory.nilpotent ring_theory.regular
import tactic.ring

universe u
variables {A : Type u} [comm_ring A]

namespace ring_theory

def is_idempotent (a : A) := a * a = a

theorem is_idempotent' {a : A} : is_idempotent a ↔ a * (1 - a) = 0 :=
by { dsimp [is_idempotent],
  rw [mul_add, mul_one, mul_neg_eq_neg_mul_symm],
  rw [← sub_eq_add_neg, sub_eq_zero],
  split; intro e; exact e.symm }

namespace is_idempotent

/-- 0 and 1 are idempotent, and (1,0) and (0,1) are idempotent in
  a product ring.
-/
theorem zero : is_idempotent (0 : A) := mul_zero 0
theorem one  : is_idempotent (1 : A) := mul_one 1

theorem left {B : Type*} {C : Type*} [comm_ring B] [comm_ring C] :
  is_idempotent (⟨1, 0⟩ : B × C) :=
show  prod.mk ((1 : B) * (1 : B)) ((0 : C) * (0 : C)) = ⟨1, 0⟩,
by { rw [mul_one, mul_zero] }

theorem right {B : Type*} {C : Type*} [comm_ring B] [comm_ring C] :
  is_idempotent (⟨0, 1⟩ : B × C) :=
show  prod.mk ((0 : B) * (0 : B)) ((1 : C) * (1 : C)) = ⟨0, 1⟩,
by { rw [mul_one, mul_zero] }

/-- If a is idempotent, then (1 - 2 * a) ^ 2 = 1 -/
def invol (a : A) := 1 - 2 * a

section one_variable

variables {a : A} (ha : is_idempotent a)
include ha

/-- Positive powers of idempotents are idempotent -/
theorem pow : ∀ (n : ℕ), a ^ (n + 1) = a
| 0 := by { rw [zero_add, pow_one] }
| (n + 1) := by { have : a * a = a := ha, rw [pow_succ, pow n, this] }

/-- If a is idempotent, then so is 1 - a.  We call this (not a),
 because it is the negation operation for a boolean algebra structure
 on the set of idempotents.
-/
theorem not : is_idempotent (1 - a) :=
by { rw [is_idempotent'] at ha ⊢, rw [mul_comm, sub_sub_cancel], exact ha }

/-- 1 is the only regular idempotent -/
theorem regular (hr : is_regular a) : a = 1 :=
by { symmetry, rw [← sub_eq_zero], exact hr _ (is_idempotent'.mp ha) }

/-- 0 is the only nilpotent idempotent -/
theorem nilpotent (hn : is_nilpotent a) : a = 0 :=
by { rcases hn with ⟨n, hn'⟩, rw [← pow ha n, pow_succ, hn', mul_zero] }

theorem mul_self_invol : a * (invol a) = - a :=
by { dsimp [is_idempotent, invol] at *,
    rw [mul_add, mul_one, two_mul, neg_add, mul_add],
    rw [mul_neg_eq_neg_mul_symm, ha, add_neg_cancel_left] }

theorem invol_square : (invol a) * (invol a) = 1 :=
begin
  change (1 - 2 * a) * invol a = 1,
  rw [sub_mul, mul_assoc, mul_self_invol ha, one_mul],
  dsimp [invol], rw [mul_neg_eq_neg_mul_symm, add_neg_cancel_right],
end

end one_variable

section two_variables
variables {a b : A} (ha : is_idempotent a) (hb : is_idempotent b)
include ha hb

/-- The set of idempotents is a boolean algebra under the
  operations given below.
-/
theorem and  : is_idempotent (a * b) :=
show (a * b) * (a * b) = a * b,
by { dsimp [is_idempotent] at ha hb,
     rw [mul_assoc, mul_comm b, mul_assoc, hb, ← mul_assoc, ha] }

theorem add (hab : a * b = 0) : is_idempotent (a + b) :=
by { dsimp [is_idempotent] at *,
     rw [mul_add, add_mul, add_mul, mul_comm b a, ha, hb, hab,
         zero_add, add_zero] }

theorem or : is_idempotent (a + b - a * b) :=
begin
  have : a + b - a * b = a + (1 - a) * b :=
    by { rw [sub_mul, one_mul, add_sub] },
  rw [this],
  apply add ha (and (not ha) hb),
  rw [← mul_assoc, is_idempotent'.mp ha, zero_mul],
end

theorem xor : is_idempotent (a + b - 2 * a * b) :=
begin
  let u := a * (1 - b),
  let v := (1 - a) * b,
  have : a + b - 2 * a * b = u + v := by { dsimp [u, v], ring },
  rw [this],
  have hu := and ha (not hb),
  have hv := and (not ha) hb,
  have huv : u * v = 0 :=
  by { dsimp [u, v], rw [mul_comm a, mul_assoc, ← mul_assoc a],
       have : a * (1 + (-a)) = 0 := is_idempotent'.mp ha,
       rw [this, zero_mul, mul_zero] },
  exact add hu hv huv
end

end two_variables

/-- Idempotents are equal if their difference is nilpotent -/
theorem eq_of_sub_nilp {e₀ e₁ : A}
  (h₀ : is_idempotent e₀) (h₁ : is_idempotent e₁)
  (h : is_nilpotent (e₀ - e₁)) : e₀ = e₁ :=
begin
  dsimp [is_idempotent] at h₀ h₁,
  let x := e₀ - e₁,
  let u := 1 - 2 * e₀,
  let v := 1 + u * x,
  have hvx := calc
  v * x = (e₀ * e₀ - e₀) * (4 * e₁ - 2 * e₀ - 1) +
          (e₁ * e₁ - e₁) * (1 - 2 * e₀) :
    by { dsimp [v, u, x], ring }
   ... = 0 : by { rw [h₀, h₁, sub_self, sub_self, zero_mul, zero_mul, zero_add] },
 have hv : is_regular v :=
  regular.add_nilpotent_aux (is_regular_one A) (is_nilpotent_smul u h),
 have hx : x = 0 := hv x hvx,
 rw [← sub_eq_zero],
 exact hx,
end

/-- If e * (1 - e) is nilpotent, then there is a unique idempotent
  that is congruent to e mod nilpotents.
-/
def lift : ∀ (e : A) (h : as_nilpotent (e * (1 - e))), A :=
 λ e ⟨n, hx⟩, let y := (1 - e ^ (n + 2) - (1 - e) ^ (n + 2)) in
  e ^ (n + 2) * (finset.range n).sum (λ i, y ^ i)

theorem lift_spec (e : A) (h : as_nilpotent (e * (1 - e))) :
 pprod (is_idempotent (lift e h)) (as_nilpotent ((lift e h) - e)) :=
begin
  rcases h with ⟨n, hx⟩,
  let x := e * (1 - e), change x ^ n = 0 at hx,
  let y := 1 - e ^ (n + 2) - (1 - e) ^ (n + 2),
  let u := (finset.range n).sum (λ i, y ^ i),
  let e₁ := e ^ (n + 2) * u,
  have : lift e ⟨n, hx⟩ = e₁ := rfl,
  rw [this],
  let f := λ (i : ℕ), e ^ i * (1 - e) ^ (n + 2 - i) * nat.choose (n + 2) i,
  let z := (finset.range (n + 1)).sum
            (λ j, e ^ j * (1 - e) ^ (n - j) * (nat.choose (n + 2) (j + 1))),
  let xz := (finset.range (n + 1)).sum (f ∘ nat.succ),
  have hxz : x * z = xz := by {
    dsimp [xz, x], rw [finset.mul_sum], apply finset.sum_congr rfl, intros i hi,
    replace hi : i ≤ n := nat.le_of_lt_succ (finset.mem_range.mp hi),
    have : (f ∘ nat.succ) i = f (i + 1) := rfl, rw [this], dsimp [f],
    have : n + 2 - (i + 1) = (n - i) + 1 := calc
      n + 2 - (i + 1) = n + 1 - i : by { rw [nat.succ_sub_succ] }
      ... = (i + (n - i)) + 1 - i : by { rw [nat.add_sub_of_le hi] }
      ... = (n - i) + 1 : by { simp only [add_comm, add_assoc, nat.add_sub_cancel_left] },
    rw [this, pow_succ, pow_succ], repeat { rw [mul_assoc] }, congr' 1,
    repeat { rw [← mul_assoc] }, rw [mul_comm (1 + - e) (e ^ i)] },
  have hf₀ : f 0 = (1 - e) ^ (n + 2) :=
    by { dsimp [f], rw [nat.choose, nat.cast_one, one_mul, mul_one] },
  have hf₁ : f (n + 2) = e ^ (n + 2) :=
    by { dsimp [f],
         rw [nat.choose_self, nat.cast_one, nat.sub_self, pow_zero,
             mul_one, mul_one] },
  have := calc
   (1 : A) = (1 : A) ^ (n + 2) : (one_pow (n + 2)).symm
     ... = (e + (1 - e)) ^ (n + 2) :
       by { congr, rw [add_sub, add_comm, add_sub_cancel] }
     ... = (finset.range (n + 2).succ).sum f : add_pow e (1 - e) (n + 2)
     ... = e ^ (n + 2) + (finset.range (n + 2)).sum f :
            by rw [finset.sum_range_succ, hf₁]
     ... = e ^ (n + 2) + (xz + (1 - e) ^ (n + 2)) :
            by rw [finset.sum_range_succ', hf₀]
     ... = e ^ (n + 2) + (x * z + (1 - e) ^ (n + 2)) : by rw [hxz],
  have hxyz := calc
    y = 1 - e ^ (n + 2) - (1 - e) ^ (n + 2) : rfl
     ... = (e ^ (n + 2) + (x * z + (1 - e) ^ (n + 2)))
            - e ^ (n + 2) - (1 - e) ^ (n + 2) :
               by { congr' 2, exact this }
     ... = x * z : by { simp only [sub_eq_add_neg, add_comm, add_left_comm,
                                   add_neg_cancel_left, add_neg_cancel_right] },
  have hy : y ^ n = 0 := by { rw [hxyz, mul_pow, hx, zero_mul] },
  have hu : u * (y - 1) = y ^ n - 1 := geom_sum_mul y n,
  rw [mul_comm, hy, zero_sub] at hu, replace hu := congr_arg has_neg.neg hu,
  rw [neg_neg, neg_mul_eq_neg_mul, neg_sub] at hu,
  have : 1 - y = e ^ (n + 2) + (1 - e) ^ (n + 2) :=
    calc 1 - y = 1 - (1 - e ^ (n + 2) - (1 - e) ^ (n + 2)) : by simp only [y]
      ... = e ^ (n + 2) + (1 - e) ^ (n + 2) : by rw [sub_sub, sub_sub_cancel],
  let hu' := hu, rw [this] at hu',
  have := calc
    1 - e₁ = (e ^ (n + 2) + (1 - e) ^ (n + 2)) * u - e₁ : by { rw [hu'] }
      ... = e ^ (n + 2) * u + (1 - e) ^ (n + 2) * u - e ^ (n + 2) * u :
        by { rw [add_mul] }
      ... = (1 - e) ^ (n + 2) * u : by { rw [add_comm, add_sub_cancel] },
  have := calc
    e₁ * (1 - e₁) = (e ^ (n + 2) * u) * (1 - e₁) : rfl
    ... = u * (e ^ (n + 2) * (1 - e₁)) : by { rw [mul_comm (e ^ (n + 2))], rw [← mul_assoc] }
    ... = u * (e ^ (n + 2) * (1 - e) ^ (n + 2) * u) : by { rw [this, mul_assoc] }
    ... = u * (x ^ (n + 2) * u) : by { rw [mul_pow, pow_add] }
    ... = 0 : by { rw [pow_add, hx, zero_mul, zero_mul, mul_zero] },
  split, { exact is_idempotent'.mpr this },
  let w := geom_series₂ 1 e (n + 1),
  have hw : x * w = e - e ^ (n + 2) := calc
    x * w = e * (w * (1 - e)) : by { dsimp [x], rw [mul_assoc, mul_comm _ w] }
    ... = e * (1 - e ^ (n + 1)) : by { rw [geom_sum_mul₂ 1 e (n + 1), one_pow] }
    ... = e - e ^ (n + 2) : by { rw [mul_sub, mul_one, pow_succ e (n + 1)] },
  have hu'' : u = 1 + x * z * u := by {
    rw [sub_mul, hxyz, one_mul] at hu, rw [← hu, sub_add_cancel] },
  have := calc
    e₁ - e = e ^ (n + 2) * u - e : rfl
    ... = e ^ (n + 2) * (1 + x * z * u) - e : by { congr' 2, exact hu'' }
    ... = (e ^ (n + 2) * (x * z * u) + e ^ (n + 2)) - e :
           by rw [mul_add, mul_one, add_comm]
    ... = x * (e ^ (n + 2) * z * u) - (e - e ^ (n + 2)) :
           by { rw [← sub_add, sub_eq_add_neg, sub_eq_add_neg],
             rw [← mul_assoc, ← mul_assoc, mul_comm (e ^ (n + 2))],
             repeat { rw [add_assoc] }, rw [add_comm (e ^ (n + 2))],
             repeat { rw [mul_assoc] } }
    ... = x * (e ^ (n + 2) * z * u - w) : by { rw [mul_sub, hw] },
  have : (e₁ - e) ^ n = 0 := by { rw [this, mul_pow, hx, zero_mul] },
  exact ⟨n, this⟩
end

theorem lift_unique (e e₁ : A)
 (h : as_nilpotent (e * (1 - e))) (hi : is_idempotent e₁)
 (hn : is_nilpotent (e₁ - e)) : e₁ = lift e h :=
begin
  rcases lift_spec e h with ⟨hi', hn'⟩,
  apply eq_of_sub_nilp hi hi',
  have : e₁ - lift e h = (e₁ - e) - (lift e h - e) :=
    by { rw [sub_sub_sub_cancel_right] },
  rw [this],
  apply is_nilpotent_sub hn ⟨hn'⟩
end

end is_idempotent

namespace is_idempotent

variables {e : A} (he : is_idempotent e)
include he

/-- An idempotent e gives a splitting of the form A ≃ B × C.
  The first factor will be denoted by (axis he), where he
  is the proof that e is idempotent.
-/

def axis := {b : A // b * e = b}

namespace axis

instance : has_coe (axis he) A := ⟨subtype.val⟩

theorem eq (b₁ b₂ : axis he) : (b₁ : A) = (b₂ : A) → b₁ = b₂ := subtype.eq

def mk (b : A) (hb : b * e = b) : axis he := ⟨b, hb⟩

theorem coe_mk {b : A} (hb : b * e = b) : ((mk he b hb) : A) = b := rfl

instance : has_zero (axis he) := ⟨⟨(0 : A), zero_mul e⟩⟩

instance : has_one (axis he) := ⟨⟨e, he⟩⟩

instance : has_neg (axis he) :=
⟨λ b, axis.mk he (- b.val) (by { rw [← neg_mul_eq_neg_mul, b.property] })⟩

instance : has_add (axis he) :=
⟨λ b₁ b₂, axis.mk he (b₁.val + b₂.val) (by { rw [add_mul, b₁.property, b₂.property] })⟩

instance : has_mul (axis he) :=
⟨λ b₁ b₂, axis.mk he (b₁.val * b₂.val) (by { rw [mul_assoc, b₂.property] })⟩

@[simp] theorem zero_coe : ((0 : axis he) : A) = 0 := rfl

@[simp] theorem one_coe  : ((1 : axis he) : A) = e := rfl

@[simp] theorem neg_coe (b : axis he) : (((- b) : axis he) : A) = - b := rfl

@[simp] theorem add_coe (b₁ b₂ : axis he) :
 ((b₁ + b₂ : axis he) : A) = b₁ + b₂ := rfl

@[simp] theorem mul_coe (b₁ b₂ : axis he) :
 ((b₁ * b₂ : axis he) : A) = b₁ * b₂ := rfl

instance : comm_ring (axis he) :=
by {
  refine_struct
  { zero := has_zero.zero _,
    one  := has_one.one _,
    neg  := has_neg.neg,
    add  := has_add.add,
    mul  := has_mul.mul,
    .. };
  try { rintro ⟨a, ha⟩ };
  try { rintro ⟨b, hb⟩ };
  try { rintro ⟨c, hc⟩ };
  apply eq,
  { repeat { rw [add_coe] }, apply add_assoc },
  { rw [add_coe, zero_coe, zero_add] },
  { rw [add_coe, zero_coe, add_zero] },
  { rw [add_coe, neg_coe, zero_coe, neg_add_self] },
  { rw [add_coe, add_coe, add_comm] },
  { repeat { rw [mul_coe] }, rw [mul_assoc] },
  { rw [mul_coe, one_coe, mul_comm], exact ha },
  { rw [mul_coe, one_coe], exact ha },
  { rw [mul_coe, add_coe, add_coe, mul_coe, mul_coe, mul_add] },
  { rw [mul_coe, add_coe, add_coe, mul_coe, mul_coe, add_mul] },
  { rw [mul_coe, mul_coe, mul_comm] } }

def proj : A → axis he :=
 λ a, ⟨a * e, by { dsimp [is_idempotent] at he, rw [mul_assoc, he] }⟩

instance proj_ring_hom : is_ring_hom (proj he) := {
  map_one := by { apply eq, change 1 * e = e, rw [one_mul] },
  map_add := λ a b, by { apply eq,
                         change (a + b) * e = a * e + b * e,
                         rw [add_mul] },
  map_mul := λ a b, by { dsimp [is_idempotent] at he,
                         apply eq,
                         change (a * b) * e = (a * e) * (b * e),
                         rw [mul_assoc a e, ← mul_assoc e b e, mul_comm e b,
                             mul_assoc b e, he, mul_assoc] } }

def split : A → (axis he) × (axis (is_idempotent.not he)) :=
λ a, ⟨(proj he a), (proj (is_idempotent.not he) a)⟩

instance split_ring_hom : is_ring_hom (split he) :=
let he' := is_idempotent.not he in
{ map_one := by {
    ext,
    { exact is_ring_hom.map_one (proj he) },
    { exact is_ring_hom.map_one (proj he') } },
  map_add := λ a b, by {
    dsimp [split], ext,
    { exact @is_ring_hom.map_add _ _ _ _ (proj he ) _ a b },
    { exact @is_ring_hom.map_add _ _ _ _ (proj he') _ a b } },
  map_mul := λ a b, by {
    dsimp [split], ext,
    { exact @is_ring_hom.map_mul _ _ _ _ (proj he ) _ a b },
    { exact @is_ring_hom.map_mul _ _ _ _ (proj he') _ a b } } }

theorem mul_eq_zero (b : axis he) (c : axis (is_idempotent.not he)) :
 (b : A) * (c : A) = 0 :=
begin
  rcases b with ⟨b, hb⟩,
  rcases c with ⟨c, hc⟩,
  change b * c = 0,
  exact calc
    b * c = (b * e) * (c * (1 - e)) : by rw [hb, hc]
    ... = b * (e * (1 - e)) * c :
      by { rw [mul_comm c, mul_assoc, mul_assoc, mul_assoc] }
    ... = 0 : by { rw [is_idempotent'.mp he, mul_zero, zero_mul] }
end

def combine : (axis he) × (axis (is_idempotent.not he)) → A :=
λ bc, bc.1.val + bc.2.val

instance combine_ring_hom : is_ring_hom (combine he) :=
{ map_one := by { change e + (1 - e) = 1, rw [add_sub_cancel'_right] },
  map_add := λ bc₁ bc₂, by {
    rcases bc₁ with ⟨⟨b₁, hb₁⟩, ⟨c₁, hc₁⟩⟩,
    rcases bc₂ with ⟨⟨b₂, hb₂⟩, ⟨c₂, hc₂⟩⟩,
    change (b₁ + b₂) + (c₁ + c₂) = (b₁ + c₁) + (b₂ + c₂),
    rw [add_assoc, ← add_assoc b₂, add_comm b₂ c₁, add_assoc, add_assoc] },
  map_mul := λ bc₁ bc₂, by {
    rcases bc₁ with ⟨⟨b₁, hb₁⟩, ⟨c₁, hc₁⟩⟩,
    rcases bc₂ with ⟨⟨b₂, hb₂⟩, ⟨c₂, hc₂⟩⟩,
    change (b₁ * b₂) + (c₁ * c₂) = (b₁ + c₁) * (b₂ + c₂),
    have ebc : b₁ * c₂ = 0 := mul_eq_zero he ⟨b₁, hb₁⟩ ⟨c₂, hc₂⟩,
    have ecb : b₂ * c₁ = 0 := mul_eq_zero he ⟨b₂, hb₂⟩ ⟨c₁, hc₁⟩,
    rw [mul_comm] at ecb,
    rw [mul_add, add_mul, add_mul, ebc, ecb, zero_add, add_zero] } }

theorem combine_split (a : A) : combine he (split he a) = a :=
by { change a * e + a * (1 - e) = a,
     rw [mul_sub, mul_one, add_sub_cancel'_right] }

theorem split_combine (bc : (axis he) × (axis (is_idempotent.not he))) :
  split he (combine he bc) = bc :=
begin
  have he' : e * (1 - e) = 0 := is_idempotent'.mp he,
  rcases bc with ⟨⟨b, hb⟩, ⟨c, hc⟩⟩,
  ext; apply subtype.eq,
  { change (b + c) * e = b,
    rw [← hc, add_mul, hb, mul_assoc, mul_comm (1 - e), he', mul_zero, add_zero] },
  { change (b + c) * (1 - e) = c,
    rw [← hb, add_mul, hc, mul_assoc, he', mul_zero, zero_add] }
end

end axis

end is_idempotent

variable (A)
def idempotent := {a : A // is_idempotent a}
variable {A}

namespace idempotent

variables (a b c : idempotent A)

instance : has_coe (idempotent A) A := ⟨subtype.val⟩

theorem eq (a₁ a₂ : idempotent A) : (a₁ : A) = (a₂ : A) → a₁ = a₂ :=
subtype.eq

theorem mul_self : (a * a : A) = a := a.property

theorem mul_not : (a * (1 - a) : A) = 0 := is_idempotent'.mp a.property

instance : has_le (idempotent A) := ⟨λ a b, (a * b : A) = a⟩
instance : lattice.has_bot (idempotent A) := ⟨⟨0, is_idempotent.zero⟩⟩
instance : lattice.has_top (idempotent A) := ⟨⟨1, is_idempotent.one⟩⟩

instance : has_neg (idempotent A) :=
⟨λ a, ⟨((1 - a) : A), is_idempotent.not a.property⟩⟩

instance : lattice.has_inf (idempotent A) :=
⟨λ a b, ⟨a * b, is_idempotent.and a.property b.property⟩⟩

instance : lattice.has_sup (idempotent A) :=
⟨λ a b, ⟨a + b - a * b, is_idempotent.or a.property b.property⟩⟩

theorem le_iff {a b : idempotent A} : a ≤ b ↔ (a * b : A) = a := by { refl }
theorem bot_coe : ((⊥ : idempotent A) : A) = 0 := rfl
theorem top_coe : ((⊤ : idempotent A) : A) = 1 := rfl

theorem neg_coe : ((- a : idempotent A) : A) = 1 - a := rfl
theorem inf_coe : ((a ⊓ b : idempotent A) : A) = a * b := rfl
theorem sup_coe : ((a ⊔ b : idempotent A) : A) = a + b - a * b := rfl

theorem neg_neg : - (- a) = a :=
by { apply eq, rw [neg_coe, neg_coe, sub_sub_cancel] }

theorem neg_inj {a b : idempotent A} (h : - a = - b) : a = b :=
by { rw [← neg_neg a, ← neg_neg b, h] }

theorem neg_le_neg {a b : idempotent A} : a ≤ b ↔ (- b) ≤ (- a) :=
begin
  rw [le_iff, le_iff, neg_coe, neg_coe, mul_sub, sub_mul, sub_mul],
  rw [mul_one, mul_one, one_mul, sub_sub, mul_comm (b : A), sub_left_inj],
  split,
  { intro h, rw [h, sub_self, add_zero] },
  { intro h, symmetry, rw [← sub_eq_zero],
    exact (add_left_inj (b : A)).mp (h.trans (add_zero (b : A)).symm) }
end

theorem neg_bot : - (⊥ : idempotent A) = ⊤ :=
by { apply eq, rw [neg_coe, bot_coe, top_coe, sub_zero] }

theorem neg_sup : - (a ⊔ b) = (- a) ⊓ (- b) :=
by { apply eq, rw [neg_coe, sup_coe, inf_coe, neg_coe, neg_coe], ring }

theorem neg_top : - (⊤ : idempotent A) = ⊥ :=
by { apply eq, rw [neg_coe, bot_coe, top_coe, sub_self] }

theorem neg_inf : - (a ⊓ b) = (- a) ⊔ (- b) :=
by { apply neg_inj, rw [neg_sup, neg_neg, neg_neg, neg_neg] }

theorem le_refl : a ≤ a := by { rw [le_iff, a.mul_self] }

theorem le_antisymm {a b : idempotent A} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
by { apply eq, rw [le_iff] at *, rw [mul_comm] at hba, exact hab.symm.trans hba }

theorem le_trans {a b c : idempotent A} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
by { rw [le_iff] at *, exact calc
     ((a * c) : A) = a * b * c : by rw [hab]
      ... = a : by rw [mul_assoc, hbc, hab] }

theorem le_top : a ≤ ⊤ := by rw [le_iff, top_coe, mul_one]

theorem le_inf (hab : a ≤ b) (hac : a ≤ c) : a ≤ b ⊓ c :=
by { rw [le_iff] at *, rw [inf_coe, ← mul_assoc, hab, hac] }

theorem inf_le_left : a ⊓ b ≤ a :=
by { rw [le_iff, inf_coe, mul_comm, ← mul_assoc, a.mul_self] }

theorem inf_le_right : a ⊓ b ≤ b :=
by { rw [le_iff, inf_coe, mul_assoc, b.mul_self] }

theorem bot_le : ⊥ ≤ a :=
by { rw [le_iff, bot_coe, zero_mul] }

theorem sup_le (hac : a ≤ c) (hbc : b ≤ c) : a ⊔ b ≤ c :=
by { rw [neg_le_neg] at *, rw [neg_sup], exact le_inf _ _ _ hac hbc }

theorem le_sup_left : a ≤ a ⊔ b :=
by { rw [neg_le_neg, neg_sup], apply inf_le_left }

theorem le_sup_right : b ≤ a ⊔ b :=
by { rw [neg_le_neg, neg_sup], apply inf_le_right }

theorem inf_sup_distrib : a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) :=
by { apply eq, simp only [inf_coe, sup_coe, mul_add, mul_sub],
     congr' 1, rw [← mul_assoc, ← mul_assoc], congr' 1,
     rw [mul_assoc, mul_comm (b : A), ← mul_assoc, a.mul_self] }

theorem sup_inf_distrib : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) :=
by { apply neg_inj,
     rw [neg_sup, neg_inf, neg_inf, neg_sup, neg_sup, inf_sup_distrib] }

theorem inf_neg_eq_bot (a : idempotent A) : a ⊓ (- a) = ⊥ :=
by { apply eq, rw [inf_coe, bot_coe, neg_coe, mul_not] }

theorem sup_neg_eq_top (a : idempotent A) : a ⊔ (- a) = ⊤ :=
by { apply neg_inj, rw [neg_sup, neg_top, inf_neg_eq_bot] }

instance : lattice.boolean_algebra (idempotent A) := {
  le := has_le.le,
  bot := ⊥,
  top := ⊤,
  sup := lattice.has_sup.sup,
  inf := lattice.has_inf.inf,
  neg := has_neg.neg,
  sub := λ a b, a ⊓ (- b),
  le_refl := le_refl,
  le_antisymm := λ a b hab hba, le_antisymm hab hba,
  le_trans := λ a b c hab hbc, le_trans hab hbc,
  bot_le := bot_le,
  le_top := le_top,
  le_inf := le_inf,
  inf_le_left := inf_le_left,
  inf_le_right := inf_le_right,
  sup_le := sup_le,
  le_sup_left := le_sup_left,
  le_sup_right := le_sup_right,
  le_sup_inf := λ a b c, by { rw [sup_inf_distrib] },
  inf_neg_eq_bot := inf_neg_eq_bot,
  sup_neg_eq_top := sup_neg_eq_top,
  sub_eq := λ a b, rfl
}

end idempotent

end ring_theory
