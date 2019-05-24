/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

An element `a` in a commutative ring is regular if whenever
`a * x = 0` we have `x = 0`.  The regular elements form a submonoid,
which contains the group of units.
-/

import algebra.ring
import algebra.group_power group_theory.submonoid
import ring_theory.nilpotent

universe u
variables {A : Type u} [comm_ring A]

namespace ring_theory

def is_regular (a : A) : Prop := ∀ (x : A), a * x = 0 → x = 0

variable (A)
lemma is_regular_one : is_regular (1 : A) := λ x h, (one_mul x) ▸ h
variable {A}

/-- Products are regular iff the factors are regular -/
lemma is_regular_mul_iff {a b : A} :
  is_regular (a * b) ↔ (is_regular a) ∧ (is_regular b) :=
begin
  split,
  { intro hab,split,
    { intros x e,
      have e' : (a * b) * x = b * (a * x) := by rw [mul_comm a b, mul_assoc],
      rw [e, mul_zero] at e',
      exact hab _ e' },
    { intros x e,
      have e' : (a * b) * x = a * (b * x) := mul_assoc a b x,
      rw [e, mul_zero] at e',
      exact hab _ e' } },
  { rintro ⟨ha,hb⟩ x e,
    rw [mul_assoc] at e,
    replace e := ha (b * x) e,
    replace e := hb x e,
    exact e }
end

/-- Powers of a are regular iff a is regular  -/
lemma is_regular_pow_iff {a : A} {n : ℕ} :
 is_regular (a ^ (n + 1)) ↔ is_regular a :=
begin
 induction n with n ih,
 {rw[zero_add,pow_one]},
 {rw[pow_succ,is_regular_mul_iff,ih,and_self]}
end

def as_zero_divisor (a : A) := {x : A // a * x = 0 ∧ x ≠ 0}

inductive is_zero_divisor (a : A) : Prop
| mk : (as_zero_divisor a) → is_zero_divisor

theorem is_zero_divisor_iff_not_regular {a : A} :
 (is_zero_divisor a) ↔ (¬ is_regular a) :=
⟨ λ ha hr, by { rcases ha with ⟨x,hax,hx⟩, exact hx (hr x hax) },
  λ hnr, by { haveI := classical.dec,
              rcases (not_forall.mp hnr) with ⟨x,hx⟩,
              by_cases hxz : x = 0,
              { exfalso, exact hx (λ _,hxz) },
              { by_cases hax : a * x = 0,
                { exact ⟨⟨x,⟨hax,hxz⟩⟩⟩ },
                { exfalso, exact hx (λ hax', (hax hax').elim) } } } ⟩

/-- Multiplication by a regular element is injective -/
theorem is_regular_mul_inj {a : A} (ha : is_regular a) :
  function.injective (λ x : A, a * x) := λ x₁ x₂ e,
begin
  change a * x₁ = a * x₂ at e,
  rw [← sub_eq_zero, ← mul_sub] at e,
  exact sub_eq_zero.mp (ha _ e)
end

variable (A)
def regular : set A := is_regular
variable {A}

namespace regular

/-- Regular elements form a submonoid -/
instance : is_submonoid (regular A : set A) :=
{ one_mem := is_regular_one A,
  mul_mem := λ a b ha hb x hx, hb x (ha (b * x) ((mul_assoc a b x) ▸ hx)) }

/-- Invertible elements are regular -/
instance : has_coe (units A) (regular A) :=
⟨λ u,
 ⟨u.val,
  λ x hx,
   calc x = 1 * x : (one_mul x).symm
        ... = 0 : by rw[← u.inv_val,mul_assoc u.inv u.val x,hx,mul_zero] ⟩ ⟩

lemma coe_coe_unit (u : units A) : ((u : regular A) : A) = u := rfl

instance of_unit_hom : is_monoid_hom (coe : units A → regular A) :=
{ map_one := by { apply subtype.eq, refl },
  map_mul := λ u v, by { apply subtype.eq, refl} }

instance val_hom : is_monoid_hom (subtype.val : regular A → A) :=
{ map_one := rfl,
  map_mul := λ a b, rfl }

/-- A regular element plus a nilpotent element is regular -/
lemma add_nilpotent_aux {a b : A} (ha : is_regular a) (hb : is_nilpotent b) :
 is_regular (a + b) :=
begin
  rcases hb  with ⟨⟨n,hn⟩⟩,
  replace ha : is_regular (a ^ n) :=
  by { cases n with m,
       { rw [pow_zero], exact is_regular_one A },
       { exact is_regular_pow_iff.mpr ha } },
  let u := (finset.range n).sum (λ i, a ^ i * (- b) ^ (n - 1 - i)),
  have hu : u * (a - (-b)) = a ^ n - (- b) ^ n := geom_sum_mul₂ a (- b) n,
  rw [sub_neg_eq_add, ← neg_one_mul, mul_pow, hn, mul_zero, sub_zero] at hu,
  rw[← hu] at ha,
  exact (is_regular_mul_iff.mp ha).right
end

def add_nilpotent (a : regular A) (b : nilradical A) : regular A :=
⟨a + b, add_nilpotent_aux a.property b.property⟩

/-- Regular elements are not nilpotent (unless the whole ring is trivial) -/
lemma not_nilpotent_aux {a : A} (ha : is_regular a)
  {n : ℕ} (hn : a ^ n = 0) : (1 : A) = 0 :=
begin
  induction n with n ih,
  { exact (pow_zero a) ▸ hn },
  { rw[pow_succ] at hn, exact ih (ha _ hn) }
end

lemma not_nilpotent (zero_ne_one : (0 : A) ≠ (1 : A)) {a : A}
  (ha : is_regular a) : ¬ (is_nilpotent a) :=
begin
  rintro ⟨⟨n,hn⟩⟩,
  exact zero_ne_one.symm (not_nilpotent_aux ha hn)
end

end regular

end ring_theory
