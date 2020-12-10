/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import group_theory.congruence
import linear_algebra.basic

/-!
# Tensor product of an indexed family of semimodules over commutative semirings

## Notations

## Tags

multilinear, tensor, tensor product
-/

noncomputable theory
open_locale classical
open function

section semiring

variables {ι : Type*} {R : Type*} [comm_semiring R] [nonempty ι]
variables {s : ι → Type*} [∀ i, add_comm_monoid (s i)] [∀ i, semimodule R (s i)]

namespace pi_tensor_product
include R
variables (R) (s)

/-- The relation on `free_add_monoid (Π i, s i)` that generates a congruence whose quotient is
the tensor product. -/
inductive eqv : free_add_monoid (Π i, s i) → free_add_monoid (Π i, s i) → Prop
| of_zero : ∀ (f : Π i, s i) (i : ι) (hf : f i = 0), eqv (free_add_monoid.of f) 0
| of_add : ∀ (f : Π i, s i) (i : ι) (m₁ m₂ : s i), eqv
    (free_add_monoid.of (update f i m₁) + free_add_monoid.of (update f i m₂))
    (free_add_monoid.of (update f i (m₁ + m₂)))
| of_smul : ∀ (f : Π i, s i) (i j : ι) (r : R), eqv
    (free_add_monoid.of (update f i (r • (f i))))
    (free_add_monoid.of (update f j (r • (f j))))
| add_comm : ∀ x y, eqv (x + y) (y + x)

end pi_tensor_product

variables (R) (s)

def pi_tensor_product : Type* :=
(add_con_gen (pi_tensor_product.eqv R s)).quotient

variables {R}

/- This enables the notation `⨂[R] i : ι, s i` for the pi tensor product, given `s : ι → Type*`. -/
localized "notation `⨂[`:100 R `] ` binders `, ` r:(scoped:67 f, pi_tensor_product R f) := r"
  in tensor_product

open_locale tensor_product

namespace pi_tensor_product

section module

instance : add_comm_monoid (⨂[R] i, s i) :=
{ add_comm := λ x y, add_con.induction_on₂ x y $ λ x y, quotient.sound' $
    add_con_gen.rel.of _ _ $ eqv.add_comm _ _,
  .. (add_con_gen (pi_tensor_product.eqv R s)).add_monoid }

instance : inhabited (⨂[R] i, s i) := ⟨0⟩

variables (R) {s}

def tprod (f : Π i, s i) : ⨂[R] i, s i := add_con.mk' _ $ free_add_monoid.of f
variables {R}

notation `⨂ₜ[`:100 R`] ` binders `, ` r:(scoped:67 f, tprod R f) := r

@[elab_as_eliminator]
protected theorem induction_on
  {C : (⨂[R] i, s i) → Prop}
  (z : ⨂[R] i, s i)
  (C0 : C 0)
  (C1 : ∀ {f : Π i, s i}, C (⨂ₜ[R] i : ι, f i))
  (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
add_con.induction_on z $ λ x, free_add_monoid.rec_on x C0 $ λ f y ih,
by { rw add_con.coe_add, exact Cp C1 ih }

lemma zero_tprod (f : Π i, s i) (i : ι) (hf: f i = 0) : ⨂ₜ[R] i, f i = 0 :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero _ i hf

@[simp] lemma zero_tprod' (f : Π i, s i) (i : ι) : tprod R (update f i 0) = 0 :=
zero_tprod _ i (update_same i 0 f)

lemma add_tprod (f : Π i, s i) (i : ι) (m₁ m₂ : s i) :
  (⨂ₜ[R] j, (update f i m₁) j) + (⨂ₜ[R] j, (update f i m₂) j) = ⨂ₜ[R] j, (update f i (m₁ + m₂)) j :=
quotient.sound' $ add_con_gen.rel.of _ _ (eqv.of_add f i m₁ m₂)

lemma smul_tprod (f : Π i, s i) (i j : ι) (r : R) :
  ⨂ₜ[R] k, (update f i (r • f i) k) = ⨂ₜ[R] k, (update f j (r • f j)) k :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_smul _ _ _ _

/-- Auxiliary function for defining scalar multiplication on the tensor product. -/
def smul.aux (r : R) : free_add_monoid (Π i, s i) →+ ⨂[R] i, s i :=
let i : ι := classical.choice (by apply_instance) in
  free_add_monoid.lift $ λ (f : Π i, s i), ⨂ₜ[R] k, (update f i (r • f i)) k

theorem smul.aux_of (r : R) (f : Π i, s i) (i : ι) :
  smul.aux r (free_add_monoid.of f) = ⨂ₜ[R] k, (update f i (r • f i)) k :=
smul_tprod f (classical.choice (by apply_instance)) i r

instance : has_scalar R (⨂[R] i, s i) :=
⟨λ r, (add_con_gen (pi_tensor_product.eqv R s)).lift (smul.aux r) $ add_con.add_con_gen_le $
λ x y hxy, match x, y, hxy with
| _, _, (eqv.of_zero f i hf)        := (add_con.ker_rel _).2 $
    by rw [add_monoid_hom.map_zero, smul.aux_of _ _ i, hf, smul_zero,
          zero_tprod _ i (update_same i 0 f)]
| _, _, (eqv.of_add f i m₁ m₂)      := (add_con.ker_rel _).2 $
    by simp [smul.aux_of _ _ i, smul_add, add_tprod]
| _, _, (eqv.of_smul f i j r')     := (add_con.ker_rel _).2 $
    by simp [smul.aux_of _ _ j, smul_tprod _ j i r, smul_smul, smul_tprod f i j _]
| _, _, (eqv.add_comm x y)         := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, add_comm]
end⟩

protected theorem smul_zero (r : R) : (r • 0 : ⨂[R] i, s i) = 0 :=
add_monoid_hom.map_zero _

protected theorem smul_add (r : R) (x y : ⨂[R] i, s i) :
  r • (x + y) = r • x + r • y :=
add_monoid_hom.map_add _ _ _

theorem smul_tprod' (r : R) (f : Π i, s i) (i : ι) :
  r • (tprod R f) = tprod R (update f i (r • f i)) :=
smul_tprod f (classical.choice (by apply_instance)) i r

instance : semimodule R (⨂[R] i, s i) :=
let j : ι := classical.choice (by apply_instance) in
{ smul := (•),
  smul_add := λ r x y, pi_tensor_product.smul_add r x y,
  mul_smul := λ r r' x,
    begin
      refine pi_tensor_product.induction_on x _ _ _,
      { simp_rw pi_tensor_product.smul_zero },
      { intros f,
        simp [smul_tprod' _ _ j, mul_smul] },
      { intros x y ihx ihy,
        simp_rw [pi_tensor_product.smul_add],
        rw [ihx, ihy] }
    end,
  one_smul := λ x, pi_tensor_product.induction_on x
    (by rw pi_tensor_product.smul_zero)
    (λ f, by simp [smul_tprod' _ _ j])
    (λ z y ihz ihy, by simp_rw [pi_tensor_product.smul_add, ihz, ihy]),
  add_smul := λ r r' x,
    begin
      refine pi_tensor_product.induction_on x _ _ _,
      { simp_rw [pi_tensor_product.smul_zero, add_zero] },
      { intro f,
        simp_rw [smul_tprod' _ _ j, add_smul, add_tprod] },
      { intros x y ihx ihy,
        simp_rw pi_tensor_product.smul_add,
        rw [ihx, ihy, add_add_add_comm] }
    end,
  smul_zero := λ r, pi_tensor_product.smul_zero r,
  zero_smul := λ x,
    begin
      refine pi_tensor_product.induction_on x _ _ _,
      { rw pi_tensor_product.smul_zero },
      { intro f,
        rw [smul_tprod' _ _ j, zero_smul],
        exact zero_tprod (update f j 0) j (update_same j 0 f) },
      { intros x y ihx ihy,
        rw [pi_tensor_product.smul_add, ihx, ihy, add_zero] },
    end }

section sum
open_locale big_operators

lemma tprod_map_sum {α : Type*} (t : finset α) (i : ι) (m : α → s i) (f : Π i, s i):
  tprod R (update f i (∑ a in t, m a)) = ∑ a in t, tprod R (update f i (m a)) :=
begin
  induction t using finset.induction with a t has ih h,
  { simp },
  { simp [finset.sum_insert has, ←add_tprod, ih] }
end

end sum

end module

end pi_tensor_product

end semiring
