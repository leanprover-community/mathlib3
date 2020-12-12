/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import group_theory.congruence
import linear_algebra.multilinear

/-!
# Tensor product of an indexed family of semimodules over commutative semirings

We define the tensor product of an indexed family `s : ι → Type*` of semimodules over commutative
semirings. We denote this space by `⨂[R] i, s i` and define it as `free_add_monoid (Π i, s i)`
quotiented by the appropriate equivalence relation. The treatment follows very closely that of the
binary tensor product in `linear_algebra/tensor_product.lean`.

## Main definitions

* `pi_tensor_product R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor product
  of all the `s i`'s. This is denoted by `⨂[R] i, s i`.
* `tprod R f` with `f : Π i, s i` is the tensor product of the vectors `f i` over all `i : ι`.
* `mk R s` is the canonical multilinear map from `Π i, s i` to `⨂[R] i, s i`.
* `lift φ` with `φ : multilinear_map R s E` is the corresponding linear map
  `(⨂[R] i, s i) →ₗ[R] E`.

## Notations

* `⨂[R] i, s i` is defined as localized notation in locale `tensor_product`
* `⨂ₜ[R] i, f i` with `f : Π i, f i` is defined globally as the tensor product of all the `f i`'s.

## Implementation notes

We have not restricted the index type `ι` to be a `fintype`, as nothing we do here strictly requires
it. However, problems may arise in the case where `ι` is infinite; use at your own caution.

## TODO

* Define tensor powers, symmetric subspace, etc.
* API for the various ways `ι` can be split into subsets; connect this with the binary
  tensor product.
* Include connection with holors.
* Port more of the API from the binary tensor product over to this case.

## Tags

multilinear, tensor, tensor product
-/

noncomputable theory
open_locale classical
open function

section semiring

variables {ι : Type*} {R : Type*} [comm_semiring R]
variables {s : ι → Type*} [∀ i, add_comm_monoid (s i)] [∀ i, semimodule R (s i)]
variables {E : Type*} [add_comm_monoid E] [semimodule R E]

namespace pi_tensor_product
include R
variables (R) (s)

/-- The relation on `free_add_monoid (R × Π i, s i)` that generates a congruence whose quotient is
the tensor product. -/
inductive eqv : free_add_monoid (R × Π i, s i) → free_add_monoid (R × Π i, s i) → Prop
| of_zero : ∀ (r : R) (f : Π i, s i) (i : ι) (hf : f i = 0), eqv (free_add_monoid.of (r, f)) 0
| of_zero_scalar : ∀ (f : Π i, s i), eqv (free_add_monoid.of (0, f)) 0
| of_add : ∀ (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i), eqv
    (free_add_monoid.of (r, update f i m₁) + free_add_monoid.of (r, update f i m₂))
    (free_add_monoid.of (r, update f i (m₁ + m₂)))
| of_add_scalar : ∀ (r r' : R) (f : Π i, s i), eqv
    (free_add_monoid.of (r, f) + free_add_monoid.of (r', f))
    (free_add_monoid.of (r + r', f))
| of_smul : ∀ (r : R) (f : Π i, s i) (i : ι) (r' : R), eqv
    (free_add_monoid.of (r, update f i (r' • (f i))))
    (free_add_monoid.of (r' * r, f))
| add_comm : ∀ x y, eqv (x + y) (y + x)

end pi_tensor_product

variables (R) (s)

/-- `pi_tensor_product R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor
  product of all the `s i`'s. This is denoted by `⨂[R] i, s i`. -/
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

/-- `tprod_coef R r f` with `r : R` and `f : Π i, s i` is the tensor product of the vectors `f i`
over all `i : ι`, multiplied by the coefficient `r`. -/
def tprod_coef (r : R) (f : Π i, s i) : ⨂[R] i, s i := add_con.mk' _ $ free_add_monoid.of (r, f)

/-- `tprod R f` with `f : Π i, s i` is the tensor product of the vectors `f i` over all `i : ι`. -/
def tprod (f : Π i, s i) : ⨂[R] i, s i := tprod_coef R 1 f

variables {R}

notation `⨂ₜ[`:100 R`] ` binders `, ` r:(scoped:67 f, tprod R f) := r

lemma zero_tprod_coef (f : Π i, s i) : tprod_coef R 0 f = 0 :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero_scalar _

lemma zero_tprod_coef' (z : R) (f : Π i, s i) (i : ι) (hf: f i = 0) : tprod_coef R z f = 0 :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero _ _ i hf

lemma zero_tprod (f : Π i, s i) (i : ι) (hf: f i = 0) : tprod R f = 0 :=
zero_tprod_coef' 1 f i hf

@[simp] lemma zero_tprod' (f : Π i, s i) (i : ι) : tprod R (update f i 0) = 0 :=
zero_tprod _ i (update_same i 0 f)

lemma add_tprod_coef (z : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i) :
  tprod_coef R z (update f i m₁) + tprod_coef R z (update f i m₂) =
    tprod_coef R z (update f i (m₁ + m₂)) :=
quotient.sound' $ add_con_gen.rel.of _ _ (eqv.of_add z f i m₁ m₂)

lemma add_tprod_coef' (z₁ z₂ : R) (f : Π i, s i) :
  tprod_coef R z₁ f + tprod_coef R z₂ f = tprod_coef R (z₁ + z₂) f :=
quotient.sound' $ add_con_gen.rel.of _ _ (eqv.of_add_scalar z₁ z₂ f)

lemma add_tprod (f : Π i, s i) (i : ι) (m₁ m₂ : s i) :
  (⨂ₜ[R] j, (update f i m₁) j) + (⨂ₜ[R] j, (update f i m₂) j) = ⨂ₜ[R] j, (update f i (m₁ + m₂)) j :=
add_tprod_coef 1 f i m₁ m₂

lemma smul_tprod_coef (z : R) (f : Π i, s i) (i : ι) (r : R) :
  tprod_coef R z (update f i (r • f i)) = tprod_coef R (r * z) f :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_smul _ _ _ _

lemma smul_tprod_index (f : Π i, s i) (i j : ι) (r : R) :
  tprod R (update f i (r • f i)) = tprod R (update f j (r • f j)) :=
by simp_rw [tprod, smul_tprod_coef]

/-- Auxiliary function for defining scalar multiplication on the tensor product. -/
def smul.aux (r : R) : free_add_monoid (R × Π i, s i) →+ ⨂[R] i, s i :=
free_add_monoid.lift $ λ (f : R × Π i, s i), tprod_coef R (r * f.1) f.2

theorem smul.aux_of (r : R) (f : R × Π i, s i) :
  smul.aux r (free_add_monoid.of f) = tprod_coef R (r * f.1) f.2 := rfl

instance : has_scalar R (⨂[R] i, s i) :=
⟨λ r, (add_con_gen (pi_tensor_product.eqv R s)).lift (smul.aux r) $ add_con.add_con_gen_le $
λ x y hxy, match x, y, hxy with
| _, _, (eqv.of_zero r' f i hf)        := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, smul.aux_of, zero_tprod_coef' _ _ _ hf]
| _, _, (eqv.of_zero_scalar f)        := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, smul.aux_of, mul_zero, zero_tprod_coef]
| _, _, (eqv.of_add z f i m₁ m₂)      := (add_con.ker_rel _).2 $
    by simp [smul.aux_of, add_tprod_coef]
| _, _, (eqv.of_add_scalar z₁ z₂ f)      := (add_con.ker_rel _).2 $
    by simp [smul.aux_of, add_tprod_coef', mul_add]
| _, _, (eqv.of_smul z f i r')     := (add_con.ker_rel _).2 $
    by { have : r' * (r * z) = r * (r' * z) := by ring,
         simp [smul.aux_of, smul_tprod_coef, this] }
| _, _, (eqv.add_comm x y)         := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, add_comm]
end⟩

lemma smul_tprod_coef' (r z : R) (f : Π i, s i) :
  r • (tprod_coef R z f) = tprod_coef R (r • z) f := rfl

lemma smul_tprod (r : R) (f : Π i, s i) (i : ι) :
  r • (tprod R f) = tprod R (update f i (r • f i)) :=
by simp [tprod, smul_tprod_coef' r 1 f, smul_tprod_coef]

lemma smul_tprod' (r : R) (f : Π i, s i) (i : ι) (m : s i) :
  r • tprod R (update f i m) = tprod R (update f i (r • m)) :=
begin
  set g := update f i m with hg,
  have h₁ : update f i (r • m) = update g i (r • m) := by simp_rw [hg, update_idem],
  have h₂ : g i = m := by simp [hg],
  rw [h₁, smul_tprod r _ i, h₂],
end

lemma tprod_coef_eq_smul_tprod (z : R) (f : Π i, s i) : tprod_coef R z f = z • tprod R f :=
begin
  have : z = z • (1 : R) := by rw [smul_eq_mul, mul_one],
  conv_lhs { rw [this] },
  rw [←smul_tprod_coef', ←tprod],
end

protected theorem smul_zero (r : R) : (r • 0 : ⨂[R] i, s i) = 0 :=
add_monoid_hom.map_zero _

protected theorem smul_add (r : R) (x y : ⨂[R] i, s i) :
  r • (x + y) = r • x + r • y :=
add_monoid_hom.map_add _ _ _

@[elab_as_eliminator]
protected theorem induction_on
  {C : (⨂[R] i, s i) → Prop}
  (z : ⨂[R] i, s i)
  (C1 : ∀ {r : R} {f : Π i, s i}, C (r • (tprod R f)))
  (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
begin
  have C0 : C 0,
  { have h₁ := @C1 0 0,
    rwa [tprod, smul_tprod_coef', zero_smul, zero_tprod_coef] at h₁ },
  refine add_con.induction_on z (λ x, free_add_monoid.rec_on x C0 _),
  simp_rw add_con.coe_add,
  refine λ f y ih, Cp _ ih,
  simp_rw [tprod, smul_tprod_coef', smul_eq_mul, mul_one] at C1,
  convert @C1 f.1 f.2,
  simp only [prod.mk.eta],
end

@[elab_as_eliminator]
protected theorem induction_on'
  {C : (⨂[R] i, s i) → Prop}
  (z : ⨂[R] i, s i)
  (C1 : ∀ {r : R} {f : Π i, s i}, C (tprod_coef R r f))
  (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
begin
  have C0 : C 0,
  { have h₁ := @C1 0 0,
    rwa [zero_tprod_coef] at h₁ },
  refine add_con.induction_on z (λ x, free_add_monoid.rec_on x C0 _),
  simp_rw add_con.coe_add,
  refine λ f y ih, Cp _ ih,
  convert @C1 f.1 f.2,
  simp only [prod.mk.eta],
end

instance : semimodule R (⨂[R] i, s i) :=
{ smul := (•),
  smul_add := λ r x y, pi_tensor_product.smul_add r x y,
  mul_smul := λ r r' x,
    begin
      refine pi_tensor_product.induction_on' x _ _,
      { intros r'' f,
        simp [smul_tprod_coef', mul_assoc] },
      { intros x y ihx ihy,
        simp_rw [pi_tensor_product.smul_add],
        rw [ihx, ihy] }
    end,
  one_smul := λ x, pi_tensor_product.induction_on' x
    (λ f, by simp [smul_tprod_coef' _ _])
    (λ z y ihz ihy, by simp_rw [pi_tensor_product.smul_add, ihz, ihy]),
  add_smul := λ r r' x,
    begin
      refine pi_tensor_product.induction_on' x _ _,
      { intros r f,
        simp_rw [smul_tprod_coef' _ _, add_smul, add_tprod_coef'] },
      { intros x y ihx ihy,
        simp_rw pi_tensor_product.smul_add,
        rw [ihx, ihy, add_add_add_comm] }
    end,
  smul_zero := λ r, pi_tensor_product.smul_zero r,
  zero_smul := λ x,
    begin
      refine pi_tensor_product.induction_on' x _ _,
      { intros r f,
        rw [smul_tprod_coef' _ _, zero_smul],
        exact zero_tprod_coef _ },
      { intros x y ihx ihy,
        rw [pi_tensor_product.smul_add, ihx, ihy, add_zero] },
    end }

variables (R) (s)
/-- The canonical `multilinear_map R s (⨂[R] i, s i)`. -/
def mk : multilinear_map R s (⨂[R] i, s i) :=
{ to_fun := tprod R,
  map_add' := λ f i x y, by rw add_tprod,
  map_smul' := λ f i r x, by simp [smul_tprod _ _ i] }
variables {R} {s}

@[simp] lemma mk_apply (f : Π i, s i) : mk R s f = tprod R f := rfl

section sum
open_locale big_operators

lemma tprod.map_sum {α : Type*} (t : finset α) (i : ι) (m : α → s i) (f : Π i, s i):
  tprod R (update f i (∑ a in t, m a)) = ∑ a in t, tprod R (update f i (m a)) :=
begin
  induction t using finset.induction with a t has ih h,
  { simp },
  { simp [finset.sum_insert has, ←add_tprod, ih] }
end

end sum

end module

section multilinear
open multilinear_map
variables {s}

/-- Auxiliary function to constructing a linear map `(⨂[R] i, s i) → E` given a
`multilinear map R s E` with the property that its composition with the canonical
`multilinear_map R s (⨂[R] i, s i)` is the given multilinear map. -/
def lift_aux (φ : multilinear_map R s E) : (⨂[R] i, s i) →+ E :=
(add_con_gen (pi_tensor_product.eqv R s)).lift
  (free_add_monoid.lift $ λ (p : R × Π i, s i), p.1 • (φ p.2)) $
  add_con.add_con_gen_le $ λ x y hxy, match x, y, hxy with
| _, _, (eqv.of_zero z f i hf)       := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, free_add_monoid.lift_eval_of,
                map_coord_zero φ i hf, smul_zero]
| _, _, (eqv.of_zero_scalar f)       := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, free_add_monoid.lift_eval_of, zero_smul]
| _, _, (eqv.of_add z f i m₁ m₂)  := (add_con.ker_rel _).2 $
    by { simp_rw [add_monoid_hom.map_add, free_add_monoid.lift_eval_of, ←smul_add],
         congr,
         simp_rw [φ.map_add] }
| _, _, (eqv.of_add_scalar z₁ z₂ f)  := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, free_add_monoid.lift_eval_of, ←add_smul]
| _, _, (eqv.of_smul z f i r)        := (add_con.ker_rel _).2 $
    by simp [free_add_monoid.lift_eval_of, φ.map_smul, smul_smul, mul_comm]
| _, _, (eqv.add_comm x y)         := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, add_comm]
end

lemma lift_aux_tprod (φ : multilinear_map R s E) (f : Π i, s i) : lift_aux φ (tprod R f) = φ f :=
by simp only [lift_aux, tprod, tprod_coef, free_add_monoid.lift_eval_of, one_smul, add_con.lift_mk']

lemma lift_aux_tprod_coef (φ : multilinear_map R s E) (z : R) (f : Π i, s i) :
  lift_aux φ (tprod_coef R z f) = z • φ f :=
by simp [lift_aux, tprod_coef, free_add_monoid.lift_eval_of]

lemma lift_aux.smul {φ : multilinear_map R s E} (r : R) (x : ⨂[R] i, s i) :
  lift_aux φ (r • x) = r • lift_aux φ x :=
begin
  refine pi_tensor_product.induction_on' x _ _,
  { intros z f,
    simp [smul_tprod_coef' r z f, lift_aux_tprod_coef, lift_aux_tprod_coef, smul_smul] },
  { intros z y ihz ihy,
    rw [smul_add, (lift_aux φ).map_add, ihz, ihy, (lift_aux φ).map_add, smul_add] }
end

/-- Constructing a linear map `(⨂[R] i, s i) → E` given a `multilinear_map R s E` with the
property that its composition with the canonical `multilinear_map R s E` is
the given multilinear map `φ`. -/
def lift (φ : multilinear_map R s E) : (⨂[R] i, s i) →ₗ[R] E :=
{ map_smul' := lift_aux.smul,
  .. lift_aux φ }

variables {φ : multilinear_map R s E}

@[simp] lemma lift.tprod (f : Π i, s i) : lift φ (tprod R f) = φ f := lift_aux_tprod φ f

@[simp] lemma lift.tprod' (f : Π i, s i) : (lift φ).1 (tprod R f) = φ f := lift.tprod _

@[ext]
theorem ext {φ₁ φ₂ : (⨂[R] i, s i) →ₗ[R] E} (H : ∀ f, φ₁ (tprod R f) = φ₂ (tprod R f)) : φ₁ = φ₂ :=
begin
  refine linear_map.ext _,
  refine λ z,
    (pi_tensor_product.induction_on' z _ (λ x y hx hy, by rw [φ₁.map_add, φ₂.map_add, hx, hy])),
  { intros r f,
    rw [tprod_coef_eq_smul_tprod, φ₁.map_smul, φ₂.map_smul],
    apply _root_.congr_arg,
    exact H f }
end

theorem lift.unique {φ' : (⨂[R] i, s i) →ₗ[R] E} (H : ∀ f, φ' (tprod R f) = φ f) :
  φ' = lift φ :=
ext $ λ f, by rw [H, lift.tprod]

theorem lift_mk : lift (mk R s) = linear_map.id :=
eq.symm $ lift.unique $ λ _, rfl

end multilinear

end pi_tensor_product

end semiring

section ring
namespace pi_tensor_product

open pi_tensor_product
open_locale tensor_product

variables {ι : Type*} {R : Type*} [comm_ring R]
variables {s : ι → Type*} [∀ i, add_comm_group (s i)] [∀ i, module R (s i)]
variables {E : Type*} [add_comm_group E] [semimodule R E]

instance : add_comm_group (⨂[R] i, s i) := semimodule.add_comm_monoid_to_add_comm_group R

lemma neg_tprod_coef (z : R) (f : Π i, s i) : tprod_coef R (-z) f = -tprod_coef R z f :=
by rw [←neg_one_smul R, ←smul_tprod_coef', neg_one_smul R]

lemma neg_tprod (f : Π i, s i) (i : ι) : tprod R (update f i (-(f i))) = -tprod R f :=
by rw [←neg_one_smul R, ←smul_tprod, neg_one_smul R]

lemma neg_tprod' (f : Π i, s i) (i : ι) (m : s i) :
  tprod R (update f i (-m)) = -tprod R (update f i m) :=
by rw [←neg_one_smul R, ←smul_tprod', neg_one_smul R]

lemma sub_tprod (f : Π i, s i) (i : ι) (m₁ m₂ : s i) :
   tprod R (update f i m₁) - tprod R (update f i m₂) = tprod R (update f i (m₁ - m₂)) :=
by rw [sub_eq_add_neg, ←neg_tprod' f i _, add_tprod f i m₁ (-m₂), sub_eq_add_neg]

end pi_tensor_product
end ring
