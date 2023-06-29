/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.equiv

/-!
# The R-algebra structure on families of R-algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

## Main defintions

* `pi.algebra`
* `pi.eval_alg_hom`
* `pi.const_alg_hom`
-/
universes u v w

namespace pi

variable {I : Type u}     -- The indexing type
variable {R : Type*}      -- The scalar type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)
variables (I f)

instance algebra {r : comm_semiring R}
  [s : ∀ i, semiring (f i)] [∀ i, algebra R (f i)] :
  algebra R (Π i : I, f i) :=
{ commutes' := λ a f, begin ext, simp [algebra.commutes], end,
  smul_def' := λ a f, begin ext, simp [algebra.smul_def], end,
  ..(pi.ring_hom (λ i, algebra_map R (f i)) : R →+* Π i : I, f i) }

lemma algebra_map_def {r : comm_semiring R}
  [s : ∀ i, semiring (f i)] [∀ i, algebra R (f i)] (a : R) :
  algebra_map R (Π i, f i) a = (λ i, algebra_map R (f i) a) := rfl

@[simp] lemma algebra_map_apply {r : comm_semiring R}
  [s : ∀ i, semiring (f i)] [∀ i, algebra R (f i)] (a : R) (i : I) :
  algebra_map R (Π i, f i) a i = algebra_map R (f i) a := rfl

-- One could also build a `Π i, R i`-algebra structure on `Π i, A i`,
-- when each `A i` is an `R i`-algebra, although I'm not sure that it's useful.

variables {I} (R) (f)

/-- `function.eval` as an `alg_hom`. The name matches `pi.eval_ring_hom`, `pi.eval_monoid_hom`,
etc. -/
@[simps]
def eval_alg_hom {r : comm_semiring R} [Π i, semiring (f i)] [Π i, algebra R (f i)] (i : I) :
  (Π i, f i) →ₐ[R] f i :=
{ to_fun := λ f, f i, commutes' := λ r, rfl, .. pi.eval_ring_hom f i}

variables (A B : Type*) [comm_semiring R] [semiring B] [algebra R B]

/-- `function.const` as an `alg_hom`. The name matches `pi.const_ring_hom`, `pi.const_monoid_hom`,
etc. -/
@[simps]
def const_alg_hom : B →ₐ[R] (A → B) :=
{ to_fun := function.const _,
  commutes' := λ r, rfl,
  .. pi.const_ring_hom A B}

/-- When `R` is commutative and permits an `algebra_map`, `pi.const_ring_hom` is equal to that
map. -/
@[simp] lemma const_ring_hom_eq_algebra_map : const_ring_hom A R = algebra_map R (A → R) :=
rfl

@[simp] lemma const_alg_hom_eq_algebra_of_id : const_alg_hom R A R = algebra.of_id R (A → R) :=
rfl

end pi

/-- A special case of `pi.algebra` for non-dependent types. Lean struggles to elaborate
definitions elsewhere in the library without this, -/
instance function.algebra {R : Type*} (I : Type*)  (A : Type*) [comm_semiring R]
  [semiring A] [algebra R A] : algebra R (I → A) :=
pi.algebra _ _

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w} {I : Type*}

variables [comm_semiring R] [semiring A] [semiring B]
variables [algebra R A] [algebra R B]

/-- `R`-algebra homomorphism between the function spaces `I → A` and `I → B`, induced by an
`R`-algebra homomorphism `f` between `A` and `B`. -/
@[simps] protected def comp_left (f : A →ₐ[R] B) (I : Type*) : (I → A) →ₐ[R] (I → B) :=
{ to_fun := λ h, f ∘ h,
  commutes' := λ c, by { ext, exact f.commutes' c },
  .. f.to_ring_hom.comp_left I }

end alg_hom

namespace alg_equiv

/-- A family of algebra equivalences `Π j, (A₁ j ≃ₐ A₂ j)` generates a
multiplicative equivalence between `Π j, A₁ j` and `Π j, A₂ j`.

This is the `alg_equiv` version of `equiv.Pi_congr_right`, and the dependent version of
`alg_equiv.arrow_congr`.
-/
@[simps apply]
def Pi_congr_right {R ι : Type*} {A₁ A₂ : ι → Type*} [comm_semiring R]
  [Π i, semiring (A₁ i)] [Π i, semiring (A₂ i)] [Π i, algebra R (A₁ i)] [Π i, algebra R (A₂ i)]
  (e : Π i, A₁ i ≃ₐ[R] A₂ i) : (Π i, A₁ i) ≃ₐ[R] Π i, A₂ i :=
{ to_fun := λ x j, e j (x j),
  inv_fun := λ x j, (e j).symm (x j),
  commutes' := λ r, by { ext i, simp },
  .. @ring_equiv.Pi_congr_right ι A₁ A₂ _ _ (λ i, (e i).to_ring_equiv) }

@[simp]
lemma Pi_congr_right_refl {R ι : Type*} {A : ι → Type*} [comm_semiring R]
  [Π i, semiring (A i)] [Π i, algebra R (A i)] :
  Pi_congr_right (λ i, (alg_equiv.refl : A i ≃ₐ[R] A i)) = alg_equiv.refl := rfl

@[simp]
lemma Pi_congr_right_symm {R ι : Type*} {A₁ A₂ : ι → Type*} [comm_semiring R]
  [Π i, semiring (A₁ i)] [Π i, semiring (A₂ i)] [Π i, algebra R (A₁ i)] [Π i, algebra R (A₂ i)]
  (e : Π i, A₁ i ≃ₐ[R] A₂ i) : (Pi_congr_right e).symm = (Pi_congr_right $ λ i, (e i).symm) := rfl

@[simp]
lemma Pi_congr_right_trans {R ι : Type*} {A₁ A₂ A₃ : ι → Type*} [comm_semiring R]
  [Π i, semiring (A₁ i)] [Π i, semiring (A₂ i)] [Π i, semiring (A₃ i)]
  [Π i, algebra R (A₁ i)] [Π i, algebra R (A₂ i)] [Π i, algebra R (A₃ i)]
  (e₁ : Π i, A₁ i ≃ₐ[R] A₂ i) (e₂ : Π i, A₂ i ≃ₐ[R] A₃ i) :
  (Pi_congr_right e₁).trans (Pi_congr_right e₂) = (Pi_congr_right $ λ i, (e₁ i).trans (e₂ i)) :=
rfl

end alg_equiv
