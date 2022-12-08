/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.hom

/-!
The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

We couldn't set this up back in `algebra.pi_instances` because this file imports it.
-/
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
