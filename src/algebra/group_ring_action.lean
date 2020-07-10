/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Group action on rings.
-/

import group_theory.group_action
import data.equiv.ring
import data.polynomial

universes u v

variables (M G : Type u) [monoid M] [group G]
variables (A R S F : Type v) [add_monoid A] [semiring R] [comm_semiring S] [field F]

section prio
set_option default_priority 100 -- see Note [default priority]

/-- Typeclass for multiplicative actions by monoids on semirings. -/
class mul_semiring_action extends distrib_mul_action M R :=
(smul_one : ∀ (g : M), (g • 1 : R) = 1)
(smul_mul : ∀ (g : M) (x y : R), g • (x * y) = (g • x) * (g • y))

end prio

export mul_semiring_action (smul_one)

variables {M R}
lemma smul_mul' [mul_semiring_action M R] (g : M) (x y : R) :
  g • (x * y) = (g • x) * (g • y) :=
mul_semiring_action.smul_mul g x y
variables (M R)

/-- Each element of the monoid defines a additive monoid homomorphism. -/
def distrib_mul_action.to_add_monoid_hom [distrib_mul_action M A] (x : M) : A →+ A :=
{ to_fun   := (•) x,
  map_zero' := smul_zero x,
  map_add' := smul_add x }

/-- Each element of the group defines an additive monoid isomorphism. -/
def distrib_mul_action.to_add_equiv [distrib_mul_action G A] (x : G) : A ≃+ A :=
{ .. distrib_mul_action.to_add_monoid_hom G A x,
  .. mul_action.to_perm G A x }

/-- The monoid of endomorphisms. -/
def monoid.End := M →* M

instance monoid.End.monoid : monoid (monoid.End M) :=
{ mul := monoid_hom.comp,
  one := monoid_hom.id M,
  mul_assoc := λ _ _ _, monoid_hom.comp_assoc _ _ _,
  mul_one := monoid_hom.comp_id,
  one_mul := monoid_hom.id_comp }

instance monoid.End.inhabited : inhabited (monoid.End M) :=
⟨1⟩

/-- The monoid of endomorphisms. -/
def add_monoid.End := A →+ A

instance add_monoid.End.monoid : monoid (add_monoid.End A) :=
{ mul := add_monoid_hom.comp,
  one := add_monoid_hom.id A,
  mul_assoc := λ _ _ _, add_monoid_hom.comp_assoc _ _ _,
  mul_one := add_monoid_hom.comp_id,
  one_mul := add_monoid_hom.id_comp }

instance add_monoid.End.inhabited : inhabited (add_monoid.End A) :=
⟨1⟩

/-- Each element of the group defines an additive monoid homomorphism. -/
def distrib_mul_action.hom_add_monoid_hom [distrib_mul_action M A] : M →* add_monoid.End A :=
{ to_fun := distrib_mul_action.to_add_monoid_hom M A,
  map_one' := add_monoid_hom.ext $ λ x, one_smul M x,
  map_mul' := λ x y, add_monoid_hom.ext $ λ z, mul_smul x y z }

/-- Each element of the monoid defines a semiring homomorphism. -/
def mul_semiring_action.to_semiring_hom [mul_semiring_action M R] (x : M) : R →+* R :=
{ map_one' := smul_one x,
  map_mul' := smul_mul' x,
  .. distrib_mul_action.to_add_monoid_hom M R x }

/-- Each element of the group defines a semiring isomorphism. -/
def mul_semiring_action.to_semiring_equiv [mul_semiring_action G R] (x : G) : R ≃+* R :=
{ .. distrib_mul_action.to_add_equiv G R x,
  .. mul_semiring_action.to_semiring_hom G R x }

section simp_lemmas

variables {M G A R}

attribute [simp] smul_one smul_mul' smul_zero smul_add

@[simp] lemma smul_inv [mul_semiring_action M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ :=
(mul_semiring_action.to_semiring_hom M F x).map_inv _

@[simp] lemma smul_pow [mul_semiring_action M R] (x : M) (m : R) (n : ℕ) :
  x • m ^ n = (x • m) ^ n :=
nat.rec_on n (smul_one x) $ λ n ih, (smul_mul' x m (m ^ n)).trans $ congr_arg _ ih

end simp_lemmas

variables [mul_semiring_action M S]

noncomputable instance : mul_semiring_action M (polynomial S) :=
{ smul := λ m, polynomial.map $ mul_semiring_action.to_semiring_hom M S m,
  one_smul := λ p, by { ext n, erw polynomial.coeff_map, exact one_smul M (p.coeff n) },
  mul_smul := λ m n p, by { ext i,
    iterate 3 { rw polynomial.coeff_map (mul_semiring_action.to_semiring_hom M S _) },
    exact mul_smul m n (p.coeff i) },
  smul_add := λ m p q, polynomial.map_add (mul_semiring_action.to_semiring_hom M S m),
  smul_zero := λ m, polynomial.map_zero (mul_semiring_action.to_semiring_hom M S m),
  smul_one := λ m, polynomial.map_one (mul_semiring_action.to_semiring_hom M S m),
  smul_mul := λ m p q, polynomial.map_mul (mul_semiring_action.to_semiring_hom M S m), }

@[simp] lemma polynomial.coeff_smul' (m : M) (p : polynomial S) (n : ℕ) :
  (m • p).coeff n = m • p.coeff n :=
polynomial.coeff_map _ _

@[simp] lemma polynomial.smul_C (m : M) (r : S) : m • polynomial.C r = polynomial.C (m • r) :=
polynomial.map_C _

@[simp] lemma polynomial.smul_X (m : M) : (m • polynomial.X : polynomial S) = polynomial.X :=
polynomial.map_X _
