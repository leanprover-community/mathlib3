/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Group action on rings.
-/

import group_theory.group_action
import data.equiv.ring
import data.polynomial.monic

universes u v
open_locale big_operators

section prio
set_option default_priority 100 -- see Note [default priority]

/-- Typeclass for multiplicative actions by monoids on semirings. -/
class mul_semiring_action (M : Type u) [monoid M] (R : Type v) [semiring R]
  extends distrib_mul_action M R :=
(smul_one : ∀ (g : M), (g • 1 : R) = 1)
(smul_mul : ∀ (g : M) (x y : R), g • (x * y) = (g • x) * (g • y))

end prio

export mul_semiring_action (smul_one)

section semiring

variables (M G : Type u) [monoid M] [group G]
variables (A R S F : Type v) [add_monoid A] [semiring R] [comm_semiring S] [field F]

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

section prod
variables [mul_semiring_action M R] [mul_semiring_action M S]

lemma list.smul_prod (g : M) (L : list R) : g • L.prod = (L.map $ (•) g).prod :=
monoid_hom.map_list_prod (mul_semiring_action.to_semiring_hom M R g : R →* R) L

lemma multiset.smul_prod (g : M) (m : multiset S) : g • m.prod = (m.map $ (•) g).prod :=
monoid_hom.map_multiset_prod (mul_semiring_action.to_semiring_hom M S g : S →* S) m

lemma smul_prod (g : M) {ι : Type*} (f : ι → S) (s : finset ι) :
  g • ∏ i in s, f i = ∏ i in s, g • f i :=
monoid_hom.map_prod (mul_semiring_action.to_semiring_hom M S g : S →* S) f s

end prod

section simp_lemmas

variables {M G A R}

attribute [simp] smul_one smul_mul' smul_zero smul_add

@[simp] lemma smul_inv [mul_semiring_action M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ :=
(mul_semiring_action.to_semiring_hom M F x).map_inv _

@[simp] lemma smul_pow [mul_semiring_action M R] (x : M) (m : R) (n : ℕ) :
  x • m ^ n = (x • m) ^ n :=
nat.rec_on n (smul_one x) $ λ n ih, (smul_mul' x m (m ^ n)).trans $ congr_arg _ ih

end simp_lemmas

namespace polynomial

variables [mul_semiring_action M S]

noncomputable instance : mul_semiring_action M (polynomial S) :=
{ smul := λ m, map $ mul_semiring_action.to_semiring_hom M S m,
  one_smul := λ p, by { ext n, erw coeff_map, exact one_smul M (p.coeff n) },
  mul_smul := λ m n p, by { ext i,
    iterate 3 { rw coeff_map (mul_semiring_action.to_semiring_hom M S _) },
    exact mul_smul m n (p.coeff i) },
  smul_add := λ m p q, map_add (mul_semiring_action.to_semiring_hom M S m),
  smul_zero := λ m, map_zero (mul_semiring_action.to_semiring_hom M S m),
  smul_one := λ m, map_one (mul_semiring_action.to_semiring_hom M S m),
  smul_mul := λ m p q, map_mul (mul_semiring_action.to_semiring_hom M S m), }

@[simp] lemma coeff_smul' (m : M) (p : polynomial S) (n : ℕ) :
  (m • p).coeff n = m • p.coeff n :=
coeff_map _ _

@[simp] lemma smul_C (m : M) (r : S) : m • C r = C (m • r) :=
map_C _

@[simp] lemma smul_X (m : M) : (m • X : polynomial S) = X :=
map_X _

theorem smul_eval_smul (m : M) (f : polynomial S) (x : S) :
  (m • f).eval (m • x) = m • f.eval x :=
polynomial.induction_on f
  (λ r, by rw [smul_C, eval_C, eval_C])
  (λ f g ihf ihg, by rw [smul_add, eval_add, ihf, ihg, eval_add, smul_add])
  (λ n r ih, by rw [smul_mul', smul_pow, smul_C, smul_X, eval_mul, eval_C, eval_pow, eval_X,
      eval_mul, eval_C, eval_pow, eval_X, smul_mul', smul_pow])

theorem eval_smul' [mul_semiring_action G S] (g : G) (f : polynomial S) (x : S) :
  f.eval (g • x) = g • (g⁻¹ • f).eval x :=
by rw [← smul_eval_smul, mul_action.smul_inv_smul]

theorem smul_eval [mul_semiring_action G S] (g : G) (f : polynomial S) (x : S) :
  (g • f).eval x = g • f.eval (g⁻¹ • x) :=
by rw [← smul_eval_smul, mul_action.smul_inv_smul]

end polynomial

end semiring

section ring

variables (M : Type u) [monoid M] {R : Type v} [ring R] [mul_semiring_action M R]
variables (S : set R) [is_subring S]
open mul_action

set_option old_structure_cmd false

/-- A subring invariant under the action. -/
class is_invariant_subring : Prop :=
(smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S)

variables [is_invariant_subring M S]

instance is_invariant_subring.to_mul_semiring_action : mul_semiring_action M S :=
{ smul := λ m x, ⟨m • x, is_invariant_subring.smul_mem m x.2⟩,
  one_smul := λ s, subtype.eq $ one_smul M s,
  mul_smul := λ m₁ m₂ s, subtype.eq $ mul_smul m₁ m₂ s,
  smul_add := λ m s₁ s₂, subtype.eq $ smul_add m s₁ s₂,
  smul_zero := λ m, subtype.eq $ smul_zero m,
  smul_one := λ m, subtype.eq $ smul_one m,
  smul_mul := λ m s₁ s₂, subtype.eq $ smul_mul' m s₁ s₂ }

instance fixed_points.is_invariant_subring : is_invariant_subring M (fixed_points M R) :=
{ smul_mem := λ g x hx g', by rw [hx, hx] }

end ring

section comm_ring

variables (G : Type u) [group G] [fintype G]
variables (R : Type v) [comm_ring R] [mul_semiring_action G R]
open mul_action
open_locale classical

noncomputable instance (s : set G) [is_subgroup s] : fintype (quotient_group.quotient s) :=
quotient.fintype _

/-- the product of `(X - g • x)` over distinct `g • x`. -/
noncomputable def prod_X_sub_smul (x : R) : polynomial R :=
(finset.univ : finset (quotient_group.quotient $ mul_action.stabilizer G x)).prod $
λ g, polynomial.X - polynomial.C (of_quotient_stabilizer G x g)

theorem prod_X_sub_smul.monic (x : R) : (prod_X_sub_smul G R x).monic :=
polynomial.monic_prod_of_monic _ _ $ λ g _, polynomial.monic_X_sub_C _

theorem prod_X_sub_smul.eval (x : R) : (prod_X_sub_smul G R x).eval x = 0 :=
(finset.prod_hom _ (polynomial.eval x)).symm.trans $ finset.prod_eq_zero (finset.mem_univ $ quotient_group.mk 1) $
by rw [of_quotient_stabilizer_mk, one_smul, polynomial.eval_sub, polynomial.eval_X, polynomial.eval_C, sub_self]

theorem prod_X_sub_smul.smul (x : R) (g : G) :
  g • prod_X_sub_smul G R x = prod_X_sub_smul G R x :=
(smul_prod _ _ _ _ _).trans $ finset.prod_bij (λ g' _, g • g') (λ _ _, finset.mem_univ _)
  (λ g' _, by rw [of_quotient_stabilizer_smul, smul_sub, polynomial.smul_X, polynomial.smul_C])
  (λ _ _ _ _ H, (mul_action.bijective g).1 H)
  (λ g' _, ⟨g⁻¹ • g', finset.mem_univ _, by rw [smul_smul, mul_inv_self, one_smul]⟩)

theorem prod_X_sub_smul.coeff (x : R) (g : G) (n : ℕ) :
  g • (prod_X_sub_smul G R x).coeff n =
  (prod_X_sub_smul G R x).coeff n :=
by rw [← polynomial.coeff_smul', prod_X_sub_smul.smul]

end comm_ring
