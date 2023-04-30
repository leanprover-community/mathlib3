/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.basic

/-!
# Homomorphisms of `R`-algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines bundled homomorphisms of `R`-algebras.

## Main definitions

* `alg_hom R A B`: the type of `R`-algebra morphisms from `A` to `B`.
* `algebra.of_id R A : R →ₐ[R] A`: the canonical map from `R` to `A`, as an `alg_hom`.

## Notations

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
-/

open_locale big_operators

universes u v w u₁ v₁

set_option old_structure_cmd true
/-- Defining the homomorphism in the category R-Alg. -/
@[nolint has_nonempty_instance]
structure alg_hom (R : Type u) (A : Type v) (B : Type w)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] extends ring_hom A B :=
(commutes' : ∀ r : R, to_fun (algebra_map R A r) = algebra_map R B r)

run_cmd tactic.add_doc_string `alg_hom.to_ring_hom "Reinterpret an `alg_hom` as a `ring_hom`"

infixr ` →ₐ `:25 := alg_hom _
notation A ` →ₐ[`:25 R `] ` B := alg_hom R A B

/-- `alg_hom_class F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`.  -/
class alg_hom_class (F : Type*) (R : out_param Type*) (A : out_param Type*) (B : out_param Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  extends ring_hom_class F A B :=
(commutes : ∀ (f : F) (r : R), f (algebra_map R A r) = algebra_map R B r)

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] alg_hom_class.to_ring_hom_class

attribute [simp] alg_hom_class.commutes

namespace alg_hom_class

variables {R : Type*} {A : Type*} {B : Type*} [comm_semiring R] [semiring A] [semiring B]
  [algebra R A] [algebra R B]

@[priority 100] -- see Note [lower instance priority]
instance {F : Type*} [alg_hom_class F R A B] : linear_map_class F R A B :=
{ map_smulₛₗ := λ f r x, by simp only [algebra.smul_def, map_mul, commutes, ring_hom.id_apply],
  ..‹alg_hom_class F R A B› }

instance {F : Type*} [alg_hom_class F R A B] : has_coe_t F (A →ₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
    commutes' := alg_hom_class.commutes f,
    .. (f : A →+* B) } }

end alg_hom_class

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section semiring

variables [comm_semiring R] [semiring A] [semiring B] [semiring C] [semiring D]
variables [algebra R A] [algebra R B] [algebra R C] [algebra R D]

instance : has_coe_to_fun (A →ₐ[R] B) (λ _, A → B) := ⟨alg_hom.to_fun⟩

initialize_simps_projections alg_hom (to_fun → apply)

@[simp, protected] lemma coe_coe {F : Type*} [alg_hom_class F R A B] (f : F) :
  ⇑(f : A →ₐ[R] B) = f := rfl

@[simp] lemma to_fun_eq_coe (f : A →ₐ[R] B) : f.to_fun = f := rfl

instance : alg_hom_class (A →ₐ[R] B) R A B :=
{ coe := to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' },
  map_add := map_add',
  map_zero := map_zero',
  map_mul := map_mul',
  map_one := map_one',
  commutes := λ f, f.commutes' }

instance coe_ring_hom : has_coe (A →ₐ[R] B) (A →+* B) := ⟨alg_hom.to_ring_hom⟩

instance coe_monoid_hom : has_coe (A →ₐ[R] B) (A →* B) := ⟨λ f, ↑(f : A →+* B)⟩

instance coe_add_monoid_hom : has_coe (A →ₐ[R] B) (A →+ B) := ⟨λ f, ↑(f : A →+* B)⟩

@[simp, norm_cast] lemma coe_mk {f : A → B} (h₁ h₂ h₃ h₄ h₅) :
  ⇑(⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f := rfl

-- make the coercion the simp-normal form
@[simp] lemma to_ring_hom_eq_coe (f : A →ₐ[R] B) : f.to_ring_hom = f := rfl

@[simp, norm_cast] lemma coe_to_ring_hom (f : A →ₐ[R] B) : ⇑(f : A →+* B) = f := rfl

@[simp, norm_cast] lemma coe_to_monoid_hom (f : A →ₐ[R] B) : ⇑(f : A →* B) = f := rfl

@[simp, norm_cast] lemma coe_to_add_monoid_hom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f := rfl

variables (φ : A →ₐ[R] B)

theorem coe_fn_injective : @function.injective (A →ₐ[R] B) (A → B) coe_fn := fun_like.coe_injective

theorem coe_fn_inj {φ₁ φ₂ : A →ₐ[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ := fun_like.coe_fn_eq

theorem coe_ring_hom_injective : function.injective (coe : (A →ₐ[R] B) → (A →+* B)) :=
λ φ₁ φ₂ H, coe_fn_injective $ show ((φ₁ : (A →+* B)) : A → B) = ((φ₂ : (A →+* B)) : A → B),
  from congr_arg _ H

theorem coe_monoid_hom_injective : function.injective (coe : (A →ₐ[R] B)  → (A →* B)) :=
ring_hom.coe_monoid_hom_injective.comp coe_ring_hom_injective

theorem coe_add_monoid_hom_injective : function.injective (coe : (A →ₐ[R] B)  → (A →+ B)) :=
ring_hom.coe_add_monoid_hom_injective.comp coe_ring_hom_injective

protected lemma congr_fun {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
fun_like.congr_fun H x
protected lemma congr_arg (φ : A →ₐ[R] B) {x y : A} (h : x = y) : φ x = φ y :=
fun_like.congr_arg φ h

@[ext]
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ := fun_like.ext _ _ H

theorem ext_iff {φ₁ φ₂ : A →ₐ[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x := fun_like.ext_iff

@[simp] theorem mk_coe {f : A →ₐ[R] B} (h₁ h₂ h₃ h₄ h₅) :
  (⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f := ext $ λ _, rfl

@[simp]
theorem commutes (r : R) : φ (algebra_map R A r) = algebra_map R B r := φ.commutes' r

theorem comp_algebra_map : (φ : A →+* B).comp (algebra_map R A) = algebra_map R B :=
ring_hom.ext $ φ.commutes

protected lemma map_add (r s : A) : φ (r + s) = φ r + φ s := map_add _ _ _
protected lemma map_zero : φ 0 = 0 := map_zero _
protected lemma map_mul (x y) : φ (x * y) = φ x * φ y := map_mul _ _ _
protected lemma map_one : φ 1 = 1 := map_one _
protected lemma map_pow (x : A) (n : ℕ) : φ (x ^ n) = (φ x) ^ n := map_pow _ _ _

@[simp] protected lemma map_smul (r : R) (x : A) : φ (r • x) = r • φ x := map_smul _ _ _

protected lemma map_sum {ι : Type*} (f : ι → A) (s : finset ι) :
  φ (∑ x in s, f x) = ∑ x in s, φ (f x) := map_sum _ _ _

protected lemma map_finsupp_sum {α : Type*} [has_zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
  φ (f.sum g) = f.sum (λ i a, φ (g i a)) := map_finsupp_sum _ _ _

protected lemma map_bit0 (x) : φ (bit0 x) = bit0 (φ x) := map_bit0 _ _
protected lemma map_bit1 (x) : φ (bit1 x) = bit1 (φ x) := map_bit1 _ _

/-- If a `ring_hom` is `R`-linear, then it is an `alg_hom`. -/
def mk' (f : A →+* B) (h : ∀ (c : R) x, f (c • x) = c • f x) : A →ₐ[R] B :=
{ to_fun := f,
  commutes' := λ c, by simp only [algebra.algebra_map_eq_smul_one, h, f.map_one],
  .. f }

@[simp] lemma coe_mk' (f : A →+* B) (h : ∀ (c : R) x, f (c • x) = c • f x) : ⇑(mk' f h) = f := rfl

section

variables (R A)
/-- Identity map as an `alg_hom`. -/
protected def id : A →ₐ[R] A :=
{ commutes' := λ _, rfl,
  ..ring_hom.id A }

@[simp] lemma coe_id : ⇑(alg_hom.id R A) = id := rfl

@[simp] lemma id_to_ring_hom : (alg_hom.id R A : A →+* A) = ring_hom.id _ := rfl

end

lemma id_apply (p : A) : alg_hom.id R A p = p := rfl

/-- Composition of algebra homeomorphisms. -/
def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
{ commutes' := λ r : R, by rw [← φ₁.commutes, ← φ₂.commutes]; refl,
  .. φ₁.to_ring_hom.comp ↑φ₂ }

@[simp] lemma coe_comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ := rfl

lemma comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) := rfl

lemma comp_to_ring_hom (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) :
  (φ₁.comp φ₂ : A →+* C) = (φ₁ : B →+* C).comp ↑φ₂ := rfl

@[simp] theorem comp_id : φ.comp (alg_hom.id R A) = φ :=
ext $ λ x, rfl

@[simp] theorem id_comp : (alg_hom.id R B).comp φ = φ :=
ext $ λ x, rfl

theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
  (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
ext $ λ x, rfl

/-- R-Alg ⥤ R-Mod -/
def to_linear_map : A →ₗ[R] B :=
{ to_fun := φ,
  map_add' := map_add _,
  map_smul' := map_smul _ }

@[simp] lemma to_linear_map_apply (p : A) : φ.to_linear_map p = φ p := rfl

theorem to_linear_map_injective : function.injective (to_linear_map : _ → (A →ₗ[R] B)) :=
λ φ₁ φ₂ h, ext $ linear_map.congr_fun h

@[simp] lemma comp_to_linear_map (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
  (g.comp f).to_linear_map = g.to_linear_map.comp f.to_linear_map := rfl

@[simp] lemma to_linear_map_id : to_linear_map (alg_hom.id R A) = linear_map.id :=
linear_map.ext $ λ _, rfl

/-- Promote a `linear_map` to an `alg_hom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
def of_linear_map (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
  A →ₐ[R] B :=
{ to_fun := f,
  map_one' := map_one,
  map_mul' := map_mul,
  commutes' := λ c, by simp only [algebra.algebra_map_eq_smul_one, f.map_smul, map_one],
  .. f.to_add_monoid_hom }

@[simp] lemma of_linear_map_to_linear_map (map_one) (map_mul) :
  of_linear_map φ.to_linear_map map_one map_mul = φ :=
by { ext, refl }

@[simp] lemma to_linear_map_of_linear_map (f : A →ₗ[R] B) (map_one) (map_mul) :
  to_linear_map (of_linear_map f map_one map_mul) = f :=
by { ext, refl }

@[simp] lemma of_linear_map_id (map_one) (map_mul) :
  of_linear_map linear_map.id map_one map_mul = alg_hom.id R A :=
ext $ λ _, rfl

lemma map_smul_of_tower {R'} [has_smul R' A] [has_smul R' B]
  [linear_map.compatible_smul A B R' R] (r : R') (x : A) : φ (r • x) = r • φ x :=
φ.to_linear_map.map_smul_of_tower r x

lemma map_list_prod (s : list A) :
  φ s.prod = (s.map φ).prod :=
φ.to_ring_hom.map_list_prod s

@[simps mul one {attrs := []}] instance End : monoid (A →ₐ[R] A) :=
{ mul := comp,
  mul_assoc := λ ϕ ψ χ, rfl,
  one := alg_hom.id R A,
  one_mul := λ ϕ, ext $ λ x, rfl,
  mul_one := λ ϕ, ext $ λ x, rfl }

@[simp] lemma one_apply (x : A) : (1 : A →ₐ[R] A) x = x := rfl

@[simp] lemma mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) := rfl

lemma algebra_map_eq_apply (f : A →ₐ[R] B) {y : R} {x : A} (h : algebra_map R A y = x) :
  algebra_map R B y = f x :=
h ▸ (f.commutes _).symm

end semiring

section comm_semiring

variables [comm_semiring R] [comm_semiring A] [comm_semiring B]
variables [algebra R A] [algebra R B] (φ : A →ₐ[R] B)

protected lemma map_multiset_prod (s : multiset A) :
  φ s.prod = (s.map φ).prod := map_multiset_prod _ _

protected lemma map_prod {ι : Type*} (f : ι → A) (s : finset ι) :
  φ (∏ x in s, f x) = ∏ x in s, φ (f x) := map_prod _ _ _

protected lemma map_finsupp_prod {α : Type*} [has_zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
  φ (f.prod g) = f.prod (λ i a, φ (g i a)) := map_finsupp_prod _ _ _

end comm_semiring

section ring

variables [comm_semiring R] [ring A] [ring B]
variables [algebra R A] [algebra R B] (φ : A →ₐ[R] B)

protected lemma map_neg (x) : φ (-x) = -φ x := map_neg _ _
protected lemma map_sub (x y) : φ (x - y) = φ x - φ y := map_sub _ _ _

end ring

end alg_hom


namespace ring_hom
variables {R S : Type*}

/-- Reinterpret a `ring_hom` as an `ℕ`-algebra homomorphism. -/
def to_nat_alg_hom [semiring R] [semiring S] (f : R →+* S) :
  R →ₐ[ℕ] S :=
{ to_fun := f, commutes' := λ n, by simp, .. f }

/-- Reinterpret a `ring_hom` as a `ℤ`-algebra homomorphism. -/
def to_int_alg_hom [ring R] [ring S] [algebra ℤ R] [algebra ℤ S] (f : R →+* S) :
  R →ₐ[ℤ] S :=
{ commutes' := λ n, by simp, .. f }

/-- Reinterpret a `ring_hom` as a `ℚ`-algebra homomorphism. This actually yields an equivalence,
see `ring_hom.equiv_rat_alg_hom`. -/
def to_rat_alg_hom [ring R] [ring S] [algebra ℚ R] [algebra ℚ S] (f : R →+* S) :
  R →ₐ[ℚ] S :=
{ commutes' := f.map_rat_algebra_map, .. f }

@[simp]
lemma to_rat_alg_hom_to_ring_hom [ring R] [ring S] [algebra ℚ R] [algebra ℚ S]
  (f : R →+* S) : ↑f.to_rat_alg_hom = f :=
ring_hom.ext $ λ x, rfl

end ring_hom

section
variables {R S : Type*}

@[simp]
lemma alg_hom.to_ring_hom_to_rat_alg_hom [ring R] [ring S] [algebra ℚ R] [algebra ℚ S]
  (f : R →ₐ[ℚ] S) : (f : R →+* S).to_rat_alg_hom = f :=
alg_hom.ext $ λ x, rfl

/-- The equivalence between `ring_hom` and `ℚ`-algebra homomorphisms. -/
@[simps]
def ring_hom.equiv_rat_alg_hom [ring R] [ring S] [algebra ℚ R] [algebra ℚ S] :
  (R →+* S) ≃ (R →ₐ[ℚ] S) :=
{ to_fun := ring_hom.to_rat_alg_hom,
  inv_fun := alg_hom.to_ring_hom,
  left_inv := ring_hom.to_rat_alg_hom_to_ring_hom,
  right_inv := alg_hom.to_ring_hom_to_rat_alg_hom, }

end

namespace algebra
variables (R : Type u) (A : Type v)
variables [comm_semiring R] [semiring A] [algebra R A]

/-- `algebra_map` as an `alg_hom`. -/
def of_id : R →ₐ[R] A :=
{ commutes' := λ _, rfl, .. algebra_map R A }
variables {R}

theorem of_id_apply (r) : of_id R A r = algebra_map R A r := rfl

end algebra

namespace mul_semiring_action
variables {M G : Type*} (R A : Type*) [comm_semiring R] [semiring A] [algebra R A]
variables [monoid M] [mul_semiring_action M A] [smul_comm_class M R A]

/-- Each element of the monoid defines a algebra homomorphism.

This is a stronger version of `mul_semiring_action.to_ring_hom` and
`distrib_mul_action.to_linear_map`. -/
@[simps]
def to_alg_hom (m : M) : A →ₐ[R] A :=
{ to_fun := λ a, m • a,
  commutes' := smul_algebra_map _,
  ..mul_semiring_action.to_ring_hom _ _ m }

theorem to_alg_hom_injective [has_faithful_smul M A] :
  function.injective (mul_semiring_action.to_alg_hom R A : M → A →ₐ[R] A) :=
λ m₁ m₂ h, eq_of_smul_eq_smul $ λ r, alg_hom.ext_iff.1 h r

end mul_semiring_action
