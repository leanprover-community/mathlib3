/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Algebra over Commutative Ring (under category)
-/

import data.polynomial data.mv_polynomial
import data.complex.basic
import linear_algebra.tensor_product
import ring_theory.subring

noncomputable theory

universes u v w u₁ v₁

open lattice
open_locale tensor_product

/-- The category of R-algebras where R is a commutative
ring is the under category R ↓ CRing. In the categorical
setting we have a forgetful functor R-Alg ⥤ R-Mod.
However here it extends module in order to preserve
definitional equality in certain cases. -/
class algebra (R : Type u) (A : Type v) [comm_ring R] [ring A] extends has_scalar R A :=
(to_fun : R → A) [hom : is_ring_hom to_fun]
(commutes' : ∀ r x, x * to_fun r = to_fun r * x)
(smul_def' : ∀ r x, r • x = to_fun r * x)

attribute [instance] algebra.hom

def algebra_map {R : Type u} (A : Type v) [comm_ring R] [ring A] [algebra R A] (x : R) : A :=
algebra.to_fun A x

namespace algebra

variables {R : Type u} {S : Type v} {A : Type w}
variables [comm_ring R] [comm_ring S] [ring A] [algebra R A]

/-- The codomain of an algebra. -/
instance : has_scalar R A := infer_instance

include R

instance : is_ring_hom (algebra_map A : R → A) := algebra.hom _ A

variables (A)
@[simp] lemma map_add (r s : R) : algebra_map A (r + s) = algebra_map A r + algebra_map A s :=
is_ring_hom.map_add _

@[simp] lemma map_neg (r : R) : algebra_map A (-r) = -algebra_map A r :=
is_ring_hom.map_neg _

@[simp] lemma map_sub (r s : R) : algebra_map A (r - s) = algebra_map A r - algebra_map A s :=
is_ring_hom.map_sub _

@[simp] lemma map_mul (r s : R) : algebra_map A (r * s) = algebra_map A r * algebra_map A s :=
is_ring_hom.map_mul _

variables (R)
@[simp] lemma map_zero : algebra_map A (0 : R) = 0 :=
is_ring_hom.map_zero _

@[simp] lemma map_one : algebra_map A (1 : R) = 1 :=
is_ring_hom.map_one _
variables {R A}

/-- Creating an algebra from a morphism in CRing. -/
def of_ring_hom (i : R → S) (hom : is_ring_hom i) : algebra R S :=
{ smul := λ c x, i c * x,
  to_fun := i,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ c x, rfl }

theorem smul_def (r : R) (x : A) : r • x = algebra_map A r * x :=
algebra.smul_def' r x

theorem commutes (r : R) (x : A) : x * algebra_map A r = algebra_map A r * x :=
algebra.commutes' r x

theorem left_comm (r : R) (x y : A) : x * (algebra_map A r * y) = algebra_map A r * (x * y) :=
by rw [← mul_assoc, commutes, mul_assoc]

@[simp] lemma mul_smul_comm (s : R) (x y : A) :
  x * (s • y) = s • (x * y) :=
by rw [smul_def, smul_def, left_comm]

@[simp] lemma smul_mul_assoc (r : R) (x y : A) :
  (r • x) * y = r • (x * y) :=
by rw [smul_def, smul_def, mul_assoc]

instance to_module : module R A :=
{ one_smul := by simp [smul_def],
  mul_smul := by simp [smul_def, mul_assoc],
  smul_add := by simp [smul_def, mul_add],
  smul_zero := by simp [smul_def],
  add_smul := by simp [smul_def, add_mul],
  zero_smul := by simp [smul_def] }

instance {F : Type u} {K : Type v} [discrete_field F] [ring K] [algebra F K] :
  vector_space F K :=
@vector_space.mk F _ _ _ algebra.to_module

/-- R[X] is the generator of the category R-Alg. -/
instance polynomial (R : Type u) [comm_ring R] : algebra R (polynomial R) :=
{ to_fun := polynomial.C,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ c p, (polynomial.C_mul' c p).symm,
  .. polynomial.module }

/-- The algebra of multivariate polynomials. -/
instance mv_polynomial (R : Type u) [comm_ring R]
  (ι : Type v) : algebra R (mv_polynomial ι R) :=
{ to_fun := mv_polynomial.C,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ c p, (mv_polynomial.C_mul' c p).symm,
  .. mv_polynomial.module }

/-- Creating an algebra from a subring. This is the dual of ring extension. -/
instance of_subring (S : set R) [is_subring S] : algebra S R :=
of_ring_hom subtype.val ⟨rfl, λ _ _, rfl, λ _ _, rfl⟩

variables (R A)
/-- The multiplication in an algebra is a bilinear map. -/
def lmul : A →ₗ A →ₗ A :=
linear_map.mk₂ R (*)
  (λ x y z, add_mul x y z)
  (λ c x y, by rw [smul_def, smul_def, mul_assoc _ x y])
  (λ x y z, mul_add x y z)
  (λ c x y, by rw [smul_def, smul_def, left_comm])

set_option class.instance_max_depth 39
def lmul_left (r : A) : A →ₗ A :=
lmul R A r

def lmul_right (r : A) : A →ₗ A :=
(lmul R A).flip r

variables {R A}

@[simp] lemma lmul_apply (p q : A) : lmul R A p q = p * q := rfl
@[simp] lemma lmul_left_apply (p q : A) : lmul_left R A p q = p * q := rfl
@[simp] lemma lmul_right_apply (p q : A) : lmul_right R A p q = q * p := rfl

end algebra

/-- Defining the homomorphism in the category R-Alg. -/
structure alg_hom (R : Type u) (A : Type v) (B : Type w)
  [comm_ring R] [ring A] [ring B] [algebra R A] [algebra R B] :=
(to_fun : A → B) [hom : is_ring_hom to_fun]
(commutes' : ∀ r : R, to_fun (algebra_map A r) = algebra_map B r)

infixr ` →ₐ `:25 := alg_hom _
notation A ` →ₐ[`:25 R `] ` B := alg_hom R A B

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}
variables [comm_ring R] [ring A] [ring B] [ring C] [ring D]
variables [algebra R A] [algebra R B] [algebra R C] [algebra R D]
include R

instance : has_coe_to_fun (A →ₐ[R] B) := ⟨λ _, A → B, to_fun⟩

variables (φ : A →ₐ[R] B)

instance : is_ring_hom ⇑φ := hom φ

@[extensionality]
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
by cases φ₁; cases φ₂; congr' 1; ext; apply H

theorem commutes (r : R) : φ (algebra_map A r) = algebra_map B r := φ.commutes' r

@[simp] lemma map_add (r s : A) : φ (r + s) = φ r + φ s :=
is_ring_hom.map_add _

@[simp] lemma map_zero : φ 0 = 0 :=
is_ring_hom.map_zero _

@[simp] lemma map_neg (x) : φ (-x) = -φ x :=
is_ring_hom.map_neg _

@[simp] lemma map_sub (x y) : φ (x - y) = φ x - φ y :=
is_ring_hom.map_sub _

@[simp] lemma map_mul (x y) : φ (x * y) = φ x * φ y :=
is_ring_hom.map_mul _

@[simp] lemma map_one : φ 1 = 1 :=
is_ring_hom.map_one _

/-- R-Alg ⥤ R-Mod -/
def to_linear_map : A →ₗ B :=
{ to_fun := φ,
  add := φ.map_add,
  smul := λ (c : R) x, by rw [algebra.smul_def, φ.map_mul, φ.commutes c, algebra.smul_def] }

@[simp] lemma to_linear_map_apply (p : A) : φ.to_linear_map p = φ p := rfl

theorem to_linear_map_inj {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁.to_linear_map = φ₂.to_linear_map) : φ₁ = φ₂ :=
ext $ λ x, show φ₁.to_linear_map x = φ₂.to_linear_map x, by rw H

variables (R A)
protected def id : A →ₐ[R] A :=
{ to_fun := id, commutes' := λ _, rfl }
variables {R A}

@[simp] lemma id_to_linear_map :
  (alg_hom.id R A).to_linear_map = @linear_map.id R A _ _ _ := rfl

@[simp] lemma id_apply (p : A) : alg_hom.id R A p = p := rfl

def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ C :=
{ to_fun := φ₁ ∘ φ₂,
  commutes' := λ r, by rw [function.comp_apply, φ₂.commutes, φ₁.commutes] }

@[simp] lemma comp_to_linear_map (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
  (g.comp f).to_linear_map = g.to_linear_map.comp f.to_linear_map := rfl

@[simp] lemma comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) :
  φ₁.comp φ₂ p = φ₁ (φ₂ p) := rfl

@[simp] theorem comp_id : φ.comp (alg_hom.id R A) = φ :=
ext $ λ x, rfl

@[simp] theorem id_comp : (alg_hom.id R B).comp φ = φ :=
ext $ λ x, rfl

theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
  (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
ext $ λ x, rfl

end alg_hom

namespace algebra

variables (R : Type u) (S : Type v) (A : Type w)
variables [comm_ring R] [comm_ring S] [ring A] [algebra R S] [algebra S A]
include R S A
def comap : Type w := A
def comap.to_comap : A → comap R S A := id
def comap.of_comap : comap R S A → A := id
omit R S A

instance comap.ring : ring (comap R S A) := _inst_3
instance comap.comm_ring (R : Type u) (S : Type v) (A : Type w)
  [comm_ring R] [comm_ring S] [comm_ring A] [algebra R S] [algebra S A] :
  comm_ring (comap R S A) := _inst_8
instance comap.module : module S (comap R S A) := show module S A, by apply_instance
instance comap.has_scalar : has_scalar S (comap R S A) := show has_scalar S A, by apply_instance

set_option class.instance_max_depth 40

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
instance comap.algebra : algebra R (comap R S A) :=
{ smul := λ r x, (algebra_map S r • x : A),
  to_fun := (algebra_map A : S → A) ∘ algebra_map S,
  hom := by letI : is_ring_hom (algebra_map A) := _inst_5.hom; apply_instance,
  commutes' := λ r x, algebra.commutes _ _,
  smul_def' := λ _ _, algebra.smul_def _ _ }

def to_comap : S →ₐ[R] comap R S A :=
{ to_fun := (algebra_map A : S → A),
  hom := _inst_5.hom,
  commutes' := λ r, rfl }

theorem to_comap_apply (x) : to_comap R S A x = (algebra_map A : S → A) x := rfl

end algebra

namespace alg_hom

variables {R : Type u} {S : Type v} {A : Type w} {B : Type u₁}
variables [comm_ring R] [comm_ring S] [ring A] [ring B]
variables [algebra R S] [algebra S A] [algebra S B] (φ : A →ₐ[S] B)
include R

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def comap : algebra.comap R S A →ₐ[R] algebra.comap R S B :=
{ to_fun := φ,
  hom := alg_hom.is_ring_hom _,
  commutes' := λ r, φ.commutes (algebra_map S r) }

end alg_hom

namespace polynomial

variables (R : Type u) (A : Type v)
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (x : A)

/-- A → Hom[R-Alg](R[X],A) -/
def aeval : polynomial R →ₐ[R] A :=
{ to_fun := eval₂ (algebra_map A) x,
  hom := ⟨eval₂_one _ x, λ _ _, eval₂_mul _ x, λ _ _, eval₂_add _ x⟩,
  commutes' := λ r, eval₂_C _ _ }

theorem aeval_def (p : polynomial R) : aeval R A x p = eval₂ (algebra_map A) x p := rfl

instance aeval.is_ring_hom : is_ring_hom (aeval R A x) :=
alg_hom.hom _

theorem eval_unique (φ : polynomial R →ₐ[R] A) (p) :
  φ p = eval₂ (algebra_map A) (φ X) p :=
begin
  apply polynomial.induction_on p,
  { intro r, rw eval₂_C, exact φ.commutes r },
  { intros f g ih1 ih2,
    rw [is_ring_hom.map_add φ, ih1, ih2, eval₂_add] },
  { intros n r ih,
    rw [pow_succ', ← mul_assoc, is_ring_hom.map_mul φ, eval₂_mul (algebra_map A : R → A), eval₂_X, ih] }
end

end polynomial

namespace mv_polynomial

variables (R : Type u) (A : Type v)
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (σ : set A)

/-- (ι → A) → Hom[R-Alg](R[ι],A) -/
def aeval : mv_polynomial σ R →ₐ[R] A :=
{ to_fun := eval₂ (algebra_map A) subtype.val,
  hom := ⟨eval₂_one _ _, λ _ _, eval₂_mul _ _, λ _ _, eval₂_add _ _⟩,
  commutes' := λ r, eval₂_C _ _ _ }

theorem aeval_def (p : mv_polynomial σ R) : aeval R A σ p = eval₂ (algebra_map A) subtype.val p := rfl

instance aeval.is_ring_hom : is_ring_hom (aeval R A σ) :=
alg_hom.hom _

variables (ι : Type w)

theorem eval_unique (φ : mv_polynomial ι R →ₐ[R] A) (p) :
  φ p = eval₂ (algebra_map A) (φ ∘ X) p :=
begin
  apply mv_polynomial.induction_on p,
  { intro r, rw eval₂_C, exact φ.commutes r },
  { intros f g ih1 ih2,
    rw [is_ring_hom.map_add φ, ih1, ih2, eval₂_add] },
  { intros p j ih,
    rw [is_ring_hom.map_mul φ, eval₂_mul, eval₂_X, ih] }
end

end mv_polynomial

namespace complex

instance algebra_over_reals : algebra ℝ ℂ :=
algebra.of_ring_hom coe $ by constructor; intros; simp [one_re]

instance : has_scalar ℝ ℂ := { smul := λ r c, ↑r * c}

end complex

structure subalgebra (R : Type u) (A : Type v)
  [comm_ring R] [ring A] [algebra R A] : Type v :=
(carrier : set A) [subring : is_subring carrier]
(range_le : set.range (algebra_map A : R → A) ≤ carrier)

attribute [instance] subalgebra.subring

namespace subalgebra

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] [algebra R A]
include R

instance : has_coe (subalgebra R A) (set A) :=
⟨λ S, S.carrier⟩

instance : has_mem A (subalgebra R A) :=
⟨λ x S, x ∈ S.carrier⟩

variables {A}
theorem mem_coe {x : A} {s : subalgebra R A} : x ∈ (s : set A) ↔ x ∈ s :=
iff.rfl

@[extensionality] theorem ext {S T : subalgebra R A}
  (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
by cases S; cases T; congr; ext x; exact h x

variables (S : subalgebra R A)

instance : is_subring (S : set A) := S.subring
instance : ring S := @@subtype.ring _ S.is_subring
instance (R : Type u) (A : Type v) {rR : comm_ring R} {rA : comm_ring A}
  {aA : algebra R A} (S : subalgebra R A) : comm_ring S := @@subtype.comm_ring _ S.is_subring

instance algebra : algebra R S :=
{ smul := λ (c:R) x, ⟨c • x.1,
    by rw algebra.smul_def; exact @@is_submonoid.mul_mem _ S.2.2 (S.3 ⟨c, rfl⟩) x.2⟩,
  to_fun := λ r, ⟨algebra_map A r, S.range_le ⟨r, rfl⟩⟩,
  hom := ⟨subtype.eq $ algebra.map_one R A, λ x y, subtype.eq $ algebra.map_mul A x y,
    λ x y, subtype.eq $ algebra.map_add A x y⟩,
  commutes' := λ c x, subtype.eq $ by apply _inst_3.4,
  smul_def' := λ c x, subtype.eq $ by apply _inst_3.5 }

instance to_algebra (R : Type u) (A : Type v) [comm_ring R] [comm_ring A]
  [algebra R A] (S : subalgebra R A) : algebra S A :=
algebra.of_subring _

def val : S →ₐ[R] A :=
{ to_fun := subtype.val,
  hom := ⟨rfl, λ _ _, rfl, λ _ _, rfl⟩,
  commutes' := λ r, rfl }

def to_submodule : submodule R A :=
{ carrier := S.carrier,
  zero := (0:S).2,
  add := λ x y hx hy, (⟨x, hx⟩ + ⟨y, hy⟩ : S).2,
  smul := λ c x hx, (algebra.smul_def c x).symm ▸ (⟨algebra_map A c, S.range_le ⟨c, rfl⟩⟩ * ⟨x, hx⟩:S).2 }

instance coe_to_submodule : has_coe (subalgebra R A) (submodule R A) :=
⟨to_submodule⟩

instance to_submodule.is_subring : is_subring ((S : submodule R A) : set A) := S.2

instance : partial_order (subalgebra R A) :=
{ le := λ S T, S.carrier ≤ T.carrier,
  le_refl := λ _, le_refl _,
  le_trans := λ _ _ _, le_trans,
  le_antisymm := λ S T hst hts, ext $ λ x, ⟨@hst x, @hts x⟩ }

def comap {R : Type u} {S : Type v} {A : Type w}
  [comm_ring R] [comm_ring S] [ring A] [algebra R S] [algebra S A]
  (iSB : subalgebra S A) : subalgebra R (algebra.comap R S A) :=
{ carrier := (iSB : set A),
  subring := iSB.is_subring,
  range_le := λ a ⟨r, hr⟩, hr ▸ iSB.range_le ⟨_, rfl⟩ }

set_option class.instance_max_depth 48

def under {R : Type u} {A : Type v} [comm_ring R] [comm_ring A]
  {i : algebra R A} (S : subalgebra R A)
  (T : subalgebra S A) : subalgebra R A :=
{ carrier := T,
  range_le := (λ a ⟨r, hr⟩, hr ▸ T.range_le ⟨⟨algebra_map A r, S.range_le ⟨r, rfl⟩⟩, rfl⟩) }

end subalgebra

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_ring R] [ring A] [ring B] [algebra R A] [algebra R B]
variables (φ : A →ₐ[R] B)

protected def range : subalgebra R B :=
{ carrier := set.range φ,
  subring :=
  { one_mem := ⟨1, φ.map_one⟩,
    mul_mem := λ y₁ y₂ ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩, ⟨x₁ * x₂, hx₁ ▸ hx₂ ▸ φ.map_mul x₁ x₂⟩ },
  range_le := λ y ⟨r, hr⟩, ⟨algebra_map A r, hr ▸ φ.commutes r⟩ }

end alg_hom

namespace algebra

variables {R : Type u} (A : Type v)
variables [comm_ring R] [ring A] [algebra R A]
include R

variables (R)
instance id : algebra R R :=
algebra.of_ring_hom id $ by apply_instance

def of_id : R →ₐ A :=
{ to_fun := algebra_map A, commutes' := λ _, rfl }
variables {R}

theorem of_id_apply (r) : of_id R A r = algebra_map A r := rfl

variables (R) {A}
def adjoin (s : set A) : subalgebra R A :=
{ carrier := ring.closure (set.range (algebra_map A : R → A) ∪ s),
  range_le := le_trans (set.subset_union_left _ _) ring.subset_closure }
variables {R}

protected lemma gc : galois_connection (adjoin R : set A → subalgebra R A) coe :=
λ s S, ⟨λ H, le_trans (le_trans (set.subset_union_right _ _) ring.subset_closure) H,
λ H, ring.closure_subset $ set.union_subset S.range_le H⟩

protected def gi : galois_insertion (adjoin R : set A → subalgebra R A) coe :=
{ choice := λ s hs, adjoin R s,
  gc := algebra.gc,
  le_l_u := λ S, (algebra.gc (S : set A) (adjoin R S)).1 $ le_refl _,
  choice_eq := λ _ _, rfl }

instance : complete_lattice (subalgebra R A) :=
galois_insertion.lift_complete_lattice algebra.gi

theorem mem_bot {x : A} : x ∈ (⊥ : subalgebra R A) ↔ x ∈ set.range (algebra_map A : R → A) :=
suffices (⊥ : subalgebra R A) = (of_id R A).range, by rw this; refl,
le_antisymm bot_le $ subalgebra.range_le _

theorem mem_top {x : A} : x ∈ (⊤ : subalgebra R A) :=
ring.mem_closure $ or.inr trivial

def to_top : A →ₐ[R] (⊤ : subalgebra R A) :=
{ to_fun := λ x, ⟨x, mem_top⟩,
  hom := ⟨rfl, λ _ _, rfl, λ _ _, rfl⟩,
  commutes' := λ _, rfl }

end algebra

section int

variables (R : Type*) [comm_ring R]

/-- CRing ⥤ ℤ-Alg -/
def alg_hom_int
  {R : Type u} [comm_ring R] [algebra ℤ R]
  {S : Type v} [comm_ring S] [algebra ℤ S]
  (f : R → S) [is_ring_hom f] : R →ₐ[ℤ] S :=
{ to_fun := f, hom := by apply_instance,
  commutes' := λ i, int.induction_on i (by rw [algebra.map_zero, algebra.map_zero, is_ring_hom.map_zero f])
      (λ i ih, by rw [algebra.map_add, algebra.map_add, algebra.map_one, algebra.map_one];
        rw [is_ring_hom.map_add f, is_ring_hom.map_one f, ih])
      (λ i ih, by rw [algebra.map_sub, algebra.map_sub, algebra.map_one, algebra.map_one];
        rw [is_ring_hom.map_sub f, is_ring_hom.map_one f, ih]) }

/-- CRing ⥤ ℤ-Alg -/
instance algebra_int : algebra ℤ R :=
algebra.of_ring_hom coe $ by constructor; intros; simp

variables {R}
/-- CRing ⥤ ℤ-Alg -/
def subalgebra_of_subring (S : set R) [is_subring S] : subalgebra ℤ R :=
{ carrier := S, range_le := λ x ⟨i, h⟩, h ▸ int.induction_on i
    (by rw algebra.map_zero; exact is_add_submonoid.zero_mem _)
    (λ i hi, by rw [algebra.map_add, algebra.map_one]; exact is_add_submonoid.add_mem hi (is_submonoid.one_mem _))
    (λ i hi, by rw [algebra.map_sub, algebra.map_one]; exact is_add_subgroup.sub_mem _ _ _ hi (is_submonoid.one_mem _)) }

@[simp] lemma mem_subalgebra_of_subring {x : R} {S : set R} [is_subring S] :
  x ∈ subalgebra_of_subring S ↔ x ∈ S :=
iff.rfl

section span_int
open submodule

lemma span_int_eq_add_group_closure (s : set R) :
  ↑(span ℤ s) = add_group.closure s :=
set.subset.antisymm (λ x hx, span_induction hx
  (λ _, add_group.mem_closure)
  (is_add_submonoid.zero_mem _)
  (λ a b ha hb, is_add_submonoid.add_mem ha hb)
  (λ n a ha, by { erw [show n • a = gsmul n a, from (gsmul_eq_mul a n).symm],
    exact is_add_subgroup.gsmul_mem ha}))
  (add_group.closure_subset subset_span)

@[simp] lemma span_int_eq (s : set R) [is_add_subgroup s] :
  (↑(span ℤ s) : set R) = s :=
by rw [span_int_eq_add_group_closure, add_group.closure_add_subgroup]

end span_int

end int
