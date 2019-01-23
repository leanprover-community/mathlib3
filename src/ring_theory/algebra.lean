/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Algebra over Commutative Ring (under category)
-/

import data.polynomial
import linear_algebra.multivariate_polynomial
import linear_algebra.tensor_product
import ring_theory.subring

universes u v w u₁ v₁

open lattice

local infix ` ⊗ `:100 := tensor_product

structure algebra.core (R : Type u) (A : Type v) [comm_ring R] [comm_ring A] :=
(to_fun : R → A) [hom : is_ring_hom to_fun]

/-- The category of R-algebras where R is a commutative
ring is the under category R ↓ CRing. In the categorical
setting we have a forgetful functor R-Alg ⥤ R-Mod.
However here it extends module in order to preserve
definitional equality in certain cases. -/
structure algebra (R : Type u) (A : Type v) [comm_ring R] [ring A] extends module R A :=
(to_fun : R → A) [hom : is_ring_hom to_fun]
(commutes' : ∀ r x, x * to_fun r = to_fun r * x)
(smul_def' : ∀ r x, r • x = to_fun r * x)

attribute [instance] algebra.hom

namespace algebra

variables {R : Type u} {S : Type v} {A : Type w}
variables [comm_ring R] [comm_ring S] [ring A]
variables (i : algebra R A)

/-- The codomain of an algebra. -/
def right (i : algebra R A) : Type w := A

namespace right

instance : ring i.right := _inst_3
instance (i : algebra R S) : comm_ring i.right := _inst_2
instance : monoid i.right := infer_instance
instance : add_comm_group i.right := infer_instance
instance : module R i.right := i.to_module
instance : has_scalar R i.right := infer_instance

instance {F : Type u} {K : Type v}
  [discrete_field F] [ring K] (i : algebra F K) :
  vector_space F i.right :=
vector_space.mk _ _

end right

instance : has_coe_to_fun (algebra R A) :=
⟨λ i, R → i.right, to_fun⟩

@[simp] lemma map_add (r s) : i (r + s) = i r + i s :=
is_ring_hom.map_add _

@[simp] lemma map_zero : i 0 = 0 :=
is_ring_hom.map_zero _

@[simp] lemma map_neg (r) : i (-r) = -i r :=
is_ring_hom.map_neg _

@[simp] lemma map_sub (r s) : i (r - s) = i r - i s :=
is_ring_hom.map_sub _

@[simp] lemma map_mul (r s) : i (r * s) = i r * i s :=
is_ring_hom.map_mul _

@[simp] lemma map_one : i 1 = 1 :=
is_ring_hom.map_one _

/-- Creating an algebra from a morphism in CRing. -/
def of_core (i : algebra.core R S) : algebra R S :=
{ smul := λ c x, i.to_fun c * x,
  smul_zero := λ x, mul_zero (i.to_fun x),
  smul_add := λ r x y, mul_add (i.to_fun r) x y,
  add_smul := λ r s x, show i.to_fun (r + s) * x = _, by rw [i.hom.3, add_mul],
  mul_smul := λ r s x, show i.to_fun (r * s) * x = _, by rw [i.hom.2, mul_assoc],
  one_smul := λ x, show i.to_fun 1 * x = _, by rw [i.hom.1, one_mul],
  zero_smul := λ x, show i.to_fun 0 * x = _, by rw [@@is_ring_hom.map_zero _ _ i.to_fun i.hom, zero_mul],
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ c x, rfl,
  .. i }

theorem smul_def (r : R) (x : i.right) : r • x = i r * x :=
smul_def' i r x

theorem commutes (r : R) (x : i.right) : x * i r = i r * x :=
commutes' i r x

theorem left_comm (r : R) (x y : i.right) : x * (i r * y) = i r * (x * y) :=
by rw [← mul_assoc, commutes, mul_assoc]

@[simp] protected lemma mul_smul (s : R) (x y : i.right) :
  x * (s • y) = s • (x * y) :=
by rw [smul_def, smul_def, left_comm]

@[simp] lemma smul_mul (r : R) (x y : i.right) :
  (r • x) * y = r • (x * y) :=
by rw [smul_def, smul_def, mul_assoc]

/-- R[X] is the generator of the category R-Alg. -/
def polynomial (R : Type u) [comm_ring R] [decidable_eq R] : algebra R (polynomial R) :=
{ to_fun := polynomial.C,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ c p, (polynomial.C_mul' c p).symm,
  .. polynomial.module }

/-- The algebra of multivariate polynomials. -/
def mv_polynomial (R : Type u) [comm_ring R] [decidable_eq R]
  (ι : Type v) [decidable_eq ι] : algebra R (mv_polynomial ι R) :=
{ to_fun := mv_polynomial.C,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ c p, (mv_polynomial.C_mul' c p).symm,
  .. mv_polynomial.module }

/-- Creating an algebra from a subring. This is the dual of ring extension. -/
def of_subring (S : set R) [is_subring S] : algebra S R := of_core
{ to_fun := subtype.val,
  hom := ⟨rfl, λ _ _, rfl, λ _ _, rfl⟩ }

/-- The multiplication in an algebra is a bilinear map. -/
def lmul : i.right →ₗ i.right →ₗ i.right :=
linear_map.mk₂ (*)
  (λ x y z, add_mul x y z)
  (λ c x y, by rw [smul_def, smul_def, mul_assoc _ x y])
  (λ x y z, mul_add x y z)
  (λ c x y, by rw [smul_def, smul_def, left_comm])

set_option class.instance_max_depth 37
def lmul_left (r : i.right) : i.right →ₗ i.right :=
i.lmul r

def lmul_right (r : i.right) : i.right →ₗ i.right :=
i.lmul.flip r

@[simp] lemma lmul_apply (p q : i.right) : i.lmul p q = p * q := rfl
@[simp] lemma lmul_left_apply (p q : i.right) : i.lmul_left p q = p * q := rfl
@[simp] lemma lmul_right_apply (p q : i.right) : i.lmul_right p q = q * p := rfl

set_option class.instance_max_depth 32

end algebra

/-- Defining the homomorphism in the category R-Alg. -/
structure alg_hom {R : Type u} {A : Type v} {B : Type w}
  [comm_ring R] [ring A] [ring B]
  (iA : algebra R A) (iB : algebra R B) :=
(to_fun : iA.right → iB.right) [hom : is_ring_hom to_fun]
(commutes' : ∀ r, to_fun (iA r) = iB r)

infixr ` →ₐ `:25 := alg_hom

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}
variables [comm_ring R] [ring A] [ring B] [ring C] [ring D]
variables (iA : algebra R A) (iB : algebra R B) (iC : algebra R C) (iD : algebra R D)
include R

instance : has_coe_to_fun (iA →ₐ iB) := ⟨λ _, iA.right → iB.right, to_fun⟩

variables {iA iB iC iD} (φ : iA →ₐ iB)

instance : is_ring_hom ⇑φ := hom φ

@[extensionality]
theorem ext {φ₁ φ₂ : iA →ₐ iB} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
by cases φ₁; cases φ₂; congr' 1; ext; apply H

theorem commutes (r) : φ (iA r) = iB r := φ.commutes' r

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
def to_linear_map : iA.right →ₗ iB.right :=
{ to_fun := φ,
  add := φ.map_add,
  smul := λ c x, by rw [algebra.smul_def, φ.map_mul, φ.commutes c, algebra.smul_def] }

@[simp] lemma to_linear_map_apply (p : A) : φ.to_linear_map p = φ p := rfl

theorem to_linear_map_inj {φ₁ φ₂ : iA →ₐ iB} (H : φ₁.to_linear_map = φ₂.to_linear_map) : φ₁ = φ₂ :=
ext $ λ x, show φ₁.to_linear_map x = φ₂.to_linear_map x, by rw H

variable (iA)
protected def id : iA →ₐ iA :=
{ to_fun := id, commutes' := λ _, rfl }
variable {iA}

@[simp] lemma id_apply (p : A) : alg_hom.id iA p = p := rfl

def comp (φ₁ : iB →ₐ iC) (φ₂ : iA →ₐ iB) : iA →ₐ iC :=
{ to_fun := φ₁ ∘ φ₂,
  commutes' := λ r, by rw [function.comp_apply, φ₂.commutes, φ₁.commutes] }

@[simp] lemma comp_apply (φ₁ : iB →ₐ iC) (φ₂ : iA →ₐ iB) (p : A) :
  φ₁.comp φ₂ p = φ₁ (φ₂ p) := rfl

@[simp] theorem comp_id : φ.comp (alg_hom.id iA) = φ :=
ext $ λ x, rfl

@[simp] theorem id_comp : (alg_hom.id iB).comp φ = φ :=
ext $ λ x, rfl

theorem comp_assoc (φ₁ : iC →ₐ iD) (φ₂ : iB →ₐ iC) (φ₃ : iA →ₐ iB) :
  (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
ext $ λ x, rfl

end alg_hom

namespace algebra

variables {R : Type u} {S : Type v} {A : Type w}
variables [comm_ring R] [comm_ring S] [ring A]
variables (i : algebra R S) (iSA : algebra S A)

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def comap : algebra R A :=
{ smul := λ r x, @has_scalar.smul.{v w} S A iSA.to_module.to_has_scalar (i r : S) x,
  smul_add := λ _ _ _, by letI := iSA.to_module; from smul_add _ _ _,
  add_smul := λ _ _ _, by letI := iSA.to_module; simp only [i.map_add]; from add_smul _ _ _,
  mul_smul := λ _ _ _, by letI := iSA.to_module; simp only [i.map_mul]; from mul_smul _ _ _,
  one_smul := λ _, by letI := iSA.to_module; simp only [i.map_one]; from one_smul _,
  zero_smul := λ _, by letI := iSA.to_module; simp only [i.map_zero]; from zero_smul _,
  smul_zero := λ _, by letI := iSA.to_module; from smul_zero _,
  to_fun := iSA ∘ i,
  commutes' := λ r x, iSA.commutes _ _,
  smul_def' := λ _ _, iSA.smul_def _ _ }

def to_comap : i →ₐ (i.comap iSA) :=
{ to_fun := iSA,
  commutes' := λ r, rfl }

theorem to_comap_apply (x) : i.to_comap iSA x = iSA x := rfl

end algebra

namespace alg_hom

variables {R : Type u} {S : Type v} {A : Type w} {B : Type u₁}
variables [comm_ring R] [comm_ring S] [ring A] [ring B]
variables (i : algebra R S)
variables {iSA : algebra S A} {iSB : algebra S B} (φ : iSA →ₐ iSB)

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def comap : i.comap iSA →ₐ i.comap iSB :=
{ to_fun := φ,
  commutes' := λ r, φ.commutes (i r) }

end alg_hom

namespace polynomial

variables (R : Type u) {A : Type v}
variables [comm_ring R] [comm_ring A] (i : algebra R A)
variables [decidable_eq R] (x : A)

/-- A → Hom[R-Alg](R[X],A) -/
def aeval : (algebra.polynomial R) →ₐ i :=
{ to_fun := eval₂ i x,
  hom := ⟨eval₂_one _ x, λ _ _, eval₂_mul _ x, λ _ _, eval₂_add _ x⟩,
  commutes' := λ r, eval₂_C _ _ }

theorem aeval_def (p : polynomial R) : aeval R i x p = eval₂ i x p := rfl

instance aeval.is_ring_hom : is_ring_hom (aeval R i x) :=
alg_hom.hom _

theorem eval_unique (φ : algebra.polynomial R →ₐ i) (p) :
  φ p = eval₂ i (φ X) p :=
begin
  apply polynomial.induction_on p,
  { intro r, rw eval₂_C, exact φ.commutes r },
  { intros f g ih1 ih2,
    rw [is_ring_hom.map_add φ, ih1, ih2, eval₂_add] },
  { intros n r ih,
    rw [pow_succ', ← mul_assoc, is_ring_hom.map_mul φ, eval₂_mul i, eval₂_X, ih] }
end

end polynomial

namespace mv_polynomial

variables (R : Type u) (A : Type v)
variables [comm_ring R] [comm_ring A] (i : algebra R A)
variables [decidable_eq R] [decidable_eq A] (σ : set A)

/-- (ι → A) → Hom[R-Alg](R[ι],A) -/
def aeval : (algebra.mv_polynomial R σ) →ₐ i :=
{ to_fun := eval₂ i subtype.val,
  hom := ⟨eval₂_one _ _, λ _ _, eval₂_mul _ _, λ _ _, eval₂_add _ _⟩,
  commutes' := λ r, eval₂_C _ _ _ }

theorem aeval_def (p : mv_polynomial σ R) : aeval R A i σ p = eval₂ i subtype.val p := rfl

instance aeval.is_ring_hom : is_ring_hom (aeval R A i σ) :=
alg_hom.hom _

variables (ι : Type w) [decidable_eq ι]

theorem eval_unique (φ : algebra.mv_polynomial R ι →ₐ i) (p) :
  φ p = eval₂ i (φ ∘ X) p :=
begin
  apply mv_polynomial.induction_on p,
  { intro r, rw eval₂_C, exact φ.commutes r },
  { intros f g ih1 ih2,
    rw [is_ring_hom.map_add φ, ih1, ih2, eval₂_add] },
  { intros p j ih,
    rw [is_ring_hom.map_mul φ, eval₂_mul, eval₂_X, ih] }
end

end mv_polynomial

section

variables (R : Type*) [comm_ring R]

/-- CRing ⥤ ℤ-Alg -/
def ring.to_ℤ_algebra : algebra ℤ R := algebra.of_core
{ to_fun := coe,
  hom := by constructor; intros; simp }

/-- CRing ⥤ ℤ-Alg -/
def is_ring_hom.to_ℤ_alg_hom
  {R : Type u} [comm_ring R] (iR : algebra ℤ R)
  {S : Type v} [comm_ring S] (iS : algebra ℤ S)
  (f : iR.right → iS.right) [is_ring_hom f] : iR →ₐ iS :=
{ to_fun := f, hom := by apply_instance,
  commutes' := λ i, int.induction_on i (by rw [iR.map_zero, iS.map_zero, is_ring_hom.map_zero f])
      (λ i ih, by rw [iR.map_add, iS.map_add, iR.map_one, iS.map_one];
        rw [is_ring_hom.map_add f, is_ring_hom.map_one f, ih])
      (λ i ih, by rw [iR.map_sub, iS.map_sub, iR.map_one, iS.map_one];
        rw [is_ring_hom.map_sub f, is_ring_hom.map_one f, ih]) }

instance : ring (polynomial ℤ) :=
comm_ring.to_ring _

end

structure subalgebra {R : Type u} {A : Type v}
  [comm_ring R] [ring A] (i : algebra R A) : Type v :=
(carrier : set A) [subring : is_subring carrier]
(range_le : set.range i ≤ carrier)

attribute [instance] subalgebra.subring

namespace subalgebra

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] (i : algebra R A)

instance : has_coe (subalgebra i) (set A) :=
⟨λ S, S.carrier⟩

instance : has_mem A (subalgebra i) :=
⟨λ x S, x ∈ S.carrier⟩

variables {i}

theorem mem_coe {x : A} {s : subalgebra i} : x ∈ (s : set A) ↔ x ∈ s :=
iff.rfl

@[extensionality] theorem ext {S T : subalgebra i}
  (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
by cases S; cases T; congr; ext x; exact h x

variables (S : subalgebra i)

instance : is_subring (S : set A) := S.subring

instance : ring S := @@subtype.ring _ S.is_subring

protected def algebra : algebra R S :=
{ smul := λ (c:R) x, ⟨@has_scalar.smul R A i.to_module.to_has_scalar c x.1,
    by rw i.smul_def; exact @@is_submonoid.mul_mem _ S.2.2 (S.3 ⟨c, rfl⟩) x.2⟩,
  smul_add := λ c x y, subtype.eq $ by apply i.1.1.2,
  add_smul := λ c x y, subtype.eq $ by apply i.1.1.3,
  mul_smul := λ c x y, subtype.eq $ by apply i.1.1.4,
  one_smul := λ x, subtype.eq $ by apply i.1.1.5,
  zero_smul := λ x, subtype.eq $ by apply i.1.1.6,
  smul_zero := λ x, subtype.eq $ by apply i.1.1.7,
  to_fun := λ r, ⟨i r, S.range_le ⟨r, rfl⟩⟩,
  hom := ⟨subtype.eq i.map_one, λ x y, subtype.eq $ i.map_mul x y,
    λ x y, subtype.eq $ i.map_add x y⟩,
  commutes' := λ c x, subtype.eq $ by apply i.4,
  smul_def' := λ c x, subtype.eq $ by apply i.5 }

def val : S.algebra →ₐ i :=
{ to_fun := subtype.val,
  hom := ⟨rfl, λ _ _, rfl, λ _ _, rfl⟩,
  commutes' := λ r, rfl }

def to_submodule : submodule R i.right :=
{ carrier := S.carrier,
  zero := (0:S).2,
  add := λ x y hx hy, (⟨x, hx⟩ + ⟨y, hy⟩ : S).2,
  smul := λ c x hx, (i.smul_def c x).symm ▸ (⟨i c, S.range_le ⟨c, rfl⟩⟩ * ⟨x, hx⟩:S).2 }

instance to_submodule.is_subring : is_subring (S.to_submodule : set i.right) := S.2

instance : partial_order (subalgebra i) :=
{ le := λ S T, S.carrier ≤ T.carrier,
  le_refl := λ _, le_refl _,
  le_trans := λ _ _ _, le_trans,
  le_antisymm := λ S T hst hts, ext $ λ x, ⟨@hst x, @hts x⟩ }

def comap {R : Type u} {S : Type v} {A : Type w}
  [comm_ring R] [comm_ring S] [ring A]
  (iRS : algebra R S) {iSA : algebra S A}
  (iSB : subalgebra iSA) : subalgebra (iRS.comap iSA) :=
{ carrier := iSB,
  range_le := λ a ⟨r, hr⟩, hr ▸ iSB.range_le ⟨_, rfl⟩ }

def under {R : Type u} {A : Type v} [comm_ring R] [comm_ring A]
  {i : algebra R A} (S : subalgebra i)
  (T : subalgebra (algebra.of_subring (S : set A))) : subalgebra i :=
{ carrier := T,
  range_le := λ a ⟨r, hr⟩, hr ▸ T.range_le ⟨⟨i r, S.range_le ⟨r, rfl⟩⟩, rfl⟩ }

end subalgebra

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_ring R] [ring A] [ring B]
variables {iA : algebra R A} {iB : algebra R B}
variables (φ : iA →ₐ iB)

protected def range : subalgebra iB :=
{ carrier := set.range φ,
  subring :=
  { one_mem := ⟨1, φ.map_one⟩,
    mul_mem := λ y₁ y₂ ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩, ⟨x₁ * x₂, hx₁ ▸ hx₂ ▸ φ.map_mul x₁ x₂⟩ },
  range_le := λ y ⟨r, hr⟩, ⟨iA r, hr ▸ φ.commutes r⟩ }

end alg_hom

namespace algebra

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] (i : algebra R A)

variables (R)
protected def id : algebra R R := algebra.of_core
{ to_fun := id }
variables {R}

def of_id : algebra.id R →ₐ i :=
{ to_fun := i, commutes' := λ _, rfl }

theorem of_id_apply (r) : i.of_id r = i r := rfl

def adjoin (s : set A) : subalgebra i :=
{ carrier := ring.closure (set.range i ∪ s),
  range_le := le_trans (set.subset_union_left _ _) ring.subset_closure }

protected def gc : galois_connection i.adjoin coe :=
λ s S, ⟨λ H, le_trans (le_trans (set.subset_union_right _ _) ring.subset_closure) H,
λ H, ring.closure_subset $ set.union_subset S.range_le H⟩

protected def gi : galois_insertion i.adjoin coe :=
{ choice := λ s hs, i.adjoin s,
  gc := i.gc,
  le_l_u := λ S, (i.gc S (i.adjoin S)).1 (le_refl _),
  choice_eq := λ _ _, rfl }

instance : complete_lattice (subalgebra i) :=
galois_insertion.lift_complete_lattice i.gi

theorem mem_bot {x : A} : x ∈ (⊥ : subalgebra i) ↔ x ∈ set.range i :=
suffices (⊥ : subalgebra i) = i.of_id.range, by rw this; refl,
le_antisymm bot_le $ subalgebra.range_le _

theorem mem_top {x : A} : x ∈ (⊤ : subalgebra i) :=
ring.mem_closure $ or.inr trivial

def to_top : i →ₐ (⊤ : subalgebra i).algebra :=
{ to_fun := λ x, ⟨x, i.mem_top⟩,
  hom := ⟨rfl, λ _ _, rfl, λ _ _, rfl⟩,
  commutes' := λ _, rfl }

end algebra
