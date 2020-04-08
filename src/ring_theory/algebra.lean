/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Algebra over Commutative Ring (under category)
-/

import data.complex.basic
import data.matrix.basic
import linear_algebra.tensor_product
import ring_theory.subring
import algebra.commute

noncomputable theory

universes u v w u₁ v₁

open_locale tensor_product

section prio
-- We set this priority to 0 later in this file
set_option default_priority 200 -- see Note [default priority]
/-- The category of R-algebras where R is a commutative
ring is the under category R ↓ CRing. In the categorical
setting we have a forgetful functor R-Alg ⥤ R-Mod.
However here it extends module in order to preserve
definitional equality in certain cases. -/
class algebra (R : Type u) (A : Type v) [comm_ring R] [ring A] extends has_scalar R A :=
(to_fun : R → A) [hom : is_ring_hom to_fun]
(commutes' : ∀ r x, x * to_fun r = to_fun r * x)
(smul_def' : ∀ r x, r • x = to_fun r * x)
end prio

def algebra_map {R : Type u} (A : Type v) [comm_ring R] [ring A] [algebra R A] (x : R) : A :=
algebra.to_fun A x

namespace algebra

variables {R : Type u} {S : Type v} {A : Type w}
variables [comm_ring R] [comm_ring S] [ring A] [algebra R A]

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

lemma smul_def'' (r : R) (x : A) : r • x = algebra_map A r * x :=
algebra.smul_def' r x

@[priority 200] -- see Note [lower instance priority]
instance to_module : module R A :=
{ one_smul := by simp [smul_def''],
  mul_smul := by simp [smul_def'', mul_assoc],
  smul_add := by simp [smul_def'', mul_add],
  smul_zero := by simp [smul_def''],
  add_smul := by simp [smul_def'', add_mul],
  zero_smul := by simp [smul_def''] }

-- from now on, we don't want to use the following instance anymore
attribute [instance, priority 0] algebra.to_has_scalar

lemma smul_def (r : R) (x : A) : r • x = algebra_map A r * x :=
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

def lmul_left (r : A) : A →ₗ A :=
lmul R A r

def lmul_right (r : A) : A →ₗ A :=
(lmul R A).flip r

variables {R A}

@[simp] lemma lmul_apply (p q : A) : lmul R A p q = p * q := rfl
@[simp] lemma lmul_left_apply (p q : A) : lmul_left R A p q = p * q := rfl
@[simp] lemma lmul_right_apply (p q : A) : lmul_right R A p q = q * p := rfl

end algebra

instance module.endomorphism_algebra (R : Type u) (M : Type v)
  [comm_ring R] [add_comm_group M] [module R M] : algebra R (M →ₗ[R] M) :=
{ to_fun    := (λ r, r • linear_map.id),
  hom       := by apply is_ring_hom.mk; intros; ext; simp [mul_smul, add_smul],
  commutes' := by intros; ext; simp,
  smul_def' := by intros; ext; simp }

set_option class.instance_max_depth 40
instance matrix_algebra (n : Type u) (R : Type v)
  [fintype n] [decidable_eq n] [comm_ring R] : algebra R (matrix n n R) :=
{ to_fun    := (λ r, r • 1),
  hom       := { map_one := by { ext, simp, },
                 map_mul := by { intros, ext, simp [mul_assoc], },
                 map_add := by { intros, simp [add_smul], } },
  commutes' := by { intros, simp },
  smul_def' := by { intros, simp } }

set_option old_structure_cmd true
/-- Defining the homomorphism in the category R-Alg. -/
structure alg_hom (R : Type u) (A : Type v) (B : Type w)
  [comm_ring R] [ring A] [ring B] [algebra R A] [algebra R B] extends ring_hom A B :=
(commutes' : ∀ r : R, to_fun (algebra_map A r) = algebra_map B r)

infixr ` →ₐ `:25 := alg_hom _
notation A ` →ₐ[`:25 R `] ` B := alg_hom R A B

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}
variables {rR : comm_ring R} {rA : ring A} {rB : ring B} {rC : ring C} {rD : ring D}
variables {aA : algebra R A} {aB : algebra R B} {aC : algebra R C} {aD : algebra R D}
include R rR rA rB aA aB

instance : has_coe_to_fun (A →ₐ[R] B) := ⟨_, λ f, f.to_fun⟩

instance : has_coe (A →ₐ[R] B) (A →+* B) := ⟨alg_hom.to_ring_hom⟩

variables (φ : A →ₐ[R] B)

instance : is_ring_hom ⇑φ := ring_hom.is_ring_hom φ.to_ring_hom

@[ext]
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
omit rB aB
variables [rR] [rA] [aA]
protected def id : A →ₐ[R] A :=
{ commutes' := λ _, rfl,
  ..ring_hom.id A  }
variables {R A rR rA aA}

@[simp] lemma id_to_linear_map :
  (alg_hom.id R A).to_linear_map = @linear_map.id R A _ _ _ := rfl

@[simp] lemma id_apply (p : A) : alg_hom.id R A p = p := rfl

include rB rC aB aC

def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
{ commutes' := λ r : R, by rw [← φ₁.commutes, ← φ₂.commutes]; refl,
  .. φ₁.to_ring_hom.comp ↑φ₂ }

@[simp] lemma comp_to_linear_map (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
  (g.comp f).to_linear_map = g.to_linear_map.comp f.to_linear_map := rfl

@[simp] lemma comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) :
  φ₁.comp φ₂ p = φ₁ (φ₂ p) := rfl

omit rC aC

@[simp] theorem comp_id : φ.comp (alg_hom.id R A) = φ :=
ext $ λ x, rfl

@[simp] theorem id_comp : (alg_hom.id R B).comp φ = φ :=
ext $ λ x, rfl

include rC aC rD aD

theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
  (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
ext $ λ x, rfl

end alg_hom

namespace algebra

variables (R : Type u) (S : Type v) (A : Type w)
include R S A

/-- `comap R S A` is a type alias for `A`, and has an R-algebra structure defined on it
  when `algebra R S` and `algebra S A`. -/
/- This is done to avoid a type class search with meta-variables `algebra R ?m_1` and
    `algebra ?m_1 A -/
/- The `nolint` attribute is added because it has unused arguments `R` and `S`, but these are necessary for synthesizing the
     appropriate type classes -/
@[nolint unused_arguments] def comap : Type w := A
def comap.to_comap : A → comap R S A := id
def comap.of_comap : comap R S A → A := id

omit R S A
variables [comm_ring R] [comm_ring S] [ring A] [algebra R S] [algebra S A]

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
  hom := @is_ring_hom.comp _ _ _ _ _ _ _ _ _ _inst_5.hom,
  commutes' := λ r x, algebra.commutes _ _,
  smul_def' := λ _ _, algebra.smul_def _ _ }

def to_comap : S →ₐ[R] comap R S A :=
{ commutes' := λ r, rfl,
  ..ring_hom.of (algebra_map A : S → A) }

theorem to_comap_apply (x) : to_comap R S A x = (algebra_map A : S → A) x := rfl

end algebra

namespace alg_hom

variables {R : Type u} {S : Type v} {A : Type w} {B : Type u₁}
variables [comm_ring R] [comm_ring S] [ring A] [ring B]
variables [algebra R S] [algebra S A] [algebra S B] (φ : A →ₐ[S] B)
include R

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def comap : algebra.comap R S A →ₐ[R] algebra.comap R S B :=
{ commutes' := λ r, φ.commutes (algebra_map S r)
  ..φ }

end alg_hom

namespace rat

instance algebra_rat {α} [division_ring α] [char_zero α] : algebra ℚ α :=
{ smul := λ r x, (r : α) * x,
  to_fun := coe,
  hom := (rat.cast_hom α).is_ring_hom,
  commutes' := λ r x, (commute.cast_int_right x r.1).div_right (commute.cast_nat_right x r.2),
  smul_def' := λ _ _, rfl }

end rat

namespace complex

instance algebra_over_reals : algebra ℝ ℂ :=
algebra.of_ring_hom coe $ by constructor; intros; simp [one_re]

instance : has_scalar ℝ ℂ := { smul := λ r c, ↑r * c}

end complex

structure subalgebra (R : Type u) (A : Type v)
  [comm_ring R] [ring A] [algebra R A] : Type v :=
(carrier : set A) [subring : is_subring carrier]
(range_le' : set.range (algebra_map A : R → A) ≤ carrier)

namespace subalgebra

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] [algebra R A]
include R

instance : has_coe (subalgebra R A) (set A) :=
⟨λ S, S.carrier⟩

lemma range_le (S : subalgebra R A) : set.range (algebra_map A : R → A) ≤ S := S.range_le'

instance : has_mem A (subalgebra R A) :=
⟨λ x S, x ∈ (S : set A)⟩

variables {A}
theorem mem_coe {x : A} {s : subalgebra R A} : x ∈ (s : set A) ↔ x ∈ s :=
iff.rfl

@[ext] theorem ext {S T : subalgebra R A}
  (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
by cases S; cases T; congr; ext x; exact h x

theorem ext_iff {S T : subalgebra R A} : S = T ↔ ∀ x : A, x ∈ S ↔ x ∈ T :=
⟨λ h x, by rw h, ext⟩

variables (S : subalgebra R A)

instance : is_subring (S : set A) := S.subring
instance : ring S := @@subtype.ring _ S.is_subring
instance : inhabited S := ⟨0⟩
instance (R : Type u) (A : Type v) {rR : comm_ring R} [comm_ring A]
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
by refine_struct { to_fun := subtype.val }; intros; refl

def to_submodule : submodule R A :=
{ carrier := S,
  zero := (0:S).2,
  add := λ x y hx hy, (⟨x, hx⟩ + ⟨y, hy⟩ : S).2,
  smul := λ c x hx, (algebra.smul_def c x).symm ▸ (⟨algebra_map A c, S.range_le ⟨c, rfl⟩⟩ * ⟨x, hx⟩:S).2 }

instance coe_to_submodule : has_coe (subalgebra R A) (submodule R A) :=
⟨to_submodule⟩

instance to_submodule.is_subring : is_subring ((S : submodule R A) : set A) := S.2

instance : partial_order (subalgebra R A) :=
{ le := λ S T, (S : set A) ≤ (T : set A),
  le_refl := λ _, le_refl _,
  le_trans := λ _ _ _, le_trans,
  le_antisymm := λ S T hst hts, ext $ λ x, ⟨@hst x, @hts x⟩ }

def comap {R : Type u} {S : Type v} {A : Type w}
  [comm_ring R] [comm_ring S] [ring A] [algebra R S] [algebra S A]
  (iSB : subalgebra S A) : subalgebra R (algebra.comap R S A) :=
{ carrier := (iSB : set A),
  subring := iSB.is_subring,
  range_le' := λ a ⟨r, hr⟩, hr ▸ iSB.range_le ⟨_, rfl⟩ }

def under {R : Type u} {A : Type v} [comm_ring R] [comm_ring A]
  {i : algebra R A} (S : subalgebra R A)
  (T : subalgebra S A) : subalgebra R A :=
{ carrier := T,
  range_le' := (λ a ⟨r, hr⟩, hr ▸ T.range_le ⟨⟨algebra_map A r, S.range_le ⟨r, rfl⟩⟩, rfl⟩) }

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
  range_le' := λ y ⟨r, hr⟩, ⟨algebra_map A r, hr ▸ φ.commutes r⟩ }

end alg_hom

namespace algebra

variables {R : Type u} (A : Type v)
variables [comm_ring R] [ring A] [algebra R A]
include R

variables (R)
instance id : algebra R R :=
algebra.of_ring_hom id $ by apply_instance

namespace id

@[simp] lemma map_eq_self (x : R) : algebra_map R x = x := rfl

@[simp] lemma smul_eq_mul (x y : R) : x • y = x * y := rfl

end id

def of_id : R →ₐ A :=
{ commutes' := λ _, rfl, .. ring_hom.of (algebra_map A) }
variables {R}

theorem of_id_apply (r) : of_id R A r = algebra_map A r := rfl

variables (R) {A}
def adjoin (s : set A) : subalgebra R A :=
{ carrier := ring.closure (set.range (algebra_map A : R → A) ∪ s),
  range_le' := le_trans (set.subset_union_left _ _) ring.subset_closure }
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

instance : inhabited (subalgebra R A) := ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : subalgebra R A) ↔ x ∈ set.range (algebra_map A : R → A) :=
suffices (⊥ : subalgebra R A) = (of_id R A).range, by rw this; refl,
le_antisymm bot_le $ subalgebra.range_le _

theorem mem_top {x : A} : x ∈ (⊤ : subalgebra R A) :=
ring.mem_closure $ or.inr trivial

theorem eq_top_iff {S : subalgebra R A} :
  S = ⊤ ↔ ∀ x : A, x ∈ S :=
⟨λ h x, by rw h; exact mem_top, λ h, by ext x; exact ⟨λ _, mem_top, λ _, h x⟩⟩

def to_top : A →ₐ[R] (⊤ : subalgebra R A) :=
by refine_struct { to_fun := λ x, (⟨x, mem_top⟩ : (⊤ : subalgebra R A)) }; intros; refl

end algebra

section int

variables (R : Type*) [comm_ring R]

/-- CRing ⥤ ℤ-Alg -/
def alg_hom_int
  {R : Type u} [comm_ring R] [algebra ℤ R]
  {S : Type v} [comm_ring S] [algebra ℤ S]
  (f : R → S) [is_ring_hom f] : R →ₐ[ℤ] S :=
{ commutes' := λ i, by change (ring_hom.of f).to_fun with f; exact
    int.induction_on i (by rw [algebra.map_zero, algebra.map_zero, is_ring_hom.map_zero f])
      (λ i ih, by rw [algebra.map_add, algebra.map_add, algebra.map_one, algebra.map_one];
        rw [is_ring_hom.map_add f, is_ring_hom.map_one f, ih])
      (λ i ih, by rw [algebra.map_sub, algebra.map_sub, algebra.map_one, algebra.map_one];
        rw [is_ring_hom.map_sub f, is_ring_hom.map_one f, ih]),
  ..ring_hom.of f }

/-- CRing ⥤ ℤ-Alg -/
instance algebra_int : algebra ℤ R :=
{ to_fun := int.cast_ring_hom R,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ _ _, gsmul_eq_mul _ _ }

variables {R}
/-- CRing ⥤ ℤ-Alg -/
def subalgebra_of_subring (S : set R) [is_subring S] : subalgebra ℤ R :=
{ carrier := S, range_le' := λ x ⟨i, h⟩, h ▸ int.induction_on i
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
  (λ n a ha, by { exact is_add_subgroup.gsmul_mem ha }))
  (add_group.closure_subset subset_span)

@[simp] lemma span_int_eq (s : set R) [is_add_subgroup s] :
  (↑(span ℤ s) : set R) = s :=
by rw [span_int_eq_add_group_closure, add_group.closure_add_subgroup]

end span_int

end int

section restrict_scalars
/- In this section, we describe restriction of scalars: if `S` is an algebra over `R`, then
`S`-modules are also `R`-modules. -/

variables (R : Type*) [comm_ring R] (S : Type*) [ring S] [algebra R S]
(E : Type*) [add_comm_group E] [module S E] {F : Type*} [add_comm_group F] [module S F]

/-- When `E` is a module over a ring `S`, and `S` is an algebra over `R`, then `E` inherits a
module structure over `R`, called `module.restrict S R E`.
Not registered as an instance as `S` can not be inferred. -/
def module.restrict_scalars : module R E :=
{ smul      := λc x, (algebra_map S c) • x,
  one_smul  := by simp,
  mul_smul  := by simp [mul_smul],
  smul_add  := by simp [smul_add],
  smul_zero := by simp [smul_zero],
  add_smul  := by simp [add_smul],
  zero_smul := by simp [zero_smul] }

variables {S E}

local attribute [instance] module.restrict_scalars

/-- The `R`-linear map induced by an `S`-linear map when `S` is an algebra over `R`. -/
def linear_map.restrict_scalars (f : E →ₗ[S] F) : E →ₗ[R] F :=
{ to_fun := f.to_fun,
  add := λx y, f.map_add x y,
  smul := λc x, f.map_smul (algebra_map S c) x }

@[simp, squash_cast] lemma linear_map.coe_restrict_scalars_eq_coe (f : E →ₗ[S] F) :
  (f.restrict_scalars R : E → F) = f := rfl

/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
instance module.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E] : module ℝ E :=
module.restrict_scalars ℝ ℂ E
attribute [instance, priority 900] module.complex_to_real

end restrict_scalars
