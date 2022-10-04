import algebra.star.star_alg_hom
import analysis.normed_space.star.basic
import category_theory.concrete_category.basic
import analysis.complex.basic

.


section prerequisites

namespace non_unital_star_alg_hom

variables {F R A B : Type*} [monoid R] [has_star A] [has_star B] [non_unital_non_assoc_semiring A]
variables [non_unital_non_assoc_semiring B] [distrib_mul_action R A] [distrib_mul_action R B]
variables [non_unital_star_alg_hom_class F R A B]

instance  : has_coe_t F (A →⋆ₙₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
    map_smul' := map_smul f,
    map_zero' := map_zero f,
    map_add' := map_add f,
    map_mul' := map_mul f,
    map_star' := map_star f } }

@[simp, protected] lemma coe_coe (f : F) : ⇑(f : A →⋆ₙₐ[R] B) = f := rfl

end non_unital_star_alg_hom

namespace star_alg_hom
variables {F R A B : Type*} [comm_semiring R] [semiring A] [algebra R A] [has_star A] [semiring B]
variables [algebra R B] [has_star B] [star_alg_hom_class F R A B]

instance  : has_coe_t F (A →⋆ₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
    map_one' := map_one f,
    commutes' := alg_hom_class.commutes f,
    ..(f : A →⋆ₙₐ[R] B) } }

@[simp, protected] lemma coe_coe (f : F) : ⇑(f : A →⋆ₐ[R] B) = f := rfl

end star_alg_hom

end prerequisites


universes u v

open category_theory

/-- The type of unital C⋆-algebras -/
structure CStarAlg₁ :=
(α : Type u)
[is_normed_ring : normed_ring α]
[is_star_ring : star_ring α]
[is_cstar_ring : cstar_ring α]
[is_normed_algebra : normed_algebra ℂ α]
[is_star_module : star_module ℂ α]
[is_complete_space : complete_space α]

namespace CStarAlg₁

noncomputable instance : inhabited CStarAlg₁ := ⟨⟨ℂ⟩⟩

instance : has_coe_to_sort CStarAlg₁ (Type u) := ⟨CStarAlg₁.α⟩

attribute [instance] is_normed_ring is_star_ring is_cstar_ring is_normed_algebra is_star_module
  is_complete_space

noncomputable instance : category CStarAlg₁.{u} :=
{ hom := λ A B, A →⋆ₐ[ℂ] B,
  id := λ A, star_alg_hom.id ℂ A,
  comp := λ A B C f g, g.comp f }

noncomputable instance : concrete_category CStarAlg₁.{u} :=
{ forget := { obj := λ A, A, map := λ A B f, f },
  forget_faithful := { } }

/-- Construct a bundled `CStarAlg₁` from the underlying typa and appropriate type classes. -/
def of (A : Type u) [normed_ring A] [star_ring A] [cstar_ring A] [normed_algebra ℂ A]
  [star_module ℂ A] [complete_space A] : CStarAlg₁ := ⟨A⟩

@[simp] lemma coe_of (A : Type u) [normed_ring A] [star_ring A] [cstar_ring A] [normed_algebra ℂ A]
  [star_module ℂ A] [complete_space A] : (of A : Type u) = A := rfl

instance forget_normed_ring (A : CStarAlg₁) : normed_ring ((forget CStarAlg₁).obj A) :=
A.is_normed_ring
instance forget_star_ring (A : CStarAlg₁) : star_ring ((forget CStarAlg₁).obj A) :=
A.is_star_ring
instance forget_cstar_ring (A : CStarAlg₁) : cstar_ring ((forget CStarAlg₁).obj A) :=
A.is_cstar_ring
instance forget_normed_algebra (A : CStarAlg₁) : normed_algebra ℂ ((forget CStarAlg₁).obj A) :=
A.is_normed_algebra
instance forget_star_module (A : CStarAlg₁) : star_module ℂ ((forget CStarAlg₁).obj A) :=
A.is_star_module
instance forget_complete_space (A : CStarAlg₁) : complete_space ((forget CStarAlg₁).obj A) :=
A.is_complete_space

/- need more imports for this, and probably we can get stronger statements, like `lipschitz_with 1`
Any morphism of `CStarAlg₁` is continuous.
lemma iso_of_bijective {X Y : CStarAlg₁.{u}} (f : X ⟶ Y) : continuous f :=
map_continuous (f : X →⋆ₐ[ℂ] Y) -/

end CStarAlg₁

namespace star_alg_equiv

/-- Build an isomorphism in the category `CStarAlg₁` from a `star_alg_equiv` between unital
C⋆-algebras -/
@[simps]
noncomputable def to_CStarAlg₁_iso {A B : Type u} [normed_ring A] [star_ring A] [cstar_ring A]
  [normed_algebra ℂ A] [star_module ℂ A] [complete_space A] [normed_ring B] [star_ring B]
  [cstar_ring B] [normed_algebra ℂ B] [star_module ℂ B] [complete_space B]
  (e : A ≃⋆ₐ[ℂ] B) : CStarAlg₁.of A ≅ CStarAlg₁.of B :=
{ hom := (e : A →⋆ₐ[ℂ] B),
  inv := (e.symm : B →⋆ₐ[ℂ] A),
  hom_inv_id' := star_alg_hom.ext $ λ _, e.symm_apply_apply _,
  inv_hom_id' := star_alg_hom.ext $ λ _, e.apply_symm_apply _ }

end star_alg_equiv
