/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.basic
import category_theory.single_obj
import category_theory.limits.functor_category
import category_theory.limits.preserves.basic
import category_theory.adjunction.limits
import category_theory.monoidal.functor_category
import category_theory.monoidal.transport
import category_theory.monoidal.rigid.of_equivalence
import category_theory.monoidal.rigid.functor_category
import category_theory.monoidal.linear
import category_theory.monoidal.braided
import category_theory.abelian.functor_category
import category_theory.abelian.transfer
import category_theory.conj
import category_theory.linear.functor_category

/-!
# `Action V G`, the category of actions of a monoid `G` inside some category `V`.

The prototypical example is `V = Module R`,
where `Action (Module R) G` is the category of `R`-linear representations of `G`.

We check `Action V G ≌ (single_obj G ⥤ V)`,
and construct the restriction functors `res {G H : Mon} (f : G ⟶ H) : Action V H ⥤ Action V G`.

* When `V` has (co)limits so does `Action V G`.
* When `V` is monoidal, braided, or symmetric, so is `Action V G`.
* When `V` is preadditive, linear, or abelian so is `Action V G`.
-/

universes u

open category_theory
open category_theory.limits

variables (V : Type (u+1)) [large_category V]

/--
An `Action V G` represents a bundled action of
the monoid `G` on an object of some category `V`.

As an example, when `V = Module R`, this is an `R`-linear representation of `G`,
while when `V = Type` this is a `G`-action.
-/
-- Note: this is _not_ a categorical action of `G` on `V`.
structure Action (G : Mon.{u}) :=
(V : V)
(ρ : G ⟶ Mon.of (End V))

namespace Action
variable {V}

@[simp]
lemma ρ_one {G : Mon.{u}} (A : Action V G) : A.ρ 1 = 𝟙 A.V :=
by { rw [monoid_hom.map_one], refl, }

/-- When a group acts, we can lift the action to the group of automorphisms. -/
@[simps]
def ρ_Aut {G : Group.{u}} (A : Action V (Mon.of G)) : G ⟶ Group.of (Aut A.V) :=
{ to_fun := λ g,
  { hom := A.ρ g,
    inv := A.ρ (g⁻¹ : G),
    hom_inv_id' := ((A.ρ).map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_self, ρ_one]),
    inv_hom_id' := ((A.ρ).map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_self, ρ_one]), },
  map_one' := by { ext, exact A.ρ.map_one },
  map_mul' := λ x y, by { ext, exact A.ρ.map_mul x y }, }

variable (G : Mon.{u})

section

/-- The trivial representation of a group. -/
def trivial : Action AddCommGroup G :=
{ V := AddCommGroup.of punit,
  ρ := 1, }

instance : inhabited (Action AddCommGroup G) := ⟨trivial G⟩
end

variables {G V}

/--
A homomorphism of `Action V G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
structure hom (M N : Action V G) :=
(hom : M.V ⟶ N.V)
(comm' : ∀ g : G, M.ρ g ≫ hom = hom ≫ N.ρ g . obviously)

restate_axiom hom.comm'

namespace hom

/-- The identity morphism on a `Action V G`. -/
@[simps]
def id (M : Action V G) : Action.hom M M :=
{ hom := 𝟙 M.V }

instance (M : Action V G) : inhabited (Action.hom M M) := ⟨id M⟩

/--
The composition of two `Action V G` homomorphisms is the composition of the underlying maps.
-/
@[simps]
def comp {M N K : Action V G} (p : Action.hom M N) (q : Action.hom N K) :
  Action.hom M K :=
{ hom := p.hom ≫ q.hom,
  comm' := λ g, by rw [←category.assoc, p.comm, category.assoc, q.comm, ←category.assoc] }

end hom

instance : category (Action V G) :=
{ hom := λ M N, hom M N,
  id := λ M, hom.id M,
  comp := λ M N K f g, hom.comp f g, }

@[simp]
lemma id_hom (M : Action V G) : (𝟙 M : hom M M).hom = 𝟙 M.V := rfl
@[simp]
lemma comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) :
  (f ≫ g : hom M K).hom = f.hom ≫ g.hom :=
rfl

/-- Construct an isomorphism of `G` actions/representations
from an isomorphism of the the underlying objects,
where the forward direction commutes with the group action. -/
@[simps]
def mk_iso {M N : Action V G} (f : M.V ≅ N.V) (comm : ∀ g : G, M.ρ g ≫ f.hom = f.hom ≫ N.ρ g) :
  M ≅ N :=
{ hom :=
  { hom := f.hom,
    comm' := comm, },
  inv :=
  { hom := f.inv,
    comm' := λ g, by { have w := comm g =≫ f.inv, simp at w, simp [w], }, }}

namespace functor_category_equivalence

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def functor : Action V G ⥤ (single_obj G ⥤ V) :=
{ obj := λ M,
  { obj := λ _, M.V,
    map := λ _ _ g, M.ρ g,
    map_id' := λ _, M.ρ.map_one,
    map_comp' := λ _ _ _ g h, M.ρ.map_mul h g, },
  map := λ M N f,
  { app := λ _, f.hom,
    naturality' := λ _ _ g, f.comm g, } }

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def inverse : (single_obj G ⥤ V) ⥤ Action V G :=
{ obj := λ F,
  { V := F.obj punit.star,
    ρ :=
    { to_fun := λ g, F.map g,
      map_one' := F.map_id punit.star,
      map_mul' := λ g h, F.map_comp h g, } },
  map := λ M N f,
  { hom := f.app punit.star,
    comm' := λ g, f.naturality g, } }.

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def unit_iso : 𝟭 (Action V G) ≅ functor ⋙ inverse :=
nat_iso.of_components (λ M, mk_iso ((iso.refl _)) (by tidy)) (by tidy).

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def counit_iso : inverse ⋙ functor ≅ 𝟭 (single_obj G ⥤ V) :=
nat_iso.of_components (λ M, nat_iso.of_components (by tidy) (by tidy)) (by tidy).

end functor_category_equivalence

section
open functor_category_equivalence

variables (V G)

/--
The category of actions of `G` in the category `V`
is equivalent to the functor category `single_obj G ⥤ V`.
-/
def functor_category_equivalence : Action V G ≌ (single_obj G ⥤ V) :=
{ functor := functor,
  inverse := inverse,
  unit_iso := unit_iso,
  counit_iso := counit_iso, }

attribute [simps] functor_category_equivalence

instance [has_finite_products V] : has_finite_products (Action V G) :=
{ out := λ J _ _, by exactI
  adjunction.has_limits_of_shape_of_equivalence (Action.functor_category_equivalence _ _).functor }

instance [has_limits V] : has_limits (Action V G) :=
adjunction.has_limits_of_equivalence (Action.functor_category_equivalence _ _).functor

instance [has_colimits V] : has_colimits (Action V G) :=
adjunction.has_colimits_of_equivalence (Action.functor_category_equivalence _ _).functor

end

section forget

variables (V G)

/-- (implementation) The forgetful functor from bundled actions to the underlying objects.

Use the `category_theory.forget` API provided by the `concrete_category` instance below,
rather than using this directly.
-/
@[simps]
def forget : Action V G ⥤ V :=
{ obj := λ M, M.V,
  map := λ M N f, f.hom, }

instance : faithful (forget V G) :=
{ map_injective' := λ X Y f g w, hom.ext _ _ w, }

instance [concrete_category V] : concrete_category (Action V G) :=
{ forget := forget V G ⋙ (concrete_category.forget V), }

instance has_forget_to_V [concrete_category V] : has_forget₂ (Action V G) V :=
{ forget₂ := forget V G }

/-- The forgetful functor is intertwined by `functor_category_equivalence` with
evaluation at `punit.star`. -/
def functor_category_equivalence_comp_evaluation :
  (functor_category_equivalence V G).functor ⋙ (evaluation _ _).obj punit.star ≅ forget V G :=
iso.refl _

noncomputable instance [has_limits V] : limits.preserves_limits (forget V G) :=
limits.preserves_limits_of_nat_iso
  (Action.functor_category_equivalence_comp_evaluation V G)

noncomputable instance [has_colimits V] : preserves_colimits (forget V G) :=
preserves_colimits_of_nat_iso
  (Action.functor_category_equivalence_comp_evaluation V G)

-- TODO construct categorical images?

end forget

lemma iso.conj_ρ {M N : Action V G} (f : M ≅ N) (g : G) :
   N.ρ g = (((forget V G).map_iso f).conj (M.ρ g)) :=
by { rw [iso.conj_apply, iso.eq_inv_comp], simp [f.hom.comm'] }

section has_zero_morphisms
variables [has_zero_morphisms V]

instance : has_zero_morphisms (Action V G) :=
{ has_zero := λ X Y, ⟨⟨0, by tidy⟩⟩, }

instance : functor.preserves_zero_morphisms (functor_category_equivalence V G).functor := {}

end has_zero_morphisms

section preadditive
variables [preadditive V]

instance : preadditive (Action V G) :=
{ hom_group := λ X Y,
  { zero := ⟨0, by simp⟩,
    add := λ f g, ⟨f.hom + g.hom, by simp [f.comm, g.comm]⟩,
    neg := λ f, ⟨-f.hom, by simp [f.comm]⟩,
    zero_add := by { intros, ext, exact zero_add _, },
    add_zero := by { intros, ext, exact add_zero _, },
    add_assoc := by { intros, ext, exact add_assoc _ _ _, },
    add_left_neg := by { intros, ext, exact add_left_neg _, },
    add_comm := by { intros, ext, exact add_comm _ _, }, },
  add_comp' := by { intros, ext, exact preadditive.add_comp _ _ _ _ _ _, },
  comp_add' := by { intros, ext, exact preadditive.comp_add _ _ _ _ _ _, }, }

instance : functor.additive (functor_category_equivalence V G).functor := {}

@[simp] lemma zero_hom {X Y : Action V G} : (0 : X ⟶ Y).hom = 0 := rfl
@[simp] lemma neg_hom {X Y : Action V G} (f : X ⟶ Y) : (-f).hom = -f.hom := rfl
@[simp] lemma add_hom {X Y : Action V G} (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := rfl

end preadditive

section linear
variables [preadditive V] {R : Type*} [semiring R] [linear R V]

instance : linear R (Action V G) :=
{ hom_module := λ X Y,
  { smul := λ r f, ⟨r • f.hom, by simp [f.comm]⟩,
    one_smul := by { intros, ext, exact one_smul _ _, },
    smul_zero := by { intros, ext, exact smul_zero _, },
    zero_smul := by { intros, ext, exact zero_smul _ _, },
    add_smul := by { intros, ext, exact add_smul _ _ _, },
    smul_add := by { intros, ext, exact smul_add _ _ _, },
    mul_smul := by { intros, ext, exact mul_smul _ _ _, }, },
  smul_comp' := by { intros, ext, exact linear.smul_comp _ _ _ _ _ _, },
  comp_smul' := by { intros, ext, exact linear.comp_smul _ _ _ _ _ _, }, }

instance : functor.linear R (functor_category_equivalence V G).functor := {}

@[simp] lemma smul_hom {X Y : Action V G} (r : R) (f : X ⟶ Y) : (r • f).hom = r • f.hom := rfl

end linear

section abelian
/-- Auxilliary construction for the `abelian (Action V G)` instance. -/
def abelian_aux : Action V G ≌ (ulift.{u} (single_obj G) ⥤ V) :=
(functor_category_equivalence V G).trans (equivalence.congr_left ulift.equivalence)

noncomputable instance [abelian V] : abelian (Action V G) :=
abelian_of_equivalence abelian_aux.functor

end abelian

section monoidal
variables [monoidal_category V]

instance : monoidal_category (Action V G) :=
monoidal.transport (Action.functor_category_equivalence _ _).symm

@[simp] lemma tensor_V {X Y : Action V G} : (X ⊗ Y).V = X.V ⊗ Y.V := rfl
@[simp] lemma tensor_rho {X Y : Action V G} {g : G} : (X ⊗ Y).ρ g = X.ρ g ⊗ Y.ρ g := rfl
@[simp] lemma tensor_hom {W X Y Z : Action V G} (f : W ⟶ X) (g : Y ⟶ Z) :
  (f ⊗ g).hom = f.hom ⊗ g.hom := rfl
@[simp] lemma associator_hom_hom {X Y Z : Action V G} :
  hom.hom (α_ X Y Z).hom = (α_ X.V Y.V Z.V).hom :=
begin
  dsimp [monoidal.transport_associator],
  simp,
end
@[simp] lemma associator_inv_hom {X Y Z : Action V G} :
  hom.hom (α_ X Y Z).inv = (α_ X.V Y.V Z.V).inv :=
begin
  dsimp [monoidal.transport_associator],
  simp,
end
@[simp] lemma left_unitor_hom_hom {X : Action V G} :
  hom.hom (λ_ X).hom = (λ_ X.V).hom :=
begin
  dsimp [monoidal.transport_left_unitor],
  simp,
end
@[simp] lemma left_unitor_inv_hom {X : Action V G} :
  hom.hom (λ_ X).inv = (λ_ X.V).inv :=
begin
  dsimp [monoidal.transport_left_unitor],
  simp,
end
@[simp] lemma right_unitor_hom_hom {X : Action V G} :
  hom.hom (ρ_ X).hom = (ρ_ X.V).hom :=
begin
  dsimp [monoidal.transport_right_unitor],
  simp,
end
@[simp] lemma right_unitor_inv_hom {X : Action V G} :
  hom.hom (ρ_ X).inv = (ρ_ X.V).inv :=
begin
  dsimp [monoidal.transport_right_unitor],
  simp,
end

variables (V G)

/-- When `V` is monoidal the forgetful functor `Action V G` to `V` is monoidal. -/
@[simps]
def forget_monoidal : monoidal_functor (Action V G) V :=
{ ε := 𝟙 _,
  μ := λ X Y, 𝟙 _,
  ..Action.forget _ _, }

instance forget_monoidal_faithful : faithful (forget_monoidal V G).to_functor :=
by { change faithful (forget V G), apply_instance, }

section
variables [braided_category V]

instance : braided_category (Action V G) :=
braided_category_of_faithful (forget_monoidal V G) (λ X Y, mk_iso (β_ _ _) (by tidy)) (by tidy)

/-- When `V` is braided the forgetful functor `Action V G` to `V` is braided. -/
@[simps]
def forget_braided : braided_functor (Action V G) V :=
{ ..forget_monoidal _ _, }

instance forget_braided_faithful : faithful (forget_braided V G).to_functor :=
by { change faithful (forget V G), apply_instance, }

end

instance [symmetric_category V] : symmetric_category (Action V G) :=
symmetric_category_of_faithful (forget_braided V G)

section
local attribute [simp] monoidal_preadditive.tensor_add monoidal_preadditive.add_tensor

variables [preadditive V] [monoidal_preadditive V]

instance : monoidal_preadditive (Action V G) := {}

variables {R : Type*} [semiring R] [linear R V] [monoidal_linear R V]

instance : monoidal_linear R (Action V G) := {}

end

variables (V G)
noncomputable theory

/-- Upgrading the functor `Action V G ⥤ (single_obj G ⥤ V)` to a monoidal functor. -/
def functor_category_monoidal_equivalence : monoidal_functor (Action V G) (single_obj G ⥤ V) :=
monoidal.from_transported (Action.functor_category_equivalence _ _).symm

instance : is_equivalence ((functor_category_monoidal_equivalence V G).to_functor) :=
by { change is_equivalence (Action.functor_category_equivalence _ _).functor, apply_instance, }

variables (H : Group.{u})

instance [right_rigid_category V] : right_rigid_category (single_obj (H : Mon.{u}) ⥤ V) :=
by { change right_rigid_category (single_obj H ⥤ V), apply_instance }

/-- If `V` is right rigid, so is `Action V G`. -/
instance [right_rigid_category V] : right_rigid_category (Action V H) :=
right_rigid_category_of_equivalence (functor_category_monoidal_equivalence V _)

instance [rigid_category V] : rigid_category (single_obj (H : Mon.{u}) ⥤ V) :=
by { change rigid_category (single_obj H ⥤ V), apply_instance }

/-- If `V` is rigid, so is `Action V G`. -/
instance [rigid_category V] : rigid_category (Action V H) :=
rigid_category_of_equivalence (functor_category_monoidal_equivalence V _)

end monoidal

/-- Actions/representations of the trivial group are just objects in the ambient category. -/
def Action_punit_equivalence : Action V (Mon.of punit) ≌ V :=
{ functor := forget V _,
  inverse :=
  { obj := λ X, ⟨X, 1⟩,
    map := λ X Y f, ⟨f, λ ⟨⟩, by simp⟩, },
  unit_iso := nat_iso.of_components (λ X, mk_iso (iso.refl _) (λ ⟨⟩, by simpa using ρ_one X))
    (by tidy),
  counit_iso := nat_iso.of_components (λ X, iso.refl _) (by tidy), }

variables (V)
/--
The "restriction" functor along a monoid homomorphism `f : G ⟶ H`,
taking actions of `H` to actions of `G`.

(This makes sense for any homomorphism, but the name is natural when `f` is a monomorphism.)
-/
@[simps]
def res {G H : Mon} (f : G ⟶ H) : Action V H ⥤ Action V G :=
{ obj := λ M,
  { V := M.V,
    ρ := f ≫ M.ρ },
  map := λ M N p,
  { hom := p.hom,
    comm' := λ g, p.comm (f g) } }

/--
The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `Action V G`.
-/
def res_id {G : Mon} : res V (𝟙 G) ≅ 𝟭 (Action V G) :=
nat_iso.of_components (λ M, mk_iso (iso.refl _) (by tidy)) (by tidy)

attribute [simps] res_id

/--
The natural isomorphism from the composition of restrictions along homomorphisms
to the restriction along the composition of homomorphism.
-/
def res_comp {G H K : Mon} (f : G ⟶ H) (g : H ⟶ K) : res V g ⋙ res V f ≅ res V (f ≫ g) :=
nat_iso.of_components (λ M, mk_iso (iso.refl _) (by tidy)) (by tidy)

attribute [simps] res_comp

-- TODO promote `res` to a pseudofunctor from
-- the locally discrete bicategory constructed from `Monᵒᵖ` to `Cat`, sending `G` to `Action V G`.

variables {G} {H : Mon.{u}} (f : G ⟶ H)

instance res_additive [preadditive V] : (res V f).additive := {}

variables {R : Type*} [semiring R]

instance res_linear [preadditive V] [linear R V] : (res V f).linear R := {}

end Action

namespace category_theory.functor

variables {V} {W : Type (u+1)} [large_category W]

/-- A functor between categories induces a functor between
the categories of `G`-actions within those categories. -/
@[simps]
def map_Action (F : V ⥤ W) (G : Mon.{u}) : Action V G ⥤ Action W G :=
{ obj := λ M,
  { V := F.obj M.V,
    ρ :=
    { to_fun := λ g, F.map (M.ρ g),
      map_one' := by simp only [End.one_def, Action.ρ_one, F.map_id],
      map_mul' := λ g h, by simp only [End.mul_def, F.map_comp, map_mul], }, },
  map := λ M N f,
  { hom := F.map f.hom,
    comm' := λ g, by { dsimp, rw [←F.map_comp, f.comm, F.map_comp], }, },
  map_id' := λ M, by { ext, simp only [Action.id_hom, F.map_id], },
  map_comp' := λ M N P f g, by { ext, simp only [Action.comp_hom, F.map_comp], }, }

variables (F : V ⥤ W) (G : Mon.{u}) [preadditive V] [preadditive W]

instance map_Action_preadditive [F.additive] : (F.map_Action G).additive := {}

variables {R : Type*} [semiring R] [category_theory.linear R V] [category_theory.linear R W]

instance map_Action_linear [F.additive] [F.linear R] : (F.map_Action G).linear R := {}

end category_theory.functor
