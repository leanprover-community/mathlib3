/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.Spec
import algebra.category.Ring.constructions

/-!
# The category of schemes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism of schemes is just a morphism of the underlying locally ringed spaces.

-/

noncomputable theory

open topological_space
open category_theory
open Top
open opposite

namespace algebraic_geometry

/--
We define `Scheme` as a `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that that the restriction of `X` to `U` is isomorphic,
as a locally ringed space, to `Spec.to_LocallyRingedSpace.obj (op R)`
for some `R : CommRing`.
-/
structure Scheme extends to_LocallyRingedSpace : LocallyRingedSpace :=
(local_affine : ∀ x : to_LocallyRingedSpace, ∃ (U : open_nhds x) (R : CommRing),
  nonempty (to_LocallyRingedSpace.restrict U.open_embedding ≅
    Spec.to_LocallyRingedSpace.obj (op R)))

namespace Scheme

/-- A morphism between schemes is a morphism between the underlying locally ringed spaces. -/
@[nolint has_nonempty_instance] -- There isn't nessecarily a morphism between two schemes.
def hom (X Y : Scheme) : Type* :=
X.to_LocallyRingedSpace ⟶ Y.to_LocallyRingedSpace

/--
Schemes are a full subcategory of locally ringed spaces.
-/
instance : category Scheme :=
{ hom := hom, ..(induced_category.category Scheme.to_LocallyRingedSpace) }

/-- The structure sheaf of a Scheme. -/
protected abbreviation sheaf (X : Scheme) := X.to_SheafedSpace.sheaf

/-- The forgetful functor from `Scheme` to `LocallyRingedSpace`. -/
@[simps, derive[full, faithful]]
def forget_to_LocallyRingedSpace : Scheme ⥤ LocallyRingedSpace :=
  induced_functor _

@[simp] lemma forget_to_LocallyRingedSpace_preimage {X Y : Scheme} (f : X ⟶ Y) :
  Scheme.forget_to_LocallyRingedSpace.preimage f = f := rfl

/-- The forgetful functor from `Scheme` to `Top`. -/
@[simps]
def forget_to_Top : Scheme ⥤ Top :=
  Scheme.forget_to_LocallyRingedSpace ⋙ LocallyRingedSpace.forget_to_Top

@[simp]
lemma id_val_base (X : Scheme) : (𝟙 X : _).1.base = 𝟙 _ := rfl

@[simp] lemma id_app {X : Scheme} (U : (opens X.carrier)ᵒᵖ) :
  (𝟙 X : _).val.c.app U = X.presheaf.map
    (eq_to_hom (by { induction U using opposite.rec, cases U, refl })) :=
PresheafedSpace.id_c_app X.to_PresheafedSpace U

@[reassoc]
lemma comp_val {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).val = f.val ≫ g.val := rfl

@[reassoc, simp]
lemma comp_coe_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).val.base = f.val.base ≫ g.val.base := rfl

@[reassoc, elementwise]
lemma comp_val_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).val.base = f.val.base ≫ g.val.base := rfl

@[reassoc, simp]
lemma comp_val_c_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (f ≫ g).val.c.app U = g.val.c.app U ≫ f.val.c.app _ := rfl

lemma congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U) :
  f.val.c.app U = g.val.c.app U ≫ X.presheaf.map (eq_to_hom (by subst e)) :=
by { subst e, dsimp, simp }

lemma app_eq {X Y : Scheme} (f : X ⟶ Y) {U V : opens Y.carrier} (e : U = V) :
  f.val.c.app (op U) = Y.presheaf.map (eq_to_hom e.symm).op ≫
    f.val.c.app (op V) ≫ X.presheaf.map (eq_to_hom (congr_arg (opens.map f.val.base).obj e)).op :=
begin
  rw [← is_iso.inv_comp_eq, ← functor.map_inv, f.val.c.naturality, presheaf.pushforward_obj_map],
  congr
end
instance is_LocallyRingedSpace_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] :
  @is_iso LocallyRingedSpace _ _ _ f :=
forget_to_LocallyRingedSpace.map_is_iso f

@[simp]
lemma inv_val_c_app {X Y : Scheme} (f : X ⟶ Y) [is_iso f] (U : opens X.carrier) :
  (inv f).val.c.app (op U) = X.presheaf.map (eq_to_hom $ by { rw is_iso.hom_inv_id, ext1, refl } :
    (opens.map (f ≫ inv f).1.base).obj U ⟶ U).op ≫
      inv (f.val.c.app (op $ (opens.map _).obj U)) :=
begin
  rw [is_iso.eq_comp_inv],
  erw ← Scheme.comp_val_c_app,
  rw [Scheme.congr_app (is_iso.hom_inv_id f),
    Scheme.id_app, ← functor.map_comp, eq_to_hom_trans, eq_to_hom_op],
  refl
end

/-- Given a morphism of schemes `f : X ⟶ Y`, and open sets `U ⊆ Y`, `V ⊆ f ⁻¹' U`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, V)`. -/
abbreviation hom.app_le {X Y : Scheme}
  (f : X ⟶ Y) {V : opens X.carrier} {U : opens Y.carrier} (e : V ≤ (opens.map f.1.base).obj U) :
    Y.presheaf.obj (op U) ⟶ X.presheaf.obj (op V) :=
f.1.c.app (op U) ≫ X.presheaf.map (hom_of_le e).op

/--
The spectrum of a commutative ring, as a scheme.
-/
def Spec_obj (R : CommRing) : Scheme :=
{ local_affine := λ x,
  ⟨⟨⊤, trivial⟩, R, ⟨(Spec.to_LocallyRingedSpace.obj (op R)).restrict_top_iso⟩⟩,
  to_LocallyRingedSpace := Spec.LocallyRingedSpace_obj R }

@[simp] lemma Spec_obj_to_LocallyRingedSpace (R : CommRing) :
  (Spec_obj R).to_LocallyRingedSpace = Spec.LocallyRingedSpace_obj R := rfl

/--
The induced map of a ring homomorphism on the ring spectra, as a morphism of schemes.
-/
def Spec_map {R S : CommRing} (f : R ⟶ S) :
  Spec_obj S ⟶ Spec_obj R :=
(Spec.LocallyRingedSpace_map f : Spec.LocallyRingedSpace_obj S ⟶ Spec.LocallyRingedSpace_obj R)

@[simp] lemma Spec_map_id (R : CommRing) :
  Spec_map (𝟙 R) = 𝟙 (Spec_obj R) :=
Spec.LocallyRingedSpace_map_id R

lemma Spec_map_comp {R S T : CommRing} (f : R ⟶ S) (g : S ⟶ T) :
  Spec_map (f ≫ g) = Spec_map g ≫ Spec_map f :=
Spec.LocallyRingedSpace_map_comp f g

/--
The spectrum, as a contravariant functor from commutative rings to schemes.
-/
@[simps] def Spec : CommRingᵒᵖ ⥤ Scheme :=
{ obj := λ R, Spec_obj (unop R),
  map := λ R S f, Spec_map f.unop,
  map_id' := λ R, by rw [unop_id, Spec_map_id],
  map_comp' := λ R S T f g, by rw [unop_comp, Spec_map_comp] }

/--
The empty scheme.
-/
@[simps]
def {u} empty : Scheme.{u} :=
{ carrier := Top.of pempty,
  presheaf := (category_theory.functor.const _).obj (CommRing.of punit),
  is_sheaf := presheaf.is_sheaf_of_is_terminal _ CommRing.punit_is_terminal,
  local_ring := λ x, pempty.elim x,
  local_affine := λ x, pempty.elim x }

instance : has_emptyc Scheme := ⟨empty⟩

instance : inhabited Scheme := ⟨∅⟩

/--
The global sections, notated Gamma.
-/
def Γ : Schemeᵒᵖ ⥤ CommRing :=
(induced_functor Scheme.to_LocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ

lemma Γ_def : Γ = (induced_functor Scheme.to_LocallyRingedSpace).op ⋙ LocallyRingedSpace.Γ := rfl

@[simp] lemma Γ_obj (X : Schemeᵒᵖ) : Γ.obj X = (unop X).presheaf.obj (op ⊤) := rfl

lemma Γ_obj_op (X : Scheme) : Γ.obj (op X) = X.presheaf.obj (op ⊤) := rfl

@[simp] lemma Γ_map {X Y : Schemeᵒᵖ} (f : X ⟶ Y) :
  Γ.map f = f.unop.1.c.app (op ⊤) := rfl

lemma Γ_map_op {X Y : Scheme} (f : X ⟶ Y) :
  Γ.map f.op = f.1.c.app (op ⊤) := rfl

section basic_open

variables (X : Scheme) {V U : opens X.carrier} (f g : X.presheaf.obj (op U))

/-- The subset of the underlying space where the given section does not vanish. -/
def basic_open : opens X.carrier := X.to_LocallyRingedSpace.to_RingedSpace.basic_open f

@[simp]
lemma mem_basic_open (x : U) : ↑x ∈ X.basic_open f ↔ is_unit (X.presheaf.germ x f) :=
RingedSpace.mem_basic_open _ _ _

@[simp]
lemma mem_basic_open_top (f : X.presheaf.obj (op ⊤)) (x : X.carrier) :
  x ∈ X.basic_open f ↔ is_unit (X.presheaf.germ (⟨x, trivial⟩ : (⊤ : opens _)) f) :=
RingedSpace.mem_basic_open _ f ⟨x, trivial⟩

@[simp]
lemma basic_open_res (i : op U ⟶ op V) :
  X.basic_open (X.presheaf.map i f) = V ⊓ X.basic_open f :=
RingedSpace.basic_open_res _ i f

-- This should fire before `basic_open_res`.
@[simp, priority 1100]
lemma basic_open_res_eq (i : op U ⟶ op V) [is_iso i] :
  X.basic_open (X.presheaf.map i f) = X.basic_open f :=
RingedSpace.basic_open_res_eq _ i f

@[sheaf_restrict]
lemma basic_open_le : X.basic_open f ≤ U :=
RingedSpace.basic_open_le _ _

@[simp]
lemma preimage_basic_open {X Y : Scheme} (f : X ⟶ Y) {U : opens Y.carrier}
  (r : Y.presheaf.obj $ op U) :
  (opens.map f.1.base).obj (Y.basic_open r) =
    @Scheme.basic_open X ((opens.map f.1.base).obj U) (f.1.c.app _ r) :=
LocallyRingedSpace.preimage_basic_open f r

@[simp]
lemma basic_open_zero (U : opens X.carrier) : X.basic_open (0 : X.presheaf.obj $ op U) = ⊥ :=
LocallyRingedSpace.basic_open_zero _ U

@[simp]
lemma basic_open_mul : X.basic_open (f * g) = X.basic_open f ⊓ X.basic_open g :=
RingedSpace.basic_open_mul _ _ _

lemma basic_open_of_is_unit {f : X.presheaf.obj (op U)} (hf : is_unit f) : X.basic_open f = U :=
RingedSpace.basic_open_of_is_unit _ hf

end basic_open

end Scheme

lemma basic_open_eq_of_affine {R : CommRing} (f : R) :
  (Scheme.Spec.obj $ op R).basic_open ((Spec_Γ_identity.app R).inv f) =
    prime_spectrum.basic_open f :=
begin
  ext,
  erw Scheme.mem_basic_open_top,
  suffices : is_unit (structure_sheaf.to_stalk R x f) ↔ f ∉ prime_spectrum.as_ideal x,
  { exact this },
  erw [← is_unit_map_iff (structure_sheaf.stalk_to_fiber_ring_hom R x),
    structure_sheaf.stalk_to_fiber_ring_hom_to_stalk],
  exact (is_localization.at_prime.is_unit_to_map_iff
    (localization.at_prime (prime_spectrum.as_ideal x)) (prime_spectrum.as_ideal x) f : _)
end

@[simp]
lemma basic_open_eq_of_affine' {R : CommRing}
  (f : (Spec.to_SheafedSpace.obj (op R)).presheaf.obj (op ⊤)) :
  (Scheme.Spec.obj $ op R).basic_open f =
    prime_spectrum.basic_open ((Spec_Γ_identity.app R).hom f) :=
begin
  convert basic_open_eq_of_affine ((Spec_Γ_identity.app R).hom f),
  exact (iso.hom_inv_id_apply _ _).symm
end

end algebraic_geometry
