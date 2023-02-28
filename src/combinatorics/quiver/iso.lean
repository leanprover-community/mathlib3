/-
Copyright (c) 2023 Adam Topaz, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Rémi Bottinelli
-/
import combinatorics.quiver.basic
import combinatorics.quiver.cast
import logic.equiv.basic
import tactic.nth_rewrite
/-!
# Isomorphisms of quivers

Isomorphisms of quivers, defined as pairs of prefunctors that compose to the identities.

## Main definitions

* For quivers `U` and `V`, `iso U V` is the type of isomorphisms between `U` and `V`, with
  associated `iso.refl`, `iso.symm`, and `iso.trans` definitions.
* `iso.of_bijective` is the isomorphism defined by a prefunctor that is bijective on vertices and
  arrows.

## Notation

* `U ≃q V` is notation for `iso U V`

-/

universes u v w z

namespace quiver

/--
An isomorphism of quivers is given by a pair of prefunctors whose two compositions
are the identities.
-/
structure iso (U V : Type*) [quiver.{u+1} U] [quiver.{v+1} V] extends prefunctor U V :=
(inv_prefunctor : V ⥤q U)
(left_inv : to_prefunctor ⋙q inv_prefunctor = 𝟭q _)
(right_inv : inv_prefunctor ⋙q to_prefunctor = 𝟭q _)

infix ` ≃q `:60 := iso

variables {U V W Z : Type*} [quiver.{u+1} U] [quiver.{v+1} V] [quiver.{w+1} W] [quiver.{z+1} Z]

instance : has_coe (iso U V) (prefunctor U V) := ⟨iso.to_prefunctor⟩

namespace iso

/--
Two isomorphisms are equal iff their `to_prefunctor` and `inv_prefunctor` agree.
Not tagged `@[ext]` because `to_prefunctor_ext` will be.
-/
lemma ext (φ ψ : iso U V)
  (hto : φ.to_prefunctor = ψ.to_prefunctor) (hinv : φ.inv_prefunctor = ψ.inv_prefunctor) : φ = ψ :=
by { cases φ, cases ψ, cases hto, cases hinv, refl, }

/-- The identity prefunctor defines an isomorphism. -/
@[simps] def refl (U : Type*) [quiver.{u+1} U] : iso U U := ⟨𝟭q _, 𝟭q _, rfl, rfl⟩

instance : inhabited (iso U U) := ⟨iso.refl U⟩

/-- Swapping `to_prefunctor` and `inv_prefunctor` inverts an isomorphism. -/
@[simps] def symm (φ : iso U V) : iso V U :=
⟨φ.inv_prefunctor, φ.to_prefunctor, φ.right_inv, φ.left_inv⟩

/-- Composing the components of two isomorphisms. -/
@[simps] def trans (φ : iso U V) (ψ : iso V W) : iso U W :=
{ to_prefunctor := φ.to_prefunctor ⋙q ψ.to_prefunctor,
  inv_prefunctor := ψ.inv_prefunctor ⋙q φ.inv_prefunctor,
  left_inv := by
  { rw [←prefunctor.comp_assoc, prefunctor.comp_assoc φ.to_prefunctor,
        ψ.left_inv, prefunctor.comp_id, φ.left_inv], },
  right_inv := by
  { rw [←prefunctor.comp_assoc, prefunctor.comp_assoc ψ.inv_prefunctor,
        φ.right_inv, prefunctor.comp_id, ψ.right_inv], }, }

/--
The equivalence on vertices induced by an isomorphism.
-/
@[simps] def to_equiv (φ : iso U V) : U ≃ V :=
{ to_fun := φ.to_prefunctor.obj,
  inv_fun := φ.inv_prefunctor.obj,
  left_inv := λ x, congr_arg (λ (F : U ⥤q U), F.obj x) φ.left_inv,
  right_inv := λ x, congr_arg (λ (F : V ⥤q V), F.obj x) φ.right_inv }

lemma inv_obj_obj_eq (φ : iso U V) (X : U) : φ.inv_prefunctor.obj (φ.to_prefunctor.obj X) = X :=
φ.to_equiv.left_inv X

lemma obj_inv_obj_eq (φ : iso U V) (X : V) : φ.to_prefunctor.obj (φ.inv_prefunctor.obj X) = X :=
φ.to_equiv.right_inv X

lemma to_obj_injective (φ : iso U V) : φ.to_prefunctor.obj.injective :=
φ.to_equiv.injective

lemma inv_obj_injective (φ : iso U V) : φ.inv_prefunctor.obj.injective :=
φ.symm.to_equiv.injective

/--
The equivalence on arrows `X ⟶ Y ≃ (φ.obj X ⟶ φ.obj Y)` induced by the isomorphism `φ`,
The forward map is `φ.to_prefunctor.map`, but the backward map is the composite of
* `φ.inv_prefunctor.map : φ.obj X ⟶ φ.obj Y → φ.symm.obj (φ.obj X) ⟶ φ.symm.obj (φ.obj Y)`, and
* `hom.equiv_cast _ _ : φ.symm.obj (φ.obj X) ⟶ φ.symm.obj (φ.obj Y) → X ⟶ Y`.
-/
@[simps] def to_equiv_hom (φ : iso U V) {X Y : U} : (X ⟶ Y) ≃ (φ.obj X ⟶ φ.obj Y) :=
{ to_fun := φ.to_prefunctor.map,
  inv_fun := hom.equiv_cast (φ.to_equiv.left_inv X) (φ.to_equiv.left_inv Y) ∘ φ.inv_prefunctor.map,
  left_inv := λ e, by
    begin
      nth_rewrite_rhs 0 ←((prefunctor.id_map _ _ _ e).rec_on $
                           prefunctor.map_cast_eq_of_eq φ.left_inv e),
      simp only [function.comp_app, prefunctor.comp_map, hom.equiv_cast_apply],
      apply hom.cast_congr,
    end,
  right_inv := λ e, by
    begin
      nth_rewrite_rhs 0 ←((prefunctor.id_map _ _ _ e).rec_on $
                           prefunctor.map_cast_eq_of_eq φ.right_inv e),
      simp only [prefunctor.map_cast, function.comp_app, prefunctor.comp_map, hom.equiv_cast_apply],
      apply hom.cast_congr,
    end }

lemma inv_map_map_eq_cast (φ : iso U V) {X Y : U} (f : X ⟶ Y) :
  φ.inv_prefunctor.map (φ.to_prefunctor.map f) =
  f.cast (φ.to_equiv.left_inv X).symm (φ.to_equiv.left_inv Y).symm :=
by { rw ←hom.cast_eq_iff_eq_cast, exact φ.to_equiv_hom.left_inv f, }

lemma map_inv_map_eq_cast (φ : iso U V) {X Y : V} (f : X ⟶ Y) :
  φ.to_prefunctor.map (φ.inv_prefunctor.map f) =
  f.cast (φ.to_equiv.right_inv X).symm (φ.to_equiv.right_inv Y).symm :=
φ.symm.inv_map_map_eq_cast _

/-- The inverse of a bijective (on objects and arrows) prefunctor. -/
@[simps] noncomputable def of_bijective_inverse_aux (φ : U ⥤q V) (hφobj : φ.obj.bijective)
  (hφmap : ∀ (x y : U), (φ.map : (x ⟶ y) → (φ.obj x ⟶ φ.obj y)).bijective ) :
  V ⥤q U :=
let
  Eobj : U ≃ V := equiv.of_bijective _ hφobj,
  Ehom : Π X Y : U, (X ⟶ Y) ≃ (φ.obj X ⟶ φ.obj Y) := λ X Y, equiv.of_bijective _ (hφmap _ _)
in
{ obj := Eobj.symm,
  map := λ X Y, (Ehom _ _).symm ∘ hom.equiv_cast
    (show X = Eobj _, by rw Eobj.apply_symm_apply) (show Y = Eobj _, by rw Eobj.apply_symm_apply) }

/-- A bijective (on objects and arrows) prefunctor defines an isomorphism. -/
noncomputable def of_bijective (φ : U ⥤q V) (hφobj : function.bijective φ.obj)
  (hφmap : ∀ (x y : U), function.bijective (φ.map : (x ⟶ y) → (φ.obj x ⟶ φ.obj y))) :
  iso U V :=
{ to_prefunctor := φ,
  inv_prefunctor := iso.of_bijective_inverse_aux φ hφobj hφmap,
  left_inv := begin
    fapply prefunctor.ext,
    { intros X, simp, },
    { intros X Y f,
      change (equiv.of_bijective φ.map _).symm ((φ.map f).cast _ _) = f.cast _ _,
      generalize_proofs _ _ _ h₄ h₅,
      change (equiv.of_bijective φ.map _).symm
        (hom.cast (congr_arg φ.obj h₄) (congr_arg φ.obj h₅) (φ.map f)) = hom.cast h₄ h₅ f,
      rw ←prefunctor.map_cast,
      apply equiv.of_bijective_symm_apply_apply, },
  end,
  right_inv := begin
    fapply prefunctor.ext,
    { intros X, dsimp, apply (equiv.of_bijective φ.obj hφobj).apply_symm_apply, },
    { intros X Y f, dsimp,
      let Eo := (equiv.of_bijective φ.obj hφobj),
      let E := equiv.of_bijective _ (hφmap (Eo.symm X) (Eo.symm Y)),
      apply E.symm.injective,
      generalize_proofs h1 h2,
      simpa only [equiv.of_bijective_symm_apply_apply, embedding_like.apply_eq_iff_eq], },
  end }

/-- Two isomorphisms agreeing on `.prefunctor` are equal. -/
@[ext] lemma to_prefunctor_ext (φ ψ : iso U V) : φ.to_prefunctor = ψ.to_prefunctor → φ = ψ :=
begin
  refine λ h, iso.ext _ _ h (prefunctor.ext (λ X, ψ.to_equiv.injective _)
                                            (λ X Y f, ψ.to_equiv_hom.injective _)),
  { dsimp,
    rw [ψ.obj_inv_obj_eq X, ←h, φ.obj_inv_obj_eq X], },
  { change ψ.map (φ.inv_prefunctor.map f) = ψ.map ((ψ.inv_prefunctor.map f).cast _ _),
    rw [prefunctor.map_cast, ψ.map_inv_map_eq_cast, hom.cast_cast, ←prefunctor.map_cast_eq_of_eq h,
        φ.map_inv_map_eq_cast, hom.cast_cast], },
end

end iso

end quiver
