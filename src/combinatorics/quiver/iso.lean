import combinatorics.quiver.basic
import combinatorics.quiver.cast
import logic.equiv.basic
import tactic.nth_rewrite

universes u v w z

namespace quiver

structure iso (U V : Type*) [quiver.{u+1} U] [quiver.{v+1} V] extends prefunctor U V :=
(inv_prefunctor : V ⥤q U)
(left_inv : to_prefunctor ⋙q inv_prefunctor = 𝟭q _)
(right_inv : inv_prefunctor ⋙q to_prefunctor = 𝟭q _)

infix ` ≃q `:60 := iso

variables {U V W Z : Type*} [quiver.{u+1} U] [quiver.{v+1} V] [quiver.{w+1} W] [quiver.{z+1} Z]

instance : has_coe (iso U V) (prefunctor U V) := ⟨iso.to_prefunctor⟩

/--
Two isomorphisms are equal iff their `to_prefunctor` and `inv_prefunctor` agree.
Not tagged `@[ext]` because `to_prefunctor_ext` will be.
-/
lemma iso.ext (φ ψ : iso U V)
  (hto : φ.to_prefunctor = ψ.to_prefunctor) (hinv : φ.inv_prefunctor = ψ.inv_prefunctor) : φ = ψ :=
by { cases φ, cases ψ, cases hto, cases hinv, refl, }

/-- The identity prefunctor defines an isomorphism. -/
@[simps] def iso.refl (U : Type*) [quiver.{u+1} U] : iso U U := ⟨𝟭q _, 𝟭q _, rfl, rfl⟩

/-- Swapping `to_prefunctor` and `inv_prefunctor` inverses an iso. -/
@[simps] def iso.symm (φ : iso U V) : iso V U :=
⟨φ.inv_prefunctor, φ.to_prefunctor, φ.right_inv, φ.left_inv⟩

/-- Composing the components of two isos. -/
@[simps] def iso.trans (φ : iso U V) (ψ : iso V W) : iso U W :=
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
@[simps] def iso.to_equiv (φ : iso U V) : U ≃ V :=
{ to_fun := φ.to_prefunctor.obj,
  inv_fun := φ.inv_prefunctor.obj,
  left_inv := λ x, congr_arg (λ (F : U ⥤q U), F.obj x) φ.left_inv,
  right_inv := λ x, congr_arg (λ (F : V ⥤q V), F.obj x) φ.right_inv }

lemma iso.inv_obj_obj_eq (φ : iso U V) (X : U) : φ.inv_prefunctor.obj (φ.to_prefunctor.obj X) = X :=
φ.to_equiv.left_inv X

lemma iso.obj_inv_obj_eq (φ : iso U V) (X : V) : φ.to_prefunctor.obj (φ.inv_prefunctor.obj X) = X :=
φ.to_equiv.right_inv X

/--
The equivalence on arrows `X ⟶ Y ≃ (φ.obj X ⟶ φ.obj Y)` induced by the isomorphism `φ`,
The forward map is `φ.to_prefunctor.map`, but the backward map is the composite of
* `φ.inv_prefunctor.map : φ.obj X ⟶ φ.obj Y → φ.symm.obj (φ.obj X) ⟶ φ.symm.obj (φ.obj Y)`, and
* `hom.equiv_cast _ _ : φ.symm.obj (φ.obj X) ⟶ φ.symm.obj (φ.obj Y) → X ⟶ Y`.
-/
@[simps] def iso.to_equiv_hom (φ : iso U V) {X Y : U} : (X ⟶ Y) ≃ (φ.obj X ⟶ φ.obj Y) :=
{ to_fun := φ.to_prefunctor.map,
  inv_fun := hom.equiv_cast (φ.to_equiv.left_inv X) (φ.to_equiv.left_inv Y) ∘ φ.inv_prefunctor.map,
  left_inv := λ e, by
    begin
      nth_rewrite_rhs 0 ←((prefunctor.id_map _ _ _ e).rec_on $
                           prefunctor.map_cast_eq_of_eq φ.left_inv e),
      simp only [function.comp_app, prefunctor.comp_map, hom.equiv_cast_apply],
      apply hom.cast_irrelevant,
    end,
  right_inv := λ e, by
    begin
      nth_rewrite_rhs 0 ←((prefunctor.id_map _ _ _ e).rec_on $
                           prefunctor.map_cast_eq_of_eq φ.right_inv e),
      simp only [prefunctor.map_cast, function.comp_app, prefunctor.comp_map, hom.equiv_cast_apply],
      apply hom.cast_irrelevant,
    end }

@[simp] def iso.to_equiv_hom' (φ : iso U V) {X Y : V} :
  (X ⟶ Y) ≃ (φ.symm.obj X ⟶ φ.symm.obj Y) := φ.symm.to_equiv_hom

lemma iso.inv_map_map_eq_cast (φ : iso U V) {X Y : U} (f : X ⟶ Y) :
  φ.inv_prefunctor.map (φ.to_prefunctor.map f) =
  f.cast (φ.to_equiv.left_inv X).symm (φ.to_equiv.left_inv Y).symm :=
by { rw ←hom.cast_eq_iff_eq_cast, exact φ.to_equiv_hom.left_inv f, }

lemma iso.map_inv_map_eq_cast (φ : iso U V) {X Y : V} (f : X ⟶ Y) :
  φ.to_prefunctor.map (φ.inv_prefunctor.map f) =
  f.cast (φ.to_equiv.right_inv X).symm (φ.to_equiv.right_inv Y).symm :=
φ.symm.inv_map_map_eq_cast _

-- Thanks Adam Topaz
@[simps]
noncomputable
def iso.of_bijective_inverse_aux (φ : U ⥤q V) (hφobj : φ.obj.bijective)
  (hφmap : ∀ (x y : U), (φ.map : (x ⟶ y) → (φ.obj x ⟶ φ.obj y)).bijective ) :
  V ⥤q U :=
let
  Eobj : U ≃ V := equiv.of_bijective _ hφobj,
  Ehom : Π X Y : U, (X ⟶ Y) ≃ (φ.obj X ⟶ φ.obj Y) := λ X Y, equiv.of_bijective _ (hφmap _ _)
in
{ obj := Eobj.symm,
  map := λ X Y, (Ehom _ _).symm ∘ hom.equiv_cast
    (show X = Eobj _, by rw Eobj.apply_symm_apply) (show Y = Eobj _, by rw Eobj.apply_symm_apply) }

-- Thanks Adam Topaz
noncomputable def iso.of_bijective (φ : U ⥤q V) (hφobj : function.bijective φ.obj)
  (hφmap : ∀ (x y : U), function.bijective (φ.map : (x ⟶ y) → (φ.obj x ⟶ φ.obj y)) ) :
  iso U V :=
{ to_prefunctor := φ,
  inv_prefunctor := iso.of_bijective_inverse_aux φ hφobj hφmap,
  left_inv := begin
    fapply prefunctor.ext,
    { intros X, simp, },
    { intros X Y f,
      dsimp,
      generalize_proofs h _ _ h1 h2,
      induction h1,
      induction h2,
      change (equiv.of_bijective _ h).symm (φ.map f) = f,
      simp only [equiv.of_bijective_symm_apply_apply], },
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

lemma iso.to_prefunctor_obj_injective (φ : iso U V) : φ.to_prefunctor.obj.injective :=
φ.to_equiv.injective

lemma iso.inv_prefunctor_obj_injective (φ : iso U V) : φ.inv_prefunctor.obj.injective :=
φ.symm.to_equiv.injective

@[ext]
lemma iso.to_prefunctor_ext (φ ψ : iso U V) : φ.to_prefunctor = ψ.to_prefunctor → φ = ψ :=
begin
  rintro h,
  apply iso.ext _ _ h,
  fapply prefunctor.ext,
  { rintro X,
    apply ψ.to_equiv.injective,
    change ψ.to_prefunctor.obj (φ.inv_prefunctor.obj X) =
           ψ.to_prefunctor.obj (ψ.inv_prefunctor.obj X),
    rw [ψ.obj_inv_obj_eq X, ←h, φ.obj_inv_obj_eq X], },
  { rintro X Y f,
    apply ψ.to_equiv_hom.injective,
    change ψ.to_prefunctor.map (φ.inv_prefunctor.map f) =
           ψ.to_prefunctor.map ((ψ.inv_prefunctor.map f).cast _ _),
    rw [prefunctor.map_cast, ψ.map_inv_map_eq_cast, hom.cast_cast, ←prefunctor.map_cast_eq_of_eq h,
        φ.map_inv_map_eq_cast, hom.cast_cast], },
end

end quiver
