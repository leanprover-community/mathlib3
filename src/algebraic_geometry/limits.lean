/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.pullbacks
import algebraic_geometry.AffineScheme
import category_theory.limits.constructions.finite_products_of_binary_products
import category_theory.limits.constructions.equalizers

/-!
# (Co)Limits of Schemes

We construct various limits and colimits in the category of schemes.

* The existence of fibred products was shown in `algebraic_geometry/pullbacks.lean`.
* `Spec ℤ` is the terminal object.
* The preceding two results imply that `Scheme` has all finite limits.
* The empty scheme is the (strict) initial object.
* Coproducts exists (and the forgetful functors preserve them).

-/

universe u

open category_theory category_theory.limits opposite topological_space

namespace algebraic_geometry

lemma Scheme.is_iso_iff {X Y : Scheme} (f : X ⟶ Y) :
  is_iso f ↔ is_iso f.1.base ∧ is_iso f.1.c :=
begin
  split,
  { intro H, resetI, split; apply_instance },
  { rintro ⟨H₁, H₂⟩,
    exactI @@is_iso_of_reflects_iso _ _ f (Scheme.forget_to_LocallyRingedSpace ⋙
      LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace)
      (PresheafedSpace.is_iso_of_components f.1 : _) _ }
end

lemma is_open_immersion.to_iso {X Y : Scheme} (f : X ⟶ Y) [h : is_open_immersion f]
  [epi f.1.base] : is_iso f :=
@@is_iso_of_reflects_iso _ _ f (Scheme.forget_to_LocallyRingedSpace ⋙
  LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace)
  (@@PresheafedSpace.is_open_immersion.to_iso _ f.1 h _) _

lemma is_open_immersion.of_stalk_iso {X Y : Scheme} (f : X ⟶ Y) (hf : open_embedding f.1.base)
  [∀ x, is_iso (PresheafedSpace.stalk_map f.1 x)] : is_open_immersion f :=
SheafedSpace.is_open_immersion.of_stalk_iso f.1 hf

instance {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) [is_open_immersion f] :
  is_open_immersion (f ∣_ U) := by { delta morphism_restrict, apply_instance }

lemma is_open_immersion_iff_stalk_iso {X Y : Scheme} (f : X ⟶ Y) :
  is_open_immersion f ↔ open_embedding f.1.base ∧ ∀ x, is_iso (PresheafedSpace.stalk_map f.1 x) :=
⟨λ H, ⟨H.1, by exactI infer_instance⟩, λ ⟨h₁, h₂⟩, @@is_open_immersion.of_stalk_iso f h₁ h₂⟩

lemma is_iso_iff_is_open_immersion {X Y : Scheme} (f : X ⟶ Y) :
  is_iso f ↔ is_open_immersion f ∧ epi f.1.base :=
⟨λ H, by exactI ⟨infer_instance, infer_instance⟩, λ ⟨h₁, h₂⟩, @@is_open_immersion.to_iso f h₁ h₂⟩

lemma is_iso_iff_stalk_iso {X Y : Scheme} (f : X ⟶ Y) :
  is_iso f ↔ is_iso f.1.base ∧ ∀ x, is_iso (PresheafedSpace.stalk_map f.1 x) :=
begin
  rw [is_iso_iff_is_open_immersion, is_open_immersion_iff_stalk_iso, and_comm, ← and_assoc],
  refine and_congr ⟨_, _⟩ iff.rfl,
  { rintro ⟨h₁, h₂⟩,
    convert_to is_iso (Top.iso_of_homeo (homeomorph.homeomorph_of_continuous_open
      (equiv.of_bijective _ ⟨h₂.inj, (Top.epi_iff_surjective _).mp h₁⟩)
      h₂.continuous h₂.is_open_map)).hom,
    { ext, refl },
    { apply_instance } },
  { intro H, exactI ⟨infer_instance, (Top.homeo_of_iso (as_iso f.1.base)).open_embedding⟩ }
end

lemma has_finite_limits_of_has_terminal_has_pullbacks
  {C : Type*} [category C] [has_terminal C] [has_pullbacks C] : has_finite_limits C :=
@@finite_limits_from_equalizers_and_finite_products _
  (@@has_finite_products_of_has_binary_and_terminal _
    (has_binary_products_of_terminal_and_pullbacks C) infer_instance)
  (@@has_equalizers_of_pullbacks_and_binary_products _
    (has_binary_products_of_terminal_and_pullbacks C) infer_instance)

noncomputable
def Spec_Z_is_terminal : is_terminal (Scheme.Spec.obj (op $ CommRing.of ℤ)) :=
(terminal_op_of_initial CommRing.Z_is_initial).is_terminal_obj Scheme.Spec _

instance : has_terminal Scheme := has_terminal_of_has_terminal_of_preserves_limit Scheme.Spec

instance : is_affine (⊤_ Scheme.{u}) :=
is_affine_of_iso (preserves_terminal.iso Scheme.Spec).inv

instance : has_finite_limits Scheme :=
has_finite_limits_of_has_terminal_has_pullbacks

section initial

def sheaf_of_is_terminal {C A : Type*} [category C] [category A] (J : grothendieck_topology C)
  {X : A} (hX : is_terminal X) :
  Sheaf J A :=
{ val := (category_theory.functor.const _).obj X,
  cond := λ _ _ _ _ _ _, ⟨hX.from _, λ _ _ _, hX.hom_ext _ _, λ _ _, hX.hom_ext _ _⟩ }

@[simps]
def Scheme_empty : Scheme.{u} :=
{ carrier := Top.of pempty,
  presheaf := (category_theory.functor.const _).obj (CommRing.of punit),
  is_sheaf := by { apply Top.presheaf.is_sheaf_spaces_of_is_sheaf_sites,
    exact (sheaf_of_is_terminal _ CommRing.punit_is_terminal).cond },
  local_ring := λ x, pempty.elim x,
  local_affine := λ x, pempty.elim x }

@[simps]
def Scheme_empty_to (X : Scheme.{u}) : Scheme_empty ⟶ X :=
⟨{ base := ⟨λ x, pempty.elim x, by continuity⟩,
    c := { app := λ U, CommRing.punit_is_terminal.from _ } }, λ x, pempty.elim x⟩

@[ext]
def Scheme_empty_ext {X : Scheme.{u}} (f g : Scheme_empty ⟶ X) : f = g :=
by { ext x, exact pempty.elim x }

@[simp]
lemma Scheme_empty_to_eq {X : Scheme.{u}} (f : Scheme_empty ⟶ X) : f = Scheme_empty_to _ :=
Scheme_empty_ext f (Scheme_empty_to X)

instance (X : Scheme.{u}) : unique (Scheme_empty ⟶ X) :=
⟨⟨Scheme_empty_to _⟩, λ _, Scheme_empty_ext _ _⟩

def empty_is_initial : is_initial Scheme_empty :=
is_initial.of_unique _

@[simp]
lemma empty_is_initial_to : empty_is_initial.to = Scheme_empty_to := rfl

instance : is_empty (Scheme.Spec.obj (op $ CommRing.of punit)).carrier :=
⟨prime_spectrum.punit⟩

lemma is_open_immersion_of_is_empty {X Y : Scheme} (f : X ⟶ Y) [is_empty X.carrier] :
  is_open_immersion f :=
begin
  apply_with is_open_immersion.of_stalk_iso { instances := ff },
  { apply open_embedding_of_continuous_injective_open,
    { continuity },
    { rintro (i : X.carrier), exact is_empty_elim i },
    { intros U hU, convert is_open_empty, ext, apply (iff_false _).mpr,
      exact λ x, is_empty_elim (show X.carrier, from x.some) } },
  { rintro (i : X.carrier), exact is_empty_elim i }
end

instance {X : Scheme} : is_open_immersion (empty_is_initial.to X) :=
@@is_open_immersion_of_is_empty _ (by exact pempty.is_empty)

lemma is_iso_of_is_empty {X Y : Scheme} (f : X ⟶ Y) [is_empty Y.carrier] : is_iso f :=
begin
  haveI : is_empty X.carrier := ⟨λ x, is_empty_elim (show Y.carrier, from f.1.base x)⟩,
  apply_with is_open_immersion.to_iso { instances := ff },
  { apply is_open_immersion_of_is_empty },
  { rw Top.epi_iff_surjective, rintro (x : Y.carrier), exact is_empty_elim x }
end

instance : is_iso (empty_is_initial.to (Scheme.Spec.obj (op $ CommRing.of punit))) :=
is_iso_of_is_empty _

noncomputable
def Spec_punit_is_initial : is_initial (Scheme.Spec.obj (op $ CommRing.of punit)) :=
empty_is_initial.of_iso (as_iso $ empty_is_initial.to _)

instance : is_affine Scheme_empty :=
is_affine_of_iso (empty_is_initial.to (Scheme.Spec.obj (op $ CommRing.of punit)))

instance : has_initial Scheme :=
has_initial_of_unique Scheme_empty

instance : is_affine (⊥_ Scheme) :=
is_affine_of_iso (is_initial.unique_up_to_iso initial_is_initial empty_is_initial).hom

instance initial_is_empty : is_empty (⊥_ Scheme).carrier :=
⟨λ x, ((initial.to Scheme_empty : _).1.base x).elim⟩

instance (X : Scheme) : is_open_immersion (initial.to X) :=
is_open_immersion_of_is_empty _

lemma bot_is_affine_open (X : Scheme) : is_affine_open (⊥ : opens X.carrier) :=
begin
  convert range_is_affine_open_of_open_immersion (initial.to X),
  ext,
  exact (false_iff _).mpr (λ x, is_empty_elim (show (⊥_ Scheme).carrier, from x.some)),
end

instance : has_strict_initial_objects Scheme :=
has_strict_initial_objects_of_initial_is_strict (λ A f, is_iso_of_is_empty f)

end initial

section coproduct

-- by showing that the coproducts of schemes in the category of locally ringed spaces is a scheme
-- (presumably using `LocallyRingedSpace.is_open_immersion.Scheme`),
-- or by showing that gluing with empty intersection is the coproduct.
instance : has_coproducts Scheme.{u} := sorry

instance (I : Type*) :
  preserves_colimits_of_shape (discrete.{u} I) Scheme.forget_to_LocallyRingedSpace.{u} := sorry

noncomputable
instance (I : Type*) :
  preserves_colimits_of_shape (discrete.{u} I) Scheme.forget_to_Top.{u} :=
by { delta Scheme.forget_to_Top LocallyRingedSpace.forget_to_Top, apply_instance }

end coproduct

end algebraic_geometry
