/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.limits.creates
import category_theory.sites.sheaf

/-!

# Limits and colimits of sheaves

## Limits

We prove that the forgetful functor from `Sheaf J D` to presheaves creates limits.
If the target category `D` has limits (of a certain shape),
this then implies that `Sheaf J D` has limits of the same shape and that the forgetful
functor preserves these limits.

## Colimits

PROJECT: Prove the existence of colimits, using sheafification.

-/
namespace category_theory.Sheaf

open category_theory
open category_theory.limits
open opposite

section limits

universes w v u
variables {C : Type (max v u)} [category.{v} C] {J : grothendieck_topology C}
variables {D : Type w} [category.{max v u} D]
variables {K : Type (max v u)} [small_category K]

noncomputable theory

section


/-- An auxiliary definition to be used below.

Whenever `E` is a cone of shape `K` of sheaves, and `S` is the multifork associated to a
covering `W` of an object `X`, with respect to the cone point `E.X`, this provides a cone of
shape `K` of objects in `D`, with cone point `S.X`.

See `is_limit_multifork_of_is_limit` for more on how this definition is used.
-/
def multifork_evaluation_cone (F : K ⥤ Sheaf J D)
  (E : cone (F ⋙ Sheaf_to_presheaf J D)) (X : C) (W : J.cover X) (S : multifork (W.index E.X)) :
  cone (F ⋙ Sheaf_to_presheaf J D ⋙ (evaluation Cᵒᵖ D).obj (op X)) :=
{ X := S.X,
  π :=
  { app := λ k, (presheaf.is_limit_of_is_sheaf J (F.obj k).1 W (F.obj k).2).lift $
      multifork.of_ι _ S.X (λ i, S.ι i ≫ (E.π.app k).app (op i.Y)) begin
        intros i,
        simp only [category.assoc],
        erw [← (E.π.app k).naturality, ← (E.π.app k).naturality],
        dsimp,
        simp only [← category.assoc],
        congr' 1,
        apply S.condition,
      end,
    naturality' := begin
      intros i j f,
      dsimp [presheaf.is_limit_of_is_sheaf],
      rw [category.id_comp],
      apply presheaf.is_sheaf.hom_ext (F.obj j).2 W,
      intros ii,
      erw [presheaf.is_sheaf.amalgamate_map],
      rw [category.assoc, ← (F.map f).naturality, ← category.assoc],
      erw [presheaf.is_sheaf.amalgamate_map],
      dsimp [multifork.of_ι],
      rw [category.assoc, ← E.w f],
      simp,
    end } }


variables [has_limits_of_shape K D]

/-- If `E` is a cone of shape `K` of sheaves, which is a limit on the level of presheves,
this definition shows that the limit presheaf satisfies the multifork variant of the sheaf
condition, at a given covering `W`.

This is used below in `is_sheaf_of_is_limit` to show that the limit presheaf is indeed a sheaf.
-/
def is_limit_multifork_of_is_limit (F : K ⥤ Sheaf J D)
  (E : cone (F ⋙ Sheaf_to_presheaf J D))
  (hE : is_limit E) (X : C) (W : J.cover X) : is_limit (W.multifork E.X) :=
multifork.is_limit.mk _
(λ S, (is_limit_of_preserves ((evaluation Cᵒᵖ D).obj (op X)) hE).lift $
  multifork_evaluation_cone F E X W S)
begin
  intros S i,
  apply (is_limit_of_preserves ((evaluation Cᵒᵖ D).obj (op i.Y)) hE).hom_ext,
  intros k,
  dsimp [multifork.of_ι],
  erw [category.assoc, (E.π.app k).naturality],
  dsimp,
  rw ← category.assoc,
  erw (is_limit_of_preserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac
    (multifork_evaluation_cone F E X W S),
  dsimp [multifork_evaluation_cone, presheaf.is_limit_of_is_sheaf],
  erw presheaf.is_sheaf.amalgamate_map,
  refl,
end
begin
  intros S m hm,
  apply (is_limit_of_preserves ((evaluation Cᵒᵖ D).obj (op X)) hE).hom_ext,
  intros k,
  dsimp,
  erw (is_limit_of_preserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac,
  apply presheaf.is_sheaf.hom_ext (F.obj k).2 W,
  intros i,
  erw presheaf.is_sheaf.amalgamate_map,
  dsimp [multifork.of_ι],
  change _ = S.ι i ≫ _,
  erw [← hm, category.assoc, ← (E.π.app k).naturality, category.assoc],
  refl,
end

/-- If `E` is a cone which is a limit on the level of presheaves,
then the limit presheaf is again a sheaf.

This is used to show that the forgetful functor from sheaves to presheaves creates limits.
-/
lemma is_sheaf_of_is_limit (F : K ⥤ Sheaf J D) (E : cone (F ⋙ Sheaf_to_presheaf J D))
  (hE : is_limit E) : presheaf.is_sheaf J E.X :=
begin
  rw presheaf.is_sheaf_iff_multifork,
  intros X S,
  exact ⟨is_limit_multifork_of_is_limit _ _ hE _ _⟩,
end

instance (F : K ⥤ Sheaf J D) : creates_limit F (Sheaf_to_presheaf J D) :=
creates_limit_of_reflects_iso $ λ E hE,
{ lifted_cone := ⟨⟨E.X, is_sheaf_of_is_limit _ _ hE⟩, ⟨E.π.app, E.π.naturality⟩⟩,
  valid_lift := cones.ext (eq_to_iso rfl) $ λ j, by { dsimp, simp },
  makes_limit :=
  { lift := λ S, hE.lift ((Sheaf_to_presheaf J D).map_cone S),
    fac' := λ S j, hE.fac ((Sheaf_to_presheaf J D).map_cone S) j,
    uniq' := λ S m hm, hE.uniq ((Sheaf_to_presheaf J D).map_cone S) m hm } }

instance : creates_limits_of_shape K (Sheaf_to_presheaf J D) := {}

instance : has_limits_of_shape K (Sheaf J D) :=
has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape (Sheaf_to_presheaf J D)

end

instance [has_limits D] : creates_limits (Sheaf_to_presheaf J D) := {}

instance [has_limits D] : has_limits (Sheaf J D) :=
has_limits_of_has_limits_creates_limits (Sheaf_to_presheaf J D)

end limits

end category_theory.Sheaf
