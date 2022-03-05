/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.basic
import topology.local_at_target

universe u

open category_theory opposite topological_space category_theory.limits algebraic_geometry

namespace algebraic_geometry

lemma open_immersion_respects_iso : respects_iso @is_open_immersion :=
by split; { introv H, resetI, apply_instance }

lemma morphism_restrict_base {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) :
  (f ∣_ U).1.base = U.1.res_continuous f.1.base :=
begin
  ext, rw morphism_restrict_base_coe, dsimp, refl
end

lemma Scheme.stalk_map.congr_hom {X Y : Scheme} (f g : X ⟶ Y) (e : f = g) (x : X.carrier) :
  PresheafedSpace.stalk_map f.1 x = eq_to_hom (by subst e) ≫ PresheafedSpace.stalk_map g.1 x :=
by { subst e, exact (category.id_comp _).symm }


lemma is_open_immersion.open_cover_tfae : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
  tfae [is_open_immersion f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      is_open_immersion (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      is_open_immersion (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), is_open_immersion (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      is_open_immersion (pullback.snd : pullback f g ⟶ U),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤),
      ∀ i, is_open_immersion (f ∣_ (U i))] :=
begin
  apply open_cover_tfae_mk,
  { exact open_immersion_respects_iso },
  { introv H,
    simp_rw property_iff_of_is_open_immersion _ open_immersion_respects_iso at H,
    apply_with is_open_immersion.of_stalk_iso { instances := ff },
    rw open_embedding_iff_open_embedding_res_of_supr_eq_top _ (λ i, open_range (𝒰.map i)),
    { intro i, convert (H i).1, dsimp only, rw morphism_restrict_base, refl },
    { rw eq_top_iff, intros x _, erw opens.mem_supr, exact ⟨_, 𝒰.covers x⟩ },
    { continuity },
    { intro x,
      haveI : is_open_immersion (f ∣_ open_range (𝒰.map (𝒰.f (f.val.base x)))) := H _,
      have := Scheme.stalk_map.congr_hom _ _
        (morphism_restrict_ι f (open_range (𝒰.map (𝒰.f (f.val.base x)))))
        ⟨x, 𝒰.covers _⟩,
      conv_lhs at this { erw PresheafedSpace.stalk_map.comp },
      conv_rhs at this { erw PresheafedSpace.stalk_map.comp },
      rw [← is_iso.inv_comp_eq, ← is_iso.comp_inv_eq] at this,
      erw ← this, apply_instance } },
  { intros X Y f U H, exactI infer_instance }
end

lemma target_affine_locally_is_open_immersion :
  target_affine_locally (λ X Y f _, is_open_immersion f) = @is_open_immersion :=
begin
  ext X Y f,
  split,
  { intro H,
    rw (is_open_immersion.open_cover_tfae f).out 0 1,
    refine ⟨Y.affine_cover, _⟩,
    intro i,
    rw property_iff_of_is_open_immersion _ open_immersion_respects_iso,
    exact H ⟨_, range_is_affine_open_of_open_immersion _⟩ },
  { intros H U, exactI infer_instance }
end

lemma is_iso_respects_iso : respects_iso (@is_iso Scheme _) :=
by split; { introv H, resetI, apply_instance }

lemma is_iso.open_cover_tfae : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
  tfae [is_iso f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      is_iso (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      is_iso (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), is_iso (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      is_iso (pullback.snd : pullback f g ⟶ U),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤),
      ∀ i, is_iso (f ∣_ (U i))] :=
begin
  apply open_cover_tfae_mk is_iso_respects_iso,
  { introv H,
    apply_with is_open_immersion.to_iso { instances := ff },
    { rw (is_open_immersion.open_cover_tfae f).out 0 1, use 𝒰, exactI infer_instance },
    { rw Top.epi_iff_surjective,
      simp_rw property_iff_of_is_open_immersion _ is_iso_respects_iso at H,
      rw surjective_iff_surjective_res_of_supr_eq_top _ (λ i, open_range (𝒰.map i)),
      { intro i,
        convert_to (function.surjective (f ∣_ open_range (𝒰.map i)).1.base),
        { dsimp only, rw morphism_restrict_base, refl },
        { rw ← Top.epi_iff_surjective, haveI : is_iso (f ∣_ open_range (𝒰.map i)) := H i,
          apply_instance } },
    { rw eq_top_iff, intros x _, erw opens.mem_supr, exact ⟨_, 𝒰.covers x⟩ },
    { apply_instance } } },
  { intros X Y f U H, exactI infer_instance }
end

lemma target_affine_locally_is_iso :
  target_affine_locally (λ X Y f _, is_iso f) = @is_iso Scheme _ :=
begin
  ext X Y f,
  split,
  { intro H,
    rw (is_iso.open_cover_tfae f).out 0 1,
    refine ⟨Y.affine_cover, _⟩,
    intro i,
    rw property_iff_of_is_open_immersion _ is_iso_respects_iso,
    exact H ⟨_, range_is_affine_open_of_open_immersion _⟩ },
  { intros H U, exactI infer_instance }
end

lemma is_iso_of_is_affine_is_iso {X Y : Scheme} [hX : is_affine X] [hY : is_affine Y] (f : X ⟶ Y)
  [hf : is_iso (f.1.c.app (op ⊤))] : is_iso f :=
begin
  rw ← mem_AffineScheme at hX hY,
  have : is_iso (AffineScheme.Γ.map (@quiver.hom.op AffineScheme _ ⟨X, hX⟩ ⟨Y, hY⟩ f)) := hf,
  have := @@is_iso_of_reflects_iso _ _ _ _ this _,
  exact @@functor.map_is_iso _ _ AffineScheme.forget_to_Scheme _ (@@is_iso_of_op _ _ this)
end


lemma target_affine_locally_affine_and_is_iso :
  target_affine_locally (λ X Y f hY, is_affine X ∧ is_iso (Scheme.Γ.map f.op)) = @is_iso Scheme _ :=
begin
  rw ← target_affine_locally_is_iso,
  congr,
  ext X Y f hY,
  split,
  { rintros ⟨hX, hf⟩, exactI @@is_iso_of_is_affine_is_iso _ _ f hf },
  { intro hf, exactI ⟨is_affine_of_iso f, infer_instance⟩ }
end

end algebraic_geometry
