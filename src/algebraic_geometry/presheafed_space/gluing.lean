/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.gluing
import algebraic_geometry.presheafed_space.has_colimits
import category_theory.limits.shapes.binary_products

/-!
# Gluing Topological spaces

Given a family of gluing data, consisting of
1. An index type `ι`
2. A topological space `U i` for each `i : ι`.
3. An open subset `V i j ⊆ U i` for each `i j : ι`.
4. A transition map `f i j : V i j ⟶ V j i` for each `i j : ι`.
such that
5. `V i i = U i`.
6. `f i i` is the identity.
7. `f i j x ∈ V j k` for all `x ∈ V i j ∩ V i k`.
8. `f i j ≫ f j k = f i k`.

We can then glue the topological spaces `U i` along `V i j`.

THe construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `Top.gluing_data`: A structure containing the family of gluing data.
* `Top.gluing_data.glued`: The glued topological space.
    This is defined as the coequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API can
    be used.
* `Top.gluing_data.imm`: The immersion `imm i : U i ⟶ glued` for each `i : ι`.
* `Top.gluing_data.rel`: A relation on `Σ i, D.U i` defined by `⟨i, x⟩ ~ ⟨j, y⟩` iff
    `⟨i, x⟩ = ⟨j, y⟩` or `f i j x = y`. See `Top.gluing_data.imm_eq_iff_rel`.

## Main results

* `Top.gluing_data.is_open_iff`: A set in `glued` is open iff its preimage along each `imm i` is
    open.
* `Top.gluing_data.imm_jointly_surjective`: The `imm i`s are jointly surjective.
* `Top.gluing_data.glue_condition` : `f i j ≫ imm j = imm i`.
* `Top.gluing_data.rel_equiv`: `rel` is an equivalence relation.
* `Top.gluing_data.imm_eq_iff_rel`: `imm i x = imm j y ↔ ⟨i, x⟩ ~ ⟨j, y⟩`.
* `Top.gluing_data.image_inter`: The intersection of the images of `U i` and `U j` in `glued` is
    `V i j`.
* `Top.gluing_data.preimage_range`: The preimage of the image of `U i` in `U j` is `V i j`.
* `Top.gluing_data.preimage_image_eq_preimage_f`: The preimage of the image of some `U ⊆ U i` is
    given by the preimage along `f j i`.
* `Top.gluing_data.imm_open_embedding`: Each of the `imm i`s are open embeddings.

-/

noncomputable theory

open topological_space category_theory
open category_theory.limits
namespace algebraic_geometry

universes v u

variables (C : Type u) [category.{v} C]

-- instance has_lift_to_open (U : Top) (V : opens U) :
--   has_lift ((opens.to_Top U).obj V) U := ⟨λ x, x.val⟩
def restrict_comp {X Y : Top} {Z : PresheafedSpace C} {f : X ⟶ Y} {g : Y ⟶ Z.1}
  (hf : open_embedding f) (hg : open_embedding g) :
  Z.restrict (f ≫ g) (hg.comp hf) ≅ ((Z.restrict _ hg).restrict _ hf) :=
{ hom := { base := 𝟙 _, c :=
  { app := λ U, Z.presheaf.map (eq_to_hom (sorry /-by simp [is_open_map.functor, ←set.image_comp]-/)),
    naturality' := λ X Y f,
    begin sorry
      -- dsimp only [PresheafedSpace.restrict],
      -- simp only [quiver.hom.unop_op, Top.presheaf.pushforward_obj_map,
      --   functor.comp_map, functor.op_map, ←functor.map_comp],
      -- congr
    end } },
  inv := { base := 𝟙 _, c :=
  { app := λ U, Z.presheaf.map (eq_to_hom (sorry /-by simp [is_open_map.functor, ←set.image_comp]-/)),
    naturality' := λ X Y f,
    begin sorry
      -- dsimp only [PresheafedSpace.restrict],
      -- simp only [quiver.hom.unop_op, Top.presheaf.pushforward_obj_map,
      --   functor.comp_map, functor.op_map, ←functor.map_comp],
      -- congr
    end } },
  hom_inv_id' := by { unfold category_struct.comp PresheafedSpace.comp, simp, congr, },
  inv_hom_id' := _ }

structure open_immersion {C : Type*} [category C] {X Y : PresheafedSpace C} (f : X ⟶ Y) :=
(base_open : open_embedding f.base)
(c_iso : X ≅ Y.restrict _ base_open)
(fac : c_iso.hom ≫ Y.of_restrict _ _ = f)

def has_pullback_of_open_immersion {C : Type*} [category C] {X Y Z : PresheafedSpace C}
  {f : X ⟶ Z} (hf : open_immersion f) {g : Y ⟶ Z} (hg : open_immersion g) : pullback_cone f g :=
begin
 fapply pullback_cone.mk,
 exact Z.restrict _ (Top.open_embedding_of_pullback_open_embeddings hf.base_open hg.base_open),
  -- split,split,split,swap,split,swap,
end

/--
A family of gluing data consists of
1. An index type `ι`
2. A topological space `U i` for each `i : ι`.
3. An open subset `V i j ⊆ U i` for each `i j : ι`.
4. A transition map `f i j : V i j ⟶ V j i` for each `i j : ι`.
such that
5. `V i i = U i`.
6. `f i i` is the identity.
7. `f i j x ∈ V j k` for all `x ∈ V i j ∩ V i k`.
8. `f i j ≫ f j k = f i k`.

We can then glue the topological spaces `U i` along `V i j`.
-/
@[nolint has_inhabited_instance]
structure glue_data : Type (max u v + 1) :=
  (ι : Type u)
  (U : ι → PresheafedSpace C)
  (V : ι × ι → PresheafedSpace C)
  (f : Π i j, V (i, j) ⟶ U i)
  (f_open : ∀ i j, open_immersion (f i j))
  (f_id : ∀ i, is_iso (f i i))
  (t : Π i j, V (i, j) ⟶ V (j, i))
  (t_id : ∀ i, t i i = 𝟙 _)
  (t' : Π i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i))
  (t_fac : ∀ i j k, t' i j k ≫ pullback.snd = pullback.fst ≫ t i j)
  (cocycle : ∀ i j k , t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _)

attribute [simp] glue_data.V_id glue_data.f_id

namespace glue_data

variable (D : glue_data.{u})

-- @[simp, reassoc, elementwise] lemma inv (i j : D.ι) :
--   D.f i j ≫ D.f j i = 𝟙 _ :=
-- begin
--   ext x,
--   change ↑(D.f j i (D.f i j x)) = ↑x,
--   have := D.cocycle i j i x (by simp),
--   rw f_id at this,
--   convert this,
--   ext, refl,
-- end

-- /-- (Implementation) The disjoint union of `U i`. -/
-- def sigma_opens : Top := ∐ D.U

-- /-- (Implementation) The family of `V i j` as topological spaces indexed by `ι × ι`. -/
-- def inters : D.ι × D.ι → Top := (λ p : D.ι × D.ι, (opens.to_Top _).obj (D.V p.1 p.2))

-- /-- (Implementation) The disjoint union of `V i j`. -/
-- def sigma_inters : Top := ∐ D.inters

-- /-- (Implementation) The projection `∐ D.inters ⟶ ∐ D.U` via left projection. -/
-- def left_imm : D.sigma_inters ⟶ D.sigma_opens :=
-- sigma.desc (λ p : D.ι × D.ι, opens.inclusion _ ≫ sigma.ι _ p.1)

-- /-- (Implementation) The projection `∐ D.inters ⟶ ∐ D.U` via right projection. -/
-- def right_imm : D.sigma_inters ⟶ D.sigma_opens :=
-- sigma.desc (λ p : D.ι × D.ι, D.f p.1 p.2 ≫ opens.inclusion _ ≫ sigma.ι _ p.2)

-- /-- (Implementation) The diagram to take colimit of. -/
-- def diagram := parallel_pair D.left_imm D.right_imm

-- /-- The glued topological space given a family of gluing data. -/
-- def glued : Top :=
-- coequalizer D.left_imm D.right_imm

-- /-- (Implementation) The projection `∐ D.U ⟶ D.glued` given by the colimit. -/
-- def π : D.sigma_opens ⟶ D.glued :=
-- coequalizer.π _ _

-- instance π_epi : epi D.π :=
-- coequalizer.π_epi

-- lemma π_surjective : function.surjective D.π :=
-- (Top.epi_iff_surjective D.π).mp infer_instance

-- /-- The open immersion `D.U i ⟶ D.glued` for each `i`. -/
-- def imm (i : D.ι) : D.U i ⟶ D.glued :=
-- sigma.ι _ _ ≫ D.π

-- lemma is_open_iff (U : set D.glued) : is_open U ↔ ∀ i, is_open (D.imm i ⁻¹' U) :=
-- by { rw [coequalizer_is_open_iff, colimit_is_open_iff], refl }


-- lemma imm_jointly_surjective (x : D.glued) : ∃ i (y : D.U i), D.imm i y = x :=
-- begin
--   rcases D.π_surjective x with ⟨x', rfl⟩,
--   rw ← (show (coprod_iso_sigma _).inv _ = x', from congr_fun (coprod_iso_sigma _).hom_inv_id x'),
--   rcases (coprod_iso_sigma _).hom x' with ⟨i, y⟩,
--   exact ⟨i, y, by simpa⟩
-- end

-- @[simp]
-- lemma glue_condition (i j : D.ι) :
--   D.f i j ≫ opens.inclusion _ ≫ D.imm j = opens.inclusion _ ≫ D.imm i :=
-- begin
--   ext x,
--   symmetry,
--   simpa [π, left_imm, right_imm] using
--     continuous_map.congr_fun (coequalizer.condition D.left_imm D.right_imm)
--       ((sigma.ι D.inters (i, j) : _) x),
-- end

-- @[simp] lemma glue_condition_apply (i j : D.ι) (x) :
--   D.imm j ↑(D.f i j x) = D.imm i ↑x :=
-- continuous_map.congr_fun (D.glue_condition i j) x

-- /--
-- An equivalence relation on `Σ i, D.U i` that holds iff `D.imm i x = D.imm j x`.
-- See `Top.gluing_data.imm_eq_iff_rel`.
-- -/
-- inductive rel : (Σ i, D.U i) → (Σ i, D.U i) → Prop
-- | refl (x : Σ i, D.U i) : rel x x
-- | eq {i j : D.ι} (x : D.V i j) (y : D.V j i) (h : D.f i j x = y) : rel ⟨i, x⟩ ⟨j, y⟩

-- lemma rel_equiv : equivalence D.rel :=
-- ⟨ rel.refl,
--   λ x y h, by { cases h, exact h, apply rel.eq, simp [←h_h] },
--   λ _ _ _ h₁ h₂, by
--   { cases h₁ with _ i j x y, exact h₂,
--     cases x with x hx, cases y with y hy,
--     cases h₂ with _ _ k z _, exact h₁,
--     cases h₂_h,
--     cases z with z hz,
--     dsimp at *,
--     have eq : x = ↑(D.f j i ⟨z, hy⟩) := by simp [←h₁_h],
--     refine rel.eq ⟨x, _⟩ ⟨(↑(D.f j k ⟨z, _⟩) : D.U k), _⟩ _; cases eq,
--     { apply D.f_inter, exact hz },
--     { apply D.f_inter, exact hy },
--     { ext, apply D.cocycle } } ⟩

-- open category_theory.limits.walking_parallel_pair

-- lemma eqv_gen_of_π_eq {x y : ∐ D.U} (h : D.π x = D.π y) :
--   eqv_gen (types.coequalizer_rel (D.left_imm) (D.right_imm)) x y :=
-- begin
--   change colimit.ι D.diagram one x = colimit.ι D.diagram one y at h,
--   have : colimit.ι (D.diagram ⋙ forget _) one x = colimit.ι (D.diagram ⋙ forget _) one y,
--   { rw ←ι_preserves_colimits_iso_hom,
--     simp[h] },
--   have :
--     (colimit.ι (D.diagram ⋙ forget _) _ ≫ colim.map _ ≫ (colimit.iso_colimit_cocone _).hom) _ =
--     (colimit.ι (D.diagram ⋙ forget _) _ ≫ colim.map _ ≫ (colimit.iso_colimit_cocone _).hom) _ :=
--     (congr_arg (colim.map (diagram_iso_parallel_pair (D.diagram ⋙ forget _)).hom
--     ≫ (colimit.iso_colimit_cocone (types.coequalizer_limit _ _)).hom) this : _),
--   simp only [eq_to_hom_refl, types_comp_apply, colimit.ι_map_assoc,
--     diagram_iso_parallel_pair_hom_app, colimit.iso_colimit_cocone_ι_hom, types_id_apply] at this,
--   exact quot.eq.1 this,
-- end

-- lemma inv_image.equivalence {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β)
--   (h : equivalence r) : equivalence (inv_image r f) :=
-- ⟨λ _, h.1 _, λ _ _ x, h.2.1 x, inv_image.trans r f h.2.2⟩

-- lemma imm_eq_iff_rel (i j : D.ι) (x : D.U i) (y : D.U j) :
--   D.imm i x = D.imm j y ↔ D.rel ⟨i, x⟩ ⟨j, y⟩ :=
-- begin
--   split,
--   { intro h,
--     rw ← (show _ = sigma.mk i x, from congr_fun (coprod_iso_sigma D.U).inv_hom_id _),
--     rw ← (show _ = sigma.mk j y, from congr_fun (coprod_iso_sigma D.U).inv_hom_id _),
--     change inv_image D.rel (coprod_iso_sigma D.U).hom _ _,
--     simp only [Top.coprod_iso_sigma_inv_app],
--     rw ←relation.eqv_gen_iff_of_equivalence (inv_image.equivalence _ _ D.rel_equiv),
--     refine relation.eqv_gen_mono _ (D.eqv_gen_of_π_eq h : _),
--     rintros _ _ ⟨x⟩,
--     rw ← (show (coprod_iso_sigma _).inv _ = x, from congr_fun (coprod_iso_sigma _).hom_inv_id x),
--     generalize : (coprod_iso_sigma D.inters).hom x = x',
--     cases x',
--     unfold inv_image left_imm right_imm,
--     simp only [opens.inclusion_to_fun, Top.comp_app, coprod_iso_sigma_inv_app,
--       category_theory.limits.colimit.ι_desc_apply, cofan.mk_ι_app,
--       coprod_iso_sigma_hom_app, continuous_map.to_fun_eq_coe],
--     apply rel.eq,
--     simp },
--   { rintro (⟨⟩ | ⟨_, _, x,_,rfl⟩),
--     refl, simp }
-- end

-- lemma imm_injective (i : D.ι) : function.injective (D.imm i) :=
-- begin
--   intros x y h,
--   rcases (D.imm_eq_iff_rel _ _ _ _).mp h with (_ | ⟨_,_,_,_,rfl⟩); simp,
-- end

-- instance imm_mono (i : D.ι) : mono (D.imm i) :=
-- (Top.mono_iff_injective _).mpr (D.imm_injective _)

-- lemma image_inter (i j : D.ι) :
--   set.range (D.imm i) ∩ set.range (D.imm j) = D.imm i '' D.V i j :=
-- begin
--   ext x,
--   split,
--   { rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩,
--   have := (D.imm_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm),
--   cases this with _ _ _ x y h,
--   exact ⟨x₁, by simp, eq₁⟩,
--   exact ⟨x, x.property, eq₁⟩ },
--   { rintro ⟨x, hx, rfl⟩,
--     split, simp,
--     exact ⟨↑(D.f i j ⟨x, hx⟩), continuous_map.congr_fun (D.glue_condition i j) ⟨x, hx⟩⟩ }
-- end

-- lemma preimage_range (i j : D.ι) :
--   D.imm j ⁻¹' (set.range (D.imm i)) = D.V j i :=
-- by rw [←set.preimage_image_eq ↑(D.V j i) (D.imm_injective j),
--        ←image_inter, set.preimage_range_inter]

-- lemma preimage_image_eq_preimage_f (i j : D.ι) (U : set (D.U i)) :
-- D.imm j ⁻¹' (D.imm i '' U) = opens.inclusion _ '' ((D.f j i ≫ opens.inclusion _) ⁻¹' U) :=
-- begin
--   have : coe ⁻¹' (D.imm j ⁻¹' (D.imm i '' U)) = (D.f j i ≫ opens.inclusion _) ⁻¹' U,
--   { ext x,
--     conv_rhs { rw ← set.preimage_image_eq U (D.imm_injective _) },
--     generalize : D.imm i '' U = U',
--     simp },
--   change _ = coe '' _,
--   rw [←this, subtype.image_preimage_coe, subtype.val_eq_coe],
--   symmetry,
--   apply set.inter_eq_self_of_subset_left,
--   rw ← D.preimage_range i j,
--   exact set.preimage_mono (set.image_subset_range _ _),
-- end

-- lemma open_image_open (i : D.ι) (U : opens (D.U i)) : is_open (D.imm i '' U) :=
-- begin
--   rw is_open_iff,
--   intro j,
--   rw preimage_image_eq_preimage_f,
--   apply (opens.open_embedding _).is_open_map,
--   apply (D.f j i ≫ (D.V i j).inclusion).continuous_to_fun.is_open_preimage,
--   exact U.property
-- end

-- lemma imm_open_embedding (i : D.ι) : open_embedding (D.imm i) :=
-- open_embedding_of_continuous_injective_open
--   (D.imm i).continuous_to_fun (D.imm_injective i) (λ U h, D.open_image_open i ⟨U, h⟩)

end glue_data

end algebraic_geometry
