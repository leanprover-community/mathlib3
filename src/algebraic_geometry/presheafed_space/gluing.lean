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

structure open_immersion {C : Type*} [category C] {X Y : PresheafedSpace C} (f : X ⟶ Y) :=
(base_open : open_embedding f.base)
(c_iso : X ≅ Y.restrict _ base_open)
(fac : c_iso.hom ≫ Y.of_restrict _ _ = f)

instance mono_pullback_to_prod {C : Type*} [category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  [has_pullback f g] [has_binary_product X Y] :
  mono (prod.lift pullback.fst pullback.snd : pullback f g ⟶ _) :=
⟨λ W i₁ i₂ h, by { ext,
                   simpa using congr_arg (λ f, f ≫ limits.prod.fst) h,
                   simpa using congr_arg (λ f, f ≫ limits.prod.snd) h }⟩

instance map_mono {C : Type*} [category C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [mono f]
  [mono g] [has_binary_product W X] [has_binary_product Y Z] : mono (limits.prod.map f g) :=
⟨λ A i₁ i₂ h, by { ext,
                   rw ←cancel_mono f, simpa using congr_arg (λ f, f ≫ limits.prod.fst) h,
                   rw ←cancel_mono g, simpa using congr_arg (λ f, f ≫ limits.prod.snd) h }⟩

lemma pullback_topology {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (pullback f g).topological_space =
    induced (pullback.fst : pullback f g ⟶ _) X.topological_space ⊓
      induced (pullback.snd : pullback f g ⟶ _) Y.topological_space :=
begin
  change (pullback f g).str = _,
  conv_lhs { rw Top.limit_induced },
  apply le_antisymm,
  rw le_inf_iff,
  exact ⟨infi_le _ walking_cospan.left, infi_le _ walking_cospan.right⟩,
  rw le_infi_iff,
  rintro (_|_|_),
  rw ← limit.w _ walking_cospan.hom.inl,
  conv_rhs { rw [coe_comp, ←induced_compose] },
  exact inf_le_left.trans (induced_mono (continuous.le_induced (by continuity))),
  exacts [inf_le_left, inf_le_right]
end

lemma prod_topology {X Y : Top} :
  (X ⨯ Y).topological_space =
    induced (limits.prod.fst : X ⨯ Y ⟶ _) X.topological_space ⊓
      induced (limits.prod.snd : X ⨯ Y ⟶ _) Y.topological_space :=
begin
  change (X ⨯ Y).str = _,
  conv_lhs { rw Top.limit_induced },
  apply le_antisymm,
  rw le_inf_iff,
  exact ⟨infi_le _ walking_pair.left, infi_le _ walking_pair.right⟩,
  rw le_infi_iff,
  rintro (_|_),
  exacts [inf_le_left, inf_le_right]
end

lemma inducing_pullback_to_prod {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
  @inducing (pullback f g : Top) (X ⨯ Y : Top) _ _
    (prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) :=
⟨by simp [prod_topology, pullback_topology, induced_compose, ←coe_comp]⟩

lemma embedding_pullback_to_prod {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
  @embedding (pullback f g : Top) (X ⨯ Y : Top) _ _
    (prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) :=
⟨inducing_pullback_to_prod f g, (Top.mono_iff_injective _).mp infer_instance⟩

/--
Given two continuous maps `f : X ⟶ Z`, `g : Y ⟶ Z`, and two elements `x : X`, `y : Y` such
that `f x = g y`, we may obtain an element in `X ×[Z] Y` whose projection onto `X` and `Y` are
`x` and `y`, respectively.
-/
def pullback_preimage {X Y Z : Top.{v}} (f : X ⟶ Z) (g : Y ⟶ Z) (x : X) (y : Y)
  (h : f x = g y) : (pullback f g : Top) :=
(limit.is_limit (cospan _ _)).lift
  (@pullback_cone.mk Top _ _ _ _ f g ⟨punit⟩
    ⟨λ _, x, by continuity⟩ ⟨λ _, y, by continuity⟩
    (by { ext a, cases a, simp[h] })) punit.star

@[simp] lemma pullback_preimage_fst {X Y Z : Top.{v}} (f : X ⟶ Z) (g : Y ⟶ Z) (x : X) (y : Y)
  (h : f x = g y) :
  (pullback.fst : pullback f g ⟶ _) (pullback_preimage f g x y h) = x :=
by { unfold pullback_preimage, simp }

@[simp] lemma pullback_preimage_snd {X Y Z : Top.{v}} (f : X ⟶ Z) (g : Y ⟶ Z) (x : X) (y : Y)
  (h : f x = g y) :
  (pullback.snd : pullback f g ⟶ _) (pullback_preimage f g x y h) = y :=
by { unfold pullback_preimage, simp }

lemma range_pullback_to_prod {X Y Z : Top} (f : X ⟶ Z) (g : Y ⟶ Z) :
  set.range (prod.lift pullback.fst pullback.snd : pullback f g ⟶ X ⨯ Y) =
  { x | (limits.prod.fst ≫ f) x = (limits.prod.snd ≫ g) x } :=
begin
  ext x,
  split,
  rintros ⟨y, rfl⟩,
  simp only [←comp_apply, set.mem_set_of_eq],
  congr' 1,
  simp [pullback.condition],
  intro h,
  use pullback_preimage f g _ _ h,
  apply concrete.limit_ext,
  rintro ⟨⟩; simp,
end

def inducing_prod_map {W X Y Z : Top} {f : W ⟶ X} {g : Y ⟶ Z}
  (hf : inducing f) (hg : inducing g) : inducing (limits.prod.map f g) :=
begin
  split,
  simp only [prod_topology, induced_compose, ←coe_comp, limits.prod.map_fst, limits.prod.map_snd,
    induced_inf],
  simp only [coe_comp],
  rw [←@induced_compose _ _ _ _ _ f, ←@induced_compose _ _ _ _ _ g, ←hf.induced, ←hg.induced]
end

def embedding_prod_map {W X Y Z : Top} {f : W ⟶ X} {g : Y ⟶ Z}
  (hf : embedding f) (hg : embedding g) : embedding (limits.prod.map f g) :=
⟨inducing_prod_map hf.to_inducing hg.to_inducing,
begin
  haveI := (Top.mono_iff_injective _).mpr hf.inj,
  haveI := (Top.mono_iff_injective _).mpr hg.inj,
  exact (Top.mono_iff_injective _).mp infer_instance
end⟩

def prod_iso_prod (X Y : Top) : ↥(X ⨯ Y) ≅ X × Y :=
begin
  refine preserves_limit_iso (forget Top) (pair X Y) ≪≫
    limits.lim.map_iso (nat_iso.of_components _ _) ≪≫
    limit.iso_limit_cone (limits.types.binary_product_limit_cone _ _),
  intro j, apply eq_to_iso, cases j; simp,
  tidy,
end

@[simp, reassoc] lemma prod_iso_prod_hom_fst (X Y : Top) :
  (prod_iso_prod X Y).hom ≫ prod.fst = (limits.prod.fst : X ⨯ Y ⟶ _) :=
begin
  simp only [category.assoc, prod_iso_prod, lim_map_eq_lim_map, iso.trans_hom,
    functor.map_iso_hom],
  erw limit.iso_limit_cone_hom_π (types.binary_product_limit_cone ↥X ↥Y) walking_pair.left,
  simp
end

@[simp, reassoc] lemma prod_iso_prod_hom_snd (X Y : Top) :
  (prod_iso_prod X Y).hom ≫ prod.snd = (limits.prod.snd : X ⨯ Y ⟶ _) :=
begin
  simp only [category.assoc, prod_iso_prod, lim_map_eq_lim_map, iso.trans_hom,
    functor.map_iso_hom],
  erw limit.iso_limit_cone_hom_π (types.binary_product_limit_cone ↥X ↥Y) walking_pair.right,
  simp
end

@[simp] lemma prod_iso_prod_hom_apply {X Y : Top} (x : X ⨯ Y) :
  (prod_iso_prod X Y).hom x =
    ((limits.prod.fst : X ⨯ Y ⟶ _) x, (limits.prod.snd : X ⨯ Y ⟶ _) x) :=
begin
  ext,
  { refine congr_fun _ x,
    change ((prod_iso_prod X Y).hom ≫ prod.fst) = _,
    simp },
  { refine congr_fun _ x,
    change ((prod_iso_prod X Y).hom ≫ prod.snd) = _,
    simp }
end

@[simp, reassoc, elementwise] lemma prod_iso_prod_inv_fst (X Y : Top) :
  (prod_iso_prod X Y).inv ≫ (limits.prod.fst : X ⨯ Y ⟶ _) = prod.fst :=
by simp [iso.inv_comp_eq]

@[simp, reassoc, elementwise] lemma prod_iso_prod_inv_snd (X Y : Top) :
  (prod_iso_prod X Y).inv ≫ (limits.prod.snd : X ⨯ Y ⟶ _) = prod.snd :=
by simp [iso.inv_comp_eq]

def range_prod_map {W X Y Z : Top} (f : W ⟶ Y) (g : X ⟶ Z) :
  set.range (limits.prod.map f g) =
    (limits.prod.fst : Y ⨯ Z ⟶ _) ⁻¹' (set.range f) ∩
      (limits.prod.snd : Y ⨯ Z ⟶ _) ⁻¹' (set.range g) :=
begin
  ext,
  split,
  rintros ⟨y, rfl⟩,
  simp only [set.mem_preimage, set.mem_range, set.mem_inter_eq, ←comp_apply],
  simp only [limits.prod.map_fst, limits.prod.map_snd,
    exists_apply_eq_apply, comp_apply, and_self],
  rintros ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩,
  use (prod_iso_prod _ _).inv (x₁, x₂),
  apply concrete.limit_ext,
  rintro ⟨⟩,
  all_goals { simp only [←comp_apply], erw lim_map_π, simpa }
end

lemma has_pullback_of_open_embedding {W X Y Z S T : Top}
  (f₁ : W ⟶ S) (f₂ : X ⟶ S) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) (i₁ : W ⟶ Y) (i₂ : X ⟶ Z)
  (i₃ : S ⟶ T) (H₁ : open_embedding i₁) (H₂ : open_embedding i₂) [H₃ : mono i₃]
  (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
  open_embedding (pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ i₂)
    (by simp [←eq₁, ←eq₂, pullback.condition_assoc]) : pullback f₁ f₂ ⟶ pullback g₁ g₂) :=
begin
  split,
  { refine embedding_of_embedding_compose (continuous_map.continuous_to_fun _)
    (show continuous (prod.lift pullback.fst pullback.snd : pullback g₁ g₂ ⟶ Y ⨯ Z), from
      continuous_map.continuous_to_fun _) _,
    suffices : embedding
      (prod.lift pullback.fst pullback.snd ≫ limits.prod.map i₁ i₂ : pullback f₁ f₂ ⟶ _),
    { simpa[←coe_comp] using this },
    rw coe_comp,
    refine embedding.comp (embedding_prod_map H₁.to_embedding H₂.to_embedding)
      (embedding_pullback_to_prod _ _) },
  generalize_proofs _ _ eq,
  have : set.range ⇑(pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ i₂) eq) =
    (pullback.fst : pullback g₁ g₂ ⟶ _) ⁻¹' (set.range i₁) ∩
      (pullback.snd : pullback g₁ g₂ ⟶ _) ⁻¹' (set.range i₂),
  { ext,
    split,
    { rintro ⟨y, rfl⟩, simp, },
    rintros ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩,
    have : f₁ x₁ = f₂ x₂,
    { apply (Top.mono_iff_injective _).mp H₃,
      simp only [←comp_apply, eq₁, eq₂],
      simp only [comp_apply, hx₁, hx₂],
      simp only [←comp_apply, pullback.condition] },
    use pullback_preimage f₁ f₂ x₁ x₂ this,
    apply concrete.limit_ext,
    rintros (_|_|_),
    { simp only [Top.comp_app, limit.lift_π_apply, pullback_preimage_fst, category.assoc,
      pullback_cone.mk_π_app_one, hx₁],
      simp only[← comp_apply],
      congr,
      apply limit.w _ walking_cospan.hom.inl },
    { simp[hx₁] },
    { simp[hx₂] } },
  rw this,
  apply is_open.inter; apply continuous.is_open_preimage,
  continuity,
  exacts [H₁.open_range, H₂.open_range]
end


def has_pullback_of_open_immersion {C : Type*} [category C] {X Y Z : PresheafedSpace C}
  (f : X ⟶ Z) (g : Y ⟶ Z) : has_pullback f g :=
begin
  split,split,split,swap,split,swap,
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
