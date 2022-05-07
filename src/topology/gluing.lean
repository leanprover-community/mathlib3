/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.category.Top
import category_theory.glue_data
import category_theory.concrete_category.elementwise

/-!
# Gluing Topological spaces

Given a family of gluing data (see `category_theory/glue_data`), we can then glue them together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `Top.glue_data`: A structure containing the family of gluing data.
* `category_theory.glue_data.glued`: The glued topological space.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `category_theory.glue_data.ι`: The immersion `ι i : U i ⟶ glued` for each `i : ι`.
* `Top.glue_data.rel`: A relation on `Σ i, D.U i` defined by `⟨i, x⟩ ~ ⟨j, y⟩` iff
    `⟨i, x⟩ = ⟨j, y⟩` or `t i j x = y`. See `Top.glue_data.ι_eq_iff_rel`.
* `Top.glue_data.mk`: A constructor of `glue_data` whose conditions are stated in terms of
  elements rather than subobjects and pullbacks.
* `Top.glue_data.of_open_subsets`: Given a family of open sets, we may glue them into a new
  topological space. This new space embeds into the original space, and is homeomorphic to it if
  the given family is an open cover (`Top.glue_data.open_cover_glue_homeo`).

## Main results

* `Top.glue_data.is_open_iff`: A set in `glued` is open iff its preimage along each `ι i` is
    open.
* `Top.glue_data.ι_jointly_surjective`: The `ι i`s are jointly surjective.
* `Top.glue_data.rel_equiv`: `rel` is an equivalence relation.
* `Top.glue_data.ι_eq_iff_rel`: `ι i x = ι j y ↔ ⟨i, x⟩ ~ ⟨j, y⟩`.
* `Top.glue_data.image_inter`: The intersection of the images of `U i` and `U j` in `glued` is
    `V i j`.
* `Top.glue_data.preimage_range`: The preimage of the image of `U i` in `U j` is `V i j`.
* `Top.glue_data.preimage_image_eq_preimage_f`: The preimage of the image of some `U ⊆ U i` is
    given by the preimage along `f j i`.
* `Top.glue_data.ι_open_embedding`: Each of the `ι i`s are open embeddings.

-/

noncomputable theory

open topological_space category_theory

universes v u
open category_theory.limits
namespace Top

/--
A family of gluing data consists of
1. An index type `J`
2. An object `U i` for each `i : J`.
3. An object `V i j` for each `i j : J`.
  (Note that this is `J × J → Top` rather than `J → J → Top` to connect to the
  limits library easier.)
4. An open embedding `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
    (This merely means that `V i j ∩ V i k ⊆ t i j ⁻¹' (V j i ∩ V j k)`.)
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the topological spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.

Most of the times it would be easier to use the constructor `Top.glue_data.mk'` where the conditions
are stated in a less categorical way.
-/
@[nolint has_inhabited_instance]
structure glue_data extends glue_data Top :=
  (f_open : ∀ i j, open_embedding (f i j))
  (f_mono := λ i j, (Top.mono_iff_injective _).mpr (f_open i j).to_embedding.inj)

namespace glue_data

variable (D : glue_data.{u})

local notation `𝖣` := D.to_glue_data

lemma π_surjective : function.surjective 𝖣 .π :=
(Top.epi_iff_surjective 𝖣 .π).mp infer_instance

lemma is_open_iff (U : set 𝖣 .glued) : is_open U ↔ ∀ i, is_open (𝖣 .ι i ⁻¹' U) :=
begin
  delta category_theory.glue_data.ι,
  simp_rw ← multicoequalizer.ι_sigma_π 𝖣 .diagram,
  rw ← (homeo_of_iso (multicoequalizer.iso_coequalizer 𝖣 .diagram).symm).is_open_preimage,
  rw [coequalizer_is_open_iff, colimit_is_open_iff.{u}],
  refl
end

lemma ι_jointly_surjective (x : 𝖣 .glued) : ∃ i (y : D.U i), 𝖣 .ι i y = x :=
𝖣 .ι_jointly_surjective (forget Top) x

/--
An equivalence relation on `Σ i, D.U i` that holds iff `𝖣 .ι i x = 𝖣 .ι j y`.
See `Top.glue_data.ι_eq_iff_rel`.
-/
def rel (a b : Σ i, ((D.U i : Top) : Type*)) : Prop :=
  a = b ∨ ∃ (x : D.V (a.1, b.1)) , D.f _ _ x = a.2 ∧ D.f _ _ (D.t _ _ x) = b.2

lemma rel_equiv : equivalence D.rel :=
⟨ λ x, or.inl (refl x),
  begin
    rintros a b (⟨⟨⟩⟩|⟨x,e₁,e₂⟩),
    exacts [or.inl rfl, or.inr ⟨D.t _ _ x, by simp [e₁, e₂]⟩]
  end,
  begin
    rintros ⟨i,a⟩ ⟨j,b⟩ ⟨k,c⟩ (⟨⟨⟩⟩|⟨x,e₁,e₂⟩), exact id,
    rintro (⟨⟨⟩⟩|⟨y,e₃,e₄⟩), exact or.inr ⟨x,e₁,e₂⟩,
    let z := (pullback_iso_prod_subtype (D.f j i) (D.f j k)).inv ⟨⟨_,_⟩, e₂.trans e₃.symm⟩,
    have eq₁ : (D.t j i) ((pullback.fst : _ ⟶ D.V _) z) = x := by simp,
    have eq₂ : (pullback.snd : _ ⟶ D.V _) z = y := pullback_iso_prod_subtype_inv_snd_apply _ _ _,
    clear_value z,
    right,
    use (pullback.fst : _ ⟶ D.V (i, k)) (D.t' _ _ _ z),
    dsimp only at *,
    substs e₁ e₃ e₄ eq₁ eq₂,
    have h₁ : D.t' j i k ≫ pullback.fst ≫ D.f i k = pullback.fst ≫ D.t j i ≫ D.f i j,
    { rw ← 𝖣 .t_fac_assoc, congr' 1, exact pullback.condition },
    have h₂ : D.t' j i k ≫ pullback.fst ≫ D.t i k ≫ D.f k i =
      pullback.snd ≫ D.t j k ≫ D.f k j,
    { rw ← 𝖣 .t_fac_assoc,
      apply @epi.left_cancellation _ _ _ _ (D.t' k j i),
      rw [𝖣 .cocycle_assoc, 𝖣 .t_fac_assoc, 𝖣 .t_inv_assoc],
      exact pullback.condition.symm },
    exact ⟨continuous_map.congr_fun h₁ z, continuous_map.congr_fun h₂ z⟩
  end⟩

open category_theory.limits.walking_parallel_pair

lemma eqv_gen_of_π_eq {x y : ∐ D.U} (h : 𝖣 .π x = 𝖣 .π y) :
  eqv_gen (types.coequalizer_rel 𝖣 .diagram.fst_sigma_map 𝖣 .diagram.snd_sigma_map) x y :=
begin
  delta glue_data.π multicoequalizer.sigma_π at h,
  simp_rw comp_app at h,
  replace h := (Top.mono_iff_injective (multicoequalizer.iso_coequalizer 𝖣 .diagram).inv).mp _ h,
  let diagram := parallel_pair 𝖣 .diagram.fst_sigma_map 𝖣 .diagram.snd_sigma_map ⋙ forget _,
  have : colimit.ι diagram one x = colimit.ι diagram one y,
  { rw ←ι_preserves_colimits_iso_hom,
    simp [h] },
  have :
    (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.iso_colimit_cocone _).hom) _ =
    (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.iso_colimit_cocone _).hom) _ :=
    (congr_arg (colim.map (diagram_iso_parallel_pair diagram).hom
    ≫ (colimit.iso_colimit_cocone (types.coequalizer_colimit _ _)).hom) this : _),
  simp only [eq_to_hom_refl, types_comp_apply, colimit.ι_map_assoc,
    diagram_iso_parallel_pair_hom_app, colimit.iso_colimit_cocone_ι_hom, types_id_apply] at this,
  exact quot.eq.1 this,
  apply_instance
end

lemma ι_eq_iff_rel (i j : D.J) (x : D.U i) (y : D.U j) :
  𝖣 .ι i x = 𝖣 .ι j y ↔ D.rel ⟨i, x⟩ ⟨j, y⟩ :=
begin
  split,
  { delta glue_data.ι,
    simp_rw ← multicoequalizer.ι_sigma_π,
    intro h,
    rw ← (show _ = sigma.mk i x,
      from concrete_category.congr_hom (sigma_iso_sigma.{u} D.U).inv_hom_id _),
    rw ← (show _ = sigma.mk j y,
      from concrete_category.congr_hom (sigma_iso_sigma.{u} D.U).inv_hom_id _),
    change inv_image D.rel (sigma_iso_sigma.{u} D.U).hom _ _,
    simp only [Top.sigma_iso_sigma_inv_apply],
    rw ← (inv_image.equivalence _ _ D.rel_equiv).eqv_gen_iff,
    refine eqv_gen.mono _ (D.eqv_gen_of_π_eq h : _),
    rintros _ _ ⟨x⟩,
    rw ← (show (sigma_iso_sigma.{u} _).inv _ = x,
      from concrete_category.congr_hom (sigma_iso_sigma.{u} _).hom_inv_id x),
    generalize : (sigma_iso_sigma.{u} D.V).hom x = x',
    obtain ⟨⟨i,j⟩,y⟩ := x',
    unfold inv_image multispan_index.fst_sigma_map multispan_index.snd_sigma_map,
    simp only [opens.inclusion_to_fun, Top.comp_app, sigma_iso_sigma_inv_apply,
      category_theory.limits.colimit.ι_desc_apply, cofan.mk_ι_app,
      sigma_iso_sigma_hom_ι_apply, continuous_map.to_fun_eq_coe],
    erw [sigma_iso_sigma_hom_ι_apply, sigma_iso_sigma_hom_ι_apply],
    exact or.inr ⟨y, by { dsimp [glue_data.diagram], simp }⟩ },
  { rintro (⟨⟨⟩⟩|⟨z,e₁,e₂⟩),
    refl, dsimp only at *, subst e₁, subst e₂, simp }
end

lemma ι_injective (i : D.J) : function.injective (𝖣 .ι i) :=
begin
  intros x y h,
  rcases (D.ι_eq_iff_rel _ _ _ _).mp h with (⟨⟨⟩⟩|⟨_,e₁,e₂⟩),
  { refl },
  { dsimp only at *, cases e₁, cases e₂, simp }
end

instance ι_mono (i : D.J) : mono (𝖣 .ι i) :=
(Top.mono_iff_injective _).mpr (D.ι_injective _)

lemma image_inter (i j : D.J) :
  set.range (𝖣 .ι i) ∩ set.range (𝖣 .ι j) = set.range (D.f i j ≫ 𝖣 .ι _) :=
begin
  ext x,
  split,
  { rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩,
    obtain (⟨⟨⟩⟩|⟨y,e₁,e₂⟩) := (D.ι_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm),
    { exact ⟨inv (D.f i i) x₁, by simp [eq₁]⟩ },
    { dsimp only at *, substs e₁ eq₁, exact ⟨y, by simp⟩ } },
  { rintro ⟨x, hx⟩,
    exact ⟨⟨D.f i j x, hx⟩, ⟨D.f j i (D.t _ _ x), by simp [← hx]⟩⟩ }
end

lemma preimage_range (i j : D.J) :
  𝖣 .ι j ⁻¹' (set.range (𝖣 .ι i)) = set.range (D.f j i) :=
by rw [← set.preimage_image_eq (set.range (D.f j i)) (D.ι_injective j), ← set.image_univ,
      ← set.image_univ, ←set.image_comp, ←coe_comp, set.image_univ,set.image_univ,
      ← image_inter, set.preimage_range_inter]

lemma preimage_image_eq_image (i j : D.J) (U : set (𝖣 .U i)) :
  𝖣 .ι j ⁻¹' (𝖣 .ι i '' U) = D.f _ _ '' ((D.t j i ≫ D.f _ _) ⁻¹' U) :=
begin
  have : D.f _ _ ⁻¹' (𝖣 .ι j ⁻¹' (𝖣 .ι i '' U)) = (D.t j i ≫ D.f _ _) ⁻¹' U,
  { ext x,
    conv_rhs { rw ← set.preimage_image_eq U (D.ι_injective _) },
    generalize : 𝖣 .ι i '' U = U',
    simp },
  rw [← this, set.image_preimage_eq_inter_range],
  symmetry,
  apply set.inter_eq_self_of_subset_left,
  rw ← D.preimage_range i j,
  exact set.preimage_mono (set.image_subset_range _ _),
end

lemma preimage_image_eq_image' (i j : D.J) (U : set (𝖣 .U i)) :
𝖣 .ι j ⁻¹' (𝖣 .ι i '' U) = (D.t i j ≫ D.f _ _) '' ((D.f _ _) ⁻¹' U) :=
begin
  convert D.preimage_image_eq_image i j U using 1,
  rw [coe_comp, coe_comp, ← set.image_image],
  congr' 1,
  rw [← set.eq_preimage_iff_image_eq, set.preimage_preimage],
  change _ = (D.t i j ≫ D.t j i ≫ _) ⁻¹' _,
  rw 𝖣 .t_inv_assoc,
  rw ← is_iso_iff_bijective,
  apply (forget Top).map_is_iso
end

lemma open_image_open (i : D.J) (U : opens (𝖣 .U i)) : is_open (𝖣 .ι i '' U) :=
begin
  rw is_open_iff,
  intro j,
  rw preimage_image_eq_image,
  apply (D.f_open _ _).is_open_map,
  apply (D.t j i ≫ D.f i j).continuous_to_fun.is_open_preimage,
  exact U.property
end

lemma ι_open_embedding (i : D.J) : open_embedding (𝖣 .ι i) :=
open_embedding_of_continuous_injective_open
  (𝖣 .ι i).continuous_to_fun (D.ι_injective i) (λ U h, D.open_image_open i ⟨U, h⟩)

/--
A family of gluing data consists of
1. An index type `J`
2. A bundled topological space `U i` for each `i : J`.
3. An open set `V i j ⊆ U i` for each `i j : J`.
4. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `V i i = U i`.
7. `t i i` is the identity.
8. For each `x ∈ V i j ∩ V i k`, `t i j x ∈ V j k`.
9. `t j k (t i j x) = t i k x`.

We can then glue the topological spaces `U i` together by identifying `V i j` with `V j i`.
-/
@[nolint has_inhabited_instance]
structure mk_core :=
{J : Type u}
(U : J → Top.{u})
(V : Π i, J → opens (U i))
(t : Π i j, (opens.to_Top _).obj (V i j) ⟶ (opens.to_Top _).obj (V j i))
(V_id : ∀ i, V i i = ⊤)
(t_id : ∀ i, ⇑(t i i) = id)
(t_inter : ∀ ⦃i j⦄ k (x : V i j), ↑x ∈ V i k → @coe (V j i) (U j) _ (t i j x) ∈ V j k)
(cocycle : ∀ i j k (x : V i j) (h : ↑x ∈ V i k),
  @coe (V k j) (U k) _ (t j k ⟨↑(t i j x), t_inter k x h⟩) = @coe (V k i) (U k) _ (t i k ⟨x, h⟩))

lemma mk_core.t_inv (h : mk_core) (i j : h.J) (x : h.V j i) : h.t i j ((h.t j i) x) = x :=
begin
  have := h.cocycle j i j x _,
  rw h.t_id at this,
  convert subtype.eq this,
  { ext, refl },
  all_goals { rw h.V_id, trivial }
end

instance (h : mk_core.{u}) (i j : h.J) : is_iso (h.t i j) :=
by { use h.t j i, split; ext1, exacts [h.t_inv _ _ _, h.t_inv _ _ _] }

/-- (Implementation) the restricted transition map to be fed into `glue_data`. -/
def mk_core.t' (h : mk_core.{u}) (i j k : h.J) : pullback (h.V i j).inclusion (h.V i k).inclusion ⟶
  pullback (h.V j k).inclusion (h.V j i).inclusion :=
begin
  refine (pullback_iso_prod_subtype _ _).hom ≫ ⟨_, _⟩ ≫ (pullback_iso_prod_subtype _ _).inv,
  { intro x,
    refine ⟨⟨⟨(h.t i j x.1.1).1, _⟩, h.t i j x.1.1⟩, rfl⟩,
    rcases x with ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, (rfl : x = x')⟩,
    exact h.t_inter _ ⟨x, hx⟩ hx' },
  continuity,
end

/-- This is a constructor of `Top.glue_data` whose arguments are in terms of elements and
intersections rather than subobjects and pullbacks. Please refer to `Top.glue_data.mk_core` for
details. -/
def mk' (h : mk_core.{u}) : Top.glue_data :=
{ J := h.J,
  U := h.U,
  V := λ i, (opens.to_Top _).obj (h.V i.1 i.2),
  f := λ i j, (h.V i j).inclusion ,
  f_id := λ i, (h.V_id i).symm ▸ is_iso.of_iso (opens.inclusion_top_iso (h.U i)),
  f_open := λ (i j : h.J), (h.V i j).open_embedding,
  t := h.t,
  t_id := λ i, by { ext, rw h.t_id, refl },
  t' := h.t',
  t_fac := λ i j k,
  begin
    delta mk_core.t',
    rw [category.assoc, category.assoc, pullback_iso_prod_subtype_inv_snd, ← iso.eq_inv_comp,
      pullback_iso_prod_subtype_inv_fst_assoc],
    ext ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, (rfl : x = x')⟩,
    refl,
  end,
  cocycle := λ i j k,
  begin
    delta mk_core.t',
    simp_rw ← category.assoc,
    rw iso.comp_inv_eq,
    simp only [iso.inv_hom_id_assoc, category.assoc, category.id_comp],
    rw [← iso.eq_inv_comp, iso.inv_hom_id],
    ext1 ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, (rfl : x = x')⟩,
    simp only [Top.comp_app, continuous_map.coe_mk, prod.mk.inj_iff,
      Top.id_app, subtype.mk_eq_mk, subtype.coe_mk],
    rw [← subtype.coe_injective.eq_iff, subtype.val_eq_coe, subtype.coe_mk, and_self],
    convert congr_arg coe (h.t_inv k i ⟨x, hx'⟩) using 3,
    ext,
    exact h.cocycle i j k ⟨x, hx⟩ hx',
  end }
.

variables {α : Type u} [topological_space α] {J : Type u} (U : J → opens α)

include U

/-- We may construct a glue data from a family of open sets. -/
@[simps to_glue_data_J to_glue_data_U to_glue_data_V to_glue_data_t to_glue_data_f]
def of_open_subsets : Top.glue_data.{u} := mk'.{u}
{ J := J,
  U := λ i, (opens.to_Top $ Top.of α).obj (U i),
  V := λ i j, (opens.map $ opens.inclusion _).obj (U j),
  t := λ i j, ⟨λ x, ⟨⟨x.1.1, x.2⟩, x.1.2⟩, by continuity⟩,
  V_id := λ i, by { ext, cases U i, simp },
  t_id := λ i, by { ext, refl },
  t_inter := λ i j k x hx, hx,
  cocycle := λ i j k x h, rfl }

/--
The canonical map from the glue of a family of open subsets `α` into `α`.
This map is an open embedding (`from_open_subsets_glue_open_embedding`),
and its range is `⋃ i, (U i : set α)` (`range_from_open_subsets_glue`).
-/
def from_open_subsets_glue : (of_open_subsets U).to_glue_data.glued ⟶ Top.of α :=
multicoequalizer.desc _ _ (λ x, opens.inclusion _) (by { rintro ⟨i, j⟩, ext x, refl })

@[simp, elementwise]
lemma ι_from_open_subsets_glue (i : J) :
  (of_open_subsets U).to_glue_data.ι i ≫ from_open_subsets_glue U = opens.inclusion _ :=
multicoequalizer.π_desc _ _ _ _ _

lemma from_open_subsets_glue_injective : function.injective (from_open_subsets_glue U) :=
begin
  intros x y e,
  obtain ⟨i, ⟨x, hx⟩, rfl⟩ := (of_open_subsets U).ι_jointly_surjective x,
  obtain ⟨j, ⟨y, hy⟩, rfl⟩ := (of_open_subsets U).ι_jointly_surjective y,
  rw [ι_from_open_subsets_glue_apply, ι_from_open_subsets_glue_apply] at e,
  change x = y at e,
  subst e,
  rw (of_open_subsets U).ι_eq_iff_rel,
  right,
  exact ⟨⟨⟨x, hx⟩, hy⟩, rfl, rfl⟩,
end

lemma from_open_subsets_glue_is_open_map : is_open_map (from_open_subsets_glue U) :=
begin
  intros s hs,
  rw (of_open_subsets U).is_open_iff at hs,
  rw is_open_iff_forall_mem_open,
  rintros _ ⟨x, hx, rfl⟩,
  obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (of_open_subsets U).ι_jointly_surjective x,
  use from_open_subsets_glue U '' s ∩ set.range (@opens.inclusion (Top.of α) (U i)),
  use set.inter_subset_left _ _,
  split,
  { erw ← set.image_preimage_eq_inter_range,
    apply (@opens.open_embedding (Top.of α) (U i)).is_open_map,
    convert hs i using 1,
    rw [← ι_from_open_subsets_glue, coe_comp, set.preimage_comp],
    congr' 1,
    refine set.preimage_image_eq _ (from_open_subsets_glue_injective U) },
  { refine ⟨set.mem_image_of_mem _ hx, _⟩,
    rw ι_from_open_subsets_glue_apply,
    exact set.mem_range_self _ },
end

lemma from_open_subsets_glue_open_embedding : open_embedding (from_open_subsets_glue U) :=
open_embedding_of_continuous_injective_open (continuous_map.continuous_to_fun _)
  (from_open_subsets_glue_injective U) (from_open_subsets_glue_is_open_map U)

lemma range_from_open_subsets_glue : set.range (from_open_subsets_glue U) = ⋃ i, (U i : set α) :=
begin
  ext,
  split,
  { rintro ⟨x, rfl⟩,
    obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (of_open_subsets U).ι_jointly_surjective x,
    rw ι_from_open_subsets_glue_apply,
    exact set.subset_Union _ i hx' },
  { rintro ⟨_, ⟨i, rfl⟩, hx⟩,
    refine ⟨(of_open_subsets U).to_glue_data.ι i ⟨x, hx⟩, ι_from_open_subsets_glue_apply _ _ _⟩ }
end

/-- The gluing of an open cover is homeomomorphic to the original space. -/
def open_cover_glue_homeo (h : (⋃ i, (U i : set α)) = set.univ) :
  (of_open_subsets U).to_glue_data.glued ≃ₜ α :=
homeomorph.homeomorph_of_continuous_open
  (equiv.of_bijective (from_open_subsets_glue U)
    ⟨from_open_subsets_glue_injective U,
      set.range_iff_surjective.mp ((range_from_open_subsets_glue U).symm ▸ h)⟩)
  (from_open_subsets_glue U).2 (from_open_subsets_glue_is_open_map U)

end glue_data

end Top
