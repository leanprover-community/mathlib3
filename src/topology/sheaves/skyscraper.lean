/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/
import topology.sheaves.punit
import topology.sheaves.stalks
import topology.sheaves.functors

/-!
# Skyscraper (pre)sheaves

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A skyscraper (pre)sheaf `𝓕 : (pre)sheaf C X` is the (pre)sheaf with value `A` at point `p₀` that is
supported only at open sets contain `p₀`, i.e. `𝓕(U) = A` if `p₀ ∈ U` and `𝓕(U) = *` if `p₀ ∉ U`
where `*` is a terminal object of `C`. In terms of stalks, `𝓕` is supported at all specializations
of `p₀`, i.e. if `p₀ ⤳ x` then `𝓕ₓ ≅ A` and if `¬ p₀ ⤳ x` then `𝓕ₓ ≅ *`.

## Main definitions

* `skyscraper_presheaf`: `skyscraper_presheaf p₀ A` is the skyscraper presheaf at point `p₀` with
  value `A`.
* `skyscraper_sheaf`: the skyscraper presheaf satisfies the sheaf condition.

## Main statements

* `skyscraper_presheaf_stalk_of_specializes`: if `y ∈ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ A` at `y` is `A`.
* `skyscraper_presheaf_stalk_of_not_specializes`: if `y ∉ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ A` at `y` is `*` the terminal object.

TODO: generalize universe level when calculating stalks, after generalizing universe level of stalk.
-/

noncomputable theory

open topological_space Top category_theory category_theory.limits opposite

universes u v w

variables {X : Top.{u}} (p₀ : X) [Π (U : opens X), decidable (p₀ ∈ U)]

section

variables {C : Type v} [category.{w} C] [has_terminal C] (A : C)

/--
A skyscraper presheaf is a presheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper presheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
@[simps] def skyscraper_presheaf : presheaf C X :=
{ obj := λ U, if p₀ ∈ unop U then A else terminal C,
  map := λ U V i, if h : p₀ ∈ unop V
    then eq_to_hom $ by erw [if_pos h, if_pos (le_of_hom i.unop h)]
    else ((if_neg h).symm.rec terminal_is_terminal).from _,
  map_id' := λ U, (em (p₀ ∈ U.unop)).elim (λ h, dif_pos h)
    (λ h, ((if_neg h).symm.rec terminal_is_terminal).hom_ext _ _),
  map_comp' := λ U V W iVU iWV,
  begin
    by_cases hW : p₀ ∈ unop W,
    { have hV : p₀ ∈ unop V := le_of_hom iWV.unop hW,
      simp only [dif_pos hW, dif_pos hV, eq_to_hom_trans] },
    { rw [dif_neg hW], apply ((if_neg hW).symm.rec terminal_is_terminal).hom_ext }
  end }

lemma skyscraper_presheaf_eq_pushforward
  [hd : Π (U : opens (Top.of punit.{u+1})), decidable (punit.star ∈ U)] :
  skyscraper_presheaf p₀ A =
  continuous_map.const (Top.of punit) p₀ _* skyscraper_presheaf punit.star A :=
by convert_to @skyscraper_presheaf X p₀
  (λ U, hd $ (opens.map $ continuous_map.const _ p₀).obj U) C _ _ A = _; congr <|> refl

/--
Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps] def skyscraper_presheaf_functor.map' {a b : C} (f : a ⟶ b) :
  skyscraper_presheaf p₀ a ⟶ skyscraper_presheaf p₀ b :=
{ app := λ U, if h : p₀ ∈ U.unop
    then eq_to_hom (if_pos h) ≫ f ≫ eq_to_hom (if_pos h).symm
    else ((if_neg h).symm.rec terminal_is_terminal).from _,
  naturality' := λ U V i,
  begin
    simp only [skyscraper_presheaf_map], by_cases hV : p₀ ∈ V.unop,
    { have hU : p₀ ∈ U.unop := le_of_hom i.unop hV, split_ifs,
      simpa only [eq_to_hom_trans_assoc, category.assoc, eq_to_hom_trans], },
    { apply ((if_neg hV).symm.rec terminal_is_terminal).hom_ext, },
  end }

lemma skyscraper_presheaf_functor.map'_id {a : C} :
  skyscraper_presheaf_functor.map' p₀ (𝟙 a) = 𝟙 _ :=
begin
  ext1, ext1, simp only [skyscraper_presheaf_functor.map'_app, nat_trans.id_app], split_ifs,
  { simp only [category.id_comp, category.comp_id, eq_to_hom_trans, eq_to_hom_refl], },
  { apply ((if_neg h).symm.rec terminal_is_terminal).hom_ext, },
end

lemma skyscraper_presheaf_functor.map'_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
  skyscraper_presheaf_functor.map' p₀ (f ≫ g) =
  skyscraper_presheaf_functor.map' p₀ f ≫ skyscraper_presheaf_functor.map' p₀ g :=
begin
  ext1, ext1, simp only [skyscraper_presheaf_functor.map'_app, nat_trans.comp_app], split_ifs,
  { simp only [category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp], },
  { apply ((if_neg h).symm.rec terminal_is_terminal).hom_ext, },
end

/--
Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps] def skyscraper_presheaf_functor : C ⥤ presheaf C X :=
{ obj := skyscraper_presheaf p₀,
  map := λ _ _, skyscraper_presheaf_functor.map' p₀,
  map_id' := λ _, skyscraper_presheaf_functor.map'_id p₀,
  map_comp' := λ _ _ _, skyscraper_presheaf_functor.map'_comp p₀ }

end

section

-- In this section, we calculate the stalks for skyscraper presheaves.
-- We need to restrict universe level.

variables {C : Type v} [category.{u} C] (A : C) [has_terminal C]

/--
The cocone at `A` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∈ closure {p₀}`
-/
@[simps] def skyscraper_presheaf_cocone_of_specializes {y : X} (h : p₀ ⤳ y) :
  cocone ((open_nhds.inclusion y).op ⋙ skyscraper_presheaf p₀ A) :=
{ X := A,
  ι := { app := λ U, eq_to_hom $ if_pos $ h.mem_open U.unop.1.2 U.unop.2,
    naturality' := λ U V inc, begin
      change dite _ _ _ ≫ _ = _, rw dif_pos,
      { erw [category.comp_id, eq_to_hom_trans], refl },
      { exact h.mem_open V.unop.1.2 V.unop.2 },
    end } }

/--
The cocone at `A` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∈ closure {p₀}` is a
colimit
-/
noncomputable def skyscraper_presheaf_cocone_is_colimit_of_specializes
  {y : X} (h : p₀ ⤳ y) : is_colimit (skyscraper_presheaf_cocone_of_specializes p₀ A h) :=
{ desc := λ c, eq_to_hom (if_pos trivial).symm ≫ c.ι.app (op ⊤),
  fac' := λ c U, begin
    rw ← c.w (hom_of_le $ (le_top : unop U ≤ _)).op,
    change _ ≫ _ ≫ dite _ _ _ ≫ _ = _,
    rw dif_pos,
    { simpa only [skyscraper_presheaf_cocone_of_specializes_ι_app,
        eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp] },
    { exact h.mem_open U.unop.1.2 U.unop.2 },
  end,
  uniq' := λ c f h, by rw [← h, skyscraper_presheaf_cocone_of_specializes_ι_app,
    eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp] }

/--
If `y ∈ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ A` at `y` is `A`.
-/
noncomputable def skyscraper_presheaf_stalk_of_specializes [has_colimits C]
  {y : X} (h : p₀ ⤳ y) : (skyscraper_presheaf p₀ A).stalk y ≅ A :=
colimit.iso_colimit_cocone ⟨_, skyscraper_presheaf_cocone_is_colimit_of_specializes p₀ A h⟩

/--
The cocone at `*` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∉ closure {p₀}`
-/
@[simps] def skyscraper_presheaf_cocone (y : X) :
  cocone ((open_nhds.inclusion y).op ⋙ skyscraper_presheaf p₀ A) :=
{ X := terminal C,
  ι :=
  { app := λ U, terminal.from _,
    naturality' := λ U V inc, terminal_is_terminal.hom_ext _ _ } }

/--
The cocone at `*` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∉ closure {p₀}` is a
colimit
-/
noncomputable def skyscraper_presheaf_cocone_is_colimit_of_not_specializes
  {y : X} (h : ¬p₀ ⤳ y) : is_colimit (skyscraper_presheaf_cocone p₀ A y) :=
let h1 : ∃ (U : open_nhds y), p₀ ∉ U.1 :=
  let ⟨U, ho, h₀, hy⟩ := not_specializes_iff_exists_open.mp h in ⟨⟨⟨U, ho⟩, h₀⟩, hy⟩ in
{ desc := λ c, eq_to_hom (if_neg h1.some_spec).symm ≫ c.ι.app (op h1.some),
  fac' := λ c U, begin
    change _ = c.ι.app (op U.unop),
    simp only [← c.w (hom_of_le $ @inf_le_left _ _ h1.some U.unop).op,
      ← c.w (hom_of_le $ @inf_le_right _ _ h1.some U.unop).op, ← category.assoc],
    congr' 1,
    refine ((if_neg _).symm.rec terminal_is_terminal).hom_ext _ _,
    exact λ h, h1.some_spec h.1,
  end,
  uniq' := λ c f H, begin
    rw [← category.id_comp f, ← H, ← category.assoc],
    congr' 1, apply terminal_is_terminal.hom_ext,
  end }

/--
If `y ∉ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ A` at `y` is isomorphic to a
terminal object.
-/
noncomputable def skyscraper_presheaf_stalk_of_not_specializes [has_colimits C]
  {y : X} (h : ¬p₀ ⤳ y) : (skyscraper_presheaf p₀ A).stalk y ≅ terminal C :=
colimit.iso_colimit_cocone ⟨_, skyscraper_presheaf_cocone_is_colimit_of_not_specializes _ A h⟩

/--
If `y ∉ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ A` at `y` is a terminal object
-/
def skyscraper_presheaf_stalk_of_not_specializes_is_terminal
  [has_colimits C] {y : X} (h : ¬p₀ ⤳ y) : is_terminal ((skyscraper_presheaf p₀ A).stalk y) :=
is_terminal.of_iso terminal_is_terminal $ (skyscraper_presheaf_stalk_of_not_specializes _ _ h).symm

lemma skyscraper_presheaf_is_sheaf : (skyscraper_presheaf p₀ A).is_sheaf :=
by classical; exact (presheaf.is_sheaf_iso_iff
  (eq_to_iso $ skyscraper_presheaf_eq_pushforward p₀ A)).mpr
  (sheaf.pushforward_sheaf_of_sheaf _ (presheaf.is_sheaf_on_punit_of_is_terminal _
  (by { dsimp, rw if_neg, exact terminal_is_terminal, exact set.not_mem_empty punit.star })))

/--
The skyscraper presheaf supported at `p₀` with value `A` is the sheaf that assigns `A` to all opens
`U` that contain `p₀` and assigns `*` otherwise.
-/
def skyscraper_sheaf : sheaf C X :=
⟨skyscraper_presheaf p₀ A, skyscraper_presheaf_is_sheaf _ _⟩

/--
Taking skyscraper sheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
def skyscraper_sheaf_functor : C ⥤ sheaf C X :=
{ obj := λ c, skyscraper_sheaf p₀ c,
  map := λ a b f, Sheaf.hom.mk $ (skyscraper_presheaf_functor p₀).map f,
  map_id' := λ c, Sheaf.hom.ext _ _ $ (skyscraper_presheaf_functor p₀).map_id _,
  map_comp' := λ _ _ _ f g, Sheaf.hom.ext _ _ $ (skyscraper_presheaf_functor p₀).map_comp _ _ }

namespace stalk_skyscraper_presheaf_adjunction_auxs

variables [has_colimits C]

/--
If `f : 𝓕.stalk p₀ ⟶ c`, then a natural transformation `𝓕 ⟶ skyscraper_presheaf p₀ c` can be
defined by: `𝓕.germ p₀ ≫ f : 𝓕(U) ⟶ c` if `p₀ ∈ U` and the unique morphism to a terminal object
if `p₀ ∉ U`.
-/
@[simps] def to_skyscraper_presheaf {𝓕 : presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
  𝓕 ⟶ skyscraper_presheaf p₀ c :=
{ app := λ U, if h : p₀ ∈ U.unop
    then 𝓕.germ ⟨p₀, h⟩ ≫ f ≫ eq_to_hom (if_pos h).symm
    else ((if_neg h).symm.rec terminal_is_terminal).from _,
  naturality' := λ U V inc,
  begin
    dsimp, by_cases hV : p₀ ∈ V.unop,
    { have hU : p₀ ∈ U.unop := le_of_hom inc.unop hV, split_ifs,
      erw [←category.assoc, 𝓕.germ_res inc.unop, category.assoc, category.assoc, eq_to_hom_trans],
      refl, },
    { split_ifs, apply ((if_neg hV).symm.rec terminal_is_terminal).hom_ext },
  end }

/--
If `f : 𝓕 ⟶ skyscraper_presheaf p₀ c` is a natural transformation, then there is a morphism
`𝓕.stalk p₀ ⟶ c` defined as the morphism from colimit to cocone at `c`.
-/
def from_stalk {𝓕 : presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraper_presheaf p₀ c) :
  𝓕.stalk p₀ ⟶ c :=
let χ : cocone ((open_nhds.inclusion p₀).op ⋙ 𝓕) := cocone.mk c $
{ app := λ U, f.app (op U.unop.1) ≫ eq_to_hom (if_pos U.unop.2),
  naturality' := λ U V inc,
  begin
    dsimp, erw [category.comp_id, ←category.assoc, comp_eq_to_hom_iff, category.assoc,
      eq_to_hom_trans, f.naturality, skyscraper_presheaf_map],
    have hV : p₀ ∈ (open_nhds.inclusion p₀).obj V.unop := V.unop.2, split_ifs,
    simpa only [comp_eq_to_hom_iff, category.assoc, eq_to_hom_trans, eq_to_hom_refl,
      category.comp_id],
  end } in colimit.desc _ χ

lemma to_skyscraper_from_stalk {𝓕 : presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraper_presheaf p₀ c) :
  to_skyscraper_presheaf p₀ (from_stalk _ f) = f :=
nat_trans.ext _ _ $ funext $ λ U, (em (p₀ ∈ U.unop)).elim
(λ h, by { dsimp, split_ifs, erw [←category.assoc, colimit.ι_desc, category.assoc,
  eq_to_hom_trans, eq_to_hom_refl, category.comp_id], refl }) $
λ h, by { dsimp, split_ifs, apply ((if_neg h).symm.rec terminal_is_terminal).hom_ext }

lemma from_stalk_to_skyscraper {𝓕 : presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
  from_stalk p₀ (to_skyscraper_presheaf _ f) = f :=
colimit.hom_ext $ λ U, by { erw [colimit.ι_desc], dsimp, rw dif_pos U.unop.2, rw [category.assoc,
  category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id, presheaf.germ], congr' 3,
  apply_fun opposite.unop using unop_injective, rw [unop_op], ext, refl }

/--
The unit in `presheaf.stalk ⊣ skyscraper_presheaf_functor`
-/
@[simps] protected def unit :
  𝟭 (presheaf C X) ⟶ presheaf.stalk_functor C p₀ ⋙ skyscraper_presheaf_functor p₀ :=
{ app := λ 𝓕, to_skyscraper_presheaf _ $ 𝟙 _,
  naturality' := λ 𝓕 𝓖 f,
  begin
    ext U, dsimp, split_ifs,
    { simp only [category.id_comp, ←category.assoc], rw [comp_eq_to_hom_iff],
      simp only [category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id],
      erw [colimit.ι_map], refl, },
    { apply ((if_neg h).symm.rec terminal_is_terminal).hom_ext, },
  end }

/--
The counit in `presheaf.stalk ⊣ skyscraper_presheaf_functor`
-/
@[simps] protected def counit :
  (skyscraper_presheaf_functor p₀ ⋙ (presheaf.stalk_functor C p₀ : presheaf C X ⥤ C)) ⟶ 𝟭 C :=
{ app := λ c, (skyscraper_presheaf_stalk_of_specializes p₀ c specializes_rfl).hom,
  naturality' := λ x y f, colimit.hom_ext $ λ U,
  begin
    erw [←category.assoc, colimit.ι_map, colimit.iso_colimit_cocone_ι_hom_assoc,
      skyscraper_presheaf_cocone_of_specializes_ι_app, category.assoc, colimit.ι_desc,
      whiskering_left_obj_map, whisker_left_app, skyscraper_presheaf_functor.map'_app,
      dif_pos U.unop.2, skyscraper_presheaf_cocone_of_specializes_ι_app, comp_eq_to_hom_iff,
      category.assoc, eq_to_hom_comp_iff, ←category.assoc, eq_to_hom_trans, eq_to_hom_refl,
      category.id_comp, comp_eq_to_hom_iff, category.assoc, eq_to_hom_trans, eq_to_hom_refl,
      category.comp_id, category_theory.functor.id_map],
  end }

end stalk_skyscraper_presheaf_adjunction_auxs

section

open stalk_skyscraper_presheaf_adjunction_auxs

/--
`skyscraper_presheaf_functor` is the right adjoint of `presheaf.stalk_functor`
-/
def skyscraper_presheaf_stalk_adjunction [has_colimits C] :
  (presheaf.stalk_functor C p₀ : presheaf C X ⥤ C) ⊣ skyscraper_presheaf_functor p₀ :=
{ hom_equiv := λ c 𝓕,
  { to_fun := to_skyscraper_presheaf _,
    inv_fun := from_stalk _,
    left_inv := from_stalk_to_skyscraper _,
    right_inv := to_skyscraper_from_stalk _ },
  unit := stalk_skyscraper_presheaf_adjunction_auxs.unit _,
  counit := stalk_skyscraper_presheaf_adjunction_auxs.counit _,
  hom_equiv_unit' := λ 𝓕 c α,
  begin
    ext U, simp only [equiv.coe_fn_mk, to_skyscraper_presheaf_app, nat_trans.comp_app,
      skyscraper_presheaf_functor.map'_app, skyscraper_presheaf_functor_map, unit_app], split_ifs,
    { erw [category.id_comp, ←category.assoc, comp_eq_to_hom_iff, category.assoc, category.assoc,
        category.assoc,  category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id,
        ←category.assoc _ _ α, eq_to_hom_trans, eq_to_hom_refl, category.id_comp], },
    { apply ((if_neg h).symm.rec terminal_is_terminal).hom_ext }
  end,
  hom_equiv_counit' := λ 𝓕 c α,
  begin
    ext U, simp only [equiv.coe_fn_symm_mk, counit_app],
    erw [colimit.ι_desc, ←category.assoc, colimit.ι_map, whisker_left_app, category.assoc,
      colimit.ι_desc], refl,
  end }

instance [has_colimits C] : is_right_adjoint (skyscraper_presheaf_functor p₀ : C ⥤ presheaf C X) :=
⟨_, skyscraper_presheaf_stalk_adjunction _⟩

instance [has_colimits C] : is_left_adjoint (presheaf.stalk_functor C p₀) :=
⟨_, skyscraper_presheaf_stalk_adjunction _⟩

/--
Taking stalks of a sheaf is the left adjoint functor to `skyscraper_sheaf_functor`
-/
def stalk_skyscraper_sheaf_adjunction [has_colimits C] :
  sheaf.forget C X ⋙ presheaf.stalk_functor _ p₀ ⊣ skyscraper_sheaf_functor p₀ :=
{ hom_equiv := λ 𝓕 c,
  ⟨λ f, ⟨to_skyscraper_presheaf p₀ f⟩, λ g, from_stalk p₀ g.1, from_stalk_to_skyscraper p₀,
   λ g, by { ext1, apply to_skyscraper_from_stalk }⟩,
  unit :=
  { app := λ 𝓕, ⟨(stalk_skyscraper_presheaf_adjunction_auxs.unit p₀).app 𝓕.1⟩,
    naturality' := λ 𝓐 𝓑 ⟨f⟩,
      by { ext1, apply (stalk_skyscraper_presheaf_adjunction_auxs.unit p₀).naturality } },
  counit := stalk_skyscraper_presheaf_adjunction_auxs.counit p₀,
  hom_equiv_unit' := λ 𝓐 c f,
    by { ext1, exact (skyscraper_presheaf_stalk_adjunction p₀).hom_equiv_unit },
  hom_equiv_counit' := λ 𝓐 c f, (skyscraper_presheaf_stalk_adjunction p₀).hom_equiv_counit }

instance [has_colimits C] : is_right_adjoint (skyscraper_sheaf_functor p₀ : C ⥤ sheaf C X) :=
⟨_, stalk_skyscraper_sheaf_adjunction _⟩

end

end
