/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.sheafed_space
import topology.sheaves.sheaf_condition.unique_gluing
import topology.sheaves.stalks
import category_theory.preadditive.injective
import algebra.category.Group.abelian

/-!
# Skyscraper (pre)sheaves

A skyscraper (pre)sheaf is a (pre)sheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper (pre)sheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.

## Main definitions

* `skyscraper_presheaf`: the skyscraper presheaf, to define a skyscraper presheaf at point `p₀` with
  value `A`, use `skypscraper_presheaf p₀ A t` where `t` is a proof that `*` is a terminal object.
* `skyscraper_sheaf`: the skyscraper presheaf satisfies the sheaf condition.

## Main statements

* `skyscraper_stalk_of_mem_closure₀`: if `y ∈ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ S t` at `y` is `S`.
* `skyscraper_stalk_of_not_mem_closure₀`: if `y ∉ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ S t` at `y` is `*`.

-/


section

open topological_space
open category_theory category_theory.limits
open Top
open opposite

universes u v w

variables {X : Top.{u}} (p₀ : X) {C : Type v} [category.{w} C] (S : C)
variables {star : C} (ts : is_terminal star)
variable [Π (U : opens X), decidable (p₀ ∈ U)]

/-
A skyscraper presheaf is a presheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper presheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
@[simps]
def skyscraper_presheaf : presheaf C X :=
{ obj := λ U, ite (p₀ ∈ unop U) S star,
  map := λ U V i, dite (p₀ ∈ unop V)
    (λ h, eq_to_hom (if_pos (le_of_hom i.unop h)) ≫ 𝟙 S ≫ eq_to_hom (if_pos h).symm)
    (λ h, ts.from _ ≫ eq_to_hom (if_neg h).symm),
  map_id' := λ U,
  begin
    split_ifs,
    { simp, },
    { rw eq_comp_eq_to_hom,
      exact ts.hom_ext _ _, },
  end,
  map_comp' := λ U V W iVU iWV,
  begin
    by_cases hW : p₀ ∈ unop W,
    { have hV : p₀ ∈ unop V := le_of_hom iWV.unop hW,
      have hU : p₀ ∈ unop U := le_of_hom iVU.unop hV,
      split_ifs,
      simp },
    { split_ifs;
      rw eq_comp_eq_to_hom;
      exact ts.hom_ext _ _, }
  end }

section

variables {p₀}

lemma skyscraper_presheaf_obj_of_mem {U : opens X} (h : p₀ ∈ U) :
  (skyscraper_presheaf p₀ S ts).obj (op U) = S :=
if_pos h

lemma skyscraper_presheaf_obj_of_not_mem {U : opens X} (h : p₀ ∉ U) :
  (skyscraper_presheaf p₀ S ts).obj (op U) = star :=
if_neg h

end

/-
A skyscraper sheaf is a sheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper sheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
def skyscraper_sheaf : sheaf C X :=
⟨skyscraper_presheaf p₀ S ts, λ c U s hs x hx,
  ⟨dite (p₀ ∈ U)
    (λ h, x (hs p₀ h).some_spec.some (hs p₀ h).some_spec.some_spec.1 ≫
        eq_to_hom ((skyscraper_presheaf_obj_of_mem S ts (hs p₀ h).some_spec.some_spec.2).trans
          (skyscraper_presheaf_obj_of_mem S ts h).symm))
    (λ h, ts.from c ≫ (eq_to_hom (skyscraper_presheaf_obj_of_not_mem S ts h).symm)),
    λ V inc h,
    begin
      by_cases hV : p₀ ∈ V,
      { have hU : p₀ ∈ U := le_of_hom inc hV,
        split_ifs,
        generalize_proofs h₁ h₂ h₃ h₄,
        dsimp,
        split_ifs,
        rw [category.id_comp, eq_to_hom_trans, category.assoc, eq_to_hom_trans],
        generalize_proofs h₅,
        have := hx (hom_of_le inf_le_left) (hom_of_le inf_le_right) h₂.some_spec.1 h rfl,
        dsimp at this,
        have hV' : p₀ ∈ h₁.some ⊓ V := ⟨h₂.some_spec.2, hV⟩,
        split_ifs at this;
        rw [category.id_comp, eq_to_hom_trans, eq_to_hom_trans, eq_comp_eq_to_hom,
          category.assoc, eq_to_hom_trans] at this;
        generalize_proofs h₆ at this;
        rw [this, category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id] },
      { dsimp,
        split_ifs,
        rw [←category.assoc, eq_comp_eq_to_hom],
        exact ts.hom_ext _ _, }
    end,
    λ y (hy : x.is_amalgamation y),
    begin
      split_ifs,
      { generalize_proofs h₁ h₂ h₃ h₄,
        have := hy h₂.some h₂.some_spec.1,
        dsimp at this,
        split_ifs at this with H,
        { rw [category.id_comp, eq_to_hom_trans, eq_comp_eq_to_hom] at this,
          rw [this, eq_comp_eq_to_hom, category.assoc, eq_to_hom_trans, eq_to_hom_refl,
            category.comp_id], },
        { exfalso,
          exact H h₂.some_spec.2, }, },
      { rw [←eq_comp_eq_to_hom],
        exact (ts.hom_ext _ _), }
    end⟩⟩

end

section

-- In this section, we calculate the stalks for skyscraper presheaves. We need to restrict universe
-- level.

open topological_space
open category_theory category_theory.limits
open Top
open opposite

universes u v

variables {X : Top.{u}} (p₀ : X) {C : Type v} [category.{u} C] (S : C)
variables {star : C} (ts : is_terminal star)
variable [Π (U : opens X), decidable (p₀ ∈ U)]
variable [has_colimits C]

lemma mem_nhds_of_not_mem_closure_singleton {y : X} (h : ¬p₀ ⤳ y) :
  ∃ (U : open_nhds y), p₀ ∉ U.1 :=
begin
  have := (not_iff_not.mpr specializes_iff_forall_open).mp h,
  push_neg at this,
  rcases this with ⟨s, o, h₁, h₂⟩,
  exact ⟨⟨⟨s, o⟩, h₁⟩, h₂⟩,
end

/--
The cocone at `S` for the salk functor of `skyscraper_presheaf p₀ S t` when `y ∈ closure {p₀}`
-/
@[simps] def skyscraper_presheaf_cocone_of_mem_closure₀ {y : X} (h : p₀ ⤳ y) :
  cocone ((open_nhds.inclusion y).op ⋙ skyscraper_presheaf p₀ S ts) :=
{ X := S,
  ι :=
  { app := λ U, eq_to_hom
      begin
        dsimp,
        rw if_pos,
        exact h.mem_open U.unop.1.2 U.unop.2,
      end ≫ 𝟙 S,
    naturality' := λ U V inc,
    begin
      simp only [functor.op_obj, unop_op, functor.comp_map, functor.op_map, skyscraper_presheaf_map,
        category.id_comp, eq_to_hom_trans, functor.const_obj_map, category.assoc],
      by_cases hV : p₀ ∈ (open_nhds.inclusion y).obj V.unop,
      { have hU : p₀ ∈ unop ((open_nhds.inclusion y).op.obj U) := le_of_hom inc.unop hV,
        split_ifs,
        erw [category.comp_id, category.comp_id, category.comp_id, eq_to_hom_trans],
        refl },
      { split_ifs with hU;
        erw [category.comp_id, category.comp_id, category.comp_id, eq_comp_eq_to_hom,
          eq_comp_eq_to_hom];
        exact ts.hom_ext _ _, },
    end } }

/--
The canonical map `S ⟶ (skyscraper_presheaf p₀ S t).stalk y` when `y ∈ closure {p₀}`
-/
noncomputable def skyscraper_presheaf_of_mem_closure₀_from {y : X} (h : p₀ ⤳ y) :
  S ⟶ (skyscraper_presheaf p₀ S ts).stalk y :=
eq_to_hom (skyscraper_presheaf_obj_of_mem S ts (by tauto : p₀ ∈ ⊤)).symm ≫
  (skyscraper_presheaf p₀ S ts).germ (⟨y, trivial⟩ : (⊤ : opens X))

noncomputable lemma skyscraper_presheaf_cocone_of_mem_closure₀_is_colimit {y : X} (h : p₀ ⤳ y) :
  is_colimit (skyscraper_presheaf_cocone_of_mem_closure₀ p₀ S ts h) :=
{ desc := λ c, (skyscraper_presheaf_of_mem_closure₀_from p₀ S ts h ≫ colimit.desc _ _ : S ⟶ c.X),
  fac' := λ c U,
  begin
    dsimp,
    simp only [skyscraper_presheaf_of_mem_closure₀_from, presheaf.germ, category.comp_id,
      category.assoc, colimit.ι_desc, eq_to_hom_trans_assoc],
    have := c.ι.naturality (hom_of_le $ (le_top : unop U ≤ _)).op,
    dsimp at this,
    have h' : p₀ ∈ (open_nhds.inclusion y).obj (unop U) := h.mem_open U.unop.1.2 U.unop.2,
    have h'' : p₀ ∈ (open_nhds.inclusion y).obj ⊤ := trivial,
    split_ifs at this,
    rw [category.comp_id, category.id_comp, eq_to_hom_trans, eq_eq_to_hom_comp] at this,
    rw [this, eq_eq_to_hom_comp, ←category.assoc, eq_to_hom_trans, eq_to_hom_refl,
      category.id_comp],
    congr,
  end,
  uniq' := λ c f h,
  begin
    simp only [skyscraper_presheaf_of_mem_closure₀_from, presheaf.germ, category.assoc],
    erw [colimit.ι_desc],
    specialize h (op ⟨⊤, trivial⟩),
    erw [←h],
    simp only [skyscraper_presheaf_cocone_of_mem_closure₀_ι_app, category.assoc,
      eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp],
    exact (category.id_comp _).symm,
  end }

/--
If `y ∈ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ S t` at `y` is `S`
-/
@[reducible]
noncomputable def skyscraper_presheaf_stalk_of_mem_closure₀ {y : X} (h : p₀ ⤳ y) :
  (skyscraper_presheaf p₀ S ts).stalk y ≅ S :=
colimit.iso_colimit_cocone ⟨_, (skyscraper_presheaf_cocone_of_mem_closure₀_is_colimit p₀ S ts h)⟩

/--
The cocone at `*` for the salk functor of `skyscraper_presheaf p₀ S t` when `y ∉ closure {p₀}`
-/
@[simps] def skyscraper_presheaf_cocone_of_not_mem_closure₀
  {y : X} (h : ¬p₀ ⤳ y) :
  cocone ((open_nhds.inclusion y).op ⋙ skyscraper_presheaf p₀ S ts) :=
{ X := star,
  ι :=
  { app := λ U, ts.from _,
    naturality' := λ U V inc, ts.hom_ext _ _ } }

/--
The canonical map `* ⟶ (skyscraper_presheaf p₀ S t).stalk y` when `y ∉ closure {p₀}`
-/
noncomputable def skyscraper_presheaf_of_not_mem_closure₀_from
  {y : X} (h : ¬p₀ ⤳ y) :
  star ⟶ (skyscraper_presheaf p₀ S ts).stalk y :=
eq_to_hom (skyscraper_presheaf_obj_of_not_mem S ts $
  (mem_nhds_of_not_mem_closure_singleton p₀ h).some_spec).symm ≫
  (skyscraper_presheaf p₀ S ts).germ (⟨y, (mem_nhds_of_not_mem_closure_singleton p₀ h).some.2⟩ :
    (mem_nhds_of_not_mem_closure_singleton p₀ h).some.1)

noncomputable lemma skyscraper_presheaf_cocone_of_not_mem_closure₀_is_colimit
  {y : X} (h : ¬p₀ ⤳ y) :
  is_colimit (skyscraper_presheaf_cocone_of_not_mem_closure₀ p₀ S ts h) :=
{ desc := λ c, ((eq_to_hom ((skyscraper_presheaf_obj_of_not_mem _ _
      (mem_nhds_of_not_mem_closure_singleton p₀ h).some_spec).symm)) ≫
    presheaf.germ (skyscraper_presheaf p₀ S ts)
      ⟨y, (mem_nhds_of_not_mem_closure_singleton p₀ h).some.2⟩ ≫ colimit.desc _ _ : star ⟶ _),
  fac' := λ c U,
  begin
    simp only [presheaf.germ, skyscraper_presheaf_cocone_of_not_mem_closure₀_ι_app],
    erw [colimit.ι_desc],
    dsimp,
    by_cases h' : p₀ ∈ (open_nhds.inclusion y).obj (unop U),
    { have eq1 : ts.from (ite (p₀ ∈ (open_nhds.inclusion y).obj (unop U)) S star) =
          eq_to_hom (if_pos h') ≫ ts.from _ := ts.hom_ext _ _,
      rw [eq1, category.assoc, eq_eq_to_hom_comp],
      have := c.ι.naturality (hom_of_le (le_top : U.unop ≤ ⊤)).op,
      dsimp at this,
      have h'' : p₀ ∈ (open_nhds.inclusion y).obj ⊤ := trivial,
      split_ifs at this,
      rw [category.comp_id, category.id_comp, eq_to_hom_trans, eq_eq_to_hom_comp] at this,
      rw this,
      clear this,
      have := c.ι.naturality
        (hom_of_le (le_top : (mem_nhds_of_not_mem_closure_singleton p₀ h).some ≤ ⊤)).op,
      dsimp at this,
      have h''' : p₀ ∉ (mem_nhds_of_not_mem_closure_singleton p₀ h).some.1 :=
        (mem_nhds_of_not_mem_closure_singleton p₀ h).some_spec,
      split_ifs at this,
      have eq2 : ts.from (ite (p₀ ∈ (open_nhds.inclusion y).obj ⊤) S star) =
        eq_to_hom (if_pos h'') ≫ ts.from _ := ts.hom_ext _ _,
      rw [category.comp_id, eq2] at this,
      simp only [←this, ←category.assoc],
      convert eq_whisker _ _,
      { ext, refl, },
      { rw [eq_comp_eq_to_hom],
        exact ts.hom_ext _ _ } },
    { have eq1 : ts.from (ite (p₀ ∈ (open_nhds.inclusion y).obj (unop U)) S star) =
        eq_to_hom (if_neg h') ≫ 𝟙 star := ts.hom_ext _ _,
      have eq2 : ts.from (ite (p₀ ∈ (open_nhds.inclusion y).obj ⊤) S star) =
        eq_to_hom (if_pos trivial) ≫ ts.from _ := ts.hom_ext _ _,
      have eq3 : ts.from (ite (p₀ ∈ (open_nhds.inclusion y).obj
          (mem_nhds_of_not_mem_closure_singleton p₀ h).some) S star) =
        eq_to_hom (if_neg (mem_nhds_of_not_mem_closure_singleton p₀ h).some_spec) ≫ 𝟙 star :=
      ts.hom_ext _ _,
      rw [eq1, category.comp_id, ←category.assoc, eq_to_hom_trans],
      have := c.ι.naturality (hom_of_le (inf_le_left :
          (mem_nhds_of_not_mem_closure_singleton p₀ h).some ⊓ unop U ≤
          (mem_nhds_of_not_mem_closure_singleton p₀ h).some)).op,
      dsimp at this,
      rw [dite_comp, category.comp_id] at this,
      simp_rw [category.id_comp, eq_to_hom_trans, eq3, category.comp_id, eq_to_hom_trans] at this,


      generalize_proofs h₁ h₂ h₃,
      have eq_coe : c.ι.app (op ⟨↑(h₁.some), h₃⟩) =
        eq_to_hom (by { congr, ext, refl }) ≫ c.ι.app (op h₁.some) ≫
          eq_to_hom (by { congr, ext, refl }),
      { symmetry,
        rw [eq_eq_to_hom_comp],
        have e := c.ι.naturality (eq_to_hom (by {ext, refl}) :
          (⟨↑h₁.some, h₃⟩ : open_nhds y) ⟶ h₁.some).op,
        dsimp at e,
        split_ifs at e with temp,
        { exfalso, exact (mem_nhds_of_not_mem_closure_singleton p₀ h).some_spec temp },
        rw [show ts.from (ite (p₀ ∈ (open_nhds.inclusion y).obj h₁.some) S star) =
          eq_to_hom (if_neg temp) ≫ 𝟙 star, from ts.hom_ext _ _, category.comp_id,
          category.comp_id, eq_to_hom_trans] at e,
        rw [←e, category.assoc, eq_eq_to_hom_comp, ←category.assoc, eq_to_hom_trans, eq_to_hom_refl,
          eq_to_hom_refl, category.comp_id, category.id_comp], },
      rw [eq_coe, ←this, ←category.assoc, eq_to_hom_trans, eq_eq_to_hom_comp, dite_comp],
      have h₅ : p₀ ∉ (open_nhds.inclusion y).obj h₁.some := h₁.some_spec,
      have h₆ : p₀ ∉ (open_nhds.inclusion y).obj (h₁.some ⊓ unop U) := λ ⟨r, _⟩, h₅ r,
      clear this,
      split_ifs,
      { exfalso, exact h₅ (by assumption) },
      { exfalso, exact h₆ (by assumption) },
      { exfalso, exact h₅ (by assumption) },
      rw [eq_comp_eq_to_hom, eq_eq_to_hom_comp, ←category.assoc, ←category.assoc, eq_to_hom_trans,
        eq_to_hom_refl, category.comp_id],
      have := c.ι.naturality (hom_of_le (inf_le_right :
          (mem_nhds_of_not_mem_closure_singleton p₀ h).some ⊓ unop U ≤ unop U)).op,
      dsimp at this,
      rw [dite_comp, category.comp_id] at this,
      rw [←this, comp_dite],
      clear this,
      split_ifs,
      rw [eq1, category.comp_id, eq_to_hom_trans, ←category.assoc, eq_to_hom_trans, eq_to_hom_refl,
        category.id_comp] }
  end,
  uniq' := λ c f H,
  begin
    erw [colimit.ι_desc, ←H],
    simp only [skyscraper_presheaf_cocone_of_not_mem_closure₀_ι_app],
    dsimp,
    have : ts.from (ite (p₀ ∈ (mem_nhds_of_not_mem_closure_singleton p₀ h).some.1) S star) =
      eq_to_hom (if_neg (mem_nhds_of_not_mem_closure_singleton p₀ h).some_spec) ≫ 𝟙 star :=
    ts.hom_ext _ _,
    erw [this, category.comp_id, ←category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.id_comp]
  end }

/--
If `y ∉ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ S t` at `y` is `*`
-/
@[reducible]
noncomputable def skyscraper_presheaf_stalk_of_not_mem_closure₀
  {y : X} (h : ¬p₀ ⤳ y) :
  (skyscraper_presheaf p₀ S ts).stalk y ≅ star :=
colimit.iso_colimit_cocone ⟨_, (skyscraper_presheaf_cocone_of_not_mem_closure₀_is_colimit _ S _ h)⟩

end
