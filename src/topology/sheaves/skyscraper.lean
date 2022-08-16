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

* `skyscraper_presheaf`:  `skyscraper_presheaf p₀ A` is the skyscraper presheaf at point `p₀` with
  value `A`.
* `skyscraper_sheaf`: the skyscraper presheaf satisfies the sheaf condition.

## Main statements

* `skyscraper_stalk_of_mem_closure₀`: if `y ∈ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ S` at `y` is `S`.
* `skyscraper_stalk_of_not_mem_closure₀`: if `y ∉ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ S` at `y` is `*` the terminal object.

-/

noncomputable theory

section

open topological_space
open category_theory category_theory.limits
open Top
open opposite

universes u v w

variables {X : Top.{u}} (p₀ : X) {C : Type v} [category.{w} C] (S : C)
variables [has_terminal C] [Π (U : opens X), decidable (p₀ ∈ U)]

/--
A skyscraper presheaf is a presheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper presheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
@[simps] def skyscraper_presheaf : presheaf C X :=
{ obj := λ U, ite (p₀ ∈ unop U) S (terminal C),
  map := λ U V i, dite (p₀ ∈ unop V)
    (λ h, eq_to_hom (if_pos (le_of_hom i.unop h)) ≫ 𝟙 S ≫ eq_to_hom (if_pos h).symm)
    (λ h, terminal.from _ ≫ eq_to_hom (if_neg h).symm),
  map_id' := λ U,
  begin
    split_ifs,
    { simp, },
    { simpa only [eq_comp_eq_to_hom] using terminal_is_terminal.hom_ext _ _, },
  end,
  map_comp' := λ U V W iVU iWV,
  begin
    by_cases hW : p₀ ∈ unop W,
    { have hV : p₀ ∈ unop V := le_of_hom iWV.unop hW,
      have hU : p₀ ∈ unop U := le_of_hom iVU.unop hV,
      split_ifs,
      simp },
    { split_ifs;
      simpa only [eq_comp_eq_to_hom] using terminal_is_terminal.hom_ext _ _, }
  end }

section

variables {p₀}

lemma skyscraper_presheaf_obj_of_mem {U : opens X} (h : p₀ ∈ U) :
  (skyscraper_presheaf p₀ S).obj (op U) = S := if_pos h

lemma skyscraper_presheaf_obj_of_not_mem {U : opens X} (h : p₀ ∉ U) :
  (skyscraper_presheaf p₀ S).obj (op U) = terminal C := if_neg h

end

/--
A skyscraper sheaf is a sheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper sheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
def skyscraper_sheaf : sheaf C X :=
⟨skyscraper_presheaf p₀ S, λ c U s hs x hx,
  ⟨dite (p₀ ∈ U)
    (λ h, x (hs p₀ h).some_spec.some (hs p₀ h).some_spec.some_spec.1 ≫
        eq_to_hom ((skyscraper_presheaf_obj_of_mem S (hs p₀ h).some_spec.some_spec.2).trans
          (skyscraper_presheaf_obj_of_mem S h).symm))
    (λ h, terminal.from c ≫ (eq_to_hom (skyscraper_presheaf_obj_of_not_mem S h).symm)),
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
        exact terminal_is_terminal.hom_ext _ _, }
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
        exact terminal_is_terminal.hom_ext _ _, }
    end⟩⟩

end

section

-- In this section, we calculate the stalks for skyscraper presheaves.
-- We need to restrict universe level.

open topological_space
open category_theory category_theory.limits
open Top
open opposite

universes u v

variables {X : Top.{u}} (p₀ : X) {C : Type v} [category.{u} C] (S : C) [has_terminal C]

lemma mem_nhds_of_not_mem_closure_singleton {y : X} (h : ¬p₀ ⤳ y) :
  ∃ (U : open_nhds y), p₀ ∉ U.1 :=
begin
  have := (not_iff_not.mpr specializes_iff_forall_open).mp h,
  push_neg at this,
  rcases this with ⟨s, o, h₁, h₂⟩,
  exact ⟨⟨⟨s, o⟩, h₁⟩, h₂⟩,
end

variable [Π (U : opens X), decidable (p₀ ∈ U)]
/--
The cocone at `S` for the salk functor of `skyscraper_presheaf p₀ S` when `y ∈ closure {p₀}`
-/
@[simps] def skyscraper_presheaf_cocone_of_mem_closure₀ {y : X} (h : p₀ ⤳ y) :
  cocone ((open_nhds.inclusion y).op ⋙ skyscraper_presheaf p₀ S) :=
{ X := S,
  ι :=
  { app := λ U, eq_to_hom $ if_pos (h.mem_open U.unop.1.2 U.unop.2),
    naturality' := λ U V inc,
    begin
      simp only [functor.op_obj, unop_op, functor.comp_map, functor.op_map, skyscraper_presheaf_map,
        category.id_comp, eq_to_hom_trans, functor.const_obj_map, category.assoc],
      by_cases hV : p₀ ∈ (open_nhds.inclusion y).obj V.unop,
      { have hU : p₀ ∈ unop ((open_nhds.inclusion y).op.obj U) := le_of_hom inc.unop hV,
        split_ifs,
        erw [eq_to_hom_trans, category.comp_id],
        refl },
      { split_ifs with hU;
        erw [category.comp_id, category.assoc, eq_to_hom_trans, eq_comp_eq_to_hom, eq_to_hom_trans];
        exact terminal_is_terminal.hom_ext _ _, },
    end } }

/--
The canonical map `S ⟶ (skyscraper_presheaf p₀ S t).stalk y` when `y ∈ closure {p₀}`
-/
noncomputable def skyscraper_presheaf_from [has_colimits C] {y : X} :
  S ⟶ (skyscraper_presheaf p₀ S).stalk y :=
eq_to_hom (skyscraper_presheaf_obj_of_mem S (by tauto : p₀ ∈ ⊤)).symm ≫
  (skyscraper_presheaf p₀ S).germ (⟨y, trivial⟩ : (⊤ : opens X))

/--
The cocone at `S` for the salk functor of `skyscraper_presheaf p₀ S` when `y ∈ closure {p₀}` is a
colimit
-/
noncomputable def skyscraper_presheaf_cocone_of_mem_closure₀_is_colimit [has_colimits C]
  {y : X} (h : p₀ ⤳ y) : is_colimit (skyscraper_presheaf_cocone_of_mem_closure₀ p₀ S h) :=
{ desc := λ c, (skyscraper_presheaf_from p₀ S ≫ colimit.desc _ _ : S ⟶ c.X),
  fac' := λ c U,
  begin
    dsimp,
    simp only [skyscraper_presheaf_from, presheaf.germ, category.comp_id,
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
    simp only [skyscraper_presheaf_from, presheaf.germ, category.assoc],
    erw [colimit.ι_desc],
    specialize h (op ⟨⊤, trivial⟩),
    erw [←h],
    simp only [skyscraper_presheaf_cocone_of_mem_closure₀_ι_app, category.assoc,
      eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp],
  end }

/--
If `y ∈ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ S` at `y` is `S`
-/
@[reducible]
noncomputable def skyscraper_presheaf_stalk_of_mem_closure₀ [has_colimits C]
  {y : X} (h : p₀ ⤳ y) : (skyscraper_presheaf p₀ S).stalk y ≅ S :=
colimit.iso_colimit_cocone ⟨_, (skyscraper_presheaf_cocone_of_mem_closure₀_is_colimit p₀ S h)⟩

/--
The cocone at `*` for the salk functor of `skyscraper_presheaf p₀ S` when `y ∉ closure {p₀}`
-/
@[simps] def skyscraper_presheaf_cocone {y : X} :
  cocone ((open_nhds.inclusion y).op ⋙ skyscraper_presheaf p₀ S) :=
{ X := terminal C,
  ι :=
  { app := λ U, terminal.from _,
    naturality' := λ U V inc, terminal_is_terminal.hom_ext _ _ } }

/--
The canonical map `* ⟶ (skyscraper_presheaf p₀ S).stalk y` when `y ∉ closure {p₀}`
-/
noncomputable def skyscraper_presheaf_of_not_mem_closure₀_from [has_colimits C]
  {y : X} (h : ¬p₀ ⤳ y) : terminal C ⟶ (skyscraper_presheaf p₀ S).stalk y :=
eq_to_hom (skyscraper_presheaf_obj_of_not_mem S $
  (mem_nhds_of_not_mem_closure_singleton p₀ h).some_spec).symm ≫
  (skyscraper_presheaf p₀ S).germ (⟨y, (mem_nhds_of_not_mem_closure_singleton p₀ h).some.2⟩ :
    (mem_nhds_of_not_mem_closure_singleton p₀ h).some.1)

/--
The cocone at `*` for the salk functor of `skyscraper_presheaf p₀ S` when `y ∉ closure {p₀}` is a
colimit
-/
noncomputable def skyscraper_presheaf_cocone_of_not_mem_closure₀_is_colimit [has_colimits C]
  {y : X} (h : ¬p₀ ⤳ y) : is_colimit (skyscraper_presheaf_cocone p₀ S) :=
{ desc := λ c, (eq_to_hom ((skyscraper_presheaf_obj_of_not_mem _
      (mem_nhds_of_not_mem_closure_singleton p₀ h).some_spec).symm)) ≫
    presheaf.germ (skyscraper_presheaf p₀ S)
      ⟨y, (mem_nhds_of_not_mem_closure_singleton p₀ h).some.2⟩ ≫ colimit.desc _ _,
  fac' := λ c U,
  begin
    simp only [presheaf.germ, skyscraper_presheaf_cocone_ι_app],
    erw [colimit.ι_desc],
    dsimp,
    by_cases h' : p₀ ∈ (open_nhds.inclusion y).obj (unop U),
    { have eq1 : terminal.from (ite (p₀ ∈ (open_nhds.inclusion y).obj (unop U)) S (terminal C)) =
          eq_to_hom (if_pos h') ≫ terminal.from _ := terminal_is_terminal.hom_ext _ _,
      rw [eq1, category.assoc, eq_eq_to_hom_comp],
      have := c.ι.naturality (hom_of_le (le_top : U.unop ≤ ⊤)).op,
      dsimp at this,
      have h'' : p₀ ∈ (open_nhds.inclusion y).obj ⊤ := trivial,
      split_ifs at this,
      rw [category.comp_id, category.id_comp, eq_to_hom_trans, eq_eq_to_hom_comp] at this,
      rw [this, ←category.assoc _ _ (c.ι.app (op ⊤)), eq_to_hom_trans],
      clear this,
      have := c.ι.naturality
        (hom_of_le (le_top : (mem_nhds_of_not_mem_closure_singleton p₀ h).some ≤ ⊤)).op,
      dsimp at this,
      have h''' : p₀ ∉ (mem_nhds_of_not_mem_closure_singleton p₀ h).some.1 :=
        (mem_nhds_of_not_mem_closure_singleton p₀ h).some_spec,
      split_ifs at this,
      have eq2 : terminal.from (ite (p₀ ∈ (open_nhds.inclusion y).obj ⊤) S (terminal C)) =
        eq_to_hom (if_pos h'') ≫ terminal.from _ := terminal_is_terminal.hom_ext _ _,
      rw [category.comp_id, eq2, category.assoc, category.assoc] at this,
      simp only [←this, ←category.assoc],
      convert eq_whisker _ _,
      { ext, refl, },
      { rw [eq_comp_eq_to_hom],
        exact terminal_is_terminal.hom_ext _ _ } },
    { have eq1 : terminal.from (ite (p₀ ∈ (open_nhds.inclusion y).obj (unop U)) S (terminal C)) =
        eq_to_hom (if_neg h') := terminal_is_terminal.hom_ext _ _,
      have eq2 : terminal.from (ite (p₀ ∈ (open_nhds.inclusion y).obj ⊤) S (terminal C)) =
        eq_to_hom (if_pos trivial) ≫ terminal.from _ := terminal_is_terminal.hom_ext _ _,
      have eq3 : terminal.from (ite (p₀ ∈ (open_nhds.inclusion y).obj
          (mem_nhds_of_not_mem_closure_singleton p₀ h).some) S (terminal C)) =
        eq_to_hom (if_neg (mem_nhds_of_not_mem_closure_singleton p₀ h).some_spec):=
      terminal_is_terminal.hom_ext _ _,
      rw [eq1, ←category.assoc, eq_to_hom_trans],
      have := c.ι.naturality (hom_of_le (inf_le_left :
          (mem_nhds_of_not_mem_closure_singleton p₀ h).some ⊓ unop U ≤
          (mem_nhds_of_not_mem_closure_singleton p₀ h).some)).op,
      dsimp at this,
      rw [dite_comp, category.comp_id] at this,
      simp_rw [category.id_comp, eq_to_hom_trans, eq3, eq_to_hom_trans] at this,
      generalize_proofs h₁ h₂ h₃ h₄ at this,
      have h' : p₀ ∉ (open_nhds.inclusion y).obj (h₁.some ⊓ unop U) := λ r, h₁.some_spec r.1,
      split_ifs at this,
      { exfalso, exact h₁.some_spec (by assumption), },
      have eq_coe : c.ι.app (op ⟨h₁.some.1, h₂⟩) =
        eq_to_hom (by { congr, ext, refl }) ≫ c.ι.app (op h₁.some) ≫
          eq_to_hom (by { congr, ext, refl }),
      { symmetry,
        rw [eq_eq_to_hom_comp],
        have e := c.ι.naturality (eq_to_hom (by {ext, refl}) :
          (⟨h₁.some.1, h₂⟩ : open_nhds y) ⟶ h₁.some).op,
        dsimp at e,
        split_ifs at e with temp,
        rw [category.comp_id, show terminal.from (ite (p₀ ∈ (open_nhds.inclusion y).obj h₁.some)
          S (terminal C)) = eq_to_hom (if_neg h₁.some_spec), from terminal_is_terminal.hom_ext _ _,
          eq_to_hom_trans, eq_to_hom_refl, category.id_comp] at e,
        rw [←e, eq_to_hom_refl, category.comp_id, eq_to_hom_refl, category.id_comp], },
      erw [eq_coe, ←this, ←category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id,
        ←category.assoc, eq_to_hom_trans],
      clear this,
      have := c.ι.naturality (hom_of_le (inf_le_right :
          (mem_nhds_of_not_mem_closure_singleton p₀ h).some ⊓ unop U ≤ unop U)).op,
      dsimp at this,
      rw [dite_comp, category.comp_id] at this,
      split_ifs at this,
      rw [←this, eq1, eq_to_hom_trans], }
  end,
  uniq' := λ c f H,
  begin
    erw [colimit.ι_desc, ←H],
    simp only [skyscraper_presheaf_cocone_ι_app],
    dsimp,
    have : terminal.from
      (ite (p₀ ∈ (mem_nhds_of_not_mem_closure_singleton p₀ h).some.1) S (terminal C)) =
      eq_to_hom (if_neg (mem_nhds_of_not_mem_closure_singleton p₀ h).some_spec) :=
    terminal_is_terminal.hom_ext _ _,
    erw [this, ←category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.id_comp]
  end }

/--
 If `y ∉ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ S` at `y` is `*`
 -/
@[reducible]
noncomputable def skyscraper_presheaf_stalk_of_not_mem_closure₀ [has_colimits C]
  {y : X} (h : ¬p₀ ⤳ y) : (skyscraper_presheaf p₀ S).stalk y ≅ terminal C :=
colimit.iso_colimit_cocone ⟨_, (skyscraper_presheaf_cocone_of_not_mem_closure₀_is_colimit _ S h)⟩

end

section

/-!
Skyscraper sheaf alternatively can be defined as the pushforward of a sheaf on a single point space
`{p₀}` defined by `∅ ↦ *` and `{p₀} ↦ S` under the inclusion `{p₀} ↪ X`.
-/

open topological_space
open category_theory category_theory.limits
open Top
open opposite
open_locale classical

universes u v w

variables {X : Top.{u}} (p₀ : X) {C : Type v} [category.{w} C] (S : C) [has_terminal C]

/--The topological space with on a point `{p₀}`. Hence the only open sets are ∅ and ⊤.-/
def single_point_space : Top := ⟨({p₀} : set X), infer_instance⟩

instance : inhabited (single_point_space p₀) := ⟨⟨p₀, rfl⟩⟩
instance : unique (single_point_space p₀) := unique.subtype_eq p₀

/--
The presheaf on a single point space `{p₀}` defined by `∅ ↦ *` and `{p₀} ↦ S`
-/
@[simps]
noncomputable def single_point_presheaf : presheaf C (single_point_space p₀) :=
{ obj := λ U, if U.unop ≠ ⊥ then S else terminal C,
  map := λ U V inc, if h : V.unop ≠ ⊥
    then eq_to_hom (if_pos $ λ r, h $ le_bot_iff.mp $ r ▸ le_of_hom inc.unop) ≫
      𝟙 S ≫ eq_to_hom (if_pos h).symm
    else terminal.from _ ≫ eq_to_hom (if_neg h).symm,
  map_id' := λ U,
  begin
    split_ifs,
    { rw [category.id_comp, eq_to_hom_trans, eq_to_hom_refl] },
    { rw [eq_comp_eq_to_hom, category.id_comp],
      exact terminal_is_terminal.hom_ext _ _, },
  end,
  map_comp' := λ U V W inc1 inc2,
  begin
    rw comp_dite,
    by_cases hW : W.unop ≠ ⊥,
    { have hV : V.unop ≠ ⊥,
      { intros r,
        refine hW (eq_bot_iff.mpr (r ▸ le_of_hom inc2.unop)), },
      have hU : U.unop ≠ ⊥,
      { intros r,
        refine hW (eq_bot_iff.mpr (r ▸ le_of_hom (inc1 ≫ inc2).unop)) },
      split_ifs,
      simp only [category.id_comp, eq_to_hom_trans], },
    { split_ifs;
      rw [eq_comp_eq_to_hom, category.assoc, category.assoc, eq_to_hom_trans,
        eq_to_hom_refl, category.comp_id];
      exact terminal_is_terminal.hom_ext _ _, },
  end }

/--
The trivial inclusion `{p₀} ↪ X`.
-/
@[simps] def single_point_inclusion : single_point_space p₀ ⟶ X :=
{ to_fun := λ p, p.1,
  continuous_to_fun := by continuity }

/--
The morphism from skyscraper presheaf to pushforward sheaf
-/
@[simps] noncomputable def skyscraper_presheaf_to_pushforward :
  skyscraper_presheaf p₀ S ⟶ (single_point_inclusion p₀) _* (single_point_presheaf p₀ S) :=
{ app := λ U, if h : p₀ ∈ U.unop
    then eq_to_hom (skyscraper_presheaf_obj_of_mem _ h) ≫ eq_to_hom
    begin
      dsimp,
      rw if_pos,
      erw opens.map_obj _ _ U.unop.2,
      change _ ≠ ⊥,
      rw opens.ne_bot_iff_nonempty,
      refine ⟨⟨p₀, rfl⟩, _⟩,
      erw set.mem_preimage,
      exact h,
    end
    else terminal.from _ ≫ eq_to_hom
    begin
      dsimp,
      rw if_neg,
      push_neg,
      rw ←opens.not_nonempty_iff_eq_bot,
      rintros ⟨⟨x, hx₁⟩, hx₂⟩,
      rw set.mem_singleton_iff at hx₁,
      subst hx₁,
      erw set.mem_preimage at hx₂,
      exact h hx₂,
    end,
  naturality' := λ U V inc,
  begin
    by_cases hV : p₀ ∈ V.unop,
    { have hU : p₀ ∈ U.unop := le_of_hom inc.unop hV,
      have hV' : ¬(opens.map (single_point_inclusion p₀)).obj (unop V) = ⊥,
      { change _ ≠ ⊥,
        rw opens.ne_bot_iff_nonempty,
        refine ⟨⟨p₀, rfl⟩, _⟩,
        erw set.mem_preimage,
        exact hV, },
      rw [comp_dite, dite_comp],
      split_ifs,
      { exfalso, exact hV' h, },
      { dsimp,
        split_ifs,
        simp only [eq_to_hom_trans, category.id_comp], }, },
    { split_ifs;
      rw [←category.assoc, eq_comp_eq_to_hom];
      exact terminal_is_terminal.hom_ext _ _ },
  end }

/--
The morphism from pushforward sheaf to skyscraper presheaf
-/
@[simps] noncomputable def pushforward_to_skyscraper_presheaf :
  (single_point_inclusion p₀) _* (single_point_presheaf p₀ S) ⟶
  skyscraper_presheaf p₀ S :=
{ app := λ U, if h : p₀ ∈ unop U
    then eq_to_hom
    begin
      dsimp,
      rw if_pos,
      erw opens.map_obj _ _ U.unop.2,
      change _ ≠ ⊥,
      rw opens.ne_bot_iff_nonempty,
      refine ⟨⟨p₀, rfl⟩, _⟩,
      erw set.mem_preimage,
      exact h,
    end ≫ eq_to_hom (skyscraper_presheaf_obj_of_mem _ h).symm
    else terminal.from _ ≫ eq_to_hom (skyscraper_presheaf_obj_of_not_mem _ h).symm,
  naturality' := λ U V inc,
  begin
    rw [comp_dite, dite_comp],
    by_cases hV : p₀ ∈ V.unop,
    { have hU : p₀ ∈ U.unop := le_of_hom inc.unop hV,
      have hV' : ¬(opens.map (single_point_inclusion p₀)).obj (unop V) = ⊥,
      { change _ ≠ ⊥,
        rw opens.ne_bot_iff_nonempty,
        refine ⟨⟨p₀, rfl⟩, _⟩,
        erw set.mem_preimage,
        exact hV, },
      split_ifs,
      { exfalso, exact hV' h, },
      { dsimp,
        split_ifs;
        rw [eq_to_hom_trans, category.id_comp, eq_to_hom_trans, eq_to_hom_trans,
          category.id_comp, eq_to_hom_trans, eq_to_hom_trans, eq_to_hom_trans], }, },
    { split_ifs;
      rw [←category.assoc, eq_comp_eq_to_hom];
      exact terminal_is_terminal.hom_ext _ _ },
  end }

/--
Skyscraper presheaf is isomorphic to pushforward of sheaf on single point.
-/
noncomputable def skyscraper_presheaf_as_pushforward :
  skyscraper_presheaf p₀ S ≅ (single_point_inclusion p₀) _* (single_point_presheaf p₀ S) :=
{ hom := skyscraper_presheaf_to_pushforward p₀ S,
  inv := pushforward_to_skyscraper_presheaf p₀ S,
  hom_inv_id' :=
  begin
    ext U,
    dsimp,
    split_ifs,
    { rw [eq_to_hom_trans, category.id_comp, eq_to_hom_trans, eq_to_hom_trans,
        eq_to_hom_refl], },
    { rw [←category.assoc, eq_comp_eq_to_hom],
      exact ts.hom_ext _ _, },
  end,
  inv_hom_id' :=
  begin
    ext U,
    dsimp,
    by_cases hU : p₀ ∈ U.unop,
    { split_ifs;
      rw [category.id_comp, eq_to_hom_trans, category.id_comp, eq_to_hom_trans, eq_to_hom_trans,
          eq_to_hom_refl], },
    { split_ifs;
      rw [←category.assoc, eq_comp_eq_to_hom];
      exact ts.hom_ext _ _, },
  end }

end

section adjoints

open topological_space
open category_theory category_theory.limits
open Top
open opposite

universes u v

variables {X : Top.{u}} (p₀ : X) {C : Type v} [category.{u} C]
variables {star : C} (ts : is_terminal star)
variable [Π (U : opens X), decidable (p₀ ∈ U)]

@[simps]
def skyscraper_presheaf_functor : C ⥤ presheaf C X :=
{ obj := λ S, skyscraper_presheaf p₀ S ts,
  map := λ x y f,
  { app := λ U, if h : p₀ ∈ U.unop
    then eq_to_hom (skyscraper_presheaf_obj_of_mem _ _ h) ≫ f ≫
      eq_to_hom (skyscraper_presheaf_obj_of_mem _ _ h).symm
    else ts.from _ ≫ eq_to_hom (skyscraper_presheaf_obj_of_not_mem _ _ h).symm,
    naturality' := λ U V inc,
    begin
      dsimp,
      simp_rw [category.id_comp, eq_to_hom_trans],
      by_cases hV : p₀ ∈ V.unop,
      { have hU : p₀ ∈ U.unop := le_of_hom inc.unop hV,
        split_ifs,
        rw [←category.assoc, eq_to_hom_trans, category.assoc, category.assoc, eq_to_hom_trans],
        refl, },
      { split_ifs;
        rw [←category.assoc, eq_comp_eq_to_hom];
        exact ts.hom_ext _ _ }
    end },
  map_id' := λ c,
  begin
    ext U,
    dsimp,
    split_ifs,
    { simp, },
    { rw [eq_comp_eq_to_hom],
      exact ts.hom_ext _ _ },
  end,
  map_comp' := λ x y z f g,
  begin
    ext U,
    dsimp,
    split_ifs,
    { simp },
    { rw [eq_comp_eq_to_hom],
      exact ts.hom_ext _ _ },
  end }

example : true := trivial

@[simps]
def skyscraper_sheaf_functor : C ⥤ sheaf C X :=
{ obj := λ S, skyscraper_sheaf p₀ S ts,
  map := λ x y f, ⟨(skyscraper_presheaf_functor p₀ ts).map f⟩,
  map_id' := λ c,
  begin
    ext1,
    exact (skyscraper_presheaf_functor p₀ ts).map_id c,
  end,
  map_comp' := λ x y z f g,
  begin
    ext1,
    exact (skyscraper_presheaf_functor p₀ ts).map_comp f g,
  end }

variable [has_colimits C]

@[simps]
noncomputable def from_stalk_to_to_skyscraper_presheaf {𝓕 : presheaf C X} {c : C}
  (f : 𝓕.stalk p₀ ⟶ c) : 𝓕 ⟶ skyscraper_presheaf p₀ c ts :=
{ app := λ U, if h : p₀ ∈ U.unop
  then 𝓕.germ ⟨p₀, h⟩ ≫ f ≫ eq_to_hom (skyscraper_presheaf_obj_of_mem _ _ h).symm
  else ts.from _ ≫ eq_to_hom (skyscraper_presheaf_obj_of_not_mem _ _ h).symm,
  naturality' := λ U V inc,
  begin
    dsimp,
    by_cases hV : p₀ ∈ V.unop,
    { have hU : p₀ ∈ U.unop := le_of_hom inc.unop hV,
      split_ifs,
      erw [←category.assoc, 𝓕.germ_res inc.unop, category.id_comp, eq_to_hom_trans,
        category.assoc, category.assoc, eq_to_hom_trans],
      refl, },
    { split_ifs,
      rw [←category.assoc, eq_comp_eq_to_hom, category.assoc, category.assoc, eq_to_hom_trans,
        eq_to_hom_refl, category.comp_id],
      exact ts.hom_ext _ _ },
  end }

@[reducible]
noncomputable def to_skyscraper_presheaf_to_from_stalk {𝓕 : presheaf C X} {c : C}
  (f : 𝓕 ⟶ skyscraper_presheaf p₀ c ts) : 𝓕.stalk p₀ ⟶ c :=
let CC : cocone ((open_nhds.inclusion p₀).op ⋙ 𝓕) :=
{ X := c,
  ι :=
  { app := λ U, f.app (op U.unop.1) ≫ eq_to_hom
    begin
      dsimp,
      rw if_pos,
      exact U.unop.2,
    end,
    naturality' := λ U V inc,
    begin
      dsimp,
      rw [category.comp_id, ←category.assoc, eq_comp_eq_to_hom, category.assoc, eq_to_hom_trans],
      generalize_proofs h,
      erw f.naturality,
      dsimp,
      have hV : p₀ ∈ (open_nhds.inclusion p₀).obj V.unop := V.unop.2,
      split_ifs,
      rw [category.id_comp, eq_to_hom_trans, eq_comp_eq_to_hom, category.assoc, eq_to_hom_trans,
        eq_to_hom_refl, category.comp_id],
      refl,
    end} } in
colimit.desc _ CC

lemma from_stalk_to_to_skyscraper_presheaf_to_skyscraper_presheaf_to_from_stalk
  {𝓕 : presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
to_skyscraper_presheaf_to_from_stalk p₀ ts (from_stalk_to_to_skyscraper_presheaf p₀ ts f) = f :=
begin
  ext U,
  dsimp,
  simp only [subtype.val_eq_coe, unop_op, colimit.ι_desc, from_stalk_to_to_skyscraper_presheaf_app],
  split_ifs,
  { rw [category.assoc, category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id],
    congr,
    dunfold presheaf.germ,
    dsimp,
    congr,
    convert op_unop _,
    ext,
    refl, },
  { exfalso, exact h U.unop.2,  }
end

lemma to_skyscraper_presheaf_to_from_stalk_from_stalk_to_to_skyscraper_presheaf
  {𝓕 : presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraper_presheaf p₀ c ts) :
from_stalk_to_to_skyscraper_presheaf p₀ ts (to_skyscraper_presheaf_to_from_stalk p₀ ts f) = f :=
begin
  ext U,
  dsimp,
  split_ifs,
  { rw [to_skyscraper_presheaf_to_from_stalk],
    dsimp,
    dunfold presheaf.germ,
    rw [←category.assoc, colimit.ι_desc],
    dsimp,
    rw [category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id], },
  { rw [eq_comp_eq_to_hom],
    exact ts.hom_ext _ _ , }
end

@[simps]
noncomputable def stalk_skyscraper_presheaf_adj_unit :
  𝟭 (presheaf C X) ⟶ presheaf.stalk_functor C p₀ ⋙ skyscraper_presheaf_functor p₀ ts :=
{ app := λ 𝓕,
  { app := λ U, if h : p₀ ∈ U.unop
    then 𝓕.germ ⟨p₀, h⟩ ≫ eq_to_hom (if_pos h).symm
    else ts.from _ ≫ eq_to_hom (if_neg h).symm,
    naturality' := λ U V inc,
    begin
      dsimp,
      by_cases hV : p₀ ∈ V.unop,
      { have hU : p₀ ∈ U.unop := le_of_hom inc.unop hV,
        split_ifs,
        erw [←category.assoc, 𝓕.germ_res inc.unop, category.id_comp, eq_to_hom_trans,
          category.assoc, eq_to_hom_trans],
        congr, },
      { split_ifs,
        rw [←category.assoc, eq_comp_eq_to_hom],
        exact ts.hom_ext _ _, },
    end },
  naturality' := λ 𝓕 𝓖 f,
  begin
    ext U,
    dsimp,
    split_ifs,
    { rw [←category.assoc, eq_comp_eq_to_hom],
      simp only [category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id],
      rw [←category.assoc _ _ ((presheaf.stalk_functor C p₀).map f), eq_to_hom_trans,
        eq_to_hom_refl, category.id_comp],
      erw [colimit.ι_map],
      congr, },
    { rw [←category.assoc, eq_comp_eq_to_hom],
      exact ts.hom_ext _ _ },
  end }

@[simps]
noncomputable def stalk_skyscraper_presheaf_adj_counit :
  skyscraper_presheaf_functor p₀ ts ⋙ presheaf.stalk_functor C p₀ ⟶ 𝟭 C :=
{ app := λ c, (skyscraper_presheaf_stalk_of_mem_closure₀ p₀ c ts (specializes_rfl : p₀ ⤳ p₀)).hom,
  naturality' := λ x y f,
  begin
    ext U,
    dsimp,
    simp only [colimit.iso_colimit_cocone_ι_hom_assoc,
      skyscraper_presheaf_cocone_of_mem_closure₀_ι_app, category.assoc],
    erw [category.id_comp, ←category.assoc, colimit.ι_map],
    dsimp,
    split_ifs,
    { rw [category.assoc, skyscraper_presheaf_stalk_of_mem_closure₀,
        colimit.iso_colimit_cocone_ι_hom],
      dsimp,
      simpa, },
    { exfalso, exact h U.unop.2 }
  end }

noncomputable def stalk_skyscraper_presheaf_adj :
  presheaf.stalk_functor C p₀ ⊣ skyscraper_presheaf_functor p₀ ts :=
{ hom_equiv := λ 𝓕 c, ⟨from_stalk_to_to_skyscraper_presheaf p₀ ts,
    to_skyscraper_presheaf_to_from_stalk p₀ ts,
    from_stalk_to_to_skyscraper_presheaf_to_skyscraper_presheaf_to_from_stalk p₀ ts,
    to_skyscraper_presheaf_to_from_stalk_from_stalk_to_to_skyscraper_presheaf p₀ ts⟩,
  unit := stalk_skyscraper_presheaf_adj_unit p₀ ts,
  counit := stalk_skyscraper_presheaf_adj_counit p₀ ts,
  hom_equiv_unit' := λ 𝓕 𝓖 f,
  begin
    ext U,
    dsimp,
    split_ifs,
    { simp, },
    { rw [eq_comp_eq_to_hom],
      exact ts.hom_ext _ _ },
  end,
  hom_equiv_counit' := λ 𝓕 c g,
  begin
    ext U,
    dsimp,
    erw [colimit.ι_desc, ←category.assoc, colimit.ι_map, category.assoc,
      colimit.iso_colimit_cocone_ι_hom],
    dsimp,
    rw [category.comp_id],
    refl,
  end }

example : true := trivial

noncomputable def stalk_skyscraper_sheaf_adj :
  sheaf.forget C X ⋙ presheaf.stalk_functor _ p₀ ⊣ skyscraper_sheaf_functor p₀ ts :=
{ hom_equiv := λ 𝓕 c,
  ⟨λ f, ⟨from_stalk_to_to_skyscraper_presheaf p₀ ts f⟩,
   λ g, to_skyscraper_presheaf_to_from_stalk p₀ ts g.1,
   λ f, from_stalk_to_to_skyscraper_presheaf_to_skyscraper_presheaf_to_from_stalk
     p₀ ts f,
   begin
     intros g,
     ext1,
     exact to_skyscraper_presheaf_to_from_stalk_from_stalk_to_to_skyscraper_presheaf p₀ ts g.1,
   end⟩,
  unit :=
  { app := λ 𝓕, ⟨(stalk_skyscraper_presheaf_adj_unit p₀ ts).app 𝓕.1⟩,
    naturality' := λ 𝓐 𝓑 ⟨f⟩,
    begin
      ext1,
      dsimp,
      exact (stalk_skyscraper_presheaf_adj_unit p₀ ts).naturality f,
    end },
  counit := stalk_skyscraper_presheaf_adj_counit p₀ ts,
  hom_equiv_unit' :=
  begin
    intros 𝓐 c f,
    ext1,
    exact (stalk_skyscraper_presheaf_adj p₀ ts).hom_equiv_unit,
  end,
  hom_equiv_counit' := λ 𝓐 c f, (stalk_skyscraper_presheaf_adj p₀ ts).hom_equiv_counit }

end adjoints

section injective

open_locale zero_object
open topological_space
open category_theory category_theory.limits
open Top
open opposite

universe u
variables {X : Top.{u}} (p₀ : X) [Π (U : opens X), decidable (p₀ ∈ U)]

lemma skyscraper_presheaf_in_Ab_injective (S : Ab.{u}) [injective S] :
  injective (skyscraper_sheaf p₀ S (is_zero.is_terminal (is_zero_zero _) : is_terminal (0 : Ab))) :=
injective.injective_of_adjoint
    (stalk_skyscraper_sheaf_adj p₀ (is_zero.is_terminal (is_zero_zero _) : is_terminal (0 : Ab)))

end injective
