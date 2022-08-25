/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.sheafed_space
import topology.sheaves.sheaf_condition.opens_le_cover
import topology.sheaves.stalks
import category_theory.preadditive.injective

/-!
# Skyscraper (pre)sheaves

A skyscraper (pre)sheaf is a (pre)sheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper (pre)sheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.

## Main definitions

* `skyscraper_presheaf`: `skyscraper_presheaf p₀ A` is the skyscraper presheaf at point `p₀` with
  value `A`.
* `skyscraper_sheaf`: the skyscraper presheaf satisfies the sheaf condition.

## Main statements

* `skyscraper_presheaf_stalk_of_specializes`: if `y ∈ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ S` at `y` is `S`.
* `skyscraper_presheaf_stalk_of_not_specializes`: if `y ∉ closure {p₀}` then the stalk of
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
{ obj := λ U, if p₀ ∈ unop U then S else terminal C,
  map := λ U V i, if h : p₀ ∈ unop V
    then eq_to_hom $ by erw [if_pos h, if_pos (le_of_hom i.unop h)]
    else (terminal_is_terminal.if_neg h).from _,
  map_id' := λ U,
  begin
    split_ifs,
    { apply eq_to_hom_refl },
    { exact (terminal_is_terminal.if_neg h).hom_ext _ _ },
  end,
  map_comp' := λ U V W iVU iWV,
  begin
    by_cases hW : p₀ ∈ unop W,
    { have hV : p₀ ∈ unop V := le_of_hom iWV.unop hW,
      simp only [dif_pos hW, dif_pos hV, eq_to_hom_trans] },
    { rw [dif_neg hW], apply (terminal_is_terminal.if_neg hW).hom_ext }
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
⟨_, (skyscraper_presheaf p₀ S).is_sheaf_iff_is_sheaf_opens_le_cover.mpr $ λ ι U, nonempty.intro
 { lift := λ c, if h : p₀ ∈ (presheaf.sheaf_condition.opens_le_cover_cocone U).X
    then c.π.app (op ⟨_, ⟨(opens.mem_supr.mp h).some, le_refl _⟩⟩) ≫ eq_to_hom
      begin
       dsimp, rw [if_pos h, if_pos (opens.mem_supr.mp h).some_spec],
      end
    else (terminal_is_terminal.if_neg h).from _,
   fac' := λ c j,
   begin
    dsimp, split_ifs with h0, swap,
    { exact (terminal_is_terminal.if_neg h0).hom_ext _ _, },
    by_cases h1 : p₀ ∈ (presheaf.sheaf_condition.opens_le_cover_cocone U).X;
    split_ifs, swap,
    { rw [eq_comp_eq_to_hom], exact (terminal_is_terminal.if_neg h1).hom_ext _ _, },
    rw [category.assoc, eq_to_hom_trans],
    transitivity c.π.app (op ⟨U (opens.mem_supr.mp h1).some ⊓ j.unop.obj, ⟨_, inf_le_left⟩⟩) ≫
      eq_to_hom _,
    rotate, { dsimp, rw [if_pos h0, if_pos], exact ⟨(opens.mem_supr.mp h1).some_spec, h0⟩ },
    { have := @nat_trans.naturality _ _ _ _ _ _ c.π j
        (op ⟨U (opens.mem_supr.mp h1).some ⊓ j.unop.obj, ⟨_, inf_le_left⟩⟩)
        (quiver.hom.op (hom_of_le _) : op j.unop ⟶ _), swap, exact inf_le_right,
      dsimp at this, simp only [category.id_comp] at this,
      have h : p₀ ∈ U _ ⊓ j.unop.obj := ⟨(opens.mem_supr.mp h1).some_spec, h0⟩,
      split_ifs at this with h', swap, { exact false.elim (h' h), },
      rw [this, category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id] },
    { have := @nat_trans.naturality _ _ _ _ _ _ c.π
        (op ⟨_, ⟨(opens.mem_supr.mp h1).some, le_refl _⟩⟩)
        (op ⟨U (opens.mem_supr.mp h1).some ⊓ j.unop.obj, ⟨_, inf_le_left⟩⟩)
        (quiver.hom.op (hom_of_le inf_le_left)),
      dsimp at this, simp only [category.id_comp] at this,
      have h : p₀ ∈ U _ ⊓ j.unop.obj := ⟨(opens.mem_supr.mp h1).some_spec, h0⟩,
      split_ifs at this with h', swap, { exact false.elim (h' h), },
      rw [this, category.assoc, eq_to_hom_trans], },
   end,
   uniq' := λ s f h0,
   begin
    dsimp at *, split_ifs with h1, swap, { exact (terminal_is_terminal.if_neg h1).hom_ext _ _ },
    specialize h0 (op ⟨_, ⟨(opens.mem_supr.mp h1).some, le_refl _⟩⟩),
    split_ifs at h0 with h2, swap, { exact false.elim (h2 (opens.mem_supr.mp h1).some_spec) },
    rw [←h0, category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id],
   end }⟩

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

private lemma mem_nhds_of_not_specializes {y : X} (h : ¬p₀ ⤳ y) :
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
@[simps] def skyscraper_presheaf_cocone_of_specializes {y : X} (h : p₀ ⤳ y) :
  cocone ((open_nhds.inclusion y).op ⋙ skyscraper_presheaf p₀ S) :=
{ X := S,
  ι := eq_to_hom $ category_theory.functor.ext
  begin
    intros U, dsimp, rw if_pos, exact h.mem_open U.unop.1.2 U.unop.2,
  end
  begin
    intros U V inc,
    dsimp, rw [category.id_comp, eq_to_hom_trans],
    have hV : p₀ ∈ (open_nhds.inclusion y).obj (unop V) := h.mem_open V.unop.1.2 V.unop.2,
    have hU : p₀ ∈ (open_nhds.inclusion y).obj (unop U):= h.mem_open U.unop.1.2 U.unop.2,
    split_ifs, refl,
  end }

/--
The canonical map `S ⟶ (skyscraper_presheaf p₀ S t).stalk y` when `y ∈ closure {p₀}`
-/
noncomputable def skyscraper_presheaf_from [has_colimits C] {y : X} :
  S ⟶ (skyscraper_presheaf p₀ S).stalk y :=
eq_to_hom (skyscraper_presheaf_obj_of_mem S (by trivial : p₀ ∈ ⊤)).symm ≫
  (skyscraper_presheaf p₀ S).germ (⟨y, trivial⟩ : (⊤ : opens X))

/--
The cocone at `S` for the stalk functor of `skyscraper_presheaf p₀ S` when `y ∈ closure {p₀}` is a
colimit
-/
noncomputable def skyscraper_presheaf_cocone_is_colimit_of_specializes [has_colimits C]
  {y : X} (h : p₀ ⤳ y) : is_colimit (skyscraper_presheaf_cocone_of_specializes p₀ S h) :=
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
    rw [category.comp_id, eq_eq_to_hom_comp] at this,
    rw [eq_to_hom_app, ←category.assoc, eq_to_hom_trans, this],
    congr,
  end,
  uniq' := λ c f h,
  begin
    simp only [skyscraper_presheaf_from, presheaf.germ, category.assoc],
    erw [colimit.ι_desc],
    specialize h (op ⟨⊤, trivial⟩),
    erw [←h],
    simp only [skyscraper_presheaf_cocone_of_specializes_ι, eq_to_hom_app,
      eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp],
  end }

/--
If `y ∈ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ S` at `y` is `S`
-/
@[reducible]
noncomputable def skyscraper_presheaf_stalk_of_specializes [has_colimits C]
  {y : X} (h : p₀ ⤳ y) : (skyscraper_presheaf p₀ S).stalk y ≅ S :=
colimit.iso_colimit_cocone ⟨_, skyscraper_presheaf_cocone_is_colimit_of_specializes p₀ S h⟩

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
noncomputable def skyscraper_presheaf_of_not_specializes [has_colimits C]
  {y : X} (h : ¬p₀ ⤳ y) : terminal C ⟶ (skyscraper_presheaf p₀ S).stalk y :=
eq_to_hom (skyscraper_presheaf_obj_of_not_mem S $
  (mem_nhds_of_not_specializes p₀ h).some_spec).symm ≫
  (skyscraper_presheaf p₀ S).germ (⟨y, (mem_nhds_of_not_specializes p₀ h).some.2⟩ :
    (mem_nhds_of_not_specializes p₀ h).some.1)

/--
The cocone at `*` for the salk functor of `skyscraper_presheaf p₀ S` when `y ∉ closure {p₀}` is a
colimit
-/
noncomputable def skyscraper_presheaf_cocone_is_colimit_of_not_specializes [has_colimits C]
  {y : X} (h : ¬p₀ ⤳ y) : is_colimit (skyscraper_presheaf_cocone p₀ S) :=
{ desc := λ c, (eq_to_hom ((skyscraper_presheaf_obj_of_not_mem _
      (mem_nhds_of_not_specializes p₀ h).some_spec).symm)) ≫
    presheaf.germ (skyscraper_presheaf p₀ S)
      ⟨y, (mem_nhds_of_not_specializes p₀ h).some.2⟩ ≫ colimit.desc _ _,
  fac' := λ c U,
  begin
    simp only [presheaf.germ, skyscraper_presheaf_cocone_ι_app],
    erw [colimit.ι_desc],
    dsimp,
    generalize_proofs h1 h2 h3,
    have eq0 : c.ι.app (op {obj := h1.some.1, property := h1.some.2}) =
      eq_to_hom (by { congr, ext, refl }) ≫ c.ι.app (op h1.some) ≫
      eq_to_hom (by { congr, ext, refl }),
    { symmetry, rw [eq_eq_to_hom_comp], symmetry,
      convert (c.ι.naturality) _, swap,
      { refine eq_to_hom _, congr, ext, refl, },
      { rw eq_to_hom_map, }, },
    erw [eq0, ←category.assoc (eq_to_hom h3), eq_to_hom_trans, ←category.assoc, ←category.assoc,
      eq_comp_eq_to_hom, eq_to_hom_refl, category.comp_id],
    transitivity _ ≫ c.ι.app (op (U.unop ⊓ h1.some)),
    work_on_goal 2
    { refine (terminal_is_terminal.if_neg _).from _,
      exact λ h, h1.some_spec h.2, },
    work_on_goal 2
    { have := c.ι.naturality ((hom_of_le inf_le_left).op : op U.unop ⟶ op (unop U ⊓ h1.some)),
      erw [category.comp_id] at this,
      erw ←this,
      congr,
      refine (terminal_is_terminal.if_neg _).hom_ext _ _,
      exact λ h, h1.some_spec h.2, },
    have := c.ι.naturality ((hom_of_le inf_le_right).op : op h1.some ⟶ op (unop U ⊓ h1.some)),
    erw [category.comp_id] at this,
    erw [←this, ←category.assoc],
    congr' 1,
    refine (terminal_is_terminal.if_neg _).hom_ext _ _,
    exact λ h, h1.some_spec h.2,
  end,
  uniq' := λ c f H,
  begin
    erw [colimit.ι_desc, ←H],
    simp only [skyscraper_presheaf_cocone_ι_app],
    dsimp,
    have : terminal.from
      (ite (p₀ ∈ (mem_nhds_of_not_specializes p₀ h).some.1) S (terminal C)) =
      eq_to_hom (if_neg (mem_nhds_of_not_specializes p₀ h).some_spec) :=
    terminal_is_terminal.hom_ext _ _,
    erw [this, ←category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.id_comp]
  end }

/--
If `y ∉ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ S` at `y` is `*`
-/
@[reducible]
noncomputable def skyscraper_presheaf_stalk_of_not_specializes [has_colimits C]
  {y : X} (h : ¬p₀ ⤳ y) : (skyscraper_presheaf p₀ S).stalk y ≅ terminal C :=
colimit.iso_colimit_cocone ⟨_, skyscraper_presheaf_cocone_is_colimit_of_not_specializes _ S h⟩

end
