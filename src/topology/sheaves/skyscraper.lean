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

A skyscraper (pre)sheaf `𝓕 : (pre)sheaf C X` is a (pre)sheaf with value `A` at point `p₀` is
supported only at open sets contain `p₀`, i.e. `𝓕(U) = A` if `p₀ ∈ U` and `𝓕(U) = *` if `p₀ ∉ U`
where `*` is a terminal object of `C`. In terms of stalks, `𝓕` is supported at all specilizations
of `p₀`, i.e. if `x ⤳ p₀` then `𝓕ₓ ≅ A` and if `¬ x ⤳ p₀` then `𝓕ₓ ≅ *`.

## Main definitions

* `skyscraper_presheaf`: `skyscraper_presheaf p₀ A` is the skyscraper presheaf at point `p₀` with
  value `A`.
* `skyscraper_sheaf`: the skyscraper presheaf satisfies the sheaf condition.

## Main statements

* `skyscraper_presheaf_stalk_of_specializes`: if `y ∈ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ A` at `y` is `A`.
* `skyscraper_presheaf_stalk_of_not_specializes`: if `y ∉ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ A` at `y` is `*` the terminal object.

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
    else ((if_neg h).symm.rec terminal_is_terminal).from _,
  map_id' := λ U,
  begin
    split_ifs,
    { apply eq_to_hom_refl },
    { exact ((if_neg h).symm.rec terminal_is_terminal).hom_ext _ _ },
  end,
  map_comp' := λ U V W iVU iWV,
  begin
    by_cases hW : p₀ ∈ unop W,
    { have hV : p₀ ∈ unop V := le_of_hom iWV.unop hW,
      simp only [dif_pos hW, dif_pos hV, eq_to_hom_trans] },
    { rw [dif_neg hW], apply ((if_neg hW).symm.rec terminal_is_terminal).hom_ext }
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
    else ((if_neg h).symm.rec terminal_is_terminal).from _,
   fac' := λ c j,
   begin
    dsimp, split_ifs with h0, swap,
    { exact ((if_neg h0).symm.rec terminal_is_terminal).hom_ext _ _, },
    by_cases h1 : p₀ ∈ (presheaf.sheaf_condition.opens_le_cover_cocone U).X;
    split_ifs, swap,
    { rw [eq_comp_eq_to_hom], exact ((if_neg h1).symm.rec terminal_is_terminal).hom_ext _ _, },
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
    dsimp at *, split_ifs with h1, swap,
    { exact ((if_neg h1).symm.rec terminal_is_terminal).hom_ext _ _ },
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
by { contrapose! h, exact specializes_iff_forall_open.2 (λ s o h₁, h ⟨⟨s, o⟩, h₁⟩) }

variable [Π (U : opens X), decidable (p₀ ∈ U)]
/--
The cocone at `S` for the stalk functor of `skyscraper_presheaf p₀ S` when `y ∈ closure {p₀}`
-/
@[simps] def skyscraper_presheaf_cocone_of_specializes {y : X} (h : p₀ ⤳ y) :
  cocone ((open_nhds.inclusion y).op ⋙ skyscraper_presheaf p₀ S) :=
{ X := S,
  ι := { app := λ U, eq_to_hom $ if_pos $ h.mem_open U.unop.1.2 U.unop.2,
    naturality' := λ U V inc, begin
      change dite _ _ _ ≫ _ = _, rw dif_pos,
      { erw [category.comp_id, eq_to_hom_trans], refl },
      { exact h.mem_open V.unop.1.2 V.unop.2 },
    end } }

/--
The cocone at `S` for the stalk functor of `skyscraper_presheaf p₀ S` when `y ∈ closure {p₀}` is a
colimit
-/
noncomputable def skyscraper_presheaf_cocone_is_colimit_of_specializes [has_colimits C]
  {y : X} (h : p₀ ⤳ y) : is_colimit (skyscraper_presheaf_cocone_of_specializes p₀ S h) :=
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
If `y ∈ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ S` at `y` is `S`.
-/
@[reducible]
noncomputable def skyscraper_presheaf_stalk_of_specializes [has_colimits C]
  {y : X} (h : p₀ ⤳ y) : (skyscraper_presheaf p₀ S).stalk y ≅ S :=
colimit.iso_colimit_cocone ⟨_, skyscraper_presheaf_cocone_is_colimit_of_specializes p₀ S h⟩

/--
The cocone at `*` for the stalk functor of `skyscraper_presheaf p₀ S` when `y ∉ closure {p₀}`
-/
@[simps] def skyscraper_presheaf_cocone (y : X) :
  cocone ((open_nhds.inclusion y).op ⋙ skyscraper_presheaf p₀ S) :=
{ X := terminal C,
  ι :=
  { app := λ U, terminal.from _,
    naturality' := λ U V inc, terminal_is_terminal.hom_ext _ _ } }

/--
The cocone at `*` for the stalk functor of `skyscraper_presheaf p₀ S` when `y ∉ closure {p₀}` is a
colimit
-/
noncomputable def skyscraper_presheaf_cocone_is_colimit_of_not_specializes [has_colimits C]
  {y : X} (h : ¬p₀ ⤳ y) : is_colimit (skyscraper_presheaf_cocone p₀ S y) :=
let h1 := mem_nhds_of_not_specializes p₀ h in
{ desc := λ c, eq_to_hom (if_neg h1.some_spec).symm ≫ c.ι.app (op h1.some),
  fac' := λ c U, begin
    change _ = c.ι.app (op U.unop),
    simp only [← c.w (hom_of_le $ @inf_le_left _ _ h1.some U.unop).op,
      ← c.w (hom_of_le $ @inf_le_right _ _ h1.some U.unop).op, ← category.assoc],
    congr' 1, dsimp,
    refine ((if_neg _ : ite _ _ _ = terminal C).symm.rec_on
      (terminal_is_terminal : is_terminal (terminal C))).hom_ext _ _,
    exact λ h, h1.some_spec h.1,
  end,
  uniq' := λ c f H, begin
    rw [← category.id_comp f, ← H, ← category.assoc],
    congr' 1, apply terminal_is_terminal.hom_ext,
  end }

/--
If `y ∉ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ S` at `y` is `*`
-/
@[reducible]
noncomputable def skyscraper_presheaf_stalk_of_not_specializes [has_colimits C]
  {y : X} (h : ¬p₀ ⤳ y) : (skyscraper_presheaf p₀ S).stalk y ≅ terminal C :=
colimit.iso_colimit_cocone ⟨_, skyscraper_presheaf_cocone_is_colimit_of_not_specializes _ S h⟩

end
