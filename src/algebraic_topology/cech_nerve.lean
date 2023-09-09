/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import algebraic_topology.simplicial_object
import category_theory.limits.shapes.wide_pullbacks
import category_theory.limits.shapes.finite_products
import category_theory.arrow

/-!

# The Čech Nerve

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides a definition of the Čech nerve associated to an arrow, provided
the base category has the correct wide pullbacks.

Several variants are provided, given `f : arrow C`:
1. `f.cech_nerve` is the Čech nerve, considered as a simplicial object in `C`.
2. `f.augmented_cech_nerve` is the augmented Čech nerve, considered as an
  augmented simplicial object in `C`.
3. `simplicial_object.cech_nerve` and `simplicial_object.augmented_cech_nerve` are
  functorial versions of 1 resp. 2.

We end the file with a description of the Čech nerve of an arrow `X ⟶ ⊤_ C` to a terminal
object, when `C` has finite products. We call this `cech_nerve_terminal_from`. When `C` is
`G`-Set this gives us `EG` (the universal cover of the classifying space of `G`) as a simplicial
`G`-set, which is useful for group cohomology.
-/

open category_theory
open category_theory.limits

noncomputable theory

universes v u w

variables {C : Type u} [category.{v} C]

namespace category_theory.arrow

variables (f : arrow C)
variables [∀ n : ℕ, has_wide_pullback.{0} f.right (λ i : fin (n+1), f.left) (λ i, f.hom)]

/-- The Čech nerve associated to an arrow. -/
@[simps]
def cech_nerve : simplicial_object C :=
{ obj := λ n, wide_pullback.{0} f.right
    (λ i : fin (n.unop.len + 1), f.left) (λ i, f.hom),
  map := λ m n g, wide_pullback.lift (wide_pullback.base _)
    (λ i, wide_pullback.π (λ i, f.hom) $ g.unop.to_order_hom i) $ λ j, by simp,
  map_id' := λ x, by { ext ⟨⟩, { simpa }, { simp } },
  map_comp' := λ x y z f g, by { ext ⟨⟩, { simpa }, { simp } } }

/-- The morphism between Čech nerves associated to a morphism of arrows. -/
@[simps]
def map_cech_nerve {f g : arrow C}
  [∀ n : ℕ, has_wide_pullback f.right (λ i : fin (n+1), f.left) (λ i, f.hom)]
  [∀ n : ℕ, has_wide_pullback g.right (λ i : fin (n+1), g.left) (λ i, g.hom)]
  (F : f ⟶ g) : f.cech_nerve ⟶ g.cech_nerve :=
{ app := λ n, wide_pullback.lift (wide_pullback.base _ ≫ F.right)
    (λ i, wide_pullback.π _ i ≫ F.left) $ λ j, by simp,
  naturality' := λ x y f, by { ext ⟨⟩, { simp }, { simp } } }

/-- The augmented Čech nerve associated to an arrow. -/
@[simps]
def augmented_cech_nerve : simplicial_object.augmented C :=
{ left := f.cech_nerve,
  right := f.right,
  hom :=
  { app := λ i, wide_pullback.base _,
    naturality' := λ x y f, by { dsimp, simp } } }

/-- The morphism between augmented Čech nerve associated to a morphism of arrows. -/
@[simps]
def map_augmented_cech_nerve {f g : arrow C}
  [∀ n : ℕ, has_wide_pullback f.right (λ i : fin (n+1), f.left) (λ i, f.hom)]
  [∀ n : ℕ, has_wide_pullback g.right (λ i : fin (n+1), g.left) (λ i, g.hom)]
  (F : f ⟶ g) : f.augmented_cech_nerve ⟶ g.augmented_cech_nerve :=
{ left := map_cech_nerve F,
  right := F.right,
  w' := by { ext, simp } }

end category_theory.arrow

namespace category_theory
namespace simplicial_object

variables [∀ (n : ℕ) (f : arrow C),
  has_wide_pullback f.right (λ i : fin (n+1), f.left) (λ i, f.hom)]

/-- The Čech nerve construction, as a functor from `arrow C`. -/
@[simps]
def cech_nerve : arrow C ⥤ simplicial_object C :=
{ obj := λ f, f.cech_nerve,
  map := λ f g F, arrow.map_cech_nerve F,
  map_id' := λ i, by { ext, { simp }, { simp } },
  map_comp' := λ x y z f g, by { ext, { simp }, { simp } } }

/-- The augmented Čech nerve construction, as a functor from `arrow C`. -/
@[simps]
def augmented_cech_nerve : arrow C ⥤ simplicial_object.augmented C :=
{ obj := λ f, f.augmented_cech_nerve,
  map := λ f g F, arrow.map_augmented_cech_nerve F,
  map_id' := λ x, by { ext, { simp }, { simp }, { refl } },
  map_comp' := λ x y z f g, by { ext, { simp }, { simp }, { refl } } }

/-- A helper function used in defining the Čech adjunction. -/
@[simps]
def equivalence_right_to_left (X : simplicial_object.augmented C) (F : arrow C)
  (G : X ⟶ F.augmented_cech_nerve) : augmented.to_arrow.obj X ⟶ F :=
{ left := G.left.app _ ≫ wide_pullback.π (λ i, F.hom) 0,
  right := G.right,
  w' := begin
    have := G.w,
    apply_fun (λ e, e.app (opposite.op $ simplex_category.mk 0)) at this,
    simpa using this,
  end }

/-- A helper function used in defining the Čech adjunction. -/
@[simps]
def equivalence_left_to_right (X : simplicial_object.augmented C) (F : arrow C)
  (G : augmented.to_arrow.obj X ⟶ F) : X ⟶ F.augmented_cech_nerve :=
{ left :=
  { app := λ x, limits.wide_pullback.lift (X.hom.app _ ≫ G.right)
      (λ i, X.left.map (simplex_category.const x.unop i).op ≫ G.left)
      (λ i, by { dsimp, erw [category.assoc, arrow.w,
        augmented.to_arrow_obj_hom, nat_trans.naturality_assoc,
        functor.const_obj_map, category.id_comp] } ),
    naturality' := begin
      intros x y f,
      ext,
      { dsimp,
        simp only [wide_pullback.lift_π, category.assoc],
        rw [← category.assoc, ← X.left.map_comp],
        refl },
      { dsimp,
        simp only [functor.const_obj_map, nat_trans.naturality_assoc,
          wide_pullback.lift_base, category.assoc],
        erw category.id_comp }
    end },
  right := G.right,
  w' := by { ext, dsimp, simp } }

/-- A helper function used in defining the Čech adjunction. -/
@[simps]
def cech_nerve_equiv (X : simplicial_object.augmented C) (F : arrow C) :
  (augmented.to_arrow.obj X ⟶ F) ≃ (X ⟶ F.augmented_cech_nerve) :=
{ to_fun := equivalence_left_to_right _ _,
  inv_fun := equivalence_right_to_left _ _,
  left_inv := begin
    intro A,
    dsimp,
    ext,
    { dsimp,
      erw wide_pullback.lift_π,
      nth_rewrite 1 ← category.id_comp A.left,
      congr' 1,
      convert X.left.map_id _,
      rw ← op_id,
      congr' 1,
      ext ⟨a,ha⟩,
      change a < 1 at ha,
      change 0 = a,
      linarith },
    { refl, }
  end,
  right_inv := begin
    intro A,
    ext _ ⟨j⟩,
    { dsimp,
      simp only [arrow.cech_nerve_map, wide_pullback.lift_π, nat_trans.naturality_assoc],
      erw wide_pullback.lift_π,
      refl },
    { erw wide_pullback.lift_base,
      have := A.w,
      apply_fun (λ e, e.app x) at this,
      rw nat_trans.comp_app at this,
      erw this,
      refl },
    { refl }
  end }

/-- The augmented Čech nerve construction is right adjoint to the `to_arrow` functor. -/
abbreviation cech_nerve_adjunction :
  (augmented.to_arrow : _ ⥤ arrow C) ⊣ augmented_cech_nerve :=
adjunction.mk_of_hom_equiv
{ hom_equiv := cech_nerve_equiv,
  hom_equiv_naturality_left_symm' := λ x y f g h, by { ext, { simp }, { simp } },
  hom_equiv_naturality_right' := λ x y f g h, by { ext, { simp }, { simp }, { refl } } }

end simplicial_object

end category_theory

namespace category_theory.arrow

variables (f : arrow C)
variables [∀ n : ℕ, has_wide_pushout f.left (λ i : fin (n+1), f.right) (λ i, f.hom)]

/-- The Čech conerve associated to an arrow. -/
@[simps]
def cech_conerve : cosimplicial_object C :=
{ obj := λ n, wide_pushout f.left
    (λ i : fin (n.len + 1), f.right) (λ i, f.hom),
  map := λ m n g, wide_pushout.desc (wide_pushout.head _)
    (λ i, wide_pushout.ι (λ i, f.hom) $ g.to_order_hom i) $
    λ i, by { rw [wide_pushout.arrow_ι (λ i, f.hom)] },
  map_id' := λ x, by { ext ⟨⟩, { simpa }, { simp } },
  map_comp' := λ x y z f g, by { ext ⟨⟩, { simpa }, { simp } } }

/-- The morphism between Čech conerves associated to a morphism of arrows. -/
@[simps]
def map_cech_conerve {f g : arrow C}
  [∀ n : ℕ, has_wide_pushout f.left (λ i : fin (n+1), f.right) (λ i, f.hom)]
  [∀ n : ℕ, has_wide_pushout g.left (λ i : fin (n+1), g.right) (λ i, g.hom)]
  (F : f ⟶ g) : f.cech_conerve ⟶ g.cech_conerve :=
{ app := λ n, wide_pushout.desc (F.left ≫ wide_pushout.head _)
      (λ i, F.right ≫ wide_pushout.ι _ i) $
      λ i, by { rw [← arrow.w_assoc F, wide_pushout.arrow_ι (λ i, g.hom)] },
  naturality' := λ x y f, by { ext, { simp }, { simp } } }

/-- The augmented Čech conerve associated to an arrow. -/
@[simps]
def augmented_cech_conerve : cosimplicial_object.augmented C :=
{ left := f.left,
  right := f.cech_conerve,
  hom :=
  { app := λ i, wide_pushout.head _,
    naturality' := λ x y f, by { dsimp, simp } } }

/-- The morphism between augmented Čech conerves associated to a morphism of arrows. -/
@[simps]
def map_augmented_cech_conerve {f g : arrow C}
  [∀ n : ℕ, has_wide_pushout f.left (λ i : fin (n+1), f.right) (λ i, f.hom)]
  [∀ n : ℕ, has_wide_pushout g.left (λ i : fin (n+1), g.right) (λ i, g.hom)]
  (F : f ⟶ g) : f.augmented_cech_conerve ⟶ g.augmented_cech_conerve :=
{ left := F.left,
  right := map_cech_conerve F,
  w' := by { ext, simp } }

end category_theory.arrow

namespace category_theory
namespace cosimplicial_object

variables [∀ (n : ℕ) (f : arrow C),
  has_wide_pushout f.left (λ i : fin (n+1), f.right) (λ i, f.hom)]

/-- The Čech conerve construction, as a functor from `arrow C`. -/
@[simps]
def cech_conerve : arrow C ⥤ cosimplicial_object C :=
{ obj := λ f, f.cech_conerve,
  map := λ f g F, arrow.map_cech_conerve F,
  map_id' := λ i, by { ext, { dsimp, simp }, { dsimp, simp } },
  map_comp' := λ f g h F G, by { ext, { simp }, { simp } } }

/-- The augmented Čech conerve construction, as a functor from `arrow C`. -/
@[simps]
def augmented_cech_conerve : arrow C ⥤ cosimplicial_object.augmented C :=
{ obj := λ f, f.augmented_cech_conerve,
  map := λ f g F, arrow.map_augmented_cech_conerve F,
  map_id' := λ f, by { ext, { refl }, { dsimp, simp }, { dsimp, simp } },
  map_comp' := λ f g h F G, by { ext, { refl }, { simp }, { simp } } }

/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps]
def equivalence_left_to_right (F : arrow C) (X : cosimplicial_object.augmented C)
  (G : F.augmented_cech_conerve ⟶ X) : F ⟶ augmented.to_arrow.obj X :=
{ left := G.left,
  right :=
    (wide_pushout.ι (λ i, F.hom) 0 ≫ G.right.app (simplex_category.mk 0) : _),
  w' := begin
    have := G.w,
    apply_fun (λ e, e.app (simplex_category.mk 0)) at this,
    simpa only [category_theory.functor.id_map, augmented.to_arrow_obj_hom,
      wide_pushout.arrow_ι_assoc (λ i, F.hom)],
  end }

/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps]
def equivalence_right_to_left (F : arrow C) (X : cosimplicial_object.augmented C)
  (G : F ⟶ augmented.to_arrow.obj X) : F.augmented_cech_conerve ⟶ X :=
{ left := G.left,
  right := { app := λ x, limits.wide_pushout.desc (G.left ≫ X.hom.app _)
      (λ i, G.right ≫ X.right.map (simplex_category.const x i))
      begin
        rintros j,
        rw ← arrow.w_assoc G,
        have t := X.hom.naturality (x.const j),
        dsimp at t ⊢,
        simp only [category.id_comp] at t,
        rw ← t,
      end,
    naturality' := begin
      intros x y f,
      ext,
      { dsimp,
        simp only [wide_pushout.ι_desc_assoc, wide_pushout.ι_desc],
        rw [category.assoc, ←X.right.map_comp],
        refl },
      { dsimp,
        simp only [functor.const_obj_map, ←nat_trans.naturality,
          wide_pushout.head_desc_assoc, wide_pushout.head_desc, category.assoc],
        erw category.id_comp }
    end },
  w' := by { ext, simp } }

/-- A helper function used in defining the Čech conerve adjunction. -/
@[simps]
def cech_conerve_equiv (F : arrow C) (X : cosimplicial_object.augmented C) :
  (F.augmented_cech_conerve ⟶ X) ≃ (F ⟶ augmented.to_arrow.obj X) :=
{ to_fun := equivalence_left_to_right _ _,
  inv_fun := equivalence_right_to_left _ _,
  left_inv := begin
    intro A,
    dsimp,
    ext _, { refl }, ext _ ⟨⟩,  -- A bug in the `ext` tactic?
    { dsimp,
      simp only [arrow.cech_conerve_map, wide_pushout.ι_desc, category.assoc,
        ← nat_trans.naturality, wide_pushout.ι_desc_assoc],
      refl },
    { erw wide_pushout.head_desc,
      have := A.w,
      apply_fun (λ e, e.app x) at this,
      rw nat_trans.comp_app at this,
      erw this,
      refl },
  end,
  right_inv := begin
    intro A,
    ext,
    { refl, },
    { dsimp,
      erw wide_pushout.ι_desc,
      nth_rewrite 1 ← category.comp_id A.right,
      congr' 1,
      convert X.right.map_id _,
      ext ⟨a,ha⟩,
      change a < 1 at ha,
      change 0 = a,
      linarith },
  end }

/-- The augmented Čech conerve construction is left adjoint to the `to_arrow` functor. -/
abbreviation cech_conerve_adjunction :
  augmented_cech_conerve ⊣ (augmented.to_arrow : _ ⥤ arrow C) :=
adjunction.mk_of_hom_equiv
{ hom_equiv := cech_conerve_equiv,
  hom_equiv_naturality_left_symm' := λ x y f g h, by { ext, { refl }, { simp }, { simp } },
  hom_equiv_naturality_right' := λ x y f g h, by { ext, { simp }, { simp } } }

end cosimplicial_object

/-- Given an object `X : C`, the natural simplicial object sending `[n]` to `Xⁿ⁺¹`. -/
def cech_nerve_terminal_from {C : Type u} [category.{v} C] [has_finite_products C] (X : C) :
  simplicial_object C :=
{ obj := λ n, ∏ (λ i : fin (n.unop.len + 1), X),
  map := λ m n f, limits.pi.lift (λ i, limits.pi.π _ (f.unop.to_order_hom i)),
  map_id' := λ f, limit.hom_ext $ λ j, by discrete_cases;
    simpa only [limit.lift_π, category.id_comp],
  map_comp' := λ m n o f g, limit.hom_ext $ λ j, by discrete_cases;
    simpa only [category.assoc, limit.lift_π, fan.mk_π_app] }

namespace cech_nerve_terminal_from

variables [has_terminal C] (ι : Type w)

/-- The diagram `option ι ⥤ C` sending `none` to the terminal object and `some j` to `X`. -/
def wide_cospan (X : C) : wide_pullback_shape ι ⥤ C :=
wide_pullback_shape.wide_cospan (terminal C) (λ i : ι, X) (λ i, terminal.from X)

instance unique_to_wide_cospan_none (X Y : C) : unique (Y ⟶ (wide_cospan ι X).obj none) :=
by unfold wide_cospan; dsimp; apply_instance

variables [has_finite_products C]

/-- The product `Xᶥ` is the vertex of a limit cone on `wide_cospan ι X`. -/
def wide_cospan.limit_cone [fintype ι] (X : C) : limit_cone (wide_cospan ι X) :=
{ cone :=
  { X := ∏ (λ i : ι, X),
    π :=
    { app := λ X, option.cases_on X (terminal.from _) (λ i, limit.π _ ⟨i⟩),
      naturality' := λ i j f,
      begin
      cases f,
      { cases i,
        all_goals { dsimp, simp }},
      { dsimp,
        simp only [terminal.comp_from],
        exact subsingleton.elim _ _ }
      end } },
  is_limit :=
  { lift := λ s, limits.pi.lift (λ j, s.π.app (some j)),
    fac' := λ s j, option.cases_on j (subsingleton.elim _ _) (λ j, limit.lift_π _ _),
    uniq' := λ s f h,
    begin
      ext j,
      dunfold limits.pi.lift,
      rw limit.lift_π,
      dsimp,
      rw ←h (some j.as),
      congr,
      ext,
      refl,
    end } }

instance has_wide_pullback [finite ι] (X : C) :
  has_wide_pullback (arrow.mk (terminal.from X)).right
  (λ i : ι, (arrow.mk (terminal.from X)).left) (λ i, (arrow.mk (terminal.from X)).hom) :=
begin
  casesI nonempty_fintype ι,
  exact ⟨⟨wide_cospan.limit_cone ι X⟩⟩,
end

/-- Given an object `X : C`, the Čech nerve of the hom to the terminal object `X ⟶ ⊤_ C` is
naturally isomorphic to a simplicial object sending `[n]` to `Xⁿ⁺¹` (when `C` is `G-Set`, this is
`EG`, the universal cover of the classifying space of `G`. -/
def iso (X : C) :
  (arrow.mk (terminal.from X)).cech_nerve ≅ cech_nerve_terminal_from X :=
iso.symm (nat_iso.of_components (λ m, ((limit.is_limit _).cone_point_unique_up_to_iso
  (wide_cospan.limit_cone (fin (m.unop.len + 1)) X).2).symm) $ λ m n f, wide_pullback.hom_ext _ _ _
(begin
  intro j,
  simp only [category.assoc],
  dunfold cech_nerve_terminal_from wide_pullback.π pi.lift,
  erw [wide_pullback.lift_π, limit.cone_point_unique_up_to_iso_inv_comp
    (wide_cospan.limit_cone _ _).2, (limit.is_limit _).cone_point_unique_up_to_iso_inv_comp
    (wide_cospan.limit_cone _ _).2, limit.lift_π],
  refl,
end)
(@subsingleton.elim _ (@unique.subsingleton _ (limits.unique_to_terminal _)) _ _))

end cech_nerve_terminal_from
end category_theory
