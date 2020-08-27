-- Copyright (c) 2019 Reid Barton. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Reid Barton

import category_theory.category
import tactic.slice

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

variables (C : Type u) [category.{v} C]

class is_filtered_or_empty : Prop :=
(cocone_objs : ∀ (X Y : C), ∃ Z (f : X ⟶ Z) (g : Y ⟶ Z), true)
(cocone_maps : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), ∃ Z (h : Y ⟶ Z), f ≫ h = g ≫ h)

class is_filtered extends is_filtered_or_empty C : Prop :=
(nonempty : nonempty C)

namespace is_filtered

variables {C} [is_filtered C]

noncomputable def sup (j j' : C) : C :=
(is_filtered_or_empty.cocone_objs j j').some

noncomputable def left_to_sup (j j' : C) : j ⟶ is_filtered.sup j j' :=
(is_filtered_or_empty.cocone_objs j j').some_spec.some

noncomputable def right_to_sup (j j' : C) : j' ⟶ is_filtered.sup j j' :=
(is_filtered_or_empty.cocone_objs j j').some_spec.some_spec.some

noncomputable def coeq {j j' : C} (f f' : j ⟶ j') : C :=
(is_filtered_or_empty.cocone_maps f f').some

noncomputable def coeq_hom {j j' : C} (f f' : j ⟶ j') : j' ⟶ coeq f f' :=
(is_filtered_or_empty.cocone_maps f f').some_spec.some

lemma coeq_condition {j j' : C} (f f' : j ⟶ j') : f ≫ coeq_hom f f' = f' ≫ coeq_hom f f' :=
(is_filtered_or_empty.cocone_maps f f').some_spec.some_spec

/--
Given a "bowtie" of morphisms
```
jx -> j₁
  \  ^
   \/
   /\
  /  v
jy -> j₂
```
in a filtered category, construct a morphism `j` sitting to the right of `j₁` and `j₂`,
making both of the resulting squares commute.
-/
noncomputable lemma bowtie {jx jy j₁ j₂ : C}
  (ix₁ : jx ⟶ j₁) (ix₂ : jx ⟶ j₂) (iy₁ : jy ⟶ j₁) (iy₂ : jy ⟶ j₂) :
  Σ' (j : C) (i₁ : j₁ ⟶ j) (i₂ : j₂ ⟶ j), ix₁ ≫ i₁ = ix₂ ≫ i₂ ∧ iy₁ ≫ i₁ = iy₂ ≫ i₂ :=
begin
  let ja := sup j₁ j₂,
  let jb := coeq (ix₁ ≫ left_to_sup _ _) (ix₂ ≫ right_to_sup _ _),
  let jc := coeq (iy₁ ≫ left_to_sup _ _) (iy₂ ≫ right_to_sup _ _),
  let jd := sup jb jc,
  let j := coeq ((coeq_hom _ _ : ja ⟶ jb) ≫ left_to_sup _ _) ((coeq_hom _ _ : ja ⟶ jc) ≫ right_to_sup _ _),
  use j,
  fsplit,
  exact left_to_sup j₁ j₂ ≫ coeq_hom _ _ ≫ left_to_sup jb jc ≫ coeq_hom _ _,
  fsplit,
  exact right_to_sup j₁ j₂ ≫ coeq_hom _ _ ≫ right_to_sup jb jc ≫ coeq_hom _ _,
  fsplit,
  { slice_lhs 1 3 { rw [←category.assoc, coeq_condition], },
    slice_lhs 3 5 { rw [←category.assoc, coeq_condition], },
    simp only [category.assoc], },
  { slice_lhs 3 5 { rw [←category.assoc, coeq_condition], },
    slice_lhs 1 3 { rw [←category.assoc, coeq_condition], },
    simp only [category.assoc], }
end

end is_filtered

end category_theory
