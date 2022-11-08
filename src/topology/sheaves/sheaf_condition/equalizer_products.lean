/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.full_subcategory
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.products
import topology.sheaves.presheaf

/-!
# The sheaf condition in terms of an equalizer of products

Here we set up the machinery for the "usual" definition of the sheaf condition,
e.g. as in https://stacks.math.columbia.edu/tag/0072
in terms of an equalizer diagram where the two objects are
`∏ F.obj (U i)` and `∏ F.obj (U i) ⊓ (U j)`.

-/

universes v' v u

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C] [has_products.{v} C]
variables {X : Top.{v'}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace presheaf

namespace sheaf_condition_equalizer_products

/-- The product of the sections of a presheaf over a family of open sets. -/
def pi_opens : C := ∏ (λ i : ι, F.obj (op (U i)))
/--
The product of the sections of a presheaf over the pairwise intersections of
a family of open sets.
-/
def pi_inters : C := ∏ (λ p : ι × ι, F.obj (op (U p.1 ⊓ U p.2)))

/--
The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U i` to `U i ⊓ U j`.
-/
def left_res : pi_opens F U ⟶ pi_inters F U :=
pi.lift (λ p : ι × ι, pi.π _ p.1 ≫ F.map (inf_le_left (U p.1) (U p.2)).op)

/--
The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def right_res : pi_opens F U ⟶ pi_inters F U :=
pi.lift (λ p : ι × ι, pi.π _ p.2 ≫ F.map (inf_le_right (U p.1) (U p.2)).op)

/--
The morphism `F.obj U ⟶ Π F.obj (U i)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def res : F.obj (op (supr U)) ⟶ pi_opens F U :=
pi.lift (λ i : ι, F.map (topological_space.opens.le_supr U i).op)

@[simp, elementwise]
lemma res_π (i : ι) : res F U ≫ limit.π _ ⟨i⟩ = F.map (opens.le_supr U i).op :=
by rw [res, limit.lift_π, fan.mk_π_app]

@[elementwise]
lemma w : res F U ≫ left_res F U = res F U ≫ right_res F U :=
begin
  dsimp [res, left_res, right_res],
  ext,
  simp only [limit.lift_π, limit.lift_π_assoc, fan.mk_π_app, category.assoc],
  rw [←F.map_comp],
  rw [←F.map_comp],
  congr,
end

/--
The equalizer diagram for the sheaf condition.
-/
@[reducible]
def diagram : walking_parallel_pair ⥤ C :=
parallel_pair (left_res F U) (right_res F U)

/--
The restriction map `F.obj U ⟶ Π F.obj (U i)` gives a cone over the equalizer diagram
for the sheaf condition. The sheaf condition asserts this cone is a limit cone.
-/
def fork : fork.{v} (left_res F U) (right_res F U) := fork.of_ι _ (w F U)

@[simp]
lemma fork_X : (fork F U).X = F.obj (op (supr U)) := rfl

@[simp]
lemma fork_ι : (fork F U).ι = res F U := rfl
@[simp]
lemma fork_π_app_walking_parallel_pair_zero :
  (fork F U).π.app walking_parallel_pair.zero = res F U := rfl
@[simp]
lemma fork_π_app_walking_parallel_pair_one :
  (fork F U).π.app walking_parallel_pair.one = res F U ≫ left_res F U := rfl

variables {F} {G : presheaf C X}

/-- Isomorphic presheaves have isomorphic `pi_opens` for any cover `U`. -/
@[simp]
def pi_opens.iso_of_iso (α : F ≅ G) : pi_opens F U ≅ pi_opens G U :=
pi.map_iso (λ X, α.app _)

/-- Isomorphic presheaves have isomorphic `pi_inters` for any cover `U`. -/
@[simp]
def pi_inters.iso_of_iso (α : F ≅ G) : pi_inters F U ≅ pi_inters G U :=
pi.map_iso (λ X, α.app _)

/-- Isomorphic presheaves have isomorphic sheaf condition diagrams. -/
def diagram.iso_of_iso (α : F ≅ G) : diagram F U ≅ diagram G U :=
nat_iso.of_components
  begin rintro ⟨⟩, exact pi_opens.iso_of_iso U α, exact pi_inters.iso_of_iso U α end
  begin
    rintro ⟨⟩ ⟨⟩ ⟨⟩,
    { simp, },
    { ext, simp [left_res], },
    { ext, simp [right_res], },
    { simp, },
  end.

/--
If `F G : presheaf C X` are isomorphic presheaves,
then the `fork F U`, the canonical cone of the sheaf condition diagram for `F`,
is isomorphic to `fork F G` postcomposed with the corresponding isomorphism between
sheaf condition diagrams.
-/
def fork.iso_of_iso (α : F ≅ G) :
  fork F U ≅ (cones.postcompose (diagram.iso_of_iso U α).inv).obj (fork G U) :=
begin
  fapply fork.ext,
  { apply α.app, },
  { ext,
    dunfold fork.ι, -- Ugh, `simp` can't unfold abbreviations.
    simp [res, diagram.iso_of_iso], }
end

end sheaf_condition_equalizer_products

/--
The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
-/
def is_sheaf_equalizer_products (F : presheaf.{v' v u} C X) : Prop :=
∀ ⦃ι : Type v⦄ (U : ι → opens X), nonempty (is_limit (sheaf_condition_equalizer_products.fork F U))

end presheaf

end Top
