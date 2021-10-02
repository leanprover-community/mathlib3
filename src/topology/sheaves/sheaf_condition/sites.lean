/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/

import category_theory.sites.sheaf
import category_theory.sites.spaces
import topology.sheaves.sheaf

/-!

# The sheaf condition in terms of sites.

The theory of sheaves on sites is developed independently from sheaves on spaces in
`category_theory/sites`. In this file, we connect the two: We show that for a topological space `X`,
a presheaf `F : (opens X)ᵒᵖ ⥤ C` is a sheaf on the site `opens X` if and only if it is a sheaf
on `X` in the usual sense.

-/

noncomputable theory

universes u v

namespace Top.presheaf

open category_theory topological_space Top category_theory.limits opposite
open Top.presheaf.sheaf_condition_equalizer_products

variables {C : Type u} [category.{v} C] [has_products C]
variables {X : Top.{v}} (F : presheaf C X)

/--
Given a presieve `R` on `U`, we obtain a covering family of open sets in `X`, by taking as index
type the type of dependent pairs `(V, f)`, where `f : V ⟶ U` is in `R`.
-/
def covering_of_presieve (U : opens X) (R : presieve U) :
  (Σ V, {f : V ⟶ U // R f}) → opens X := λ f, f.1

@[simp]
lemma covering_of_presieve_apply (U : opens X) (R : presieve U) (f : Σ V, {f : V ⟶ U // R f}) :
  covering_of_presieve U R f = f.1 := rfl

/--
If `R` is a presieve in the grothendieck topology on `opens X`, the covering family associated to
`R` really is _covering_, i.e. the union of all open sets equals `U`.
-/
lemma supr_covering_of_presieve_eq (U : opens X) (R : presieve U)
  (hR : sieve.generate R ∈ opens.grothendieck_topology X U) :
  supr (covering_of_presieve U R) = U :=
begin
  apply le_antisymm,
  { refine supr_le _,
    intro f,
    exact f.2.1.le, },
  intros x hxU,
  rw [subtype.val_eq_coe, opens.mem_coe, opens.mem_supr],
  obtain ⟨V, iVU, ⟨W, iVW, iWU, hiWU, -⟩, hxV⟩ := hR x hxU,
  exact ⟨⟨W, ⟨iWU, hiWU⟩⟩, iVW.le hxV⟩,
end

namespace covering_of_presieve

variables (U : opens X) (R : presieve U)

/-- The isomorphism between the first objects in the equalizer diagram. -/
def first_obj_iso_pi_opens : presheaf.first_obj R F ≅ pi_opens F (covering_of_presieve U R) :=
eq_to_iso rfl

/--
The isomorphism `first_obj_iso_pi_opens` is compatible with canonical projections out of the
product.
-/
lemma first_obj_iso_pi_opens_π (f : Σ V, {f : V ⟶ U // R f}) :
  (first_obj_iso_pi_opens F U R).hom ≫ limit.π _ f = limit.π _ f :=
begin dsimp [first_obj_iso_pi_opens], rw category.id_comp, end

/-- The isomorphism between the second objects in the equalizer diagram. -/
def second_obj_iso_pi_inters :
  presheaf.second_obj R F ≅ pi_inters F (covering_of_presieve U R) :=
has_limit.iso_of_nat_iso $ discrete.nat_iso $ λ i, eq_to_iso $
begin
  dsimp,
  rw complete_lattice.pullback_eq_inf,
end

/--
The isomorphism `second_obj_iso_pi_inters` is compatible with canonical projections out of the
product. Here, we have to insert an `eq_to_hom` arrow to pass from
`F.obj (op (pullback f.2.1 g.2.1))` to `F.obj (op (f.1 ⊓ g.1))`.
-/
lemma second_obj_iso_pi_inters_π (f g : Σ V, {f : V ⟶ U // R f}) :
  (second_obj_iso_pi_inters F U R).hom ≫ limit.π _ (f, g) =
  limit.π _ (f, g) ≫ F.map (eq_to_hom (complete_lattice.pullback_eq_inf f.2.1 g.2.1).symm).op :=
begin
  dsimp [second_obj_iso_pi_inters],
  rw [has_limit.iso_of_nat_iso_hom_π, eq_to_hom_op, eq_to_hom_map],
  refl,
end

/--
The fork maps of the equalizer diagram are compatible with the isomorphism between the
first objects.
-/
lemma fork_map_comp_first_obj_iso_pi_opens_eq
  (hR : sieve.generate R ∈ opens.grothendieck_topology X U) :
  presheaf.fork_map R F ≫ (first_obj_iso_pi_opens F U R).hom =
  F.map (eq_to_hom (supr_covering_of_presieve_eq U R hR)).op ≫ res F (covering_of_presieve U R) :=
begin
  ext f,
  rw [category.assoc, category.assoc],
  rw first_obj_iso_pi_opens_π,
  dsimp [presheaf.fork_map, res],
  rw [limit.lift_π, fan.mk_π_app, limit.lift_π, fan.mk_π_app, ← F.map_comp],
  congr,
end

/--
First naturality condition. Under the isomorphisms `first_obj_iso_pi_opens` and
`second_obj_iso_pi_inters`, the map `presheaf.first_map` corresponds to `left_res`.
-/
lemma first_obj_iso_comp_left_res_eq :
  presheaf.first_map R F ≫ (second_obj_iso_pi_inters F U R).hom =
  (first_obj_iso_pi_opens F U R).hom ≫ left_res F (covering_of_presieve U R) :=
begin
  ext ⟨f, g⟩,
  rw [category.assoc, category.assoc, second_obj_iso_pi_inters_π],
  dsimp [left_res, presheaf.first_map],
  rw [limit.lift_π, fan.mk_π_app, limit.lift_π_assoc, fan.mk_π_app, ← category.assoc],
  erw [first_obj_iso_pi_opens_π, category.assoc, ← F.map_comp],
  refl,
end

/--
Second naturality condition. Under the isomorphisms `first_obj_iso_pi_opens` and
`second_obj_iso_pi_inters`, the map `presheaf.second_map` corresponds to `right_res`.
-/
lemma first_obj_iso_comp_right_res_eq :
  presheaf.second_map R F ≫ (second_obj_iso_pi_inters F U R).hom =
  (first_obj_iso_pi_opens F U R).hom ≫ right_res F (covering_of_presieve U R) :=
begin
  ext ⟨f, g⟩,
  rw [category.assoc, category.assoc, second_obj_iso_pi_inters_π],
  dsimp [right_res, presheaf.second_map],
  rw [limit.lift_π, fan.mk_π_app, limit.lift_π_assoc, fan.mk_π_app, ← category.assoc],
  erw [first_obj_iso_pi_opens_π, category.assoc, ← F.map_comp],
  refl,
end

/-- The natural isomorphism between the two equalizer diagrams of the sheaf conditions. -/
@[simps]
def diagram_nat_iso : parallel_pair (presheaf.first_map R F) (presheaf.second_map R F) ≅
  diagram F (covering_of_presieve U R) :=
nat_iso.of_components
  (λ i, walking_parallel_pair.cases_on i (first_obj_iso_pi_opens F U R) (second_obj_iso_pi_inters F U R))
begin
  intros i j f,
  cases i,
  { cases j,
    { cases f, simp },
    { cases f,
      { exact first_obj_iso_comp_left_res_eq F U R, },
      { exact first_obj_iso_comp_right_res_eq F U R, } } },
  { cases j,
    { cases f, },
    { cases f, simp } },
end

/--
Postcomposing the given fork of the _sites_ diagram with the natural isomorphism between the
diagrams gives us a fork of the _spaces_ diagram. We construct a morphism from this fork to the
given fork of the _spaces_ diagram. This is shown to be an isomorphism below.
-/
@[simps]
def postcompose_diagram_fork_hom (hR : sieve.generate R ∈ opens.grothendieck_topology X U) :
  (cones.postcompose (diagram_nat_iso F U R).hom).obj (fork.of_ι _ (presheaf.w R F)) ⟶
  fork F (covering_of_presieve U R) :=
fork.mk_hom (F.map (eq_to_hom (supr_covering_of_presieve_eq U R hR)).op)
  (fork_map_comp_first_obj_iso_pi_opens_eq F U R hR).symm

instance is_iso_postcompose_diagram_fork_hom_hom
  (hR : sieve.generate R ∈ opens.grothendieck_topology X U) :
  is_iso (postcompose_diagram_fork_hom F U R hR).hom :=
begin rw postcompose_diagram_fork_hom_hom, apply eq_to_hom.is_iso, end

instance is_iso_postcompose_diagram_fork_hom
  (hR : sieve.generate R ∈ opens.grothendieck_topology X U) :
  is_iso (postcompose_diagram_fork_hom F U R hR) :=
cones.cone_iso_of_hom_iso _

/-- See `postcompose_diagram_fork_hom`. -/
def postcompose_diagram_fork_iso (hR : sieve.generate R ∈ opens.grothendieck_topology X U) :
  (cones.postcompose (diagram_nat_iso F U R).hom).obj (fork.of_ι _ (presheaf.w R F)) ≅
  fork F (covering_of_presieve U R) :=
as_iso (postcompose_diagram_fork_hom F U R hR)

end covering_of_presieve

open covering_of_presieve

lemma is_sheaf_sites_of_is_sheaf_spaces (Fsh : F.is_sheaf) :
  presheaf.is_sheaf (opens.grothendieck_topology X) F :=
begin
  rw presheaf.is_sheaf_iff_is_sheaf',
  intros U R hR,
  refine ⟨_⟩,
  apply (is_limit.of_cone_equiv (cones.postcompose_equivalence (diagram_nat_iso F U R))).to_fun,
  apply (is_limit.equiv_iso_limit (postcompose_diagram_fork_iso F U R hR)).inv_fun,
  exact (Fsh (covering_of_presieve U R)).some,
end

end Top.presheaf
