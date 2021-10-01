/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import topology.sheaves.sheaf
import category_theory.sites.sheaf
import category_theory.limits.lattice

/-!
# Grothendieck topology on a topological space

Define the Grothendieck topology and the pretopology associated to a topological space, and show
that the pretopology induces the topology.

The covering (pre)sieves on `X` are those for which the union of domains contains `X`.

## Tags

site, Grothendieck topology, space

## References

* [https://ncatlab.org/nlab/show/Grothendieck+topology][nlab]
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We define the two separately, rather than defining the Grothendieck topology as that generated
by the pretopology for the purpose of having nice definitional properties for the sieves.
-/

universes u v

open category_theory topological_space Top Top.presheaf category_theory.limits

namespace opens

variables (T : Type u) [topological_space T]

/-- The Grothendieck topology associated to a topological space. -/
def grothendieck_topology : grothendieck_topology (opens T) :=
{ sieves := λ X S, ∀ x ∈ X, ∃ U (f : U ⟶ X), S f ∧ x ∈ U,
  top_mem' := λ X x hx, ⟨_, 𝟙 _, trivial, hx⟩,
  pullback_stable' := λ X Y S f hf y hy,
  begin
    rcases hf y (f.le hy) with ⟨U, g, hg, hU⟩,
    refine ⟨U ⊓ Y, hom_of_le inf_le_right, _, hU, hy⟩,
    apply S.downward_closed hg (hom_of_le inf_le_left),
  end,
  transitive' := λ X S hS R hR x hx,
  begin
    rcases hS x hx with ⟨U, f, hf, hU⟩,
    rcases hR hf _ hU with ⟨V, g, hg, hV⟩,
    exact ⟨_, g ≫ f, hg, hV⟩,
  end }

/-- The Grothendieck pretopology associated to a topological space. -/
def pretopology : pretopology (opens T) :=
{ coverings := λ X R, ∀ x ∈ X, ∃ U (f : U ⟶ X), R f ∧ x ∈ U,
  has_isos := λ X Y f i x hx,
        by exactI ⟨_, _, presieve.singleton_self _, (inv f).le hx⟩,
  pullbacks := λ X Y f S hS x hx,
  begin
    rcases hS _ (f.le hx) with ⟨U, g, hg, hU⟩,
    refine ⟨_, _, presieve.pullback_arrows.mk _ _ hg, _⟩,
    have : U ⊓ Y ≤ pullback g f,
      refine le_of_hom (pullback.lift (hom_of_le inf_le_left) (hom_of_le inf_le_right) rfl),
    apply this ⟨hU, hx⟩,
  end,
  transitive := λ X S Ti hS hTi x hx,
  begin
    rcases hS x hx with ⟨U, f, hf, hU⟩,
    rcases hTi f hf x hU with ⟨V, g, hg, hV⟩,
    exact ⟨_, _, ⟨_, g, f, hf, hg, rfl⟩, hV⟩,
  end }

/--
The pretopology associated to a space induces the Grothendieck topology associated to the space.
-/
@[simp]
lemma pretopology_to_grothendieck :
  pretopology.to_grothendieck _ (opens.pretopology T) = opens.grothendieck_topology T :=
begin
  apply le_antisymm,
  { rintro X S ⟨R, hR, RS⟩ x hx,
    rcases hR x hx with ⟨U, f, hf, hU⟩,
    exact ⟨_, f, RS _ hf, hU⟩ },
  { intros X S hS,
    exact ⟨S, hS, le_refl _⟩ }
end

end opens

noncomputable theory

variables {C : Type u} [category.{v} C] [has_products C]
variables {X : Top.{v}} (F : presheaf C X)

namespace is_sheaf_sites_of_is_sheaf_spaces

open Top.presheaf.sheaf_condition_equalizer_products
open opposite

variables (U : opens X) (R : presieve U)

def covering_of_presieve : (Σ V, {f : V ⟶ U // R f}) → opens X :=
λ f, f.1

@[simp]
lemma covering_of_presieve_apply (f : Σ V, {f : V ⟶ U // R f}) :
  covering_of_presieve U R f = f.1 := rfl

lemma supr_covering_of_presieve_eq (hR : sieve.generate R ∈ opens.grothendieck_topology X U) :
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

def first_obj_iso_pi_opens : presheaf.first_obj R F ≅ pi_opens F (covering_of_presieve U R) :=
eq_to_iso rfl

lemma first_obj_iso_pi_opens_π (f : Σ V, {f : V ⟶ U // R f}) :
  (first_obj_iso_pi_opens F U R).hom ≫ limit.π _ f = limit.π _ f :=
begin dsimp [first_obj_iso_pi_opens], rw category.id_comp, end

def second_obj_iso_pi_inters :
  presheaf.second_obj R F ≅ pi_inters F (covering_of_presieve U R) :=
has_limit.iso_of_nat_iso $ discrete.nat_iso $ λ i, eq_to_iso $
begin
  dsimp,
  rw complete_lattice.pullback_eq_inf,
end

lemma second_obj_iso_pi_inters_π (f g : Σ V, {f : V ⟶ U // R f}) :
  (second_obj_iso_pi_inters F U R).hom ≫ limit.π _ (f, g) =
  limit.π _ (f, g) ≫ F.map (eq_to_hom (complete_lattice.pullback_eq_inf f.2.1 g.2.1).symm).op :=
begin
  dsimp [second_obj_iso_pi_inters],
  rw [has_limit.iso_of_nat_iso_hom_π, eq_to_hom_op, eq_to_hom_map],
  refl,
end

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

def postcompose_diagram_fork_iso (hR : sieve.generate R ∈ opens.grothendieck_topology X U) :
  (cones.postcompose (diagram_nat_iso F U R).hom).obj (fork.of_ι _ (presheaf.w R F)) ≅
  fork F (covering_of_presieve U R) :=
as_iso (postcompose_diagram_fork_hom F U R hR)

end is_sheaf_sites_of_is_sheaf_spaces

open is_sheaf_sites_of_is_sheaf_spaces

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
