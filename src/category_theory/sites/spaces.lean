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

namespace is_sheaf_spaces_of_is_sheaf_sites

open Top.presheaf.sheaf_condition_equalizer_products
open opposite

variables {C : Type u} [category.{v} C] [has_products C]
variables {X : Top.{v}} (F : presheaf C X)
variables (U : opens X) (R : presieve U)

def covering_of_presieve : (Σ V, {f : V ⟶ U // R f}) ⟶ opens X :=
λ f, f.1

@[simp]
lemma covering_of_presieve_eq (f : Σ V, {f : V ⟶ U // R f}) : covering_of_presieve U R f = f.1 :=
rfl

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
  limit.π _ (f, g) ≫ eq_to_hom
    (begin congr, ext fg, rw complete_lattice.pullback_eq_inf, refl end) :=
begin
  dsimp [second_obj_iso_pi_inters],
  rw has_limit.iso_of_nat_iso_hom_π,
  refl,
end

lemma res_pullback_fst_comp_eq_to_hom_eq (f g : Σ V, {f : V ⟶ U // R f}) :
  F.map pullback.fst.op ≫ eq_to_hom (show F.obj (op (pullback f.2.1 g.2.1)) = _,
    by { congr, rw complete_lattice.pullback_eq_inf }) =
  F.map (opens.inf_le_left f.1 g.1).op :=
begin
  rw [← eq_to_hom_map F, ← eq_to_hom_op, ← F.map_comp], refl,
  rw complete_lattice.pullback_eq_inf,
end

lemma res_pullback_snd_comp_eq_to_hom_eq (f g : Σ V, {f : V ⟶ U // R f}) :
  F.map pullback.snd.op ≫ eq_to_hom (show F.obj (op (pullback f.2.1 g.2.1)) = _,
    by { congr, rw complete_lattice.pullback_eq_inf }) =
  F.map (opens.inf_le_right f.1 g.1).op :=
begin
  rw [← eq_to_hom_map F, ← eq_to_hom_op, ← F.map_comp], refl,
  rw complete_lattice.pullback_eq_inf,
end

lemma first_obj_iso_comp_left_res_eq :
  (first_obj_iso_pi_opens F U R).hom ≫ left_res F (covering_of_presieve U R) =
  presheaf.first_map R F ≫ (second_obj_iso_pi_inters F U R).hom :=
begin
  ext ⟨f, g⟩,
  rw [category.assoc, category.assoc, second_obj_iso_pi_inters_π],
  dsimp [left_res, presheaf.first_map],
  rw [limit.lift_π, fan.mk_π_app, limit.lift_π_assoc, fan.mk_π_app, ← category.assoc],
  erw [first_obj_iso_pi_opens_π, category.assoc, res_pullback_fst_comp_eq_to_hom_eq],
end

lemma first_obj_iso_comp_right_res_eq :
  (first_obj_iso_pi_opens F U R).hom ≫ right_res F (covering_of_presieve U R) =
  presheaf.second_map R F ≫ (second_obj_iso_pi_inters F U R).hom :=
begin
  ext ⟨f, g⟩,
  rw [category.assoc, category.assoc, second_obj_iso_pi_inters_π],
  dsimp [right_res, presheaf.second_map],
  rw [limit.lift_π, fan.mk_π_app, limit.lift_π_assoc, fan.mk_π_app, ← category.assoc],
  erw [first_obj_iso_pi_opens_π, category.assoc, res_pullback_snd_comp_eq_to_hom_eq],
end

end is_sheaf_spaces_of_is_sheaf_sites
