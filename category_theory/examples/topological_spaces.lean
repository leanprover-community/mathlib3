-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Patrick Massot, Scott Morrison, Mario Carneiro

import category_theory.full_subcategory
import category_theory.functor_category
import category_theory.natural_isomorphism
import analysis.topology.topological_space
import analysis.topology.continuity
import order.galois_connection

open category_theory
open category_theory.nat_iso

universe u

namespace category_theory.examples

/-- The category of topological spaces and continuous maps. -/
@[reducible] def Top : Type (u+1) := bundled topological_space

instance (x : Top) : topological_space x := x.str

namespace Top
instance : concrete_category @continuous := ⟨@continuous_id, @continuous.comp⟩

-- local attribute [class] continuous
-- instance {R S : Top} (f : R ⟶ S) : continuous (f : R → S) := f.2
end Top

structure open_set (X : Top.{u}) : Type u :=
(s : set X.α)
(is_open : topological_space.is_open X.str s)

variables {X : Top.{u}}

namespace open_set
open topological_space lattice
instance : has_coe (open_set X) (set X.α) := { coe := λ U, U.s }

instance : has_subset (open_set X) :=
{ subset := λ U V, U.s ⊆ V.s }

instance : has_mem X.α (open_set X) :=
{ mem := λ a V, a ∈ V.s }

@[extensionality] lemma ext {U V : open_set X} (h : U.s = V.s) : U = V :=
by cases U; cases V; congr; exact h

instance : partial_order (open_set X) := by refine { le := (⊆), .. } ; tidy

instance open_sets : small_category (open_set X) := by apply_instance

def interior (s : set X) : open_set X :=
{ s := interior s,
  is_open := is_open_interior }

def gc : galois_connection (@s X) interior :=
λ U s, ⟨λ h, interior_maximal h U.is_open, λ h, le_trans h interior_subset⟩

def gi : @galois_insertion (order_dual (set X)) (order_dual (open_set X)) _ _ interior (@s X) :=
{ choice := λ s hs, { s := s, is_open := interior_eq_iff_open.mp $ le_antisymm interior_subset hs },
  gc := gc.dual,
  le_l_u := λ _, interior_subset,
  choice_eq := λ s hs, le_antisymm interior_subset hs }

instance : complete_lattice (open_set X) :=
@order_dual.lattice.complete_lattice _
  (@galois_insertion.lift_complete_lattice
    (order_dual (set X)) (order_dual (open_set X)) _ interior (@s X) _ gi)

@[simp] lemma Sup_s {Us : set (open_set X)} : (Sup Us).s = ⋃₀ (open_set.s '' Us) :=
by rw [@galois_connection.l_Sup _ _ _ _ (@open_set.s X) interior (gc) Us, set.sUnion_image]

def nbhd (x : X.α) := { U : open_set X // x ∈ U }
def nbhds (x : X.α) : small_category (nbhd x) := begin unfold nbhd, apply_instance end

/-- `open_set.map f` gives the functor from open sets in Y to open set in X,
    given by taking preimages under f. -/
def map
  {X Y : Top.{u}} (f : X ⟶ Y) : open_set Y ⥤ open_set X :=
{ obj := λ U, ⟨ f.val ⁻¹' U.s, f.property _ U.is_open ⟩,
  map' := λ U V i, ⟨ ⟨ λ a b, i.down.down b ⟩ ⟩ }.

@[simp] lemma map_id_obj (X : Top.{u}) (U : open_set X) : map (𝟙 X) U = U :=
begin
  cases U, tidy
end

@[simp] def map_id (X : Top.{u}) : map (𝟙 X) ≅ functor.id (open_set X) :=
{ hom := { app := λ U, 𝟙 U },
  inv := { app := λ U, 𝟙 U } }

-- We could make f g implicit here, but it's nice to be able to see when they are the identity (often!)
def map_iso {X Y : Top.{u}} (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
nat_iso.of_components (λ U, eq_to_iso (congr_fun (congr_arg _ (congr_arg _ h)) _) ) (by obviously)

@[simp] def map_iso_id {X : Top.{u}} (h) : map_iso (𝟙 X) (𝟙 X) h = iso.refl (map _) := rfl

def is_basis (B : set (open_set X)) : Prop := is_topological_basis (open_set.s '' B)

lemma is_basis_iff_nbhd {B : set (open_set X)} :
is_basis B ↔ ∀ {U : open_set X} {x : X}, x ∈ U → ∃ U' ∈ B, x ∈ U' ∧ U' ⊆ U :=
begin
split; intro h,
{ rintros ⟨sU, hU⟩ x hx,
  rcases (mem_nhds_of_is_topological_basis h).mp (mem_nhds_sets hU hx) with ⟨sV,⟨⟨V,H₁,H₂⟩,hsV⟩⟩,
  refine ⟨V,H₁,_⟩,
  cases V, dsimp at H₂, subst H₂, exact hsV },
{ refine is_topological_basis_of_open_of_nhds _ _,
  { rintros sU ⟨U,⟨H₁,H₂⟩⟩, subst H₂, exact U.is_open },
  { intros x sU hx hsU,
    rcases @h (⟨sU,hsU⟩ : open_set X) x hx with ⟨V,hV,H⟩,
    refine ⟨V, ⟨V,hV,rfl⟩, H⟩ } }
end

lemma is_basis_iff_cover {B : set (open_set X)} :
is_basis B ↔ ∀ U : open_set X, ∃ Us ⊆ B, U = Sup Us :=
begin
  split,
  { intros hB U,
    rcases sUnion_basis_of_is_open hB U.is_open with ⟨sUs, H, hU⟩,
    existsi {U : open_set X | U ∈ B ∧ U.s ∈ sUs},
    split,
    { intros U hU, exact hU.left },
    { apply ext, rw [Sup_s, hU], congr,
      ext s; split; intro hs,
      { rcases H hs with ⟨V,hV⟩,
        rw ← hV.right at hs,
        refine ⟨V,⟨⟨hV.left,hs⟩,hV.right⟩⟩ },
      { rcases hs with ⟨V,⟨⟨H₁,H₂⟩,H₃⟩⟩,
        subst H₃, exact H₂ } } },
  { intro h,
    rw is_basis_iff_nbhd,
    intros U x hx,
    rcases h U with ⟨Us, hUs, H⟩,
    replace H := congr_arg open_set.s H,
    rw Sup_s at H,
    change x ∈ U.s at hx,
    rw H at hx,
    rcases set.mem_sUnion.mp hx with ⟨sV, ⟨⟨V,H₁,H₂⟩,hsV⟩⟩,
    refine ⟨V,hUs H₁,_⟩,
    cases V, dsimp at H₂, subst H₂,
    refine ⟨hsV,_⟩,
    change V_s ⊆ U.s, rw H,
    exact set.subset_sUnion_of_mem ⟨⟨V_s,V_is_open⟩,⟨H₁,rfl⟩⟩ }
end

end open_set

end category_theory.examples
