/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Calle Sönne
-/

import topology.category.CompHaus
import topology.connected
import topology.subset_properties
import category_theory.adjunction.reflective
import category_theory.Fintype


/-!
# The category of Profinite Types

We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `Top`. The fully faithful functor
is called `Profinite_to_Top`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

## TODO

0. Link to category of projective limits of finite discrete sets.
1. existence of products, limits(?), finite coproducts
2. `Profinite_to_Top` creates limits?
3. Clausen/Scholze topology on the category `Profinite`.

## Tags

profinite

-/

open category_theory

/-- The type of profinite topological spaces. -/
structure Profinite :=
(to_Top : Top)
[is_compact : compact_space to_Top]
[is_t2 : t2_space to_Top]
[is_totally_disconnected : totally_disconnected_space to_Top]

namespace Profinite

instance : inhabited Profinite := ⟨{to_Top := { α := pempty }}⟩

instance : has_coe_to_sort Profinite := ⟨Type*, λ X, X.to_Top⟩
instance {X : Profinite} : compact_space X := X.is_compact
instance {X : Profinite} : t2_space X := X.is_t2
instance {X : Profinite} : totally_disconnected_space X := X.is_totally_disconnected

instance category : category Profinite := induced_category.category to_Top

@[simp]
lemma coe_to_Top {X : Profinite} : (X.to_Top : Type*) = X :=
rfl

end Profinite

/-- The fully faithful embedding of `Profinite` in `Top`. -/
@[simps, derive [full, faithful]]
def Profinite_to_Top : Profinite ⥤ Top := induced_functor _

/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
@[simps] def Profinite.to_CompHaus : Profinite ⥤ CompHaus :=
{ obj := λ X, { to_Top := X.to_Top },
  map := λ _ _ f, f }

instance : full Profinite.to_CompHaus := { preimage := λ _ _ f, f }
instance : faithful Profinite.to_CompHaus := {}

@[simp] lemma Profinite.to_CompHaus_to_Top :
  Profinite.to_CompHaus ⋙ CompHaus_to_Top = Profinite_to_Top :=
rfl

section Profinite
open topological_space
local attribute [instance] connected_component_setoid

universes u

/--
(Implementation) The object part of the connected_components functor from compact Hausdorff spaces
to Profinite spaces, given by quotienting a space by its connected components.
See: https://stacks.math.columbia.edu/tag/0900
-/
-- Without explicit universe annotations here, Lean introduces two universe variables and
-- unhelpfully defines a function `CompHaus.{max u₁ u₂} → Profinite.{max u₁ u₂}`.
def CompHaus.to_Profinite_obj (X : CompHaus.{u}) : Profinite.{u} :=
{ to_Top := { α := connected_components X.to_Top.α },
  is_compact := quotient.compact_space,
  is_t2 := connected_components.t2,
  is_totally_disconnected := connected_components.totally_disconnected_space }

/--
(Implementation) The bijection of homsets to establish the reflective adjunction of Profinite
spaces in compact Hausdorff spaces.
-/
def Profinite.to_CompHaus_equivalence (X : CompHaus.{u}) (Y : Profinite.{u}) :
  (CompHaus.to_Profinite_obj X ⟶ Y) ≃ (X ⟶ Profinite.to_CompHaus.obj Y) :=
{ to_fun := λ f,
  { to_fun := f.1 ∘ quotient.mk,
    continuous_to_fun := continuous.comp f.2 (continuous_quotient_mk) },
  inv_fun := λ g,
    { to_fun := continuous.connected_components_lift g.2,
      continuous_to_fun := continuous.connected_components_lift_continuous g.2},
  left_inv := λ f, continuous_map.ext $ λ x, quotient.induction_on x $ λ a, rfl,
  right_inv := λ f, continuous_map.ext $ λ x, rfl }

/--
The connected_components functor from compact Hausdorff spaces to profinite spaces,
left adjoint to the inclusion functor.
-/
def CompHaus.to_Profinite : CompHaus ⥤ Profinite :=
adjunction.left_adjoint_of_equiv Profinite.to_CompHaus_equivalence (λ _ _ _ _ _, rfl)

/--
The adjunction between CompHaus.to_Profinite and Profinite.to_CompHaus
-/
def Profinite.to_Profinite_adj_to_CompHaus : CompHaus.to_Profinite ⊣ Profinite.to_CompHaus :=
adjunction.adjunction_of_equiv_left _ _

lemma CompHaus.to_Profinite_obj' (X : CompHaus) :
  ↥(CompHaus.to_Profinite.obj X) = connected_components X.to_Top.α := rfl

/-- The category of profinite sets is reflective in the category of compact hausdroff spaces -/
instance Profinite.to_CompHaus.reflective : reflective Profinite.to_CompHaus :=
{ to_is_right_adjoint := ⟨CompHaus.to_Profinite, Profinite.to_Profinite_adj_to_CompHaus⟩ }

/-- The functor from Fintype to Profinite, equipping a given object with the discrete topology. -/
def Fintype.to_Profinite : Fintype ⥤ Profinite :=
{ obj := λ X,
  { to_Top := ⟨X, ⊥⟩,
    is_t2 := @t2_space_discrete _ _ ⟨rfl⟩,
    is_totally_disconnected := by letI:topological_space X := ⊥;
                                  letI:discrete_topology X := ⟨rfl⟩; apply_instance },
  map := λ X Y f, by letI:topological_space X := ⊥; letI:discrete_topology X := ⟨rfl⟩;
                  by letI:topological_space Y := ⊥; letI:discrete_topology Y := ⟨rfl⟩;
                  exact ⟨f, continuous_of_discrete_topology⟩ }

end Profinite

namespace Profinite

/-
In this section we formalize that a profinite set can be seen as a limit of finite sets by
following: https://stacks.math.columbia.edu/tag/08ZY
-/

open set
open category_theory.limits

variable {X : Profinite}

/--
The type of the skeleton, i.e. the points, of the diagram which X will be the limit of.
It is defined as the type of finite, disjoint partitions of X into nonempty clopen sets.
-/
def skeleton (X : Profinite) :=
{ I : set (set (X.to_Top.α)) // (I.finite) ∧ (∀ U ∈ I, is_clopen U ∧ U.nonempty) ∧
  (⋃₀ I = univ) ∧ (∀ U V ∈ I, (U ∩ V : set X.to_Top.α).nonempty → (U = V) ) }

noncomputable instance : inhabited X.skeleton :=
begin
  split,
  by_cases nonempty X,
  -- If X is nonempty, we can pick {X}.
  { refine ⟨{univ},finite_singleton _,λ U hU, _,_,_⟩,
    { rw mem_singleton_iff at hU,
      rw hU,
      refine ⟨is_clopen_univ,_⟩,
      exactI univ_nonempty },
    { simp only [sUnion_singleton] },
    intros U V hU hV hUV,
    rw mem_singleton_iff at hU,
    rw mem_singleton_iff at hV,
    rw [hU, hV] },
  -- If empty, we can pick {}.
  refine ⟨{},finite_empty,_,_,_⟩,
  { rintro _ ⟨⟩ },
  { simp,
    symmetry,
    rw univ_eq_empty_iff,
    exact h },
  rintro _ _ ⟨⟩,
end

instance skeleton_nonempty : nonempty X.skeleton := nonempty_of_inhabited

/--
The skeleton forms a partial order with respect to refinement.
This will be the morphisms of the diagram.
-/
instance skeleton.preorder : preorder (skeleton X) :=
{ le := λ I J, (∀ (U ∈ I.1), (∃ V : set X.to_Top.α, V ∈ J.1 ∧ U ⊆ V)),
  le_refl := λ I U hU, exists.intro U ⟨hU, subset.refl U⟩,
  le_trans :=
  begin
    intros I J K hIJ hJK U hU,
    rcases hIJ U hU with ⟨V, hV, hUV⟩,
    rcases hJK V hV with ⟨W, hW, hVW⟩,
    use W,
    exact ⟨hW, subset.trans hUV hVW⟩,
  end }

/--
The skeleton forms a small category, this will be the codomain of our diagram.
-/
instance : small_category (skeleton X) := preorder.small_category _

/-- Map on objects of the diagram. -/
noncomputable def diagram_obj (I : skeleton X) : Fintype :=
{ α := I.1, str := finite.fintype I.2.1 }

/--
Map on morphisms of the diagram.
If I refines J it sends a clopen set of I to a clopen set of J containing it.
-/
def diagram_map {I J : skeleton X} (f : I ⟶ J) : (diagram_obj I) ⟶ (diagram_obj J) :=
by {exact λ U, ⟨(classical.some (f.1.1 U.1 U.2)), (classical.some_spec (f.1.1 U.1 U.2)).1⟩}

lemma sub_of_diagram_map_self {I J : skeleton X} (f : I ⟶ J) (U : (diagram_obj I).α) :
  U.1 ⊆ (diagram_map f U).1 := (classical.some_spec (f.1.1 U.1 U.2)).2

lemma diagram_map_unique {I J : skeleton X} (f : I ⟶ J)
  (U : (diagram_obj I).α) (V : (diagram_obj J).α)
  (hUV : U.1 ⊆ V.1) : diagram_map f U = V :=
subtype.ext
  (J.2.2.2.2 (diagram_map f U).1 V.1 (diagram_map f U).2 V.2
    (nonempty.mono (subset_inter (sub_of_diagram_map_self f U) hUV) (I.2.2.1 U.1 U.2).2))

/-- The diagram into Fintype given by diagram_obj and diagram_map -/
noncomputable def diagram' (X : Profinite) : skeleton X ⥤ Fintype :=
{ obj := diagram_obj,
  map := λ I J, @diagram_map X I J,
  map_id' := by {refine λ I, funext (λ U, diagram_map_unique _ _ _ (subset.refl U.1)) },
  map_comp' := λ I J K f g, funext (λ U, diagram_map_unique _ _ _
                (subset.trans (sub_of_diagram_map_self f U) (sub_of_diagram_map_self g _)))}

/-- The diagram intro Profinite of which a given profinite set is the limit of -/
noncomputable def diagram (X : Profinite) : skeleton X ⥤ Profinite :=
(diagram' X) ⋙ Fintype.to_Profinite

/--
Projection map from X to a given object of the diagram.
Given a partition I, it sends a point of X to an clopen in the partition that it belongs to.
-/
def projection (I : skeleton X) : X → (diagram_obj I) :=
λ x, by { have H := mem_sUnion.1 ((I.2.2.2.1).symm ▸ (mem_univ x) : x ∈ ⋃₀ I.1),
  exact ⟨classical.some H, classical.some (classical.some_spec H)⟩ }

/-- The image under projection seen as an open subset of X is a member of the original partition -/
lemma projection_mem_of_self (I : skeleton X) (x : X) : (projection I x).1 ∈ I.1 :=
classical.some (classical.some_spec (mem_sUnion.1 ((I.2.2.2.1).symm ▸ (mem_univ x) : x ∈ ⋃₀ I.1)))

/-- Any point of x is a member of its projection seen as an open subset of X -/
lemma projection_point_mem_of_self (I : skeleton X) (x : X) : x ∈ (projection I x).1 :=
classical.some_spec $ classical.some_spec
  (mem_sUnion.1 ((I.2.2.2.1).symm ▸ (mem_univ x) : x ∈ ⋃₀ I.1))

/--
The projection map is well defined, i.e. the clopen set of a partition
containing a given point is unique.
-/
lemma projection_unique (I : skeleton X) {x : X} {U : set X} (hU : U ∈ I.1) (hx : x ∈ U) :
  (projection I x).1 = U :=
I.2.2.2.2 (projection I x).1 U (projection_mem_of_self I x) hU
  (nonempty_of_mem (mem_inter (projection_point_mem_of_self I x) hx))

/-- Preimage of a given set under the partition map -/
lemma projection_preimage {I : skeleton X} (A : set (diagram_obj I)) :
  (projection I ⁻¹' A) = ⋃ (a : A), a.1.1 :=
begin
  refine set.ext (λ x, ⟨λ hx, _ , λ hx, mem_preimage.2 _⟩),
  { exact mem_Union.2 ⟨⟨projection I x, mem_preimage.1 hx⟩, projection_point_mem_of_self I x⟩ },
  rcases mem_Union.1 hx with ⟨⟨U, hU⟩, hx⟩,
  convert hU,
  refine subtype.ext (projection_unique I U.2 hx),
end

/-- X forms a cone over the diagram -/
noncomputable def cone_profinite (X : Profinite) : cone (diagram X) :=
{ X := X,
  π :=
  { app := λ I,
    { to_fun := projection I,
      continuous_to_fun :=
      begin
        fsplit,
        intros A hA,
        rw projection_preimage,
        refine is_open_Union (λ U, (I.2.2.1 U.1.1 U.1.2).1.1),
      end },
    naturality' :=
      begin
        refine λ I J f, continuous_map.ext (λ x, subtype.ext _),
        apply projection_unique _ (diagram_map f (projection I x)).2,
        exact mem_of_subset_of_mem (sub_of_diagram_map_self f _) (projection_point_mem_of_self I x)
      end }}

end Profinite
