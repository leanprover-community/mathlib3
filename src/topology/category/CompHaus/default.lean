/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bhavik Mehta
-/

import category_theory.adjunction.reflective
import topology.category.Top
import topology.stone_cech
import category_theory.monad.limits
import topology.urysohns_lemma

/-!
# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `Top`.
The fully faithful functor `CompHaus ⥤ Top` is denoted `CompHaus_to_Top`.

**Note:** The file `topology/category/Compactum.lean` provides the equivalence between `Compactum`,
which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`Compactum_to_CompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `Compactum_to_CompHaus.is_equivalence`.
See `topology/category/Compactum.lean` for a more detailed discussion where these definitions are
introduced.

-/

universes v u

open category_theory

/-- The type of Compact Hausdorff topological spaces. -/
structure CompHaus :=
(to_Top : Top)
[is_compact : compact_space to_Top]
[is_hausdorff : t2_space to_Top]

namespace CompHaus

instance : inhabited CompHaus := ⟨{to_Top := { α := pempty }}⟩

instance : has_coe_to_sort CompHaus Type* := ⟨λ X, X.to_Top⟩
instance {X : CompHaus} : compact_space X := X.is_compact
instance {X : CompHaus} : t2_space X := X.is_hausdorff

instance category : category CompHaus := induced_category.category to_Top

instance concrete_category : concrete_category CompHaus :=
induced_category.concrete_category _

@[simp]
lemma coe_to_Top {X : CompHaus} : (X.to_Top : Type*) = X :=
rfl

variables (X : Type*) [topological_space X] [compact_space X] [t2_space X]

/-- A constructor for objects of the category `CompHaus`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference. -/
def of : CompHaus :=
{ to_Top := Top.of X,
  is_compact := ‹_›,
  is_hausdorff := ‹_› }

@[simp] lemma coe_of : (CompHaus.of X : Type _) = X := rfl

/-- Any continuous function on compact Hausdorff spaces is a closed map. -/
lemma is_closed_map {X Y : CompHaus.{u}} (f : X ⟶ Y) : is_closed_map f :=
λ C hC, (hC.is_compact.image f.continuous).is_closed

/-- Any continuous bijection of compact Hausdorff spaces is an isomorphism. -/
lemma is_iso_of_bijective {X Y : CompHaus.{u}} (f : X ⟶ Y) (bij : function.bijective f) :
  is_iso f :=
begin
  let E := equiv.of_bijective _ bij,
  have hE : continuous E.symm,
  { rw continuous_iff_is_closed,
    intros S hS,
    rw ← E.image_eq_preimage,
    exact is_closed_map f S hS },
  refine ⟨⟨⟨E.symm, hE⟩, _, _⟩⟩,
  { ext x,
    apply E.symm_apply_apply },
  { ext x,
    apply E.apply_symm_apply }
end

/-- Any continuous bijection of compact Hausdorff spaces induces an isomorphism. -/
noncomputable
def iso_of_bijective {X Y : CompHaus.{u}} (f : X ⟶ Y) (bij : function.bijective f) : X ≅ Y :=
by letI := is_iso_of_bijective _ bij; exact as_iso f

end CompHaus

/-- The fully faithful embedding of `CompHaus` in `Top`. -/
@[simps {rhs_md := semireducible}, derive [full, faithful]]
def CompHaus_to_Top : CompHaus.{u} ⥤ Top.{u} := induced_functor _

instance CompHaus.forget_reflects_isomorphisms : reflects_isomorphisms (forget CompHaus.{u}) :=
⟨by introsI A B f hf; exact CompHaus.is_iso_of_bijective _ ((is_iso_iff_bijective f).mp hf)⟩

/--
(Implementation) The object part of the compactification functor from topological spaces to
compact Hausdorff spaces.
-/
@[simps]
def StoneCech_obj (X : Top) : CompHaus := CompHaus.of (stone_cech X)

/--
(Implementation) The bijection of homsets to establish the reflective adjunction of compact
Hausdorff spaces in topological spaces.
-/
noncomputable def stone_cech_equivalence (X : Top.{u}) (Y : CompHaus.{u}) :
  (StoneCech_obj X ⟶ Y) ≃ (X ⟶ CompHaus_to_Top.obj Y) :=
{ to_fun := λ f,
  { to_fun := f ∘ stone_cech_unit,
    continuous_to_fun := f.2.comp (@continuous_stone_cech_unit X _) },
  inv_fun := λ f,
  { to_fun := stone_cech_extend f.2,
    continuous_to_fun := continuous_stone_cech_extend f.2 },
  left_inv :=
  begin
    rintro ⟨f : stone_cech X ⟶ Y, hf : continuous f⟩,
    ext (x : stone_cech X),
    refine congr_fun _ x,
    apply continuous.ext_on dense_range_stone_cech_unit (continuous_stone_cech_extend _) hf,
    rintro _ ⟨y, rfl⟩,
    apply congr_fun (stone_cech_extend_extends (hf.comp _)) y,
  end,
  right_inv :=
  begin
    rintro ⟨f : (X : Type*) ⟶ Y, hf : continuous f⟩,
    ext,
    exact congr_fun (stone_cech_extend_extends hf) _,
  end }

/--
The Stone-Cech compactification functor from topological spaces to compact Hausdorff spaces,
left adjoint to the inclusion functor.
-/
noncomputable def Top_to_CompHaus : Top.{u} ⥤ CompHaus.{u} :=
adjunction.left_adjoint_of_equiv stone_cech_equivalence.{u} (λ _ _ _ _ _, rfl)

lemma Top_to_CompHaus_obj (X : Top) : ↥(Top_to_CompHaus.obj X) = stone_cech X :=
rfl

/--
The category of compact Hausdorff spaces is reflective in the category of topological spaces.
-/
noncomputable instance CompHaus_to_Top.reflective : reflective CompHaus_to_Top :=
{ to_is_right_adjoint := ⟨Top_to_CompHaus, adjunction.adjunction_of_equiv_left _ _⟩ }

noncomputable instance CompHaus_to_Top.creates_limits : creates_limits CompHaus_to_Top :=
monadic_creates_limits _

instance CompHaus.has_limits : limits.has_limits CompHaus :=
has_limits_of_has_limits_creates_limits CompHaus_to_Top

instance CompHaus.has_colimits : limits.has_colimits CompHaus :=
has_colimits_of_reflective CompHaus_to_Top

namespace CompHaus

/-- An explicit limit cone for a functor `F : J ⥤ CompHaus`, defined in terms of
`Top.limit_cone`. -/
def limit_cone {J : Type v} [small_category J] (F : J ⥤ CompHaus.{max v u}) :
  limits.cone F :=
{ X :=
  { to_Top := (Top.limit_cone (F ⋙ CompHaus_to_Top)).X,
    is_compact := begin
      show compact_space ↥{u : Π j, (F.obj j) | ∀ {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j},
      rw ← is_compact_iff_compact_space,
      apply is_closed.is_compact,
      have : {u : Π j, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j} =
        ⋂ (i j : J) (f : i ⟶ j), {u | F.map f (u i) = u j},
      { ext1, simp only [set.mem_Inter, set.mem_set_of_eq], },
      rw this,
      apply is_closed_Inter, intros i,
      apply is_closed_Inter, intros j,
      apply is_closed_Inter, intros f,
      apply is_closed_eq,
      { exact (continuous_map.continuous (F.map f)).comp (continuous_apply i), },
      { exact continuous_apply j, }
    end,
    is_hausdorff :=
      show t2_space ↥{u : Π j, (F.obj j) | ∀ {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j},
      from infer_instance },
  π :=
  { app := λ j, (Top.limit_cone (F ⋙ CompHaus_to_Top)).π.app j,
    naturality' := by { intros _ _ _, ext ⟨x, hx⟩,
      simp only [comp_apply, functor.const.obj_map, id_apply], exact (hx f).symm, } } }

/-- The limit cone `CompHaus.limit_cone F` is indeed a limit cone. -/
def limit_cone_is_limit {J : Type v} [small_category J] (F : J ⥤ CompHaus.{max v u}) :
  limits.is_limit (limit_cone F) :=
{ lift := λ S,
    (Top.limit_cone_is_limit (F ⋙ CompHaus_to_Top)).lift (CompHaus_to_Top.map_cone S),
  uniq' := λ S m h, (Top.limit_cone_is_limit _).uniq (CompHaus_to_Top.map_cone S) _ h }

lemma epi_iff_surjective {X Y : CompHaus.{u}} (f : X ⟶ Y) : epi f ↔ function.surjective f :=
begin
  split,
  { contrapose!,
    rintros ⟨y, hy⟩ hf,
    let C := set.range f,
    have hC : is_closed C := (is_compact_range f.continuous).is_closed,
    let D := {y},
    have hD : is_closed D := is_closed_singleton,
    have hCD : disjoint C D,
    { rw set.disjoint_singleton_right, rintro ⟨y', hy'⟩, exact hy y' hy' },
    haveI : normal_space ↥(Y.to_Top) := normal_of_compact_t2,
    obtain ⟨φ, hφ0, hφ1, hφ01⟩ := exists_continuous_zero_one_of_closed hC hD hCD,
    haveI : compact_space (ulift.{u} $ set.Icc (0:ℝ) 1) := homeomorph.ulift.symm.compact_space,
    haveI : t2_space (ulift.{u} $ set.Icc (0:ℝ) 1) := homeomorph.ulift.symm.t2_space,
    let Z := of (ulift.{u} $ set.Icc (0:ℝ) 1),
    let g : Y ⟶ Z := ⟨λ y', ⟨⟨φ y', hφ01 y'⟩⟩,
      continuous_ulift_up.comp (continuous_subtype_mk (λ y', hφ01 y') φ.continuous)⟩,
    let h : Y ⟶ Z := ⟨λ _, ⟨⟨0, set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩,
    have H : h = g,
    { rw ← cancel_epi f,
      ext x, dsimp,
      simp only [comp_apply, continuous_map.coe_mk, subtype.coe_mk, hφ0 (set.mem_range_self x),
        pi.zero_apply], },
    apply_fun (λ e, (e y).down) at H,
    dsimp at H,
    simp only [subtype.mk_eq_mk, hφ1 (set.mem_singleton y), pi.one_apply] at H,
    exact zero_ne_one H, },
  { rw ← category_theory.epi_iff_surjective,
    apply faithful_reflects_epi (forget CompHaus) },
end

lemma mono_iff_injective {X Y : CompHaus.{u}} (f : X ⟶ Y) : mono f ↔ function.injective f :=
begin
  split,
  { introsI hf x₁ x₂ h,
    let g₁ : of punit ⟶ X := ⟨λ _, x₁, continuous_of_discrete_topology⟩,
    let g₂ : of punit ⟶ X := ⟨λ _, x₂, continuous_of_discrete_topology⟩,
    have : g₁ ≫ f = g₂ ≫ f, by { ext, exact h },
    rw cancel_mono at this,
    apply_fun (λ e, e punit.star) at this,
    exact this },
  { rw ← category_theory.mono_iff_injective,
    apply faithful_reflects_mono (forget CompHaus) }
end

end CompHaus
