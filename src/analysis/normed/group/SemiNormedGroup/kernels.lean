/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin, Scott Morrison
-/
import analysis.normed.group.SemiNormedGroup
import analysis.normed.group.quotient
import category_theory.limits.shapes.kernels

/-!
# Cokernels in SemiNormedGroup₁ and SemiNormedGroup

We show that `SemiNormedGroup₁` has cokernels
(for which of course the `cokernel.π f` maps are norm non-increasing),
as well as the easier result that `SemiNormedGroup` has cokernels.

So far, I don't see a way to state nicely what we really want:
`SemiNormedGroup` has cokernels, and `cokernel.π f` is norm non-increasing.
The problem is that the limits API doesn't promise you any particular model of the cokernel,
and in `SemiNormedGroup` one can always take a cokernel and rescale its norm
(and hence making `cokernel.π f` arbitrarily large in norm), obtaining another categorical cokernel.

-/

open category_theory
open category_theory.limits

universe u

namespace SemiNormedGroup₁

noncomputable theory

/-- Auxiliary definition for `has_cokernels SemiNormedGroup₁`. -/
def cokernel_cocone {X Y : SemiNormedGroup₁.{u}} (f : X ⟶ Y) : cofork f 0 :=
cofork.of_π
  (@SemiNormedGroup₁.mk_hom
    _ (SemiNormedGroup.of (quotient_add_group.quotient (normed_group_hom.range f.1)))
    f.1.range.normed_mk
    (normed_group_hom.is_quotient_quotient _).norm_le)
  begin
    ext,
    simp only [comp_apply, limits.zero_comp, normed_group_hom.zero_apply,
      SemiNormedGroup₁.mk_hom_apply, SemiNormedGroup₁.zero_apply, ←normed_group_hom.mem_ker,
      f.1.range.ker_normed_mk, f.1.mem_range],
    use x,
    refl,
  end

/-- Auxiliary definition for `has_cokernels SemiNormedGroup₁`. -/
def cokernel_lift {X Y : SemiNormedGroup₁.{u}} (f : X ⟶ Y) (s : cokernel_cofork f) :
  (cokernel_cocone f).X ⟶ s.X :=
begin
  fsplit,
  -- The lift itself:
  { apply normed_group_hom.lift _ s.π.1,
    rintro _ ⟨b, rfl⟩,
    change (f ≫ s.π) b = 0,
    simp, },
  -- The lift has norm at most one:
  exact normed_group_hom.lift_norm_noninc _ _ _ s.π.2,
end

instance : has_cokernels SemiNormedGroup₁.{u} :=
{ has_colimit := λ X Y f, has_colimit.mk
  { cocone := cokernel_cocone f,
    is_colimit := is_colimit_aux _
      (cokernel_lift f)
      (λ s, begin
        ext,
        apply normed_group_hom.lift_mk f.1.range,
        rintro _ ⟨b, rfl⟩,
        change (f ≫ s.π) b = 0,
        simp,
      end)
      (λ s m w, subtype.eq
        (normed_group_hom.lift_unique f.1.range _ _ _ (congr_arg subtype.val w : _))), } }

-- Sanity check
example : has_cokernels SemiNormedGroup₁ := by apply_instance

end SemiNormedGroup₁

namespace SemiNormedGroup
-- PROJECT: can we reuse the work to construct cokernels in `SemiNormedGroup₁` here?
-- I don't see a way to do this that is less work than just repeating the relevant parts.

/-- Auxiliary definition for `has_cokernels SemiNormedGroup`. -/
def cokernel_cocone {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) : cofork f 0 :=
@cofork.of_π _ _ _ _ _ _
  (SemiNormedGroup.of (quotient_add_group.quotient (normed_group_hom.range f)))
  f.range.normed_mk
  begin
    ext,
    simp only [comp_apply, limits.zero_comp, normed_group_hom.zero_apply,
      ←normed_group_hom.mem_ker, f.range.ker_normed_mk, f.mem_range, exists_apply_eq_apply],
  end

/-- Auxiliary definition for `has_cokernels SemiNormedGroup`. -/
def cokernel_lift {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) (s : cokernel_cofork f) :
  (cokernel_cocone f).X ⟶ s.X := normed_group_hom.lift _ s.π
begin
  rintro _ ⟨b, rfl⟩,
  change (f ≫ s.π) b = 0,
  simp,
end

/-- Auxiliary definition for `has_cokernels SemiNormedGroup`. -/
def is_colimit_cokernel_cocone {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
  is_colimit (cokernel_cocone f) :=
is_colimit_aux _ (cokernel_lift f)
(λ s, begin
  ext,
  apply normed_group_hom.lift_mk f.range,
  rintro _ ⟨b, rfl⟩,
  change (f ≫ s.π) b = 0,
  simp,
end)
(λ s m w, normed_group_hom.lift_unique f.range _ _ _ w)

instance : has_cokernels SemiNormedGroup.{u} :=
{ has_colimit := λ X Y f, has_colimit.mk
  { cocone := cokernel_cocone f,
    is_colimit := is_colimit_cokernel_cocone f } }

-- Sanity check
example : has_cokernels SemiNormedGroup := by apply_instance

section explicit_cokernel

/-- An explicit choice of cokernel, which has good properties with respect to the norm. -/
def explicit_cokernel {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) : SemiNormedGroup.{u} :=
(cokernel_cocone f).X

/-- Descend to the explicit cokernel. -/
def explicit_cokernel_desc {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (w : f ≫ g = 0) : explicit_cokernel f ⟶ Z :=
(is_colimit_cokernel_cocone f).desc (cofork.of_π g (by simp [w]))

/-- The projection from `Y` to the explicit cokernel of `X ⟶ Y`. -/
def explicit_cokernel_π {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) : Y ⟶ explicit_cokernel f :=
(cokernel_cocone f).ι.app walking_parallel_pair.one

@[simp, reassoc]
lemma comp_explicit_cokernel_π {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
  f ≫ explicit_cokernel_π f = 0 :=
begin
  convert (cokernel_cocone f).w walking_parallel_pair_hom.left,
  simp,
end

@[simp, reassoc]
lemma explicit_cokernel_π_desc {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (w : f ≫ g = 0) : explicit_cokernel_π f ≫ explicit_cokernel_desc w = g :=
(is_colimit_cokernel_cocone f).fac _ _

lemma explicit_cokernel_desc_unique {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (w : f ≫ g = 0) (e : explicit_cokernel f ⟶ Z) (he : explicit_cokernel_π f ≫ e = g) :
  e = explicit_cokernel_desc w :=
begin
  apply (is_colimit_cokernel_cocone f).uniq (cofork.of_π g (by simp [w])),
  rintro (_|_),
  { convert w.symm,
    simp },
  { exact he }
end

@[ext]
lemma explicit_cokernel_hom_ext {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y}
  (e₁ e₂ : explicit_cokernel f ⟶ Z)
  (h : explicit_cokernel_π f ≫ e₁ = explicit_cokernel_π f ≫ e₂) : e₁ = e₂ :=
begin
  let g : Y ⟶ Z := explicit_cokernel_π f ≫ e₂,
  have w : f ≫ g = 0, by simp,
  have : e₂ = explicit_cokernel_desc w,
  { apply explicit_cokernel_desc_unique, refl },
  rw this,
  apply explicit_cokernel_desc_unique,
  exact h,
end

lemma is_quotient_explicit_cokernel_π {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
normed_group_hom.is_quotient (explicit_cokernel_π f) :=
normed_group_hom.is_quotient_quotient _

lemma norm_noninc_explicit_cokernel_π {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
  (explicit_cokernel_π f).norm_noninc :=
(is_quotient_explicit_cokernel_π f).norm_le

open_locale nnreal

lemma explicit_cokernel_desc_norm_le_of_norm_le {X Y Z : SemiNormedGroup.{u}}
  {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) (c : ℝ≥0) (h : ∥ g ∥ ≤ c) :
  ∥ explicit_cokernel_desc w ∥ ≤ c :=
normed_group_hom.lift_norm_le _ _ _ h

lemma explicit_cokernel_desc_norm_le {X Y Z : SemiNormedGroup.{u}}
  {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) : ∥ explicit_cokernel_desc w ∥ ≤ ∥ g ∥ :=
explicit_cokernel_desc_norm_le_of_norm_le w ∥ g ∥₊ (le_refl _)

/-- The explicit cokernel is isomorphic to the usual cokernel. -/
def explicit_cokernel_iso {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
  explicit_cokernel f ≅ cokernel f :=
(is_colimit_cokernel_cocone f).cocone_point_unique_up_to_iso (colimit.is_colimit _)

@[simp]
lemma explicit_cokernel_iso_hom_π {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
  explicit_cokernel_π f ≫ (explicit_cokernel_iso f).hom = cokernel.π _ :=
by simp [explicit_cokernel_π, explicit_cokernel_iso]

@[simp]
lemma explicit_cokernel_iso_inv_π {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
  cokernel.π f ≫ (explicit_cokernel_iso f).inv = explicit_cokernel_π f :=
by simp [explicit_cokernel_π, explicit_cokernel_iso]

@[simp]
lemma explicit_cokernel_iso_hom_desc {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (w : f ≫ g = 0) :
  (explicit_cokernel_iso f).hom ≫ cokernel.desc f g w = explicit_cokernel_desc w :=
begin
  ext1,
  simp [explicit_cokernel_desc, explicit_cokernel_π, explicit_cokernel_iso],
end

end explicit_cokernel

end SemiNormedGroup
