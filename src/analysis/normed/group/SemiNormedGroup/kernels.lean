/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin, Scott Morrison
-/
import analysis.normed.group.SemiNormedGroup
import analysis.normed.group.quotient
import category_theory.limits.shapes.kernels

/-!
# Kernels and cokernels in SemiNormedGroup₁ and SemiNormedGroup

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that `SemiNormedGroup₁` has cokernels
(for which of course the `cokernel.π f` maps are norm non-increasing),
as well as the easier result that `SemiNormedGroup` has cokernels. We also show that
`SemiNormedGroup` has kernels.

So far, I don't see a way to state nicely what we really want:
`SemiNormedGroup` has cokernels, and `cokernel.π f` is norm non-increasing.
The problem is that the limits API doesn't promise you any particular model of the cokernel,
and in `SemiNormedGroup` one can always take a cokernel and rescale its norm
(and hence making `cokernel.π f` arbitrarily large in norm), obtaining another categorical cokernel.

-/

open category_theory category_theory.limits

universe u

namespace SemiNormedGroup₁

noncomputable theory

/-- Auxiliary definition for `has_cokernels SemiNormedGroup₁`. -/
def cokernel_cocone {X Y : SemiNormedGroup₁.{u}} (f : X ⟶ Y) : cofork f 0 :=
cofork.of_π
  (@SemiNormedGroup₁.mk_hom
    _ (SemiNormedGroup.of (Y ⧸ (normed_add_group_hom.range f.1)))
    f.1.range.normed_mk
    (normed_add_group_hom.is_quotient_quotient _).norm_le)
  begin
    ext,
    simp only [comp_apply, limits.zero_comp, normed_add_group_hom.zero_apply,
      SemiNormedGroup₁.mk_hom_apply, SemiNormedGroup₁.zero_apply, ←normed_add_group_hom.mem_ker,
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
  { apply normed_add_group_hom.lift _ s.π.1,
    rintro _ ⟨b, rfl⟩,
    change (f ≫ s.π) b = 0,
    simp, },
  -- The lift has norm at most one:
  exact normed_add_group_hom.lift_norm_noninc _ _ _ s.π.2,
end

instance : has_cokernels SemiNormedGroup₁.{u} :=
{ has_colimit := λ X Y f, has_colimit.mk
  { cocone := cokernel_cocone f,
    is_colimit := is_colimit_aux _
      (cokernel_lift f)
      (λ s, begin
        ext,
        apply normed_add_group_hom.lift_mk f.1.range,
        rintro _ ⟨b, rfl⟩,
        change (f ≫ s.π) b = 0,
        simp,
      end)
      (λ s m w, subtype.eq
        (normed_add_group_hom.lift_unique f.1.range _ _ _ (congr_arg subtype.val w : _))), } }

-- Sanity check
example : has_cokernels SemiNormedGroup₁ := by apply_instance

end SemiNormedGroup₁

namespace SemiNormedGroup

section equalizers_and_kernels

/-- The equalizer cone for a parallel pair of morphisms of seminormed groups. -/
def fork {V W : SemiNormedGroup.{u}} (f g : V ⟶ W) : fork f g :=
@fork.of_ι _ _ _ _ _ _ (of (f - g).ker) (normed_add_group_hom.incl (f - g).ker) $
begin
  ext v,
  have : v.1 ∈ (f - g).ker := v.2,
  simpa only [normed_add_group_hom.incl_apply, pi.zero_apply, coe_comp,
    normed_add_group_hom.coe_zero, subtype.val_eq_coe, normed_add_group_hom.mem_ker,
    normed_add_group_hom.coe_sub, pi.sub_apply, sub_eq_zero] using this
end

instance has_limit_parallel_pair {V W : SemiNormedGroup.{u}} (f g : V ⟶ W) :
  has_limit (parallel_pair f g) :=
{ exists_limit := nonempty.intro
  { cone := fork f g,
    is_limit := fork.is_limit.mk _
      (λ c, normed_add_group_hom.ker.lift (fork.ι c) _ $
      show normed_add_group_hom.comp_hom (f - g) c.ι = 0,
      by { rw [add_monoid_hom.map_sub, add_monoid_hom.sub_apply, sub_eq_zero], exact c.condition })
      (λ c, normed_add_group_hom.ker.incl_comp_lift _ _ _)
      (λ c g h, by { ext x, dsimp, rw ← h, refl }) } }

instance : limits.has_equalizers.{u (u+1)} SemiNormedGroup :=
@has_equalizers_of_has_limit_parallel_pair SemiNormedGroup _ $ λ V W f g,
  SemiNormedGroup.has_limit_parallel_pair f g

end equalizers_and_kernels

section cokernel

-- PROJECT: can we reuse the work to construct cokernels in `SemiNormedGroup₁` here?
-- I don't see a way to do this that is less work than just repeating the relevant parts.

/-- Auxiliary definition for `has_cokernels SemiNormedGroup`. -/
def cokernel_cocone {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) : cofork f 0 :=
@cofork.of_π _ _ _ _ _ _
  (SemiNormedGroup.of (Y ⧸ (normed_add_group_hom.range f)))
  f.range.normed_mk
  begin
    ext,
    simp only [comp_apply, limits.zero_comp, normed_add_group_hom.zero_apply,
      ←normed_add_group_hom.mem_ker, f.range.ker_normed_mk, f.mem_range, exists_apply_eq_apply],
  end

/-- Auxiliary definition for `has_cokernels SemiNormedGroup`. -/
def cokernel_lift {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) (s : cokernel_cofork f) :
  (cokernel_cocone f).X ⟶ s.X := normed_add_group_hom.lift _ s.π
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
  apply normed_add_group_hom.lift_mk f.range,
  rintro _ ⟨b, rfl⟩,
  change (f ≫ s.π) b = 0,
  simp,
end)
(λ s m w, normed_add_group_hom.lift_unique f.range _ _ _ w)

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

lemma explicit_cokernel_π_surjective {X Y : SemiNormedGroup.{u}} {f : X ⟶ Y} :
  function.surjective (explicit_cokernel_π f) :=
surjective_quot_mk _

@[simp, reassoc]
lemma comp_explicit_cokernel_π {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
  f ≫ explicit_cokernel_π f = 0 :=
begin
  convert (cokernel_cocone f).w walking_parallel_pair_hom.left,
  simp,
end

@[simp]
lemma explicit_cokernel_π_apply_dom_eq_zero {X Y : SemiNormedGroup.{u}} {f : X ⟶ Y} (x : X) :
  (explicit_cokernel_π f) (f x) = 0 :=
show (f ≫ (explicit_cokernel_π f)) x = 0, by { rw [comp_explicit_cokernel_π], refl }

@[simp, reassoc]
lemma explicit_cokernel_π_desc {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (w : f ≫ g = 0) : explicit_cokernel_π f ≫ explicit_cokernel_desc w = g :=
(is_colimit_cokernel_cocone f).fac _ _

@[simp]
lemma explicit_cokernel_π_desc_apply {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  {cond : f ≫ g = 0} (x : Y) : explicit_cokernel_desc cond (explicit_cokernel_π f x) = g x :=
show (explicit_cokernel_π f ≫ explicit_cokernel_desc cond) x = g x, by rw explicit_cokernel_π_desc

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

lemma explicit_cokernel_desc_comp_eq_desc {X Y Z W : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  {h : Z ⟶ W} {cond : f ≫ g = 0} :
  explicit_cokernel_desc cond ≫ h = explicit_cokernel_desc (show f ≫ (g ≫ h) = 0,
  by rw [← category_theory.category.assoc, cond, limits.zero_comp]) :=
begin
  refine explicit_cokernel_desc_unique _ _ _,
  rw [← category_theory.category.assoc, explicit_cokernel_π_desc]
end

@[simp]
lemma explicit_cokernel_desc_zero {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} :
  explicit_cokernel_desc (show f ≫ (0 : Y ⟶ Z) = 0, from category_theory.limits.comp_zero) = 0 :=
eq.symm $ explicit_cokernel_desc_unique _ _ category_theory.limits.comp_zero

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

instance explicit_cokernel_π.epi {X Y : SemiNormedGroup.{u}} {f : X ⟶ Y} :
  epi (explicit_cokernel_π f) :=
begin
  constructor,
  intros Z g h H,
  ext x,
  obtain ⟨x, hx⟩ := explicit_cokernel_π_surjective (explicit_cokernel_π f x),
  change (explicit_cokernel_π f ≫ g) _ = _,
  rw [H]
end

lemma is_quotient_explicit_cokernel_π {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
normed_add_group_hom.is_quotient (explicit_cokernel_π f) :=
normed_add_group_hom.is_quotient_quotient _

lemma norm_noninc_explicit_cokernel_π {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
  (explicit_cokernel_π f).norm_noninc :=
(is_quotient_explicit_cokernel_π f).norm_le

open_locale nnreal

lemma explicit_cokernel_desc_norm_le_of_norm_le {X Y Z : SemiNormedGroup.{u}}
  {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) (c : ℝ≥0) (h : ‖ g ‖ ≤ c) :
  ‖ explicit_cokernel_desc w ‖ ≤ c :=
normed_add_group_hom.lift_norm_le _ _ _ h

lemma explicit_cokernel_desc_norm_noninc {X Y Z : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  {cond : f ≫ g = 0} (hg : g.norm_noninc) :
  (explicit_cokernel_desc cond).norm_noninc :=
begin
  refine normed_add_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.2 _,
  rw [← nnreal.coe_one],
  exact explicit_cokernel_desc_norm_le_of_norm_le cond 1
    (normed_add_group_hom.norm_noninc.norm_noninc_iff_norm_le_one.1 hg)
end

lemma explicit_cokernel_desc_comp_eq_zero {X Y Z W : SemiNormedGroup.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  {h : Z ⟶ W} (cond : f ≫ g = 0) (cond2 : g ≫ h = 0) :
  explicit_cokernel_desc cond ≫ h = 0 :=
begin
  rw [← cancel_epi (explicit_cokernel_π f), ← category.assoc, explicit_cokernel_π_desc],
  simp [cond2]
end

lemma explicit_cokernel_desc_norm_le {X Y Z : SemiNormedGroup.{u}}
  {f : X ⟶ Y} {g : Y ⟶ Z} (w : f ≫ g = 0) : ‖ explicit_cokernel_desc w ‖ ≤ ‖ g ‖ :=
explicit_cokernel_desc_norm_le_of_norm_le w ‖ g ‖₊ le_rfl

/-- The explicit cokernel is isomorphic to the usual cokernel. -/
def explicit_cokernel_iso {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
  explicit_cokernel f ≅ cokernel f :=
(is_colimit_cokernel_cocone f).cocone_point_unique_up_to_iso (colimit.is_colimit _)

@[simp]
lemma explicit_cokernel_iso_hom_π {X Y : SemiNormedGroup.{u}} (f : X ⟶ Y) :
  explicit_cokernel_π f ≫ (explicit_cokernel_iso f).hom = cokernel.π _ :=
by simp [explicit_cokernel_π, explicit_cokernel_iso, is_colimit.cocone_point_unique_up_to_iso]

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
  simp [explicit_cokernel_desc, explicit_cokernel_π, explicit_cokernel_iso,
    is_colimit.cocone_point_unique_up_to_iso],
end

/-- A special case of `category_theory.limits.cokernel.map` adapted to `explicit_cokernel`. -/
noncomputable def explicit_cokernel.map {A B C D : SemiNormedGroup.{u}} {fab : A ⟶ B}
  {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D} (h : fab ≫ fbd = fac ≫ fcd) :
  explicit_cokernel fab ⟶ explicit_cokernel fcd :=
@explicit_cokernel_desc _ _ _ fab (fbd ≫ explicit_cokernel_π _) $ by simp [reassoc_of h]

/-- A special case of `category_theory.limits.cokernel.map_desc` adapted to `explicit_cokernel`. -/
lemma explicit_coker.map_desc {A B C D B' D' : SemiNormedGroup.{u}}
  {fab : A ⟶ B} {fbd : B ⟶ D} {fac : A ⟶ C} {fcd : C ⟶ D}
  {h : fab ≫ fbd = fac ≫ fcd} {fbb' : B ⟶ B'} {fdd' : D ⟶ D'}
  {condb : fab ≫ fbb' = 0} {condd : fcd ≫ fdd' = 0} {g : B' ⟶ D'}
  (h' : fbb' ≫ g = fbd ≫ fdd'):
  explicit_cokernel_desc condb ≫ g = explicit_cokernel.map h ≫ explicit_cokernel_desc condd :=
begin
  delta explicit_cokernel.map,
  simp [← cancel_epi (explicit_cokernel_π fab), category.assoc, explicit_cokernel_π_desc, h']
end

end explicit_cokernel

end cokernel

end SemiNormedGroup
