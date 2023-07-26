/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.normal_mono.equalizers
import category_theory.abelian.images
import category_theory.preadditive.basic

/-!
# Every non_preadditive_abelian category is preadditive

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In mathlib, we define an abelian category as a preadditive category with a zero object,
kernels and cokernels, products and coproducts and in which every monomorphism and epimorphis is
normal.

While virtually every interesting abelian category has a natural preadditive structure (which is why
it is included in the definition), preadditivity is not actually needed: Every category that has
all of the other properties appearing in the definition of an abelian category admits a preadditive
structure. This is the construction we carry out in this file.

The proof proceeds in roughly five steps:
1. Prove some results (for example that all equalizers exist) that would be trivial if we already
   had the preadditive structure but are a bit of work without it.
2. Develop images and coimages to show that every monomorphism is the kernel of its cokernel.

The results of the first two steps are also useful for the "normal" development of abelian
categories, and will be used there.

3. For every object `A`, define a "subtraction" morphism `σ : A ⨯ A ⟶ A` and use it to define
   subtraction on morphisms as `f - g := prod.lift f g ≫ σ`.
4. Prove a small number of identities about this subtraction from the definition of `σ`.
5. From these identities, prove a large number of other identities that imply that defining
   `f + g := f - (0 - g)` indeed gives an abelian group structure on morphisms such that composition
   is bilinear.

The construction is non-trivial and it is quite remarkable that this abelian group structure can
be constructed purely from the existence of a few limits and colimits. Even more remarkably,
since abelian categories admit exactly one preadditive structure (see
`subsingleton_preadditive_of_has_binary_biproducts`), the construction manages to exactly
reconstruct any natural preadditive structure the category may have.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

-/

noncomputable theory

open category_theory
open category_theory.limits

namespace category_theory
section
universes v u

variables (C : Type u) [category.{v} C]

/-- We call a category `non_preadditive_abelian` if it has a zero object, kernels, cokernels, binary
    products and coproducts, and every monomorphism and every epimorphism is normal. -/
class non_preadditive_abelian extends has_zero_morphisms C, normal_mono_category C,
  normal_epi_category C :=
[has_zero_object : has_zero_object C]
[has_kernels : has_kernels C]
[has_cokernels : has_cokernels C]
[has_finite_products : has_finite_products C]
[has_finite_coproducts : has_finite_coproducts C]

set_option default_priority 100

attribute [instance] non_preadditive_abelian.has_zero_object
attribute [instance] non_preadditive_abelian.has_kernels
attribute [instance] non_preadditive_abelian.has_cokernels
attribute [instance] non_preadditive_abelian.has_finite_products
attribute [instance] non_preadditive_abelian.has_finite_coproducts

end
end category_theory

open category_theory

universes v u

variables {C : Type u} [category.{v} C] [non_preadditive_abelian C]

namespace category_theory.non_preadditive_abelian

section factor

variables {P Q : C} (f : P ⟶ Q)

/-- The map `p : P ⟶ image f` is an epimorphism -/
instance : epi (abelian.factor_thru_image f) :=
let I := abelian.image f, p := abelian.factor_thru_image f,
    i := kernel.ι (cokernel.π f) in
-- It will suffice to consider some g : I ⟶ R such that p ≫ g = 0 and show that g = 0.
normal_mono_category.epi_of_zero_cancel _ $ λ R (g : I ⟶ R) (hpg : p ≫ g = 0),
begin
  -- Since C is abelian, u := ker g ≫ i is the kernel of some morphism h.
  let u := kernel.ι g ≫ i,
  haveI : mono u := mono_comp _ _,
  haveI hu := normal_mono_of_mono u,
  let h := hu.g,
  -- By hypothesis, p factors through the kernel of g via some t.
  obtain ⟨t, ht⟩ := kernel.lift' g p hpg,
  have fh : f ≫ h = 0, calc
    f ≫ h = (p ≫ i) ≫ h : (abelian.image.fac f).symm ▸ rfl
       ... = ((t ≫ kernel.ι g) ≫ i) ≫ h : ht ▸ rfl
       ... = t ≫ u ≫ h : by simp only [category.assoc]; conv_lhs { congr, skip, rw ←category.assoc }
       ... = t ≫ 0 : hu.w ▸ rfl
       ... = 0 : has_zero_morphisms.comp_zero _ _,
  -- h factors through the cokernel of f via some l.
  obtain ⟨l, hl⟩ := cokernel.desc' f h fh,
  have hih : i ≫ h = 0, calc
    i ≫ h = i ≫ cokernel.π f ≫ l : hl ▸ rfl
       ... = 0 ≫ l : by rw [←category.assoc, kernel.condition]
       ... = 0 : zero_comp,
  -- i factors through u = ker h via some s.
  obtain ⟨s, hs⟩ := normal_mono.lift' u i hih,
  have hs' : (s ≫ kernel.ι g) ≫ i = 𝟙 I ≫ i, by rw [category.assoc, hs, category.id_comp],
  haveI : epi (kernel.ι g) := epi_of_epi_fac ((cancel_mono _).1 hs'),
  -- ker g is an epimorphism, but ker g ≫ g = 0 = ker g ≫ 0, so g = 0 as required.
  exact zero_of_epi_comp _ (kernel.condition g)
end

instance is_iso_factor_thru_image [mono f] : is_iso (abelian.factor_thru_image f) :=
is_iso_of_mono_of_epi _

/-- The canonical morphism `i : coimage f ⟶ Q` is a monomorphism -/
instance : mono (abelian.factor_thru_coimage f) :=
let I := abelian.coimage f, i := abelian.factor_thru_coimage f,
    p := cokernel.π (kernel.ι f) in
normal_epi_category.mono_of_cancel_zero _ $ λ R (g : R ⟶ I) (hgi : g ≫ i = 0),
begin
  -- Since C is abelian, u := p ≫ coker g is the cokernel of some morphism h.
  let u := p ≫ cokernel.π g,
  haveI : epi u := epi_comp _ _,
  haveI hu := normal_epi_of_epi u,
  let h := hu.g,
  -- By hypothesis, i factors through the cokernel of g via some t.
  obtain ⟨t, ht⟩ := cokernel.desc' g i hgi,
  have hf : h ≫ f = 0, calc
    h ≫ f = h ≫ (p ≫ i) : (abelian.coimage.fac f).symm ▸ rfl
    ... = h ≫ (p ≫ (cokernel.π g ≫ t)) : ht ▸ rfl
    ... = h ≫ u ≫ t : by simp only [category.assoc]; conv_lhs { congr, skip, rw ←category.assoc }
    ... = 0 ≫ t : by rw [←category.assoc, hu.w]
    ... = 0 : zero_comp,
  -- h factors through the kernel of f via some l.
  obtain ⟨l, hl⟩ := kernel.lift' f h hf,
  have hhp : h ≫ p = 0, calc
    h ≫ p = (l ≫ kernel.ι f) ≫ p : hl ▸ rfl
    ... = l ≫ 0 : by rw [category.assoc, cokernel.condition]
    ... = 0 : comp_zero,
  -- p factors through u = coker h via some s.
  obtain ⟨s, hs⟩ := normal_epi.desc' u p hhp,
  have hs' : p ≫ cokernel.π g ≫ s = p ≫ 𝟙 I, by rw [←category.assoc, hs, category.comp_id],
  haveI : mono (cokernel.π g) := mono_of_mono_fac ((cancel_epi _).1 hs'),
  -- coker g is a monomorphism, but g ≫ coker g = 0 = 0 ≫ coker g, so g = 0 as required.
  exact zero_of_comp_mono _ (cokernel.condition g)
end

instance is_iso_factor_thru_coimage [epi f] :
  is_iso (abelian.factor_thru_coimage f) :=
is_iso_of_mono_of_epi _

end factor

section cokernel_of_kernel
variables {X Y : C} {f : X ⟶ Y}

/-- In a `non_preadditive_abelian` category, an epi is the cokernel of its kernel. More precisely:
    If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
    of `fork.ι s`. -/
def epi_is_cokernel_of_kernel [epi f] (s : fork f 0) (h : is_limit s) :
  is_colimit (cokernel_cofork.of_π f (kernel_fork.condition s)) :=
is_cokernel.cokernel_iso _ _
  (cokernel.of_iso_comp _ _
    (limits.is_limit.cone_point_unique_up_to_iso (limit.is_limit _) h)
    (cone_morphism.w (limits.is_limit.unique_up_to_iso (limit.is_limit _) h).hom _))
  (as_iso $ abelian.factor_thru_coimage f) (abelian.coimage.fac f)

/-- In a `non_preadditive_abelian` category, a mono is the kernel of its cokernel. More precisely:
    If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, then `f` is a kernel
    of `cofork.π s`. -/
def mono_is_kernel_of_cokernel [mono f] (s : cofork f 0) (h : is_colimit s) :
  is_limit (kernel_fork.of_ι f (cokernel_cofork.condition s)) :=
is_kernel.iso_kernel _ _
  (kernel.of_comp_iso _ _
    (limits.is_colimit.cocone_point_unique_up_to_iso h (colimit.is_colimit _))
    (cocone_morphism.w (limits.is_colimit.unique_up_to_iso h $ colimit.is_colimit _).hom _))
  (as_iso $ abelian.factor_thru_image f) (abelian.image.fac f)

end cokernel_of_kernel
section

/-- The composite `A ⟶ A ⨯ A ⟶ cokernel (Δ A)`, where the first map is `(𝟙 A, 0)` and the second map
    is the canonical projection into the cokernel. -/
abbreviation r (A : C) : A ⟶ cokernel (diag A) := prod.lift (𝟙 A) 0 ≫ cokernel.π (diag A)

instance mono_Δ {A : C} : mono (diag A) := mono_of_mono_fac $ prod.lift_fst _ _

instance mono_r {A : C} : mono (r A) :=
begin
  let hl : is_limit (kernel_fork.of_ι (diag A) (cokernel.condition (diag A))),
  { exact mono_is_kernel_of_cokernel _ (colimit.is_colimit _) },
  apply normal_epi_category.mono_of_cancel_zero,
  intros Z x hx,
  have hxx : (x ≫ prod.lift (𝟙 A) (0 : A ⟶ A)) ≫ cokernel.π (diag A) = 0,
  { rw [category.assoc, hx] },
  obtain ⟨y, hy⟩ := kernel_fork.is_limit.lift' hl _ hxx,
  rw kernel_fork.ι_of_ι at hy,
  have hyy : y = 0,
  { erw [←category.comp_id y, ←limits.prod.lift_snd (𝟙 A) (𝟙 A),  ←category.assoc, hy,
      category.assoc, prod.lift_snd, has_zero_morphisms.comp_zero] },
  haveI : mono (prod.lift (𝟙 A) (0 : A ⟶ A)) := mono_of_mono_fac (prod.lift_fst _ _),
  apply (cancel_mono (prod.lift (𝟙 A) (0 : A ⟶ A))).1,
  rw [←hy, hyy, zero_comp, zero_comp]
end

instance epi_r {A : C} : epi (r A) :=
begin
  have hlp : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ limits.prod.snd = 0 := prod.lift_snd _ _,
  let hp1 : is_limit (kernel_fork.of_ι (prod.lift (𝟙 A) (0 : A ⟶ A)) hlp),
  { refine fork.is_limit.mk _ (λ s, fork.ι s ≫ limits.prod.fst) _ _,
    { intro s,
      ext; simp, erw category.comp_id },
    { intros s m h,
      haveI : mono (prod.lift (𝟙 A) (0 : A ⟶ A)) := mono_of_mono_fac (prod.lift_fst _ _),
      apply (cancel_mono (prod.lift (𝟙 A) (0 : A ⟶ A))).1,
      convert h,
      ext; simp } },
  let hp2 : is_colimit (cokernel_cofork.of_π (limits.prod.snd : A ⨯ A ⟶ A) hlp),
  { exact epi_is_cokernel_of_kernel _ hp1 },
  apply normal_mono_category.epi_of_zero_cancel,
  intros Z z hz,
  have h : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ cokernel.π (diag A) ≫ z = 0,
  { rw [←category.assoc, hz] },
  obtain ⟨t, ht⟩ := cokernel_cofork.is_colimit.desc' hp2 _ h,
  rw cokernel_cofork.π_of_π at ht,
  have htt : t = 0,
  { rw [←category.id_comp t],
    change 𝟙 A ≫ t = 0,
    rw [←limits.prod.lift_snd (𝟙 A) (𝟙 A), category.assoc, ht, ←category.assoc,
      cokernel.condition, zero_comp] },
  apply (cancel_epi (cokernel.π (diag A))).1,
  rw [←ht, htt, comp_zero, comp_zero]
end

instance is_iso_r {A : C} : is_iso (r A) :=
is_iso_of_mono_of_epi _

/-- The composite `A ⨯ A ⟶ cokernel (diag A) ⟶ A` given by the natural projection into the cokernel
    followed by the inverse of `r`. In the category of modules, using the normal kernels and
    cokernels, this map is equal to the map `(a, b) ↦ a - b`, hence the name `σ` for
    "subtraction". -/
abbreviation σ {A : C} : A ⨯ A ⟶ A := cokernel.π (diag A) ≫ inv (r A)

end

@[simp, reassoc] lemma diag_σ {X : C} : diag X ≫ σ = 0 :=
by rw [cokernel.condition_assoc, zero_comp]

@[simp, reassoc] lemma lift_σ {X : C} : prod.lift (𝟙 X) 0 ≫ σ = 𝟙 X :=
by rw [←category.assoc, is_iso.hom_inv_id]

@[reassoc] lemma lift_map {X Y : C} (f : X ⟶ Y) :
  prod.lift (𝟙 X) 0 ≫ limits.prod.map f f = f ≫ prod.lift (𝟙 Y) 0 :=
by simp

/-- σ is a cokernel of Δ X. -/
def is_colimit_σ {X : C} : is_colimit (cokernel_cofork.of_π σ diag_σ) :=
cokernel.cokernel_iso _ σ (as_iso (r X)).symm (by rw [iso.symm_hom, as_iso_inv])

/-- This is the key identity satisfied by `σ`. -/
lemma σ_comp {X Y : C} (f : X ⟶ Y) : σ ≫ f = limits.prod.map f f ≫ σ :=
begin
  obtain ⟨g, hg⟩ :=
    cokernel_cofork.is_colimit.desc' is_colimit_σ (limits.prod.map f f ≫ σ) (by simp),
  suffices hfg : f = g,
  { rw [←hg, cofork.π_of_π, hfg] },
  calc f = f ≫ prod.lift (𝟙 Y) 0 ≫ σ : by rw [lift_σ, category.comp_id]
    ... = prod.lift (𝟙 X) 0 ≫ limits.prod.map f f ≫ σ : by rw lift_map_assoc
    ... = prod.lift (𝟙 X) 0 ≫ σ ≫ g : by rw [←hg, cokernel_cofork.π_of_π]
    ... = g : by rw [←category.assoc, lift_σ, category.id_comp]
end

section

/- We write `f - g` for `prod.lift f g ≫ σ`. -/
/-- Subtraction of morphisms in a `non_preadditive_abelian` category. -/
def has_sub {X Y : C} : has_sub (X ⟶ Y) := ⟨λ f g, prod.lift f g ≫ σ⟩
local attribute [instance] has_sub

/- We write `-f` for `0 - f`. -/
/-- Negation of morphisms in a `non_preadditive_abelian` category. -/
def has_neg {X Y : C} : has_neg (X ⟶ Y) := ⟨λ f, 0 - f⟩
local attribute [instance] has_neg

/- We write `f + g` for `f - (-g)`. -/
/-- Addition of morphisms in a `non_preadditive_abelian` category. -/
def has_add {X Y : C} : has_add (X ⟶ Y) := ⟨λ f g, f - (-g)⟩
local attribute [instance] has_add

lemma sub_def {X Y : C} (a b : X ⟶ Y) : a - b = prod.lift a b ≫ σ := rfl
lemma add_def {X Y : C} (a b : X ⟶ Y) : a + b = a - (-b) := rfl
lemma neg_def {X Y : C} (a : X ⟶ Y) : -a = 0 - a := rfl

lemma sub_zero {X Y : C} (a : X ⟶ Y) : a - 0 = a :=
begin
  rw sub_def,
  conv_lhs { congr, congr, rw ←category.comp_id a, skip, rw (show 0 = a ≫ (0 : Y ⟶ Y), by simp)},
  rw [← prod.comp_lift, category.assoc, lift_σ, category.comp_id]
end

lemma sub_self {X Y : C} (a : X ⟶ Y) : a - a = 0 :=
by rw [sub_def, ←category.comp_id a, ← prod.comp_lift, category.assoc, diag_σ, comp_zero]

lemma lift_sub_lift {X Y : C} (a b c d : X ⟶ Y) :
  prod.lift a b - prod.lift c d = prod.lift (a - c) (b - d) :=
begin
  simp only [sub_def],
  ext,
  { rw [category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_fst, prod.lift_fst, prod.lift_fst] },
  { rw [category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_snd, prod.lift_snd, prod.lift_snd] }
end

lemma sub_sub_sub {X Y : C} (a b c d : X ⟶ Y) : (a - c) - (b - d) = (a - b) - (c - d) :=
begin
  rw [sub_def, ←lift_sub_lift, sub_def, category.assoc, σ_comp, prod.lift_map_assoc], refl
end

lemma neg_sub {X Y : C} (a b : X ⟶ Y) : (-a) - b = (-b) - a :=
by conv_lhs { rw [neg_def, ←sub_zero b, sub_sub_sub, sub_zero, ←neg_def] }

lemma neg_neg {X Y : C} (a : X ⟶ Y) : -(-a) = a :=
begin
  rw [neg_def, neg_def],
  conv_lhs { congr, rw ←sub_self a },
  rw [sub_sub_sub, sub_zero, sub_self, sub_zero]
end

lemma add_comm {X Y : C} (a b : X ⟶ Y) : a + b = b + a :=
begin
  rw [add_def],
  conv_lhs { rw ←neg_neg a },
  rw [neg_def, neg_def, neg_def, sub_sub_sub],
  conv_lhs {congr, skip, rw [←neg_def, neg_sub] },
  rw [sub_sub_sub, add_def, ←neg_def, neg_neg b, neg_def]
end

lemma add_neg {X Y : C} (a b : X ⟶ Y) : a + (-b) = a - b :=
by rw [add_def, neg_neg]

lemma add_neg_self {X Y : C} (a : X ⟶ Y) : a + (-a) = 0 :=
by rw [add_neg, sub_self]

lemma neg_add_self {X Y : C} (a : X ⟶ Y) : (-a) + a = 0 :=
by rw [add_comm, add_neg_self]

lemma neg_sub' {X Y : C} (a b : X ⟶ Y) : -(a - b) = (-a) + b :=
begin
  rw [neg_def, neg_def],
  conv_lhs { rw ←sub_self (0 : X ⟶ Y) },
  rw [sub_sub_sub, add_def, neg_def]
end

lemma neg_add {X Y : C} (a b : X ⟶ Y) : -(a + b) = (-a) - b :=
by rw [add_def, neg_sub', add_neg]

lemma sub_add {X Y : C} (a b c : X ⟶ Y) : (a - b) + c = a - (b - c) :=
by rw [add_def, neg_def, sub_sub_sub, sub_zero]

lemma add_assoc {X Y : C} (a b c : X ⟶ Y) : (a + b) + c = a + (b + c) :=
begin
  conv_lhs { congr, rw add_def },
  rw [sub_add, ←add_neg, neg_sub', neg_neg]
end

lemma add_zero {X Y : C} (a : X ⟶ Y) : a + 0 = a :=
by rw [add_def, neg_def, sub_self, sub_zero]

lemma comp_sub {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g - h) = f ≫ g - f ≫ h :=
by rw [sub_def, ←category.assoc, prod.comp_lift, sub_def]

lemma sub_comp {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z) : (f - g) ≫ h = f ≫ h - g ≫ h :=
by rw [sub_def, category.assoc, σ_comp, ←category.assoc, prod.lift_map, sub_def]

lemma comp_add (X Y Z : C) (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h :=
by rw [add_def, comp_sub, neg_def, comp_sub, comp_zero, add_def, neg_def]

lemma add_comp (X Y Z : C) (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h :=
by rw [add_def, sub_comp, neg_def, sub_comp, zero_comp, add_def, neg_def]

/-- Every `non_preadditive_abelian` category is preadditive. -/
def preadditive : preadditive C :=
{ hom_group := λ X Y,
  { add := (+),
    add_assoc := add_assoc,
    zero := 0,
    zero_add := neg_neg,
    add_zero := add_zero,
    neg := λ f, -f,
    add_left_neg := neg_add_self,
    add_comm := add_comm },
  add_comp' := add_comp,
  comp_add' := comp_add }

end

end category_theory.non_preadditive_abelian
