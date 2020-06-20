/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.strong_epi

/-!
# Definitions and basic properties of regular and normal monomorphisms and epimorphisms.

A regular monomorphism is a morphism that is the equalizer of some parallel pair.
A normal monomorphism is a morphism that is the kernel of some other morphism.

We give the constructions
* `split_mono → regular_mono`
* `normal_mono → regular_mono`, and
* `regular_mono → mono`
as well as the dual constructions for regular and normal epimorphisms. Additionally, we give the
construction
* `regular_epi ⟶ strong_epi`.

-/

namespace category_theory
open category_theory.limits

universes v₁ u₁

variables {C : Type u₁} [category.{v₁} C]

variables {X Y : C}

/-- A regular monomorphism is a morphism which is the equalizer of some parallel pair. -/
class regular_mono (f : X ⟶ Y) :=
(Z : C)
(left right : Y ⟶ Z)
(w : f ≫ left = f ≫ right)
(is_limit : is_limit (fork.of_ι f w))

attribute [reassoc] regular_mono.w

/-- Every regular monomorphism is a monomorphism. -/
@[priority 100]
instance regular_mono.mono (f : X ⟶ Y) [regular_mono f] : mono f :=
mono_of_is_limit_parallel_pair regular_mono.is_limit

instance equalizer_regular (g h : X ⟶ Y) [has_limit (parallel_pair g h)] :
  regular_mono (equalizer.ι g h) :=
{ Z := Y,
  left := g,
  right := h,
  w := equalizer.condition g h,
  is_limit := fork.is_limit.mk _ (λ s, limit.lift _ s) (by simp) (λ s m w, by { ext1, simp [←w] }) }

/-- Every split monomorphism is a regular monomorphism. -/
@[priority 100]
instance regular_mono.of_split_mono (f : X ⟶ Y) [split_mono f] : regular_mono f :=
{ Z     := Y,
  left  := 𝟙 Y,
  right := retraction f ≫ f,
  w     := by tidy,
  is_limit := split_mono_equalizes f }

/-- If `f` is a regular mono, then any map `k : W ⟶ Y` equalizing `regular_mono.left` and
    `regular_mono.right` induces a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def regular_mono.lift' {W : C} (f : X ⟶ Y) [regular_mono f] (k : W ⟶ Y)
  (h : k ≫ (regular_mono.left : Y ⟶ @regular_mono.Z _ _ _ _ f _) = k ≫ regular_mono.right) :
  {l : W ⟶ X // l ≫ f = k} :=
fork.is_limit.lift' regular_mono.is_limit _ h

/-- A regular monomorphism is an isomorphism if it is an epimorphism. -/
def is_iso_of_regular_mono_of_epi (f : X ⟶ Y) [regular_mono f] [e : epi f] : is_iso f :=
@is_iso_limit_cone_parallel_pair_of_epi _ _ _ _ _ _ _ regular_mono.is_limit e

section
variables [has_zero_morphisms.{v₁} C]
/-- A normal monomorphism is a morphism which is the kernel of some morphism. -/
class normal_mono (f : X ⟶ Y) :=
(Z : C)
(g : Y ⟶ Z)
(w : f ≫ g = 0)
(is_limit : is_limit (kernel_fork.of_ι f w))

/-- Every normal monomorphism is a regular monomorphism. -/
@[priority 100]
instance normal_mono.regular_mono (f : X ⟶ Y) [I : normal_mono f] : regular_mono f :=
{ left := I.g,
  right := 0,
  w := (by simpa using I.w),
  ..I }

/-- If `f` is a normal mono, then any map `k : W ⟶ Y` such that `k ≫ normal_mono.g = 0` induces
    a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def normal_mono.lift' {W : C} (f : X ⟶ Y) [normal_mono f] (k : W ⟶ Y) (h : k ≫ normal_mono.g = 0) :
  {l : W ⟶ X // l ≫ f = k} :=
kernel_fork.is_limit.lift' normal_mono.is_limit _ h

end
/-- A regular epimorphism is a morphism which is the coequalizer of some parallel pair. -/
class regular_epi (f : X ⟶ Y) :=
(W : C)
(left right : W ⟶ X)
(w : left ≫ f = right ≫ f)
(is_colimit : is_colimit (cofork.of_π f w))

attribute [reassoc] regular_epi.w

/-- Every regular epimorphism is an epimorphism. -/
@[priority 100]
instance regular_epi.epi (f : X ⟶ Y) [regular_epi f] : epi f :=
epi_of_is_colimit_parallel_pair regular_epi.is_colimit

instance coequalizer_regular (g h : X ⟶ Y) [has_colimit (parallel_pair g h)] :
  regular_epi (coequalizer.π g h) :=
{ W := X,
  left := g,
  right := h,
  w := coequalizer.condition g h,
  is_colimit := cofork.is_colimit.mk _ (λ s, colimit.desc _ s) (by simp) (λ s m w, by { ext1, simp [←w] }) }

/-- Every split epimorphism is a regular epimorphism. -/
@[priority 100]
instance regular_epi.of_split_epi (f : X ⟶ Y) [split_epi f] : regular_epi f :=
{ W     := X,
  left  := 𝟙 X,
  right := f ≫ section_ f,
  w     := by tidy,
  is_colimit := split_epi_coequalizes f }

/-- If `f` is a regular epi, then every morphism `k : X ⟶ W` coequalizing `regular_epi.left` and
    `regular_epi.right` induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def regular_epi.desc' {W : C} (f : X ⟶ Y) [regular_epi f] (k : X ⟶ W)
  (h : (regular_epi.left : regular_epi.W f ⟶ X) ≫ k = regular_epi.right ≫ k) :
  {l : Y ⟶ W // f ≫ l = k} :=
cofork.is_colimit.desc' (regular_epi.is_colimit) _ h

/-- A regular epimorphism is an isomorphism if it is a monomorphism. -/
def is_iso_of_regular_epi_of_mono (f : X ⟶ Y) [regular_epi f] [m : mono f] : is_iso f :=
@is_iso_limit_cocone_parallel_pair_of_epi _ _ _ _ _ _ _ regular_epi.is_colimit m

@[priority 100]
instance strong_epi_of_regular_epi (f : X ⟶ Y) [regular_epi f] : strong_epi f :=
{ epi := by apply_instance,
  has_lift :=
  begin
    introsI,
    have : (regular_epi.left : regular_epi.W f ⟶ X) ≫ u = regular_epi.right ≫ u,
    { apply (cancel_mono z).1,
      simp only [category.assoc, h, regular_epi.w_assoc] },
    obtain ⟨t, ht⟩ := regular_epi.desc' f u this,
    exact ⟨t, ht, (cancel_epi f).1
      (by simp only [←category.assoc, ht, ←h, arrow.mk_hom, arrow.hom_mk'_right])⟩,
  end }

section
variables [has_zero_morphisms.{v₁} C]
/-- A normal epimorphism is a morphism which is the cokernel of some morphism. -/
class normal_epi (f : X ⟶ Y) :=
(W : C)
(g : W ⟶ X)
(w : g ≫ f = 0)
(is_colimit : is_colimit (cokernel_cofork.of_π f w))

/-- Every normal epimorphism is a regular epimorphism. -/
@[priority 100]
instance normal_epi.regular_epi (f : X ⟶ Y) [I : normal_epi f] : regular_epi f :=
{ left := I.g,
  right := 0,
  w := (by simpa using I.w),
  ..I }

/-- If `f` is a normal epi, then every morphism `k : X ⟶ W` satisfying `normal_epi.g ≫ k = 0`
    induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def normal_epi.desc' {W : C} (f : X ⟶ Y) [normal_epi f] (k : X ⟶ W) (h : normal_epi.g ≫ k = 0) :
  {l : Y ⟶ W // f ≫ l = k} :=
cokernel_cofork.is_colimit.desc' (normal_epi.is_colimit) _ h

end

end category_theory
