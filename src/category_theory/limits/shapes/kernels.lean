/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.equalizers

/-!
# Kernels and cokernels

In a category with zero morphisms, the kernel of a morphism `f : X ⟶ Y` is just the equalizer of `f`
and `0 : X ⟶ Y`. (Similarly the cokernel is the coequalizer.)

We don't yet prove much here, just provide
* `kernel : (X ⟶ Y) → C`
* `kernel.ι : kernel f ⟶ X`
* `kernel.condition : kernel.ι f ≫ f = 0` and
* `kernel.lift (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f` (as well as the dual versions)

## Main statements

Besides the definition and lifts,
* `kernel.ι_zero_is_iso`: a kernel map of a zero morphism is an isomorphism
* `kernel.is_limit_cone_zero_cone`: if our category has a zero object, then the map from the zero
  obect is a kernel map of any monomorphism

## Future work
* TODO: images and coimages, and then abelian categories.
* TODO: connect this with existing working in the group theory and ring theory libraries.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

universes v u

open category_theory
open category_theory.limits.walking_parallel_pair

namespace category_theory.limits

variables {C : Type u} [category.{v} C]
variables [has_zero_morphisms C]

/-- A morphism `f` has a kernel if the functor `parallel_pair f 0` has a limit. -/
abbreviation has_kernel {X Y : C} (f : X ⟶ Y) : Type (max u v) := has_limit (parallel_pair f 0)
/-- A morphism `f` has a cokernel if the functor `parallel_pair f 0` has a colimit. -/
abbreviation has_cokernel {X Y : C} (f : X ⟶ Y) : Type (max u v) := has_colimit (parallel_pair f 0)

variables {X Y : C} (f : X ⟶ Y)

section

/-- A kernel fork is just a fork where the second morphism is a zero morphism. -/
abbreviation kernel_fork := fork f 0

variables {f}

@[simp, reassoc] lemma kernel_fork.condition (s : kernel_fork f) : fork.ι s ≫ f = 0 :=
by erw [fork.condition, has_zero_morphisms.comp_zero]

@[simp] lemma kernel_fork.app_one (s : kernel_fork f) : s.π.app one = 0 :=
by rw [←fork.app_zero_left, kernel_fork.condition]

/-- A morphism `ι` satisfying `ι ≫ f = 0` determines a kernel fork over `f`. -/
abbreviation kernel_fork.of_ι {Z : C} (ι : Z ⟶ X) (w : ι ≫ f = 0) : kernel_fork f :=
fork.of_ι ι $ by rw [w, has_zero_morphisms.comp_zero]

/-- If `s` is a limit kernel fork and `k : W ⟶ X` satisfies ``k ≫ f = 0`, then there is some
    `l : W ⟶ s.X` sich that `l ≫ fork.ι s = k`. -/
def kernel_fork.is_limit.lift' {s : kernel_fork f} (hs : is_limit s) {W : C} (k : W ⟶ X)
  (h : k ≫ f = 0) : {l : W ⟶ s.X // l ≫ fork.ι s = k} :=
⟨hs.lift $ kernel_fork.of_ι _ h, hs.fac _ _⟩

end

section
variables [has_kernel f]

/-- The kernel of a morphism, expressed as the equalizer with the 0 morphism. -/
abbreviation kernel : C := equalizer f 0

/-- The map from `kernel f` into the source of `f`. -/
abbreviation kernel.ι : kernel f ⟶ X := equalizer.ι f 0

@[simp, reassoc] lemma kernel.condition : kernel.ι f ≫ f = 0 :=
kernel_fork.condition _

/-- Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through `kernel.ι f`
    via `kernel.lift : W ⟶ kernel f`. -/
abbreviation kernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
limit.lift (parallel_pair f 0) (kernel_fork.of_ι k h)

@[simp, reassoc]
lemma kernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : kernel.lift f k h ≫ kernel.ι f = k :=
limit.lift_π _ _

/-- Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ kernel f` such that
    `l ≫ kernel.ι f = k`. -/
def kernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : {l : W ⟶ kernel f // l ≫ kernel.ι f = k} :=
⟨kernel.lift f k h, kernel.lift_ι _ _ _⟩

/-- Every kernel of the zero morphism is an isomorphism -/
def kernel.ι_zero_is_iso [has_kernel (0 : X ⟶ Y)] :
  is_iso (kernel.ι (0 : X ⟶ Y)) :=
equalizer.ι_of_self _

lemma eq_zero_of_epi_kernel [epi (kernel.ι f)] : f = 0 :=
(cancel_epi (kernel.ι f)).1 (by simp)

variables {f}

lemma kernel_not_epi_of_nonzero (w : f ≠ 0) : ¬epi (kernel.ι f) :=
λ I, by exactI w (eq_zero_of_epi_kernel f)

lemma kernel_not_iso_of_nonzero (w : f ≠ 0) : (is_iso (kernel.ι f)) → false :=
λ I, kernel_not_epi_of_nonzero w $ by { resetI, apply_instance }

end

section has_zero_object
variables [has_zero_object C]

local attribute [instance] has_zero_object.has_zero

/-- The morphism from the zero object determines a cone on a kernel diagram -/
def kernel.zero_cone : cone (parallel_pair f 0) :=
{ X := 0,
  π := { app := λ j, 0 }}

/-- The map from the zero object is a kernel of a monomorphism -/
def kernel.is_limit_cone_zero_cone [mono f] : is_limit (kernel.zero_cone f) :=
fork.is_limit.mk _ (λ s, 0)
  (λ s, by { erw has_zero_morphisms.zero_comp,
    convert (zero_of_comp_mono f _).symm,
    exact kernel_fork.condition _ })
  (λ _ _ _, has_zero_object.zero_of_to_zero _)

/-- The kernel of a monomorphism is isomorphic to the zero object -/
def kernel.of_mono [has_kernel f] [mono f] : kernel f ≅ 0 :=
functor.map_iso (cones.forget _) $ is_limit.unique_up_to_iso
  (limit.is_limit (parallel_pair f 0)) (kernel.is_limit_cone_zero_cone f)

/-- The kernel morphism of a monomorphism is a zero morphism -/
lemma kernel.ι_of_mono [has_kernel f] [mono f] : kernel.ι f = 0 :=
by rw [←category.id_comp (kernel.ι f), ←iso.hom_inv_id (kernel.of_mono f), category.assoc,
  has_zero_object.zero_of_to_zero (kernel.of_mono f).hom, has_zero_morphisms.zero_comp]

end has_zero_object

section transport

/-- If `i` is an isomorphism such that `l ≫ i.hom = f`, then any kernel of `f` is a kernel of `l`.-/
def is_kernel.of_comp_iso {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f)
  {s : kernel_fork f} (hs : is_limit s) : is_limit (kernel_fork.of_ι (fork.ι s) $
    show fork.ι s ≫ l = 0, by simp [←i.comp_inv_eq.2 h.symm]) :=
fork.is_limit.mk _
  (λ s, hs.lift $ kernel_fork.of_ι (fork.ι s) $ by simp [←h])
  (λ s, by simp)
  (λ s m h, by { apply fork.is_limit.hom_ext hs, simpa using h walking_parallel_pair.zero })

/-- If `i` is an isomorphism such that `l ≫ i.hom = f`, then the kernel of `f` is a kernel of `l`.-/
def kernel.of_comp_iso [has_kernel f]
  {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f) :
  is_limit (kernel_fork.of_ι (kernel.ι f) $
    show kernel.ι f ≫ l = 0, by simp [←i.comp_inv_eq.2 h.symm]) :=
is_kernel.of_comp_iso f l i h $ limit.is_limit _

/-- If `s` is any limit kernel cone over `f` and if  `i` is an isomorphism such that
    `i.hom ≫ s.ι  = l`, then `l` is a kernel of `f`. -/
def is_kernel.iso_kernel {Z : C} (l : Z ⟶ X) {s : kernel_fork f} (hs : is_limit s)
  (i : Z ≅ s.X) (h : i.hom ≫ fork.ι s = l) : is_limit (kernel_fork.of_ι l $
    show l ≫ f = 0, by simp [←h]) :=
is_limit.of_iso_limit hs $ cones.ext i.symm $ λ j,
  by { cases j, { exact (iso.eq_inv_comp i).2 h }, { simp } }

/-- If `i` is an isomorphism such that `i.hom ≫ kernel.ι f = l`, then `l` is a kernel of `f`. -/
def kernel.iso_kernel [has_kernel f]
  {Z : C} (l : Z ⟶ X) (i : Z ≅ kernel f) (h : i.hom ≫ kernel.ι f = l) :
  is_limit (kernel_fork.of_ι l $ by simp [←h]) :=
is_kernel.iso_kernel f l (limit.is_limit _) i h

end transport

section
variables (X Y)

/-- The kernel morphism of a zero morphism is an isomorphism -/
def kernel.ι_of_zero [has_kernel (0 : X ⟶ Y)] : is_iso (kernel.ι (0 : X ⟶ Y)) :=
equalizer.ι_of_self _

end

section

/-- A cokernel cofork is just a cofork where the second morphism is a zero morphism. -/
abbreviation cokernel_cofork := cofork f 0

variables {f}

@[simp, reassoc] lemma cokernel_cofork.condition (s : cokernel_cofork f) : f ≫ cofork.π s = 0 :=
by rw [cofork.condition, has_zero_morphisms.zero_comp]

@[simp] lemma cokernel_cofork.app_zero (s : cokernel_cofork f) : s.ι.app zero = 0 :=
by rw [←cofork.left_app_one, cokernel_cofork.condition]

/-- A morphism `π` satisfying `f ≫ π = 0` determines a cokernel cofork on `f`. -/
abbreviation cokernel_cofork.of_π {Z : C} (π : Y ⟶ Z) (w : f ≫ π = 0) : cokernel_cofork f :=
cofork.of_π π $ by rw [w, has_zero_morphisms.zero_comp]

/-- If `s` is a colimit cokernel cofork, then every `k : Y ⟶ W` satisfying `f ≫ k = 0` induces
    `l : s.X ⟶ W` such that `cofork.π s ≫ l = k`. -/
def cokernel_cofork.is_colimit.desc' {s : cokernel_cofork f} (hs : is_colimit s) {W : C} (k : Y ⟶ W)
  (h : f ≫ k = 0) : {l : s.X ⟶ W // cofork.π s ≫ l = k} :=
⟨hs.desc $ cokernel_cofork.of_π _ h, hs.fac _ _⟩

end

section
variables [has_cokernel f]

/-- The cokernel of a morphism, expressed as the coequalizer with the 0 morphism. -/
abbreviation cokernel : C := coequalizer f 0

/-- The map from the target of `f` to `cokernel f`. -/
abbreviation cokernel.π : Y ⟶ cokernel f := coequalizer.π f 0

@[simp, reassoc] lemma cokernel.condition : f ≫ cokernel.π f = 0 :=
cokernel_cofork.condition _

/-- Given any morphism `k : Y ⟶ W` such that `f ≫ k = 0`, `k` factors through `cokernel.π f`
    via `cokernel.desc : cokernel f ⟶ W`. -/
abbreviation cokernel.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel f ⟶ W :=
colimit.desc (parallel_pair f 0) (cokernel_cofork.of_π k h)

@[simp, reassoc]
lemma cokernel.π_desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
  cokernel.π f ≫ cokernel.desc f k h = k :=
colimit.ι_desc _ _

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = 0` induces `l : cokernel f ⟶ W` such that
    `cokernel.π f ≫ l = k`. -/
def cokernel.desc' {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
  {l : cokernel f ⟶ W // cokernel.π f ≫ l = k} :=
⟨cokernel.desc f k h, cokernel.π_desc _ _ _⟩

/-- The cokernel of the zero morphism is an isomorphism -/
def cokernel.π_zero_is_iso [has_colimit (parallel_pair (0 : X ⟶ Y) 0)] :
  is_iso (cokernel.π (0 : X ⟶ Y)) :=
coequalizer.π_of_self _

lemma eq_zero_of_mono_cokernel [mono (cokernel.π f)] : f = 0 :=
(cancel_mono (cokernel.π f)).1 (by simp)

variables {f}

lemma cokernel_not_mono_of_nonzero (w : f ≠ 0) : ¬mono (cokernel.π f) :=
λ I, by exactI w (eq_zero_of_mono_cokernel f)

lemma cokernel_not_iso_of_nonzero (w : f ≠ 0) : (is_iso (cokernel.π f)) → false :=
λ I, cokernel_not_mono_of_nonzero w $ by { resetI, apply_instance }

end

section has_zero_object
variables [has_zero_object C]

local attribute [instance] has_zero_object.has_zero

/-- The morphism to the zero object determines a cocone on a cokernel diagram -/
def cokernel.zero_cocone : cocone (parallel_pair f 0) :=
{ X := 0,
  ι := { app := λ j, 0 } }

/-- The morphism to the zero object is a cokernel of an epimorphism -/
def cokernel.is_colimit_cocone_zero_cocone [epi f] : is_colimit (cokernel.zero_cocone f) :=
cofork.is_colimit.mk _ (λ s, 0)
  (λ s, by { erw has_zero_morphisms.zero_comp,
    convert (zero_of_epi_comp f _).symm,
    exact cokernel_cofork.condition _ })
  (λ _ _ _, has_zero_object.zero_of_from_zero _)

/-- The cokernel of an epimorphism is isomorphic to the zero object -/
def cokernel.of_epi [has_cokernel f] [epi f] : cokernel f ≅ 0 :=
functor.map_iso (cocones.forget _) $ is_colimit.unique_up_to_iso
  (colimit.is_colimit (parallel_pair f 0)) (cokernel.is_colimit_cocone_zero_cocone f)

/-- The cokernel morphism if an epimorphism is a zero morphism -/
lemma cokernel.π_of_epi [has_cokernel f] [epi f] : cokernel.π f = 0 :=
by rw [←category.comp_id (cokernel.π f), ←iso.hom_inv_id (cokernel.of_epi f), ←category.assoc,
  has_zero_object.zero_of_from_zero (cokernel.of_epi f).inv, has_zero_morphisms.comp_zero]

end has_zero_object

section
variables (X Y)

/-- The cokernel of a zero morphism is an isomorphism -/
def cokernel.π_of_zero [has_cokernel (0 : X ⟶ Y)] :
  is_iso (cokernel.π (0 : X ⟶ Y)) :=
coequalizer.π_of_self _

end


section has_zero_object
variables [has_zero_object C]

local attribute [instance] has_zero_object.has_zero

/-- The kernel of the cokernel of an epimorphism is an isomorphism -/
instance kernel.of_cokernel_of_epi [has_cokernel f]
  [has_kernel (cokernel.π f)] [epi f] : is_iso (kernel.ι (cokernel.π f)) :=
equalizer.ι_of_eq $ cokernel.π_of_epi f

/-- The cokernel of the kernel of a monomorphism is an isomorphism -/
instance cokernel.of_kernel_of_mono [has_kernel f]
  [has_cokernel (kernel.ι f)] [mono f] : is_iso (cokernel.π (kernel.ι f)) :=
coequalizer.π_of_eq $ kernel.ι_of_mono f

end has_zero_object

section transport

/-- If `i` is an isomorphism such that `i.hom ≫ l = f`, then any cokernel of `f` is a cokernel of
    `l`. -/
def is_cokernel.of_iso_comp {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f)
  {s : cokernel_cofork f} (hs : is_colimit s) : is_colimit (cokernel_cofork.of_π (cofork.π s) $
    show l ≫ cofork.π s = 0, by simp [i.eq_inv_comp.2 h]) :=
cofork.is_colimit.mk _
  (λ s, hs.desc $ cokernel_cofork.of_π (cofork.π s) $ by simp [←h])
  (λ s, by simp)
  (λ s m h, by { apply cofork.is_colimit.hom_ext hs, simpa using h walking_parallel_pair.one })

/-- If `i` is an isomorphism such that `i.hom ≫ l = f`, then the cokernel of `f` is a cokernel of
    `l`. -/
def cokernel.of_iso_comp [has_cokernel f]
  {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) :
  is_colimit (cokernel_cofork.of_π (cokernel.π f) $
    show l ≫ cokernel.π f = 0, by simp [i.eq_inv_comp.2 h]) :=
is_cokernel.of_iso_comp f l i h $ colimit.is_colimit _

/-- If `s` is any colimit cokernel cocone over `f` and `i` is an isomorphism such that
    `s.π ≫ i.hom = l`, then `l` is a cokernel of `f`. -/
def is_cokernel.cokernel_iso {Z : C} (l : Y ⟶ Z) {s : cokernel_cofork f} (hs : is_colimit s)
  (i : s.X ≅ Z) (h : cofork.π s ≫ i.hom = l) : is_colimit (cokernel_cofork.of_π l $
    show f ≫ l = 0, by simp [←h]) :=
is_colimit.of_iso_colimit hs $ cocones.ext i $ λ j, by { cases j, { simp }, { exact h } }

/-- If `i` is an isomorphism such that `cokernel.π f ≫ i.hom = l`, then `l` is a cokernel of `f`. -/
def cokernel.cokernel_iso [has_cokernel f]
  {Z : C} (l : Y ⟶ Z) (i : cokernel f ≅ Z) (h : cokernel.π f ≫ i.hom = l) :
  is_colimit (cokernel_cofork.of_π l $ by simp [←h]) :=
is_cokernel.cokernel_iso f l (colimit.is_colimit _) i h

end transport

end category_theory.limits

namespace category_theory.limits
variables (C : Type u) [category.{v} C]

variables [has_zero_morphisms C]

/-- `has_kernels` represents a choice of kernel for every morphism -/
class has_kernels :=
(has_limit : Π {X Y : C} (f : X ⟶ Y), has_kernel f)

/-- `has_cokernels` represents a choice of cokernel for every morphism -/
class has_cokernels :=
(has_colimit : Π {X Y : C} (f : X ⟶ Y), has_cokernel f)

attribute [instance, priority 100] has_kernels.has_limit has_cokernels.has_colimit

/-- Kernels are finite limits, so if `C` has all finite limits, it also has all kernels -/
def has_kernels_of_has_finite_limits [has_finite_limits C] : has_kernels C :=
{ has_limit := infer_instance }

/-- Cokernels are finite limits, so if `C` has all finite colimits, it also has all cokernels -/
def has_cokernels_of_has_finite_colimits [has_finite_colimits C] : has_cokernels C :=
{ has_colimit := infer_instance }

end category_theory.limits
