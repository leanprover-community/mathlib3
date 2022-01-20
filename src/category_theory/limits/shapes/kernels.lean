/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import category_theory.limits.shapes.zero

/-!
# Kernels and cokernels

In a category with zero morphisms, the kernel of a morphism `f : X ⟶ Y` is
the equalizer of `f` and `0 : X ⟶ Y`. (Similarly the cokernel is the coequalizer.)

The basic definitions are
* `kernel : (X ⟶ Y) → C`
* `kernel.ι : kernel f ⟶ X`
* `kernel.condition : kernel.ι f ≫ f = 0` and
* `kernel.lift (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f` (as well as the dual versions)

## Main statements

Besides the definition and lifts, we prove
* `kernel.ι_zero_is_iso`: a kernel map of a zero morphism is an isomorphism
* `kernel.eq_zero_of_epi_kernel`: if `kernel.ι f` is an epimorphism, then `f = 0`
* `kernel.of_mono`: the kernel of a monomorphism is the zero object
* `kernel.lift_mono`: the lift of a monomorphism `k : W ⟶ X` such that `k ≫ f = 0`
  is still a monomorphism
* `kernel.is_limit_cone_zero_cone`: if our category has a zero object, then the map from the zero
  obect is a kernel map of any monomorphism
* `kernel.ι_of_zero`: `kernel.ι (0 : X ⟶ Y)` is an isomorphism

and the corresponding dual statements.

## Future work
* TODO: connect this with existing working in the group theory and ring theory libraries.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

noncomputable theory

universes v u u'

open category_theory
open category_theory.limits.walking_parallel_pair

namespace category_theory.limits

variables {C : Type u} [category.{v} C]
variables [has_zero_morphisms C]

/-- A morphism `f` has a kernel if the functor `parallel_pair f 0` has a limit. -/
abbreviation has_kernel {X Y : C} (f : X ⟶ Y) : Prop := has_limit (parallel_pair f 0)
/-- A morphism `f` has a cokernel if the functor `parallel_pair f 0` has a colimit. -/
abbreviation has_cokernel {X Y : C} (f : X ⟶ Y) : Prop := has_colimit (parallel_pair f 0)

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

@[simp] lemma kernel_fork.ι_of_ι {X Y P : C} (f : X ⟶ Y) (ι : P ⟶ X) (w : ι ≫ f = 0) :
  fork.ι (kernel_fork.of_ι ι w) = ι := rfl

section
local attribute [tidy] tactic.case_bash

/-- Every kernel fork `s` is isomorphic (actually, equal) to `fork.of_ι (fork.ι s) _`. -/
def iso_of_ι (s : fork f 0) : s ≅ fork.of_ι (fork.ι s) (fork.condition s) :=
cones.ext (iso.refl _) $ by tidy

/-- If `ι = ι'`, then `fork.of_ι ι _` and `fork.of_ι ι' _` are isomorphic. -/
def of_ι_congr {P : C} {ι ι' : P ⟶ X} {w : ι ≫ f = 0} (h : ι = ι') :
  kernel_fork.of_ι ι w ≅ kernel_fork.of_ι ι' (by rw [←h, w]) :=
cones.ext (iso.refl _) $ by tidy

/-- If `F` is an equivalence, then applying `F` to a diagram indexing a (co)kernel of `f` yields
    the diagram indexing the (co)kernel of `F.map f`. -/
def comp_nat_iso {D : Type u'} [category.{v} D] [has_zero_morphisms D] (F : C ⥤ D)
  [is_equivalence F] : parallel_pair f 0 ⋙ F ≅ parallel_pair (F.map f) 0 :=
nat_iso.of_components (λ j, match j with
  | zero := iso.refl _
  | one := iso.refl _
  end) $ by tidy

end

/-- If `s` is a limit kernel fork and `k : W ⟶ X` satisfies ``k ≫ f = 0`, then there is some
    `l : W ⟶ s.X` such that `l ≫ fork.ι s = k`. -/
def kernel_fork.is_limit.lift' {s : kernel_fork f} (hs : is_limit s) {W : C} (k : W ⟶ X)
  (h : k ≫ f = 0) : {l : W ⟶ s.X // l ≫ fork.ι s = k} :=
⟨hs.lift $ kernel_fork.of_ι _ h, hs.fac _ _⟩

/-- This is a slightly more convenient method to verify that a kernel fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def is_limit_aux (t : kernel_fork f)
  (lift : Π (s : kernel_fork f), s.X ⟶ t.X)
  (fac : ∀ (s : kernel_fork f), lift s ≫ t.ι = s.ι)
  (uniq : ∀ (s : kernel_fork f) (m : s.X ⟶ t.X) (w : m ≫ t.ι = s.ι), m = lift s) :
  is_limit t :=
{ lift := lift,
  fac' := λ s j, by { cases j, { exact fac s, }, { simp, }, },
  uniq' := λ s m w, uniq s m (w limits.walking_parallel_pair.zero), }

/--
This is a more convenient formulation to show that a `kernel_fork` constructed using
`kernel_fork.of_ι` is a limit cone.
-/
def is_limit.of_ι {W : C} (g : W ⟶ X) (eq : g ≫ f = 0)
  (lift : Π {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0), W' ⟶ W)
  (fac : ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0), lift g' eq' ≫ g = g')
  (uniq :
    ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0) (m : W' ⟶ W) (w : m ≫ g = g'), m = lift g' eq') :
  is_limit (kernel_fork.of_ι g eq) :=
is_limit_aux _ (λ s, lift s.ι s.condition) (λ s, fac s.ι s.condition) (λ s, uniq s.ι s.condition)

end

section
variables [has_kernel f]

/-- The kernel of a morphism, expressed as the equalizer with the 0 morphism. -/
abbreviation kernel : C := equalizer f 0

/-- The map from `kernel f` into the source of `f`. -/
abbreviation kernel.ι : kernel f ⟶ X := equalizer.ι f 0

@[simp] lemma equalizer_as_kernel : equalizer.ι f 0 = kernel.ι f := rfl

@[simp, reassoc] lemma kernel.condition : kernel.ι f ≫ f = 0 :=
kernel_fork.condition _

/-- Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through `kernel.ι f`
    via `kernel.lift : W ⟶ kernel f`. -/
abbreviation kernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
limit.lift (parallel_pair f 0) (kernel_fork.of_ι k h)

@[simp, reassoc]
lemma kernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : kernel.lift f k h ≫ kernel.ι f = k :=
limit.lift_π _ _

@[simp]
lemma kernel.lift_zero {W : C} {h} : kernel.lift f (0 : W ⟶ X) h = 0 :=
by { ext, simp, }

instance kernel.lift_mono {W : C} (k : W ⟶ X) (h : k ≫ f = 0) [mono k] : mono (kernel.lift f k h) :=
⟨λ Z g g' w,
begin
  replace w := w =≫ kernel.ι f,
  simp only [category.assoc, kernel.lift_ι] at w,
  exact (cancel_mono k).1 w,
end⟩

/-- Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ kernel f` such that
    `l ≫ kernel.ι f = k`. -/
def kernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : {l : W ⟶ kernel f // l ≫ kernel.ι f = k} :=
⟨kernel.lift f k h, kernel.lift_ι _ _ _⟩

/-- A commuting square induces a morphism of kernels. -/
abbreviation kernel.map {X' Y' : C} (f' : X' ⟶ Y') [has_kernel f']
  (p : X ⟶ X') (q : Y ⟶ Y') (w : f ≫ q = p ≫ f') : kernel f ⟶ kernel f' :=
kernel.lift f' (kernel.ι f ≫ p) (by simp [←w])

/--
Given a commutative diagram
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
with horizontal arrows composing to zero,
then we obtain a commutative square
   X ---> kernel g
   |         |
   |         | kernel.map
   |         |
   v         v
   X' --> kernel g'
-/
lemma kernel.lift_map {X Y Z X' Y' Z' : C}
  (f : X ⟶ Y) (g : Y ⟶ Z) [has_kernel g] (w : f ≫ g = 0)
  (f' : X' ⟶ Y') (g' : Y' ⟶ Z') [has_kernel g'] (w' : f' ≫ g' = 0)
  (p : X ⟶ X') (q : Y ⟶ Y') (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
  kernel.lift g f w ≫ kernel.map g g' q r h₂ = p ≫ kernel.lift g' f' w' :=
by { ext, simp [h₁], }

/-- Every kernel of the zero morphism is an isomorphism -/
instance kernel.ι_zero_is_iso : is_iso (kernel.ι (0 : X ⟶ Y)) :=
equalizer.ι_of_self _

lemma eq_zero_of_epi_kernel [epi (kernel.ι f)] : f = 0 :=
(cancel_epi (kernel.ι f)).1 (by simp)

/-- The kernel of a zero morphism is isomorphic to the source. -/
def kernel_zero_iso_source : kernel (0 : X ⟶ Y) ≅ X :=
equalizer.iso_source_of_self 0

@[simp] lemma kernel_zero_iso_source_hom :
  kernel_zero_iso_source.hom = kernel.ι (0 : X ⟶ Y) := rfl

@[simp] lemma kernel_zero_iso_source_inv :
  kernel_zero_iso_source.inv = kernel.lift (0 : X ⟶ Y) (𝟙 X) (by simp) :=
by { ext, simp [kernel_zero_iso_source], }

/-- If two morphisms are known to be equal, then their kernels are isomorphic. -/
def kernel_iso_of_eq {f g : X ⟶ Y} [has_kernel f] [has_kernel g] (h : f = g) :
  kernel f ≅ kernel g :=
has_limit.iso_of_nat_iso (by simp[h])

@[simp]
lemma kernel_iso_of_eq_refl {h : f = f} : kernel_iso_of_eq h = iso.refl (kernel f) :=
by { ext, simp [kernel_iso_of_eq], }

@[simp]
lemma kernel_iso_of_eq_trans {f g h : X ⟶ Y} [has_kernel f] [has_kernel g] [has_kernel h]
  (w₁ : f = g) (w₂ : g = h) :
  kernel_iso_of_eq w₁ ≪≫ kernel_iso_of_eq w₂ = kernel_iso_of_eq (w₁.trans w₂) :=
by { unfreezingI { induction w₁, induction w₂, }, ext, simp [kernel_iso_of_eq], }

variables {f}

lemma kernel_not_epi_of_nonzero (w : f ≠ 0) : ¬epi (kernel.ι f) :=
λ I, by exactI w (eq_zero_of_epi_kernel f)

lemma kernel_not_iso_of_nonzero (w : f ≠ 0) : (is_iso (kernel.ι f)) → false :=
λ I, kernel_not_epi_of_nonzero w $ by { resetI, apply_instance }

-- TODO the remainder of this section has obvious generalizations to `has_equalizer f g`.

instance has_kernel_comp_mono {X Y Z : C} (f : X ⟶ Y) [has_kernel f] (g : Y ⟶ Z) [mono g] :
  has_kernel (f ≫ g) :=
{ exists_limit :=
  ⟨{ cone := kernel_fork.of_ι (kernel.ι f) (by simp),
     is_limit := is_limit_aux _ (λ s, kernel.lift _ s.ι ((cancel_mono g).mp (by simp)))
      (by tidy) (by tidy) }⟩ }

/--
When `g` is a monomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `f`.
-/
@[simps]
def kernel_comp_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_kernel f] [mono g] :
  kernel (f ≫ g) ≅ kernel f :=
{ hom := kernel.lift _ (kernel.ι _) (by { rw [←cancel_mono g], simp, }),
  inv := kernel.lift _ (kernel.ι _) (by simp), }

instance has_kernel_iso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso f] [has_kernel g] :
  has_kernel (f ≫ g) :=
{ exists_limit :=
  ⟨{ cone := kernel_fork.of_ι (kernel.ι g ≫ inv f) (by simp),
     is_limit := is_limit_aux _ (λ s, kernel.lift _ (s.ι ≫ f) (by tidy)) (by tidy)
       (λ s m w, by { simp_rw [←w], ext, simp, }), }⟩ }

/--
When `f` is an isomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `g`.
-/
@[simps]
def kernel_is_iso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso f] [has_kernel g] :
  kernel (f ≫ g) ≅ kernel g :=
{ hom := kernel.lift _ (kernel.ι _ ≫ f) (by simp),
  inv := kernel.lift _ (kernel.ι _ ≫ inv f) (by simp), }

end

section has_zero_object
variables [has_zero_object C]

open_locale zero_object

/-- The morphism from the zero object determines a cone on a kernel diagram -/
def kernel.zero_cone : cone (parallel_pair f 0) :=
{ X := 0,
  π := { app := λ j, 0 }}

/-- The map from the zero object is a kernel of a monomorphism -/
def kernel.is_limit_cone_zero_cone [mono f] : is_limit (kernel.zero_cone f) :=
fork.is_limit.mk _ (λ s, 0)
  (λ s, by { erw zero_comp,
    convert (zero_of_comp_mono f _).symm,
    exact kernel_fork.condition _ })
  (λ _ _ _, zero_of_to_zero _)

/-- The kernel of a monomorphism is isomorphic to the zero object -/
def kernel.of_mono [has_kernel f] [mono f] : kernel f ≅ 0 :=
functor.map_iso (cones.forget _) $ is_limit.unique_up_to_iso
  (limit.is_limit (parallel_pair f 0)) (kernel.is_limit_cone_zero_cone f)

/-- The kernel morphism of a monomorphism is a zero morphism -/
lemma kernel.ι_of_mono [has_kernel f] [mono f] : kernel.ι f = 0 :=
zero_of_source_iso_zero _ (kernel.of_mono f)

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
lemma kernel.ι_of_zero : is_iso (kernel.ι (0 : X ⟶ Y)) :=
equalizer.ι_of_self _

end

section

/-- A cokernel cofork is just a cofork where the second morphism is a zero morphism. -/
abbreviation cokernel_cofork := cofork f 0

variables {f}

@[simp, reassoc] lemma cokernel_cofork.condition (s : cokernel_cofork f) : f ≫ cofork.π s = 0 :=
by rw [cofork.condition, zero_comp]

@[simp] lemma cokernel_cofork.app_zero (s : cokernel_cofork f) : s.ι.app zero = 0 :=
by rw [←cofork.left_app_one, cokernel_cofork.condition]

/-- A morphism `π` satisfying `f ≫ π = 0` determines a cokernel cofork on `f`. -/
abbreviation cokernel_cofork.of_π {Z : C} (π : Y ⟶ Z) (w : f ≫ π = 0) : cokernel_cofork f :=
cofork.of_π π $ by rw [w, zero_comp]

@[simp] lemma cokernel_cofork.π_of_π {X Y P : C} (f : X ⟶ Y) (π : Y ⟶ P) (w : f ≫ π = 0) :
  cofork.π (cokernel_cofork.of_π π w) = π := rfl

/-- Every cokernel cofork `s` is isomorphic (actually, equal) to `cofork.of_π (cofork.π s) _`. -/
def iso_of_π (s : cofork f 0) : s ≅ cofork.of_π (cofork.π s) (cofork.condition s) :=
cocones.ext (iso.refl _) $ λ j, by cases j; tidy

/-- If `π = π'`, then `cokernel_cofork.of_π π _` and `cokernel_cofork.of_π π' _` are isomorphic. -/
def of_π_congr {P : C} {π π' : Y ⟶ P} {w : f ≫ π = 0} (h : π = π') :
  cokernel_cofork.of_π π w ≅ cokernel_cofork.of_π π' (by rw [←h, w]) :=
cocones.ext (iso.refl _) $ λ j, by cases j; tidy

/-- If `s` is a colimit cokernel cofork, then every `k : Y ⟶ W` satisfying `f ≫ k = 0` induces
    `l : s.X ⟶ W` such that `cofork.π s ≫ l = k`. -/
def cokernel_cofork.is_colimit.desc' {s : cokernel_cofork f} (hs : is_colimit s) {W : C} (k : Y ⟶ W)
  (h : f ≫ k = 0) : {l : s.X ⟶ W // cofork.π s ≫ l = k} :=
⟨hs.desc $ cokernel_cofork.of_π _ h, hs.fac _ _⟩

/--
This is a slightly more convenient method to verify that a cokernel cofork is a colimit cocone.
It only asks for a proof of facts that carry any mathematical content -/
def is_colimit_aux (t : cokernel_cofork f)
  (desc : Π (s : cokernel_cofork f), t.X ⟶ s.X)
  (fac : ∀ (s : cokernel_cofork f), t.π ≫ desc s = s.π)
  (uniq : ∀ (s : cokernel_cofork f) (m : t.X ⟶ s.X) (w : t.π ≫ m = s.π), m = desc s) :
  is_colimit t :=
{ desc := desc,
  fac' := λ s j, by { cases j, { simp, }, { exact fac s, }, },
  uniq' := λ s m w, uniq s m (w limits.walking_parallel_pair.one), }

/--
This is a more convenient formulation to show that a `cokernel_cofork` constructed using
`cokernel_cofork.of_π` is a limit cone.
-/
def is_colimit.of_π {Z : C} (g : Y ⟶ Z) (eq : f ≫ g = 0)
  (desc : Π {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0), Z ⟶ Z')
  (fac : ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0), g ≫ desc g' eq' = g')
  (uniq :
    ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0) (m : Z ⟶ Z') (w : g ≫ m = g'), m = desc g' eq') :
  is_colimit (cokernel_cofork.of_π g eq) :=
is_colimit_aux _ (λ s, desc s.π s.condition) (λ s, fac s.π s.condition) (λ s, uniq s.π s.condition)

end

section
variables [has_cokernel f]

/-- The cokernel of a morphism, expressed as the coequalizer with the 0 morphism. -/
abbreviation cokernel : C := coequalizer f 0

/-- The map from the target of `f` to `cokernel f`. -/
abbreviation cokernel.π : Y ⟶ cokernel f := coequalizer.π f 0

@[simp] lemma coequalizer_as_cokernel : coequalizer.π f 0 = cokernel.π f := rfl

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

@[simp]
lemma cokernel.desc_zero {W : C} {h} : cokernel.desc f (0 : Y ⟶ W) h = 0 :=
by { ext, simp, }

instance cokernel.desc_epi
  {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) [epi k] : epi (cokernel.desc f k h) :=
⟨λ Z g g' w,
begin
  replace w := cokernel.π f ≫= w,
  simp only [cokernel.π_desc_assoc] at w,
  exact (cancel_epi k).1 w,
end⟩

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = 0` induces `l : cokernel f ⟶ W` such that
    `cokernel.π f ≫ l = k`. -/
def cokernel.desc' {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
  {l : cokernel f ⟶ W // cokernel.π f ≫ l = k} :=
⟨cokernel.desc f k h, cokernel.π_desc _ _ _⟩

/-- A commuting square induces a morphism of cokernels. -/
abbreviation cokernel.map {X' Y' : C} (f' : X' ⟶ Y') [has_cokernel f']
  (p : X ⟶ X') (q : Y ⟶ Y') (w : f ≫ q = p ≫ f') : cokernel f ⟶ cokernel f' :=
cokernel.desc f (q ≫ cokernel.π f') (by simp [reassoc_of w])

/--
Given a commutative diagram
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
with horizontal arrows composing to zero,
then we obtain a commutative square
   cokernel f ---> Z
   |               |
   | cokernel.map  |
   |               |
   v               v
   cokernel f' --> Z'
-/
lemma cokernel.map_desc {X Y Z X' Y' Z' : C}
  (f : X ⟶ Y) [has_cokernel f] (g : Y ⟶ Z) (w : f ≫ g = 0)
  (f' : X' ⟶ Y') [has_cokernel f'] (g' : Y' ⟶ Z') (w' : f' ≫ g' = 0)
  (p : X ⟶ X') (q : Y ⟶ Y') (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
  cokernel.map f f' p q h₁ ≫ cokernel.desc f' g' w' = cokernel.desc f g w ≫ r :=
by { ext, simp [h₂], }

/-- The cokernel of the zero morphism is an isomorphism -/
instance cokernel.π_zero_is_iso :
  is_iso (cokernel.π (0 : X ⟶ Y)) :=
coequalizer.π_of_self _

lemma eq_zero_of_mono_cokernel [mono (cokernel.π f)] : f = 0 :=
(cancel_mono (cokernel.π f)).1 (by simp)

/-- The cokernel of a zero morphism is isomorphic to the target. -/
def cokernel_zero_iso_target : cokernel (0 : X ⟶ Y) ≅ Y :=
coequalizer.iso_target_of_self 0

@[simp] lemma cokernel_zero_iso_target_hom :
  cokernel_zero_iso_target.hom = cokernel.desc (0 : X ⟶ Y) (𝟙 Y) (by simp) :=
by { ext, simp [cokernel_zero_iso_target], }

@[simp] lemma cokernel_zero_iso_target_inv :
  cokernel_zero_iso_target.inv = cokernel.π (0 : X ⟶ Y) := rfl

/-- If two morphisms are known to be equal, then their cokernels are isomorphic. -/
def cokernel_iso_of_eq {f g : X ⟶ Y} [has_cokernel f] [has_cokernel g] (h : f = g) :
  cokernel f ≅ cokernel g :=
has_colimit.iso_of_nat_iso (by simp[h])

@[simp]
lemma cokernel_iso_of_eq_refl {h : f = f} : cokernel_iso_of_eq h = iso.refl (cokernel f) :=
by { ext, simp [cokernel_iso_of_eq], }

@[simp]
lemma cokernel_iso_of_eq_trans {f g h : X ⟶ Y} [has_cokernel f] [has_cokernel g] [has_cokernel h]
  (w₁ : f = g) (w₂ : g = h) :
  cokernel_iso_of_eq w₁ ≪≫ cokernel_iso_of_eq w₂ = cokernel_iso_of_eq (w₁.trans w₂) :=
by { unfreezingI { induction w₁, induction w₂, }, ext, simp [cokernel_iso_of_eq], }

variables {f}

lemma cokernel_not_mono_of_nonzero (w : f ≠ 0) : ¬mono (cokernel.π f) :=
λ I, by exactI w (eq_zero_of_mono_cokernel f)

lemma cokernel_not_iso_of_nonzero (w : f ≠ 0) : (is_iso (cokernel.π f)) → false :=
λ I, cokernel_not_mono_of_nonzero w $ by { resetI, apply_instance }

-- TODO the remainder of this section has obvious generalizations to `has_coequalizer f g`.

instance has_cokernel_comp_iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_cokernel f] [is_iso g] :
  has_cokernel (f ≫ g) :=
{ exists_colimit :=
  ⟨{ cocone := cokernel_cofork.of_π (inv g ≫ cokernel.π f) (by simp),
     is_colimit := is_colimit_aux _ (λ s, cokernel.desc _ (g ≫ s.π)
       (by { rw [←category.assoc, cokernel_cofork.condition], }))
       (by tidy)
       (λ s m w, by { simp_rw [←w], ext, simp, }), }⟩ }

/--
When `g` is an isomorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `f`.
-/
@[simps]
def cokernel_comp_is_iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_cokernel f] [is_iso g] :
  cokernel (f ≫ g) ≅ cokernel f :=
{ hom := cokernel.desc _ (inv g ≫ cokernel.π f) (by simp),
  inv := cokernel.desc _ (g ≫ cokernel.π (f ≫ g)) (by rw [←category.assoc, cokernel.condition]), }

instance has_cokernel_epi_comp {X Y Z : C} (f : X ⟶ Y) [epi f] (g : Y ⟶ Z) [has_cokernel g] :
  has_cokernel (f ≫ g) :=
{ exists_colimit :=
  ⟨{ cocone := cokernel_cofork.of_π (cokernel.π g) (by simp),
     is_colimit := is_colimit_aux _
      (λ s, cokernel.desc _ s.π ((cancel_epi f).mp (by { rw ← category.assoc, simp })))
      (by tidy) (by tidy) }⟩ }

/--
When `f` is an epimorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `g`.
-/
@[simps]
def cokernel_epi_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  [epi f] [has_cokernel g] :
  cokernel (f ≫ g) ≅ cokernel g :=
{ hom := cokernel.desc _ (cokernel.π g) (by simp),
  inv := cokernel.desc _ (cokernel.π (f ≫ g)) (by { rw [←cancel_epi f, ←category.assoc], simp, }), }

end

section has_zero_object
variables [has_zero_object C]

open_locale zero_object

/-- The morphism to the zero object determines a cocone on a cokernel diagram -/
def cokernel.zero_cocone : cocone (parallel_pair f 0) :=
{ X := 0,
  ι := { app := λ j, 0 } }

/-- The morphism to the zero object is a cokernel of an epimorphism -/
def cokernel.is_colimit_cocone_zero_cocone [epi f] : is_colimit (cokernel.zero_cocone f) :=
cofork.is_colimit.mk _ (λ s, 0)
  (λ s, by { erw zero_comp,
    convert (zero_of_epi_comp f _).symm,
    exact cokernel_cofork.condition _ })
  (λ _ _ _, zero_of_from_zero _)

/-- The cokernel of an epimorphism is isomorphic to the zero object -/
def cokernel.of_epi [has_cokernel f] [epi f] : cokernel f ≅ 0 :=
functor.map_iso (cocones.forget _) $ is_colimit.unique_up_to_iso
  (colimit.is_colimit (parallel_pair f 0)) (cokernel.is_colimit_cocone_zero_cocone f)

/-- The cokernel morphism of an epimorphism is a zero morphism -/
lemma cokernel.π_of_epi [has_cokernel f] [epi f] : cokernel.π f = 0 :=
zero_of_target_iso_zero _ (cokernel.of_epi f)

end has_zero_object

section has_image

/--
The cokernel of the image inclusion of a morphism `f` is isomorphic to the cokernel of `f`.

(This result requires that the factorisation through the image is an epimorphism.
This holds in any category with equalizers.)
-/
@[simps]
def cokernel_image_ι {X Y : C} (f : X ⟶ Y)
  [has_image f] [has_cokernel (image.ι f)] [has_cokernel f] [epi (factor_thru_image f)] :
  cokernel (image.ι f) ≅ cokernel f :=
{ hom := cokernel.desc _ (cokernel.π f)
  begin
    have w := cokernel.condition f,
    conv at w { to_lhs, congr, rw ←image.fac f, },
    rw [←has_zero_morphisms.comp_zero (limits.factor_thru_image f), category.assoc, cancel_epi]
      at w,
    exact w,
  end,
  inv := cokernel.desc _ (cokernel.π _)
  begin
    conv { to_lhs, congr, rw ←image.fac f, },
    rw [category.assoc, cokernel.condition, has_zero_morphisms.comp_zero],
  end, }

end has_image

section
variables (X Y)

/-- The cokernel of a zero morphism is an isomorphism -/
lemma cokernel.π_of_zero :
  is_iso (cokernel.π (0 : X ⟶ Y)) :=
coequalizer.π_of_self _

end


section has_zero_object
variables [has_zero_object C]

open_locale zero_object

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

/-- `has_kernels` represents the existence of kernels for every morphism. -/
class has_kernels : Prop :=
(has_limit : Π {X Y : C} (f : X ⟶ Y), has_kernel f . tactic.apply_instance)

/-- `has_cokernels` represents the existence of cokernels for every morphism. -/
class has_cokernels : Prop :=
(has_colimit : Π {X Y : C} (f : X ⟶ Y), has_cokernel f . tactic.apply_instance)

attribute [instance, priority 100] has_kernels.has_limit has_cokernels.has_colimit

@[priority 100]
instance has_kernels_of_has_equalizers [has_equalizers C] : has_kernels C :=
{}

@[priority 100]
instance has_cokernels_of_has_coequalizers [has_coequalizers C] : has_cokernels C :=
{}

end category_theory.limits
