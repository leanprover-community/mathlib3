/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.group.hom
import category_theory.limits.shapes.kernels
import algebra.big_operators.basic
import algebra.module.basic
import category_theory.endomorphism

/-!
# Preadditive categories

A preadditive category is a category in which `X ⟶ Y` is an abelian group in such a way that
composition of morphisms is linear in both variables.

This file contains a definition of preadditive category that directly encodes the definition given
above. The definition could also be phrased as follows: A preadditive category is a category
enriched over the category of Abelian groups. Once the general framework to state this in Lean is
available, the contents of this file should become obsolete.

## Main results

* Definition of preadditive categories and basic properties
* In a preadditive category, `f : Q ⟶ R` is mono if and only if `g ≫ f = 0 → g = 0` for all
  composable `g`.
* A preadditive category with kernels has equalizers.

## Implementation notes

The simp normal form for negation and composition is to push negations as far as possible to
the outside. For example, `f ≫ (-g)` and `(-f) ≫ g` both become `-(f ≫ g)`, and `(-f) ≫ (-g)`
is simplified to `f ≫ g`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

## Tags

additive, preadditive, Hom group, Ab-category, Ab-enriched
-/

universes v u

open category_theory.limits

open_locale big_operators

namespace category_theory

variables (C : Type u) [category.{v} C]

/-- A category is called preadditive if `P ⟶ Q` is an abelian group such that composition is
    linear in both variables. -/
class preadditive :=
(hom_group : Π P Q : C, add_comm_group (P ⟶ Q) . tactic.apply_instance)
(add_comp' : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R),
  (f + f') ≫ g = f ≫ g + f' ≫ g . obviously)
(comp_add' : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R),
  f ≫ (g + g') = f ≫ g + f ≫ g' . obviously)

attribute [instance] preadditive.hom_group
restate_axiom preadditive.add_comp'
restate_axiom preadditive.comp_add'
attribute [simp,reassoc] preadditive.add_comp
attribute [reassoc] preadditive.comp_add -- (the linter doesn't like `simp` on this lemma)
attribute [simp] preadditive.comp_add

end category_theory

open category_theory

namespace category_theory
namespace preadditive

section preadditive
open add_monoid_hom
variables {C : Type u} [category.{v} C] [preadditive C]

section induced_category
universes u'
variables {C} {D : Type u'} (F : D → C)

instance induced_category.category : preadditive.{v} (induced_category C F) :=
{ hom_group := λ P Q, @preadditive.hom_group C _ _ (F P) (F Q),
  add_comp' := λ P Q R f f' g, add_comp' _ _ _ _ _ _,
  comp_add' := λ P Q R f g g', comp_add' _ _ _ _ _ _, }

end induced_category

instance (X : C) : add_comm_group (End X) := by { dsimp [End], apply_instance, }

instance (X : C) : ring (End X) :=
{ left_distrib := λ f g h, preadditive.add_comp X X X g h f,
  right_distrib := λ f g h, preadditive.comp_add X X X h f g,
  ..(infer_instance : add_comm_group (End X)),
  ..(infer_instance : monoid (End X)) }

/-- Composition by a fixed left argument as a group homomorphism -/
def left_comp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
mk' (λ g, f ≫ g) $ λ g g', by simp

/-- Composition by a fixed right argument as a group homomorphism -/
def right_comp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
mk' (λ f, f ≫ g) $ λ f f', by simp

variables {P Q R : C} (f f' : P ⟶ Q) (g g' : Q ⟶ R)

/-- Composition as a bilinear group homomorphism -/
def comp_hom : (P ⟶ Q) →+ (Q ⟶ R) →+ (P ⟶ R) :=
add_monoid_hom.mk' (λ f, left_comp _ f) $
  λ f₁ f₂, add_monoid_hom.ext $ λ g, (right_comp _ g).map_add f₁ f₂

@[simp, reassoc] lemma sub_comp :
  (f - f') ≫ g = f ≫ g - f' ≫ g :=
map_sub (right_comp P g) f f'

-- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma.
@[reassoc, simp] lemma comp_sub :
  f ≫ (g - g') = f ≫ g - f ≫ g' :=
map_sub (left_comp R f) g g'

@[simp, reassoc] lemma neg_comp : (-f) ≫ g = -(f ≫ g) :=
map_neg (right_comp P g) f

/- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma. -/
@[reassoc, simp] lemma comp_neg : f ≫ (-g) = -(f ≫ g) :=
map_neg (left_comp R f) g

@[reassoc] lemma neg_comp_neg : (-f) ≫ (-g) = f ≫ g :=
by simp

lemma nsmul_comp (n : ℕ) : (n • f) ≫ g = n • (f ≫ g) :=
map_nsmul (right_comp P g) f n

lemma comp_nsmul (n : ℕ) : f ≫ (n • g) = n • (f ≫ g) :=
map_nsmul (left_comp R f) g n

lemma zsmul_comp (n : ℤ) : (n • f) ≫ g = n • (f ≫ g) :=
map_zsmul (right_comp P g) f n

lemma comp_zsmul (n : ℤ) : f ≫ (n • g) = n • (f ≫ g) :=
map_zsmul (left_comp R f) g n

@[reassoc] lemma comp_sum {P Q R : C} {J : Type*} (s : finset J) (f : P ⟶ Q) (g : J → (Q ⟶ R)) :
  f ≫ ∑ j in s, g j = ∑ j in s, f ≫ g j :=
map_sum (left_comp R f) _ _

@[reassoc] lemma sum_comp {P Q R : C} {J : Type*} (s : finset J) (f : J → (P ⟶ Q)) (g : Q ⟶ R) :
  (∑ j in s, f j) ≫ g  = ∑ j in s, f j ≫ g :=
map_sum (right_comp P g) _ _

instance {P Q : C} {f : P ⟶ Q} [epi f] : epi (-f) :=
⟨λ R g g' H, by rwa [neg_comp, neg_comp, ←comp_neg, ←comp_neg, cancel_epi, neg_inj] at H⟩

instance {P Q : C} {f : P ⟶ Q} [mono f] : mono (-f) :=
⟨λ R g g' H, by rwa [comp_neg, comp_neg, ←neg_comp, ←neg_comp, cancel_mono, neg_inj] at H⟩

@[priority 100]
instance preadditive_has_zero_morphisms : has_zero_morphisms C :=
{ has_zero := infer_instance,
  comp_zero' := λ P Q f R, show left_comp R f 0 = 0, from map_zero _,
  zero_comp' := λ P Q R f, show right_comp P f 0 = 0, from map_zero _ }

instance module_End_right {X Y : C} : module (End Y) (X ⟶ Y) :=
{ smul_add := λ r f g, add_comp _ _ _ _ _ _,
  smul_zero := λ r, zero_comp,
  add_smul := λ r s f, comp_add _ _ _ _ _ _,
  zero_smul := λ r, comp_zero }

lemma mono_of_cancel_zero {Q R : C} (f : Q ⟶ R) (h : ∀ {P : C} (g : P ⟶ Q), g ≫ f = 0 → g = 0) :
  mono f :=
⟨λ P g g' hg, sub_eq_zero.1 $ h _ $ (map_sub (right_comp P f) g g').trans $ sub_eq_zero.2 hg⟩

lemma mono_iff_cancel_zero {Q R : C} (f : Q ⟶ R) :
  mono f ↔ ∀ (P : C) (g : P ⟶ Q), g ≫ f = 0 → g = 0 :=
⟨λ m P g, by exactI zero_of_comp_mono _, mono_of_cancel_zero f⟩

lemma mono_of_kernel_zero {X Y : C} {f : X ⟶ Y} [has_limit (parallel_pair f 0)]
  (w : kernel.ι f = 0) : mono f :=
mono_of_cancel_zero f (λ P g h, by rw [←kernel.lift_ι f g h, w, limits.comp_zero])

lemma epi_of_cancel_zero {P Q : C} (f : P ⟶ Q) (h : ∀ {R : C} (g : Q ⟶ R), f ≫ g = 0 → g = 0) :
  epi f :=
⟨λ R g g' hg, sub_eq_zero.1 $ h _ $ (map_sub (left_comp R f) g g').trans $ sub_eq_zero.2 hg⟩

lemma epi_iff_cancel_zero {P Q : C} (f : P ⟶ Q) :
  epi f ↔ ∀ (R : C) (g : Q ⟶ R), f ≫ g = 0 → g = 0 :=
⟨λ e R g, by exactI zero_of_epi_comp _, epi_of_cancel_zero f⟩

lemma epi_of_cokernel_zero {X Y : C} {f : X ⟶ Y} [has_colimit (parallel_pair f 0 )]
  (w : cokernel.π f = 0) : epi f :=
epi_of_cancel_zero f (λ P g h, by rw [←cokernel.π_desc f g h, w, limits.zero_comp])

namespace is_iso

@[simp] lemma comp_left_eq_zero [is_iso f] :
  f ≫ g = 0 ↔ g = 0 :=
by rw [← is_iso.eq_inv_comp, limits.comp_zero]

@[simp] lemma comp_right_eq_zero [is_iso g] :
  f ≫ g = 0 ↔ f = 0 :=
by rw [← is_iso.eq_comp_inv, limits.zero_comp]

end is_iso

open_locale zero_object
variables [has_zero_object C]

lemma mono_of_kernel_iso_zero {X Y : C} {f : X ⟶ Y} [has_limit (parallel_pair f 0)]
  (w : kernel f ≅ 0) : mono f :=
mono_of_kernel_zero (zero_of_source_iso_zero _ w)

lemma epi_of_cokernel_iso_zero {X Y : C} {f : X ⟶ Y} [has_colimit (parallel_pair f 0)]
  (w : cokernel f ≅ 0) : epi f :=
epi_of_cokernel_zero (zero_of_target_iso_zero _ w)

end preadditive

section equalizers
variables {C : Type u} [category.{v} C] [preadditive C]

section
variables {X Y : C} {f : X ⟶ Y} {g : X ⟶ Y}

/-- Map a kernel cone on the difference of two morphisms to the equalizer fork. -/
def fork_of_kernel_fork (c : kernel_fork (f - g)) : fork f g :=
fork.of_ι c.ι $ by rw [← sub_eq_zero, ← comp_sub, c.condition]

/-- Map any equalizer fork to a cone on the difference of the two morphisms. -/
def kernel_fork_of_fork (c : fork f g) : kernel_fork (f - g) :=
fork.of_ι c.ι $ by rw [comp_sub, comp_zero, sub_eq_zero, c.condition]

/-- A kernel of `f - g` is an equalizer of `f` and `g`. -/
def is_limit_fork_of_kernel_fork {c : kernel_fork (f - g)} (i : is_limit c) :
  is_limit (fork_of_kernel_fork c) :=
fork.is_limit.mk' _ $ λ s,
  ⟨i.lift (kernel_fork_of_fork s), i.fac _ _,
   λ m h, by { apply fork.is_limit.hom_ext i, rw [i.fac], exact h }⟩

/-- An equalizer of `f` and `g` is a kernel of `f - g`. -/
def is_limit_kernel_fork_of_fork {c : fork f g} (i : is_limit c) :
  is_limit (kernel_fork_of_fork c) :=
fork.is_limit.mk' _ $ λ s,
  ⟨i.lift (fork_of_kernel_fork s), i.fac _ _,
    λ m h, by { apply fork.is_limit.hom_ext i, rw [i.fac], exact h }⟩

variables (f g)

/-- A preadditive category has an equalizer for `f` and `g` if it has a kernel for `f - g`. -/
lemma has_equalizer_of_has_kernel [has_kernel (f - g)] : has_equalizer f g :=
has_limit.mk { cone := fork_of_kernel_fork _,
  is_limit := is_limit_fork_of_kernel_fork (equalizer_is_equalizer (f - g) 0) }

/-- A preadditive category has a kernel for `f - g` if it has an equalizer for `f` and `g`. -/
lemma has_kernel_of_has_equalizer [has_equalizer f g] : has_kernel (f - g) :=
has_limit.mk { cone := kernel_fork_of_fork (equalizer.fork f g),
  is_limit := is_limit_kernel_fork_of_fork (limit.is_limit (parallel_pair f g)) }

variables {f g}

/-- Map a cokernel cocone on the difference of two morphisms to the coequalizer cofork. -/
def cofork_of_cokernel_cofork (c : cokernel_cofork (f - g)) : cofork f g :=
cofork.of_π c.π $ by rw [← sub_eq_zero, ← sub_comp, c.condition]

/-- Map any coequalizer cofork to a cocone on the difference of the two morphisms. -/
def cokernel_cofork_of_cofork (c : cofork f g) : cokernel_cofork (f - g) :=
cofork.of_π c.π $ by rw [sub_comp, zero_comp, sub_eq_zero, c.condition]

/-- A cokernel of `f - g` is a coequalizer of `f` and `g`. -/
def is_colimit_cofork_of_cokernel_cofork {c : cokernel_cofork (f - g)} (i : is_colimit c) :
  is_colimit (cofork_of_cokernel_cofork c) :=
cofork.is_colimit.mk' _ $ λ s,
  ⟨i.desc (cokernel_cofork_of_cofork s), i.fac _ _,
   λ m h, by { apply cofork.is_colimit.hom_ext i, rw [i.fac], exact h }⟩

/-- A coequalizer of `f` and `g` is a cokernel of `f - g`. -/
def is_colimit_cokernel_cofork_of_cofork {c : cofork f g} (i : is_colimit c) :
  is_colimit (cokernel_cofork_of_cofork c) :=
cofork.is_colimit.mk' _ $ λ s,
  ⟨i.desc (cofork_of_cokernel_cofork s), i.fac _ _,
    λ m h, by { apply cofork.is_colimit.hom_ext i, rw [i.fac], exact h }⟩

variables (f g)

/-- A preadditive category has a coequalizer for `f` and `g` if it has a cokernel for `f - g`. -/
lemma has_coequalizer_of_has_cokernel [has_cokernel (f - g)] : has_coequalizer f g :=
has_colimit.mk { cocone := cofork_of_cokernel_cofork _,
  is_colimit := is_colimit_cofork_of_cokernel_cofork (coequalizer_is_coequalizer (f - g) 0) }

/-- A preadditive category has a cokernel for `f - g` if it has a coequalizer for `f` and `g`. -/
lemma has_cokernel_of_has_coequalizer [has_coequalizer f g] : has_cokernel (f - g) :=
has_colimit.mk { cocone := cokernel_cofork_of_cofork (coequalizer.cofork f g),
  is_colimit := is_colimit_cokernel_cofork_of_cofork (colimit.is_colimit (parallel_pair f g)) }

end

/-- If a preadditive category has all kernels, then it also has all equalizers. -/
lemma has_equalizers_of_has_kernels [has_kernels C] : has_equalizers C :=
@has_equalizers_of_has_limit_parallel_pair _ _ (λ _ _ f g, has_equalizer_of_has_kernel f g)


/-- If a preadditive category has all cokernels, then it also has all coequalizers. -/
lemma has_coequalizers_of_has_cokernels [has_cokernels C] : has_coequalizers C :=
@has_coequalizers_of_has_colimit_parallel_pair _ _ (λ _ _ f g, has_coequalizer_of_has_cokernel f g)

end equalizers

end preadditive

end category_theory
