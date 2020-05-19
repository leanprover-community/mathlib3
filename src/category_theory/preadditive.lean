/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.group.hom
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.biproducts

/-!
# Preadditive categories

A preadditive category is a category in which `X ⟶ Y` is an abelian group in such a way that
composition of morphisms is linear in both variables.

This file contains a definition of preadditive category that directly encodes the definition given
above. The definition could also be phrased as follows: A preadditive category is a category
enriched over the category of Abelian groups. Once the general framework to state this in Lean is
available, the contents of this file should become obsolete.

## Main results

We define preadditive categories and show their basic properties, including the following
statements:

* In a preadditive category, `f : Q ⟶ R` is mono if and only if `g ≫ f = 0 → g = 0` for all
  composable `g`.
* A preadditive category with kernels has equalizers.

Furthermore, we define the notion of "preadditive binary biproduct", which is a preadditive version
of the notion of biproduct. We show that a preadditive binary biproduct is a binary biproduct and
construct preadditive binary biproducts both from binary products and binary coproducts.

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
open add_monoid_hom

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
attribute [simp] preadditive.add_comp preadditive.comp_add

end category_theory

open category_theory

namespace category_theory.preadditive

section preadditive
variables {C : Type u} [category.{v} C] [preadditive.{v} C]

/-- Composition by a fixed left argument as a group homomorphism -/
def left_comp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
mk' (λ g, f ≫ g) $ λ g g', by simp

/-- Composition by a fixed right argument as a group homomorphism -/
def right_comp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
mk' (λ f, f ≫ g) $ λ f f', by simp

@[simp] lemma sub_comp {P Q R : C} (f f' : P ⟶ Q) (g : Q ⟶ R) :
  (f - f') ≫ g = f ≫ g - f' ≫ g :=
map_sub (right_comp P g) f f'

@[simp] lemma comp_sub {P Q R : C} (f : P ⟶ Q) (g g' : Q ⟶ R) :
  f ≫ (g - g') = f ≫ g - f ≫ g' :=
map_sub (left_comp R f) g g'

@[simp] lemma neg_comp {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : (-f) ≫ g = -(f ≫ g) :=
map_neg (right_comp _ _) _

@[simp] lemma comp_neg {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : f ≫ (-g) = -(f ≫ g) :=
map_neg (left_comp _ _) _

lemma neg_comp_neg {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : (-f) ≫ (-g) = f ≫ g :=
by simp

instance {P Q : C} {f : P ⟶ Q} [epi f] : epi (-f) :=
⟨λ R g g', by { rw [neg_comp, neg_comp, ←comp_neg, ←comp_neg, cancel_epi], exact neg_inj }⟩

instance {P Q : C} {f : P ⟶ Q} [mono f] : mono (-f) :=
⟨λ R g g', by { rw [comp_neg, comp_neg, ←neg_comp, ←neg_comp, cancel_mono], exact neg_inj }⟩

@[priority 100]
instance preadditive_has_zero_morphisms : has_zero_morphisms.{v} C :=
{ has_zero := infer_instance,
  comp_zero' := λ P Q f R, map_zero $ left_comp R f,
  zero_comp' := λ P Q R f, map_zero $ right_comp P f }

lemma mono_of_cancel_zero {Q R : C} (f : Q ⟶ R) (h : ∀ {P : C} (g : P ⟶ Q), g ≫ f = 0 → g = 0) :
  mono f :=
⟨λ P g g' hg, sub_eq_zero.1 $ h _ $ (map_sub (right_comp P f) g g').trans $ sub_eq_zero.2 hg⟩

lemma mono_iff_cancel_zero {Q R : C} (f : Q ⟶ R) :
  mono f ↔ ∀ (P : C) (g : P ⟶ Q), g ≫ f = 0 → g = 0 :=
⟨λ m P g, by exactI zero_of_comp_mono _, mono_of_cancel_zero f⟩

lemma epi_of_cancel_zero {P Q : C} (f : P ⟶ Q) (h : ∀ {R : C} (g : Q ⟶ R), f ≫ g = 0 → g = 0) :
  epi f :=
⟨λ R g g' hg, sub_eq_zero.1 $ h _ $ (map_sub (left_comp R f) g g').trans $ sub_eq_zero.2 hg⟩

lemma epi_iff_cancel_zero {P Q : C} (f : P ⟶ Q) :
  epi f ↔ ∀ (R : C) (g : Q ⟶ R), f ≫ g = 0 → g = 0 :=
⟨λ e R g, by exactI zero_of_epi_comp _, epi_of_cancel_zero f⟩

end preadditive

section equalizers
variables {C : Type u} [category.{v} C] [preadditive.{v} C]

section
variables {X Y : C} (f : X ⟶ Y) (g : X ⟶ Y)

/-- A kernel of `f - g` is an equalizer of `f` and `g`. -/
def has_limit_parallel_pair [has_limit (parallel_pair (f - g) 0)] :
  has_limit (parallel_pair f g) :=
{ cone := fork.of_ι (kernel.ι (f - g)) (sub_eq_zero.1 $
    by { rw ←comp_sub, exact kernel.condition _ }),
  is_limit := fork.is_limit.mk _
    (λ s, kernel.lift (f - g) (fork.ι s) $
      by { rw comp_sub, apply sub_eq_zero.2, exact fork.condition _ })
    (λ s, by simp)
    (λ s m h, by { ext, simpa using h walking_parallel_pair.zero }) }

end

section

/-- If a preadditive category has all kernels, then it also has all equalizers. -/
def has_equalizers_of_has_kernels [has_kernels.{v} C] : has_equalizers.{v} C :=
@has_equalizers_of_has_limit_parallel_pair _ _ (λ _ _ f g, has_limit_parallel_pair f g)

end

section
variables {X Y : C} (f : X ⟶ Y) (g : X ⟶ Y)

/-- A cokernel of `f - g` is a coequalizer of `f` and `g`. -/
def has_colimit_parallel_pair [has_colimit (parallel_pair (f - g) 0)] :
  has_colimit (parallel_pair f g) :=
{ cocone := cofork.of_π (cokernel.π (f - g)) (sub_eq_zero.1 $
    by { rw ←sub_comp, exact cokernel.condition _ }),
  is_colimit := cofork.is_colimit.mk _
    (λ s, cokernel.desc (f - g) (cofork.π s) $
      by { rw sub_comp, apply sub_eq_zero.2, exact cofork.condition _ })
    (λ s, by simp)
    (λ s m h, by { ext, simpa using h walking_parallel_pair.one }) }

end

section

/-- If a preadditive category has all cokernels, then it also has all coequalizers. -/
def has_coequalizers_of_has_cokernels [has_cokernels.{v} C] : has_coequalizers.{v} C :=
@has_coequalizers_of_has_colimit_parallel_pair _ _ (λ _ _ f g, has_colimit_parallel_pair f g)

end

end equalizers

section biproduct
variables {C : Type u} [category.{v} C] [preadditive.{v} C]

/-- A preadditive binary biproduct is a bicone on two objects `X` and `Y` satisfying a set of five
    axioms expressing the properties of a biproduct in additive terms. The notion of preadditive
    binary biproduct is strictly stronger than the notion of binary biproduct (but it can be shown
    that in any preadditive category, the existence of a binary biproduct implies the existence of
    a preadditive binary biproduct). -/
class has_preadditive_binary_biproduct (X Y : C) :=
(bicone : binary_bicone.{v} X Y)
(ι₁_π₁' : bicone.ι₁ ≫ bicone.π₁ = 𝟙 X . obviously)
(ι₂_π₂' : bicone.ι₂ ≫ bicone.π₂ = 𝟙 Y . obviously)
(ι₂_π₁' : bicone.ι₂ ≫ bicone.π₁ = 0 . obviously)
(ι₁_π₂' : bicone.ι₁ ≫ bicone.π₂ = 0 . obviously)
(total' : bicone.π₁ ≫ bicone.ι₁ + bicone.π₂ ≫ bicone.ι₂ = 𝟙 bicone.X . obviously)

restate_axiom has_preadditive_binary_biproduct.ι₁_π₁'
restate_axiom has_preadditive_binary_biproduct.ι₂_π₂'
restate_axiom has_preadditive_binary_biproduct.ι₂_π₁'
restate_axiom has_preadditive_binary_biproduct.ι₁_π₂'
restate_axiom has_preadditive_binary_biproduct.total'
attribute [simp, reassoc] has_preadditive_binary_biproduct.ι₁_π₁
  has_preadditive_binary_biproduct.ι₂_π₂ has_preadditive_binary_biproduct.ι₂_π₁
  has_preadditive_binary_biproduct.ι₁_π₂
attribute [simp] has_preadditive_binary_biproduct.total

section
local attribute [tidy] tactic.case_bash

/-- A preadditive binary biproduct is a binary biproduct. -/
@[priority 100]
instance (X Y : C) [has_preadditive_binary_biproduct.{v} X Y] : has_binary_biproduct.{v} X Y :=
{ bicone := has_preadditive_binary_biproduct.bicone,
  is_limit :=
  { lift := λ s, binary_fan.fst s ≫ has_preadditive_binary_biproduct.bicone.ι₁ +
      binary_fan.snd s ≫ has_preadditive_binary_biproduct.bicone.ι₂,
    uniq' := λ s m h, by erw [←category.comp_id m, ←has_preadditive_binary_biproduct.total,
      comp_add, reassoc_of (h walking_pair.left), reassoc_of (h walking_pair.right)] },
  is_colimit :=
  { desc := λ s, has_preadditive_binary_biproduct.bicone.π₁ ≫ binary_cofan.inl s +
      has_preadditive_binary_biproduct.bicone.π₂ ≫ binary_cofan.inr s,
    uniq' := λ s m h, by erw [←category.id_comp m, ←has_preadditive_binary_biproduct.total,
      add_comp, category.assoc, category.assoc, h walking_pair.left, h walking_pair.right] } }

end

section
variables (X Y : C) [has_preadditive_binary_biproduct.{v} X Y]

@[simp, reassoc] lemma biprod.inl_fst : (biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.fst = 𝟙 X :=
has_preadditive_binary_biproduct.ι₁_π₁
@[simp, reassoc] lemma biprod.inr_snd : (biprod.inr : Y ⟶ X ⊞ Y) ≫ biprod.snd = 𝟙 Y :=
has_preadditive_binary_biproduct.ι₂_π₂
@[simp, reassoc] lemma biprod.inr_fst : (biprod.inr : Y ⟶ X ⊞ Y) ≫ biprod.fst = 0 :=
has_preadditive_binary_biproduct.ι₂_π₁
@[simp, reassoc] lemma biprod.inl_snd : (biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.snd = 0 :=
has_preadditive_binary_biproduct.ι₁_π₂
@[simp] lemma biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) :=
has_preadditive_binary_biproduct.total

end

section has_limit_pair

/-- In a preadditive category, if the product of `X` and `Y` exists, then the preadditive binary
    biproduct of `X` and `Y` exists. -/
def has_preadditive_binary_biproduct.of_has_limit_pair (X Y : C) [has_limit.{v} (pair X Y)] :
  has_preadditive_binary_biproduct.{v} X Y :=
{ bicone :=
  { X := X ⨯ Y,
    π₁ := category_theory.limits.prod.fst,
    π₂ := category_theory.limits.prod.snd,
    ι₁ := prod.lift (𝟙 X) 0,
    ι₂ := prod.lift 0 (𝟙 Y) } }

/-- In a preadditive category, if the coproduct of `X` and `Y` exists, then the preadditive binary
    biproduct of `X` and `Y` exists. -/
def has_preadditive_binary_biproduct.of_has_colimit_pair (X Y : C) [has_colimit.{v} (pair X Y)] :
  has_preadditive_binary_biproduct.{v} X Y :=
{ bicone :=
  { X := X ⨿ Y,
    π₁ := coprod.desc (𝟙 X) 0,
    π₂ := coprod.desc 0 (𝟙 Y),
    ι₁ := category_theory.limits.coprod.inl,
    ι₂ := category_theory.limits.coprod.inr } }

end has_limit_pair

section
variable (C)

/-- A preadditive category `has_preadditive_binary_biproducts` if the preadditive binary biproduct
    exists for every pair of objects. -/
class has_preadditive_binary_biproducts :=
(has_preadditive_binary_biproduct : Π (X Y : C), has_preadditive_binary_biproduct.{v} X Y)

attribute [instance, priority 100] has_preadditive_binary_biproducts.has_preadditive_binary_biproduct

/-- If a preadditive category has all binary products, then it has all preadditive binary
    biproducts. -/
def has_preadditive_binary_biproducts_of_has_binary_products [has_binary_products.{v} C] :
  has_preadditive_binary_biproducts.{v} C :=
⟨λ X Y, has_preadditive_binary_biproduct.of_has_limit_pair X Y⟩

/-- If a preadditive category has all binary coproducts, then it has all preadditive binary
    biproducts. -/
def has_preadditive_binary_biproducts_of_has_binary_coproducts [has_binary_coproducts.{v} C] :
  has_preadditive_binary_biproducts.{v} C :=
⟨λ X Y, has_preadditive_binary_biproduct.of_has_colimit_pair X Y⟩

end

end biproduct
end category_theory.preadditive
