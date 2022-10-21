/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.groupoid
import category_theory.groupoid.quotient
import category_theory.groupoid.free_groupoid

/-!
# Presentations of groupoids

Given a quiver `V` and a family `W` of elements of the free groupoid on `V`, we construct the
groupoid presented by the pair `V,W`, and verify that the construction satisfies the expected
universal property.
-/

namespace category_theory

universes u v

open groupoid

variables {V : Type u} [quiver.{v+1} V] (W : ∀ (x y : free_groupoid V), set $ x ⟶ y)

/--
The groupoid with generator `V` and relations `W`.
-/
def presented_groupoid :=
  quotient_groupoid _ ( subgroupoid.generated_normal_is_normal W )

instance : groupoid (presented_groupoid W) :=
  quotient_groupoid.category_theory.groupoid _ ( subgroupoid.generated_normal_is_normal W )

namespace presented_groupoid

/--
The inclusion of `V` in `presented_groupoid W`
-/
noncomputable def of : prefunctor V (presented_groupoid W) :=
(free.of V).comp (quotient_groupoid.of _ ( subgroupoid.generated_normal_is_normal W )).to_prefunctor

section ump

variables {V' : Type*} [groupoid V'] (φ : prefunctor V V')
  (hφ : ∀ (x y : free_groupoid V), W x y ⊆ (subgroupoid.ker $ free.lift φ).arrows x y)

include φ hφ

/--
The lift of the prefunctor `φ` to a functor `presented_groupoid W ⥤ V'`,
assumming `φ` satisfies the relations in `W`
 -/
def lift : presented_groupoid W ⥤ V' :=
begin
  fapply quotient_groupoid.lift,
  { apply free.lift φ, },
  { apply subgroupoid.generated_normal_le_of_normal_containing,
    apply subgroupoid.ker_is_normal,
    apply hφ },
end

lemma lift_spec : (of W).comp (lift W φ hφ).to_prefunctor = φ :=
begin
  dsimp only [of, lift],
  rw [prefunctor.comp_assoc, functor.to_prefunctor_comp],
  rw [quotient_groupoid.lift_spec, free.lift_spec],
end

lemma lift_unique (Φ : presented_groupoid W ⥤ V') (hΦ : (of W).comp Φ.to_prefunctor = φ) :
  Φ = (lift W φ hφ) :=
begin
  dsimp only [of, lift],
  apply quotient_groupoid.lift_unique,
  apply free.lift_unique,
  exact hΦ,
end

end ump

end presented_groupoid

end category_theory
