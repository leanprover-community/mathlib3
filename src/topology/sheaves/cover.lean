import category_theory.isomorphism
import order.complete_lattice
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.products

/-!
# Covers parameterized by the union

In the definition of the sheaf condition, we work with an indexed family `U : ι → opens X` of open
sets, and write the sheaf condition in terms of `F.obj (supr U)` and restrictions from there.

Often instead we have some fixed open set `U`, and some cover of it
(i.e. a family `𝒰 : ι → opens X`, along with the fact that `supr 𝒰 = U`).

This file develops the basics of this notion.

-/

universes v u

open category_theory
open category_theory.limits

variables {C : Type u} [category.{v} C]

structure family_over (U : C) :=
(ι : Type v)
(𝒰 : ι → C)
(φ : Π i, 𝒰 i ⟶ U)

namespace family_over

def single {U V : C} (f : U ⟶ V) : family_over V :=
{ ι := punit,
  𝒰 := λ _, U,
  φ := λ _, f }

def of_family {U : C} (c : family_over U) (f : Π i : c.ι, family_over (c.𝒰 i)) : family_over U :=
{ ι := Σ i : c.ι, (f i).ι,
  𝒰 := λ p, (f p.1).𝒰 p.2,
  φ := λ p, (f p.1).φ p.2 ≫ c.φ p.1, }

def pullback {U V : C} (c : family_over U) (f : V ⟶ U) [∀ i, has_pullback f (c.φ i)] : family_over V :=
{ ι := c.ι,
  𝒰 := λ i, pullback f (c.φ i),
  φ := λ i, pullback.fst, }

def desc_is_iso {U : C} (c : family_over U) [has_coproduct c.𝒰] : Type v :=
is_iso (sigma.desc c.φ)

instance has_coproduct_single {U V : C} (f : U ⟶ V) : has_coproduct (single f).𝒰 :=
by { dsimp [single], apply_instance, }

def single_desc_is_iso {U V : C} (f : U ≅ V) : (single f.hom).desc_is_iso :=
by { dunfold desc_is_iso, dsimp [single], simp, apply_instance, }

instance has_coproduct_of_family
  {U : C} (c : family_over U) [has_coproduct c.𝒰] (i : c.desc_is_iso)
  (f : Π i : c.ι, family_over (c.𝒰 i)) [∀ i, has_coproduct (f i).𝒰] :
  has_coproduct (c.of_family f).𝒰 :=
begin
  dsimp [of_family],
  haveI : has_coproduct (λ (b : c.ι), ∐ (λ (i : c.ι), (f i).𝒰) b) := sorry,
  exact limits.has_coproduct_of_shape_sigma _ (λ i, (f i).𝒰),
end

def of_family_desc_is_iso {U : C} (c : family_over U) [has_coproduct c.𝒰] (c_i : c.desc_is_iso)
  (f : Π i : c.ι, family_over (c.𝒰 i)) [∀ i, has_coproduct (f i).𝒰] (f_i : ∀ i, (f i).desc_is_iso)
  [has_coproduct (c.of_family f).𝒰] :
  (c.of_family f).desc_is_iso :=
begin
  dunfold desc_is_iso, dsimp [of_family],
  sorry
end

instance has_coproduct_pullback
  {U : C} (c : family_over U) [has_coproduct c.𝒰] (c_i : c.desc_is_iso)
  {V : C} (f : V ⟶ U) [∀ i, has_pullback f (c.φ i)] :
  has_coproduct (c.pullback f).𝒰 :=
begin
  dsimp [pullback],
  apply limits.has_coproduct_pullback C _ _ f,
  apply_instance,
  unfreezingI { dsimp [desc_is_iso] at c_i, },
  apply_instance,
end

def pullback_desc_is_iso
  {U : C} (c : family_over U) [has_coproduct c.𝒰] (c_i : c.desc_is_iso)
  {V : C} (f : V ⟶ U) [∀ i, has_pullback f (c.φ i)] :
  begin
    haveI := family_over.has_coproduct_pullback c c_i f,
    exact (c.pullback f).desc_is_iso,
  end :=
begin
  dunfold desc_is_iso, dsimp [pullback],
  unfreezingI { dsimp [desc_is_iso] at c_i, },
  sorry
end

end family_over

variables {α : Type u} [complete_lattice α]

/--
A cover of `U : α` is an indexed family of objects with supremem `U`.
-/
-- (We use the typeclass `complete_lattice` for lack of an appropriate semilattice typeclass.)
structure cover (U : α) extends family_over U :=
(supr : supr 𝒰 = U)


attribute [protected] cover.supr

namespace cover

/--
The trivial cover, indexed by `punit`.
-/
def single (U : α) : cover U :=
{ supr := by { dsimp [family_over.single], exact supr_const },
  .. family_over.single (𝟙 U) }

/--
Convert an indexed family of objects into a cover of their `supr`.
-/
def of {ι : Type u} (𝒰 : ι → α) : cover (supr 𝒰) :=
{ ι := ι,
  𝒰 := 𝒰,
  supr := rfl,
  φ := λ i, hom_of_le (le_supr 𝒰 i), }

/--
Assemble a family of covers of the elements of a cover into a single cover.
-/
def of_covers {U : α} {c : cover U} (C : Π i : c.ι, cover (c.𝒰 i)) : cover U :=
{ supr :=
  begin
    dsimp,
    apply le_antisymm,
    { apply supr_le_iff.mpr,
      sorry, },
    { conv_lhs { rw ←c.supr },
      apply supr_le_iff.mpr,
      intro i,
      rw ←(C i).supr,
      apply supr_le_iff.mpr,
      intro i',
      convert le_supr _ (⟨i, i'⟩ : Σ i : c.ι, (C i).ι),
      refl, },
  end,
  .. family_over.of_family c.to_family_over (λ i, (C i).to_family_over) }

end cover
