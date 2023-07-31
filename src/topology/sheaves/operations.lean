/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebra.category.Ring.instances
import algebra.category.Ring.filtered_colimits
import ring_theory.localization.basic
import topology.sheaves.stalks

/-!

# Operations on sheaves

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definition

- `submonoid_presheaf` : A subpresheaf with a submonoid structure on each of the components.
- `localization_presheaf` : The localization of a presheaf of commrings at a `submonoid_presheaf`.
- `total_quotient_presheaf` : The presheaf of total quotient rings.

-/

open_locale non_zero_divisors

open topological_space opposite category_theory

universes v u w

namespace Top

namespace presheaf

variables {X : Top.{w}} {C : Type u} [category.{v} C] [concrete_category C]

local attribute [instance] concrete_category.has_coe_to_sort

/-- A subpresheaf with a submonoid structure on each of the components. -/
structure submonoid_presheaf [∀ X : C, mul_one_class X]
  [∀ (X Y : C), monoid_hom_class (X ⟶ Y) X Y] (F : X.presheaf C) :=
(obj : ∀ U, submonoid (F.obj U))
(map : ∀ {U V : (opens X)ᵒᵖ} (i : U ⟶ V), (obj U) ≤ (obj V).comap (F.map i))

variables {F : X.presheaf CommRing.{w}} (G : F.submonoid_presheaf)

/-- The localization of a presheaf of `CommRing`s with respect to a `submonoid_presheaf`. -/
protected noncomputable
def submonoid_presheaf.localization_presheaf :
  X.presheaf CommRing :=
{ obj := λ U, CommRing.of $ localization (G.obj U),
  map := λ U V i, CommRing.of_hom $ is_localization.map _ (F.map i) (G.map i),
  map_id' := λ U, begin
    apply is_localization.ring_hom_ext (G.obj U),
    any_goals { dsimp, apply_instance },
    refine (is_localization.map_comp _).trans _,
    rw F.map_id,
    refl,
  end,
  map_comp' := λ U V W i j, by { refine eq.trans _ (is_localization.map_comp_map _ _).symm,
    ext, dsimp, congr, rw F.map_comp, refl } }

/-- The map into the localization presheaf. -/
def submonoid_presheaf.to_localization_presheaf :
  F ⟶ G.localization_presheaf :=
{ app := λ U, CommRing.of_hom $ algebra_map (F.obj U) (localization $ G.obj U),
  naturality' := λ U V i, (is_localization.map_comp (G.map i)).symm }

instance : epi G.to_localization_presheaf :=
@@nat_trans.epi_of_epi_app _ _ G.to_localization_presheaf (λ U, localization.epi' (G.obj U))

variable (F)

/-- Given a submonoid at each of the stalks, we may define a submonoid presheaf consisting of
sections whose restriction onto each stalk falls in the given submonoid. -/
@[simps] noncomputable
def submonoid_presheaf_of_stalk (S : ∀ x : X, submonoid (F.stalk x)) :
  F.submonoid_presheaf :=
{ obj := λ U, ⨅ x : (unop U), submonoid.comap (F.germ x) (S x),
  map := λ U V i, begin
    intros s hs,
    simp only [submonoid.mem_comap, submonoid.mem_infi] at ⊢ hs,
    intro x,
    change (F.map i.unop.op ≫ F.germ x) s ∈ _,
    rw F.germ_res,
    exact hs _,
  end }

noncomputable
instance : inhabited F.submonoid_presheaf := ⟨F.submonoid_presheaf_of_stalk (λ _, ⊥)⟩

/-- The localization of a presheaf of `CommRing`s at locally non-zero-divisor sections. -/
noncomputable
def total_quotient_presheaf : X.presheaf CommRing.{w} :=
(F.submonoid_presheaf_of_stalk (λ x, (F.stalk x)⁰)).localization_presheaf

/-- The map into the presheaf of total quotient rings -/
@[derive epi] noncomputable
def to_total_quotient_presheaf : F ⟶ F.total_quotient_presheaf :=
submonoid_presheaf.to_localization_presheaf _

instance (F : X.sheaf CommRing.{w}) : mono F.presheaf.to_total_quotient_presheaf :=
begin
  apply_with nat_trans.mono_of_mono_app { instances := ff },
  intro U,
  apply concrete_category.mono_of_injective,
  apply is_localization.injective _,
  swap 3, { exact localization.is_localization },
  intros s hs t e,
  apply section_ext F (unop U),
  intro x,
  rw map_zero,
  apply submonoid.mem_infi.mp hs x,
  rw [← map_mul, e, map_zero]
end


end presheaf

end Top
