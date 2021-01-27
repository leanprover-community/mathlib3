/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import category_theory.sites.sheaf_of_types
import category_theory.concrete_category

/-!
# Sheaves taking values in a category

If C is a category with a Grothendieck topology, we define the notion of a sheaf
taking values in an arbitrary category `A`. We follow the definition in
https://stacks.math.columbia.edu/tag/00VR , noting that the presheaf of sets "defined above"
can be seen in the comments between tags 00VQ and 00VR on the
page https://stacks.math.columbia.edu/tag/00VL . The advantage of this definition is that
we need no assumptions whatsoever on `A` other than the assumption that the morphisms
in `C` and `A` live in the same universe.

TODO: Everything.

-/
-- sheaves taking values in objects of a category

universes v v' u' u

noncomputable theory

namespace category_theory

open opposite category_theory category limits sieve classical

namespace presheaf

variables {C : Type u} [category.{v} C]

variables {A : Type u'} [category.{v} A]

variables (J : grothendieck_topology C)

-- We follow https://stacks.math.columbia.edu/tag/00VL definition 00VR

/-
A sheaf of A is a presheaf P : C^op => A such that for every X : A, the
presheaf of types given by sending U : C to Hom_{A}(X, P U) is a sheaf of types.

https://stacks.math.columbia.edu/tag/00VR
-/

def is_sheaf (P : Cᵒᵖ ⥤ A) : Prop := ∀ X : A,
presieve.is_sheaf J (P ⋙ coyoneda.obj (op X))


/-!

## practice

-/

#check coyoneda.obj (op punit.{v+1})
#check iso_comp_punit

lemma practice (P : Cᵒᵖ ⥤ Type v) : P ≅ (P ⋙ coyoneda.obj (op punit.{v+1})) :=
{ hom := { app := λ X a _, a },
  inv := { app := λ X f, f punit.star},-- Hom (*, P X) → P X},
  hom_inv_id' := by tidy,
  inv_hom_id' := by tidy }

example (P Q : Cᵒᵖ ⥤ Type v) (h : P ≅ Q) : presieve.is_sheaf J P → presieve.is_sheaf J Q :=
begin
  exact presieve.is_sheaf_iso J h,
end

end presheaf

variables {C : Type u} [category.{v} C]
variables (J : grothendieck_topology C)
variables (A : Type u') [category.{v} A]

/-- The category of sheaves on a grothendieck topology. -/
@[derive category]
def Sheaf : Type* :=
{P : Cᵒᵖ ⥤ A // presheaf.is_sheaf J P}

-- instance : inhabited (Sheaf (⊥ : grothendieck_topology C)) :=
-- ⟨⟨(functor.const _).obj punit,
--   λ X S hS,
--   begin
--     simp only [grothendieck_topology.bot_covering] at hS,
--     subst hS,
--     apply presieve.is_sheaf_for_top_sieve,
--   end⟩⟩

/-- The inclusion functor from sheaves to presheaves. -/
@[simps {rhs_md := semireducible}, derive [full, faithful]]
def Sheaf_to_presheaf : Sheaf J A ⥤ (Cᵒᵖ ⥤ A) :=
full_subcategory_inclusion (presheaf.is_sheaf J)

theorem Sheaf_is_SheafOfTypes (P : Cᵒᵖ ⥤ Type v) (hP : presheaf.is_sheaf J P) :
  presieve.is_sheaf J P :=
begin
  specialize hP punit,
  apply presieve.is_sheaf_iso J,
  apply practice,
end


theorem Sheaf_of_types_equiv_Sheaf : Sheaf J (Type v) ≌ SheafOfTypes J :=
{ functor := { obj := λ S, ⟨S.1, _⟩,
    map := _,
    map_id' := _,
    map_comp' := _ },
  inverse := _,
  unit_iso := _,
  counit_iso := _,
  --functor_unit_iso_comp' := _ }
}

end category_theory

namespace category_theory

open opposite category_theory category limits sieve classical

namespace presheaf

-- under here is the equalizer story, which is equivalent if A has products (and doesn't
-- make sense otherwise). It's described between 00VQ and 00VR in stacks.
-- we need [category.{u} A] possibly

variables {C : Type v} [small_category C] [has_pullbacks C]

variables {A : Type u} [category.{v} A] [has_products A]

variables (J : grothendieck_topology C)

variables {U : C} (R : presieve U)

variables (P : Cᵒᵖ ⥤ A)

def first_obj : A :=
∏ (λ (f : Σ V, {f : V ⟶ U // R f}), P.obj (op f.1))

/--
The rightmost object of the fork diagram of https://stacks.math.columbia.edu/tag/00VM, which
contains the data used to check a family of elements for a presieve is compatible.
-/
def second_obj : A :=
∏ (λ (fg : (Σ V, {f : V ⟶ U // R f}) × (Σ W, {g : W ⟶ U // R g})),
  P.obj (op (pullback fg.1.2.1 fg.2.2.1)))

/-- The map `pr₀*` of https://stacks.math.columbia.edu/tag/00VL. -/
def first_map : first_obj R P ⟶ second_obj R P :=
pi.lift (λ fg, pi.π _ _ ≫ P.map pullback.fst.op)

/-- The map `pr₁*` of https://stacks.math.columbia.edu/tag/00VL. -/
def second_map : first_obj R P ⟶ second_obj R P :=
pi.lift (λ fg, pi.π _ _ ≫ P.map pullback.snd.op)

/--
The left morphism of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of https://stacks.math.columbia.edu/tag/00VM.
-/
def fork_map : P.obj (op U) ⟶ first_obj R P :=
pi.lift (λ f, P.map f.2.1.op)

lemma w : fork_map R P ≫ first_map R P = fork_map R P ≫ second_map R P :=
begin
  apply limit.hom_ext,
  rintro ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩,
  simp only [first_map, second_map, fork_map, limit.lift_π, limit.lift_π_assoc, assoc,
    fan.mk_π_app, subtype.coe_mk, subtype.val_eq_coe],
  rw [← P.map_comp, ← op_comp, pullback.condition],
  simp,
end

def is_sheaf' (P : Cᵒᵖ ⥤ A) : Prop := ∀ (U : C) (R : presieve U) (hR : generate R ∈ J U),
nonempty (is_limit (fork.of_ι _ (w R P)))

theorem is_sheaf_iff_is_sheaf' (P : Cᵒᵖ ⥤ A) :
is_sheaf J P ↔ is_sheaf' J P :=
begin
  split,
  { sorry },
  { sorry }
end

end presheaf

end category_theory
