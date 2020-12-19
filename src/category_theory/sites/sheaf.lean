import category_theory.sites.sheaf_of_types
import category_theory.concrete_category

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
A sheaf of abelian groups is a presheaf F : C^op => AbGroup such that for every X : AbGroup, the
presheaf of types given by sending U to the homset X -> F U is a sheaf.
https://stacks.math.columbia.edu/tag/00VR
-/



def is_sheaf (P : Cᵒᵖ ⥤ A) : Prop := ∀ X : A,
presieve.is_sheaf J (P ⋙ coyoneda.obj (op X))

end presheaf

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
  simp only [first_map, second_map, fork_map],
  simp only [limit.lift_π, limit.lift_π_assoc, assoc, fan.mk_π_app, subtype.coe_mk,
             subtype.val_eq_coe],
  rw [← P.map_comp, ← op_comp, pullback.condition],
  simp,
end

-- definition 3 in Bhaviks list

def is_sheaf' (P : Cᵒᵖ ⥤ A) : Prop := ∀ (U : C) (R : presieve U) (hR : generate R ∈ J U),
nonempty (is_limit (fork.of_ι _ (w R P)))

theorem is_sheaf_iff_is_sheaf' (P : Cᵒᵖ ⥤ A) :
is_sheaf J P ↔ is_sheaf' J P :=
begin
  sorry
end

end presheaf

end category_theory
