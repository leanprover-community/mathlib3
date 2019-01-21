/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

Introduce CommRing -- the category of commutative rings.

Currently only the basic setup.
-/

import category_theory.examples.monoids
import category_theory.fully_faithful
import category_theory.adjunction
import linear_algebra.multivariate_polynomial
import algebra.ring

universes u v

open category_theory

namespace category_theory.examples

/-- The category of rings. -/
@[reducible] def Ring : Type (u+1) := bundled ring

instance (x : Ring) : ring x := x.str

instance concrete_is_ring_hom : concrete_category @is_ring_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

instance Ring_hom_is_ring_hom {R S : Ring} (f : R ⟶ S) : is_ring_hom (f : R → S) := f.2

/-- The category of commutative rings. -/
@[reducible] def CommRing : Type (u+1) := bundled comm_ring

instance (x : CommRing) : comm_ring x := x.str

-- Here we don't use the `concrete` machinery,
-- because it would require introducing a useless synonym for `is_ring_hom`.
instance : category CommRing :=
{ hom := λ R S, { f : R → S // is_ring_hom f },
  id := λ R, ⟨ id, by resetI; apply_instance ⟩,
  comp := λ R S T g h, ⟨ h.1 ∘ g.1, begin haveI := g.2, haveI := h.2, apply_instance end ⟩ }

namespace CommRing
variables {R S T : CommRing.{u}}

@[simp] lemma id_val : subtype.val (𝟙 R) = id := rfl
@[simp] lemma comp_val (f : R ⟶ S) (g : S ⟶ T) :
  (f ≫ g).val = g.val ∘ f.val := rfl

instance hom_coe : has_coe_to_fun (R ⟶ S) :=
{ F := λ f, R → S,
  coe := λ f, f.1 }

@[simp] lemma hom_coe_app (f : R ⟶ S) (r : R) : f r = f.val r := rfl

@[extensionality] lemma hom_ext {f : R ⟶ S} {g : R ⟶ S} : f = g ↔ f.val = g.val :=
@subtype.ext _ _ f g

instance hom_is_ring_hom (f : R ⟶ S) : is_ring_hom (f : R → S) := f.2

/-- The forgetful functor to Type. -/
def forget : CommRing.{u} ⥤ Type u :=
{ obj := λ R, R,
  map := λ _ _ f, f }

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
def forget_to_CommMon : CommRing.{u} ⥤ CommMon.{u} :=
{ obj := λ X, { α := X.1, str := by apply_instance },
  map := λ X Y f, ⟨ f, by apply_instance ⟩ }

instance : faithful (forget_to_CommMon) := {}

example : faithful (forget_to_CommMon ⋙ CommMon.forget_to_Mon) := by apply_instance

section
open mv_polynomial
local attribute [instance, priority 0] subtype.fintype set_fintype classical.prop_decidable

noncomputable def polynomial : Type u ⥤ CommRing.{u} :=
{ obj := λ α, ⟨mv_polynomial α ℤ, by apply_instance⟩,
  map := λ α β f, ⟨eval₂ C (X ∘ f), by apply_instance⟩,
  map_id' := λ α, hom_ext.mpr $ funext $ eval₂_eta,
  map_comp' := λ α β γ f g,
  begin
    rw hom_ext,
    funext p,
    apply mv_polynomial.induction_on p;
    { intros,
      simp [eval₂_add, eval₂_mul, *] at * {contextual := tt} }
  end }

def adj : adjunction polynomial (forget : CommRing ⥤ Type u) :=
{ hom_equiv := λ α R,
  { to_fun := λ f, f ∘ X,
    inv_fun := λ f, ⟨eval₂ int.cast f, by apply_instance⟩,
    left_inv := λ f, hom_ext.mpr $
    begin
      ext1 p,
      apply mv_polynomial.induction_on p,
      all_goals { intros,
        simp [eval₂_add, eval₂_mul, *] at * {contextual := tt} },
      { symmetry,
        convert int.eq_cast (f.val ∘ C) _ _ _,
        simpa using f.2.map_one,
        intros, simpa using @is_ring_hom.map_add _ _ _ _ f.1 f.2 _ _, },
      simpa using (@is_ring_hom.map_add _ _ _ _ f.1 f.2 _ _).symm,
      simpa using (@is_ring_hom.map_mul _ _ _ _ f.1 f.2 _ _).symm
    end,
    right_inv := by tidy },
  unit :=
  { app := λ α, mv_polynomial.X,
    naturality' := λ α β f, funext $ λ a : α,
    begin dsimp [polynomial, forget], convert eval₂_eta,  end },
  counit :=
  { app := λ R, ⟨eval₂ int.cast id, by apply_instance⟩,
    naturality' := λ R S f, hom_ext.mpr $ funext $ λ p : mv_polynomial R ℤ,
    begin
      dsimp [polynomial, forget] at *,
      apply mv_polynomial.induction_on p,
      all_goals { intros,
        simp [eval₂_add, eval₂_mul, *] at * {contextual := tt} },
      {  },
      repeat {sorry}
    end }, }

end

end CommRing

end category_theory.examples
