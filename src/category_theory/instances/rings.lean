/- Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

Introduce CommRing -- the category of commutative rings.

Currently only the basic setup.
-/

import category_theory.instances.monoids
import category_theory.fully_faithful
import category_theory.adjunction
import linear_algebra.multivariate_polynomial
import algebra.ring

universes u v

open category_theory

namespace category_theory.instances

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

instance hom_is_ring_hom (f : R ⟶ S) : is_ring_hom (f : R → S) := f.2

def Int : CommRing := ⟨ℤ, infer_instance⟩

def Int.cast {R : CommRing} : Int ⟶ R := { val := int.cast, property := by apply_instance }

def int.eq_cast' {R : Type u} [ring R] (f : int → R) [is_ring_hom f] : f = int.cast :=
funext $ int.eq_cast f (is_ring_hom.map_one f) (λ _ _, is_ring_hom.map_add f)

def Int.hom_unique {R : CommRing} : unique (Int ⟶ R) :=
{ default := Int.cast,
  uniq := λ f, subtype.ext.mpr $ funext $ int.eq_cast f f.2.map_one f.2.map_add }

/-- The forgetful functor commutative rings to Type. -/
def forget : CommRing.{u} ⥤ Type u :=
{ obj := λ R, R,
  map := λ _ _ f, f }

instance forget.faithful : faithful (forget) := {}

/-- The functor from commutative rings to rings. -/
def to_Ring : CommRing.{u} ⥤ Ring.{u} :=
{ obj := λ X, { α := X.1, str := by apply_instance },
  map := λ X Y f, ⟨ f, by apply_instance ⟩ }

instance to_Ring.faithful : faithful (to_Ring) := {}

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
def forget_to_CommMon : CommRing.{u} ⥤ CommMon.{u} :=
{ obj := λ X, { α := X.1, str := by apply_instance },
  map := λ X Y f, ⟨ f, by apply_instance ⟩ }

instance forget_to_CommMon.faithful : faithful (forget_to_CommMon) := {}

example : faithful (forget_to_CommMon ⋙ CommMon.forget_to_Mon) := by apply_instance

section
open mv_polynomial
local attribute [instance, priority 0] subtype.fintype set_fintype classical.prop_decidable

noncomputable def polynomial : Type u ⥤ CommRing.{u} :=
{ obj := λ α, ⟨mv_polynomial α ℤ, by apply_instance⟩,
  map := λ α β f, ⟨eval₂ C (X ∘ f), by apply_instance⟩,
  map_id' := λ α, subtype.ext.mpr $ funext $ eval₂_eta,
  map_comp' := λ α β γ f g, subtype.ext.mpr $ funext $ λ p,
  by apply mv_polynomial.induction_on p; intros;
    simp only [*, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, comp_val,
      eq_self_iff_true, function.comp_app, types_comp] at * }

@[simp] lemma polynomial_obj_α {α : Type u} :
  (polynomial.obj α).α = mv_polynomial α ℤ := rfl

@[simp] lemma polynomial_map_val {α β : Type u} {f : α → β} :
  (CommRing.polynomial.map f).val = eval₂ C (X ∘ f) := rfl

noncomputable def adj : adjunction polynomial (forget : CommRing ⥤ Type u) :=
adjunction.mk_of_hom_equiv _ _
{ hom_equiv := λ α R,
  { to_fun := λ f, f ∘ X,
    inv_fun := λ f, ⟨eval₂ int.cast f, by apply_instance⟩,
    left_inv := λ f, subtype.ext.mpr $ funext $ λ p,
    begin
      have H0 := λ n, (congr (int.eq_cast' (f.val ∘ C)) (rfl : n = n)).symm,
      have H1 := λ p₁ p₂, (@is_ring_hom.map_add _ _ _ _ f.val f.2 p₁ p₂).symm,
      have H2 := λ p₁ p₂, (@is_ring_hom.map_mul _ _ _ _ f.val f.2 p₁ p₂).symm,
      apply mv_polynomial.induction_on p; intros;
      simp only [*, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
        eq_self_iff_true, function.comp_app, hom_coe_app] at *
    end,
    right_inv := by tidy },
  hom_equiv_naturality_left_symm' := λ X' X Y f g, subtype.ext.mpr $ funext $ λ p,
  begin
    apply mv_polynomial.induction_on p; intros;
    simp only [*, eval₂_mul, eval₂_add, eval₂_C, eval₂_X,
      comp_val, equiv.coe_fn_symm_mk, hom_coe_app, polynomial_map_val,
      eq_self_iff_true, function.comp_app, add_right_inj, types_comp] at *
  end }

end

end CommRing

end category_theory.instances
