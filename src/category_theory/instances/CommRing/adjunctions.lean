/- Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/

import category_theory.instances.CommRing.basic
import category_theory.adjunction
import data.mv_polynomial

universe u

open mv_polynomial
open category_theory

namespace CommRing

local attribute [instance, priority 0] subtype.fintype set_fintype classical.prop_decidable

noncomputable def polynomial_ring : Type u ⥤ CommRing.{u} :=
{ obj := λ α, ⟨mv_polynomial α ℤ, by apply_instance⟩,
  map := λ α β f, ⟨eval₂ C (X ∘ f), by apply_instance⟩,
  map_id' := λ α, subtype.ext.mpr $ funext $ eval₂_eta,
  map_comp' := λ α β γ f g, subtype.ext.mpr $ funext $ λ p,
  by apply mv_polynomial.induction_on p; intros;
    simp only [*, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, comp_val,
      eq_self_iff_true, function.comp_app, types_comp] at * }

@[simp] lemma polynomial_ring_obj_α {α : Type u} :
  (polynomial_ring.obj α).α = mv_polynomial α ℤ := rfl

@[simp] lemma polynomial_ring_map_val {α β : Type u} {f : α → β} :
  (polynomial_ring.map f).val = eval₂ C (X ∘ f) := rfl

lemma hom_coe_app' {R S : CommRing} (f : R ⟶ S) (r : R) : f r = f.val r := rfl
-- this is usually a bad idea, as it forgets that `f` is ring homomorphism
local attribute [simp] hom_coe_app'

noncomputable def adj : polynomial_ring ⊣ (forget : CommRing ⥤ Type u) :=
adjunction.mk_of_hom_equiv
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
        eq_self_iff_true, function.comp_app, hom_coe_app'] at *
    end,
    right_inv := by tidy },
  hom_equiv_naturality_left_symm' := λ X' X Y f g, subtype.ext.mpr $ funext $ λ p,
  begin
    apply mv_polynomial.induction_on p; intros;
    simp only [*, eval₂_mul, eval₂_add, eval₂_C, eval₂_X,
      comp_val, equiv.coe_fn_symm_mk, hom_coe_app, polynomial_ring_map_val,
      eq_self_iff_true, function.comp_app, add_right_inj, types_comp] at *
  end }

end CommRing
