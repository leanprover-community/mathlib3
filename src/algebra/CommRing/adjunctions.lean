/- Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/

import algebra.CommRing.basic
import category_theory.adjunction.basic
import data.mv_polynomial

universe u

open mv_polynomial
open category_theory

namespace CommRing

local attribute [instance, priority 0] classical.prop_decidable

noncomputable def polynomial_ring : Type u ⥤ CommRing.{u} :=
{ obj := λ α, ⟨mv_polynomial α ℤ⟩,
  map := λ α β f, ⟨rename f, by apply_instance⟩ }

@[simp] lemma polynomial_ring_obj_α {α : Type u} :
  (polynomial_ring.obj α).α = mv_polynomial α ℤ := rfl

@[simp] lemma polynomial_ring_map_val {α β : Type u} {f : α → β} :
  (polynomial_ring.map f).val = rename f := rfl

noncomputable def adj : polynomial_ring ⊣ (forget : CommRing ⥤ Type u) :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ α R,
  { to_fun    := λ f, f ∘ X,
    inv_fun   := λ f, ⟨eval₂ (λ n : ℤ, (n : R)) f, by { unfold_coes, apply_instance }⟩,
    left_inv  := λ f, bundled.hom_ext (@eval₂_hom_X _ _ _ _ _ _ f.val _),
    right_inv := λ x, by { ext1, unfold_coes, simp only [function.comp_app, eval₂_X] } },
  hom_equiv_naturality_left_symm' :=
  λ X X' Y f g, by { ext1, dsimp, apply eval₂_cast_comp } }.

end CommRing
