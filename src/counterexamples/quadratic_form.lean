/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.quadratic_form.basic
import algebra.char_p.two
import data.zmod.basic

/-!
# `quadratic_form R M` and `subtype bilin_form.is_symm` are distinct notions in characteristic 2

The main result of this file is `bilin_form.not_inj_on_to_quadratic_form_is_symm`.

The counterexample we use is $B (x, y) (x', y') ↦ xy' + x'y$ where `x y x' y' : zmod 2`.
-/

variables (F : Type*) [nontrivial F] [comm_ring F] [char_p F 2]

open bilin_form

/-- The bilinear form we will use as a counterexample, over some field `F` of characteristic two. -/
def B : bilin_form F (F × F) :=
bilin_form.lin_mul_lin (linear_map.fst _ _ _) (linear_map.snd _ _ _)
 + bilin_form.lin_mul_lin (linear_map.snd _ _ _) (linear_map.fst _ _ _)

@[simp]
lemma B_apply (x y : F × F) : B F x y = x.1 * y.2 + x.2 * y.1 := rfl

lemma is_symm_B : (B F).is_symm := λ x y, by simp [mul_comm, add_comm]

lemma is_alt_B : (B F).is_alt := λ x, by simp [mul_comm, char_two.add_self_eq_zero (x.1 * x.2)]

lemma B_ne_zero : B F ≠ 0 := λ h, by simpa using bilin_form.congr_fun h (1, 0) (1, 1)

/-- `bilin_form.to_quadratic_form` is not injective on symmetric bilinear forms.

This disproves a weaker version of `quadratic_form.associated_left_inverse`.
-/
lemma {u} bilin_form.not_inj_on_to_quadratic_form_is_symm :
  ¬∀ {R M : Type u} [semiring R] [add_comm_monoid M],
    by exactI ∀ [module R M],
    by exactI set.inj_on
      (to_quadratic_form : bilin_form R M → quadratic_form R M)
      { B | B.is_symm }:=
begin
  intro h,
  let F := ulift.{u} (zmod 2),
  apply B_ne_zero F,
  apply h (is_symm_B F) (is_symm_zero),
  rw [bilin_form.to_quadratic_form_zero, bilin_form.to_quadratic_form_eq_zero],
  exact is_alt_B F,
end
