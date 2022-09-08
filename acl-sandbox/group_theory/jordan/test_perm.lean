/-
Copyright (c) 2022 ACL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ACL
-/

import tactic
import logic.equiv.basic
import .mul_action_finset

variables {α β γ : Type*} [decidable_eq α] [decidable_eq β] [decidable_eq γ]

def equiv_ulift : α ≃ ulift α := {
    to_fun := λ a, {down := a},
    inv_fun := λ b, b.down,
    left_inv := λ a, rfl,
    right_inv := λ b, by simp only [ulift.up_down], }

/- def equiv.perm_ulift : equiv.perm (ulift α) ≃* equiv.perm α := {
to_fun := λ k, {
  to_fun := λ x, (k {down := x}).down,
  inv_fun := λ x, (k.symm {down := x}).down,
  left_inv := λ x,
    by simp only [ulift.down_up, ulift.up_down, k.left_inv, equiv.symm_apply_apply],
  right_inv := λ x,
    by simp only [ulift.down_up, ulift.up_down, k.right_inv, equiv.apply_symm_apply], },
inv_fun := λ k, {
  to_fun := λ x, {down := k x.down},
  inv_fun := λ x, {down := k.symm x.down},
  left_inv := λ x,
    by simp only [ulift.down_up, ulift.up_down, k.left_inv, equiv.symm_apply_apply],
  right_inv := λ x,
    by simp only [ulift.down_up, ulift.up_down, k.right_inv, equiv.apply_symm_apply], },
left_inv := λ k, equiv.perm.ext (λ x,
    by simp only [equiv.coe_fn_mk, ulift.down_inj, embedding_like.apply_eq_iff_eq, ulift.up_down]),
right_inv := λ k, equiv.perm.ext (λ x,by simp only [equiv.coe_fn_mk]),
map_mul' := λ h k, equiv.perm.ext (λ x, by
    simp only [ulift.up_down, equiv.perm.coe_mul, equiv.coe_fn_mk, ulift.down_inj]),
     } -/

def equiv.of_perm_of_equiv (f : α ≃ β) : equiv.perm α ≃* equiv.perm β := {
  map_mul' := λ h k, equiv.perm.ext ( λ x, by simp only [equiv.to_fun_as_coe,
    equiv.equiv_congr_apply_apply, equiv.perm.coe_mul, function.comp_app, equiv.symm_apply_apply] ),
  .. equiv.equiv_congr f f , }

def equiv.of_perm_of_equiv' (f : α ≃ β) : equiv.perm α ≃* equiv.perm β := {
  to_fun := λ k, {
    to_fun := λ x, f (k (f.symm x)),
    inv_fun := λ x, f (k.symm (f.symm x)),
    left_inv := λ x, by simp only [equiv.symm_apply_apply, equiv.apply_symm_apply],
    right_inv := λ x, by simp only [equiv.symm_apply_apply, equiv.apply_symm_apply]},
  inv_fun := λ k, {
    to_fun := λ x, f.symm (k (f x)),
    inv_fun := λ x, f.symm (k.symm (f x)),
    left_inv := λ x, by simp only [equiv.symm_apply_apply, equiv.apply_symm_apply],
    right_inv := λ x, by simp only [equiv.symm_apply_apply, equiv.apply_symm_apply] },
  left_inv := λ k, equiv.perm.ext (λ x, by simp only [equiv.symm_apply_apply, equiv.coe_fn_mk] ),
  right_inv := λ k, equiv.perm.ext (λ x, by simp only [equiv.apply_symm_apply, equiv.coe_fn_mk] ),
  map_mul' := λ h k, equiv.perm.ext (λ x,
    by simp only [equiv.symm_apply_apply, equiv.perm.coe_mul, equiv.coe_fn_mk,
      embedding_like.apply_eq_iff_eq] ), }

lemma equiv.of_perm_of_equiv_trans (f : α ≃ β) (g : β ≃ γ) :
  equiv.of_perm_of_equiv (f.trans g) =
    (equiv.of_perm_of_equiv f).trans (equiv.of_perm_of_equiv g) :=
mul_equiv.ext (λ k, equiv.perm.ext (λx, rfl))

lemma equiv.of_perm_of_equiv_symm (f : α ≃ β):
  equiv.of_perm_of_equiv (f.symm) = (equiv.of_perm_of_equiv f).symm :=
mul_equiv.ext (λ x, equiv.perm.ext (λ x, rfl))

example : equiv.perm α ≃* equiv.perm (ulift α):=
equiv_ulift.of_perm_of_equiv

variables {s : finset α} {f : α ≃ β}

-- f s
example : finset β := s.image f.to_fun

-- s ≃ f s
def f' : s ≃ (s.image f.to_fun) := equiv.subtype_equiv f (λ a,
  by simp only [equiv.to_fun_as_coe, finset.mem_image, embedding_like.apply_eq_iff_eq,
    exists_prop, exists_eq_right])

-- F : equiv.perm s ≃* equiv.perm (f s) := equiv.of_perm_of_equiv f'
example : equiv.perm s ≃* equiv.perm (s.image f.to_fun) := equiv.of_perm_of_equiv (f')

example (g : equiv.perm s) : equiv.perm β :=
  (equiv.of_perm_of_equiv f) (equiv.perm.of_subtype g)

example (g : equiv.perm s) : equiv.perm (s.image f.to_fun) :=
  (equiv.of_perm_of_equiv (f') g)

example (g : equiv.perm s) : equiv.perm β :=
  equiv.perm.of_subtype (equiv.of_perm_of_equiv (f') g : equiv.perm (s.image f.to_fun))

lemma test (g : equiv.perm s) :
  equiv.perm.of_subtype (equiv.of_perm_of_equiv (f') g : equiv.perm (s.image f.to_fun)) =
    (equiv.of_perm_of_equiv f) (equiv.perm.of_subtype g)  :=
begin
  ext,
  cases em (x ∈ s.image f.to_fun) with hx hx',
  { rw equiv.perm.of_subtype_apply_of_mem,
    simp only [equiv.of_perm_of_equiv, f', mul_equiv.has_coe_to_fun ],
    simp only [subtype.coe_mk, equiv.subtype_equiv_symm, equiv.to_fun_as_coe, mul_equiv.coe_mk,
      equiv.equiv_congr_apply_apply, equiv.subtype_equiv_apply, embedding_like.apply_eq_iff_eq],
    rw equiv.perm.of_subtype_apply_of_mem,
    exact hx, },
  { rw equiv.perm.of_subtype_apply_of_not_mem,
    simp only [equiv.of_perm_of_equiv, f', mul_equiv.has_coe_to_fun ],
    simp only [equiv.to_fun_as_coe, mul_equiv.coe_mk, equiv.equiv_congr_apply_apply],
    rw equiv.perm.of_subtype_apply_of_not_mem,
    { simp only [equiv.apply_symm_apply], },
    { intro hx, apply hx', rw ← equiv.apply_symm_apply f x,
      rw finset.mem_image,
      use f.symm x, use hx, refl, },
    exact hx', },
end


example {s' : finset α} (g : equiv.perm α)
  (f : equiv.perm s →* equiv.perm α) (f' : equiv.perm s' →* equiv.perm α) :
  (mul_aut.conj g) • f.range = f'.range := sorry
