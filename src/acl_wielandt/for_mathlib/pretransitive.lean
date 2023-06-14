/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import group_theory.group_action.basic
-- import group_theory.group_action.defs
-- import group_theory.group_action.sub_mul_action
-- import group_theory.subgroup.pointwise

/-! # Complements to pretransitive actions

Given `mul_action G X` where `G` is a group,

- `is_pretransitive.mk_base G a` shows that `is_pretransitive G X`
iff every element is translated from `a`

- `orbit.is_pretransitive_iff G a` shows that `is_pretransitive G X`
iff the `orbit G a` is full.

## TODO

They should probably go to `group_theory.group_action.defs` and `group.theory.group_action.basic`
respectively.

-/
variables (G : Type*) [group G] {X : Type*} [mul_action G X]

namespace mul_action

open mul_action

/-- An action is pretransitive iff every element is translated from a given one-/
variable{G}

lemma is_pretransitive.mk_base_iff (a : X) :
  is_pretransitive G X ↔ ∀ (x : X), ∃ (g : G), g • a = x :=
begin
  split,
  { intros hG x, let hG_eq := hG.exists_smul_eq,
    exact hG_eq a x },
  { intro hG,
    apply is_pretransitive.mk,
    intros x y,
    obtain ⟨g, hx⟩ := hG x,
    obtain ⟨h, hy⟩ := hG y,
    use h * g⁻¹,
    rw ← hx, rw [smul_smul, inv_mul_cancel_right],
    exact hy }
end

lemma is_pretransitive.mk_base (a : X) (hG : ∀ (x : X), ∃ (g : G), g • a = x) :
  is_pretransitive G X :=
begin
  apply is_pretransitive.mk,
  intros x y,
  obtain ⟨g, hx⟩ := hG x,
  obtain ⟨h, hy⟩ := hG y,
  use h * g⁻¹,
  rw ← hx, rw [smul_smul, inv_mul_cancel_right],
  exact hy
end

/-- An action is pretransitive iff the orbit of every given element is full -/
lemma orbit.is_pretransitive_iff (a : X) :
  orbit G a = ⊤ ↔ is_pretransitive G X :=
begin
  rw is_pretransitive.mk_base_iff a,
  rw set.ext_iff ,
  apply forall_congr,
  intro x,
  simp_rw [set.top_eq_univ, set.mem_univ, iff_true],
  rw mem_orbit_iff,
end

end mul_action
