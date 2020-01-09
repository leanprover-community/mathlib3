/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import linear_algebra.basic

/-!
# Linear actions

For modules M and N, we can regard a linear map M →ₗ End N as a "linear action" of M on N.
In this file we introduce classes `add_action` and `linear_action` to make it easier to work
with such actions.

## Tags

additive action, linear action
-/

universes u v

section prio
set_option default_priority 100 -- see Note [default priority]
/--
A binary operation representing one type with additive structure acting on another. Note that this
is not in general a group action even if the acting type's additive structure is a group operation.
-/
class add_action (M : Type u) (N : Type v)
  [has_add M] [has_add N] extends has_scalar M N :=
(add_smul : ∀ (m m' : M) (n : N), (m + m') • n = m • n + m' • n)
(smul_add : ∀ (m : M) (n n' : N), m • (n + n') = m • n + m • n')
end prio

@[simp] lemma zero_add_action (M : Type u) (N : Type v)
  [add_monoid M] [add_group N] [add_action M N] (n : N) :
  (0 : M) • n = 0 :=
begin
  have H : (0 : M) • n + (0 : M) • n = (0 : M) • n + 0 := by { rw ←add_action.add_smul, simp, },
  exact add_left_cancel H,
end

@[simp] lemma add_action_zero (M : Type u) (N : Type v)
  [has_add M] [add_group N] [add_action M N] (m : M) :
  m • (0 : N) = 0 :=
begin
  have H : m • (0 : N) + m • (0 : N) = m • (0 : N) + 0 := by { rw ←add_action.smul_add, simp, },
  exact add_left_cancel H,
end

@[simp] lemma add_action_add_smul (M : Type u) (N : Type v)
  [has_add M] [has_add N] [add_action M N] (m m' : M) (n : N) :
  (m + m') • n = m • n + m' • n := add_action.add_smul m m' n

@[simp] lemma add_action_smul_add (M : Type u) (N : Type v)
  [has_add M] [has_add N] [add_action M N] (m : M) (n n' : N) :
  m • (n + n') = m • n + m • n' := add_action.smul_add m n n'

section prio
set_option default_priority 100 -- see Note [default priority]
/--
A binary operation representing one module acting linearly on another.
-/
class linear_action (R : Type u) (M N : Type v)
  [comm_ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  extends add_action M N :=
(smul_smul  : ∀ (r : R) (m : M) (n : N), (r • m) • n = r • (m • n))
(smul_smul' : ∀ (r : R) (m : M) (n : N), m • (r • n) = (r • m) • n)
end prio

@[simp] lemma linear_action_smul_smul (R : Type u) (M N : Type v)
  [comm_ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  [linear_action R M N]
  (r : R) (m : M) (n : N) : (r • m) • n = r • (m • n) := linear_action.smul_smul r m n

@[simp] lemma linear_action_smul_smul' (R : Type u) (M N : Type v)
  [comm_ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  [linear_action R M N]
  (r : R) (m : M) (n : N) : m • (r • n) = (r • m) • n := linear_action.smul_smul' r m n

namespace linear_action

def of_endo_map (R : Type u) (M N : Type v)
  [comm_ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  (α : M →ₗ[R] module.End R N) : linear_action R M N := {
  smul       := λ m n, α m n,
  add_smul   := by { intros, simp only [], rw linear_map.map_add, simp, },
  smul_add   := by { intros, simp, },
  smul_smul  := by { intros, simp only [], rw linear_map.map_smul, simp, },
  smul_smul' := by { intros, simp only [], repeat { rw linear_map.map_smul }, simp, } }

def to_endo_map (R : Type u) (M N : Type v)
  [comm_ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  (α : linear_action R M N) : M →ₗ[R] module.End R N := {
  to_fun  := λ m, {
    to_fun := λ n, m • n,
    add    := by { intros, simp, },
    smul   := by { intros, simp, }, },
  add     := by { intros, ext, simp, },
  smul    := by { intros, ext, simp, } }

end linear_action
