/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import linear_algebra.basic

/-!
# Linear actions

For modules M and N, we can regard a linear map M →ₗ End N as a "linear action" of M on N.
In this file we introduce the class `linear_action` to make it easier to work with such actions.

## Tags

linear action
-/

universes u v

section linear_action

variables (R : Type u) (M N : Type v)
variables [comm_ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]

section prio
set_option default_priority 100 -- see Note [default priority]
/--
A binary operation representing one module acting linearly on another.
-/
class linear_action :=
(act      : M → N → N)
(add_act  : ∀ (m m' : M) (n : N), act (m + m') n = act m n + act m' n)
(act_add  : ∀ (m : M) (n n' : N), act m (n + n') = act m n + act m n')
(act_smul : ∀ (r : R) (m : M) (n : N), act (r • m) n = r • (act m n))
(smul_act : ∀ (r : R) (m : M) (n : N), act m (r • n) = act (r • m) n)
end prio

@[simp] lemma zero_linear_action [linear_action R M N] (n : N) :
  linear_action.act R (0 : M) n = 0 :=
begin
  let z := linear_action.act R (0 : M) n,
  have H : z + z = z + 0 := by { rw ←linear_action.add_act, simp, },
  exact add_left_cancel H,
end

@[simp] lemma linear_action_zero [linear_action R M N] (m : M) :
  linear_action.act R m (0 : N) = 0 :=
begin
  let z := linear_action.act R m (0 : N),
  have H : z + z = z + 0 := by { rw ←linear_action.act_add, simp, },
  exact add_left_cancel H,
end

@[simp] lemma linear_action_add_act [linear_action R M N] (m m' : M) (n : N) :
  linear_action.act R (m + m') n = linear_action.act R m n +
                                   linear_action.act R m' n :=
linear_action.add_act m m' n

@[simp] lemma linear_action_act_add [linear_action R M N] (m : M) (n n' : N) :
  linear_action.act R m (n + n') = linear_action.act R m n +
                                   linear_action.act R m n' :=
linear_action.act_add m n n'

@[simp] lemma linear_action_act_smul [linear_action R M N] (r : R) (m : M) (n : N) :
  linear_action.act R (r • m) n = r • (linear_action.act R m n) :=
linear_action.act_smul r m n

@[simp] lemma linear_action_smul_act [linear_action R M N] (r : R) (m : M) (n : N) :
  linear_action.act R m (r • n) = linear_action.act R (r • m) n :=
linear_action.smul_act r m n

end linear_action

namespace linear_action

variables (R : Type u) (M N : Type v)
variables [comm_ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]

/--
A linear map to the endomorphism algebra yields a linear action.
-/
def of_endo_map (α : M →ₗ[R] module.End R N) : linear_action R M N :=
{ act      := λ m n, α m n,
  add_act  := by { intros, rw linear_map.map_add, simp, },
  act_add  := by { intros, simp, },
  act_smul := by { intros, rw linear_map.map_smul, simp, },
  smul_act := by { intros, repeat { rw linear_map.map_smul }, simp, } }

/--
A linear action yields a linear map to the endomorphism algebra.
-/
def to_endo_map (α : linear_action R M N) : M →ₗ[R] module.End R N :=
{ to_fun  := λ m,
  { to_fun    := λ n, linear_action.act R m n,
    map_add'  := by { intros, simp, },
    map_smul' := by { intros, simp, }, },
  map_add'  := by { intros, ext, simp, },
  map_smul' := by { intros, ext, simp, } }

end linear_action
