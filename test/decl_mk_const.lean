-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import tactic.decl_mk_const
import algebra.ordered_ring


open tactic

-- decl_mk_const doesn't yet work; some universe levels don't get replaced correctly.

meta def f : tactic unit :=
do d ← get_decl `le_mul_iff_one_le_left,
   (e, t) ← decl_mk_const d,
   trace t,
   mp ← iff_mpr_core e t,
   apply mp,
   skip

meta def f' : tactic unit :=
do d ← get_decl `le_mul_iff_one_le_left,
   e ← mk_const d.to_name,
   t ← infer_type e,
   trace t,
   mp ← iff_mpr_core e t,
   apply mp,
   skip

set_option pp.universes true

example {a b : ℕ} : b ≤ a * b :=
begin
  -- fails:
  f,
  -- the problem is that the type `t` is computed as:
  --   ∀ {α : Type u} [_inst_1 : linear_ordered_semiring.{?l_1} α] {a b : α}, b > 0 → (b ≤ a * b ↔ 1 ≤ a)
  -- (note the `u` in `{α : Type u}`, which should be `?l_1`)
end

example {a b : ℕ} (ha : a > 0) (hb : b > 0) : b ≤ a * b :=
begin
  f',
  exact hb,
  exact ha,
end
