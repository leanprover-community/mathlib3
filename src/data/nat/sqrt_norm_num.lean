/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.norm_num
import data.nat.sqrt

/-! ### `norm_num` plugin for `sqrt`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The `norm_num` plugin evaluates `sqrt` by bounding it between consecutive integers.
-/

namespace norm_num
open tactic nat

lemma is_sqrt {n a a2 b : ℕ}
  (ha2 : a * a = a2) (hb : a2 + b = n) (hle : b ≤ bit0 a) : sqrt n = a :=
by { rw [← hb, ← ha2, ← pow_two], exact sqrt_add_eq' _ hle }

/-- Given `n` provides `(a, ⊢ nat.sqrt n = a)`. -/
meta def prove_sqrt (ic : instance_cache) (n : expr) : tactic (instance_cache × expr × expr) := do
  nn ← n.to_nat,
  let na := nn.sqrt,
  (ic, a) ← ic.of_nat na,
  (ic, a2, ha2) ← prove_mul_nat ic a a,
  (ic, b) ← ic.of_nat (nn - na*na),
  (ic, hb) ← prove_add_nat ic a2 b n,
  (ic, hle) ← prove_le_nat ic b (`(bit0:ℕ→ℕ).mk_app [a]),
  pure (ic, a, `(@is_sqrt).mk_app [n, a, a2, b, ha2, hb, hle])

/-- A `norm_num` plugin for `sqrt n` when `n` is a numeral. -/
@[norm_num] meta def eval_sqrt : expr → tactic (expr × expr)
| `(sqrt %%en) := do
    n ← en.to_nat,
    match n with
    | 0 := pure (`(0:ℕ), `(sqrt_zero))
    | _ := do
      c ← mk_instance_cache `(ℕ),
      prod.snd <$> prove_sqrt c en
    end
| _ := failed

end norm_num
