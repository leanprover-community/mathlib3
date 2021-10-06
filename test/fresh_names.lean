/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.fresh_names

open tactic
open native

example {α β γ δ ε θ} (a : α) (b : β) (c : γ) (d : δ) (e : ε) (f : θ) : true :=
begin
  (do [a, b, c, d, e, f] ← [`a, `b, `c, `d, `e, `f].mmap get_local,
      [na, nb, nc, nd, ne, nf] ← pure $
        [a, b, c, d, e, f].map expr.local_uniq_name,

      let renames : name_map (name ⊕ list name) := rb_map.of_list
        [ (na, sum.inr [`p, `j]),
          (nb, sum.inr [`i, `k]),
          (nc, sum.inr [`i, `k]),
          (nd, sum.inr [`i]),
          (ne, sum.inl `i_2),
          (nf, sum.inl `i_2) ],
      let reserved := name_set.of_list [`i_1],
      rename_fresh renames reserved),

  guard_hyp p : α,
  guard_hyp i : β,
  guard_hyp k : γ,
  guard_hyp i_3 : δ,
  guard_hyp i_2 : θ,
  dedup,
  guard_hyp i_2 : ε,
  guard_hyp i_2_1 : θ,
  trivial
end
