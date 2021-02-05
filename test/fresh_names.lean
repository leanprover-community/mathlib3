/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import tactic.fresh_names

open tactic
open native

example (n m o p : ℕ) : true :=
by do
  [n, m, o, p] ← [`n, `m, `o, `p].mmap get_local,
  [n_uname, m_uname, o_uname, p_uname] ← pure $
    [n, m, o, p].map expr.local_uniq_name,

  let renames := rb_map.of_list
    [ (n_uname, [`p, `j]),
      (m_uname, [`i, `k]),
      (o_uname, [`i, `k]),
      (p_uname, [`i]) ],
  let reserved := name_set.of_list [`i_1],
  rename_fresh renames reserved,

  `[ guard_hyp p : ℕ ],
  `[ guard_hyp i : ℕ ],
  `[ guard_hyp k : ℕ ],
  `[ guard_hyp i_2 : ℕ ],

  exact `(trivial)
