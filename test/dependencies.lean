/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.dependencies

open tactic
open native.rb_map (set_of_list)

namespace native

meta def rb_set.equals {α} (xs ys : rb_set α) : bool :=
xs.fold tt (λ x b, b ∧ ys.contains x) &&
ys.fold tt (λ y b, b ∧ xs.contains y)

end native

open native

example (n m : ℕ) (f : fin n) : let k := m, o := k in o > 0 → true :=
begin
  intros k o h,
  (do [n, m, f, k, o, h] ← [`n, `m, `f, `k, `o, `h].mmap get_local,

      -- hyp_depends_on_locals
      h_dep_m ← hyp_depends_on_locals h [m],
      guard h_dep_m <|> fail! "h_dep_m = {h_dep_m}",
      h_dep_n ← hyp_depends_on_locals h [n],
      guard ¬ h_dep_n <|> fail! "h_dep_n = {h_dep_n}",
      m_dep_n ← hyp_depends_on_locals m [n],
      guard ¬ m_dep_n <|> fail! "m_dep_n = {m_dep_n}",
      f_dep_n ← hyp_depends_on_locals f [n],
      guard f_dep_n <|> fail! "f_dep_n = {f_dep_n}",
      f_dep_n_m ← hyp_depends_on_locals f [n, m],
      guard f_dep_n_m <|> fail! "f_dep_n_m = {f_dep_n_m}",

      -- hyps_depend_on_locals
      dep_fk ← hyps_depend_on_locals [n, m, f, k, o, h] [f, k],
      guard (dep_fk = [ff, ff, ff, ff, tt, tt]) <|> fail! "dep_fk = {dep_fk}",
      dep_m ← hyps_depend_on_locals [n, m, f, k, o, h] [m],
      guard (dep_m = [ff, ff, ff, tt, tt, tt]) <|> fail! "dep_m = {dep_m}",

      -- hyp_depends_on_locals_inclusive
      h_idep_h ← hyp_depends_on_locals_inclusive h [h],
      guard h_idep_h <|> fail! "h_idep_h = {h_idep_h}",
      h_idep_n ← hyp_depends_on_locals_inclusive h [n],
      guard ¬ h_idep_n <|> fail! "h_idep_n = {h_idep_n}",

      -- hyps_depend_on_locals_inclusive
      idep_fk ← hyps_depend_on_locals_inclusive [n, m, f, k, o, h] [f, k],
      guard (idep_fk = [ff, ff, tt, tt, tt, tt]) <|> fail! "idep_fk = {idep_fk}",
      idep_m ← hyps_depend_on_locals_inclusive [n, m, f, k, o, h] [m],
      guard (idep_m = [ff, tt, ff, tt, tt, tt]) <|> fail! "idep_m = {idep_m}",

      -- dependency_set_of_hyp
      f_dep_set ← dependency_set_of_hyp f,
      guard (f_dep_set.equals (set_of_list [n])) <|> fail! "f_dep_set = {f_dep_set}",
      h_dep_set ← dependency_set_of_hyp h,
      guard (h_dep_set.equals (set_of_list [o, k, m])) <|> fail! "h_dep_set = {h_dep_set}",
      n_dep_set ← dependency_set_of_hyp n,
      guard n_dep_set.empty <|> fail! "n_dep_set = {n_dep_set}",

      -- dependency_sets_of_hyps
      fhn_dep_sets ← dependency_sets_of_hyps [f, h, n],
      guard ((fhn_dep_sets.zip_with rb_set.equals ([[n], [o, k, m], []].map set_of_list)).band) <|>
        fail! "fhn_dep_sets = {fhn_dep_sets}",

      -- dependency_set_of_hyp_inclusive
      f_idep_set ← dependency_set_of_hyp_inclusive f,
      guard (f_idep_set.equals (set_of_list [n, f])) <|> fail! "f_idep_set = {f_idep_set}",
      h_idep_set ← dependency_set_of_hyp_inclusive h,
      guard (h_idep_set.equals (set_of_list [o, k, m, h])) <|> fail! "h_idep_set = {h_idep_set}",
      n_idep_set ← dependency_set_of_hyp_inclusive n,
      guard (n_idep_set.equals (set_of_list [n])) <|> fail! "n_idep_set = {n_idep_set}",

      -- dependency_sets_of_hyps_inclusive
      fhn_idep_sets ← dependency_sets_of_hyps_inclusive [f, h, n],
      guard ((fhn_idep_sets.zip_with rb_set.equals ([[f, n], [h, o, k, m], [n]].map set_of_list)).band) <|>
        fail! "fhn_idep_sets = {fhn_idep_sets}",

      -- reverse_dependencies_of_hyps
      n_revdep_set ← reverse_dependencies_of_hyps [n],
      guard (n_revdep_set = [f]) <|> fail! "n_revdep_set = {n_revdep_set}",
      n_f_revdep_set ← reverse_dependencies_of_hyps [n, f],
      guard (n_f_revdep_set = []) <|> fail! "n_f_revdep_set = {n_f_revdep_set}",
      m_revdep_set ← reverse_dependencies_of_hyps [m],
      guard (m_revdep_set = [k, o, h]) <|> fail! "m_revdep_set = {m_revdep_set}",
      m_o_revdep_set ← reverse_dependencies_of_hyps [m, o],
      guard (m_o_revdep_set = [k, h]) <|> fail! "m_o_revdep_set = {m_o_revdep_set}",
      f_revdep_set ← reverse_dependencies_of_hyps [f],
      guard (f_revdep_set = []) <|> fail! "f_revdep_set = {f_revdep_set}",

      -- reverse_dependencies_of_hyps_inclusive
      n_irevdep_set ← reverse_dependencies_of_hyps_inclusive [n],
      guard (n_irevdep_set = [n, f]) <|> fail! "n_irevdep_set = {n_irevdep_set}",
      n_f_irevdep_set ← reverse_dependencies_of_hyps_inclusive [n, f],
      guard (n_f_irevdep_set = [n, f]) <|> fail! "n_f_irevdep_set = {n_f_irevdep_set}",
      m_irevdep_set ← reverse_dependencies_of_hyps_inclusive [m],
      guard (m_irevdep_set = [m, k, o, h]) <|> fail! "m_irevdep_set = {m_irevdep_set}",
      m_o_irevdep_set ← reverse_dependencies_of_hyps_inclusive [m, o],
      guard (m_o_irevdep_set = [m, k, o, h]) <|> fail! "m_o_irevdep_set = {m_o_irevdep_set}",
      f_irevdep_set ← reverse_dependencies_of_hyps_inclusive [f],
      guard (f_irevdep_set = [f]) <|> fail! "f_irevdep_set = {f_irevdep_set}",

      -- revert_lst'
      (n_reverted₁, reverted) ← revert_lst' [n, m],
      guard (n_reverted₁ = 6) <|> fail! "n_reverted₁ = {n_reverted₁}",
      guard
        (reverted.map expr.local_uniq_name =
        [n, m, f, k, o, h].map expr.local_uniq_name),
      `[ guard_target ∀ (n m : ℕ) (f : fin n), let k := m, o := k in o > 0 → true ],

      intros,
      [n, m, f, k, o, h] ← [`n, `m, `f, `k, `o, `h].mmap get_local,

      -- revert_reverse_dependencies_of_hyps
      n_reverted₂ ← revert_reverse_dependencies_of_hyps [n, k],
      guard (n_reverted₂ = 3) <|> fail! "n_reverted₂ = {n_reverted₂}",
      `[ guard_hyp n : ℕ ],
      `[ guard_hyp m : ℕ ],
      `[ guard_hyp k : ℕ := m ],
      `[ guard_target ∀ (f : fin n), let o := k in o > 0 → true ],

      pure ()
  ),
  intros,
  trivial
end
