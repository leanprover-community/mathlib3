import tactic.mk_iff_of_inductive_prop

import data.list data.list.perm data.multiset

run_cmd tactic.mk_iff_of_inductive_prop `list.chain `test.chain_iff

run_cmd tactic.mk_iff_of_inductive_prop `false    `test.false_iff

run_cmd tactic.mk_iff_of_inductive_prop `true     `test.true_iff

run_cmd tactic.mk_iff_of_inductive_prop `nonempty `test.non_empty_iff

run_cmd tactic.mk_iff_of_inductive_prop `and      `test.and_iff

run_cmd tactic.mk_iff_of_inductive_prop `or       `test.or_iff

run_cmd tactic.mk_iff_of_inductive_prop `eq       `test.eq_iff

run_cmd tactic.mk_iff_of_inductive_prop `heq      `test.heq_iff

run_cmd tactic.mk_iff_of_inductive_prop `list.perm  `test.perm_iff

run_cmd tactic.mk_iff_of_inductive_prop `list.pairwise  `test.pairwise_iff

inductive test.is_true (p : Prop) : Prop
| triviality : p → test.is_true

run_cmd tactic.mk_iff_of_inductive_prop `test.is_true `test.is_true_iff
