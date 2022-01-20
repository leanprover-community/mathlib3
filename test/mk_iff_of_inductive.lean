import data.list
import data.list.perm
import data.multiset.basic

mk_iff_of_inductive_prop list.chain test.chain_iff

mk_iff_of_inductive_prop false    test.false_iff

mk_iff_of_inductive_prop true     test.true_iff

mk_iff_of_inductive_prop nonempty test.non_empty_iff

mk_iff_of_inductive_prop and      test.and_iff

mk_iff_of_inductive_prop or       test.or_iff

mk_iff_of_inductive_prop eq       test.eq_iff

mk_iff_of_inductive_prop heq      test.heq_iff

mk_iff_of_inductive_prop list.perm  test.perm_iff

mk_iff_of_inductive_prop list.pairwise  test.pairwise_iff

inductive test.is_true (p : Prop) : Prop
| triviality : p → test.is_true

mk_iff_of_inductive_prop test.is_true test.is_true_iff

@[mk_iff] structure foo (m n : ℕ) : Prop :=
(equal : m = n)
(sum_eq_two : m + n = 2)

example (m n : ℕ) : foo m n ↔ m = n ∧ m + n = 2 := foo_iff m n

@[mk_iff bar] structure foo2 (m n : ℕ) : Prop :=
(equal : m = n)
(sum_eq_two : m + n = 2)

example (m n : ℕ) : foo2 m n ↔ m = n ∧ m + n = 2 := bar m n
