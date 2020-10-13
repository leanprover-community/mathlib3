/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/

import data.int.basic

/-!
# IMO 1981 Q3

Determine the maximum value of `m ^ 2 + n ^ 2`, where `m` and `n` are integers in
`{1, 2, ..., 1981}` and `(n ^ 2 - m * n - m ^ 2) ^ 2 = 1`.
-/

/-
First, define the problem in terms of finding the maximum of a set.
-/

def up_to_1981 : set ℤ := {n : ℤ | 0 < n ∧ n < 1982}

def problem_predicate (m n : ℤ) : Prop := (n ^ 2 - m * n - m ^ 2) ^ 2 = 1

def specified_set : set ℤ :=
{k : ℤ | ∃ m : up_to_1981, ∃ n : up_to_1981, k = m ^ 2 + n ^ 2 ∧ problem_predicate m n}

/-
Next, prove some basic statements for pairs of integers that satisfy the predicate.
-/
