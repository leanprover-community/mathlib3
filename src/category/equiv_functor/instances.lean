/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import tactic.equiv_rw

/-!
# `equiv_functor` instances

We derive some `equiv_functor` instances, to enable `equiv_rw` to rewrite under these functions.
-/

open equiv

instance equiv_functor_unique : equiv_functor unique :=
{ map := λ α β e, equiv.unique_congr e, }

instance equiv_functor_perm : equiv_functor perm :=
{ map := λ α β e p, (e.symm.trans p).trans e }
