/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.fintype.basic
import control.equiv_functor

/-!
# `equiv_functor` instances

We derive some `equiv_functor` instances, to enable `equiv_rw` to rewrite under these functions.
-/

open equiv

instance equiv_functor_unique : equiv_functor unique :=
{ map := λ α β e, equiv.unique_congr e, }

instance equiv_functor_perm : equiv_functor perm :=
{ map := λ α β e p, (e.symm.trans p).trans e }

-- There is a classical instance of `is_lawful_functor finset` available,
-- but we provide this computable alternative separately.
instance equiv_functor_finset : equiv_functor finset :=
{ map := λ α β e s, s.map e.to_embedding, }

instance equiv_functor_fintype : equiv_functor fintype :=
{ map := λ α β e s, by exactI fintype.of_bijective e e.bijective, }
