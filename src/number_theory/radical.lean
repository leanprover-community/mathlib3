/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.unique_factorization_domain

variables {M : Type*} [comm_cancel_monoid_with_zero M] [unique_factorization_monoid M]

def radical (x : M) : associates M :=
_
