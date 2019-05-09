/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.multiset

def free_comm_monoid (α) := multiset α

namespace free_comm_monoid
variables {α : Type*}

instance : comm_monoid (free_comm_monoid α) :=
{ mul := λ x y, multiset.union x y,
  mul_assoc := _,
  one := [],
  one_mul := _,
  mul_one := _,
  mul_comm := _ }

end free_comm_monoid
