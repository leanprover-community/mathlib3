/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.multiset

def free_comm_monoid (α) := multiset α

namespace free_comm_monoid
variables {α}

instance : comm_monoid (free_comm_monoid α)

end free_comm_monoid
