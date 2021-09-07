/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin
-/

import linear_algebra.tensor_product.construction

section lift

variables {R M N T Q : Type*}
variables [comm_semiring R]
variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid T] [add_comm_monoid Q]
variables [module R M] [module R N] [module R T] [module R Q] [is_tensor_product R M N T]
variables (f : M →ₗ[R] N →ₗ[R] Q)

-- def lift : T →ₗ[R] Q :=
-- { to_fun := _,
--   map_add' := _,
--   map_smul' := _ }

end lift
