import linear_algebra.tensor_product
import deprecated.subring

-- swap these ↑ two imports, and then `foo` will be happy
-- otherwise, get a timeout

import algebra.module.submodule

variables {R M N P Q : Type*} [comm_ring R]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]

open function

lemma injective_iff (f : M →ₗ[R] N) : function.injective f ↔ ∀ m, f m = 0 → m = 0 :=
add_monoid_hom.injective_iff f.to_add_monoid_hom

lemma foo (L : submodule R (unit → R)) :
  injective (tensor_product.map L.subtype L.subtype) :=
(injective_iff _).mpr (sorry)
