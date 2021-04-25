import linear_algebra.basic
import algebra.monoid_algebra
import algebra.module.submodule

universes u v w

class representation (k : Type u) (G : Type v) (M : Type w)
  [semiring k] [monoid G] [add_comm_monoid M]
  [module k M] [distrib_mul_action G M] : Type (max u v w) :=
(smul_smul :  ∀ (g : G) (r : k) (m : M), g • (r • m) = r • (g • m))

section definitions
variables (k : Type u) (G : Type v) (M : Type w)
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [module k M] [distrib_mul_action G M]

structure subrepresentation [representation k G M] extends submodule k M :=
(group_smul_mem' : ∀ (c : G) {x : M}, x ∈ carrier → c • x ∈ carrier)

end definitions
