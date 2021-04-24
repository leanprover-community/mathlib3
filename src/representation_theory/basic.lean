import linear_algebra.basic
import algebra.monoid_algebra
import algebra.module.basic

universes u v w

class representation (k : Type u) (G : Type v) (M : Type w)
  [semiring k] [monoid G] [add_comm_monoid M]
  [semimodule k M] [distrib_mul_action G M] : Type (max u v w) :=
(smul_smul :  ∀ (g : G) (r : k) (m : M), g • (r • m) = r • (g • m))

section definitions
variables (k : Type u) (G : Type v) (M : Type w)
variables [semiring k] [monoid G] [add_comm_monoid M]
variables [semimodule k M] [distrib_mul_action G M]

class subrepresentation [representation k G M] extends submodule k M :=
(group_smul_mem' : ∀ (c : G) {x : M}, x ∈ carrier → c • x ∈ carrier)

end definitions
