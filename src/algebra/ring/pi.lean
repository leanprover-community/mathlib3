import tactic.pi_instances algebra.group.pi algebra.ring.basic
import algebra.module.basic
namespace pi
universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

instance mul_zero_class [Π i, mul_zero_class $ f i] : mul_zero_class (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), mul := (*), .. }; tactic.pi_instance_derive_field

instance distrib [Π i, distrib $ f i] : distrib (Π i : I, f i) :=
by refine_struct { add := (+), mul := (*), .. }; tactic.pi_instance_derive_field

instance semiring [∀ i, semiring $ f i] : semiring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*), .. };
  tactic.pi_instance_derive_field

instance ring [∀ i, ring $ f i] : ring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*),
  neg := has_neg.neg, .. }; tactic.pi_instance_derive_field

instance comm_ring [∀ i, comm_ring $ f i] : comm_ring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*),
  neg := has_neg.neg, .. }; tactic.pi_instance_derive_field

end pi
