/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.group.ulift

/-!
# Pi instances for ring

This file defines instances for ring, semiring and related structures on Pi Types
-/

universes u v
variables {α : Type u} {x y : ulift.{v} α}

namespace ulift

instance mul_zero_class [mul_zero_class α] : mul_zero_class (ulift α) :=
by refine_struct { zero := (0 : ulift α), mul := (*), .. }; tactic.pi_instance_derive_field

instance distrib [distrib α] : distrib (ulift α) :=
by refine_struct { add := (+), mul := (*), .. }; tactic.pi_instance_derive_field

instance semiring [semiring α] : semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*), .. };
  tactic.pi_instance_derive_field

instance comm_semiring [comm_semiring α] : comm_semiring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*),  .. };
  tactic.pi_instance_derive_field

instance ring [ring α] : ring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*),
  neg := has_neg.neg, .. }; tactic.pi_instance_derive_field

instance comm_ring [comm_ring α] : comm_ring (ulift α) :=
by refine_struct { zero := (0 : ulift α), one := 1, add := (+), mul := (*),
  neg := has_neg.neg, .. }; tactic.pi_instance_derive_field

end ulift
