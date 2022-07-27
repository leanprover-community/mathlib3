/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.field.basic
import algebra.ring.opposite

/-!
# Field structure on the multiplicative opposite
-/

variables (α : Type*)

namespace mul_opposite

instance [division_ring α] : division_ring αᵐᵒᵖ :=
{ .. mul_opposite.group_with_zero α, .. mul_opposite.ring α }

instance [field α] : field αᵐᵒᵖ :=
{ .. mul_opposite.division_ring α, .. mul_opposite.comm_ring α }

end mul_opposite
