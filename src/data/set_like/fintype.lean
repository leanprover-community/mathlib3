/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.set_like.basic
import data.fintype.powerset
/-!
# Set-like fintype

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains a fintype instance for set-like objects such as subgroups. If `set_like A B`
and `fintype B` then `fintype A`.
-/

namespace set_like

/-- TODO: It should be possible to obtain a computable version of this for most
set_like objects. If we add those instances, we should remove this one. -/
@[nolint dangerous_instance, instance, priority 100]
noncomputable instance {A B : Type*} [fintype B] [set_like A B] : fintype A :=
fintype.of_injective coe set_like.coe_injective

@[nolint dangerous_instance, priority 100] -- See note [lower instance priority]
instance {A B : Type*} [finite B] [set_like A B] : finite A :=
finite.of_injective coe set_like.coe_injective

end set_like
