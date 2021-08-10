/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.set_like.basic.basic
import data.fintype.basic
/-!
# Set-like fintype

This file contains a fintype instance for set-like objects such as subgroups. If `set_like A B`
and `fintype B` then `fintype A`.
-/

namespace set_like

noncomputable instance {A B : Type*} [fintype B] [set_like A B] : fintype A :=
fintype.of_injective coe set_like.coe_injective

end set_like
