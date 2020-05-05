/-
Copyright (c) 2018 Ashwin Iyengar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ashwin Iyengar
-/

/-import ring_theory.noetherian

universe u

section prio
set_option default_priority 100 -- see Note [default priority]
class dedekind_domain (α : Type u) extends integral_domain α :=
(noetherian : is_noetherian α α)
(integrally_closed : is)
end prio-/
