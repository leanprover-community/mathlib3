/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.enriched.enriched_over
import algebra.category.Group.basic
import tactic.transport

universes v u

namespace category_theory

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

abbreviation preadditive' := enriched_over.{v} AddCommGroup.{v} C

set_option trace.equiv_rw_type true

-- instance (X Y : C) [preadditive' C] : add_comm_group (X ⟶ Y) :=
-- begin
--   have : (X ⟶[AddCommGroup.{v}] Y : Type v) = (X ⟶ Y), by simp,
--   have e := equiv.cast this,
--   have S : add_comm_group (X ⟶[AddCommGroup.{v}] Y : Type v) := by apply_instance,
--   refine_struct { .. },
--   { have add := S.add, equiv_rw e at add, exact add, },

--   transport S using e, -- fail!
-- end

end category_theory
