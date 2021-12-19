/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.quiver

variables {α W : Type*}

structure multigraph (α : Type*) extends quiver α :=
(hom_equiv (a b : α) : (a ⟶ b) ≃ (b ⟶ a))
(hom_equiv_symm (a b : α) : (hom_equiv a b).symm = hom_equiv b a)

structure simple_multigraph (α : Type*) extends multigraph α :=
(hom_self (a : α) : is_empty (a ⟶ a))

structure weight_multigraph (α W : Type*) extends multigraph α :=
(weight' {a b : α} : (a ⟶ b) → W)
(weight_symm' (a b : α) (e : a ⟶ b) : weight' (hom_equiv _ _ e) = weight' e)

structure simple_weight_multigraph (α W : Type*) extends weight_multigraph α W :=
(hom_self (a : α) : is_empty (a ⟶ a))
