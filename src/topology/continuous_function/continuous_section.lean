/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import topology.continuous_function.basic
import data.right_inv

set_option old_structure_cmd true

variables {α: Type*} {β: Type*} {f : α → β}
variables [topological_space α] [topological_space β]

structure continuous_section (f : α → β) extends right_inv f, C(β, α)

instance : has_coe_to_fun (continuous_section f) := ⟨λ f, β → α, continuous_section.to_fun⟩

instance : has_coe (continuous_section f) (right_inv f) :=
⟨continuous_section.to_right_inv⟩

namespace continuous_section

variables {s t : continuous_section f}

lemma coe_injective (H : ⇑s = t) : s = t :=
by { cases s, cases t, congr' }

@[ext] theorem ext (H : ∀ a, s a = t a) : s = t :=
coe_injective $ funext H

@[simp] lemma to_fun_eq_coe (g : continuous_section f) : g.to_fun = ⇑g := rfl
@[simp] lemma coe_fn_coe (g : continuous_section f) :
  ⇑(g : right_inv f) = g := rfl

end continuous_section
