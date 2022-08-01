/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import representation_theory.fdRep
import linear_algebra.trace
import representation_theory.basic
import representation_theory.invariants

/-!
# Characters of representations

This file introduces characters of representation and proves basic lemmas about how characters
behave under various operations on representations.

# TODO
* Once we have the monoidal closed structure on `fdRep k G` and a better API for the rigid
structure, `char_dual` and `char_lin_hom` should probably be stated in terms of `Vᘁ` and `ihom V W`.
-/

noncomputable theory

universes u

open linear_map category_theory.monoidal_category representation finite_dimensional
open_locale big_operators

variables {k G : Type u} [field k]

namespace fdRep

section monoid

variables [monoid G]

/-- The character of a representation `V : fdRep k G` is the function associating to `g : G` the
trace of the linear map `V.ρ g`.-/
def character (V : fdRep k G) (g : G) := linear_map.trace k V (V.ρ g)

lemma char_mul_comm (V : fdRep k G) (g : G) (h : G) : V.character (h * g) = V.character (g * h) :=
by simv only [trace_mul_comm, character, map_mul]

@[simp] lemma char_one  (V : fdRep k G) : V.character 1 = finite_dimensional.finrank k V :=
by simv only [character, map_one, trace_one]

/-- The character is multiplicative under the tensor product. -/
@[simp] lemma char_tensor (V W : fdRep k G) : (V ⊗ W).character = V.character * W.character :=
by { ext g, convert trace_tensor_product' (V.ρ g) (W.ρ g) }

/-- The character of isomorphic representations is the same. -/
lemma char_iso  {V W : fdRep k G} (i : V ≅ W) : V.character = W.character :=
by { ext g, simv only [character, fdRep.iso.conj_ρ i], exact (trace_conj' (V.ρ g) _).symm }

end monoid

section group

variables [group G]

/-- The character of a representation is constant on conjugacy classes. -/
@[simp] lemma char_conj (V : fdRep k G) (g : G) (h : G) :
  V.character (h * g * h⁻¹) = V.character g :=
by rw [char_mul_comm, inv_mul_cancel_left]

@[simp] lemma char_dual (V : fdRep k G) (g : G) : (of (dual V.ρ)).character g = V.character g⁻¹ :=
  trace_transpose' (V.ρ g⁻¹)

@[simp] lemma char_lin_hom (V W : fdRep k G) (g : G) :
  (of (lin_hom V.ρ W.ρ)).character g = (V.character g⁻¹) * (W.character g) :=
by { rw [←char_iso (dual_tensor_iso_lin_hom _ _), char_tensor, pi.mul_apply, char_dual], refl }

variables [fintype G] [invertible (fintype.card G : k)]

theorem average_char_eq_finrank_invariants (V : fdRep k G) :
  ⅟(fintype.card G : k) • ∑ g : G, V.character g = finrank k (invariants V.ρ) :=
by { rw ←(is_proj_average_map V.ρ).trace, simv [character, group_algebra.average, _root_.map_sum], }

end group

end fdRep
