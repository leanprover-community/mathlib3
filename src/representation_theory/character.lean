/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import representation_theory.fdRep
import linear_algebra.trace
import representation_theory.invariants

/-!
# Characters of representations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file introduces characters of representation and proves basic lemmas about how characters
behave under various operations on representations.

# TODO
* Once we have the monoidal closed structure on `fdRep k G` and a better API for the rigid
structure, `char_dual` and `char_lin_hom` should probably be stated in terms of `Vᘁ` and `ihom V W`.
-/

noncomputable theory

universes u

open category_theory linear_map category_theory.monoidal_category representation finite_dimensional
open_locale big_operators

variables {k : Type u} [field k]

namespace fdRep

section monoid

variables {G : Type u} [monoid G]

/-- The character of a representation `V : fdRep k G` is the function associating to `g : G` the
trace of the linear map `V.ρ g`.-/
def character (V : fdRep k G) (g : G) := linear_map.trace k V (V.ρ g)

lemma char_mul_comm (V : fdRep k G) (g : G) (h : G) : V.character (h * g) = V.character (g * h) :=
by simp only [trace_mul_comm, character, map_mul]

@[simp] lemma char_one  (V : fdRep k G) : V.character 1 = finite_dimensional.finrank k V :=
by simp only [character, map_one, trace_one]

/-- The character is multiplicative under the tensor product. -/
@[simp] lemma char_tensor (V W : fdRep k G) : (V ⊗ W).character = V.character * W.character :=
by { ext g, convert trace_tensor_product' (V.ρ g) (W.ρ g) }

/-- The character of isomorphic representations is the same. -/
lemma char_iso  {V W : fdRep k G} (i : V ≅ W) : V.character = W.character :=
by { ext g, simp only [character, fdRep.iso.conj_ρ i], exact (trace_conj' (V.ρ g) _).symm }

end monoid

section group

variables {G : Type u} [group G]

/-- The character of a representation is constant on conjugacy classes. -/
@[simp] lemma char_conj (V : fdRep k G) (g : G) (h : G) :
  V.character (h * g * h⁻¹) = V.character g :=
by rw [char_mul_comm, inv_mul_cancel_left]

@[simp] lemma char_dual (V : fdRep k G) (g : G) : (of (dual V.ρ)).character g = V.character g⁻¹ :=
  trace_transpose' (V.ρ g⁻¹)

@[simp] lemma char_lin_hom (V W : fdRep k G) (g : G) :
  (of (lin_hom V.ρ W.ρ)).character g = (V.character g⁻¹) * (W.character g) :=
by rw [←char_iso (dual_tensor_iso_lin_hom _ _), char_tensor, pi.mul_apply, char_dual]

variables [fintype G] [invertible (fintype.card G : k)]

theorem average_char_eq_finrank_invariants (V : fdRep k G) :
  ⅟(fintype.card G : k) • ∑ g : G, V.character g = finrank k (invariants V.ρ) :=
by { rw ←(is_proj_average_map V.ρ).trace, simp [character, group_algebra.average, _root_.map_sum], }

end group

section orthogonality

variables {G : Group.{u}} [is_alg_closed k]

open_locale classical

variables [fintype G] [invertible (fintype.card G : k)]

/-- Orthogonality of characters for irreducible representations of finite group over an
algebraically closed field whose characteristic doesn't divide the order of the group. -/
lemma char_orthonormal (V W : fdRep k G) [simple V] [simple W] :
  ⅟(fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
  if nonempty (V ≅ W) then ↑1 else ↑0 :=
begin
  -- First, we can rewrite the summand `V.character g * W.character g⁻¹` as the character
  -- of the representation `V ⊗ W* ≅ Hom(W, V)` applied to `g`.
  conv in (V.character _ * W.character _)
  { rw [mul_comm, ←char_dual, ←pi.mul_apply, ←char_tensor],
    rw [char_iso (fdRep.dual_tensor_iso_lin_hom W.ρ V)], } ,

  -- The average over the group of the character of a representation equals the dimension of the
  -- space of invariants.
  rw average_char_eq_finrank_invariants,
  rw [show (of (lin_hom W.ρ V.ρ)).ρ = lin_hom W.ρ V.ρ, from fdRep.of_ρ (lin_hom W.ρ V.ρ)],

  -- The space of invariants of `Hom(W, V)` is the subspace of `G`-equivariant linear maps,
  -- `Hom_G(W, V)`.
  rw (lin_hom.invariants_equiv_fdRep_hom W V).finrank_eq,

  -- By Schur's Lemma, the dimension of `Hom_G(W, V)` is `1` is `V ≅ W` and `0` otherwise.
  rw_mod_cast [finrank_hom_simple_simple W V, iso.nonempty_iso_symm],
end

end orthogonality

end fdRep
