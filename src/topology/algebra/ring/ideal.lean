/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import topology.algebra.ring.basic
import ring_theory.ideal.quotient
/-!
# Ideals and quotients of topological rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `ideal.closure` to be the topological closure of an ideal in a topological
ring. We also define a `topological_space` structure on the quotient of a topological ring by an
ideal and prove that the quotient is a topological ring.
-/

section ring
variables {R : Type*} [topological_space R] [ring R] [topological_ring R]

/-- The closure of an ideal in a topological ring as an ideal. -/
protected def ideal.closure (I : ideal R) : ideal R :=
{ carrier   := closure I,
  smul_mem' := λ c x hx, map_mem_closure (mul_left_continuous _) hx $ λ a, I.mul_mem_left c,
  ..(add_submonoid.topological_closure I.to_add_submonoid) }

@[simp] lemma ideal.coe_closure (I : ideal R) : (I.closure : set R) = closure I := rfl

@[simp] lemma ideal.closure_eq_of_is_closed (I : ideal R) [hI : is_closed (I : set R)] :
  I.closure = I :=
set_like.ext' hI.closure_eq

end ring

section comm_ring
variables {R : Type*} [topological_space R] [comm_ring R] (N : ideal R)
open ideal.quotient

instance topological_ring_quotient_topology : topological_space (R ⧸ N) :=
quotient.topological_space

-- note for the reader: in the following, `mk` is `ideal.quotient.mk`, the canonical map `R → R/I`.

variable [topological_ring R]

lemma quotient_ring.is_open_map_coe : is_open_map (mk N) :=
begin
  intros s s_op,
  change is_open (mk N ⁻¹' (mk N '' s)),
  rw quotient_ring_saturate,
  exact is_open_Union (λ ⟨n, _⟩, is_open_map_add_left n s s_op)
end

lemma quotient_ring.quotient_map_coe_coe : quotient_map (λ p : R × R, (mk N p.1, mk N p.2)) :=
is_open_map.to_quotient_map
((quotient_ring.is_open_map_coe N).prod (quotient_ring.is_open_map_coe N))
((continuous_quot_mk.comp continuous_fst).prod_mk (continuous_quot_mk.comp continuous_snd))
(by rintro ⟨⟨x⟩, ⟨y⟩⟩; exact ⟨(x, y), rfl⟩)

instance topological_ring_quotient : topological_ring (R ⧸ N) :=
topological_semiring.to_topological_ring
{ continuous_add :=
    have cont : continuous (mk N ∘ (λ (p : R × R), p.fst + p.snd)) :=
      continuous_quot_mk.comp continuous_add,
    (quotient_map.continuous_iff (quotient_ring.quotient_map_coe_coe N)).mpr cont,
  continuous_mul :=
    have cont : continuous (mk N ∘ (λ (p : R × R), p.fst * p.snd)) :=
      continuous_quot_mk.comp continuous_mul,
    (quotient_map.continuous_iff (quotient_ring.quotient_map_coe_coe N)).mpr cont }

end comm_ring
