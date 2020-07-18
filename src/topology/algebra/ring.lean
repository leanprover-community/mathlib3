/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Theory of topological rings.
-/
import topology.algebra.group
import ring_theory.ideals

open classical set filter topological_space
open_locale classical

section topological_ring
universes u v w
variables (α : Type u) [topological_space α]

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A topological semiring is a semiring where addition and multiplication are continuous. -/
class topological_semiring [semiring α]
  extends has_continuous_add α, has_continuous_mul α : Prop
end prio

variables [ring α]

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A topological ring is a ring where the ring operations are continuous. -/
class topological_ring extends has_continuous_add α, has_continuous_mul α : Prop :=
(continuous_neg : continuous (λa:α, -a))
end prio

variables [t : topological_ring α]
@[priority 100] -- see Note [lower instance priority]
instance topological_ring.to_topological_semiring : topological_semiring α := {..t}

@[priority 100] -- see Note [lower instance priority]
instance topological_ring.to_topological_add_group : topological_add_group α := {..t}

end topological_ring

section topological_comm_ring
variables {α : Type*} [topological_space α] [comm_ring α] [topological_ring α]

def ideal.closure (S : ideal α) : ideal α :=
{ carrier := closure S,
  zero_mem' := subset_closure S.zero_mem,
  add_mem'  := assume x y hx hy,
    mem_closure2 continuous_add hx hy $ assume a b, S.add_mem,
  smul_mem'  := assume c x hx,
    have continuous (λx:α, c * x) := continuous_const.mul continuous_id,
    mem_closure this hx $ assume a, S.mul_mem_left }

@[simp] lemma ideal.coe_closure (S : ideal α) :
  (S.closure : set α) = closure S := rfl

end topological_comm_ring

section topological_ring
variables {α : Type*} [topological_space α] [comm_ring α] (N : ideal α)
open ideal.quotient

instance topological_ring_quotient_topology : topological_space N.quotient :=
by dunfold ideal.quotient submodule.quotient; apply_instance

lemma quotient_ring_saturate {α : Type*} [comm_ring α] (N : ideal α) (s : set α) :
  mk N ⁻¹' (mk N '' s) = (⋃ x : N, (λ y, x.1 + y) '' s) :=
begin
  ext x,
  simp only [mem_preimage, mem_image, mem_Union, ideal.quotient.eq],
  split,
  { exact assume ⟨a, a_in, h⟩, ⟨⟨_, N.neg_mem h⟩, a, a_in, by simp⟩ },
  { exact assume ⟨⟨i, hi⟩, a, ha, eq⟩, ⟨a, ha,
      by rw [← eq, sub_add_eq_sub_sub_swap, sub_self, zero_sub];
      exact N.neg_mem hi⟩ }
end

variable [topological_ring α]

lemma quotient_ring.is_open_map_coe : is_open_map (mk N) :=
begin
  assume s s_op,
  show is_open (mk N ⁻¹' (mk N '' s)),
  rw quotient_ring_saturate N s,
  exact is_open_Union (assume ⟨n, _⟩, is_open_map_add_left n s s_op)
end

lemma quotient_ring.quotient_map_coe_coe : quotient_map (λ p : α × α, (mk N p.1, mk N p.2)) :=
begin
  apply is_open_map.to_quotient_map,
  { exact (quotient_ring.is_open_map_coe N).prod (quotient_ring.is_open_map_coe N) },
  { exact (continuous_quot_mk.comp continuous_fst).prod_mk
          (continuous_quot_mk.comp continuous_snd) },
  { rintro ⟨⟨x⟩, ⟨y⟩⟩,
    exact ⟨(x, y), rfl⟩ }
end

instance topological_ring_quotient : topological_ring N.quotient :=
{ continuous_add :=
    have cont : continuous (mk N ∘ (λ (p : α × α), p.fst + p.snd)) :=
      continuous_quot_mk.comp continuous_add,
    (quotient_map.continuous_iff (quotient_ring.quotient_map_coe_coe N)).2 cont,
  continuous_neg := continuous_quotient_lift _ (continuous_quot_mk.comp continuous_neg),
  continuous_mul :=
    have cont : continuous (mk N ∘ (λ (p : α × α), p.fst * p.snd)) :=
      continuous_quot_mk.comp continuous_mul,
    (quotient_map.continuous_iff (quotient_ring.quotient_map_coe_coe N)).2 cont }

end topological_ring
