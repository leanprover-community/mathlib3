/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Theory of topological rings.
-/
import topology.algebra.group
import ring_theory.ideal.basic
import ring_theory.subring
import algebra.ring.prod

/-!

# Topological (semi)rings

A topological (semi)ring is a (semi)ring equipped with a topology such that all operations are
continuous. Besides this definition, this file proves that the topological closure of a subring
(resp. an ideal) is a subring (resp. an ideal) and defines products and quotients
of topological (semi)rings.

## Main Results

- `subring.topological_closure`/`subsemiring.topological_closure`: the topological closure of a
  `subring`/`subsemiring` is itself a `sub(semi)ring`.
- `prod.topological_semiring`/`prod.topological_ring`: The product of two topological (semi)rings.
- `pi.topological_semiring`/`pi.topological_ring`: The arbitrary product of topological (semi)rings.
- `ideal.closure`: The closure of an ideal is an ideal.
- `topological_ring_quotient`: The quotient of a topological ring by an ideal is a topological ring.

-/

open classical set filter topological_space
open_locale classical

section topological_ring
variables (α : Type*)

/-- A topological semiring is a semiring where addition and multiplication are continuous. -/
class topological_semiring [topological_space α] [semiring α]
  extends has_continuous_add α, has_continuous_mul α : Prop

section
variables {α} [topological_space α] [semiring α] [topological_semiring α]

/-- The (topological-space) closure of a subsemiring of a topological semiring is
itself a subsemiring. -/
def subsemiring.topological_closure (s : subsemiring α) : subsemiring α :=
{ carrier := closure (s : set α),
  ..(s.to_submonoid.topological_closure),
  ..(s.to_add_submonoid.topological_closure ) }

@[simp] lemma subsemiring.topological_closure_coe (s : subsemiring α) :
  (s.topological_closure : set α) = closure (s : set α) :=
rfl

instance subsemiring.topological_closure_topological_semiring (s : subsemiring α) :
  topological_semiring (s.topological_closure) :=
{ ..s.to_add_submonoid.topological_closure_has_continuous_add,
  ..s.to_submonoid.topological_closure_has_continuous_mul }

lemma subsemiring.subring_topological_closure (s : subsemiring α) :
  s ≤ s.topological_closure :=
subset_closure

lemma subsemiring.is_closed_topological_closure (s : subsemiring α) :
  is_closed (s.topological_closure : set α) :=
by convert is_closed_closure

lemma subsemiring.topological_closure_minimal
  (s : subsemiring α) {t : subsemiring α} (h : s ≤ t) (ht : is_closed (t : set α)) :
  s.topological_closure ≤ t :=
closure_minimal h ht

/-- The product topology on the cartesian product of two topological semirings
  makes the product into a topological semiring. -/
instance {β : Type*}
  [semiring β] [topological_space β] [topological_semiring β] : topological_semiring (α × β) :=
{}

instance {β : Type*} {C : β → Type*} [∀ b, topological_space (C b)]
  [Π b, semiring (C b)] [Π b, topological_semiring (C b)] : topological_semiring (Π b, C b) :=
{}

end

/-- A topological ring is a ring where the ring operations are continuous. -/
class topological_ring [topological_space α] [ring α]
  extends topological_add_group α, has_continuous_mul α : Prop

variables {α} [ring α] [topological_space α]

section
variables [t : topological_ring α]
@[priority 100] -- see Note [lower instance priority]
instance topological_ring.to_topological_semiring : topological_semiring α := {..t}
end

variables [topological_ring α]

/-- The product topology on the cartesian product of two topological rings
  makes the product into a topological ring. -/
instance {β : Type*}
  [ring β] [topological_space β] [topological_ring β] : topological_ring (α × β) :=
{ }

instance {β : Type*} {C : β → Type*} [Π b, topological_space (C b)]
  [Π b, ring (C b)] [∀ b, topological_ring (C b)] : topological_ring (Π b, C b) :=
{ continuous_neg := continuous_neg }

/-- In a topological ring, the left-multiplication `add_monoid_hom` is continuous. -/
lemma mul_left_continuous (x : α) : continuous (add_monoid_hom.mul_left x) :=
continuous_const.mul continuous_id

/-- In a topological ring, the right-multiplication `add_monoid_hom` is continuous. -/
lemma mul_right_continuous (x : α) : continuous (add_monoid_hom.mul_right x) :=
continuous_id.mul continuous_const

/-- The (topological-space) closure of a subring of a topological semiring is
itself a subring. -/
def subring.topological_closure (S : subring α) : subring α :=
{ carrier := closure (S : set α),
  ..S.to_submonoid.topological_closure,
  ..S.to_add_subgroup.topological_closure }

instance subring.topological_closure_topological_ring (s : subring α) :
  topological_ring (s.topological_closure) :=
{ ..s.to_add_subgroup.topological_closure_topological_add_group,
  ..s.to_submonoid.topological_closure_has_continuous_mul }

lemma subring.subring_topological_closure (s : subring α) :
  s ≤ s.topological_closure := subset_closure

lemma subring.is_closed_topological_closure (s : subring α) :
  is_closed (s.topological_closure : set α) := by convert is_closed_closure

lemma subring.topological_closure_minimal
  (s : subring α) {t : subring α} (h : s ≤ t) (ht : is_closed (t : set α)) :
  s.topological_closure ≤ t := closure_minimal h ht

end topological_ring

section topological_comm_ring
variables {α : Type*} [topological_space α] [comm_ring α] [topological_ring α]

/-- The closure of an ideal in a topological ring as an ideal. -/
def ideal.closure (S : ideal α) : ideal α :=
{ carrier   := closure S,
  smul_mem' := λ c x hx, map_mem_closure (mul_left_continuous _) hx $ λ a, S.mul_mem_left c,
  ..(add_submonoid.topological_closure S.to_add_submonoid) }

@[simp] lemma ideal.coe_closure (S : ideal α) : (S.closure : set α) = closure S := rfl

end topological_comm_ring

section topological_ring
variables {α : Type*} [topological_space α] [comm_ring α] (N : ideal α)
open ideal.quotient

instance topological_ring_quotient_topology : topological_space N.quotient :=
by dunfold ideal.quotient submodule.quotient; apply_instance

-- note for the reader: in the following, `mk` is `ideal.quotient.mk`, the canonical map `R → R/I`.

variable [topological_ring α]

lemma quotient_ring.is_open_map_coe : is_open_map (mk N) :=
begin
  intros s s_op,
  change is_open (mk N ⁻¹' (mk N '' s)),
  rw quotient_ring_saturate,
  exact is_open_Union (λ ⟨n, _⟩, is_open_map_add_left n s s_op)
end

lemma quotient_ring.quotient_map_coe_coe : quotient_map (λ p : α × α, (mk N p.1, mk N p.2)) :=
is_open_map.to_quotient_map
((quotient_ring.is_open_map_coe N).prod (quotient_ring.is_open_map_coe N))
((continuous_quot_mk.comp continuous_fst).prod_mk (continuous_quot_mk.comp continuous_snd))
(by rintro ⟨⟨x⟩, ⟨y⟩⟩; exact ⟨(x, y), rfl⟩)

instance topological_ring_quotient : topological_ring N.quotient :=
{ continuous_add :=
    have cont : continuous (mk N ∘ (λ (p : α × α), p.fst + p.snd)) :=
      continuous_quot_mk.comp continuous_add,
    (quotient_map.continuous_iff (quotient_ring.quotient_map_coe_coe N)).mpr cont,
  continuous_neg :=
    by convert continuous_quotient_lift _ (continuous_quot_mk.comp continuous_neg); apply_instance,
  continuous_mul :=
    have cont : continuous (mk N ∘ (λ (p : α × α), p.fst * p.snd)) :=
      continuous_quot_mk.comp continuous_mul,
    (quotient_map.continuous_iff (quotient_ring.quotient_map_coe_coe N)).mpr cont }

end topological_ring
