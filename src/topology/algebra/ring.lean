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
- `prod.topological_ring`/`prod.topological_ring`: The product of two topological (semi)rings.
- `pi.topological_ring`/`pi.topological_ring`: The arbitrary product of topological (semi)rings.
- `ideal.closure`: The closure of an ideal is an ideal.
- `topological_ring_quotient`: The quotient of a topological ring by an ideal is a topological ring.

-/

open classical set filter topological_space
open_locale classical

section topological_ring
variables (α : Type*)

/-- A topological (semi)ring is a (semi)ring `R` where addition and multiplication are continuous.
If `R` is a ring, then negation is automatically continuous, as it is multiplication with `-1`. -/
class topological_ring [topological_space α] [semiring α]
  extends has_continuous_add α, has_continuous_mul α : Prop

section
variables {α} [topological_space α] [semiring α] [topological_ring α]

/-- The (topological-space) closure of a subsemiring of a topological semiring is
itself a subsemiring. -/
def subsemiring.topological_closure (s : subsemiring α) : subsemiring α :=
{ carrier := closure (s : set α),
  ..(s.to_submonoid.topological_closure),
  ..(s.to_add_submonoid.topological_closure ) }

@[simp] lemma subsemiring.topological_closure_coe (s : subsemiring α) :
  (s.topological_closure : set α) = closure (s : set α) :=
rfl

instance subsemiring.topological_closure_topological_ring (s : subsemiring α) :
  topological_ring (s.topological_closure) :=
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
instance {β : Type*} [semiring β] [topological_space β] [topological_ring β] :
  topological_ring (α × β) := {}

instance {β : Type*} {C : β → Type*} [∀ b, topological_space (C b)]
  [Π b, semiring (C b)] [Π b, topological_ring (C b)] : topological_ring (Π b, C b) := {}

end

variables {α} [ring α] [topological_space α] [topological_ring α]

@[priority 100] -- See note [lower instance priority]
instance topological_ring.to_topological_add_group : topological_add_group α :=
{ continuous_add := continuous_add,
  continuous_neg := by simpa only [neg_one_mul, id.def] using
    (@continuous_const α α _ _ (-1)).mul continuous_id }

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
  continuous_mul :=
    have cont : continuous (mk N ∘ (λ (p : α × α), p.fst * p.snd)) :=
      continuous_quot_mk.comp continuous_mul,
    (quotient_map.continuous_iff (quotient_ring.quotient_map_coe_coe N)).mpr cont }

end topological_ring

/-!
### Lattice of ring topologies
We define a type class `ring_topology α` which endows a ring `α` with a topology such that all ring
operations are continuous.

Ring topologies on a fixed ring `α` are ordered, by reverse inclusion. They form a complete lattice,
with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : topological_space α → ring_topology β`. -/

universes u v

/-- A ring topology on a ring `α` is a topology for which addition, negation and multiplication
are continuous. -/
@[ext]
structure ring_topology (α : Type u) [ring α]
  extends topological_space α, topological_ring α : Type u

namespace ring_topology
variables {α : Type*} [ring α]

instance inhabited {α : Type u} [ring α] : inhabited (ring_topology α) :=
⟨{to_topological_space := ⊤,
  continuous_add       := continuous_top,
  continuous_mul       := continuous_top}⟩

@[ext]
lemma ext' {f g : ring_topology α} (h : f.is_open = g.is_open) : f = g :=
by { ext, rw h }

/-- The ordering on ring topologies on the ring `α`.
  `t ≤ s` if every set open in `s` is also open in `t` (`t` is finer than `s`). -/
instance : partial_order (ring_topology α) :=
partial_order.lift ring_topology.to_topological_space $ ext

local notation `cont` := @continuous _ _

private def def_Inf (S : set (ring_topology α)) : ring_topology α :=
let Inf_S' := Inf (to_topological_space '' S) in
{ to_topological_space := Inf_S',
  continuous_add       :=
  begin
    apply continuous_Inf_rng,
    rintros _ ⟨⟨t, tr⟩, haS, rfl⟩, resetI,
    have h := continuous_Inf_dom (set.mem_image_of_mem to_topological_space haS) continuous_id,
    have h_continuous_id := @continuous.prod_map _ _ _ _ t t Inf_S' Inf_S' _ _ h h,
    have h_continuous_add : cont (id _) t (λ (p : α × α), p.fst + p.snd) := continuous_add,
    exact @continuous.comp _ _ _ (id _) (id _) t _ _ h_continuous_add h_continuous_id,
  end,
  continuous_mul       :=
  begin
    apply continuous_Inf_rng,
    rintros _ ⟨⟨t, tr⟩, haS, rfl⟩, resetI,
    have h := continuous_Inf_dom (set.mem_image_of_mem to_topological_space haS) continuous_id,
    have h_continuous_id := @continuous.prod_map _ _ _ _ t t Inf_S' Inf_S' _ _ h h,
    have h_continuous_mul : cont (id _) t (λ (p : α × α), p.fst * p.snd) := continuous_mul,
    exact @continuous.comp _ _ _ (id _) (id _) t _ _ h_continuous_mul h_continuous_id,
  end }

/-- Ring topologies on `α` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of ring topologies is the topology generated by all their open sets
(which is a ring topology).

The supremum of two ring topologies `s` and `t` is the infimum of the family of all ring topologies
contained in the intersection of `s` and `t`. -/
instance : complete_semilattice_Inf (ring_topology α) :=
{ Inf    := def_Inf,
  Inf_le := λ S a haS, by { apply topological_space.complete_lattice.Inf_le, use [a, ⟨ haS, rfl⟩] },
  le_Inf :=
  begin
    intros S a hab,
    apply topological_space.complete_lattice.le_Inf,
    rintros _ ⟨b, hbS, rfl⟩,
    exact hab b hbS,
  end,
  ..ring_topology.partial_order }

instance : complete_lattice (ring_topology α) :=
complete_lattice_of_complete_semilattice_Inf _

/--  Given `f : α → β` and a topology on `α`, the coinduced ring topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological ring. -/
def coinduced {α β : Type*} [t : topological_space α] [ring β] (f : α → β) :
  ring_topology β :=
Inf {b : ring_topology β | (topological_space.coinduced f t) ≤ b.to_topological_space}

lemma coinduced_continuous {α β : Type*} [t : topological_space α] [ring β] (f : α → β) :
  cont t (coinduced f).to_topological_space f :=
begin
  rw continuous_iff_coinduced_le,
  refine le_Inf _,
  rintros _ ⟨t', ht', rfl⟩,
  exact ht',
end

end ring_topology
