/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import algebra.ring.prod
import ring_theory.subring.basic
import topology.algebra.group.basic

/-!

# Topological (semi)rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A topological (semi)ring is a (semi)ring equipped with a topology such that all operations are
continuous. Besides this definition, this file proves that the topological closure of a subring
(resp. an ideal) is a subring (resp. an ideal) and defines products and quotients
of topological (semi)rings.

## Main Results

- `subring.topological_closure`/`subsemiring.topological_closure`: the topological closure of a
  `subring`/`subsemiring` is itself a `sub(semi)ring`.
- `prod.topological_semiring`/`prod.topological_ring`: The product of two topological
  (semi)rings.
- `pi.topological_semiring`/`pi.topological_ring`: The arbitrary product of topological
  (semi)rings.

-/

open classical set filter topological_space function
open_locale classical topology filter

section topological_semiring
variables (α : Type*)

/-- a topological semiring is a semiring `R` where addition and multiplication are continuous.
We allow for non-unital and non-associative semirings as well.

The `topological_semiring` class should *only* be instantiated in the presence of a
`non_unital_non_assoc_semiring` instance; if there is an instance of `non_unital_non_assoc_ring`,
then `topological_ring` should be used. Note: in the presence of `non_assoc_ring`, these classes are
mathematically equivalent (see `topological_semiring.has_continuous_neg_of_mul` or
`topological_semiring.to_topological_ring`).  -/
class topological_semiring [topological_space α] [non_unital_non_assoc_semiring α]
  extends has_continuous_add α, has_continuous_mul α : Prop

/-- A topological ring is a ring `R` where addition, multiplication and negation are continuous.

If `R` is a (unital) ring, then continuity of negation can be derived from continuity of
multiplication as it is multiplication with `-1`. (See
`topological_semiring.has_continuous_neg_of_mul` and
`topological_semiring.to_topological_add_group`) -/
class topological_ring [topological_space α] [non_unital_non_assoc_ring α]
  extends topological_semiring α, has_continuous_neg α : Prop

variables {α}

/-- If `R` is a ring with a continuous multiplication, then negation is continuous as well since it
is just multiplication with `-1`. -/
lemma topological_semiring.has_continuous_neg_of_mul [topological_space α] [non_assoc_ring α]
  [has_continuous_mul α] : has_continuous_neg α :=
{ continuous_neg :=
  by simpa using (continuous_const.mul continuous_id : continuous (λ x : α, (-1) * x)) }

/-- If `R` is a ring which is a topological semiring, then it is automatically a topological
ring. This exists so that one can place a topological ring structure on `R` without explicitly
proving `continuous_neg`. -/
lemma topological_semiring.to_topological_ring [topological_space α] [non_assoc_ring α]
  (h : topological_semiring α) : topological_ring α :=
{ ..h,
  ..(by { haveI := h.to_has_continuous_mul,
          exact topological_semiring.has_continuous_neg_of_mul } : has_continuous_neg α) }

@[priority 100] -- See note [lower instance priority]
instance topological_ring.to_topological_add_group [non_unital_non_assoc_ring α]
  [topological_space α] [topological_ring α] : topological_add_group α :=
{ ..topological_ring.to_topological_semiring.to_has_continuous_add,
  ..topological_ring.to_has_continuous_neg }

@[priority 50]
instance discrete_topology.topological_semiring [topological_space α]
  [non_unital_non_assoc_semiring α] [discrete_topology α] : topological_semiring α := ⟨⟩

@[priority 50]
instance discrete_topology.topological_ring [topological_space α]
  [non_unital_non_assoc_ring α] [discrete_topology α] : topological_ring α := ⟨⟩

section
variables [topological_space α] [semiring α] [topological_semiring α]
namespace subsemiring

instance (S : subsemiring α) :
  topological_semiring S :=
{ ..S.to_submonoid.has_continuous_mul,
  ..S.to_add_submonoid.has_continuous_add }

end subsemiring

/-- The (topological-space) closure of a subsemiring of a topological semiring is
itself a subsemiring. -/
def subsemiring.topological_closure (s : subsemiring α) : subsemiring α :=
{ carrier := closure (s : set α),
  ..(s.to_submonoid.topological_closure),
  ..(s.to_add_submonoid.topological_closure ) }

@[simp] lemma subsemiring.topological_closure_coe (s : subsemiring α) :
  (s.topological_closure : set α) = closure (s : set α) :=
rfl

lemma subsemiring.le_topological_closure (s : subsemiring α) :
  s ≤ s.topological_closure :=
subset_closure

lemma subsemiring.is_closed_topological_closure (s : subsemiring α) :
  is_closed (s.topological_closure : set α) :=
by convert is_closed_closure

lemma subsemiring.topological_closure_minimal
  (s : subsemiring α) {t : subsemiring α} (h : s ≤ t) (ht : is_closed (t : set α)) :
  s.topological_closure ≤ t :=
closure_minimal h ht

/-- If a subsemiring of a topological semiring is commutative, then so is its
topological closure. -/
def subsemiring.comm_semiring_topological_closure [t2_space α] (s : subsemiring α)
  (hs : ∀ (x y : s), x * y = y * x) : comm_semiring s.topological_closure :=
{ ..s.topological_closure.to_semiring,
  ..s.to_submonoid.comm_monoid_topological_closure hs }
end

section
variables {β : Type*} [topological_space α] [topological_space β]

/-- The product topology on the cartesian product of two topological semirings
  makes the product into a topological semiring. -/
instance [non_unital_non_assoc_semiring α] [non_unital_non_assoc_semiring β]
  [topological_semiring α] [topological_semiring β] : topological_semiring (α × β) := {}

/-- The product topology on the cartesian product of two topological rings
  makes the product into a topological ring. -/
instance [non_unital_non_assoc_ring α] [non_unital_non_assoc_ring β]
  [topological_ring α] [topological_ring β] : topological_ring (α × β) := {}

end

instance {β : Type*} {C : β → Type*} [∀ b, topological_space (C b)]
  [Π b, non_unital_non_assoc_semiring (C b)]
  [Π b, topological_semiring (C b)] : topological_semiring (Π b, C b) := {}

instance {β : Type*} {C : β → Type*} [∀ b, topological_space (C b)]
  [Π b, non_unital_non_assoc_ring (C b)]
  [Π b, topological_ring (C b)] : topological_ring (Π b, C b) := {}

section mul_opposite
open mul_opposite

instance [non_unital_non_assoc_semiring α] [topological_space α] [has_continuous_add α] :
  has_continuous_add αᵐᵒᵖ :=
{ continuous_add := continuous_induced_rng.2 $ (@continuous_add α _ _ _).comp
  (continuous_unop.prod_map continuous_unop) }

instance [non_unital_non_assoc_semiring α] [topological_space α] [topological_semiring α] :
  topological_semiring αᵐᵒᵖ := {}

instance [non_unital_non_assoc_ring α] [topological_space α] [has_continuous_neg α] :
  has_continuous_neg αᵐᵒᵖ :=
{ continuous_neg := continuous_induced_rng.2 $ (@continuous_neg α _ _ _).comp continuous_unop }

instance [non_unital_non_assoc_ring α] [topological_space α] [topological_ring α] :
  topological_ring αᵐᵒᵖ := {}

end mul_opposite

section add_opposite
open add_opposite

instance [non_unital_non_assoc_semiring α] [topological_space α] [has_continuous_mul α] :
  has_continuous_mul αᵃᵒᵖ :=
{ continuous_mul := by convert
  (continuous_op.comp $ (@continuous_mul α _ _ _).comp $ continuous_unop.prod_map continuous_unop) }

instance [non_unital_non_assoc_semiring α] [topological_space α] [topological_semiring α] :
  topological_semiring αᵃᵒᵖ := {}

instance [non_unital_non_assoc_ring α] [topological_space α] [topological_ring α] :
  topological_ring αᵃᵒᵖ := {}

end add_opposite


section
variables {R : Type*} [non_unital_non_assoc_ring R] [topological_space R]

lemma topological_ring.of_add_group_of_nhds_zero [topological_add_group R]
  (hmul : tendsto (uncurry ((*) : R → R → R)) ((𝓝 0) ×ᶠ (𝓝 0)) $ 𝓝 0)
  (hmul_left : ∀ (x₀ : R), tendsto (λ x : R, x₀ * x) (𝓝 0) $ 𝓝 0)
  (hmul_right : ∀ (x₀ : R), tendsto (λ x : R, x * x₀) (𝓝 0) $ 𝓝 0) : topological_ring R :=
begin
  refine {..‹topological_add_group R›, ..},
  have hleft : ∀ x₀ : R, 𝓝 x₀ = map (λ x, x₀ + x) (𝓝 0), by simp,
  have hadd : tendsto (uncurry ((+) : R → R → R)) ((𝓝 0) ×ᶠ (𝓝 0)) (𝓝 0),
  { rw ← nhds_prod_eq,
    convert continuous_add.tendsto ((0 : R), (0 : R)),
    rw zero_add },
  rw continuous_iff_continuous_at,
  rintro ⟨x₀, y₀⟩,
  rw [continuous_at, nhds_prod_eq, hleft x₀, hleft y₀, hleft (x₀*y₀), filter.prod_map_map_eq,
      tendsto_map'_iff],
  suffices :
    tendsto ((λ (x : R), x + x₀ * y₀) ∘ (λ (p : R × R), p.1 + p.2) ∘
              (λ (p : R × R), (p.1*y₀ + x₀*p.2, p.1*p.2)))
            ((𝓝 0) ×ᶠ (𝓝 0)) (map (λ (x : R), x + x₀ * y₀) $ 𝓝 0),
  { convert this using 1,
    { ext, simp only [comp_app, mul_add, add_mul], abel },
    { simp only [add_comm] } },
  refine tendsto_map.comp (hadd.comp (tendsto.prod_mk _ hmul)),
  exact hadd.comp (((hmul_right y₀).comp tendsto_fst).prod_mk ((hmul_left  x₀).comp tendsto_snd))
end

lemma topological_ring.of_nhds_zero
  (hadd : tendsto (uncurry ((+) : R → R → R)) ((𝓝 0) ×ᶠ (𝓝 0)) $ 𝓝 0)
  (hneg : tendsto (λ x, -x : R → R) (𝓝 0) (𝓝 0))
  (hmul : tendsto (uncurry ((*) : R → R → R)) ((𝓝 0) ×ᶠ (𝓝 0)) $ 𝓝 0)
  (hmul_left : ∀ (x₀ : R), tendsto (λ x : R, x₀ * x) (𝓝 0) $ 𝓝 0)
  (hmul_right : ∀ (x₀ : R), tendsto (λ x : R, x * x₀) (𝓝 0) $ 𝓝 0)
  (hleft : ∀ x₀ : R, 𝓝 x₀ = map (λ x, x₀ + x) (𝓝 0)) : topological_ring R :=
begin
  haveI := topological_add_group.of_comm_of_nhds_zero hadd hneg hleft,
  exact topological_ring.of_add_group_of_nhds_zero hmul hmul_left hmul_right
end

end

variables {α} [topological_space α]

section
variables [non_unital_non_assoc_ring α] [topological_ring α]

/-- In a topological semiring, the left-multiplication `add_monoid_hom` is continuous. -/
lemma mul_left_continuous (x : α) : continuous (add_monoid_hom.mul_left x) :=
continuous_const.mul continuous_id

/-- In a topological semiring, the right-multiplication `add_monoid_hom` is continuous. -/
lemma mul_right_continuous (x : α) : continuous (add_monoid_hom.mul_right x) :=
continuous_id.mul continuous_const

end

variables [ring α] [topological_ring α]

namespace subring

instance (S : subring α) :
  topological_ring S :=
topological_semiring.to_topological_ring S.to_subsemiring.topological_semiring

end subring

/-- The (topological-space) closure of a subring of a topological ring is
itself a subring. -/
def subring.topological_closure (S : subring α) : subring α :=
{ carrier := closure (S : set α),
  ..S.to_submonoid.topological_closure,
  ..S.to_add_subgroup.topological_closure }

lemma subring.le_topological_closure (s : subring α) :
  s ≤ s.topological_closure := subset_closure

lemma subring.is_closed_topological_closure (s : subring α) :
  is_closed (s.topological_closure : set α) := by convert is_closed_closure

lemma subring.topological_closure_minimal
  (s : subring α) {t : subring α} (h : s ≤ t) (ht : is_closed (t : set α)) :
  s.topological_closure ≤ t := closure_minimal h ht

/-- If a subring of a topological ring is commutative, then so is its topological closure. -/
def subring.comm_ring_topological_closure [t2_space α] (s : subring α)
  (hs : ∀ (x y : s), x * y = y * x) : comm_ring s.topological_closure :=
{ ..s.topological_closure.to_ring,
  ..s.to_submonoid.comm_monoid_topological_closure hs }

end topological_semiring

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
  continuous_mul       := continuous_top,
  continuous_neg       := continuous_top}⟩

@[ext]
lemma ext' {f g : ring_topology α} (h : f.is_open = g.is_open) : f = g :=
by { ext : 2, exact h }

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
    apply continuous_Inf_rng.2,
    rintros _ ⟨⟨t, tr⟩, haS, rfl⟩, resetI,
    have h := continuous_Inf_dom (set.mem_image_of_mem to_topological_space haS) continuous_id,
    have h_continuous_id := @continuous.prod_map _ _ _ _ t t Inf_S' Inf_S' _ _ h h,
    exact @continuous.comp _ _ _ (id _) (id _) t _ _ continuous_add h_continuous_id,
  end,
  continuous_mul       :=
  begin
    apply continuous_Inf_rng.2,
    rintros _ ⟨⟨t, tr⟩, haS, rfl⟩, resetI,
    have h := continuous_Inf_dom (set.mem_image_of_mem to_topological_space haS) continuous_id,
    have h_continuous_id := @continuous.prod_map _ _ _ _ t t Inf_S' Inf_S' _ _ h h,
    exact @continuous.comp _ _ _ (id _) (id _) t _ _ continuous_mul h_continuous_id,
  end,
  continuous_neg       :=
  begin
    apply continuous_Inf_rng.2,
    rintros _ ⟨⟨t, tr⟩, haS, rfl⟩, resetI,
    have h := continuous_Inf_dom (set.mem_image_of_mem to_topological_space haS) continuous_id,
    exact @continuous.comp _ _ _ (id _) (id _) t _ _ continuous_neg h,
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

/-- The forgetful functor from ring topologies on `a` to additive group topologies on `a`. -/
def to_add_group_topology (t : ring_topology α) : add_group_topology α :=
{ to_topological_space     := t.to_topological_space,
  to_topological_add_group := @topological_ring.to_topological_add_group _ _ t.to_topological_space
    t.to_topological_ring }

/-- The order embedding from ring topologies on `a` to additive group topologies on `a`. -/
def to_add_group_topology.order_embedding : order_embedding (ring_topology α)
  (add_group_topology α) :=
order_embedding.of_map_le_iff to_add_group_topology $ λ _ _, iff.rfl

end ring_topology

section absolute_value

/-- Construct an absolute value on a semiring `T` from an absolute value on a semiring `R`
and an injective ring homomorphism `f : T →+* R` -/
def absolute_value.comp {R S T : Type*} [semiring T] [semiring R] [ordered_semiring S]
  (v : absolute_value R S) {f : T →+* R} (hf : function.injective f)  :
  absolute_value T S :=
{ to_fun := v ∘ f,
  map_mul' := by simp only [function.comp_app, map_mul, eq_self_iff_true, forall_const],
  nonneg' := by simp only [v.nonneg, forall_const],
  eq_zero' := by simp only [map_eq_zero_iff f hf, v.eq_zero, forall_const, iff_self],
  add_le' := by simp only [function.comp_app, map_add, v.add_le, forall_const], }

end absolute_value
