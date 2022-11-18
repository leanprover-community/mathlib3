/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import algebra.star.subalgebra
import topology.algebra.algebra
import topology.algebra.star

/-!
# Topological star (sub)algebras

A topological star algebra over a topological semiring `R` is a topological semiring with a
compatible continuous scalar multiplication by elements of `R` and a continuous star operation.
We reuse typeclass `has_continuous_smul` for topological algebras.

## Results

This is just a minimal stub for now!

The topological closure of a star subalgebra is still a star subalgebra,
which as a star algebra is a topological star algebra.
-/

open classical set topological_space
open_locale classical

namespace star_subalgebra

section topological_star_algebra
variables {R A B : Type*} [comm_semiring R] [star_ring R]
variables [topological_space A] [semiring A] [algebra R A] [star_ring A] [star_module R A]

instance [topological_space R] [has_continuous_smul R A] (s : star_subalgebra R A) :
  has_continuous_smul R s :=
s.to_subalgebra.has_continuous_smul

instance [topological_semiring A] (s : star_subalgebra R A) : topological_semiring s :=
s.to_subalgebra.topological_semiring

/-- The `star_subalgebra.inclusion` of a star subalgebra is an `embedding`. -/
lemma embedding_inclusion {S₁ S₂ : star_subalgebra R A} (h : S₁ ≤ S₂) :
  embedding (inclusion h) :=
{ induced := eq.symm induced_compose,
  inj := subtype.map_injective h function.injective_id }

/-- The `star_subalgebra.inclusion` of a closed star subalgebra is a `closed_embedding`. -/
lemma closed_embedding_inclusion {S₁ S₂ : star_subalgebra R A} (h : S₁ ≤ S₂)
  (hS₁ : is_closed (S₁ : set A)) :
  closed_embedding (inclusion h) :=
{ closed_range := is_closed_induced_iff.2
    ⟨S₁, hS₁, by { convert (set.range_subtype_map id _).symm, rw set.image_id, refl }⟩,
  .. embedding_inclusion h }

variables [topological_semiring A] [has_continuous_star A]
variables [topological_space B] [semiring B] [algebra R B] [star_ring B
]
/-- The closure of a star subalgebra in a topological star algebra as a star subalgebra. -/
def topological_closure (s : star_subalgebra R A) :
  star_subalgebra R A :=
{ carrier := closure (s : set A),
  star_mem' := λ a ha, map_mem_closure continuous_star ha (λ x, (star_mem : x ∈ s → star x ∈ s)),
  .. s.to_subalgebra.topological_closure }

@[simp] lemma topological_closure_coe (s : star_subalgebra R A) :
  (s.topological_closure : set A) = closure (s : set A) :=
rfl

lemma le_topological_closure (s : star_subalgebra R A) : s ≤ s.topological_closure :=
subset_closure

lemma is_closed_topological_closure (s : star_subalgebra R A) :
  is_closed (s.topological_closure : set A) :=
is_closed_closure

instance {A : Type*} [uniform_space A] [complete_space A] [semiring A] [star_ring A]
  [topological_semiring A] [has_continuous_star A] [algebra R A] [star_module R A]
  {S : star_subalgebra R A} : complete_space S.topological_closure :=
is_closed_closure.complete_space_coe

lemma topological_closure_minimal {s t : star_subalgebra R A} (h : s ≤ t)
  (ht : is_closed (t : set A)) : s.topological_closure ≤ t :=
closure_minimal h ht

lemma topological_closure_mono : monotone (topological_closure : _ → star_subalgebra R A) :=
λ S₁ S₂ h, topological_closure_minimal (h.trans $ le_topological_closure S₂)
  (is_closed_topological_closure S₂)

/-- If a star subalgebra of a topological star algebra is commutative, then so is its topological
closure. See note [reducible non-instances]. -/
@[reducible]
def comm_semiring_topological_closure [t2_space A] (s : star_subalgebra R A)
  (hs : ∀ (x y : s), x * y = y * x) : comm_semiring s.topological_closure :=
s.to_subalgebra.comm_semiring_topological_closure hs

/-- If a star subalgebra of a topological star algebra is commutative, then so is its topological
closure. See note [reducible non-instances]. -/
@[reducible]
def comm_ring_topological_closure {R A} [comm_ring R] [star_ring R] [topological_space A] [ring A]
  [algebra R A] [star_ring A] [star_module R A] [topological_ring A] [has_continuous_star A]
  [t2_space A] (s : star_subalgebra R A) (hs : ∀ (x y : s), x * y = y * x) :
  comm_ring s.topological_closure :=
s.to_subalgebra.comm_ring_topological_closure hs

/-- Continuous `star_alg_hom`s from the the topological closure of a `star_subalgebra` whose
compositions with the `star_subalgebra.inclusion` map agree are, in fact, equal. -/
lemma _root_.star_alg_hom.ext_topological_closure [t2_space B] {S : star_subalgebra R A}
  {φ ψ : S.topological_closure →⋆ₐ[R] B} (hφ : continuous φ) (hψ : continuous ψ)
  (h : φ.comp (inclusion (le_topological_closure S))
    = ψ.comp (inclusion (le_topological_closure S))) :
  φ = ψ :=
begin
  rw fun_like.ext'_iff,
  have : dense (set.range $ inclusion (le_topological_closure S)),
  { refine embedding_subtype_coe.to_inducing.dense_iff.2 (λ x, _),
    convert (show ↑x ∈ closure (S : set A), from x.prop),
    rw ←set.range_comp,
    exact set.ext (λ y, ⟨by { rintro ⟨y, rfl⟩, exact y.prop }, λ hy, ⟨⟨y, hy⟩, rfl⟩⟩), },
  refine continuous.ext_on this hφ hψ _,
  rintro _ ⟨x, rfl⟩,
  simpa only using fun_like.congr_fun h x,
end

lemma _root_.star_alg_hom_class.ext_topological_closure [t2_space B] {F : Type*}
  {S : star_subalgebra R A} [star_alg_hom_class F R S.topological_closure B] {φ ψ : F}
  (hφ : continuous φ) (hψ : continuous ψ)
  (h : ∀ x : S, φ ((inclusion (le_topological_closure S) x))
    = ψ ((inclusion (le_topological_closure S)) x)) :
  φ = ψ :=
begin
  have : (φ : S.topological_closure →⋆ₐ[R] B) = (ψ : S.topological_closure →⋆ₐ[R] B),
  { refine star_alg_hom.ext_topological_closure hφ hψ (star_alg_hom.ext _);
    simpa only [star_alg_hom.coe_comp, star_alg_hom.coe_coe] using h },
  simpa only [fun_like.ext'_iff, star_alg_hom.coe_coe],
end

end topological_star_algebra

end star_subalgebra

section elemental

open star_subalgebra

variables (R : Type*) {A B : Type*} [comm_semiring R] [star_ring R]
variables [topological_space A] [semiring A] [star_ring A] [topological_semiring A]
variables [has_continuous_star A] [algebra R A] [star_module R A]
variables [topological_space B] [semiring B] [star_ring B] [algebra R B]

/-- The topological closure of the subalgebra generated by a single element. -/
def elemental_star_algebra (x : A) : star_subalgebra R A :=
(adjoin R ({x} : set A)).topological_closure

namespace elemental_star_algebra

lemma self_mem (x : A) : x ∈ elemental_star_algebra R x :=
set_like.le_def.mp (le_topological_closure _) (self_mem_adjoin_singleton R x)

lemma star_self_mem (x : A) : star x ∈ elemental_star_algebra R x :=
star_mem $ self_mem R x

/-- The `elemental_star_algebra` generated by a normal element is commutative. -/
instance [t2_space A] {x : A} [is_star_normal x] : comm_semiring (elemental_star_algebra R x) :=
star_subalgebra.comm_semiring_topological_closure _ mul_comm

/-- The `elemental_star_algebra` generated by a normal element is commutative. -/
instance {R A} [comm_ring R] [star_ring R] [topological_space A] [ring A] [algebra R A]
  [star_ring A] [star_module R A] [topological_ring A] [has_continuous_star A] [t2_space A]
  {x : A} [is_star_normal x] : comm_ring (elemental_star_algebra R x) :=
star_subalgebra.comm_ring_topological_closure _ mul_comm

protected lemma is_closed (x : A) : is_closed (elemental_star_algebra R x : set A) :=
is_closed_closure

instance {A : Type*} [uniform_space A] [complete_space A] [semiring A] [star_ring A]
  [topological_semiring A] [has_continuous_star A] [algebra R A] [star_module R A] (x : A) :
  complete_space (elemental_star_algebra R x) :=
is_closed_closure.complete_space_coe

lemma le_of_is_closed_of_mem {S : star_subalgebra R A} (hS : is_closed (S : set A)) {x : A}
  (hx : x ∈ S) : elemental_star_algebra R x ≤ S :=
topological_closure_minimal (adjoin_le $ set.singleton_subset_iff.2 hx) hS

/-- The coercion from an elemental algebra to the full algebra as a `closed_embedding`. -/
lemma closed_embedding_coe (x : A) : closed_embedding (coe : elemental_star_algebra R x → A) :=
{ induced := rfl,
  inj := subtype.coe_injective,
  closed_range :=
  begin
    convert elemental_star_algebra.is_closed R x,
    exact set.ext (λ y, ⟨by {rintro ⟨y, rfl⟩, exact y.prop}, λ hy, ⟨⟨y, hy⟩, rfl⟩⟩),
  end }

lemma star_alg_hom_class_ext [t2_space B] {F : Type*} {a : A}
  [star_alg_hom_class F R (elemental_star_algebra R a) B] {φ ψ : F} (hφ : continuous φ)
  (hψ : continuous ψ) (h : φ ⟨a, self_mem R a⟩ = ψ ⟨a, self_mem R a⟩) :
  φ = ψ :=
begin
  refine star_alg_hom_class.ext_topological_closure hφ hψ (λ x, adjoin_induction' x _ _ _ _ _),
  exacts [λ y hy, by simpa only [set.mem_singleton_iff.mp hy] using h,
    λ r, by simp only [alg_hom_class.commutes],
    λ x y hx hy, by simp only [map_add, hx, hy],
    λ x y hx hy, by simp only [map_mul, hx, hy],
    λ x hx, by simp only [map_star, hx]],
end

end elemental_star_algebra

end elemental
