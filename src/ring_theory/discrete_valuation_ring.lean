/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import ring_theory.principal_ideal_domain order.conditionally_complete_lattice
import ring_theory.multiplicity
import ring_theory.valuation.basic
import tactic

/-!
# Discrete valuation rings

This file defines discrete valuation rings (DVRs) and develops a basic interface
for them.

## Important definitions

There are various definitions of a DVR in the literature; we define a DVR to be a local PID
which is a not a field (the first definition on Wikipedia) and prove that this is equivalent
to being a PID with a unique non-zero prime ideal (the definition in Serre's
book "Local Fields").

Let R be an integral domain, assumed to be a principal ideal ring and a local ring.

* `DVR R` : a predicate expresing that R is a DVR

### Notation

It's a theorem that an element of a DVR is a uniformiser if and only if it's irreducible.
We do not hence define `uniformiser` at all, because we can use `irreducible` instead.

### Definitions

## Implementation notes

## Tags

discrete valuation ring
-/

open_locale classical

universe u

open ideal local_ring

/-- A commutative ring is a discrete valuation ring if it's a local PID which is not a field -/
class discrete_valuation_ring (R : Type u) [integral_domain R]
  extends is_principal_ideal_ring R, local_ring R : Prop :=
(not_a_field' : maximal_ideal R ≠ ⊥)

namespace discrete_valuation_ring

variables (R : Type u) [integral_domain R] [discrete_valuation_ring R]

def not_a_field : maximal_ideal R ≠ ⊥ := not_a_field'

variable {R}

open principal_ideal_ring

/-- An element of a DVR is irreducible iff it is a uniformiser, that is, generates the
  maximal ideal of R -/
theorem irreducible_iff_uniformiser (ϖ : R) :
  irreducible ϖ ↔ maximal_ideal R = ideal.span {ϖ} :=
⟨λ hϖ, (eq_maximal_ideal (is_maximal_of_irreducible hϖ)).symm,
begin
  intro h,
  have h2 : ¬(is_unit ϖ) := show ϖ ∈ maximal_ideal R,
    from h.symm ▸ submodule.mem_span_singleton_self ϖ,
  split, exact h2,
  intros a b hab,
  by_contra h,
  push_neg at h,
  cases h with ha hb,
  change a ∈ maximal_ideal R at ha,
  change b ∈ maximal_ideal R at hb,
  rw h at ha hb,
  rw mem_span_singleton' at ha hb,
  rcases ha with ⟨a, rfl⟩,
  rcases hb with ⟨b, rfl⟩,
  rw (show a * ϖ * (b * ϖ) = ϖ * (ϖ * (a * b)), by ring) at hab,
  have h3 := eq_zero_of_mul_eq_self_right _ hab.symm,
  { apply not_a_field R,
    simp [h, h3]},
  { intro hh, apply h2,
    refine is_unit_of_dvd_one ϖ _,
    use a * b, exact hh.symm}
end⟩

variable (R)

/-- Uniformisers exist in a DVR -/
theorem exists_irreducible : ∃ ϖ : R, irreducible ϖ :=
by {simp_rw [irreducible_iff_uniformiser],
    exact (is_principal_ideal_ring.principal $ maximal_ideal R).principal}

/-- an integral domain is a DVR iff it's a PID with a unique non-zero prime ideal -/
theorem iff_PID_with_one_nonzero_prime (R : Type u) [integral_domain R] :
  discrete_valuation_ring R ↔ is_principal_ideal_ring R ∧ ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P :=
begin
  split,
  { intro RDVR,
    rcases id RDVR with ⟨RPID, Rlocal, Rnotafield⟩,
    split, assumption,
    resetI,
    use local_ring.maximal_ideal R,
    split, split,
    { assumption},
    { apply_instance},
    { rintro Q ⟨hQ1, hQ2⟩,
      obtain ⟨q, rfl⟩ := (is_principal_ideal_ring.principal Q).1,
      have hq : q ≠ 0,
      { rintro rfl,
        apply hQ1,
        simp,
      },
      erw span_singleton_prime hq at hQ2,
      replace hQ2 := irreducible_of_prime hQ2,
      rw irreducible_iff_uniformiser at hQ2,
      exact hQ2.symm}},
  { rintro ⟨RPID, Punique⟩,
    haveI : local_ring R := local_of_unique_nonzero_prime R Punique,
    refine {not_a_field' := _},
    rcases Punique with ⟨P, ⟨hP1, hP2⟩, hP3⟩,
    have hPM : P ≤ maximal_ideal R := le_maximal_ideal (hP2.1),
    intro h, rw [h, le_bot_iff] at hPM, exact hP1 hPM}
end

lemma associated_of_irreducible {a b : R} (ha : irreducible a) (hb : irreducible b) :
  associated a b :=
begin
  rw irreducible_iff_uniformiser at ha hb,
  rw [←span_singleton_eq_span_singleton, ←ha, hb],
end

end discrete_valuation_ring

/-
Serre:
"The non-zero ideals of A are of the form pi^n A, where pi is a uniformiser.
If x ≠ 0 is any element of A, one can write x = pi^n u, with n ∈ ℕ and u invertible;
the integer n is called the valuation of x and is denoted v(x); it doesn't depends
on the choice of pi. We make the convention that v(0)=+infty."
-/

-- this shoudl be somewhere else
noncomputable def add_valuation {R : Type*} [comm_ring R] (I : ideal R) (r : R) : enat :=
multiplicity I (span {r} : ideal R)

--instance foo : partial_order enat := by apply_instance
--instance : partial_order (multiplicative enat) := foo

-- want type T
-- T = {0} ∪ {g^n : n ∈ ℤ}, 0 <

-- C∞₀

#where

def C_infty₀ := with_zero (multiplicative ℤ)

#exit
-- R : DVR, canonical map R -> enat; Frac(R) -> ℤ ∪ {∞} canonical
-- v: Frac(R) -> ℝ≥0, v(ϖ) ∈ (0,1), not sure where to put it
-- v : Frac(R) -> Γ, v(ϖ) = "-1" 
-- R=Z_p, ϖ = p, traditionally v(ϖ) = 1/p ∈ ℝ≥0
-- R = ℂ[[T]], ϖ = T, v(ϖ) = anything in (0,1)
-- but the map from R to Γ is canonical 
-- If t ∈ ℝ>0 then x ↦ x^t is an isomorphism of groups-with-zero ℝ≥0 → ℝ≥0 , sending 0 to 0 and 1 to 1




set_option old_structure_cmd true

section prio
-- look this up later
class linear_ordered_comm_group (G : Type u) extends ordered_comm_group G, linear_order G.
end prio

namespace with_zero

instance (G : Type*) [group G] : group_with_zero (with_zero G) :=
{ inv_zero := with_zero.inv_zero,
  mul_inv_cancel := with_zero.mul_right_inv,
  .. with_zero.monoid,
  .. with_zero.mul_zero_class,
  .. with_zero.has_inv,
  .. with_zero.nonzero }

instance (G : Type u) [comm_group G] : comm_group_with_zero (with_zero G) :=
  {.. with_zero.group_with_zero G,
   .. with_zero.comm_monoid }

lemma zero_le {G : Type u} [partial_order G] (x : with_zero G) : 0 ≤ x :=
bot_le

lemma le_zero_iff {G : Type u} [partial_order G] (x : with_zero G) : x ≤ 0 ↔ x = 0 :=
le_bot_iff

lemma eq_zero_or_coe {G : Type u} : ∀ x : with_zero G, x = 0 ∨ ∃ y : G, ↑y = x
| none     := or.inl rfl
| (some y) := or.inr ⟨y, rfl⟩

lemma coe_le_coe {G : Type u} [partial_order G] {x y : G} : (x : with_zero G) ≤ y ↔ x ≤ y :=
with_bot.coe_le_coe

instance (G : Type u) [linear_ordered_comm_group G] : linear_ordered_comm_group_with_zero (with_zero G) :=
{ mul_le_mul_left := begin
    intros a b hab c,
    rcases eq_zero_or_coe a with rfl | ⟨a, rfl⟩, { rw mul_zero, exact with_zero.zero_le _ },
    rcases eq_zero_or_coe b with rfl | ⟨b, rfl⟩, { rw le_zero_iff at hab, cases hab },
    rw with_bot.coe_le_coe at hab,
    rcases eq_zero_or_coe c with rfl | ⟨c, rfl⟩, { rw [zero_mul, zero_mul], exact le_refl _ },
    rw [mul_coe, mul_coe, with_bot.coe_le_coe], exact mul_le_mul_left' hab
  end,
  zero_le_one := with_zero.zero_le _,
  .. with_zero.comm_group_with_zero G,
  .. with_zero.linear_order }

end with_zero

instance {α : Type u} [h : has_le α] : has_le (multiplicative α) := h
instance {α : Type u} [h : preorder α] : preorder (multiplicative α) := h
instance {α : Type u} [h : partial_order α] : partial_order (multiplicative α) := h
instance {α : Type u} [h : linear_order α] : linear_order (multiplicative α) := h

instance (G : Type u) [ordered_add_comm_group G] : ordered_comm_group (multiplicative G) :=
{ mul_le_mul_left := @add_le_add_left G _,
  ..(by apply_instance : comm_group (multiplicative G)),
  ..(by apply_instance : partial_order (multiplicative G)) }

instance (G : Type u) [decidable_linear_ordered_add_comm_group G] : linear_ordered_comm_group (multiplicative G) :=
{ ..(by apply_instance : ordered_comm_group (multiplicative G)),
  ..(by apply_instance : linear_order (multiplicative G)) }

instance : linear_ordered_comm_group_with_zero Γ := by dunfold Γ; apply_instance

instance baz : add_comm_monoid enat := by apply_instance

--def sdfsdf : ℕ →+ ℤ := nat.cast_add_monoid_hom _

noncomputable def qux : enat → with_zero (multiplicative ℤ)
| ⟨P, n⟩ := if H : P then ↑(multiplicative.of_add (n H) : multiplicative ℤ)⁻¹ else 0

def hom_with_zero {α β} [monoid α] [monoid β] (f : α →* β) : α →* with_zero β :=
{ to_fun := some ∘ f,
  map_one' := congr_arg some f.map_one,
  map_mul' := λ x y, congr_arg some $ f.map_mul _ _ }

def foo (n : enat) [decidable n.dom] : with_zero (multiplicative ℤ) :=
n.to_option.map $ λ k, multiplicative.of_add (-k)

theorem foo_top' : foo ⊤ = 0 := rfl
theorem foo_top {h : decidable (⊤ : enat).dom} : foo ⊤ = 0 := by convert foo_top'

theorem foo_coe' (n : ℕ) : foo (n : ℕ) = ↑(multiplicative.of_add (-n : ℤ)) := rfl
theorem foo_coe (n : ℕ) {h : decidable (n : enat).dom} :
  foo (n : ℕ) = ↑(multiplicative.of_add (-n : ℤ)) := by convert foo_coe' n

open_locale classical

theorem foo_add (x y) : foo (x + y) = foo x * foo y :=
begin
  refine enat.cases_on x _ (λ m, _),
  { simp_rw [enat.top_add, foo_top, zero_mul] },
  refine enat.cases_on y _ (λ n, _),
  { simp_rw [enat.add_top, foo_top, mul_zero] },
  simp_rw [← enat.coe_add, foo_coe, int.coe_nat_add, neg_add, of_add_add, ← with_zero.mul_coe]
end

theorem of_add_le {α : Type u} [has_le α] {x y : α} :
  multiplicative.of_add x ≤ multiplicative.of_add y ↔ x ≤ y :=
iff.rfl



theorem foo_le (x y) : foo x ≤ foo y ↔ y ≤ x :=
begin
  refine enat.cases_on x _ (λ m, _),
  { simp_rw [foo_top, with_zero.zero_le, le_top] },
  refine enat.cases_on y _ (λ n, _),
  { simp_rw [foo_top, with_zero.le_zero_iff, foo_coe, top_le_iff, with_zero.coe_ne_zero, enat.coe_ne_top] },
  simp_rw [foo_coe, with_zero.coe_le_coe, of_add_le, neg_le_neg_iff, int.coe_nat_le, enat.coe_le_coe]
end


-- instance : complete_lattice enat :=  by apply_instance


/-
Serre then proves that if A is a commutative ring, it's a DVR iff it's Noetherian and
local, and its maximal ideal is generated by a non-nilpotent element.
-/


/-
Wikipedia:
In abstract algebra, a discrete valuation ring (DVR) is a principal ideal domain (PID)
with exactly one non-zero maximal ideal.

This means a DVR is an integral domain R which satisfies any one of the following equivalent conditions:

-- USED    R is a local principal ideal domain, and not a field.
    R is a valuation ring with a value group isomorphic to the integers under addition.
    R is a local Dedekind domain and not a field.
    R is a Noetherian local domain whose maximal ideal is principal, and not a field.[1]
    R is an integrally closed Noetherian local ring with Krull dimension one.
-- WORKING ON THIS    R is a principal ideal domain with a unique non-zero prime ideal.
    R is a principal ideal domain with a unique irreducible element (up to multiplication by units).
    R is a unique factorization domain with a unique irreducible element (up to multiplication by units).
    R is Noetherian, not a field, and every nonzero fractional ideal of R is irreducible in the sense that it cannot be written as a finite intersection of fractional ideals properly containing it.
    There is some discrete valuation ν on the field of fractions K of R such that R = {x : x in K, ν(x) ≥ 0}.

Serre defines a DVR to be a PID with a unique non-zero prime ideal and one can build the
theory relatively quickly from this.
-/
