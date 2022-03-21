/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/

import algebra.squarefree
import ring_theory.unique_factorization_domain
import ring_theory.dedekind_domain.ideal

/-!

# Chains of divisors

The results in this file show that in the monoid `associates M` of a unique_factorization_monoid
`M`, an element `a` is an n-th prime power iff its set of divisors is a strictly increasing chain
of length `n + 1`, aka we can find strictly increasing bijection bewteen `fin (n + 1)` and
the set of factors of `a`

We can then use this to show that given `a b : M`, if there is an monotone bijection
between the sets of factors of `associates.mk a` and `associates.mk b` then the prime
factorisations of `a` and `b` have the same shape.


## Main results
- `prime_pow_has_chain` : existence of chain for prime powers
- `eq_prime_pow_of_has_chain` : elements that have a chain are prime powers
- `multiplicity_le_of_monotone` : if there is a monotone bijection `d` between the set
  of factors of `a : associates M` and the set of factors of `b : associates N` then
  for any prime `p ∣ a`, `multiplicity p a ≤ multiplicity (d p) b`.

## Todo
- show that under the assumptions of `multiplicity_le_of_monotone`, `d p` is prime. Applying
  `multiplicity_le_of_monotone` on `d.symm` then gives us `multiplicity p a = multiplicity (d p) b`

-/


section factorisations_same_shape

noncomputable theory
open_locale classical

open unique_factorization_monoid multiplicity irreducible

variables {M : Type*} [cancel_comm_monoid_with_zero M]

lemma multiplicity_eq_multiplicity_associates_mk [wf_dvd_monoid M] {p q : M} (hp : prime p)
  (hq : q ≠ 0) : multiplicity p q = multiplicity (associates.mk p) (associates.mk q) :=
begin
  have finite₁ := multiplicity.finite_prime_left hp hq,
  have finite₂ := multiplicity.finite_prime_left ((associates.prime_mk p).2 hp)
    (associates.mk_ne_zero.2 hq),
  apply le_antisymm,
  suffices : ↑((multiplicity p q).get finite₁) ≤ multiplicity (associates.mk p) (associates.mk q),
  { rw enat.coe_le_iff at this,
    exact enat.get_le_get.1 (this finite₂) },
  apply multiplicity.le_multiplicity_of_pow_dvd,
  rw [← associates.mk_pow, associates.mk_dvd_mk],
  exact multiplicity.pow_multiplicity_dvd finite₁,

  suffices : ↑((multiplicity (associates.mk p) (associates.mk q)).get finite₂) ≤ multiplicity p q,
  { rw enat.coe_le_iff at this,
    exact enat.get_le_get.1 (this finite₁) },
  apply multiplicity.le_multiplicity_of_pow_dvd,
  rw [← associates.mk_dvd_mk, associates.mk_pow],
  exact multiplicity.pow_multiplicity_dvd finite₂,
end

variable [unique_factorization_monoid M]

variables {N : Type*} [cancel_comm_monoid_with_zero N] [unique_factorization_monoid N]

lemma order_iso.map_eq_bot_iff {α β : Type*} [partial_order α] [partial_order β] [order_bot α]
  [order_bot β] {a : α} (f : α ≃o β) : f a = ⊥ ↔ a = ⊥ :=
⟨(λ h, by rw [(show a = f.symm ⊥, by simp only [← h, order_iso.symm_apply_apply]),
  order_iso.map_bot f.symm]), λ h, by rw [h, f.map_bot]⟩

variables [nontrivial M] [nontrivial N] {m : associates M}

instance : ordered_comm_monoid (associates M) :=
{ mul_le_mul_left := λ a b h c, by {obtain ⟨d, rfl⟩ := h, rw ← mul_assoc,
  exact associates.le_mul_right},
  ..associates.comm_monoid,
  ..associates.partial_order}

instance : canonically_ordered_monoid (associates M) :=
{ le_iff_exists_mul := λ a b, ⟨λ h, h, λ h, h⟩,
  ..associates.cancel_comm_monoid_with_zero,
  ..associates.bounded_order,
  ..associates.ordered_comm_monoid}

instance order_bot_divisors : order_bot {l : associates M // l ≤ m} :=
subtype.order_bot bot_le

@[simp]
lemma mem_subtype_eq_bot_iff {α : Type*} [preorder α] [order_bot α] {P : α → Prop}
  (Pbot : P ⊥) {x : α} (Px : P x) :
  (⟨x, Px⟩ : {y : α // P y}) = (subtype.order_bot Pbot).bot ↔ x = ⊥ := by simp



lemma associates.is_unit_iff_eq_bot {a : associates M}: is_unit a ↔ a = ⊥ :=
by rw [associates.is_unit_iff_eq_one, bot_eq_one]

lemma map_is_unit_of_monotone_is_unit {m u : associates M} {n : associates N}
  (hu : is_unit u) (hu' : u ≤ m)
  (d : {l : associates M // l ≤ m} ≃o {l : associates N // l ≤ n}) :
  is_unit (d ⟨u, hu'⟩ : associates N) :=
begin
  rw associates.is_unit_iff_eq_one,
  rw ← bot_eq_one,
  suffices : d ⟨u, hu'⟩ = ⟨⊥, bot_le⟩,
  { rw [subtype.ext_iff, subtype.coe_mk] at this,
    exact this },
  have : (⊥ :  {l : associates N // l ≤ n}) = ⟨⊥, bot_le⟩ := rfl,
  rw ← this,
  rw order_iso.map_eq_bot_iff d,
  rw associates.is_unit_iff_eq_one at hu,
  have : (⊥ :  {l : associates M // l ≤ m}) = ⟨⊥, bot_le⟩ := rfl,
  simp only [this, hu, bot_eq_one],
end

lemma map_is_unit_iff_is_unit {m u : associates M} {n : associates N} (hu' : u ≤ m)
  (d : {l : associates M // l ≤ m} ≃o {l : associates N // l ≤ n}) :
  is_unit u ↔ is_unit (d ⟨u, hu'⟩ : associates N) :=
⟨λ hu, map_is_unit_of_monotone_is_unit hu hu' d, λ hu, by
  { rw (show u = ↑(d.symm ⟨↑(d ⟨u, hu'⟩), (d ⟨u, hu'⟩).prop⟩), from by simp),
    exact map_is_unit_of_monotone_is_unit hu _ d.symm }⟩

variable (hm : m ≠ 0)


instance divisors_has_bot: has_bot {l : associates M // l ≤ m} :=
{ bot := ⟨(⊥ : associates M), show ⊥ ≤ m, from by exact bot_le⟩ }

lemma mem_divisors_eq_bot_iff {a : associates M} (ha : a ≤ m) : a = ⊥
  ↔ (⟨a, ha⟩ : {l : associates M // l ≤ m}) = ⟨⊥, bot_le⟩ := by simp

lemma divisors_bot : ↑(⟨⊥, bot_le⟩ : {l : associates M // l ≤ m}) = (⊥ : associates M) := rfl

lemma divisors_bot' : (@divisors_has_bot M _ _ _ m).bot = ⟨⊥, bot_le⟩ := rfl

lemma map_prime_of_monotone_equiv {m p : associates M} {n : associates N}
  (hn : n ≠ 0) (hp : p ∈ normalized_factors m)
  (d : {l : associates M // l ≤ m} ≃o {l : associates N // l ≤ n}) (hd : monotone d)
  (hd' : monotone d.symm) {s : ℕ} (hs : s ≠ 0) (hs' : p^s ≤ m) :
  irreducible (d ⟨p, dvd_of_mem_normalized_factors hp⟩ : associates N) :=
begin
  refine (associates.is_atom_iff (ne_zero_of_dvd_ne_zero hn (d ⟨p, _⟩).prop)).mp ⟨_, λ b hb, _⟩,
  { rw [ne.def, ← associates.is_unit_iff_eq_bot, ← map_is_unit_iff_is_unit
    (dvd_of_mem_normalized_factors hp) d],
    exact prime.not_unit (prime_of_normalized_factor p hp) },
  { obtain ⟨x, hx⟩ := d.surjective ⟨b, le_trans (le_of_lt hb)
      (d ⟨p, dvd_of_mem_normalized_factors hp⟩).prop⟩,
    rw [← subtype.coe_mk b _ , subtype.coe_lt_coe, ← hx] at hb,
    suffices : x = ⊥,
    { rw [this, order_iso.map_bot d, divisors_bot'] at hx,
      exact subtype.mk_eq_mk.mp hx.symm  },
    obtain ⟨a, ha⟩ := x,
    rw [divisors_bot', ← mem_divisors_eq_bot_iff],
    exact ((associates.is_atom_iff (prime.ne_zero (prime_of_normalized_factor p hp))).mpr
      (irreducible_of_normalized_factor p hp) ).right a (subtype.mk_lt_mk.mp (d.lt_iff_lt.mp hb)) },
end

variable [unique (units M)]

def associates.mk_monoid_equiv : M ≃* associates M := mul_equiv.of_bijective
  (@associates.mk_monoid_hom M _) ⟨associates.mk_injective, associates.mk_surjective⟩

variables [comm_ring M] [is_domain M] [is_dedekind_domain M]




end factorisations_same_shape
