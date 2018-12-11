/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
import tactic.ring data.quot ring_theory.ideals group_theory.submonoid

universe u

namespace localization

variables (α : Type u) [comm_ring α] (S : set α) [is_submonoid S]

def r : α × S → α × S → Prop :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, ∃ t ∈ S, (s₁ * r₂ - s₂ * r₁) * t = 0

local infix ≈ := r α S

section
variables {α S}
theorem r_of_eq : ∀{a₀ a₁ : α × S} (h : a₀.2.1 * a₁.1 = a₁.2.1 * a₀.1), a₀ ≈ a₁
| ⟨r₀, s₀, hs₀⟩ ⟨r₁, s₁, hs₁⟩ h := ⟨1, is_submonoid.one_mem S, by simp [h] at h ⊢⟩
end

theorem refl (x : α × S) : x ≈ x := r_of_eq rfl

theorem symm : ∀ (x y : α × S), x ≈ y → y ≈ x :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩, ⟨t, hts,
  calc (s₂ * r₁ - s₁ * r₂) * t = -((s₁ * r₂ - s₂ * r₁) * t) : by simp [add_mul]
    ... = 0 : by rw ht; simp⟩

theorem trans : ∀ (x y z : α × S), x ≈ y → y ≈ z → x ≈ z :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨t, hts, ht⟩ ⟨t', hts', ht'⟩,
⟨s₂ * t' * t, is_submonoid.mul_mem (is_submonoid.mul_mem hs₂ hts') hts,
  calc (s₁ * r₃ - s₃ * r₁) * (s₂ * t' * t) =
    t' * s₃ * ((s₁ * r₂ - s₂ * r₁) * t) + t * s₁ * ((s₂ * r₃ - s₃ * r₂) * t') :
      by simp [mul_left_comm, mul_add, mul_comm]
    ... = 0 : by rw [ht, ht']; simp⟩

instance : setoid (α × S) :=
⟨r α S, refl α S, symm α S, trans α S⟩

def loc := quotient $ localization.setoid α S

instance : has_add (loc α S) :=
⟨quotient.lift₂
  (λ x y : α × S, (⟦⟨x.2 * y.1 + y.2 * x.1, _, is_submonoid.mul_mem x.2.2 y.2.2⟩⟧ : loc α S)) $
  λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨r₄, s₄, hs₄⟩ ⟨t₅, hts₅, ht₅⟩ ⟨t₆, hts₆, ht₆⟩,
  quotient.sound ⟨t₆ * t₅, is_submonoid.mul_mem hts₆ hts₅,
    calc (s₁ * s₂ * (s₃ * r₄ + s₄ * r₃) - s₃ * s₄ * (s₁ * r₂ + s₂ * r₁)) * (t₆ * t₅) =
      s₁ * s₃ * ((s₂ * r₄ - s₄ * r₂) * t₆) * t₅ + s₂ * s₄ * ((s₁ * r₃ - s₃ * r₁) * t₅) * t₆ : by ring
      ... = 0 : by rw [ht₆, ht₅]; simp⟩⟩

instance : has_neg (loc α S) :=
⟨quotient.lift (λ x : α × S, (⟦⟨-x.1, x.2⟩⟧ : loc α S)) $
  λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
  quotient.sound ⟨t, hts,
    calc (s₁ * -r₂ - s₂ * -r₁) * t = -((s₁ * r₂ - s₂ * r₁) * t) : by ring
      ... = 0 : by rw ht; simp⟩⟩

instance : has_mul (loc α S) :=
⟨quotient.lift₂
  (λ x y : α × S, (⟦⟨x.1 * y.1, _, is_submonoid.mul_mem x.2.2 y.2.2⟩⟧ : loc α S)) $
  λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨r₄, s₄, hs₄⟩ ⟨t₅, hts₅, ht₅⟩ ⟨t₆, hts₆, ht₆⟩,
  quotient.sound ⟨t₆ * t₅, is_submonoid.mul_mem hts₆ hts₅,
    calc ((s₁ * s₂) * (r₃ * r₄) - (s₃ * s₄) * (r₁ * r₂)) * (t₆ * t₅) =
      t₆ * ((s₁ * r₃ - s₃ * r₁) * t₅) * r₂ * s₄ + t₅ * ((s₂ * r₄ - s₄ * r₂) * t₆) * r₃ * s₁ :
        by simp [mul_left_comm, mul_add, mul_comm]
      ... = 0 : by rw [ht₅, ht₆]; simp⟩⟩

def of_comm_ring : α → loc α S := λ r, ⟦⟨r, 1, is_submonoid.one_mem S⟩⟧

instance : comm_ring (loc α S) :=
by refine
{ add            := has_add.add,
  add_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  zero           := of_comm_ring α S 0,
  zero_add       := quotient.ind _,
  add_zero       := quotient.ind _,
  neg            := has_neg.neg,
  add_left_neg   := quotient.ind _,
  add_comm       := quotient.ind₂ _,
  mul            := has_mul.mul,
  mul_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  one            := of_comm_ring α S 1,
  one_mul        := quotient.ind _,
  mul_one        := quotient.ind _,
  left_distrib   := λ m n k, quotient.induction_on₃ m n k _,
  right_distrib  := λ m n k, quotient.induction_on₃ m n k _,
  mul_comm       := quotient.ind₂ _ };
{ intros,
  try {rcases a with ⟨r₁, s₁, hs₁⟩},
  try {rcases b with ⟨r₂, s₂, hs₂⟩},
  try {rcases c with ⟨r₃, s₃, hs₃⟩},
  refine (quotient.sound $ r_of_eq _),
  simp [mul_left_comm, mul_add, mul_comm] }

instance : is_ring_hom (of_comm_ring α S) :=
{ map_add := λ x y, quotient.sound $ by simp,
  map_mul := λ x y, quotient.sound $ by simp,
  map_one := rfl }

variable {α}

def away (x : α) := loc α (powers x)

instance away.comm_ring (x : α) : comm_ring (away x) :=
localization.comm_ring α (powers x)

section at_prime

variables (P : ideal α) [hp : ideal.is_prime P]
include hp

instance prime.is_submonoid :
  is_submonoid (set.compl ↑P) :=
{ one_mem := P.ne_top_iff_one.1 hp.1,
  mul_mem := λ x y hnx hny hxy, or.cases_on (hp.2 hxy) hnx hny }

def at_prime := loc α (set.compl P)

instance at_prime.comm_ring : comm_ring (at_prime P) :=
localization.comm_ring α (set.compl P)

instance at_prime.local_ring : is_local_ring (at_prime P) :=
local_of_nonunits_ideal
  (λ hze,
    let ⟨t, hts, ht⟩ := quotient.exact hze in
    hts $ have htz : t = 0, by simpa using ht,
      suffices (0:α) ∈ P, by rwa htz,
      P.zero_mem)
  (begin
    rintro ⟨⟨r₁, s₁, hs₁⟩⟩ ⟨⟨r₂, s₂, hs₂⟩⟩ hx hy hu,
    rcases is_unit_iff_exists_inv.1 hu with ⟨⟨⟨r₃, s₃, hs₃⟩⟩, hz⟩,
    rcases quotient.exact hz with ⟨t, hts, ht⟩,
    simp at ht,
    have : ∀ {r s hs}, (⟦⟨r, s, hs⟩⟧ : at_prime P) ∈ nonunits (at_prime P) → r ∈ P,
    { haveI := classical.dec,
      exact λ r s hs, not_imp_comm.1 (λ nr,
        is_unit_iff_exists_inv.2 ⟨⟦⟨s, r, nr⟩⟧,
          quotient.sound $ r_of_eq $ by simp [mul_comm]⟩) },
    have hr₃ := (hp.mem_or_mem_of_mul_eq_zero ht).resolve_right hts,
    have := (ideal.add_mem_iff_left _ _).1 hr₃,
    { exact not_or (mt hp.mem_or_mem (not_or hs₁ hs₂)) hs₃ (hp.mem_or_mem this) },
    { exact P.neg_mem (P.mul_mem_right
        (P.add_mem (P.mul_mem_left (this hy)) (P.mul_mem_left (this hx)))) }
  end)

end at_prime

variable (α)

def non_zero_divisors : set α := {x | ∀ z, z * x = 0 → z = 0}

instance non_zero_divisors.is_submonoid : is_submonoid (non_zero_divisors α) :=
{ one_mem := λ z hz, by simpa using hz,
  mul_mem := λ x₁ x₂ hx₁ hx₂ z hz,
    have z * x₁ * x₂ = 0, by rwa mul_assoc,
    hx₁ z $ hx₂ (z * x₁) this }

def quotient_ring := loc α (non_zero_divisors α)

instance quotient_ring.comm_ring : comm_ring (quotient_ring α) :=
localization.comm_ring α (non_zero_divisors α)

section quotient_ring

variables {β : Type u} [integral_domain β] [decidable_eq β]

lemma ne_zero_of_mem_non_zero_divisors {x : β}
  (hm : x ∈ localization.non_zero_divisors β) : x ≠ 0 | hz :=
zero_ne_one (hm 1 (by simpa)).symm

lemma eq_zero_of_ne_zero_of_mul_eq_zero {x y : β} :
  x ≠ 0 → y * x = 0 → y = 0 :=
λ hnx hxy, or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

lemma mem_non_zero_divisors_of_ne_zero {x : β} :
  x ≠ 0 → x ∈ localization.non_zero_divisors β :=
λ hnx z, eq_zero_of_ne_zero_of_mul_eq_zero hnx

variable (β)

def inv_aux : β × (non_zero_divisors β) → quotient_ring β :=
λ ⟨r, s, hs⟩, if h : r = 0 then 0 else ⟦⟨s, r, mem_non_zero_divisors_of_ne_zero h⟩⟧

instance : has_inv (quotient_ring β) :=
⟨quotient.lift (inv_aux β) $
  λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
  begin
    have hrs : s₁ * r₂ = 0 + s₂ * r₁,
      from sub_eq_iff_eq_add.1 (hts _ ht),
    by_cases hr₁ : r₁ = 0;
    by_cases hr₂ : r₂ = 0;
    simp [hr₁, hr₂] at hrs; simp [inv_aux, hr₁, hr₂],
    { exfalso,
      exact ne_zero_of_mem_non_zero_divisors hs₁ hrs },
    { exfalso,
      exact ne_zero_of_mem_non_zero_divisors hs₂ hrs },
    { apply r_of_eq,
      simpa [mul_comm] using hrs.symm }
  end⟩

instance : decidable_eq (quotient_ring β) :=
@quotient.decidable_eq (β × non_zero_divisors β) (localization.setoid β (non_zero_divisors β)) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, show decidable (∃ t ∈ non_zero_divisors β, (s₁ * r₂ - s₂ * r₁) * t = 0),
from decidable_of_iff (s₁ * r₂ - s₂ * r₁ = 0)
⟨λ H, ⟨1, λ y, (mul_one y).symm ▸ id, H.symm ▸ zero_mul _⟩,
λ ⟨t, ht1, ht2⟩, or.resolve_right (mul_eq_zero.1 ht2) $ λ ht,
  one_ne_zero (ht1 1 ((one_mul t).symm ▸ ht))⟩

def quotient_ring.field.of_integral_domain : discrete_field (quotient_ring β) :=
by refine
{ inv            := has_inv.inv,
  zero_ne_one    := λ hzo,
    let ⟨t, hts, ht⟩ := quotient.exact hzo in
    zero_ne_one (by simpa using hts _ ht : 0 = 1),
  mul_inv_cancel := quotient.ind _,
  inv_mul_cancel := quotient.ind _,
  has_decidable_eq := localization.decidable_eq β,
  inv_zero := dif_pos rfl,
  .. localization.comm_ring β _ };
{ intros x hnx,
  rcases x with ⟨x, z, hz⟩,
  have : x ≠ 0,
    from assume hx, hnx (quotient.sound $ r_of_eq $ by simp [hx]),
  simp [has_inv.inv, inv_aux, inv_aux._match_1, this],
  exact (quotient.sound $ r_of_eq $ by simp; ring) }

end quotient_ring

end localization
