/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
import tactic.ring data.quot ring_theory.ideal_operations group_theory.submonoid

universes u v

namespace localization

variables (α : Type u) [comm_ring α] (S : set α) [is_submonoid S]

def r (x y : α × S) : Prop :=
∃ t ∈ S, ((x.2 : α) * y.1 - y.2 * x.1) * t = 0

local infix ≈ := r α S

section
variables {α S}
theorem r_of_eq {a₀ a₁ : α × S} (h : (a₀.2 : α) * a₁.1 = a₁.2 * a₀.1) : a₀ ≈ a₁ :=
⟨1, is_submonoid.one_mem S, by rw [h, sub_self, mul_one]⟩
end

theorem refl (x : α × S) : x ≈ x := r_of_eq rfl

theorem symm (x y : α × S) : x ≈ y → y ≈ x :=
λ ⟨t, hts, ht⟩, ⟨t, hts, by rw [← neg_sub, ← neg_mul_eq_neg_mul, ht, neg_zero]⟩

theorem trans : ∀ (x y z : α × S), x ≈ y → y ≈ z → x ≈ z :=
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨t, hts, ht⟩ ⟨t', hts', ht'⟩,
⟨s₂ * t' * t, is_submonoid.mul_mem (is_submonoid.mul_mem hs₂ hts') hts,
  calc (s₁ * r₃ - s₃ * r₁) * (s₂ * t' * t) =
    t' * s₃ * ((s₁ * r₂ - s₂ * r₁) * t) + t * s₁ * ((s₂ * r₃ - s₃ * r₂) * t') :
      by simp [mul_left_comm, mul_add, mul_comm]
    ... = 0 : by simp only [subtype.coe_mk] at ht ht'; rw [ht, ht']; simp⟩

instance : setoid (α × S) :=
⟨r α S, refl α S, symm α S, trans α S⟩

def loc := quotient $ localization.setoid α S

instance : has_add (loc α S) :=
⟨quotient.lift₂
  (λ x y : α × S, (⟦⟨x.2 * y.1 + y.2 * x.1, x.2 * y.2⟩⟧ : loc α S)) $
  λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨r₄, s₄, hs₄⟩ ⟨t₅, hts₅, ht₅⟩ ⟨t₆, hts₆, ht₆⟩,
  quotient.sound ⟨t₆ * t₅, is_submonoid.mul_mem hts₆ hts₅,
    calc (s₁ * s₂ * (s₃ * r₄ + s₄ * r₃) - s₃ * s₄ * (s₁ * r₂ + s₂ * r₁)) * (t₆ * t₅) =
      s₁ * s₃ * ((s₂ * r₄ - s₄ * r₂) * t₆) * t₅ + s₂ * s₄ * ((s₁ * r₃ - s₃ * r₁) * t₅) * t₆ : by ring
      ... = 0 : by simp only [subtype.coe_mk] at ht₅ ht₆; rw [ht₆, ht₅]; simp⟩⟩

instance : has_neg (loc α S) :=
⟨quotient.lift (λ x : α × S, (⟦⟨-x.1, x.2⟩⟧ : loc α S)) $
  λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
  quotient.sound ⟨t, hts,
    calc (s₁ * -r₂ - s₂ * -r₁) * t = -((s₁ * r₂ - s₂ * r₁) * t) : by ring
      ... = 0 : by simp only [subtype.coe_mk] at ht; rw ht; simp⟩⟩

instance : has_mul (loc α S) :=
⟨quotient.lift₂
  (λ x y : α × S, (⟦⟨x.1 * y.1, x.2 * y.2⟩⟧ : loc α S)) $
  λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨r₃, s₃, hs₃⟩ ⟨r₄, s₄, hs₄⟩ ⟨t₅, hts₅, ht₅⟩ ⟨t₆, hts₆, ht₆⟩,
  quotient.sound ⟨t₆ * t₅, is_submonoid.mul_mem hts₆ hts₅,
    calc ((s₁ * s₂) * (r₃ * r₄) - (s₃ * s₄) * (r₁ * r₂)) * (t₆ * t₅) =
      t₆ * ((s₁ * r₃ - s₃ * r₁) * t₅) * r₂ * s₄ + t₅ * ((s₂ * r₄ - s₄ * r₂) * t₆) * r₃ * s₁ :
        by simp [mul_left_comm, mul_add, mul_comm]
      ... = 0 : by simp only [subtype.coe_mk] at ht₅ ht₆; rw [ht₅, ht₆]; simp⟩⟩

variables {α S}

def of (r : α) (s : S) : loc α S := ⟦(r, s)⟧

instance : comm_ring (loc α S) :=
by refine
{ add            := has_add.add,
  add_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  zero           := of 0 1,
  zero_add       := quotient.ind _,
  add_zero       := quotient.ind _,
  neg            := has_neg.neg,
  add_left_neg   := quotient.ind _,
  add_comm       := quotient.ind₂ _,
  mul            := has_mul.mul,
  mul_assoc      := λ m n k, quotient.induction_on₃ m n k _,
  one            := of 1 1,
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

instance of.is_ring_hom : is_ring_hom (λ x, of x 1 : α → loc α S) :=
{ map_add := λ x y, quotient.sound $ by simp,
  map_mul := λ x y, quotient.sound $ by simp,
  map_one := rfl }

instance : has_coe α (loc α S) := ⟨λ x, of x 1⟩

instance coe.is_ring_hom : is_ring_hom (coe : α → loc α S) :=
localization.of.is_ring_hom

section
variables (α S) (x y : α) (n : ℕ)
@[simp] lemma of_one : (of 1 1 : loc α S) = 1 := rfl
@[simp] lemma of_add : (of (x + y) 1 : loc α S) = of x 1 + of y 1 :=
by apply of.is_ring_hom.map_add

@[simp] lemma of_sub : (of (x - y) 1 : loc α S) = of x 1 - of y 1 :=
@@is_ring_hom.map_sub _ _ (λ x, of x 1) of.is_ring_hom

@[simp] lemma of_mul : (of (x * y) 1 : loc α S) = of x 1 * of y 1 :=
@@is_ring_hom.map_mul _ _ (λ x, of x 1) of.is_ring_hom

@[simp] lemma of_neg : (of (-x) 1 : loc α S) = -of x 1 :=
@@is_ring_hom.map_neg _ _ (λ x, of x 1) of.is_ring_hom

@[simp] lemma of_pow : (of (x ^ n) 1 : loc α S) = (of x 1) ^ n :=
@@is_semiring_hom.map_pow _ _ (λ x, of x 1) (@@is_ring_hom.is_semiring_hom _ _ _ of.is_ring_hom) x n

@[simp] lemma coe_zero : ((0 : α) : loc α S) = 0 := rfl
@[simp] lemma coe_one : ((1 : α) : loc α S) = 1 := rfl
@[simp] lemma coe_add : (↑(x + y) : loc α S) = x + y := of_add _ _ _ _
@[simp] lemma coe_sub : (↑(x - y) : loc α S) = x - y := of_sub _ _ _ _
@[simp] lemma coe_mul : (↑(x * y) : loc α S) = x * y := of_mul _ _ _ _
@[simp] lemma coe_neg : (↑(-x) : loc α S) = -x := of_neg _ _ _
@[simp] lemma coe_pow : (↑(x ^ n) : loc α S) = x ^ n := of_pow _ _ _ _
end

@[simp] lemma of_zero (s : S) : of 0 s = 0 :=
quotient.sound ⟨s, s.2, by simp only [mul_zero, sub_zero, zero_mul]⟩

@[simp] lemma of_self {x : α} {hx : x ∈ S} :
  (of x ⟨x, hx⟩ : loc α S) = 1 :=
quotient.sound ⟨1, is_submonoid.one_mem S,
by simp only [subtype.coe_mk, is_submonoid.coe_one, mul_one, one_mul, sub_self]⟩

@[simp] lemma of_self' {s : S} :
  (of s s : loc α S) = 1 :=
by cases s; exact of_self

@[simp] lemma of_self'' {s : S} :
  (of s.1 s : loc α S) = 1 :=
of_self'

@[simp] lemma coe_mul_of (x y : α) (s : S) :
  ↑x * of y s = of (x * y) s :=
quotient.sound $ r_of_eq $ by rw one_mul

lemma of_eq_mul_of_one (r : α) (s : S) :
  of r s = r * of 1 s :=
by rw [coe_mul_of, mul_one]

@[simp] lemma of_mul_of (x y : α) (s t : S) :
  of x s * of y t = of (x * y) (s * t) := rfl

@[simp] lemma of_mul_cancel_left (r : α) (s : S) :
  of (↑s * r) s = r :=
by rw [of_eq_mul_of_one, mul_comm ↑s, coe_mul,
       mul_assoc, ← of_eq_mul_of_one, of_self', mul_one]

@[simp] lemma of_mul_cancel_right (r : α) (s : S) :
  of (r * s) s = r :=
by rw [mul_comm, of_mul_cancel_left]

@[elab_as_eliminator]
protected theorem induction_on {C : loc α S → Prop} (x : loc α S)
  (ih : ∀ r s, C (of r s : loc α S)) : C x :=
by rcases x with ⟨r, s⟩; exact ih r s

@[elab_with_expected_type]
protected def rec {β : Type v} [comm_ring β]
  (f : α → β) [hf : is_ring_hom f] (g : S → units β) (hg : ∀ s, (g s : β) = f s)
  (x : loc α S) : β :=
quotient.lift_on x (λ p, f p.1 * ((g p.2)⁻¹ : units β)) $ λ ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨t, hts, ht⟩,
show f r₁ * ↑(g s₁)⁻¹ = f r₂ * ↑(g s₂)⁻¹, from
calc  f r₁ * ↑(g s₁)⁻¹
    = (f r₁ * g s₂ + ((g s₁ * f r₂ - g s₂ * f r₁) * g ⟨t, hts⟩) * ↑(g ⟨t, hts⟩)⁻¹) * ↑(g s₁)⁻¹ * ↑(g s₂)⁻¹ :
  by simp only [hg, subtype.coe_mk, (is_ring_hom.map_mul f).symm, (is_ring_hom.map_sub f).symm, ht, is_ring_hom.map_zero f,
                zero_mul, add_zero]; rw [is_ring_hom.map_mul f, ← hg, mul_right_comm, mul_assoc (f r₁), ← units.coe_mul, mul_inv_self];
     rw [units.coe_one, mul_one]
... = f r₂ * ↑(g s₂)⁻¹ :
  by rw [mul_assoc, mul_assoc, ← units.coe_mul, mul_inv_self, units.coe_one, mul_one, mul_comm ↑(g s₂), add_sub_cancel'_right];
     rw [mul_comm ↑(g s₁), ← mul_assoc, mul_assoc (f r₂), ← units.coe_mul, mul_inv_self, units.coe_one, mul_one]

instance rec.is_ring_hom {β : Type v} [comm_ring β]
  (f : α → β) [hf : is_ring_hom f] (g : S → units β) (hg : ∀ s, (g s : β) = f s) :
  is_ring_hom (localization.rec f g hg) :=
{ map_one := have g 1 = 1, from units.ext (by rw hg; exact is_ring_hom.map_one f),
    show f 1 * ↑(g 1)⁻¹ = 1, by rw [this, one_inv, units.coe_one, mul_one, is_ring_hom.map_one f],
  map_mul := λ x y, localization.induction_on x $ λ r₁ s₁,
    localization.induction_on y $ λ r₂ s₂,
    have g (s₁ * s₂) = g s₁ * g s₂, from units.ext (by simp only [hg, units.coe_mul]; exact is_ring_hom.map_mul f),
    show _ * ↑(g (_ * _))⁻¹ = (_ * _) * (_ * _),
    by simp only [subtype.coe_mk, mul_one, one_mul, subtype.coe_eta, this, mul_inv_rev];
       rw [is_ring_hom.map_mul f, units.coe_mul, ← mul_assoc, ← mul_assoc];
       simp only [mul_right_comm],
  map_add := λ x y, localization.induction_on x $ λ r₁ s₁,
    localization.induction_on y $ λ r₂ s₂,
    have g (s₁ * s₂) = g s₁ * g s₂, from units.ext (by simp only [hg, units.coe_mul]; exact is_ring_hom.map_mul f),
    show _ * ↑(g (_ * _))⁻¹ = _ * _ + _ * _,
    by simp only [subtype.coe_mk, mul_one, one_mul, subtype.coe_eta, this, mul_inv_rev];
       simp only [is_ring_hom.map_mul f, is_ring_hom.map_add f, add_mul, (hg _).symm];
       simp only [mul_assoc, mul_comm, mul_left_comm, (units.coe_mul _ _).symm];
       rw [mul_inv_cancel_left, mul_left_comm, ← mul_assoc, mul_inv_cancel_right, add_comm] }

@[reducible] def away (x : α) := loc α (powers x)

@[simp] def away.inv_self (x : α) : away x :=
of 1 ⟨x, 1, pow_one x⟩

@[elab_with_expected_type]
protected noncomputable def away.rec {x : α} {β : Type v} [comm_ring β]
  (f : α → β) [hf : is_ring_hom f] (hfx : is_unit (f x)) : away x → β :=
localization.rec f (λ s, classical.some hfx ^ classical.some s.2) $ λ s,
by rw [units.coe_pow, ← classical.some_spec hfx, ← is_semiring_hom.map_pow f, classical.some_spec s.2]; refl

noncomputable def away_to_away_right (x y : α) : away x → away (x * y) :=
localization.away.rec coe $
is_unit_of_mul_one x (y * away.inv_self (x * y)) $
by rw [away.inv_self, coe_mul_of, coe_mul_of, mul_one, of_self]

instance away.rec.is_ring_hom {x : α} {β : Type v} [comm_ring β]
  (f : α → β) [hf : is_ring_hom f] (hfx : is_unit (f x)) :
  is_ring_hom (localization.away.rec f hfx) :=
rec.is_ring_hom _ _ _

instance away_to_away_right.is_ring_hom (x y : α) :
  is_ring_hom (away_to_away_right x y) :=
away.rec.is_ring_hom _ _

section at_prime

variables (P : ideal α) [hp : ideal.is_prime P]
include hp

instance prime.is_submonoid :
  is_submonoid (-P : set α) :=
{ one_mem := P.ne_top_iff_one.1 hp.1,
  mul_mem := λ x y hnx hny hxy, or.cases_on (hp.2 hxy) hnx hny }

@[reducible] def at_prime := loc α (-P)

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
{ one_mem := λ z hz, by rwa mul_one at hz,
  mul_mem := λ x₁ x₂ hx₁ hx₂ z hz,
    have z * x₁ * x₂ = 0, by rwa mul_assoc,
    hx₁ z $ hx₂ (z * x₁) this }

@[reducible] def fraction_ring := loc α (non_zero_divisors α)

section fraction_ring

variables {β : Type u} [integral_domain β] [decidable_eq β]

lemma ne_zero_of_mem_non_zero_divisors {x : β}
  (hm : x ∈ non_zero_divisors β) : x ≠ 0 | hz :=
zero_ne_one (hm 1 $ by rw [hz, one_mul]).symm

lemma eq_zero_of_ne_zero_of_mul_eq_zero {x y : β} :
  x ≠ 0 → y * x = 0 → y = 0 :=
λ hnx hxy, or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

lemma mem_non_zero_divisors_of_ne_zero {x : β} :
  x ≠ 0 → x ∈ non_zero_divisors β :=
λ hnx z, eq_zero_of_ne_zero_of_mul_eq_zero hnx

variable (β)

def inv_aux (x : β × (non_zero_divisors β)) : fraction_ring β :=
if h : x.1 = 0 then 0 else ⟦⟨x.2, x.1, mem_non_zero_divisors_of_ne_zero h⟩⟧

instance : has_inv (fraction_ring β) :=
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

instance : decidable_eq (fraction_ring β) :=
@quotient.decidable_eq (β × non_zero_divisors β) (localization.setoid β (non_zero_divisors β)) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, show decidable (∃ t ∈ non_zero_divisors β, (s₁ * r₂ - s₂ * r₁) * t = 0),
from decidable_of_iff (s₁ * r₂ - s₂ * r₁ = 0)
⟨λ H, ⟨1, λ y, (mul_one y).symm ▸ id, H.symm ▸ zero_mul _⟩,
λ ⟨t, ht1, ht2⟩, or.resolve_right (mul_eq_zero.1 ht2) $ λ ht,
  one_ne_zero (ht1 1 ((one_mul t).symm ▸ ht))⟩

instance fraction_ring.field : discrete_field (fraction_ring β) :=
by refine
{ inv            := has_inv.inv,
  zero_ne_one    := λ hzo,
    let ⟨t, hts, ht⟩ := quotient.exact hzo in
    zero_ne_one (by simpa using hts _ ht : 0 = 1),
  mul_inv_cancel := quotient.ind _,
  inv_mul_cancel := quotient.ind _,
  has_decidable_eq := localization.decidable_eq β,
  inv_zero := dif_pos rfl,
  .. localization.comm_ring };
{ intros x hnx,
  rcases x with ⟨x, z, hz⟩,
  have : x ≠ 0,
    from assume hx, hnx (quotient.sound $ r_of_eq $ by simp [hx]),
  simp only [has_inv.inv, inv_aux, quotient.lift_beta, dif_neg this],
  exact (quotient.sound $ r_of_eq $ by simp [mul_comm]) }

@[simp] lemma of_eq_div {r s} : (of r s : fraction_ring β) = (r / s : fraction_ring β) :=
show _ = _ * dite (s.1 = 0) _ _, by rw [dif_neg (ne_zero_of_mem_non_zero_divisors s.2)];
exact localization.of_eq_mul_of_one _ _

end fraction_ring

section ideals

theorem map_comap (J : ideal (loc α S)) :
  ideal.map coe (ideal.comap (coe : α → loc α S) J) = J :=
le_antisymm (ideal.map_le_iff_le_comap.2 (le_refl _)) $ λ x,
localization.induction_on x $ λ r s hJ, (submodule.mem_coe _).2 $
mul_one r ▸ coe_mul_of r 1 s ▸ (ideal.mul_mem_right _ $ ideal.mem_map_of_mem $
have _ := @ideal.mul_mem_left (loc α S) _ _ s _ hJ,
by rwa [coe_coe, coe_mul_of, of_mul_cancel_left] at this)

def le_order_embedding :
  ((≤) : ideal (loc α S) → ideal (loc α S) → Prop) ≼o
  ((≤) : ideal α → ideal α → Prop) :=
{ to_fun := λ J, ideal.comap coe J,
  inj := function.injective_of_left_inverse (map_comap α),
  ord := λ J₁ J₂, ⟨ideal.comap_mono, λ hJ,
    map_comap α J₁ ▸ map_comap α J₂ ▸ ideal.map_mono hJ⟩ }

end ideals

end localization
