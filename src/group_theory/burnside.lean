/-
Copyright (c) 2019 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Prove Burnside lemma (not due to Burnside): the number of orbits of a group action equals the average number of points fixed by an element of the group.
-/

import .group_action ..order.fixed_points

/- TODO: What file is a good home for this? -/
instance lattice.fixed_points_fintype
  {α : Type*} [fintype α] [h : decidable_eq α] (f : α → α) :
  fintype (lattice.fixed_points f) :=
@subtype.fintype _ _ (lattice.fixed_points f) (assume x, h (f x) x)

namespace mul_action

universes u v

variables {G : Type u} [group G] {α : Type v} [mul_action G α]

@[simp]
lemma smul_inv_left {g : G} {x : α} : g⁻¹ • g • x = x :=
by rw [← mul_smul, mul_left_inv, one_smul]

@[simp]
lemma smul_inv_right {g : G} {x : α} : g • g⁻¹ • x = x :=
by rw [← mul_smul, mul_right_inv, one_smul]

lemma stabilizer_orbit_iff {x : α} {g g' : G} :
  g' ∈ stabilizer G x ↔ (g * g' * g⁻¹ ∈ stabilizer G (g • x)) :=
show _ • _ = _ ↔ _ • _ = _,
begin
  simp only [mul_smul,smul_inv_left],
  symmetry,
  exact (bijective g).1.eq_iff
end

lemma stabilizer_orbit_inv_iff {x : α} {g g' : G} :
  g' ∈ stabilizer G (g • x) ↔ (g⁻¹ * g' * g ∈ stabilizer G x) :=
begin
  symmetry,
  convert stabilizer_orbit_iff; try { apply_instance },
  rw [mul_assoc,mul_inv_cancel_right,mul_inv_cancel_left]
end

def equiv.stabilizer (g : G) (x : α) : stabilizer G x ≃ stabilizer G (g • x) :=
begin
  use assume g', ⟨g * g'.1 * g⁻¹, stabilizer_orbit_iff.1 g'.2⟩,         -- to_fun
  use assume g', ⟨g⁻¹ * g'.1 * g, stabilizer_orbit_inv_iff.1 g'.2⟩,     -- inv_fun
  all_goals { assume g',
              apply subtype.eq',
              simp,
              rw mul_assoc },
    { rw inv_mul_cancel_right,
      exact inv_mul_cancel_left _ _ },
    { rw mul_inv_cancel_right,
      exact mul_inv_cancel_left _ _ }
end

variables G α
def orbits : Type v := quotient $ orbit_rel G α

local attribute [instance] mul_action.orbit_rel
local attribute [reducible] lattice.fixed_points

/-- A trivial equivalence used in the proof of Burnside Lemma -/
def burnside_aux₁ :
  (Σ g : G, lattice.fixed_points ((•) g : α → α)) ≃
    (Σ (o : orbits G α) (x : {x // ⟦x⟧ = o}), stabilizer G x.val) :=
{ to_fun  := λ y, ⟨⟦y.snd.val⟧, ⟨⟨y.snd.val, rfl⟩, ⟨y.fst, y.snd.property⟩⟩⟩,
  inv_fun := λ y, ⟨y.snd.snd.val, ⟨y.snd.fst.val, y.snd.snd.property⟩⟩,
  left_inv := λ ⟨g, ⟨x, h⟩⟩, rfl,
  right_inv := λ ⟨o, ⟨⟨x, hx⟩, ⟨g, h⟩⟩⟩, by subst o
}

noncomputable theory
open classical

variables {G α}

/-- Choose an element of the group that sends `o.out` to a specific point of the orbit. -/
def orbit_choice {o : orbits G α} (x : {x // ⟦x⟧ = o}) : G :=
  some (quotient.exact $ x.2.trans o.out_eq.symm)

def orbit_choice_spec {o : orbits G α} (x : {x // ⟦x⟧ = o}) :
  orbit_choice x • o.out = x.val :=
some_spec (quotient.exact $ x.2.trans o.out_eq.symm)

/-- Disjoint union of stabilizers of all points of a given orbit
    has the same cardinality as the group. -/
def sigma_stabilizer_equiv_group (o : orbits G α) :
  (Σ x : {x // ⟦x⟧ = o}, stabilizer G x.val) ≃ G :=
begin
  have h₁ : (Σ x : {x // ⟦x⟧ = o}, stabilizer G x.val) ≃
    ({x // ⟦x⟧ = o} × (stabilizer G o.out)),
    by { apply equiv.sigma_equiv_prod_of_equiv,
         assume x,
         rw [← (orbit_choice_spec x)],
         symmetry,
         apply equiv.stabilizer },

  have h₂ : ({x // ⟦x⟧ = o} × (stabilizer G o.out)) ≃ ((orbit G o.out) × (stabilizer G o.out)),
    by { apply equiv.cast,
         congr,
         funext,
         apply propext,
         rw [← quotient.out_eq o,quotient.eq,quotient.out_eq],
         refl },

  have h₃ : ((orbit G o.out) × (stabilizer G o.out)) ≃ G,
    by { generalize: o.out = y,
         symmetry,
         apply (@mul_action.is_subgroup G _ _ _ y).group_equiv_quotient_times_subgroup.trans,
         apply equiv.prod_congr,
           { exact (orbit_equiv_quotient_stabilizer _ _).symm },
           { refl } },

  calc _ ≃ ({x // ⟦x⟧ = o} × (stabilizer G o.out))  : h₁
    ...  ≃ ((orbit G o.out) × (stabilizer G o.out)) : h₂
    ...  ≃ G                                        : h₃
end

/-- Equivalence behind Burnside Lemma.

    Disjoint union of fixed points of all elements of the group is equivalent
    to the product of the group and the orbits space. -/
def burnside_equiv :
  (Σ g : G, lattice.fixed_points ((•) g : α → α)) ≃ (G × orbits G α) :=
calc _ ≃ (Σ (o : orbits G α) (x : {x // ⟦x⟧ = o}), stabilizer G x.val) : burnside_aux₁ G α
   ... ≃ (Σ (o : orbits G α), G) : by { apply equiv.sigma_congr_right, exact sigma_stabilizer_equiv_group }
   ... ≃ (orbits G α × G) : equiv.sigma_equiv_prod _ _
   ... ≃ (G × orbits G α) : equiv.prod_comm _ _

open fintype finset

variables [fintype G] [decidable_eq G] [fintype α] [decidable_eq α]

instance orbits_fintype : fintype $ orbits G α := quotient.fintype _

/-- Burnside's lemma: number of orbits of a group action equals the average number of fixed points of a group element.

    For the case of infinite sets, see `burnside_equiv`. -/
lemma burnside :
  card G * card (orbits G α) =
    sum univ (λ g : G, card $ lattice.fixed_points ((•) g : α → α)) :=
begin
  symmetry,
  rw [← card_prod,← fintype.card_sigma],
  exact card_congr burnside_equiv
end
end mul_action
