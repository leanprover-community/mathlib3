/-
Copyright (c) 2022 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Kevin Buzzard
-/
import tactic.interval_cases
import group_theory.index
import group_theory.p_group
import group_theory.quotient_group
import group_theory.coset
import group_theory.specific_groups.cyclic
import group_theory.abelianization
import data.finite.basic
import data.finite.card
import data.real.basic
import group_theory.subgroup.basic
import data.zmod.basic

/-!
# Groups of order p^2

This file contains a proof that if `G` is a group of order `p` squared (where `p` is a prime
number), `G` is abelian. It also contains code to get a `comm_group` instance when a group is
commutative; this code was provided by Eric Wieser in response to a PR I (Sidharth Hariharan) had
made earlier to add a lemma that fixed an issue I was facing.

## Main Result:

- `order_psq_abelian` : proof that groups of order p^2 are abelian
-/

open fintype
open is_p_group
open group

/-- A group that is commutative can be turned into a comm_group
(See https://github.com/leanprover-community/mathlib/pull/14960#issuecomment-1178880188)
-/
instance {G} : can_lift (group G) (comm_group G) :=
{ coe := @comm_group.to_group G,
  cond := λ g, by exactI (∀ x y : G, commute x y),
  prf := λ g hg, ⟨{mul_comm := hg, ..g}, by cases g; refl⟩ }

/-- A group whose center is ⊤ must be abelian. -/
lemma group.of_comm_center_eq_top {H : Type*} [group H] (h : (subgroup.center H = ⊤)) :
  (∀ a b : H, a * b = b * a) :=
begin
  rw subgroup.eq_top_iff' at h,
  intros x y,
  rw (h x),
end

/-- Basic Setup: `p` is a prime and `G` is a group of order `p` squared. -/

variables (p : ℕ) [fact (nat.prime p)]
variables (G : Type*) [fintype G] [group G]

/-- A group of order p^2 is one whose cardinality is the square of a prime number. -/
def order_psq : Prop := card G = p^2

namespace order_psq

section G_has_order_psq

variables (hG : order_psq p G)
include hG

/-- G is a p-group. -/
lemma p_group : is_p_group p G := of_card hG

/-- G has a nontrivial center Z(G). -/
lemma psq_center_nontrivial [nontrivial G] : nontrivial (subgroup.center G) :=
center_nontrivial (p_group p G hG)

open_locale classical

/-- G ⧸ Z(G) is a fintype. -/
@[instance] def quotient_with_center_is_fintype : finite (G ⧸ subgroup.center G) :=
infer_instance

/-- |G ⧸ Z(G)| is not prime. -/
lemma center_index_not_prime : ¬ nat.prime (fintype.card (G ⧸ subgroup.center G)) :=
begin
  intro h1,
  haveI : fact(nat.prime (card (G ⧸ subgroup.center G))) := ⟨h1⟩,
  haveI := is_cyclic_of_prime_card (rfl : card (G ⧸ subgroup.center G) = _),
  have h2 := commutative_of_cyclic_center_quotient (quotient_group.mk' (subgroup.center G))
    (by simp),
  unfreezingI { lift ‹group G› to comm_group G using h2 },
  have h3 : subgroup.center G = ⊤, exact comm_group.center_eq_top,
  have h4 : card (G ⧸ subgroup.center G) = 1,
  { simp_rw [h3, ← nat.card_eq_fintype_card],
    exact subgroup.index_top, },
  rw h4 at h1,
  exact nat.not_prime_one h1,
end

/-- G is abelian. -/
theorem order_psq_abelian [nontrivial G] : (∀ x1 x2 : G, x1 * x2 = x2 * x1) :=
begin
  -- We show it suffices to show that Z(G) = ⊤.
  apply group.of_comm_center_eq_top,
  have h1 : (card (subgroup.center G) ∣ card (G)), exact (subgroup.center G).card_subgroup_dvd_card,
  unfold order_psq at hG,
  rw [hG, nat.dvd_prime_pow] at h1,
  -- We know it suffices to show that |Z(G)| = |G| = p^2.
  -- We can thus use Lagrange's Theorem and condition on |Z(G)|.
  rcases h1 with ⟨k, hk1, hk2⟩,
  swap,
  apply fact.out,
  interval_cases k,
  -- We look at the case |Z(G)| = 1
  { simp at hk2,
    exfalso,
    have h31 : nontrivial (subgroup.center G), exact center_nontrivial (p_group p G hG),
    rw subgroup.nontrivial_iff_exists_ne_one at h31,
    rcases h31 with ⟨x, hx, hxx⟩,
    have h32 : subgroup.center G = ⊥, rw [← subgroup.card_le_one_iff_eq_bot, hk2],
    have hxx' : x = 1,
    { rw subgroup.eq_bot_iff_forall at h32,
      exact h32 x hx, },
    contradiction, },
  -- We look at the case |Z(G)| = p
  { exfalso,
    have h41 : p * (subgroup.center G).index = p^2,
    { simp at hk2,
      simp_rw ← nat.card_eq_fintype_card at hk2,
      simp_rw ← nat.card_eq_fintype_card at hG,
      rw [← hG, ← hk2],
      exact subgroup.card_mul_index (subgroup.center G), },
    have h42 : (subgroup.center G).index = p,
    { have hcalc : p * (subgroup.center G).index = p * p,
      { simp_rw h41,
        exact sq p, },
      simp at hcalc,
      have hcalc2 : ¬ (p = 0),
      { intro hcp,
        have hcp2 := _inst_1.out,
        rw hcp at hcp2,
        have hcp3 := nat.not_prime_zero,
        contradiction, },
      cases hcalc with hcl hcr,
      { exact hcl, },
      { exfalso,
        contradiction, }, },
    have h43 : nat.prime (card (G ⧸ subgroup.center G)),
    { have hcalc : nat.card (G ⧸ subgroup.center G) = p, exact h42,
      rw nat.card_eq_fintype_card at hcalc,
      rw hcalc,
      exact _inst_1.out, },
    have h44 : ¬ nat.prime (fintype.card (G ⧸ subgroup.center G)),
    { apply center_index_not_prime p G,
      exact hG, },
    contradiction, },
  -- We look at the case |Z(G)| = p^2
  { apply subgroup.eq_top_of_card_eq,
    rw hG,
    exact hk2, },
end

end G_has_order_psq

end order_psq
