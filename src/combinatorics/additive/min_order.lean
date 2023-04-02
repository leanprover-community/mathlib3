/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.additive.mathlib
import data.nat.prime
import data.zmod.basic

/-! ### Minimum size of a nontrivial subgroup -/

variables {α : Type*}

namespace monoid
section monoid
variables (α) [monoid α]

/-- The minimum size of a nontrivial subgroup of a given group. Returns `1` if there is no
nontrivial finite subgroup. -/
@[to_additive "The minimum size of a nontrivial subgroup of a given additive group. Returns `1` if
there is no nontrivial finite subgroup."]
noncomputable def min_order : ℕ∞ := ⨅ (a : α) (ha : a ≠ 1) (ha' : is_of_fin_order a), order_of a

variables {α} {a : α}

@[simp, to_additive] lemma min_order_eq_top : min_order α = ⊤ ↔ is_torsion_free α :=
by simpa [min_order]

@[simp, to_additive] protected lemma is_torsion_free.min_order :
  is_torsion_free α → min_order α = ⊤ :=
min_order_eq_top.2

@[simp, to_additive] lemma le_min_order {n : ℕ∞} :
  n ≤ min_order α ↔ ∀ ⦃a : α⦄, a ≠ 1 → is_of_fin_order a → n ≤ order_of a :=
by simp [min_order]

@[to_additive]
lemma min_order_le_order_of (ha : a ≠ 1) (ha' : is_of_fin_order a) : min_order α ≤ order_of a :=
le_min_order.1 le_rfl ha ha'

end monoid

open subgroup

variables [group α] {s : subgroup α} {n : ℕ}

@[to_additive] lemma le_min_order' {n : ℕ∞} :
  n ≤ min_order α ↔ ∀ ⦃s : subgroup α⦄, s ≠ ⊥ → (s : set α).finite → n ≤ nat.card s :=
begin
  rw le_min_order,
  refine ⟨λ h s hs hs', _, λ h a ha ha', _⟩,
  { obtain ⟨a, has, ha⟩ := s.bot_or_exists_ne_one.resolve_left hs,
    exact (h ha $ finite_zpowers.1 $ hs'.subset $ zpowers_le.2 has).trans
      (with_top.coe_le_coe.2 $ order_of_le_card hs' has) },
  { simpa using h (zpowers_ne_bot.2 ha) ha'.finite_zpowers' }
end

@[to_additive]
lemma min_order_le_nat_card (hs : s ≠ ⊥) (hs' : (s : set α).finite) : min_order α ≤ nat.card s :=
le_min_order'.1 le_rfl hs hs'

end monoid

open add_monoid add_subgroup nat set

namespace zmod

@[simp] protected lemma min_order {n : ℕ} (hn : n ≠ 0) (hn₁ : n ≠ 1) :
  min_order (zmod n) = n.min_fac :=
begin
  haveI : fact (1 < n) := by obtain _ | _ | n := n; contradiction <|> exact ⟨n.one_lt_succ_succ⟩,
  classical,
  have : (↑(n / n.min_fac) : zmod n) ≠ 0,
  { rw [ne.def, ring_char.spec, ring_char.eq (zmod n) n],
    exact not_dvd_of_pos_of_lt (nat.div_pos (min_fac_le hn.bot_lt) n.min_fac_pos)
      (div_lt_self hn.bot_lt (min_fac_prime hn₁).one_lt) },
  refine ((min_order_le_nat_card (zmultiples_eq_bot.not.2 this) $ to_finite _).trans
    _).antisymm (le_min_order'.2 $ λ s hs _, _),
  { rw [card_eq_fintype_card, ←add_order_eq_card_zmultiples, zmod.add_order_of_coe _ hn,
      gcd_eq_right (div_dvd_of_dvd n.min_fac_dvd), nat.div_div_self n.min_fac_dvd hn],
    exact le_rfl },
  { rw card_eq_fintype_card,
    haveI : nontrivial s := s.bot_or_nontrivial.resolve_left hs,
    exact with_top.coe_le_coe.2 (min_fac_le_of_dvd fintype.one_lt_card $
      (card_add_subgroup_dvd_card _).trans (zmod.card _).dvd) }
end

@[simp] lemma min_order_of_prime {p : ℕ} [fact p.prime] : min_order (zmod p) = p :=
by rw [zmod.min_order (ne_zero.out : p ≠ 0) (fact.out p.prime).ne_one,
  (fact.out p.prime).min_fac_eq]

end zmod
