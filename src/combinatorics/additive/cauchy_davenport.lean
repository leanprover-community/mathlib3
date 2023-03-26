/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.additive.mathlib
import data.nat.prime
import data.zmod.basic

/-!
# The Cauchy-Davenport theorem

This file proves the Cauchy-Davenport theorem as a corollary to a more general result.

## Main declarations

* `subgroup.nontrivial_size`: The minimum size of a finite nontrivial subgroup of a given group. If
  the group is trivial, it is `1` by convention.
* `finset.card_add_card_sub_one_le_min_nontrivial_size_card_mul`: A generalisation of Károlyi's
  theorem.
* `zmod.card_add_card_sub_one_le_min_card_add_zmod`: The Cauchy-Davenport theorem.

## References

* Matt DeVos, *On a generalization of the Cauchy-Davenport theorem*

## Tags

additive combinatorics, number theory, sumset, karolyi, cauchy-davenport
-/

namespace subgroup
variables (α : Type*) [group α]

open_locale classical

/-- The minimum size of a nontrivial subgroup of a given group. Returns `1` if there is no
nontrivial finite subgroup. -/
@[to_additive "The minimum size of a nontrivial subgroup of a given additive group. Returns `1` if
there is no nontrivial finite subgroup."]
noncomputable def nontrivial_size : ℕ :=
if ∃ s : subgroup α, s ≠ ⊥ ∧ (s : set α).finite then
  ⨅ s : {s : subgroup α // s ≠ ⊥ ∧ (s : set α).finite}, nat.card s.1 else 1

@[to_additive] lemma nontrivial_size_of_subsingleton [subsingleton α] : nontrivial_size α = 1 :=
by { convert if_neg _, rintro ⟨s, hs, hs'⟩, exact hs (subsingleton.elim _ _) }

variables {α} {s : subgroup α} {n : ℕ}

@[to_additive] lemma nontrivial_size_aux [finite α] [nontrivial α] :
  ∃ s : subgroup α, s ≠ ⊥ ∧ (s : set α).finite :=
⟨⊤, top_ne_bot, set.to_finite _⟩

@[to_additive] instance nontrivial_size_nonempty_aux [finite α] [nontrivial α] :
  nonempty {s : subgroup α // s ≠ ⊥ ∧ (s : set α).finite} :=
⟨⟨⊤, top_ne_bot, set.to_finite _⟩⟩

@[to_additive]
lemma nontrivial_size_le_nat_card (hs : s ≠ ⊥) (hs' : (s : set α).finite) :
  nontrivial_size α ≤ nat.card s :=
(if_pos (⟨s, hs, hs'⟩ : ∃ s : subgroup α, s ≠ ⊥ ∧ (s : set α).finite)).trans_le $
  cinfi_le' _ (⟨s, hs, hs'⟩ : {s : subgroup α // s ≠ ⊥ ∧ (s : set α).finite})

@[to_additive]
lemma le_nontrivial_size (hα : ∃ s : subgroup α, s ≠ ⊥ ∧ (s : set α).finite)
  (hn : ∀ (s ≠ (⊥ : subgroup α)) (hs' : (s : set α).finite), n ≤ nat.card s) :
  n ≤ nontrivial_size α :=
(if_pos hα).symm.trans_ge $ begin
  obtain ⟨s, hs, hs'⟩ := hα,
  haveI : nonempty {s : subgroup α // s ≠ ⊥ ∧ (s : set α).finite} := ⟨⟨s, hs, hs'⟩⟩,
  exact le_cinfi (λ s, hn _ s.2.1 s.2.2),
end

end subgroup

namespace add_subgroup

open nat set

@[simp] lemma nontrivial_size_zmod {n : ℕ} (hn : n ≠ 0) : nontrivial_size (zmod n) = n.min_fac :=
begin
  obtain rfl | hn₁ := eq_or_ne n 1,
  { exact nontrivial_size_of_subsingleton _ },
  haveI : fact (1 < n) := by obtain _ | _ | n := n; contradiction <|> exact ⟨n.one_lt_succ_succ⟩,
  classical,
  have : (↑(n / n.min_fac) : zmod n) ≠ 0,
  { rw [ne.def, ring_char.spec, ring_char.eq (zmod n) n],
    exact not_dvd_of_pos_of_lt (nat.div_pos (min_fac_le hn.bot_lt) n.min_fac_pos)
      (div_lt_self hn.bot_lt (min_fac_prime hn₁).one_lt) },
  refine ((nontrivial_size_le_nat_card (zmultiples_eq_bot.not.2 this) $ to_finite _).trans
    _).antisymm (le_nontrivial_size nontrivial_size_aux $ λ s hs _, _),
  { rw [card_eq_fintype_card, ←add_order_eq_card_zmultiples, zmod.add_order_of_coe _ hn,
      gcd_eq_right (div_dvd_of_dvd n.min_fac_dvd), nat.div_div_self n.min_fac_dvd hn] },
  { rw card_eq_fintype_card,
   haveI : nontrivial s := s.bot_or_nontrivial.resolve_left hs,
    exact min_fac_le_of_dvd fintype.one_lt_card
      ((card_add_subgroup_dvd_card _).trans (zmod.card _).dvd) }
end

@[simp] lemma nontrivial_size_zmod_prime {p : ℕ} [fact p.prime] : nontrivial_size (zmod p) = p :=
by rw [nontrivial_size_zmod (ne_zero.out : p ≠ 0), (fact.out p.prime).min_fac_eq]

end add_subgroup

open mul_opposite order_dual subgroup
open_locale pointwise

namespace finset
variables {α : Type*} [group α] [decidable_eq α] {x y : finset α × finset α} {s t : finset α}

/-- The relation we induct along in the proof Károlyi's theorem. `(s₁, t₁) < (s₂, t₂)` iff
* `|s₁ * t₁| < |s₂ * t₂|`
* or `|s₁ * t₁| = |s₂ * t₂|` and `|s₂| + |t₂| < |s₁| + |t₁|`
* or `|s₁ * t₁| = |s₂ * t₂|` and `|s₁| + |t₁| = |s₂| + |t₂|` and `|s₁| < |s₂|`. -/
@[to_additive "The relation we induct along in the proof Károlyi's theorem. `(s₁, t₁) < (s₂, t₂)`
iff
* `|s₁ + t₁| < |s₂ + t₂|`
* or `|s₁ + t₁| = |s₂ + t₂|` and `|s₂| + |t₂| < |s₁| + |t₁|`
* or `|s₁ + t₁| = |s₂ + t₂|` and `|s₁| + |t₁| = |s₂| + |t₂|` and `|s₁| < |s₂|`."]
private def devos_mul_rel : finset α × finset α → finset α × finset α → Prop :=
prod.lex (<) (prod.lex (>) (<)) on λ x, ((x.1 * x.2).card, x.1.card + x.2.card, x.1.card)

@[to_additive]
lemma devos_mul_rel_iff :
  devos_mul_rel x y ↔ (x.1 * x.2).card < (y.1 * y.2).card ∨
    (x.1 * x.2).card = (y.1 * y.2).card ∧ y.1.card + y.2.card < x.1.card + x.2.card ∨
      (x.1 * x.2).card = (y.1 * y.2).card ∧ x.1.card + x.2.card = y.1.card + y.2.card ∧
        x.1.card < y.1.card :=
by simp [devos_mul_rel, prod.lex_iff, and_or_distrib_left]

@[to_additive] lemma devos_mul_rel_of_le (hmul : (x.1 * x.2).card ≤ (y.1 * y.2).card)
  (hadd : y.1.card + y.2.card < x.1.card + x.2.card) :
  devos_mul_rel x y :=
devos_mul_rel_iff.2 $ hmul.lt_or_eq.imp_right $ λ h, or.inl ⟨h, hadd⟩

@[to_additive] lemma devos_mul_rel_of_le_of_le (hmul : (x.1 * x.2).card ≤ (y.1 * y.2).card)
  (hadd : y.1.card + y.2.card ≤ x.1.card + x.2.card) (hone : x.1.card < y.1.card) :
  devos_mul_rel x y :=
devos_mul_rel_iff.2 $ hmul.lt_or_eq.imp_right $ λ h, hadd.gt_or_eq.imp (and.intro h) $
  λ h', ⟨h, h', hone⟩

@[to_additive]
lemma well_founded_on_devos_mul_rel :
  {x : finset α × finset α | x.1.nonempty ∧ x.2.nonempty}.well_founded_on
    (devos_mul_rel : finset α × finset α → finset α × finset α → Prop) :=
begin
  refine is_well_founded.wf.on_fun.well_founded_on.prod_lex (λ n, set.well_founded_on.prod_lex _ $
    λ n, is_well_founded.wf.on_fun.well_founded_on),
  exact is_well_founded.wf.on_fun.well_founded_on.mono' (λ x hx y hy, tsub_lt_tsub_left_of_le $
    add_le_add ((card_le_card_mul_right _ hx.1.2).trans_eq hx.2) $
      (card_le_card_mul_left _ hx.1.1).trans_eq hx.2),
end

@[to_additive card_add_card_sub_one_le_min_nontrivial_size_card_add]
lemma card_add_card_sub_one_le_min_nontrivial_size_card_mul (hs : s.nonempty) (ht : t.nonempty) :
  min (nontrivial_size α) (s.card + t.card - 1) ≤ (s * t).card :=
begin
  set x := (s, t) with hx,
  clear_value x,
  simp only [prod.ext_iff] at hx,
  obtain ⟨rfl, rfl⟩ := hx,
  refine well_founded_on_devos_mul_rel.induction ⟨hs, ht⟩ _,
  clear_dependent x,
  rintro ⟨s, t⟩ ⟨hs, ht⟩ ih,
  simp only [min_le_iff, tsub_le_iff_right, prod.forall, set.mem_set_of_eq, and_imp] at *,
  -- If `t.card < s.card`, we're done by the induction hypothesis on `(t⁻¹, s⁻¹)`
  obtain hts | hst := lt_or_le t.card s.card,
  { simpa [←mul_inv_rev, add_comm] using ih _ _ ht.inv hs.inv
      (devos_mul_rel_iff.2 $ or.inr $ or.inr $ by simpa [←mul_inv_rev, add_comm]) },
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial,
  { simp [add_comm] },
  obtain ⟨g, hg, hgs⟩ : ∃ g : α, g ≠ 1 ∧ (s ∩ op g • s).nonempty :=
    ⟨b⁻¹ * a, inv_mul_eq_one.not.2 hab.symm, _,
      mem_inter.2 ⟨ha, mem_smul_finset.2 ⟨_, hb, by simp⟩⟩⟩,
  obtain hsg | hsg := eq_or_ne (op g • s) s,
  { have hS : (zpowers g : set α) ⊆ a⁻¹ • s,
    { refine coe_zpowers_subset ⟨_, ha, inv_mul_self _⟩ (λ c hc, _) (λ c hc, _),
      { rw [←hsg, coe_smul_finset, smul_comm],
       exact set.smul_mem_smul_set hc },
      { rwa [←op_smul_eq_mul, op_inv, ←set.mem_smul_set_iff_inv_smul_mem, smul_comm,
          ←coe_smul_finset, hsg] } },
    exact or.inl ((nontrivial_size_le_nat_card (zpowers_ne_bot.2 hg) $
      s.finite_to_set.smul_set.subset hS).trans $
      ((nat.card_mono s.finite_to_set.smul_set hS).trans_eq $ by simp).trans $
      card_le_card_mul_right _ ht) },
  replace hsg : (s ∩ op g • s).card < s.card := card_lt_card ⟨inter_subset_left _ _, λ h, hsg $
    eq_of_superset_of_card_ge (h.trans $ inter_subset_right _ _) (card_smul_finset _ _).le⟩,
  have aux0 : op g • s * g⁻¹ • t = s * t,
  { rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul] },
  have aux1 : (s ∩ op g • s) * (t ∪ g⁻¹ • t) ⊆ s * t,
  { exact inter_mul_union_subset_union.trans (union_subset subset.rfl aux0.subset') },
  have aux2 : (s ∪ op g • s) * (t ∩ g⁻¹ • t) ⊆ s * t,
  { refine union_mul_inter_subset_union.trans (union_subset subset.rfl aux0.subset') },
  replace aux1 := card_le_of_subset aux1,
  replace aux2 := card_le_of_subset aux2,
  obtain hgt | hgt := disjoint_or_nonempty_inter t (g⁻¹ • t),
  { rw ←card_smul_finset g⁻¹ t,
    refine or.inr ((add_le_add_right hst _).trans _),
    rw ←card_union_eq hgt,
    exact (card_le_card_mul_left _ hgs).trans (le_add_of_le_left aux1) },
  obtain hstg | hstg : s.card + t.card ≤ (s ∩ op g • s).card + (t ∪ g⁻¹ • t).card
    ∨ s.card + t.card < (s ∪ op g • s).card + (t ∩ g⁻¹ • t).card := le_or_lt_of_add_le_add _,
  { exact (ih _ _ hgs (hgt.mono inter_subset_union) $ devos_mul_rel_of_le_of_le aux1 hstg hsg).imp
      aux1.trans' (λ h, hstg.trans $ h.trans $ add_le_add_right aux1 _) },
  { exact (ih _ _ (hgs.mono inter_subset_union) hgt $ devos_mul_rel_of_le aux2 hstg).imp
      aux2.trans' (λ h, hstg.le.trans $ h.trans $ add_le_add_right aux2 _) },
  { rw [add_add_add_comm, add_add_add_comm (s ∩ op g • s).card, card_inter_add_card_union,
    card_union_add_card_inter, card_smul_finset, card_smul_finset] }
end

end finset

open finset

namespace zmod
variables {p : ℕ} [fact p.prime] {s t : finset (zmod p)}

/-- The **Cauchy-Davenport theorem**. -/
lemma card_add_card_sub_one_le_min_card_add_zmod (hs : s.nonempty) (ht : t.nonempty) :
  min p (s.card + t.card - 1) ≤ (s + t).card :=
by simpa using card_add_card_sub_one_le_min_nontrivial_size_card_add hs ht

end zmod
