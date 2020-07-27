import data.rel
import analysis.convex.basic

noncomputable theory
open_locale classical big_operators
open finset

variables {α : Type*} {β : Type*}

section falling_product

variables (s : ℕ)

def falling_product (x : ℝ) : ℝ :=
if ((s : ℝ) < x + 1) then (∏ i in (finset.Ico 0 s), (x - i)) / s.fact else 0

variables {s}

lemma falling_product_eq_choose (x : ℕ) :
  falling_product s ↑x = ↑(x.choose s) :=
begin
  unfold falling_product, norm_cast, split_ifs,
  { apply div_eq_of_eq_mul, {norm_cast, apply nat.fact_ne_zero s},
    rw nat.choose_eq_fact_div_fact, sorry, linarith, },
  { norm_cast, rw nat.choose_eq_zero_of_lt, linarith, }
end

lemma falling_product_eq_zero_of_le {x : ℝ} {spos : s ≠ 0} (hle : x ≤ (s : ℝ) - 1) :
  falling_product s x = 0 :=
begin
  rw le_iff_lt_or_eq at hle, cases hle,
  { unfold falling_product, rw if_neg, linarith, },
  cases s, tauto,
  have h : x = ↑s, rw hle, rw nat.succ_eq_add_one, simp,
  rw h, rw falling_product_eq_choose, simp,
end

lemma falling_product_convex_of_le : convex_on {x : ℝ | ↑s ≤ x + 1} (falling_product s) :=
begin
  sorry,
end

lemma falling_product_convex {spos : s ≠ 0} : convex_on set.univ (falling_product s) :=
begin
  unfold convex_on, split, exact convex_univ,
  sorry,
end

end falling_product

variable (r : rel α β)

namespace rel

def is_complete_subrel (A : set α) (B : set β) : Prop := ∀ a b, a ∈ A ∧ b ∈ B → r a b

def complete_subrel_cards (s t : ℕ) : Type* :=
{ AB : (finset α) × (finset β) // AB.1.card = s ∧ AB.2.card = t ∧ r.is_complete_subrel ↑AB.1 ↑AB.2}

def omits_complete_subrel (s t : ℕ) : Prop :=
  ∀ (A : finset α) (B : finset β), A.card = s ∧ B.card = t → ¬ r.is_complete_subrel ↑A ↑B

lemma omits_complete_subrel_iff_complete_subrel_card_empty {s t : ℕ} :
  r.omits_complete_subrel s t ↔ (r.complete_subrel_cards s t → false) :=
begin
  unfold omits_complete_subrel,
  split; intro h, {exact λ AB, h AB.val.1 AB.val.2 ⟨ AB.prop.1, AB.prop.2.1⟩ AB.prop.2.2},
  intros A B hab con, apply h, use (A,B), tauto,
end

variables [fintype α] [fintype β] (s : ℕ)

def left_degree (a : α) : ℕ := (univ.filter (r a)).card

def right_degree (b : β) : ℕ := (univ.filter (λ a, r a b)).card

def edge_finset : finset (α × β) := univ.filter (λ x, r x.fst x.snd)

lemma card_edges_eq_sum_left_degree :
  r.edge_finset.card = ∑ a : α, r.left_degree a :=
begin
  sorry,
end

lemma card_edges_eq_sum_right_degree :
  r.edge_finset.card = ∑ b : β, r.right_degree b :=
begin
  sorry,
end

def is_star (s : ℕ) (A : finset α) (b : β) : Prop := A.card = s ∧ ∀ a, a ∈ A → r a b

def stars : finset ((finset α) × β) := univ.filter (function.uncurry (r.is_star s))

variables {s} {t : ℕ}

lemma stars_eq_bind_over_powerset_len :
  r.stars s = (powerset_len s univ).bind (λ A, univ.filter (λ Ab, Ab.1 = A ∧ r.is_star s A Ab.2)) :=
begin
  rw [stars, function.uncurry], ext,
  simp only [true_and, mem_bind, exists_prop, mem_filter, mem_univ],
  split; intro h, {use a.fst, simp [mem_powerset_len, h, h.left, subset_univ]},
  cases h with A hA, rw hA.2.1, exact hA.2.2,
end

lemma card_stars_eq_sum_over_powerset_len :
  (r.stars s).card = ∑ A in powerset_len s (univ : finset α), (univ.filter (r.is_star s A)).card :=
begin
  rw [stars_eq_bind_over_powerset_len, card_bind],
  { apply sum_congr rfl, intros A hA,
    have h : (univ.filter (r.is_star s A)) =
      finset.image prod.snd (filter (λ (x : finset α × β), x.fst = A ∧ r.is_star s A x.snd) univ),
    { ext, simp, },
    rw [h, card_image_of_inj_on],
    simp only [true_and, and_imp, prod.forall, mem_filter, mem_univ, prod.mk.inj_iff],
    intros, rw a_1, tauto, },
  { simp only [disjoint_filter, and_imp, forall_prop_of_true, prod.forall, not_and, mem_univ, ne.def],
   intros, exfalso, apply a, rwa ← a_2, }
end

lemma stars_eq_bind_over_right :
  r.stars s = (univ).bind (λ b : β, univ.filter (λ Ab, Ab.snd = b ∧ r.is_star s Ab.fst b)) :=
by { rw [stars, function.uncurry], ext, simp }

lemma card_stars_eq_sum_over_right : (r.stars s).card = ∑ b : β, (r.right_degree b).choose s :=
begin
  rw stars_eq_bind_over_right, rw card_bind,
  { apply sum_congr rfl, intros b hb,
    unfold right_degree, rw ← card_powerset_len,
    have h : powerset_len s (filter (λ (a : α), r a b) univ) =
      finset.image prod.fst (filter (λ (x : finset α × β), x.snd = b ∧ r.is_star s x.fst b) univ),
    { ext, simp only [is_star, mem_powerset_len, subset_iff, true_and, exists_prop, mem_filter, exists_and_distrib_right, mem_univ,
 exists_eq_left, exists_eq_right, finset.mem_image, prod.exists], tauto, },
    rw [h, card_image_of_inj_on],
    simp only [true_and, and_imp, prod.forall, mem_filter, mem_univ, prod.mk.inj_iff],
    intros, rw a_1, tauto, },
  { simp only [disjoint_filter, and_imp, forall_prop_of_true, prod.forall, not_and, mem_univ, ne.def],
   intros, exfalso, apply a, rwa ← a_2, }
end

instance : fintype (r.complete_subrel_cards s t) := subtype.fintype _

variable (noKst : r.omits_complete_subrel s t)
include noKst

lemma upper_bound_stars :
  (r.stars s).card ≤ ((fintype.card α).choose s) * (t - 1) :=
begin
  rw card_stars_eq_sum_over_powerset_len, rw fintype.card, rw ← card_powerset_len,
  transitivity ∑ (A : finset α) in powerset_len s univ, (t - 1),
  { apply sum_le_sum, intros A hA, contrapose noKst,
    have h := exists_smaller_set (filter (r.is_star s A) univ) t _, cases h with B hB,
    { unfold omits_complete_subrel, push_neg, use [A, B],
      split, {rw mem_powerset_len at hA, cc},
      unfold is_complete_subrel, rw subset_iff at hB,
      intros a b hab, cases hab with ha hb, have hb' := hB.1 hb,
      rw [mem_filter, is_star] at hb', apply hb'.2.2, apply ha, },
    { rw not_le at noKst, apply nat.le_of_pred_lt noKst, } },
  { rw sum_const_nat, intros, refl, }
end

lemma lower_bound_stars {spos : s ≠ 0} {betapos : fintype.card β ≠ 0} :
  falling_product s ((fintype.card β : ℝ)⁻¹ * r.edge_finset.card)  ≤ (fintype.card β : ℝ)⁻¹  * (r.stars s).card :=
begin
  rw [card_edges_eq_sum_right_degree, sum_nat_cast, mul_sum,
    card_stars_eq_sum_over_right, sum_nat_cast], simp_rw ← falling_product_eq_choose, rw mul_sum,
  apply convex_on.map_sum_le falling_product_convex, {simp},
  { have h : (fintype.card β : ℝ) ≠ 0, simp [betapos],
    rw fintype.card at h,
    simp [fintype.card, mul_inv_cancel h],
  },
  { simp, },
  { exact spos, }
end

lemma combine_bounds {spos : s ≠ 0} {betapos : fintype.card β ≠ 0} :
  falling_product s ((fintype.card β : ℝ)⁻¹  * r.edge_finset.card) ≤ (fintype.card β : ℝ)⁻¹ * ((fintype.card α).choose s) * ↑(t - 1) :=
begin
  transitivity, apply lower_bound_stars, iterate 3 {assumption},
  rw mul_assoc, apply mul_le_mul, refl, norm_cast, apply upper_bound_stars _ noKst,
  iterate 2 { repeat {rw inv_nonneg}, norm_cast, apply nat.zero_le, }
end

theorem kovari_sos_toth :
  r.edge_finset.card ≤ 100 * (↑(fintype.card α) * (fintype.card β : ℝ) ^ ((↑s - 1) / ↑s) + ↑(fintype.card β)) := sorry

end rel
