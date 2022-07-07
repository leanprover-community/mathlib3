import algebra.big_operators.ring
import data.finset.powerset
import data.nat.interval
import data.rat.defs
import order.upper_lower

/-!
# The Ahlswede-Zhang identity

This file proves the Ahlswede-Zhang identity, which is a nontrivial relation between

## Main declarations

* `finset.truncated_sup`
* `finset.truncated_inf`
-/

namespace finset
variables {ι α : Type*}

section fintype
variables [fintype α] [decidable_eq α] {s t : finset α}

@[simp] lemma compl_subset_compl_iff : sᶜ ⊆ tᶜ ↔ t ⊆ s := @compl_le_compl_iff_le (finset α) _ _ _

end fintype

section
variables [boolean_algebra α]

@[simp] protected lemma compl_sup (s : finset ι) (f : ι → α) : (s.sup f)ᶜ = s.inf (compl ∘ f) :=
map_finset_sup (order_iso.compl α) _ _

@[simp] protected lemma compl_inf (s : finset ι) (f : ι → α) : (s.inf f)ᶜ = s.sup (compl ∘ f) :=
map_finset_inf (order_iso.compl α) _ _

end

section
variables [preorder α] {s t : set α} {a : α}

--TODO: Will come from `order.upper_lower`
def nontriv_z (s : set α) (a : α) : Prop := ∃ b ∈ s, b ≤ a
def nontriv_z_star (s : set α) (a : α) : Prop := ∃ b ∈ s, a ≤ b

instance (s : finset α) [@decidable_rel α (≤)] : decidable_pred (nontriv_z (s : set α)) :=
λ _, finset.decidable_dexists_finset

instance (s : finset α) [@decidable_rel α (≤)] : decidable_pred (nontriv_z_star (s : set α)) :=
λ _, finset.decidable_dexists_finset

lemma nontriv_z_union_iff : nontriv_z (s ∪ t) a ↔ nontriv_z s a ∨ nontriv_z t a :=
by simp [nontriv_z, or_and_distrib_right, exists_or_distrib]

lemma nontriv_z_star_union_iff :
  nontriv_z_star (s ∪ t) a ↔ nontriv_z_star s a ∨ nontriv_z_star t a :=
by simp [nontriv_z_star, or_and_distrib_right, exists_or_distrib]

end

section
variables [semilattice_sup α] {s t : set α} {a : α}

lemma nontriv_z_image2_sup_iff : nontriv_z (set.image2 (⊔) s t) a ↔ nontriv_z s a ∧ nontriv_z t a :=
begin
  simp only [nontriv_z, set.mem_image2, exists_and_distrib_left, exists_prop],
  split,
  { rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩,
    exact ⟨⟨b, hb, le_sup_left.trans ha⟩, c, hc, le_sup_right.trans ha⟩ },
  { rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩,
    exact ⟨b ⊔ c, ⟨b, hb, c, hc, rfl⟩, _root_.sup_le hab hac⟩ }
end

end

section
variables [semilattice_inf α] {s t : set α} {a : α}

lemma nontriv_z_star_image2_inf_iff :
  nontriv_z_star (set.image2 (⊓) s t) a ↔ nontriv_z_star s a ∧ nontriv_z_star t a :=
begin
  simp only [nontriv_z_star, set.mem_image2, exists_and_distrib_left, exists_prop],
  split,
  { rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩,
    exact ⟨⟨b, hb, ha.trans inf_le_left⟩, c, hc, ha.trans inf_le_right⟩ },
  { rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩,
    exact ⟨b ⊓ c, ⟨b, hb, c, hc, rfl⟩, _root_.le_inf hab hac⟩ }
end

end

section
variables [semilattice_sup α] [bounded_order α] [@decidable_rel α (≤)] {s t : finset α} {a : α}

/-- The infimum of the elements of `s` less than `a` if there are some, otherwise `⊥`. -/
def truncated_sup (s : finset α) (a : α) : α :=
if nontriv_z_star (s : set α) a then (s.filter $ λ ℬ, a ≤ ℬ).sup id else ⊤

lemma truncated_sup_of_nontriv_z_star (h : nontriv_z_star (s : set α) a) :
  truncated_sup s a = (s.filter $ λ ℬ, a ≤ ℬ).sup id :=
if_pos h

lemma truncated_sup_of_not_nontriv_z_star (h : ¬ nontriv_z_star (s : set α) a) :
  truncated_sup s a = ⊤ := if_neg h

lemma le_truncated_sup (s : finset α) (a : α) : a ≤ truncated_sup s a :=
begin
  rw truncated_sup,
  split_ifs,
  { obtain ⟨ℬ, hb, h⟩ := h,
    exact h.trans (le_sup $ mem_filter.2 ⟨hb, h⟩) },
  { exact le_top }
end

variables [decidable_eq α]

lemma truncated_sup_union (hs : nontriv_z_star (s : set α) a) (ht : nontriv_z_star (t : set α) a) :
  truncated_sup (s ∪ t) a = truncated_sup s a ⊔ truncated_sup t a :=
begin
  rw [truncated_sup_of_nontriv_z_star hs, truncated_sup_of_nontriv_z_star ht,
    truncated_sup_of_nontriv_z_star],
  rw [filter_union, sup_union],
  push_cast,
  exact nontriv_z_star_union_iff.2 (or.inl hs),
end

end

section
variables [semilattice_inf α] [bounded_order α] [@decidable_rel α (≤)] {s t : finset α} {a : α}

/-- The infimum of the elements of `s` less than `a` if there are some, otherwise `⊥`. -/
def truncated_inf (s : finset α) (a : α) : α :=
if nontriv_z (s : set α) a then (s.filter $ λ ℬ, ℬ ≤ a).inf id else ⊥

lemma truncated_inf_of_nontriv_z (h : nontriv_z (s : set α) a) :
  truncated_inf s a = (s.filter $ λ ℬ, ℬ ≤ a).inf id :=
if_pos h

lemma truncated_inf_of_not_nontriv_z (h : ¬ nontriv_z (s : set α) a) : truncated_inf s a = ⊥ := if_neg h

lemma truncated_inf_le (s : finset α) (a : α) : truncated_inf s a ≤ a :=
begin
  rw truncated_inf,
  split_ifs,
  { obtain ⟨ℬ, hb, h⟩ := h,
    exact (inf_le $ mem_filter.2 ⟨hb, h⟩).trans h },
  { exact bot_le }
end

variables [decidable_eq α]

lemma truncated_inf_union (hs : nontriv_z (s : set α) a) (ht : nontriv_z (t : set α) a) :
  truncated_inf (s ∪ t) a = truncated_inf s a ⊓ truncated_inf t a :=
begin
  rw [truncated_inf_of_nontriv_z hs, truncated_inf_of_nontriv_z ht,  truncated_inf_of_nontriv_z],
  rw [filter_union, inf_union],
  push_cast,
  exact nontriv_z_union_iff.2 (or.inl hs),
end

end

section
variables [boolean_algebra α] [@decidable_rel α (≤)] {s : finset α} {a : α}

@[simp] lemma nontriv_z_compl_iff :
  nontriv_z (s.map ⟨compl, compl_injective⟩ : set α) aᶜ ↔ nontriv_z_star (s : set α) a :=
(equiv.exists_congr_left ⟨compl, compl, compl_compl, compl_compl⟩).trans $ by simp [nontriv_z_star]

@[simp] lemma nontriv_z_star_compl_iff :
  nontriv_z_star (s.map ⟨compl, compl_injective⟩ : set α) aᶜ ↔ nontriv_z (s : set α) a :=
(equiv.exists_congr_left ⟨compl, compl, compl_compl, compl_compl⟩).trans $ by simp [nontriv_z]

@[simp] lemma  compl_truncated_sup (s : finset α) (a : α) :
  (truncated_sup s a)ᶜ = truncated_inf (s.map ⟨compl, compl_injective⟩) aᶜ :=
begin
  unfold truncated_sup,
  split_ifs,
  { rw truncated_inf_of_nontriv_z (nontriv_z_compl_iff.2 h),
    simp [map_filter, function.comp] },
  { rw [compl_top, truncated_inf_of_not_nontriv_z (nontriv_z_compl_iff.not.2 h)] }
end

@[simp] lemma  compl_truncated_inf (s : finset α) (a : α) :
  (truncated_inf s a)ᶜ = truncated_sup (s.map ⟨compl, compl_injective⟩) aᶜ :=
begin
  unfold truncated_inf,
  split_ifs,
  { rw truncated_sup_of_nontriv_z_star (nontriv_z_star_compl_iff.2 h),
    simp [map_filter, function.comp] },
  { rw [compl_bot, truncated_sup_of_not_nontriv_z_star (nontriv_z_star_compl_iff.not.2 h)] }
end

end
end finset

open finset (hiding card) fintype nat
open_locale big_operators

variables {α : Type*} [decidable_eq α] [fintype α]

def Δ (𝒜 : finset (finset α)) : ℚ :=
∑ s, (truncated_inf 𝒜 s).card / (s.card * (card α).choose s.card)

def Γ (𝒜 : finset (finset α)) : ℚ :=
∑ s, (truncated_sup 𝒜 s).card / ((card α - s.card) * (card α).choose s.card)

def Φ (n : nat) : ℚ := n * ∑ k in Ico 1 n, k⁻¹ -- `n * ∑ k in range n, k⁻¹`?

lemma truncated_sup_inters_product_eq_inter_z_star_of_nontriv
  {𝒜 ℬ : finset (finset α)} {s : finset α}
  (nontriv_a : nontriv_z_star 𝒜 x) (nontriv_b : nontriv_z_star ℬ x) :
  truncated_sup ((𝒜.product ℬ).image (function.uncurry (∩))) x = truncated_sup 𝒜 x ∩ truncated_sup ℬ x :=
begin
  dunfold truncated_sup,
  rw [ if_pos nontriv_a,
       if_pos nontriv_b,
       if_pos (nontriv_z_star_inters_product_iff.mpr ⟨nontriv_a, nontriv_b⟩) ],
  ext n_1,
  simp,
  split; intro h,
  { rcases mem_sup.mp h with ⟨y, hy, hny⟩,
    simp at hy,
    rcases hy with ⟨⟨ya, yb, ⟨⟨hya, hyb⟩, hy⟩⟩, hxy⟩,
    subst hy,
    split;
    apply mem_sup.mpr;
    simp,
    { exact ⟨ya, ⟨hya, (subset_inter_iff.mp hxy).1⟩, (mem_inter.mp hny).1⟩ },
    { exact ⟨yb, ⟨hyb, (subset_inter_iff.mp hxy).2⟩, (mem_inter.mp hny).2⟩ } },
  { rcases mem_sup.mp h.1 with ⟨ya, hya, hnya⟩,
    rcases mem_sup.mp h.2 with ⟨yb, hyb, hnyb⟩,
    simp at hya hyb,
    cases hya with hya hxya,
    cases hyb with hyb hxyb,
    apply mem_sup.mpr,
    simp,
    exact ⟨ ya ∩ yb, ⟨⟨ya, yb, ⟨hya, hyb⟩, rfl⟩, subset_inter hxya hxyb⟩,
            mem_inter.mpr ⟨hnya, hnyb⟩⟩ }
end

lemma truncated_sup_union_eq_of_triv_of_nontriv
  {𝒜 ℬ : finset (finset α)} {s : finset α}
  (triv_a : ¬nontriv_z_star 𝒜 x) (nontriv_b : nontriv_z_star ℬ x) :
  truncated_sup (𝒜 ∪ ℬ) x = truncated_sup ℬ x :=
begin
  dunfold truncated_sup,
  rw [ if_pos (nontriv_z_star_union_iff.mpr (or.inr nontriv_b)),
       if_pos nontriv_b ],
  simp [nontriv_z_star] at triv_a,
  congr' 1,
  ext y,
  rw [mem_filter, mem_filter], -- should i use `simp only [mem_filter]`?
  exact ⟨ λ ⟨h₁, h₂⟩, (mem_union.mp h₁).elim (λ h, (triv_a _ h h₂).elim) (λ h, ⟨h, h₂⟩),
          λ ⟨h₁, h₂⟩, ⟨mem_union_right _ h₁, h₂⟩⟩
end

lemma truncated_sup_union_eq_of_nontriv_of_triv
  {𝒜 ℬ : finset (finset α)} {s : finset α}
  (nontriv_a : nontriv_z_star 𝒜 x) (triv_b : ¬nontriv_z_star ℬ x) :
  truncated_sup (𝒜 ∪ ℬ) x = truncated_sup 𝒜 x :=
begin
  rw union_comm,
  apply truncated_sup_union_eq_of_triv_of_nontriv triv_b nontriv_a,
end

lemma card_z_star_union_add_card_z_star_intetrs_product_eq_z_star_add_z_star
  (𝒜 ℬ : finset (finset α))
  (s : finset α) :
  (z_star (𝒜 ∪ ℬ) x).card + (z_star ((𝒜.product ℬ).image (function.uncurry (∩))) x).card =
    (z_star 𝒜 x).card + (z_star ℬ x).card :=
begin
  cases decidable.em (nontriv_z_star 𝒜 x) with nontriv_a triv_a;
  cases decidable.em (nontriv_z_star ℬ x) with nontriv_b triv_b,
  { rw [ truncated_sup_union_distr_of_nontriv nontriv_a nontriv_b,
         truncated_sup_inters_product_eq_inter_z_star_of_nontriv nontriv_a nontriv_b ],
    apply card_union_add_card_inter },
  { rw truncated_sup_union_eq_of_nontriv_of_triv nontriv_a triv_b,
    dunfold truncated_sup,
    rw [ if_neg triv_b,
         if_neg (λ contra, triv_b (nontriv_z_star_inters_product_iff.mp contra).2) ] },
  { rw truncated_sup_union_eq_of_triv_of_nontriv triv_a nontriv_b,
    dunfold truncated_sup,
    rw [ if_neg triv_a,
         if_neg (λ contra, triv_a (nontriv_z_star_inters_product_iff.mp contra).1) ],
    rw add_comm },
  { dunfold truncated_sup,
    rw [ if_neg triv_a,
         if_neg triv_b,
         if_neg (λ contra, triv_a (nontriv_z_star_inters_product_iff.mp contra).1),
         if_neg (λ contra, (nontriv_z_star_union_iff.mp contra).elim triv_a triv_b) ], }
end
lemma Γ_union_eq (𝒜 ℬ : finset (finset α)) :
  Γ (𝒜 ∪ ℬ) = Γ 𝒜 + Γ ℬ - Γ ((𝒜.product ℬ).image (function.uncurry (∩))) :=
begin
  apply eq_sub_of_add_eq,
  dunfold Γ,
  rw [←sum_add_distrib, ←sum_add_distrib],
  congr,
  ext,
  rw [div_add_div_same, div_add_div_same],
  congr' 1,
  rw [←nat.cast_add, ←nat.cast_add],
  congr' 1,
  apply card_z_star_union_add_card_z_star_intetrs_product_eq_z_star_add_z_star,
end

lemma attach_compl_eq_bUnion_powerset_len :
  ({univ}ᶜ : finset (finset α)) = (range α.card).bUnion (λ k, powerset_len k univ) :=
begin
  rw ←image_bUnion_filter_eq {univ}ᶜ card,
  symmetry,
  apply bUnion_congr,
  { ext k,
    split;
    intro h;
    simp at ⊢ h,
    { rw ←card_attach at h,
      rcases exists_smaller_set univ k (le_of_lt h) with ⟨x, hx, hcard⟩,
      subst hcard,
      use x,
      split,
      { intro contra,
        rw contra at h,
        cases (lt_self_iff_false _).mp h },
      { refl } },
    { rcases h with ⟨x, hx, hcard⟩,
      subst hcard,
      cases lt_or_eq_of_le (card_le_univ x),
      { rw fintype.card_coe at h,
        exact h },
      { cases hx (eq_univ_of_card _ h), } } },
  { intros x hx,
    simp at hx,
    ext k,
    { split;
      intro h,
      { simp,
        rw mem_powerset_len at h,
        split,
        { intro contra,
          rw [←h.2, contra, card_attach] at hx,
          exact (lt_self_iff_false _).mp hx },
        { exact h.2 } },
      { simp at h,
        exact mem_powerset_len.mpr ⟨subset_univ _, h.2⟩ } } }
end

lemma pairwise_disjoint_powerset_len (s : finset α) :
  (range α.card : set ℕ).pairwise_disjoint (λ k, powerset_len k s) :=
begin
  dunfold set.pairwise_disjoint,
  -- why can't i unfold disjoint?
  sorry
end

lemma sum_div_sub_card_mul_choose_card_eq_Φ_add_one [nonempty α] :
  ({univ}ᶜ : finset (finset α)).sum
    (λ i, (α.card / ((α.card - i.card) * α.card.choose i.card) : ℚ)) =
  Φ α.card + 1 :=
begin
  rw attach_compl_eq_bUnion_powerset_len,
  rw sum_bUnion (pairwise_disjoint_powerset_len _),
  have : ∀ (x : ℕ) (i : finset ↥α) (hi : i ∈ powerset_len x (univ)),
    (α.card / ((α.card - i.card) * α.card.choose i.card) : ℚ) =
    (α.card / ((α.card - x) * α.card.choose x)),
  { intros x i hi,
    rw (mem_powerset_len.mp hi).2 },
  simp_rw sum_congr rfl (this _),
  simp_rw sum_const,
  simp_rw card_powerset_len,
  simp,
  have : ∀ (x ∈ range α.card),
    ((α.card.choose x) * (α.card / ((α.card - x) * α.card.choose x)) : ℚ) = α.card * (α.card - x)⁻¹,
  { intros x hx,
    have : (α.card.choose x : ℚ) ≠ 0
      := (norm_num.ne_zero_of_pos _ $ nat.cast_pos.mpr $ nat.choose_pos $ mem_range_le hx),
    rw [mul_div_left_comm, div_mul_left this, mul_one_div, div_eq_mul_inv] },
  rw sum_congr rfl this,
  rw ←mul_sum,
  unfold Φ,
  rw [ ←@mul_inv_cancel ℚ _ _ (nat.cast_ne_zero.mpr (hα ∘ card_eq_zero.mp)),
      ←mul_add ],
  simp,
  left,
  rw [add_comm],
  rw ←@sum_insert _ _ _ _ (λ x : ℕ, (x⁻¹ : ℚ)) _ _ right_not_mem_Ico,
  rw Ico_insert_right (nat.one_le_iff_ne_zero.mpr (hα ∘ card_eq_zero.mp)),
  apply sum_bij (λ x _, α.card - x),
  { intros x hx,
    simp at ⊢ hx,
    exact nat.succ_le_of_lt (nat.sub_pos_of_lt hx) },
  { intros x hx,
    simp at ⊢ hx,
    exact (nat.cast_sub (le_of_lt hx)).symm },
  { intros x y hx hy heq,
    simp at ⊢ hx hy,
    exact (tsub_right_inj (le_of_lt hx) (le_of_lt hy)).mp heq, },
  { intros x hx,
    simp at ⊢ hx,
    exact ⟨ α.card - x, nat.sub_lt (nat.pos_of_ne_zero (hα ∘ card_eq_zero.mp)) (hx.1),
                        (nat.sub_sub_self hx.2).symm ⟩ }
end

lemma finset.map_compl {α β : Type*} [fintype α] [fintype β] [decidable_eq α] [decidable_eq β]
  (s : finset α) (f : α → β) (hbij : function.bijective f) :
  (sᶜ).map ⟨f, hbij.1⟩ = (s.map ⟨f, hbij.1⟩)ᶜ :=
begin
  ext x,
  split,
  { simp,
    intros y hy hfy truncated_inf hz hfz,
    subst hfz,
    exact hy ((hbij.1 hfy).symm ▸ hz) },
  { simp,
    rintro h,
    cases hbij.2 x with y hy,
    subst hy,
    exact ⟨y, λ contra, h _ contra rfl, rfl⟩ }
end

lemma Γ_add_delta_eq_Φ_add_one (hα : α ≠ ∅) (𝒜 : finset ( finset α)) :
  Γ (𝒜.map ⟨compl, compl_injective⟩) + Δ 𝒜 = Φ α.card + 1 :=
begin
  dunfold Γ,
  dunfold Δ,
  have := finset.map_compl ({univ} : finset (finset α)) compl compl_bijective,
  simp [compl_α] at this,
  rw ←this,
  simp [sum_add_distrib.symm],
  simp_rw [(fintype.card_coe α).symm,
            card_compl,
            nat.cast_sub (card_le_univ _),
            nat.choose_symm (card_le_univ _) ],
  have := λ {x},  compl_truncated_inf_eq_z_star_compl 𝒜 xᶜ,
  simp at this,
  simp_rw [ this.symm,
            div_add_div_same,
            card_compl,
            nat.cast_sub (card_le_univ _) ],
  simp,
  simp_rw div_eq_mul_inv,
  apply sum_div_sub_card_mul_choose_card_eq_Φ_add_one hα,
end

lemma binomial_sum_eq (n m : ℕ) (h : n < m) :
  (range (n+1)).sum (λ (i : ℕ), ((n.choose i) * (n - m) * (m - i)⁻¹ * (m.choose i)⁻¹ : ℚ)) = -1 :=
begin
  let f : ℕ → ℚ := λ i, n.choose i * (m.choose i)⁻¹,
  have : ∀ (i ∈ range (n+1)), f (i + 1) - f i = (n.choose i) * (n - m) * (m - i)⁻¹ * (m.choose i)⁻¹,
  { intros i h₁,
    simp at h₁,
    have h₁ := nat.le_of_lt_succ h₁,
    have h₂ := lt_of_le_of_lt h₁ h,
    have h₃ := le_of_lt h₂,
    simp [f],
    have hi₄ : (i + 1 : ℚ) ≠ 0,
    { have := (@nat.cast_ne_zero ℚ _ _ _ _).mpr (nat.succ_ne_zero i),
      push_cast at this,
      exact this },
    have := congr_arg (coe : ℕ → ℚ) (nat.choose_succ_right_eq m i),
    push_cast at this,
    rw (eq_mul_inv_iff_mul_eq₀ hi₄).mpr this,
    have := congr_arg (coe : ℕ → ℚ) (nat.choose_succ_right_eq n i),
    push_cast at this,
    rw (eq_mul_inv_iff_mul_eq₀ hi₄).mpr this,
    have : (m - i : ℚ) ≠ 0 := sub_ne_zero_of_ne (ne_of_lt (nat.cast_lt.mpr h₂)).symm,
    have : (n.choose i : ℚ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_lt (nat.choose_pos h₁)).symm,
    have : (m.choose i : ℚ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_lt (nat.choose_pos h₃)).symm,
    field_simp,
    ring, },
  rw ←sum_congr rfl this,
  rw sum_range_sub,
  simp [f],
  simp [nat.choose_self, nat.choose_zero_right, nat.choose_eq_zero_of_lt h]
end

lemma filter_subset_compl_α_eq_union_powerset_len {y : finset α} (hy : y ≠ univ) :
  (filter (λ (s : finset α), x ⊆ y) {univ}ᶜ) = (range α.card).bUnion (λ k, powerset_len k y) :=
begin
  ext x,
  simp,
  split;
  intro h,
  { use x.card,
    have := lt_of_le_of_ne (card_le_univ _) (h.1 ∘ (card_eq_iff_eq_univ _).mp),
    simp at this,
    exact ⟨this, mem_powerset_len.mpr ⟨h.2, rfl⟩⟩ },
  { rcases h with ⟨n, hn, hx⟩,
    cases mem_powerset_len.mp hx with hxy hcard,
    subst hcard,
    split,
    { intro contra,
      rw contra at hn,
      simp at hn,
      exact hn },
    { exact hxy } }
end

lemma Γ_singleton_eq_Φ (hα : α ≠ ∅) {y : finset α} (hy : y ≠ univ) : Γ {y} = Φ α.card :=
begin
  rw ←sub_eq_of_eq_add (sum_div_sub_card_mul_choose_card_eq_Φ_add_one hα),
  dunfold Γ,
  rw sub_eq_add_neg,
  apply eq_add_of_sub_eq',
  rw ←sum_sub_distrib,
  simp_rw div_sub_div_same,
  rw ←sum_filter_add_sum_filter_not _ (λ x, x ⊆ y),
  have : ∀ (x ∈ filter (λ x, ¬x ⊆ y) {univ}ᶜ),
    ((((z_star {y} x).card) - α.card) / ((α.card - x.card) * (α.card.choose x.card)) : ℚ) = 0,
  { intros x hx,
    simp at hx,
    dunfold truncated_sup nontriv_z_star,
    simp [if_neg hx.2] },
  rw sum_congr rfl this,
  simp,
  have : ∀ (x ∈ filter (λ x, x ⊆ y) {univ}ᶜ),
    ((((z_star {y} x).card) - α.card) / ((α.card - x.card) * (α.card.choose x.card)) : ℚ) =
    (y.card - α.card) / ((α.card - x.card) * (α.card.choose x.card)),
  { intros x hx,
    simp at hx,
    dunfold truncated_sup nontriv_z_star,
    simp [filter_singleton, if_pos hx.2] },
  rw sum_congr rfl this,
  rw filter_subset_compl_α_eq_union_powerset_len hy,
  rw sum_bUnion (pairwise_disjoint_powerset_len _),
  have : ∀ (x : ℕ) (i ∈ powerset_len x y),
    ((y.card - α.card) / ((α.card - i.card) * (α.card.choose i.card)) : ℚ) =
    (y.card - α.card) * (α.card - x)⁻¹ * (α.card.choose x)⁻¹,
  { intros x i hi,
    rw [(mem_powerset_len.mp hi).2, div_eq_mul_inv, mul_inv, mul_assoc] },
  simp_rw [sum_congr rfl (this _), sum_const, card_powerset_len],
  simp,
  simp_rw ←mul_assoc,
  have h_card_y : y.card + 1 ≤ α.card,
  { cases lt_or_eq_of_le (card_le_univ y),
    { simp at h,
      exact nat.succ_le_of_lt h, },
    { cases hy (eq_univ_of_card _ h) } },
  have := Ico_union_Ico_eq_Ico (zero_le (y.card+1)) h_card_y,
  simp at this,
  rw [←this, range_eq_Ico, sum_union (Ico_disjoint_Ico_consecutive _ _ _)],
  have : ∀ (i ∈ Ico (y.card + 1) α.card),
    ((y.card.choose i) * (y.card - α.card) * (α.card - i)⁻¹ * (α.card.choose i)⁻¹ : ℚ) = 0,
  { intros i hi,
    simp at hi,
    rw nat.choose_eq_zero_iff.mpr (nat.lt_of_succ_le hi.1),
    simp, },
  rw [sum_congr rfl this],
  simp,
  apply binomial_sum_eq,
  cases lt_or_eq_of_le (card_le_univ y),
  { simp at h,
    exact h },
  { cases hy (eq_univ_of_card _ h) }
end

-- should i prove 𝒜 right version of this even if i don't use it?
lemma finset.left_eq_univ_of_inter_eq_univ {α : Type*} [fintype α] [decidable_eq α]
  {s t : finset α} :
  s ∩ t = univ → s = univ
:= λ h, eq_univ_of_forall (λ x, (mem_inter.mp (eq_univ_iff_forall.mp h x)).1)

theorem Γ_eq_Φ (𝒜 : finset (finset α)) (hα : α ≠ ∅) (ha : 𝒜 ≠ ∅ ∧ univ ∉ 𝒜) : Γ 𝒜 = Φ α.card :=
begin
  cases exists.intro 𝒜.card rfl with m' hcard,
  revert hcard 𝒜,
  apply nat.strong_induction_on m',
  intros m ih 𝒜 ha hcard,
  have ih : ∀ (a' : finset (finset α)), a'.card < m → a' ≠ ∅ → univ ∉ a' → Γ a' = Φ α.card
    := λ a' hcard ha'₁ ha'₂, ih a'.card hcard a' ⟨ha'₁, ha'₂⟩ rfl,
  rcases m with (_ | (_ | _)),
  { cases ha.1 (card_eq_zero.mp hcard) },
  { cases card_eq_one.mp hcard,
    subst h,
    simp at ha,
    apply Γ_singleton_eq_Φ hα (ne.symm ha) },
  rcases card_eq_succ.mp hcard with ⟨hd, tl, h_hd_tl, h_insert, h_card_tl⟩,
  subst h_insert,
  rw insert_eq,
  rw Γ_union_eq,
  rw [ih, ih, ih],
  simp,
  { apply @nat.lt_of_le_of_lt _ tl.card _,
    { rw [←@card_map _ _ tl, singleton_product],
      apply card_image_le },
    { rw h_card_tl,
      apply lt_add_one } },
  { intro contra,
    cases product_eq_empty.mp (image_eq_empty.mp contra),
    { exact singleton_ne_empty _ h, },
    { subst h,
      simp at h_card_tl,
      injection h_card_tl } },
  { intro contra,
    have := mem_image.mp contra,
    simp at this,
    rcases this with ⟨x, y, ⟨hx, hy⟩, hxy⟩,
    rw hx at hxy,
    exact (not_or_distrib.mp (ha.2 ∘ mem_insert.mpr)).1
          (finset.left_eq_univ_of_inter_eq_univ hxy).symm },
  { rw h_card_tl,
    apply lt_add_one },
  { intro contra,
    subst contra,
    simp at h_card_tl,
    injection h_card_tl },
  { exact (not_or_distrib.mp (ha.2 ∘ mem_insert.mpr)).2, },
  { simp },
  { simp },
  { simp,
    exact (not_or_distrib.mp (ha.2 ∘ mem_insert.mpr)).1 }
end
