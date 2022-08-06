import algebra.big_operators.ring
import data.finset.powerset
import data.nat.interval
import data.rat.defs
import data.rat.basic
import order.upper_lower
import data.finset.n_ary
import data.finset.lattice
import data.fintype.basic

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

def sum_truncated_inf_div_card_mul_choose (𝒜 : finset (finset α)) : ℚ :=
∑ s, (truncated_inf 𝒜 s).card / (s.card * (card α).choose s.card)

def sum_trancated_sup_div_sub_card_mul_choose (𝒜 : finset (finset α)) : ℚ :=
∑ s, (truncated_sup 𝒜 s).card / ((card α - s.card) * (card α).choose s.card)

-- def Φ (n : nat) : ℚ := n * ∑ k in Ico 1 n, k⁻¹ -- `n * ∑ k in range n, k⁻¹`?
def mul_sum_range_inv (n : nat) : ℚ := n * ∑ k in range n, k⁻¹

lemma truncated_sup_union_eq_of_not_nontriv_of_nontriv
  {𝒜 ℬ : finset (finset α)} {s : finset α}
  (ha : ¬nontriv_z_star (𝒜 : set (finset α)) s) (hb : nontriv_z_star (ℬ : set (finset α)) s) :
  truncated_sup (𝒜 ∪ ℬ) s = truncated_sup ℬ s :=
begin
  have := nontriv_z_star_union_iff.mpr (or.inr hb),
  rw ←coe_union at this,
  rw [truncated_sup_of_nontriv_z_star this,
      truncated_sup_of_nontriv_z_star hb],
  simp [nontriv_z_star] at ha,
  rw filter_union,
  simp_rw le_iff_subset,
  rw filter_false_of_mem ha,
  simp,
end

lemma truncated_sup_union_eq_of_nontriv_of_not_nontriv
  {𝒜 ℬ : finset (finset α)} {s : finset α}
  (ha : nontriv_z_star (𝒜 : set (finset α)) s) (hb : ¬nontriv_z_star (ℬ : set (finset α)) s) :
  truncated_sup (𝒜 ∪ ℬ) s = truncated_sup 𝒜 s :=
begin
  rw union_comm,
  exact truncated_sup_union_eq_of_not_nontriv_of_nontriv hb ha,
end

lemma truncated_sup_union_eq_of_not_nontriv
  {𝒜 ℬ : finset (finset α)} {s : finset α}
  (ha : ¬nontriv_z_star (𝒜 : set (finset α)) s) (hb : ¬nontriv_z_star (ℬ : set (finset α)) s) :
  truncated_sup (𝒜 ∪ ℬ) s = ⊤ :=
begin
  have := λ h, or.elim (nontriv_z_star_union_iff.mp h) ha hb,
  rw ←coe_union at this,
  rw truncated_sup_of_not_nontriv_z_star this,
end

lemma truncated_sup_image2_inf_eq_inter_z_star_of_nontriv
  {𝒜 ℬ : finset (finset α)} {s : finset α}
  (h𝒜 : nontriv_z_star (𝒜 : set (finset α)) s) (hℬ : nontriv_z_star (ℬ : set (finset α)) s) :
  truncated_sup (image₂ (⊓) 𝒜 ℬ) s = truncated_sup 𝒜 s ⊓ truncated_sup ℬ s :=
begin
  rw [truncated_sup_of_nontriv_z_star h𝒜,
      truncated_sup_of_nontriv_z_star hℬ,
      truncated_sup_of_nontriv_z_star],
  swap,
  { exact (coe_image₂ (⊓) 𝒜 ℬ).symm ▸ nontriv_z_star_image2_inf_iff.mpr ⟨h𝒜, hℬ⟩, },
  /- simp [sup_inf_distrib_left, sup_inf_distrib_right, ←bUnion_image_left, filter_bUnion], -/
  ext,
  split;
  intro h,
  { rcases mem_sup.mp h with ⟨u, hu, hau⟩,
    cases mem_filter.mp hu with hu hsu,
    rcases mem_image₂.mp hu with ⟨v, w, hv, hw, hvwu⟩,
    rw ←hvwu at hsu,
    cases _root_.le_inf_iff.mp hsu with hsv hsw,
    refine mem_of_subset _ hau,
    rw [←hvwu, id.def],
    exact le_iff_subset.mp (inf_le_inf (le_sup (mem_filter.mpr ⟨hv, hsv⟩))
                                       (le_sup (mem_filter.mpr ⟨hw, hsw⟩))), },
  { simp at h,
    rcases mem_sup.mp h.1 with ⟨v, hv, hav⟩,
    rcases mem_sup.mp h.2 with ⟨w, hw, haw⟩,
    rcases mem_filter.mp hv with ⟨hv, hsv⟩,
    rcases mem_filter.mp hw with ⟨hw, hsw⟩,
    exact mem_sup.mpr ⟨v ⊓ w, mem_filter.mpr ⟨mem_image₂.mpr ⟨v, w, hv, hw, rfl⟩, le_inf hsv hsw⟩,
                              mem_inter.mpr ⟨hav, haw⟩⟩, },
end

lemma truncated_sup_image2_inf_of_not_nontriv_left {𝒜 ℬ : finset (finset α)} {s : finset α}
  (h𝒜 : ¬nontriv_z_star (𝒜 : set (finset α)) s) :
  truncated_sup (image₂ (⊓) 𝒜 ℬ) s = ⊤ :=
begin
  have := h𝒜 ∘ and.left ∘ nontriv_z_star_image2_inf_iff.mp,
  rw ←coe_image₂ at this,
  rw truncated_sup_of_not_nontriv_z_star this,
end

lemma truncated_sup_image2_inf_of_not_nontriv_right {𝒜 ℬ : finset (finset α)} {s : finset α}
  (hℬ : ¬nontriv_z_star (ℬ : set (finset α)) s) :
  truncated_sup (image₂ (⊓) 𝒜 ℬ) s = ⊤ :=
begin
  rw [image₂_comm (@_root_.inf_comm _ _), truncated_sup_image2_inf_of_not_nontriv_left hℬ],
end

lemma card_truncated_sup_union_add_card_truncated_sup_image₂_inf_eq_card_truncated_sup_add_card_truncated_sup
  (𝒜 ℬ : finset (finset α))
  (s : finset α) :
  (truncated_sup (𝒜 ∪ ℬ) s).card + (truncated_sup (image₂ (⊓) 𝒜 ℬ) s).card =
    (truncated_sup 𝒜 s).card + (truncated_sup ℬ s).card :=
begin
  cases decidable.em (nontriv_z_star (𝒜 : set (finset α)) s) with ha ha;
  cases decidable.em (nontriv_z_star (ℬ : set (finset α)) s) with hb hb,
  { rw [truncated_sup_union ha hb,
        truncated_sup_image2_inf_eq_inter_z_star_of_nontriv ha hb],
    apply card_union_add_card_inter },
  { rw [truncated_sup_union_eq_of_nontriv_of_not_nontriv ha hb,
        truncated_sup_of_not_nontriv_z_star hb,
        truncated_sup_image2_inf_of_not_nontriv_right hb], },
  { rw [truncated_sup_union_eq_of_not_nontriv_of_nontriv ha hb,
        truncated_sup_of_not_nontriv_z_star ha,
        truncated_sup_image2_inf_of_not_nontriv_left ha,
        add_comm], },
  { rw [truncated_sup_of_not_nontriv_z_star ha,
        truncated_sup_of_not_nontriv_z_star hb,
        truncated_sup_union_eq_of_not_nontriv ha hb,
        truncated_sup_image2_inf_of_not_nontriv_left ha], },
end

lemma sum_truncated_inf_div_card_mul_choose_union_eq (𝒜 ℬ : finset (finset α)) :
  sum_trancated_sup_div_sub_card_mul_choose (𝒜 ∪ ℬ) =
  sum_trancated_sup_div_sub_card_mul_choose 𝒜 + sum_trancated_sup_div_sub_card_mul_choose ℬ -
  sum_trancated_sup_div_sub_card_mul_choose (image₂ (⊓) 𝒜 ℬ) :=
begin
  apply eq_sub_of_add_eq,
  dunfold sum_trancated_sup_div_sub_card_mul_choose,
  rw [←sum_add_distrib, ←sum_add_distrib],
  congr,
  ext : 1,
  rw [div_add_div_same, div_add_div_same],
  congr' 1,
  rw [←nat.cast_add, ←nat.cast_add],
  congr' 1,
  exact card_truncated_sup_union_add_card_truncated_sup_image₂_inf_eq_card_truncated_sup_add_card_truncated_sup _ _ _,
end

lemma sum_div_sub_card_mul_choose_card_eq_mul_sum_range_inv_add_one [nonempty α] :
  ∑ i : finset (finset α), (card α / ((card α - i.card) * (card α).choose i.card) : ℚ) =
  mul_sum_range_inv (card α) + 1 :=
begin
  have := finset.powerset_univ,
  have : (univ : finset (finset α)) = univ := rfl,
  have := set.powerset_univ,
  rw powerset_card_bUnion,
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
