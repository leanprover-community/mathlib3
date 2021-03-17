import data.fin
import data.fintype.basic
import data.finset.basic
import data.nat.basic
import algebra.big_operators.order

lemma erase_inj_on {α : Type*} [decidable_eq α] {x y : α} (s : finset α) (hx : x ∈ s) :
  s.erase x = s.erase y → x = y :=
begin
  rw [←finset.sdiff_singleton_eq_erase, ←finset.sdiff_singleton_eq_erase],
  intro h,
  have : x ∈ s ∩ {x}, simpa,
  rw finset.inter_eq_inter_of_sdiff_eq_sdiff h at this,
  simpa [hx] using this,
end

lemma never_inj {α β : Type*} [decidable_eq α] [decidable_eq β] (s : finset α) (f : α → β)
  (h : ∀ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y) :
2 * (s.image f).card ≤ s.card :=
begin
  rw finset.card_eq_sum_card_image f s,
  have : ∀ a ∈ s.image f, 2 ≤ (s.filter (λ x, f x = a)).card,
  { intros a ha,
    simp only [finset.mem_image] at ha,
    rcases ha with ⟨a, ha, rfl⟩,
    apply finset.one_lt_card.2,
    rcases h a ha with ⟨b, hb₁, hab₁, hab₂⟩,
    simp only [exists_prop, finset.mem_filter],
    refine ⟨a, ⟨‹a ∈ s›, rfl⟩, b, ⟨‹b ∈ s›, ‹f a = f b›.symm⟩, ‹a ≠ b›⟩ },
  convert finset.sum_le_sum this,
  rw mul_comm,
  rw finset.sum_const_nat,
  simp,
end

example {a b : ℕ} (h : 2 * b ≤ a) : a ≤ 2 * (a - b) :=
begin
  rw [nat.mul_sub_left_distrib, two_mul a, nat.add_sub_assoc h],
  apply nat.le.intro rfl,
end

lemma injective_fails {α β : Type*} (f : α → β) [decidable_eq α] [decidable_eq β] (X : finset α) :
(X.filter (λ x, ∃ y ∈ X, x ≠ y ∧ f x = f y)).card ≤ 2 * (X.card - (X.image f).card) :=
begin
  let K := X.filter (λ x, ∃ y ∈ X, x ≠ y ∧ f x = f y),
  change K.card ≤ 2 * _,
  have : ((X \ K).image f).card = (X \ K).card,
  { apply finset.card_image_of_inj_on,
  simp only [finset.mem_sdiff, and_imp],
  rintro x hx hx' y hy - fxfy,
  by_contra,
  apply ‹x ∉ K›,
  exact finset.mem_filter.2 ⟨‹x ∈ X›, y, ‹y ∈ X›, ‹x ≠ y›, ‹f x = f y›⟩ },
  have : disjoint (K.image f) ((X \ K).image f),
  { simp only [finset.disjoint_left, not_exists, and_imp, exists_prop, not_and,
      finset.mem_image, exists_imp_distrib, forall_apply_eq_imp_iff₂, finset.mem_sdiff],
    rintro x _ y hy₁ hy₂ _,
    have hy₃ := hy₂,
    simp only [not_exists, exists_prop, not_and, ne.def, finset.mem_filter, hy₁, true_and] at hy₃,
    apply hy₃ _ (finset.filter_subset _ _ ‹x ∈ K›) _ ‹f y = f x›,
    apply (ne_of_mem_of_not_mem ‹x ∈ K› ‹y ∉ K›).symm },
  have : (K.image f).card + ((X \ K).image f).card = (X.image f).card,
  { rw [←finset.card_disjoint_union ‹disjoint _ _›, ←finset.image_union,
        finset.union_sdiff_of_subset (finset.filter_subset _ _)], },
  have : (X \ K).card + K.card = X.card,
  { rw [←finset.card_disjoint_union finset.sdiff_disjoint,
        finset.sdiff_union_of_subset (finset.filter_subset _ _)] },
  have hK : ∀ x ∈ K, (∃ y ∈ K, x ≠ y ∧ f x = f y),
  { intros x hx,
    rcases finset.mem_filter.1 hx with ⟨_, y, _, _, _⟩,
    refine ⟨y, _, ‹x ≠ y›, ‹f x = f y›⟩,
    apply finset.mem_filter.2,
    refine ⟨‹y ∈ X›, x, ‹x ∈ X›, ‹x ≠ y›.symm, ‹f x = f y›.symm⟩ },
  have := never_inj _ f hK,
  rw ‹_ = X.card›.symm,
  rw ‹_ = (X.image f).card›.symm,
  rw ‹((X \ K).image f).card = _›,
  rw nat.add_comm,
  rw nat.add_sub_add_right,
  rw [nat.mul_sub_left_distrib, two_mul K.card, nat.add_sub_assoc this],
  apply nat.le.intro rfl,
end

lemma non_inj_card_two {α β : Type*} (f : α → β) [decidable_eq α] [decidable_eq β]
  (X : finset α)
  (hX₁ : X.card = (X.image f).card + 1) :
(X.filter (λ x, ∃ y ∈ X, x ≠ y ∧ f x = f y)).card = 2 :=
begin
  let K := X.filter (λ x, ∃ y ∈ X, x ≠ y ∧ f x = f y),
  have hK : ∀ x ∈ K, (∃ y ∈ K, x ≠ y ∧ f x = f y),
  { intros x hx,
    rcases finset.mem_filter.1 hx with ⟨_, y, _, _, _⟩,
    refine ⟨y, _, ‹x ≠ y›, ‹f x = f y›⟩,
    apply finset.mem_filter.2,
    refine ⟨‹y ∈ X›, x, ‹x ∈ X›, ‹x ≠ y›.symm, ‹f x = f y›.symm⟩ },
  change K.card = 2,
  have : (X.image f).card < X.card,
  { rw hX₁,
    exact lt_add_one (finset.card _) },
  have : ¬(∀ (x₁ ∈ X) (x₂ ∈ X), f x₁ = f x₂ → x₁ = x₂),
  { intro t,
    apply ne_of_lt this,
    apply finset.card_image_of_inj_on t },
  push_neg at this,
  rcases this with ⟨x₁, hx₁, x₂, hx₂, x₁x₂, neq⟩,
  apply le_antisymm,
  { have : K.card ≤ _ := injective_fails f X,
    rw hX₁ at this,
    simpa using this },
  { apply finset.one_lt_card.2,
    refine ⟨_, finset.mem_filter.2 ⟨‹x₁ ∈ X›, _, ‹x₂ ∈ X›, ‹x₁ ≠ x₂›, ‹f x₁ = f x₂›⟩, _,
               finset.mem_filter.2 ⟨‹x₂ ∈ X›, _, ‹x₁ ∈ X›, ‹x₁ ≠ x₂›.symm, ‹f x₁ = f x₂›.symm⟩,
               ‹x₁ ≠ x₂›⟩ }
end

lemma subset_erase_iff {α : Type*} [decidable_eq α] (x : α) {s t : finset α} :
  s ⊆ t.erase x ↔ s ⊆ t ∧ x ∉ s :=
⟨λ h, ⟨finset.subset.trans h (finset.erase_subset x t), λ q, by simpa using h q⟩,
 λ ⟨h₁, h₂⟩ y hy, finset.mem_erase_of_ne_of_mem (ne_of_mem_of_not_mem hy h₂) (h₁ hy)⟩

lemma my_thing {α β : Type*} (f : α → β) [decidable_eq α] [decidable_eq β]
  (X : finset α) (Z : finset β)
  (hX₁ : X.card = Z.card + 1) (hX₂ : X.image f = Z) :
(X.powerset.filter (λ (Y : finset _), Y.image f = Z ∧ Y.card = Z.card)).card = 2 :=
begin
  subst hX₂,
  have : (X.powerset.filter (λ Y, finset.image f Y = X.image f ∧ Y.card = (X.image f).card)).card =
    (X.filter (λ x, ∃ y ∈ X, x ≠ y ∧ f x = f y)).card,
  { apply (finset.card_congr (λ a _, X.erase a) _ _ _).symm,
    { intros a ha,
      dsimp,
      rw finset.mem_filter at ha,
      simp only [finset.mem_powerset, finset.mem_filter, finset.erase_subset, true_and],
      rw finset.card_erase_of_mem ha.1,
      rw hX₁,
      simp only [and_true, eq_self_iff_true, nat.pred_succ],
      conv_rhs {rw ← finset.insert_erase ha.1},
      rw finset.image_insert,
      rw finset.insert_eq_of_mem,
      simpa [and_assoc, and_comm (_ ∈ X), ←ne.def, ne_comm, eq_comm] using ha.2 },
    { intros a b ha hb h,
      exact erase_inj_on X (finset.filter_subset _ X ha) h },
    { intros Y hY,
      dsimp,
      simp only [finset.mem_powerset, finset.mem_filter] at hY,
      simp only [exists_prop, finset.mem_filter],
      have : (X \ Y).nonempty,
      { rw [←finset.card_pos, finset.card_sdiff hY.1, hX₁, hY.2.2],
        simp only [nat.zero_lt_one, nat.add_sub_cancel_left] },
      rcases this with ⟨x, hx⟩,
      simp only [finset.mem_sdiff] at hx,
      refine ⟨x, ⟨hx.1, _⟩, _⟩,
      have : f x ∈ Y.image f,
      { rw hY.2.1,
        apply finset.mem_image_of_mem,
        apply hx.1 },
      simp only [exists_prop, finset.mem_image] at this,
      rcases this with ⟨y, _, _⟩,
      refine ⟨y, hY.1 ‹y ∈ Y›, (ne_of_mem_of_not_mem ‹y ∈ Y› hx.2).symm, ‹f y = f x›.symm⟩,
      symmetry,
      apply finset.eq_of_subset_of_card_le,
      rw subset_erase_iff,
      refine ⟨hY.1, hx.2⟩,
      rw finset.card_erase_of_mem hx.1,
      rw hX₁,
      rw hY.2.2,
      simp } },
  rw this,
  apply non_inj_card_two,
  apply hX₁,
end

example {α : Type*} {m : ℕ} (f : α → fin m) [decidable_eq α] (X : finset α) (hX₁ : X.card = m+1)
  (hX₂ : X.image f = finset.univ) :
(X.powerset.filter (λ (Y : finset _), Y.image f = finset.univ ∧ Y.card = m)).card = 2 :=
begin
  rw ← finset.card_fin m at hX₁,
  simpa using my_thing f X finset.univ hX₁ hX₂,
end

example {α : Type*} {m : ℕ} (f : α → fin (m+1)) [decidable_eq α] (X : finset α) (hX₁ : X.card = m+1)
  (hX₂ : X.image f = finset.univ.erase 0) :
(X.powerset.filter (λ (Y : finset _), Y.image f = finset.univ.erase 0 ∧ Y.card = m)).card = 2 :=
begin
  have : X.card = (finset.univ.erase 0 : finset (fin (m+1))).card + 1,
  { simp [hX₁, finset.card_erase_of_mem] },
  simpa [finset.card_erase_of_mem] using my_thing f X (finset.univ.erase 0) ‹X.card = _› hX₂,
end
