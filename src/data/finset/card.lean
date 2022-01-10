/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import data.finset.basic
import tactic.by_contra

/-!
# Cardinality of a finite set

This defines the cardinality of a `finset` and provides induction principles for finsets.

## Main declarations

* `finset.card`: `s.card : ℕ` returns the cardinality of `s : finset α`.

### Induction principles

* `finset.strong_induction`: Strong induction
* `finset.strong_induction_on`
* `finset.strong_downward_induction`
* `finset.strong_downward_induction_on`
* `finset.case_strong_induction_on`

## TODO

Should we add a noncomputable version?
-/

open function multiset nat

variables {α β : Type*}

namespace finset
variables {s t : finset α} {a : α}

/-- `s.card` is the number of elements of `s`, aka its cardinality. -/
def card (s : finset α) : ℕ := s.1.card

lemma card_def (s : finset α) : s.card = s.1.card := rfl

@[simp] lemma card_mk {m nodup} : (⟨m, nodup⟩ : finset α).card = m.card := rfl

@[simp] lemma card_empty : card (∅ : finset α) = 0 := rfl

lemma card_le_of_subset : s ⊆ t → s.card ≤ t.card := multiset.card_le_of_le ∘ val_le_iff.mpr

@[mono] lemma card_mono : monotone (@card α) := by apply card_le_of_subset

@[simp] lemma card_eq_zero : s.card = 0 ↔ s = ∅ := card_eq_zero.trans val_eq_zero

lemma card_pos : 0 < s.card ↔ s.nonempty :=
pos_iff_ne_zero.trans $ (not_congr card_eq_zero).trans nonempty_iff_ne_empty.symm

alias finset.card_pos ↔ _ finset.nonempty.card_pos

lemma card_ne_zero_of_mem (h : a ∈ s) : s.card ≠ 0 := (not_congr card_eq_zero).2 $ ne_empty_of_mem h

@[simp] lemma card_singleton (a : α) : card ({a} : finset α) = 1 := card_singleton _

lemma card_singleton_inter [decidable_eq α] : ({a} ∩ s).card ≤ 1 :=
begin
  cases (finset.decidable_mem a s),
  { simp [finset.singleton_inter_of_not_mem h] },
  { simp [finset.singleton_inter_of_mem h] }
end

@[simp] lemma card_cons (h : a ∉ s) : (s.cons a h).card = s.card + 1 := card_cons _ _

section insert_erase
variables [decidable_eq α]

@[simp] lemma card_insert_of_not_mem (h : a ∉ s) : (insert a s).card = s.card + 1 :=
by rw [←cons_eq_insert _ _ h, card_cons]

lemma card_insert_of_mem (h : a ∈ s) : card (insert a s) = s.card := by rw insert_eq_of_mem h

lemma card_insert_le (a : α) (s : finset α) : card (insert a s) ≤ s.card + 1 :=
by by_cases a ∈ s; [{rw insert_eq_of_mem h, exact nat.le_succ _ }, rw card_insert_of_not_mem h]

/-- If `a ∈ s` is known, see also `finset.card_insert_of_mem` and `finset.card_insert_of_not_mem`.
-/
lemma card_insert_eq_ite : card (insert a s) = if a ∈ s then s.card else s.card + 1 :=
begin
  by_cases h : a ∈ s,
  { rw [card_insert_of_mem h, if_pos h] },
  { rw [card_insert_of_not_mem h, if_neg h] }
end

@[simp]
lemma card_erase_of_mem : a ∈ s → (s.erase a).card = pred s.card := card_erase_of_mem

@[simp] lemma card_erase_add_one : a ∈ s → (s.erase a).card + 1 = s.card := card_erase_add_one

lemma card_erase_lt_of_mem : a ∈ s → (s.erase a).card < s.card := card_erase_lt_of_mem

lemma card_erase_le : (s.erase a).card ≤ s.card := card_erase_le

lemma pred_card_le_card_erase : s.card - 1 ≤ (s.erase a).card :=
begin
  by_cases h : a ∈ s,
  { exact (card_erase_of_mem h).ge },
  { rw erase_eq_of_not_mem h,
    exact nat.sub_le _ _ }
end

/-- If `a ∈ s` is known, see also `finset.card_erase_of_mem` and `finset.erase_eq_of_not_mem`. -/
lemma card_erase_eq_ite : (s.erase a).card = if a ∈ s then pred s.card else s.card :=
card_erase_eq_ite

end insert_erase

@[simp] lemma card_range (n : ℕ) : (range n).card = n := card_range n

@[simp] lemma card_attach : s.attach.card = s.card := multiset.card_attach

end finset

section to_list_multiset
variables [decidable_eq α] (m : multiset α) (l : list α)

lemma multiset.card_to_finset : m.to_finset.card = m.erase_dup.card := rfl

lemma multiset.to_finset_card_le : m.to_finset.card ≤ m.card := card_le_of_le $ erase_dup_le _

lemma multiset.to_finset_card_of_nodup {m : multiset α} (h : m.nodup) : m.to_finset.card = m.card :=
congr_arg card $ multiset.erase_dup_eq_self.mpr h

lemma list.card_to_finset : l.to_finset.card = l.erase_dup.length := rfl

lemma list.to_finset_card_le : l.to_finset.card ≤ l.length := multiset.to_finset_card_le ⟦l⟧

lemma list.to_finset_card_of_nodup {l : list α} (h : l.nodup) : l.to_finset.card = l.length :=
multiset.to_finset_card_of_nodup h

end to_list_multiset

namespace finset
variables {s t : finset α} {f : α → β} {n : ℕ}

@[simp] lemma length_to_list (s : finset α) : s.to_list.length = s.card :=
by { rw [to_list, ←multiset.coe_card, multiset.coe_to_list], refl }

lemma card_image_le [decidable_eq β] : (s.image f).card ≤ s.card :=
by simpa only [card_map] using (s.1.map f).to_finset_card_le

lemma card_image_of_inj_on [decidable_eq β] (H : set.inj_on f s) : (s.image f).card = s.card :=
by simp only [card, image_val_of_inj_on H, card_map]

lemma inj_on_of_card_image_eq [decidable_eq β] (H : (s.image f).card = s.card) : set.inj_on f s :=
begin
  change (s.1.map f).erase_dup.card = s.1.card at H,
  have : (s.1.map f).erase_dup = s.1.map f,
  { refine multiset.eq_of_le_of_card_le (multiset.erase_dup_le _) _,
    rw H,
    simp only [multiset.card_map] },
  rw multiset.erase_dup_eq_self at this,
  exact inj_on_of_nodup_map this,
end

lemma card_image_eq_iff_inj_on [decidable_eq β] : (s.image f).card = s.card ↔ set.inj_on f s :=
⟨inj_on_of_card_image_eq, card_image_of_inj_on⟩

lemma card_image_of_injective [decidable_eq β] (s : finset α) (H : injective f) :
  (s.image f).card = s.card :=
card_image_of_inj_on $ λ x _ y _ h, H h

lemma fiber_card_ne_zero_iff_mem_image (s : finset α) (f : α → β) [decidable_eq β] (y : β) :
  (s.filter (λ x, f x = y)).card ≠ 0 ↔ y ∈ s.image f :=
by { rw [←pos_iff_ne_zero, card_pos, fiber_nonempty_iff_mem_image] }

@[simp] lemma card_map (f : α ↪ β) : (s.map f).card = s.card := multiset.card_map _ _

@[simp] lemma card_subtype (p : α → Prop) [decidable_pred p] (s : finset α) :
  (s.subtype p).card = (s.filter p).card :=
by simp [finset.subtype]

lemma card_filter_le (s : finset α) (p : α → Prop) [decidable_pred p] :
  (s.filter p).card ≤ s.card :=
card_le_of_subset $ filter_subset _ _

lemma eq_of_subset_of_card_le {s t : finset α} (h : s ⊆ t) (h₂ : t.card ≤ s.card) : s = t :=
eq_of_veq $ multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂

lemma filter_card_eq {p : α → Prop} [decidable_pred p] (h : (s.filter p).card = s.card) (x : α)
  (hx : x ∈ s) :
  p x :=
begin
  rw [←eq_of_subset_of_card_le (s.filter_subset p) h.ge, mem_filter] at hx,
  exact hx.2,
end

lemma card_lt_card (h : s ⊂ t) : s.card < t.card := card_lt_of_lt $ val_lt_iff.2 h

lemma card_eq_of_bijective (f : ∀ i, i < n → α) (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a)
  (hf' : ∀ i (h : i < n), f i h ∈ s) (f_inj : ∀ i j (hi : i < n)
  (hj : j < n), f i hi = f j hj → i = j) :
  s.card = n :=
begin
  classical,
  have : ∀ (a : α), a ∈ s ↔ ∃ i (hi : i ∈ range n), f i (mem_range.1 hi) = a,
    from λ a, ⟨λ ha, let ⟨i, hi, eq⟩ := hf a ha in ⟨i, mem_range.2 hi, eq⟩,
      λ ⟨i, hi, eq⟩, eq ▸ hf' i (mem_range.1 hi)⟩,
  have : s = ((range n).attach.image $ λi, f i.1 (mem_range.1 i.2)),
    by simpa only [ext_iff, mem_image, exists_prop, subtype.exists, mem_attach, true_and],
  calc s.card = card ((range n).attach.image $ λ i, f i.1 (mem_range.1 i.2)) :
      by rw this
    ... = card ((range n).attach) :
      card_image_of_injective _ $ λ ⟨i, hi⟩ ⟨j, hj⟩ eq,
        subtype.eq $ f_inj i j (mem_range.1 hi) (mem_range.1 hj) eq
    ... = card (range n) : card_attach
    ... = n : card_range n
end

lemma card_congr {t : finset β} (f : Π a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
  (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) :
  s.card = t.card :=
by classical;
calc s.card = s.attach.card : card_attach.symm
... = (s.attach.image (λ (a : {a // a ∈ s}), f a.1 a.2)).card
    : eq.symm (card_image_of_injective _ $ λ a b h, subtype.eq $ h₂ _ _ _ _ h)
... = t.card : congr_arg card (finset.ext $ λ b,
    ⟨λ h, let ⟨a, ha₁, ha₂⟩ := mem_image.1 h in ha₂ ▸ h₁ _ _,
      λ h, let ⟨a, ha₁, ha₂⟩ := h₃ b h in mem_image.2 ⟨⟨a, ha₁⟩, by simp [ha₂]⟩⟩)

lemma card_le_card_of_inj_on {t : finset β} (f : α → β) (hf : ∀ a ∈ s, f a ∈ t)
  (f_inj : ∀ a₁ ∈ s, ∀ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂) :
  s.card ≤ t.card :=
by classical;
  calc s.card = (s.image f).card : (card_image_of_inj_on f_inj).symm
    ... ≤ t.card : card_le_of_subset $ image_subset_iff.2 hf

/-- If there are more pigeons than pigeonholes, then there are two pigeons in the same pigeonhole.
-/
lemma exists_ne_map_eq_of_card_lt_of_maps_to {t : finset β} (hc : t.card < s.card)
  {f : α → β} (hf : ∀ a ∈ s, f a ∈ t) :
  ∃ (x ∈ s) (y ∈ s), x ≠ y ∧ f x = f y :=
begin
  classical,
  by_contra' hz,
  refine hc.not_le (card_le_card_of_inj_on f hf _),
  intros x hx y hy, contrapose, exact hz x hx y hy,
end

lemma le_card_of_inj_on_range (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
  (f_inj : ∀ (i < n) (j < n), f i = f j → i = j) :
  n ≤ s.card :=
calc n = card (range n) : (card_range n).symm
  ... ≤ s.card : card_le_card_of_inj_on f (by simpa only [mem_range]) (by simpa only [mem_range])

lemma surj_on_of_inj_on_of_card_le {t : finset β} (f : Π a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
  (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : t.card ≤ s.card) :
  ∀ b ∈ t, ∃ a ha, b = f a ha :=
begin
  classical,
  intros b hb,
  have h : (s.attach.image $ λ (a : {a // a ∈ s}), f a a.prop).card = s.card,
  { exact @card_attach _ s ▸ card_image_of_injective _
      (λ ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ h, subtype.eq $ hinj _ _ _ _ h) },
  have h' : image (λ a : {a // a ∈ s}, f a a.prop) s.attach = t,
  { exact eq_of_subset_of_card_le (λ b h, let ⟨a, ha₁, ha₂⟩ := mem_image.1 h in
      ha₂ ▸ hf _ _) (by simp [hst, h]) },
  rw ←h' at hb,
  obtain ⟨a, ha₁, ha₂⟩ := mem_image.1 hb,
  exact ⟨a, a.2, ha₂.symm⟩,
end

lemma inj_on_of_surj_on_of_card_le {t : finset β} (f : Π a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
  (hsurj : ∀ b ∈ t, ∃ a ha, b = f a ha) (hst : s.card ≤ t.card) ⦃a₁ a₂⦄ (ha₁ : a₁ ∈ s)
  (ha₂ : a₂ ∈ s) (ha₁a₂: f a₁ ha₁ = f a₂ ha₂) :
  a₁ = a₂ :=
by haveI : inhabited {x // x ∈ s} := ⟨⟨a₁, ha₁⟩⟩; exact
let f' : {x // x ∈ s} → {x // x ∈ t} := λ x, ⟨f x.1 x.2, hf x.1 x.2⟩ in
let g : {x // x ∈ t} → {x // x ∈ s} :=
  @surj_inv _ _ f'
    (λ x, let ⟨y, hy₁, hy₂⟩ := hsurj x.1 x.2 in ⟨⟨y, hy₁⟩, subtype.eq hy₂.symm⟩) in
have hg : injective g, from injective_surj_inv _,
have hsg : surjective g, from λ x,
  let ⟨y, hy⟩ := surj_on_of_inj_on_of_card_le (λ (x : {x // x ∈ t}) (hx : x ∈ t.attach), g x)
    (λ x _, show (g x) ∈ s.attach, from mem_attach _ _)
    (λ x y _ _ hxy, hg hxy) (by simpa) x (mem_attach _ _) in
  ⟨y, hy.snd.symm⟩,
have hif : injective f',
  from (left_inverse_of_surjective_of_right_inverse hsg
      (right_inverse_surj_inv _)).injective,
subtype.ext_iff_val.1 (@hif ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ (subtype.eq ha₁a₂))

/-! ### Lattice structure -/

section lattice
variables [decidable_eq α]

lemma card_union_add_card_inter (s t : finset α) : (s ∪ t).card + (s ∩ t).card = s.card + t.card :=
finset.induction_on t (by simp) $ λ a r har, by by_cases a ∈ s; simp *; cc

lemma card_union_le (s t : finset α) : (s ∪ t).card ≤ s.card + t.card :=
card_union_add_card_inter s t ▸ nat.le_add_right _ _

lemma card_union_eq (h : disjoint s t) : (s ∪ t).card = s.card + t.card :=
by rw [←card_union_add_card_inter, disjoint_iff_inter_eq_empty.1 h, card_empty, add_zero]

@[simp] lemma card_disjoint_union (h : disjoint s t) : card (s ∪ t) = s.card + t.card :=
by rw [←card_union_add_card_inter, disjoint_iff_inter_eq_empty.1 h, card_empty, add_zero]

lemma card_sdiff (h : s ⊆ t) : card (t \ s) = t.card - s.card :=
suffices card (t \ s) = card ((t \ s) ∪ s) - s.card, by rwa sdiff_union_of_subset h at this,
by rw [card_disjoint_union sdiff_disjoint, add_tsub_cancel_right]

lemma card_sdiff_add_card : (s \ t).card + t.card = (s ∪ t).card :=
by rw [←card_disjoint_union sdiff_disjoint, sdiff_union_self_eq_union]

end lattice

lemma filter_card_add_filter_neg_card_eq_card (p : α → Prop) [decidable_pred p] :
  (s.filter p).card + (s.filter (not ∘ p)).card = s.card :=
by { classical, simp [←card_union_eq, filter_union_filter_neg_eq, disjoint_filter] }

/-- Given a set `A` and a set `B` inside it, we can shrink `A` to any appropriate size, and keep `B`
inside it. -/
lemma exists_intermediate_set {A B : finset α} (i : ℕ) (h₁ : i + card B ≤ card A) (h₂ : B ⊆ A) :
  ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
begin
  classical,
  rcases nat.le.dest h₁ with ⟨k, _⟩,
  clear h₁,
  induction k with k ih generalizing A,
  { exact ⟨A, h₂, subset.refl _, h.symm⟩ },
  have : (A \ B).nonempty,
  { rw [←card_pos, card_sdiff h₂, ←h, nat.add_right_comm,
        add_tsub_cancel_right, nat.add_succ],
    apply nat.succ_pos },
  rcases this with ⟨a, ha⟩,
  have z : i + card B + k = card (erase A a),
  { rw [card_erase_of_mem, ←h, nat.add_succ, nat.pred_succ],
    rw mem_sdiff at ha,
    exact ha.1 },
  rcases ih _ z with ⟨B', hB', B'subA', cards⟩,
  { exact ⟨B', hB', trans B'subA' (erase_subset _ _), cards⟩ },
  { rintro t th,
    apply mem_erase_of_ne_of_mem _ (h₂ th),
    rintro rfl,
    exact not_mem_sdiff_of_mem_right th ha }
end

/-- We can shrink `A` to any smaller size. -/
lemma exists_smaller_set (A : finset α) (i : ℕ) (h₁ : i ≤ card A) :
  ∃ (B : finset α), B ⊆ A ∧ card B = i :=
let ⟨B, _, x₁, x₂⟩ := exists_intermediate_set i (by simpa) (empty_subset A) in ⟨B, x₁, x₂⟩

lemma exists_subset_or_subset_of_two_mul_lt_card [decidable_eq α] {X Y : finset α} {n : ℕ}
  (hXY : 2 * n < (X ∪ Y).card) :
  ∃ C : finset α, n < C.card ∧ (C ⊆ X ∨ C ⊆ Y) :=
begin
  have h₁ : (X ∩ (Y \ X)).card = 0 := finset.card_eq_zero.mpr (finset.inter_sdiff_self X Y),
  have h₂ : (X ∪ Y).card = X.card + (Y \ X).card,
  { rw [←card_union_add_card_inter X (Y \ X), finset.union_sdiff_self_eq_union, h₁, add_zero] },
  rw [h₂, two_mul] at hXY,
  rcases lt_or_lt_of_add_lt_add hXY with h|h,
  { exact ⟨X, h, or.inl (finset.subset.refl X)⟩ },
  { exact ⟨Y \ X, h, or.inr (finset.sdiff_subset Y X)⟩ }
end

/-! ### Explicit description of a finset from its card -/

lemma card_eq_one : s.card = 1 ↔ ∃ a, s = {a} :=
by cases s; simp only [multiset.card_eq_one, finset.card, ←val_inj, singleton_val]

lemma card_le_one : s.card ≤ 1 ↔ ∀ (a ∈ s) (b ∈ s), a = b :=
begin
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty,
  { simp },
  refine (nat.succ_le_of_lt (card_pos.2 ⟨x, hx⟩)).le_iff_eq.trans (card_eq_one.trans ⟨_, _⟩),
  { rintro ⟨y, rfl⟩,
    simp },
  { exact λ h, ⟨x, eq_singleton_iff_unique_mem.2 ⟨hx, λ y hy, h _ hy _ hx⟩⟩ }
end

lemma card_le_one_iff : s.card ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b := by { rw card_le_one, tauto }

lemma card_le_one_iff_subset_singleton [nonempty α] : s.card ≤ 1 ↔ ∃ (x : α), s ⊆ {x} :=
begin
  refine ⟨λ H, _, _⟩,
  { obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty,
    { exact ⟨classical.arbitrary α, empty_subset _⟩ },
    { exact ⟨x, λ y hy, by rw [card_le_one.1 H y hy x hx, mem_singleton]⟩ } },
  { rintro ⟨x, hx⟩,
    rw ←card_singleton x,
    exact card_le_of_subset hx }
end

/-- A `finset` of a subsingleton type has cardinality at most one. -/
lemma card_le_one_of_subsingleton [subsingleton α] (s : finset α) : s.card ≤ 1 :=
finset.card_le_one_iff.2 $ λ _ _ _ _, subsingleton.elim _ _

lemma one_lt_card : 1 < s.card ↔ ∃ (a ∈ s) (b ∈ s), a ≠ b :=
by { rw ←not_iff_not, push_neg, exact card_le_one }

lemma one_lt_card_iff : 1 < s.card ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b :=
by { rw one_lt_card, simp only [exists_prop, exists_and_distrib_left] }

lemma exists_ne_of_one_lt_card (hs : 1 < s.card) (a : α) : ∃ b, b ∈ s ∧ b ≠ a :=
begin
  obtain ⟨x, hx, y, hy, hxy⟩ := finset.one_lt_card.mp hs,
  by_cases ha : y = a,
  { exact ⟨x, hx, ne_of_ne_of_eq hxy ha⟩ },
  { exact ⟨y, hy, ha⟩ }
end

lemma card_eq_succ [decidable_eq α] :
  s.card = n + 1 ↔ (∃ a t, a ∉ t ∧ insert a t = s ∧ t.card = n) :=
⟨λ eq,
  let ⟨a, has⟩ := card_pos.mp (eq.symm ▸ nat.zero_lt_succ _ : 0 < s.card) in
    ⟨a, s.erase a, s.not_mem_erase a, insert_erase has,
      by simp only [eq, card_erase_of_mem has, pred_succ]⟩,
  λ ⟨a, t, hat, s_eq, n_eq⟩, s_eq ▸ n_eq ▸ card_insert_of_not_mem hat⟩

lemma card_eq_two [decidable_eq α] : s.card = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} :=
begin
  split,
  { rw card_eq_succ,
    simp_rw [card_eq_one],
    rintro ⟨a, _, hab, rfl, b, rfl⟩,
    exact ⟨a, b, not_mem_singleton.1 hab, rfl⟩ },
  { rintro ⟨x, y, hxy, rfl⟩,
    simp only [hxy, card_insert_of_not_mem, not_false_iff, mem_singleton, card_singleton] }
end

lemma card_eq_three [decidable_eq α] :
  s.card = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} :=
begin
  split,
  { rw card_eq_succ,
    simp_rw [card_eq_two],
    rintro ⟨a, _, abc, rfl, b, c, bc, rfl⟩,
    rw [mem_insert, mem_singleton, not_or_distrib] at abc,
    exact ⟨a, b, c, abc.1, abc.2, bc, rfl⟩ },
  { rintro ⟨x, y, z, xy, xz, yz, rfl⟩,
    simp only [xy, xz, yz, mem_insert, card_insert_of_not_mem, not_false_iff, mem_singleton,
      or_self, card_singleton] }
end

/-! ### Inductions -/

/-- Suppose that, given objects defined on all strict subsets of any finset `s`, one knows how to
define an object on `s`. Then one can inductively define an object on all finsets, starting from
the empty set and iterating. This can be used either to define data, or to prove properties. -/
def strong_induction {p : finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s) :
  ∀ (s : finset α), p s
| s := H s (λ t h, have t.card < s.card, from card_lt_card h, strong_induction t)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf card⟩]}

lemma strong_induction_eq {p : finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s) (s : finset α) :
  strong_induction H s = H s (λ t h, strong_induction H t) :=
by rw strong_induction

/-- Analogue of `strong_induction` with order of arguments swapped. -/
@[elab_as_eliminator] def strong_induction_on {p : finset α → Sort*} (s : finset α) :
  (∀ s, (∀ t ⊂ s, p t) → p s) → p s :=
λ H, strong_induction H s

lemma strong_induction_on_eq {p : finset α → Sort*} (s : finset α) (H : ∀ s, (∀ t ⊂ s, p t) → p s) :
  s.strong_induction_on H = H s (λ t h, t.strong_induction_on H) :=
by { dunfold strong_induction_on, rw strong_induction }

@[elab_as_eliminator] lemma case_strong_induction_on [decidable_eq α] {p : finset α → Prop}
  (s : finset α) (h₀ : p ∅) (h₁ : ∀ a s, a ∉ s → (∀ t ⊆ s, p t) → p (insert a s)) :
  p s :=
finset.strong_induction_on s $ λ s,
finset.induction_on s (λ _, h₀) $ λ a s n _ ih, h₁ a s n $
λ t ss, ih _ (lt_of_le_of_lt ss (ssubset_insert n) : t < _)

/-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all finsets `s` of
cardinality less than `n`, starting from finsets of card `n` and iterating. This
can be used either to define data, or to prove properties. -/
def strong_downward_induction {p : finset α → Sort*} {n : ℕ} (H : ∀ t₁, (∀ {t₂ : finset α},
  t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
  ∀ (s : finset α), s.card ≤ n → p s
| s := H s (λ t ht h, have n - t.card < n - s.card,
     from (tsub_lt_tsub_iff_left_of_le ht).2 (finset.card_lt_card h),
  strong_downward_induction t ht)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ (t : finset α), n - t.card)⟩]}

lemma strong_downward_induction_eq {p : finset α → Sort*}
  (H : ∀ t₁, (∀ {t₂ : finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁)
  (s : finset α) :
  strong_downward_induction H s = H s (λ t ht hst, strong_downward_induction H t ht) :=
by rw strong_downward_induction

/-- Analogue of `strong_downward_induction` with order of arguments swapped. -/
@[elab_as_eliminator] def strong_downward_induction_on {p : finset α → Sort*} (s : finset α)
  (H : ∀ t₁, (∀ {t₂ : finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
  s.card ≤ n → p s :=
strong_downward_induction H s

lemma strong_downward_induction_on_eq {p : finset α → Sort*} (s : finset α) (H : ∀ t₁,
  (∀ {t₂ : finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
  s.strong_downward_induction_on H = H s (λ t ht h, t.strong_downward_induction_on H ht) :=
by { dunfold strong_downward_induction_on, rw strong_downward_induction }

lemma lt_wf {α} : well_founded (@has_lt.lt (finset α) _) :=
have H : subrelation (@has_lt.lt (finset α) _)
    (inv_image ( < ) card),
  from λ x y hxy, card_lt_card hxy,
subrelation.wf H $ inv_image.wf _ $ nat.lt_wf

end finset
