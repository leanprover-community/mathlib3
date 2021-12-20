/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.locally_finite
import data.finsupp.basic

open finset
open_locale big_operators pointwise

section dite
variables {α β γ : Sort*} {σ : α → Sort*} (f : α → β) {P Q : Prop} [decidable P] [decidable Q]
  {a b c : α}

lemma exists_iff_of_forall {Q : P → Prop} (h : ∀ h, Q h) : (∃ h, Q h) ↔ P :=
⟨Exists.fst, λ H, ⟨H, h H⟩⟩

lemma not_ne_iff : ¬ a ≠ b ↔ a = b := not_not

lemma dite_eq_iff {a : P → α} {b : ¬ P → α} : dite P a b = c ↔ (∃ h, a h = c) ∨ ∃ h, b h = c :=
by by_cases P; simp *

@[simp] lemma dite_eq_left_iff {b : ¬ P → α} : dite P (λ _, a) b = a ↔ ∀ h, b h = a :=
by by_cases P; simp *

@[simp] lemma dite_eq_right_iff {a : P → α} : dite P a (λ _, b) = b ↔ ∀ h, a h = b :=
by by_cases P; simp *

lemma dite_ne_left_iff {b : ¬ P → α} : dite P (λ _, a) b ≠ a ↔ ∃ h, a ≠ b h :=
by { rw [ne.def, dite_eq_left_iff, not_forall], exact exists_congr (λ h, by rw ne_comm) }

lemma dite_ne_right_iff {a : P → α} : dite P a (λ _, b) ≠ b ↔ ∃ h, a h ≠ b :=
by simp_rw [ne.def, dite_eq_right_iff, not_forall]

protected lemma ne.dite_eq_left_iff {b : ¬ P → α} (h' : ∀ h, a ≠ b h) : dite P (λ _, a) b = a ↔ P :=
dite_eq_left_iff.trans $ ⟨λ H, of_not_not $ λ h, h' h (H h).symm, λ h H, (H h).elim⟩

protected lemma ne.dite_eq_right_iff {a : P → α} (h : ∀ h', a h' ≠ b) :
  dite P a (λ _, b) = b ↔ ¬ P :=
dite_eq_right_iff.trans $ ⟨λ H h', h h' (H h'), λ h' H, (h' H).elim⟩

protected lemma ne.dite_ne_left_iff {b : ¬ P → α} (h : ∀ h', a ≠ b h') :
  dite P (λ _, a) b ≠ a ↔ ¬ P :=
dite_ne_left_iff.trans $ exists_iff_of_forall h

protected lemma ne.dite_ne_right_iff {a : P → α} (h : ∀ h', a h' ≠ b) : dite P a (λ _, b) ≠ b ↔ P :=
dite_ne_right_iff.trans $ exists_iff_of_forall h

end dite

variables {ι α β : Type*}

namespace finsupp
variables [has_zero α] [decidable_eq α] {s : finset ι} [decidable_pred (∈ s)] {i : ι}

open function

/-- Create an element of `ι →₀ α` from a finset `s` and a function `f` defined on this finset. -/
def indicator (s : finset ι) [decidable_pred (∈ s)] (f : Π i ∈ s, α) : ι →₀ α :=
{ to_fun := λ i, if H : i ∈ s then f i H else 0,
  support := (s.attach.filter $ λ i : s, f i.1 i.2 ≠ 0).map $ embedding.subtype _,
  mem_support_to_fun := λ i, begin
    rw [mem_map, dite_ne_right_iff],
    exact ⟨λ ⟨⟨j, hj⟩, hf, rfl⟩, ⟨hj, (mem_filter.1 hf).2⟩,
      λ ⟨hi, hf⟩, ⟨⟨i, hi⟩, mem_filter.2 $ ⟨mem_attach _ _, hf⟩, rfl⟩⟩,
  end }

@[simp] lemma indicator_apply (s : finset ι) [decidable_pred (∈ s)] (f : Π i ∈ s, α) (i : ι) :
  indicator s f i = if hi : i ∈ s then f i hi else 0 :=
rfl

@[simp] lemma indicator_of_mem (hi : i ∈ s) (f : Π i ∈ s, α) : indicator s f i = f i hi :=
dif_pos hi

@[simp] lemma indicator_of_not_mem (hi : i ∉ s) (f : Π i ∈ s, α) : indicator s f i = 0 := dif_neg hi

lemma indicator_injective (s : finset ι) [decidable_pred (∈ s)] :
  injective (λ f : Π i ∈ s, α, indicator s f) :=
begin
  intros a b h,
  ext i hi,
  rw [←indicator_of_mem hi a, ←indicator_of_mem hi b],
  exact congr_fun h i,
end

lemma support_indicator_subset (s : finset ι) [decidable_pred (∈ s)] (f : Π i ∈ s, α) :
  ((indicator s f).support : set ι) ⊆ s :=
begin
  rintro i hi,
  rw [mem_coe, mem_support_iff] at hi,
  by_contra,
  exact hi (indicator_of_not_mem h _),
end

-- lemma support_indicator (s : finset ι) [decidable_pred (∈ s)] (f : Π i ∈ s, α) :
--   ((indicator s f).support : set ι) = s ∩ function.support f :=
-- sorry

end finsupp

open finsupp

namespace finset

lemma not_mem_subset {s t :finset α} (h : s ⊆ t) {a : α} : a ∉ t → a ∉ s := mt $ @h _

@[to_additive]
lemma one_mem_one [has_one α] : (1 : α) ∈ (1 : finset α) := by simp [has_one.one]

@[simp] lemma Icc_eq_singleton_iff [partial_order α] [locally_finite_order α] {a b c : α} :
  Icc a b = {c} ↔ a = c ∧ b = c :=
begin
  refine ⟨λ h, _, _⟩,
  { have hab : a ≤ b := nonempty_Icc.1 (h.symm.subst $ singleton_nonempty c),
    exact ⟨eq_of_mem_singleton $ h.subst $ left_mem_Icc.2 hab,
      eq_of_mem_singleton $ h.subst $ right_mem_Icc.2 hab⟩ },
  { rintro ⟨rfl, rfl⟩,
    exact Icc_self _ }
end

variables [decidable_eq ι] [decidable_eq α] [has_zero α]

/-- Finitely supported product of finsets. -/
def finsupp (s : finset ι) (t : ι → finset α) : finset (ι →₀ α) :=
(s.pi t).map ⟨indicator s, indicator_injective s⟩

@[simp] lemma mem_finsupp_iff {s : finset ι} {t : ι → finset α} {f : ι →₀ α} :
  f ∈ s.finsupp t ↔ f.support ⊆ s ∧ ∀ i ∈ s, f i ∈ t i :=
begin
  refine mem_map.trans ⟨_, _⟩,
  { rintro ⟨f, hf, rfl⟩,
    refine ⟨support_indicator_subset _ _, λ i hi, _⟩,
    convert mem_pi.1 hf i hi,
    exact indicator_of_mem hi _ },
  { refine λ h, ⟨λ i _, f i, mem_pi.2 h.2, _⟩,
    ext i,
    dsimp,
    exact ite_eq_left_iff.2 (λ hi, (not_mem_support_iff.1 $ λ H, hi $ h.1 H).symm) }
end

/-- -/
@[simp] lemma mem_finsupp_iff_of_support_subset {s : finset ι} {t : ι →₀ finset α} {f : ι →₀ α}
  (ht : t.support ⊆ s) :
  f ∈ s.finsupp t ↔ ∀ i, f i ∈ t i :=
begin
  refine mem_finsupp_iff.trans (forall_and_distrib.symm.trans $ forall_congr $ λ i, ⟨λ h, _,
    λ h, ⟨λ hi, ht $ mem_support_iff.2 $ λ H, mem_support_iff.1 hi _, λ _, h⟩⟩),
  { by_cases hi : i ∈ s,
    { exact h.2 hi },
    { rw [not_mem_support_iff.1 (mt h.1 hi), not_mem_support_iff.1 (not_mem_subset ht hi)],
      exact zero_mem_zero } },
  { rwa [H, mem_zero] at h }
end

@[simp] lemma card_finsupp (s : finset ι) (t : ι → finset α) :
  (s.finsupp t).card = ∏ i in s, (t i).card :=
(card_map _).trans $ card_pi _ _

end finset

open finset

namespace finsupp
section bundled_Icc
variables [decidable_eq ι] [has_zero α] [partial_order α] [locally_finite_order α] {f g : ι →₀ α}
  {i : ι} {a : α}

/-- A pointwise `finset.Icc` bundled as a `finsupp`. -/
@[simps] def Icc (f g : ι →₀ α) : ι →₀ finset α :=
{ to_fun := λ i, Icc (f i) (g i),
  support := f.support ∪ g.support,
  mem_support_to_fun := λ i, begin
    rw [mem_union, ←not_iff_not, not_or_distrib, not_mem_support_iff, not_mem_support_iff,
      not_ne_iff],
    exact Icc_eq_singleton_iff.symm,
  end }

@[simp] lemma mem_Icc_apply_iff : a ∈ f.Icc g i ↔ f i ≤ a ∧ a ≤ g i := mem_Icc

end bundled_Icc

section pi
variables [decidable_eq ι] [decidable_eq α] [has_zero α]

/-- Given a finitely supported function `f : ι →₀ finset α`, one can define the finset
`f.pi` of all finitely supported functions whose value at `i` is in `f i` for all `i`. -/
def pi (f : ι →₀ finset α) : finset (ι →₀ α) := f.support.finsupp f

@[simp] lemma mem_pi {f : ι →₀ finset α} {g : ι →₀ α} : g ∈ f.pi ↔ ∀ i, g i ∈ f i :=
mem_finsupp_iff_of_support_subset $ subset.refl _

@[simp] lemma card_pi (f : ι →₀ finset α) : f.pi.card = f.prod (λ i, (f i).card) :=
begin
  rw [pi, card_finsupp],
  exact finset.prod_congr rfl (λ i _, by simp only [pi.nat_apply, nat.cast_id]),
end

end pi

section locally_finite
variables [decidable_eq ι] [decidable_eq α] [partial_order α] [has_zero α] [locally_finite_order α]

instance : locally_finite_order (ι →₀ α) :=
locally_finite_order.of_Icc (ι →₀ α)
  (λ f g, (f.support ∪ g.support).finsupp $ f.Icc g)
  (λ f g x, begin
    refine (mem_finsupp_iff_of_support_subset $ subset.refl _).trans (_),
    simp_rw [mem_Icc_apply_iff, forall_and_distrib],
    refl,
  end)

variables (f g : ι →₀ α)

lemma card_Icc : (finset.Icc f g).card =
  ∏ i in f.support ∪ g.support, (finset.Icc (f i) (g i)).card :=
card_finsupp _ _

lemma card_Ico : (Ico f g).card = ∏ i in f.support ∪ g.support, (finset.Icc (f i) (g i)).card - 1 :=
by rw [card_Ico_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioc : (Ioc f g).card = ∏ i in f.support ∪ g.support, (finset.Icc (f i) (g i)).card - 1 :=
by rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]

lemma card_Ioo : (Ioo f g).card = ∏ i in f.support ∪ g.support, (finset.Icc (f i) (g i)).card - 2 :=
by rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]

end locally_finite
end finsupp
