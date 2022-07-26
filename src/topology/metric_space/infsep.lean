/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import topology.metric_space.basic

/-!

Draft implementation of infimum separation.

This is NOT A FINISHED FILE.
In particular it needs: documentation, missing lemmas, and possibly other stuff.
-/

variables {α β : Type*}

section extras

lemma set.not_subsingleton_iff {s : set α} : ¬ s.subsingleton ↔ ∃ x y ∈ s, x ≠ y :=
by simp_rw [set.subsingleton, not_forall]

open_locale ennreal

lemma le_edist_pi_iff {π : β → Type*} [fintype β] [nonempty β]
  [Π b, pseudo_emetric_space (π b)] {f g : Π b, π b} {d : ℝ≥0∞} :
  d ≤ edist f g ↔ ∃ b, d ≤ edist (f b) (g b) :=
begin
  by_cases hd : ⊥ < d,
  { exact (finset.le_sup_iff hd).trans (by simp only [finset.mem_univ, exists_true_left]) },
  { rw not_bot_lt_iff at hd, rw hd, simp only [ennreal.bot_eq_zero, zero_le, exists_const] }
end

lemma finset.off_diag_nonempty_iff [decidable_eq α] {s : finset α} :
  s.off_diag.nonempty ↔ ∃ x y ∈ s, x ≠ y :=
begin
  refine ⟨λ H, _, λ H, _⟩,
  { rcases H with ⟨⟨x, y⟩, hxy⟩, rw finset.mem_off_diag at hxy,
    rcases hxy with ⟨hx, hy, hxy⟩,
    exact ⟨x, hx, y, hy, hxy⟩ },
  { rcases H with ⟨x, hx, y, hy, hxy⟩,
    refine ⟨⟨x, y⟩, _⟩, rw finset.mem_off_diag,
    exact ⟨hx, hy, hxy⟩ }
end

end extras

namespace set

section infesep
open_locale ennreal
open function
/-- The "extended infimum separation" of a set with an edist function. -/
noncomputable def infesep [has_edist α] (s : set α) := ⨅ (x ∈ s) (y ∈ s) (hxy : x ≠ y), edist x y

section has_edist
variables [has_edist α] {x y : α} {s : set α}

lemma le_infesep_iff {d} : d ≤ s.infesep ↔ ∀ x y ∈ s, x ≠ y → d ≤ edist x y :=
by simp_rw [infesep, le_infi_iff]

lemma le_infesep_image_iff {d} {f : β → α} {s : set β} :
  d ≤ infesep (f '' s) ↔ ∀ x y ∈ s, f x ≠ f y → d ≤ edist (f x) (f y) :=
by simp_rw [le_infesep_iff, ball_image_iff]

lemma le_infesep_image_injective_iff {d} {f : β → α} (hf : injective f) {s : set β} :
  d ≤ infesep (f '' s) ↔ ∀ x y ∈ s, x ≠ y → d ≤ edist (f x) (f y) :=
by simp_rw [le_infesep_image_iff, hf.ne_iff]

lemma le_edist_of_le_infesep {d} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) (hd : d ≤ s.infesep) :
  d ≤ edist x y := le_infesep_iff.1 hd x hx y hy hxy

lemma infesep_le_edist_of_mem (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.infesep ≤ edist x y :=
le_edist_of_le_infesep hx hy hxy le_rfl

lemma le_infesep {d} (h : ∀ x y ∈ s, x ≠ y → d ≤ edist x y) : d ≤ s.infesep := le_infesep_iff.2 h

lemma infesep_lt_iff {d} : s.infesep < d ↔ ∃ x y ∈ s, x ≠ y ∧ edist x y < d :=
by simp_rw [infesep, infi_lt_iff, exists_prop]

lemma infesep_subsingleton (hs : s.subsingleton) : s.infesep = ∞ :=
eq_top_iff.2 (le_infesep (λ x hx y hy hxy, false.elim (hxy (hs hx hy))))

@[simp] lemma infesep_empty : infesep (∅ : set α) = ∞ :=
infesep_subsingleton subsingleton_empty

@[simp] lemma infesep_singleton : infesep ({x} : set α) = ∞ :=
infesep_subsingleton subsingleton_singleton

lemma infesep_Union_mem_option {ι : Type*} (o : option ι) (s : ι → set α) :
  infesep (⋃ i ∈ o, s i) = ⨅ i ∈ o, infesep (s i) := by cases o; simp

lemma infesep_anti : @antitone (set α) _ _ _ infesep :=
λ s t h, le_infesep $ λ x hx y hy, infesep_le_edist_of_mem (h hx) (h hy)

lemma infesep_insert_le : infesep (insert x s) ≤ ⨅ (y ∈ s) (hxy : x ≠ y), edist x y :=
begin
  simp_rw [le_infi_iff],
  refine λ _ hy hxy, infesep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ hy) hxy
end

lemma infesep_pair_le_left (hxy : x ≠ y) : infesep ({x, y} : set α) ≤ edist x y :=
infesep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hxy

lemma infesep_pair_le_right (hxy : x ≠ y) : infesep ({x, y} : set α) ≤ edist y x :=
by rw pair_comm; exact infesep_pair_le_left hxy.symm

lemma le_infesep_pair : (edist x y) ⊓ (edist y x) ≤ infesep ({x, y} : set α) :=
begin
  simp_rw [le_infesep_iff, inf_le_iff, mem_insert_iff, mem_singleton_iff],
  rintros a (rfl | rfl) b (rfl | rfl) hab; finish
end

lemma infesep_pair_eq' (hxy : x ≠ y) : infesep ({x, y} : set α) = (edist x y) ⊓ (edist y x) :=
le_antisymm (le_inf (infesep_pair_le_left hxy) (infesep_pair_le_right hxy)) le_infesep_pair

end has_edist

section pseudo_emetric_space
variables [pseudo_emetric_space α] {x y z : α} {s t : set α}

lemma infesep_pair_eq (hxy : x ≠ y) : infesep ({x, y} : set α) = edist x y :=
begin
  nth_rewrite 0 [← min_self (edist x y)],
  convert infesep_pair_eq' hxy using 2,
  rw edist_comm
end

lemma infesep_insert :
  infesep (insert x s) = (⨅ (y ∈ s) (hxy : x ≠ y), edist x y) ⊓ (s.infesep) :=
begin
  refine le_antisymm (le_min infesep_insert_le (infesep_anti (subset_insert _ _))) _,
  simp_rw [le_infesep_iff, inf_le_iff, mem_insert_iff],
  rintros y (rfl | hy) z (rfl | hz) hyz,
  { exact false.elim (hyz rfl) },
  { exact or.inl (infi_le_of_le _ (infi₂_le hz hyz)) },
  { rw edist_comm, exact or.inl (infi_le_of_le _ (infi₂_le hy hyz.symm)) },
  { exact or.inr (infesep_le_edist_of_mem hy hz hyz) }
end

lemma infesep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
  infesep ({x, y, z} : set α) = (edist x y) ⊓ (edist x z) ⊓ (edist y z) :=
by simp_rw [  infesep_insert, infi_insert, infi_singleton, infesep_singleton,
              inf_top_eq, cinfi_pos hxy, cinfi_pos hyz, cinfi_pos hxz]

lemma infesep_pi_le_of_le {π : β → Type*} [fintype β] [∀ b, pseudo_emetric_space (π b)]
  {s : Π (b : β), set (π b)} {c : ℝ≥0∞} (h : ∀ b, c ≤ infesep (s b) ) :
  c ≤ infesep (set.pi univ s) :=
begin
  refine le_infesep (λ x hx y hy hxy, _),
  rw function.ne_iff at hxy,
  haveI := nonempty_of_exists hxy,
  rcases hxy with ⟨i, hi⟩,
  rw mem_univ_pi at hx hy,
  exact le_edist_pi_iff.mpr ⟨i, (le_infesep_iff.1 (h i) _ (hx _) _ (hy _) hi)⟩
end

end pseudo_emetric_space

section pseudo_metric_space
variables [pseudo_metric_space α] {s : set α}

theorem infesep_eq_infty_iff : s.infesep = ∞ ↔ s.subsingleton :=
begin
  split,
  rw infesep, simp_rw infi_eq_top,
  intros H _ hx _ hy, by_contradiction hxy,
  exact edist_ne_top _ _ (H _ hx _ hy hxy),
  exact infesep_subsingleton,
end

theorem infesep_bounded_iff_not_subsingleton : s.infesep < ∞ ↔ ∃ (x ∈ s) (y ∈ s), x ≠ y :=
begin
  rw lt_top_iff_ne_top,
  refine iff.not_left _,
  push_neg,
  exact infesep_eq_infty_iff
end

end pseudo_metric_space

end infesep

section infsep

open set function
/-- The "infimum separation" of a set with an edist function. -/
noncomputable def infsep [has_edist α] (s : set α) : ℝ := ennreal.to_real (s.infesep)

end infsep

end set



namespace finset
section infesep
open_locale ennreal
open function

/-- The "extended infimum separation" of a finset with an edist function. -/
noncomputable def infesep [decidable_eq α] [has_edist α] (s : finset α) :=
s.off_diag.inf (uncurry edist)

variables [decidable_eq α]

section has_edist
variables [has_edist α] {x y : α} {s : finset α}

lemma le_infesep_iff {d} : d ≤ s.infesep ↔ ∀ x y ∈ s, x ≠ y → d ≤ edist x y :=
begin
  simp_rw [infesep, le_inf_iff, mem_off_diag], split,
  { exact λ H _ hx _ hy hxy, H ⟨_, _⟩ ⟨hx, hy, hxy⟩ },
  { exact λ H _ ⟨hx, hy, hxy⟩, H _ hx _ hy hxy }
end

lemma le_infesep_image_iff {d} {f : β → α} {s : finset β} :
  d ≤ infesep (image f s) ↔ ∀ x y ∈ s, f x ≠ f y → d ≤ edist (f x) (f y) :=
begin
  simp_rw [le_infesep_iff, mem_image], split,
  { exact λ H x hx y hy hxy, H _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy },
  { rintros H _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy, exact H _ hx _ hy hxy }
end

lemma le_infesep_image_injective_iff {d} {f : β → α} (hf : injective f) {s : finset β} :
  d ≤ infesep (image f s) ↔ ∀ x y ∈ s, x ≠ y → d ≤ edist (f x) (f y) :=
by simp_rw [le_infesep_image_iff, hf.ne_iff]

lemma le_edist_of_le_infesep {d} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) (hd : d ≤ s.infesep) :
  d ≤ edist x y := le_infesep_iff.1 hd x hx y hy hxy

lemma infesep_le_edist_of_mem (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.infesep ≤ edist x y :=
le_edist_of_le_infesep hx hy hxy le_rfl

lemma le_infesep {d} (h : ∀ x y ∈ s, x ≠ y → d ≤ edist x y) : d ≤ s.infesep := le_infesep_iff.2 h

lemma infesep_lt_iff {d} : s.infesep < d ↔ ∃ x y ∈ s, x ≠ y ∧ edist x y < d :=
begin
  simp_rw [infesep, finset.inf_lt_iff, exists_prop, mem_off_diag], split,
  { rintros ⟨_, ⟨hx, hy, hxy⟩, hxyd⟩, exact ⟨_, hx, _, hy, hxy, hxyd⟩ },
  { rintros ⟨x, hx, y, hy, hxy, hxyd⟩, exact ⟨(x, y), ⟨hx, hy, hxy⟩, hxyd⟩ }
end

lemma infesep_subsingleton (hs : ∀ {a b : α}, a ∈ s → b ∈ s → a = b) : s.infesep = ∞ :=
eq_top_iff.2 (le_infesep (λ x hx y hy hxy, false.elim (hxy (hs hx hy))))

@[simp] lemma infesep_empty : infesep (∅ : finset α) = ∞ :=
infesep_subsingleton (λ _ _ ha _, false.elim (not_mem_empty _ ha))

@[simp] lemma infesep_singleton : infesep ({x} : finset α) = ∞ :=
infesep_subsingleton (λ a b ha hb, by rw [mem_singleton.1 ha, mem_singleton.1 hb])

lemma infesep_anti : @antitone (finset α) _ _ _ infesep :=
λ s t h, le_infesep $ λ x hx y hy, infesep_le_edist_of_mem (h hx) (h hy)

lemma infesep_insert_le : infesep (insert x s) ≤ ⨅ (y ∈ s) (hxy : x ≠ y), edist x y :=
begin
  simp_rw [le_infi_iff],
  refine λ _ hy hxy, infesep_le_edist_of_mem (mem_insert_self _ _) (mem_insert_of_mem hy) hxy
end

lemma infesep_pair_le_left (hxy : x ≠ y) : infesep ({x, y} : finset α) ≤ edist x y :=
infesep_le_edist_of_mem (mem_insert_self _ _) (mem_insert_of_mem (mem_singleton_self _)) hxy

lemma infesep_pair_le_right (hxy : x ≠ y) : infesep ({x, y} : finset α) ≤ edist y x :=
by rw pair_comm; exact infesep_pair_le_left hxy.symm

lemma le_infesep_pair : (edist x y) ⊓ (edist y x) ≤ infesep ({x, y} : finset α) :=
begin
  simp_rw [le_infesep_iff, inf_le_iff, mem_insert, mem_singleton],
  rintros a (rfl | rfl) b (rfl | rfl) hab; finish
end

lemma infesep_pair_eq' (hxy : x ≠ y) : infesep ({x, y} : finset α) = (edist x y) ⊓ (edist y x) :=
le_antisymm (_root_.le_inf (infesep_pair_le_left hxy) (infesep_pair_le_right hxy)) le_infesep_pair

end has_edist

section pseudo_emetric_space
variables [pseudo_emetric_space α] {x y z : α} {s t : finset α}

lemma infesep_pair_eq (hxy : x ≠ y) : infesep ({x, y} : finset α) = edist x y :=
begin
  nth_rewrite 0 [← min_self (edist x y)],
  convert infesep_pair_eq' hxy using 2,
  rw edist_comm
end

lemma infesep_insert :
  infesep (insert x s) = (⨅ (y ∈ s) (hxy : x ≠ y), edist x y) ⊓ (s.infesep) :=
begin
  refine le_antisymm (_root_.le_min infesep_insert_le (infesep_anti (subset_insert _ _))) _,
  simp_rw [le_infesep_iff, inf_le_iff, mem_insert],
  rintros y (rfl | hy) z (rfl | hz) hyz,
  { exact false.elim (hyz rfl) },
  { exact or.inl (infi_le_of_le _ (infi₂_le hz hyz)) },
  { rw edist_comm, exact or.inl (infi_le_of_le _ (infi₂_le hy hyz.symm)) },
  { exact or.inr (infesep_le_edist_of_mem hy hz hyz) }
end

lemma infesep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
  infesep ({x, y, z} : finset α) = (edist x y) ⊓ (edist x z) ⊓ (edist y z) :=
by simp_rw [  infesep_insert, infi_insert, infi_singleton, infesep_singleton,
              inf_top_eq, cinfi_pos hxy, cinfi_pos hyz, cinfi_pos hxz]

end pseudo_emetric_space

end infesep

section infsep
open set function

/-- The "infimum separation" of a finset with an edist function. -/
noncomputable def infsep [decidable_eq α] [has_edist α] (s : finset α) :=
(s.off_diag.inf (uncurry edist)).to_real

end infsep

end finset

section esep_set_finset
open_locale classical
open function
variables [has_edist α]

lemma set.infesep_to_finset {s : set α} [fintype s] : s.infesep = s.to_finset.infesep :=
begin
  refine le_antisymm _ _,
  { simp_rw [finset.le_infesep_iff, set.mem_to_finset],
    exact λ _ hx _, set.infesep_le_edist_of_mem hx },
  { simp_rw [set.le_infesep_iff, ←set.mem_to_finset],
    exact λ _ hx _, finset.infesep_le_edist_of_mem hx }
end

lemma set.finite.infesep_to_finset {s : set α} (hs : s.finite) :
  s.infesep = hs.to_finset.infesep := @set.infesep_to_finset _ _ _ hs.fintype

lemma finset.infesep_coe {s : finset α} : s.infesep = (s : set α).infesep :=
begin
  refine le_antisymm _ _,
  { simp_rw set.le_infesep_iff,
    exact λ _ hx _, finset.infesep_le_edist_of_mem hx },
  { simp_rw [finset.le_infesep_iff, ←finset.mem_coe],
    exact λ _ hx _, set.infesep_le_edist_of_mem hx }
end

end esep_set_finset

section sep_set_finset
end sep_set_finset
