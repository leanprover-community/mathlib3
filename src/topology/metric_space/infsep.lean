/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import topology.metric_space.basic

/-!
# Infimum separation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the extended infimum separation of a set. This is approximately dual to the
diameter of a set, but where the extended diameter of a set is the supremum of the extended distance
between elements of the set, the extended infimum separation is the infimum of the (extended)
distance between *distinct* elements in the set.

We also define the infimum separation as the cast of the extended infimum separation to the reals.
This is the infimum of the distance between distinct elements of the set when in a pseudometric
space.

All lemmas and definitions are in the `set` namespace to give access to dot notation.

## Main definitions
* `set.einfsep`: Extended infimum separation of a set.
* `set.infsep`: Infimum separation of a set (when in a pseudometric space).

!-/

variables {α β : Type*}

namespace set

section einfsep
open_locale ennreal
open function

/-- The "extended infimum separation" of a set with an edist function. -/
noncomputable def einfsep [has_edist α] (s : set α) : ℝ≥0∞ :=
⨅ (x ∈ s) (y ∈ s) (hxy : x ≠ y), edist x y

section has_edist
variables [has_edist α] {x y : α} {s t : set α}

lemma le_einfsep_iff {d} : d ≤ s.einfsep ↔ ∀ (x y ∈ s) (hxy : x ≠ y), d ≤ edist x y :=
by simp_rw [einfsep, le_infi_iff]

theorem einfsep_zero :
  s.einfsep = 0 ↔ ∀ C (hC : 0 < C), ∃ (x y ∈ s) (hxy : x ≠ y), edist x y < C :=
by simp_rw [einfsep, ← bot_eq_zero, infi_eq_bot, infi_lt_iff]

theorem einfsep_pos :
  0 < s.einfsep ↔ ∃ C (hC : 0 < C), ∀ (x y ∈ s) (hxy : x ≠ y), C ≤ edist x y :=
by { rw [pos_iff_ne_zero, ne.def, einfsep_zero], simp only [not_forall, not_exists, not_lt] }

lemma einfsep_top : s.einfsep = ∞ ↔ ∀ (x y ∈ s) (hxy : x ≠ y), edist x y = ∞ :=
by simp_rw [einfsep, infi_eq_top]

lemma einfsep_lt_top : s.einfsep < ∞ ↔ ∃ (x y ∈ s) (hxy : x ≠ y), edist x y < ∞ :=
by simp_rw [einfsep, infi_lt_iff]

lemma einfsep_ne_top : s.einfsep ≠ ∞ ↔ ∃ (x y ∈ s) (hxy : x ≠ y), edist x y ≠ ∞ :=
by simp_rw [←lt_top_iff_ne_top, einfsep_lt_top]

lemma einfsep_lt_iff {d} : s.einfsep < d ↔ ∃ (x y ∈ s) (h : x ≠ y), edist x y < d :=
by simp_rw [einfsep, infi_lt_iff]

lemma nontrivial_of_einfsep_lt_top (hs : s.einfsep < ∞) : s.nontrivial :=
by { rcases einfsep_lt_top.1 hs with ⟨_, hx, _, hy, hxy, _⟩, exact ⟨_, hx, _, hy, hxy⟩ }

lemma nontrivial_of_einfsep_ne_top (hs : s.einfsep ≠ ∞) : s.nontrivial :=
nontrivial_of_einfsep_lt_top (lt_top_iff_ne_top.mpr hs)

lemma subsingleton.einfsep (hs : s.subsingleton) : s.einfsep = ∞ :=
by { rw einfsep_top, exact λ _ hx _ hy hxy, (hxy $ hs hx hy).elim }

lemma le_einfsep_image_iff {d} {f : β → α} {s : set β} :
  d ≤ einfsep (f '' s) ↔ ∀ x y ∈ s, f x ≠ f y → d ≤ edist (f x) (f y) :=
by simp_rw [le_einfsep_iff, ball_image_iff]

lemma le_edist_of_le_einfsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
  (hd : d ≤ s.einfsep) : d ≤ edist x y := le_einfsep_iff.1 hd x hx y hy hxy

lemma einfsep_le_edist_of_mem {x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y) :
  s.einfsep ≤ edist x y := le_edist_of_le_einfsep hx hy hxy le_rfl

lemma einfsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
  (hxy' : edist x y ≤ d) : s.einfsep ≤ d := le_trans (einfsep_le_edist_of_mem hx hy hxy) hxy'

lemma le_einfsep {d} (h : ∀ (x y ∈ s) (hxy : x ≠ y), d ≤ edist x y) :
  d ≤ s.einfsep := le_einfsep_iff.2 h

@[simp] lemma einfsep_empty : (∅ : set α).einfsep = ∞ := subsingleton_empty.einfsep

@[simp] lemma einfsep_singleton : ({x} : set α).einfsep = ∞ := subsingleton_singleton.einfsep

lemma einfsep_Union_mem_option {ι : Type*} (o : option ι) (s : ι → set α) :
  (⋃ i ∈ o, s i).einfsep = ⨅ i ∈ o, (s i).einfsep := by cases o; simp

lemma einfsep_anti (hst : s ⊆ t) : t.einfsep ≤ s.einfsep :=
le_einfsep $ λ x hx y hy, einfsep_le_edist_of_mem (hst hx) (hst hy)

lemma einfsep_insert_le : (insert x s).einfsep ≤ ⨅ (y ∈ s) (hxy : x ≠ y), edist x y :=
begin
  simp_rw le_infi_iff,
  refine λ _ hy hxy, einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ hy) hxy
end

lemma le_einfsep_pair : edist x y ⊓ edist y x ≤ ({x, y} : set α).einfsep :=
begin
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff, mem_singleton_iff],
  rintros a (rfl | rfl) b (rfl | rfl) hab; finish
end

lemma einfsep_pair_le_left (hxy : x ≠ y) : ({x, y} : set α).einfsep ≤ edist x y :=
einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hxy

lemma einfsep_pair_le_right (hxy : x ≠ y) : ({x, y} : set α).einfsep ≤ edist y x :=
by rw pair_comm; exact einfsep_pair_le_left hxy.symm

lemma einfsep_pair_eq_inf (hxy : x ≠ y) : ({x, y} : set α).einfsep = (edist x y) ⊓ (edist y x) :=
le_antisymm (le_inf (einfsep_pair_le_left hxy) (einfsep_pair_le_right hxy)) le_einfsep_pair

lemma einfsep_eq_infi : s.einfsep = ⨅ d : s.off_diag, (uncurry edist) (d : α × α) :=
begin
  refine eq_of_forall_le_iff (λ _, _),
  simp_rw [le_einfsep_iff, le_infi_iff, imp_forall_iff, set_coe.forall, subtype.coe_mk,
          mem_off_diag, prod.forall, uncurry_apply_pair, and_imp]
end

lemma einfsep_of_fintype [decidable_eq α] [fintype s] :
  s.einfsep = s.off_diag.to_finset.inf (uncurry edist) :=
begin
  refine eq_of_forall_le_iff (λ _, _),
  simp_rw [le_einfsep_iff, imp_forall_iff, finset.le_inf_iff, mem_to_finset, mem_off_diag,
          prod.forall, uncurry_apply_pair, and_imp]
end

lemma finite.einfsep (hs : s.finite) :
  s.einfsep = hs.off_diag.to_finset.inf (uncurry edist) :=
begin
  refine eq_of_forall_le_iff (λ _, _),
  simp_rw [le_einfsep_iff, imp_forall_iff, finset.le_inf_iff, finite.mem_to_finset, mem_off_diag,
          prod.forall, uncurry_apply_pair, and_imp]
end

lemma finset.coe_einfsep [decidable_eq α] {s : finset α} :
  (s : set α).einfsep = s.off_diag.inf (uncurry edist) :=
by simp_rw [einfsep_of_fintype, ← finset.coe_off_diag, finset.to_finset_coe]

lemma nontrivial.einfsep_exists_of_finite [finite s] (hs : s.nontrivial) :
  ∃ (x y ∈ s) (hxy : x ≠ y), s.einfsep = edist x y :=
begin
  classical,
  casesI nonempty_fintype s,
  simp_rw einfsep_of_fintype,
  rcases @finset.exists_mem_eq_inf _ _ _ _ (s.off_diag.to_finset) (by simpa) (uncurry edist)
    with ⟨_, hxy, hed⟩,
  simp_rw mem_to_finset at hxy,
  refine ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩
end

lemma finite.einfsep_exists_of_nontrivial (hsf : s.finite) (hs : s.nontrivial) :
  ∃ (x y ∈ s) (hxy : x ≠ y), s.einfsep = edist x y :=
by { letI := hsf.fintype, exact hs.einfsep_exists_of_finite }

end has_edist

section pseudo_emetric_space
variables [pseudo_emetric_space α] {x y z : α} {s t : set α}

lemma einfsep_pair (hxy : x ≠ y) : ({x, y} : set α).einfsep = edist x y :=
begin
  nth_rewrite 0 [← min_self (edist x y)],
  convert einfsep_pair_eq_inf hxy using 2,
  rw edist_comm
end

lemma einfsep_insert :
  einfsep (insert x s) = (⨅ (y ∈ s) (hxy : x ≠ y), edist x y) ⊓ (s.einfsep) :=
begin
  refine le_antisymm (le_min einfsep_insert_le (einfsep_anti (subset_insert _ _))) _,
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff],
  rintros y (rfl | hy) z (rfl | hz) hyz,
  { exact false.elim (hyz rfl) },
  { exact or.inl (infi_le_of_le _ (infi₂_le hz hyz)) },
  { rw edist_comm, exact or.inl (infi_le_of_le _ (infi₂_le hy hyz.symm)) },
  { exact or.inr (einfsep_le_edist_of_mem hy hz hyz) }
end

lemma einfsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
  einfsep ({x, y, z} : set α) = edist x y ⊓ edist x z ⊓ edist y z :=
by simp_rw [einfsep_insert, infi_insert, infi_singleton, einfsep_singleton,
            inf_top_eq, cinfi_pos hxy, cinfi_pos hyz, cinfi_pos hxz]

lemma le_einfsep_pi_of_le {π : β → Type*} [fintype β] [∀ b, pseudo_emetric_space (π b)]
  {s : Π (b : β), set (π b)} {c : ℝ≥0∞} (h : ∀ b, c ≤ einfsep (s b) ) :
  c ≤ einfsep (set.pi univ s) :=
begin
  refine le_einfsep (λ x hx y hy hxy, _),
  rw mem_univ_pi at hx hy,
  rcases function.ne_iff.mp hxy with ⟨i, hi⟩,
  exact le_trans (le_einfsep_iff.1 (h i) _ (hx _) _ (hy _) hi) (edist_le_pi_edist _ _ i)
end

end pseudo_emetric_space

section pseudo_metric_space
variables [pseudo_metric_space α] {s : set α}

theorem subsingleton_of_einfsep_eq_top (hs : s.einfsep = ∞) : s.subsingleton :=
begin
  rw einfsep_top at hs,
  exact λ _ hx _ hy, of_not_not (λ hxy, edist_ne_top _ _ (hs _ hx _ hy hxy))
end

theorem einfsep_eq_top_iff : s.einfsep = ∞ ↔ s.subsingleton :=
⟨subsingleton_of_einfsep_eq_top, subsingleton.einfsep⟩

theorem nontrivial.einfsep_ne_top (hs : s.nontrivial) : s.einfsep ≠ ∞ :=
by { contrapose! hs, rw not_nontrivial_iff, exact subsingleton_of_einfsep_eq_top hs }

theorem nontrivial.einfsep_lt_top (hs : s.nontrivial) : s.einfsep < ∞ :=
by { rw lt_top_iff_ne_top, exact hs.einfsep_ne_top }

theorem einfsep_lt_top_iff : s.einfsep < ∞ ↔ s.nontrivial :=
⟨nontrivial_of_einfsep_lt_top, nontrivial.einfsep_lt_top⟩

theorem einfsep_ne_top_iff : s.einfsep ≠ ∞ ↔ s.nontrivial :=
⟨nontrivial_of_einfsep_ne_top, nontrivial.einfsep_ne_top⟩

lemma le_einfsep_of_forall_dist_le {d} (h : ∀ (x y ∈ s) (hxy : x ≠ y), d ≤ dist x y) :
  ennreal.of_real d ≤ s.einfsep :=
le_einfsep $
λ x hx y hy hxy, (edist_dist x y).symm ▸ ennreal.of_real_le_of_real (h x hx y hy hxy)

end pseudo_metric_space

section emetric_space
variables [emetric_space α] {x y z : α} {s t : set α} {C : ℝ≥0∞} {sC : set ℝ≥0∞}

lemma einfsep_pos_of_finite [finite s] : 0 < s.einfsep :=
begin
  casesI nonempty_fintype s,
  by_cases hs : s.nontrivial,
  { rcases hs.einfsep_exists_of_finite with ⟨x, hx, y, hy, hxy, hxy'⟩,
    exact hxy'.symm ▸ edist_pos.2 hxy },
  { rw not_nontrivial_iff at hs,
    exact hs.einfsep.symm ▸ with_top.zero_lt_top }
end

lemma relatively_discrete_of_finite [finite s] :
  ∃ C (hC : 0 < C), ∀ (x y ∈ s) (hxy : x ≠ y), C ≤ edist x y :=
by { rw ← einfsep_pos, exact einfsep_pos_of_finite }

lemma finite.einfsep_pos (hs : s.finite) : 0 < s.einfsep :=
by { letI := hs.fintype, exact einfsep_pos_of_finite }

lemma finite.relatively_discrete (hs : s.finite) :
  ∃ C (hC : 0 < C), ∀ (x y ∈ s) (hxy : x ≠ y), C ≤ edist x y :=
by { letI := hs.fintype, exact relatively_discrete_of_finite }

end emetric_space

end einfsep

section infsep
open_locale ennreal
open set function

/-- The "infimum separation" of a set with an edist function. -/
noncomputable def infsep [has_edist α] (s : set α) : ℝ := ennreal.to_real (s.einfsep)

section has_edist
variables [has_edist α] {x y : α} {s : set α}

lemma infsep_zero : s.infsep = 0 ↔ s.einfsep = 0 ∨ s.einfsep = ∞ :=
by rw [infsep, ennreal.to_real_eq_zero_iff]

lemma infsep_nonneg : 0 ≤ s.infsep := ennreal.to_real_nonneg

lemma infsep_pos : 0 < s.infsep ↔ 0 < s.einfsep ∧ s.einfsep < ∞ :=
by simp_rw [infsep, ennreal.to_real_pos_iff]

lemma subsingleton.infsep_zero (hs : s.subsingleton) : s.infsep = 0 :=
by { rw [infsep_zero, hs.einfsep], right, refl }

lemma nontrivial_of_infsep_pos (hs : 0 < s.infsep) : s.nontrivial :=
by { contrapose hs, rw not_nontrivial_iff at hs, exact hs.infsep_zero ▸ lt_irrefl _ }

lemma infsep_empty : (∅ : set α).infsep = 0 :=
subsingleton_empty.infsep_zero

lemma infsep_singleton : ({x} : set α).infsep = 0 :=
subsingleton_singleton.infsep_zero

lemma infsep_pair_le_to_real_inf (hxy : x ≠ y) :
  ({x, y} : set α).infsep ≤ (edist x y ⊓ edist y x).to_real :=
by simp_rw [infsep, einfsep_pair_eq_inf hxy]

end has_edist

section pseudo_emetric_space
variables [pseudo_emetric_space α] {x y : α} {s : set α}

lemma infsep_pair_eq_to_real : ({x, y} : set α).infsep = (edist x y).to_real :=
begin
  by_cases hxy : x = y,
  { rw hxy, simp only [infsep_singleton, pair_eq_singleton, edist_self, ennreal.zero_to_real] },
  { rw [infsep, einfsep_pair hxy] }
end

end pseudo_emetric_space

section pseudo_metric_space

variables [pseudo_metric_space α] {x y z: α} {s t : set α}

lemma nontrivial.le_infsep_iff {d} (hs : s.nontrivial) :
  d ≤ s.infsep ↔ ∀ (x y ∈ s) (hxy : x ≠ y), d ≤ dist x y :=
by simp_rw [infsep, ← ennreal.of_real_le_iff_le_to_real (hs.einfsep_ne_top), le_einfsep_iff,
            edist_dist, ennreal.of_real_le_of_real_iff (dist_nonneg)]

lemma nontrivial.infsep_lt_iff {d} (hs : s.nontrivial) :
  s.infsep < d ↔ ∃ (x y ∈ s) (hxy : x ≠ y), dist x y < d :=
by { rw ← not_iff_not, push_neg, exact hs.le_infsep_iff }

lemma nontrivial.le_infsep {d} (hs : s.nontrivial) (h : ∀ (x y ∈ s) (hxy : x ≠ y), d ≤ dist x y) :
  d ≤ s.infsep := hs.le_infsep_iff.2 h

lemma le_edist_of_le_infsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s)
  (hxy : x ≠ y) (hd : d ≤ s.infsep) : d ≤ dist x y :=
begin
  by_cases hs : s.nontrivial,
  { exact hs.le_infsep_iff.1 hd x hx y hy hxy },
  { rw not_nontrivial_iff at hs,
    rw hs.infsep_zero at hd,
    exact le_trans hd dist_nonneg }
end

lemma infsep_le_dist_of_mem (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.infsep ≤ dist x y :=
le_edist_of_le_infsep hx hy hxy le_rfl

lemma infsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
  (hxy' : dist x y ≤ d) : s.infsep ≤ d := le_trans (infsep_le_dist_of_mem hx hy hxy) hxy'

lemma infsep_pair : ({x, y} : set α).infsep = dist x y :=
by { rw [infsep_pair_eq_to_real, edist_dist], exact ennreal.to_real_of_real (dist_nonneg) }

lemma infsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
  ({x, y, z} : set α).infsep = dist x y ⊓ dist x z ⊓ dist y z :=
by simp only [infsep, einfsep_triple hxy hyz hxz, ennreal.to_real_inf, edist_ne_top x y,
             edist_ne_top x z, edist_ne_top y z, dist_edist, ne.def, inf_eq_top_iff,
             and_self, not_false_iff]


lemma nontrivial.infsep_anti (hs : s.nontrivial) (hst : s ⊆ t) : t.infsep ≤ s.infsep :=
ennreal.to_real_mono hs.einfsep_ne_top (einfsep_anti hst)

lemma infsep_eq_infi [decidable s.nontrivial] :
  s.infsep = if s.nontrivial then ⨅ d : s.off_diag, (uncurry dist) (d : α × α) else 0 :=
begin
  split_ifs with hs,
  { have hb : bdd_below (uncurry dist '' s.off_diag),
    { refine ⟨0, λ d h, _⟩,
      simp_rw [mem_image, prod.exists, uncurry_apply_pair] at h,
      rcases h with ⟨_, _, _, rfl⟩,
      exact dist_nonneg },
    refine eq_of_forall_le_iff (λ _, _),
    simp_rw [hs.le_infsep_iff, le_cinfi_set_iff (off_diag_nonempty.mpr hs) hb, imp_forall_iff,
            mem_off_diag, prod.forall, uncurry_apply_pair, and_imp] },
  { exact ((not_nontrivial_iff).mp hs).infsep_zero }
end

lemma nontrivial.infsep_eq_infi (hs : s.nontrivial)
  : s.infsep = ⨅ d : s.off_diag, (uncurry dist) (d : α × α) :=
by { classical, rw [infsep_eq_infi, if_pos hs] }

lemma infsep_of_fintype [decidable s.nontrivial] [decidable_eq α] [fintype s] :
  s.infsep = if hs : s.nontrivial then s.off_diag.to_finset.inf' (by simpa) (uncurry dist) else 0 :=
begin
  split_ifs with hs,
  { refine eq_of_forall_le_iff (λ _, _),
    simp_rw [hs.le_infsep_iff, imp_forall_iff, finset.le_inf'_iff, mem_to_finset, mem_off_diag,
             prod.forall, uncurry_apply_pair, and_imp] },
  { rw not_nontrivial_iff at hs, exact hs.infsep_zero }
end

lemma nontrivial.infsep_of_fintype [decidable_eq α] [fintype s] (hs : s.nontrivial) :
  s.infsep = s.off_diag.to_finset.inf' (by simpa) (uncurry dist) :=
by { classical, rw [infsep_of_fintype, dif_pos hs] }

lemma finite.infsep [decidable s.nontrivial] (hsf : s.finite) :
  s.infsep = if hs : s.nontrivial then hsf.off_diag.to_finset.inf' (by simpa) (uncurry dist)
  else 0 :=
begin
  split_ifs with hs,
  { refine eq_of_forall_le_iff (λ _, _),
    simp_rw [hs.le_infsep_iff, imp_forall_iff, finset.le_inf'_iff, finite.mem_to_finset,
            mem_off_diag, prod.forall, uncurry_apply_pair, and_imp] },
  { rw not_nontrivial_iff at hs, exact hs.infsep_zero }
end

lemma finite.infsep_of_nontrivial (hsf : s.finite) (hs : s.nontrivial) :
  s.infsep = hsf.off_diag.to_finset.inf' (by simpa) (uncurry dist) :=
  by { classical, simp_rw [hsf.infsep, dif_pos hs] }

lemma _root_.finset.coe_infsep [decidable_eq α] (s : finset α) :
  (s : set α).infsep = if hs : s.off_diag.nonempty then s.off_diag.inf' hs (uncurry dist)
                         else 0 :=
begin
  have H : (s : set α).nontrivial ↔ s.off_diag.nonempty,
  by rwa [← set.off_diag_nonempty, ← finset.coe_off_diag, finset.coe_nonempty],
  split_ifs with hs,
  { simp_rw [(H.mpr hs).infsep_of_fintype, ← finset.coe_off_diag, finset.to_finset_coe] },
  { exact ((not_nontrivial_iff).mp (H.mp.mt hs)).infsep_zero }
end

lemma _root_.finset.coe_infsep_of_off_diag_nonempty [decidable_eq α] {s : finset α}
  (hs : s.off_diag.nonempty) : (s : set α).infsep = s.off_diag.inf' hs (uncurry dist) :=
by rw [finset.coe_infsep, dif_pos hs]

lemma _root_.finset.coe_infsep_of_off_diag_empty [decidable_eq α] {s : finset α}
  (hs : s.off_diag = ∅) : (s : set α).infsep = 0 :=
by { rw ← finset.not_nonempty_iff_eq_empty at hs, rw [finset.coe_infsep, dif_neg hs] }

lemma nontrivial.infsep_exists_of_finite [finite s] (hs : s.nontrivial) :
  ∃ (x y ∈ s) (hxy : x ≠ y), s.infsep = dist x y :=
begin
  classical,
  casesI nonempty_fintype s,
  simp_rw hs.infsep_of_fintype,
  rcases @finset.exists_mem_eq_inf' _ _ _ (s.off_diag.to_finset) (by simpa) (uncurry dist)
    with ⟨_, hxy, hed⟩,
  simp_rw mem_to_finset at hxy,
  exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩
end

lemma finite.infsep_exists_of_nontrivial (hsf : s.finite) (hs : s.nontrivial) :
  ∃ (x y ∈ s) (hxy : x ≠ y), s.infsep = dist x y :=
by { letI := hsf.fintype, exact hs.infsep_exists_of_finite }

end pseudo_metric_space

section metric_space
variables [metric_space α] {s : set α}

lemma infsep_zero_iff_subsingleton_of_finite [finite s] :
  s.infsep = 0 ↔ s.subsingleton :=
begin
  rw [infsep_zero, einfsep_eq_top_iff, or_iff_right_iff_imp],
  exact λ H, (einfsep_pos_of_finite.ne' H).elim
end

lemma infsep_pos_iff_nontrivial_of_finite [finite s] :
  0 < s.infsep ↔ s.nontrivial :=
begin
  rw [infsep_pos, einfsep_lt_top_iff, and_iff_right_iff_imp],
  exact λ _, einfsep_pos_of_finite
end

lemma finite.infsep_zero_iff_subsingleton (hs : s.finite) :
  s.infsep = 0 ↔ s.subsingleton :=
by { letI := hs.fintype, exact infsep_zero_iff_subsingleton_of_finite }

lemma finite.infsep_pos_iff_nontrivial (hs : s.finite) :
  0 < s.infsep ↔ s.nontrivial :=
by { letI := hs.fintype, exact infsep_pos_iff_nontrivial_of_finite }

lemma _root_.finset.infsep_zero_iff_subsingleton (s : finset α) :
  (s : set α).infsep = 0 ↔ (s : set α).subsingleton := infsep_zero_iff_subsingleton_of_finite

lemma _root_.finset.infsep_pos_iff_nontrivial (s : finset α) :
  0 < (s : set α).infsep ↔ (s : set α).nontrivial := infsep_pos_iff_nontrivial_of_finite

end metric_space

end infsep

end set
