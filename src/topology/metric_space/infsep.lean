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

open_locale ennreal

lemma finset.off_diag_nonempty_iff [decidable_eq α] {s : finset α} :
  (s : set α).nontrivial ↔ s.off_diag.nonempty :=
by simp_rw [set.nontrivial, finset.nonempty, finset.mem_off_diag, finset.mem_coe,
            prod.exists, exists_and_distrib_left, exists_prop]

lemma set.nontrivial_iff_to_finset_off_diag_nonempty [decidable_eq α] {s : set α} [fintype s]
  : s.to_finset.off_diag.nonempty ↔ s.nontrivial :=
by simp_rw [set.nontrivial, finset.nonempty, finset.mem_off_diag, set.mem_to_finset,
           prod.exists, exists_and_distrib_left, exists_prop]

lemma set.nontrivial.to_finset_off_diag_nonempty [decidable_eq α] {s : set α}
  [fintype s] (hs : s.nontrivial) : s.to_finset.off_diag.nonempty :=
set.nontrivial_iff_to_finset_off_diag_nonempty.mpr hs

lemma set.finite.nontrivial_iff_to_finset_off_diag_nonempty [decidable_eq α] {s : set α}
  (hs : s.finite) : hs.to_finset.off_diag.nonempty ↔ s.nontrivial :=
by { letI := hs.fintype, exact set.nontrivial_iff_to_finset_off_diag_nonempty }

lemma set.finite.to_finset_off_diag_nonempty_of_nontrivial [decidable_eq α] {s : set α}
  (hsf : s.finite) (hs : s.nontrivial) : hsf.to_finset.off_diag.nonempty :=
hsf.nontrivial_iff_to_finset_off_diag_nonempty.mpr hs

end extras

namespace set

section infesep
open_locale ennreal
open function

/-- The "extended infimum separation" of a set with an edist function. -/
noncomputable def infesep [has_edist α] (s : set α) : ℝ≥0∞ :=
⨅ (x ∈ s) (y ∈ s) (hxy : x ≠ y), edist x y

section has_edist
variables [has_edist α] {x y : α} {s t : set α}

theorem infesep_zero :
  s.infesep = 0 ↔ ∀ C (hC : 0 < C), ∃ (x y ∈ s) (hxy : x ≠ y), edist x y < C :=
by simp_rw [infesep, ← bot_eq_zero, infi_eq_bot, infi_lt_iff]

theorem infesep_pos :
  0 < s.infesep ↔ ∃ C (hC : 0 < C), ∀ (x y ∈ s) (hxy : x ≠ y), C ≤ edist x y :=
by { rw [pos_iff_ne_zero, ne.def, infesep_zero], simp only [not_forall, not_exists, not_lt] }

lemma infesep_top : s.infesep = ∞ ↔ ∀ (x y ∈ s) (hxy : x ≠ y), edist x y = ∞ :=
by simp_rw [infesep, infi_eq_top]

lemma infesep_lt_top : s.infesep < ∞ ↔ ∃ (x y ∈ s) (hxy : x ≠ y), edist x y < ∞ :=
by simp_rw [infesep, infi_lt_iff]

lemma infesep_ne_top : s.infesep ≠ ∞ ↔ ∃ (x y ∈ s) (hxy : x ≠ y), edist x y ≠ ∞ :=
by simp_rw [←lt_top_iff_ne_top, infesep_lt_top]

lemma le_infesep_iff {d} : d ≤ s.infesep ↔ ∀ (x y ∈ s) (hxy : x ≠ y), d ≤ edist x y :=
by simp_rw [infesep, le_infi_iff]

lemma infesep_lt_iff {d} : s.infesep < d ↔ ∃ (x y ∈ s) (h : x ≠ y), edist x y < d :=
by simp_rw [infesep, infi_lt_iff]

lemma nontrivial_of_infesep_lt_top (hs : s.infesep < ∞) : s.nontrivial :=
by { rcases infesep_lt_top.1 hs with ⟨_, hx, _, hy, hxy, _⟩, exact ⟨_, hx, _, hy, hxy⟩ }

lemma nontrivial_of_infesep_ne_top (hs : s.infesep ≠ ∞) : s.nontrivial :=
nontrivial_of_infesep_lt_top (lt_top_iff_ne_top.mpr hs)

lemma subsingleton.infesep (hs : s.subsingleton) : s.infesep = ∞ :=
by { rw infesep_top, exact λ _ hx _ hy hxy, (hxy $ hs hx hy).elim }

lemma le_infesep_image_iff {d} {f : β → α} {s : set β} :
  d ≤ infesep (f '' s) ↔ ∀ x y ∈ s, f x ≠ f y → d ≤ edist (f x) (f y) :=
by simp_rw [le_infesep_iff, ball_image_iff]

lemma le_edist_of_le_infesep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
  (hd : d ≤ s.infesep) : d ≤ edist x y := le_infesep_iff.1 hd x hx y hy hxy

lemma infesep_le_edist_of_mem {x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y) :
  s.infesep ≤ edist x y := le_edist_of_le_infesep hx hy hxy le_rfl

lemma infesep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
  (hxy' : edist x y ≤ d) : s.infesep ≤ d := le_trans (infesep_le_edist_of_mem hx hy hxy) hxy'

lemma le_infesep {d} (h : ∀ (x y ∈ s) (hxy : x ≠ y), d ≤ edist x y) :
  d ≤ s.infesep := le_infesep_iff.2 h

@[simp] lemma infesep_empty : (∅ : set α).infesep = ∞ := subsingleton_empty.infesep

@[simp] lemma infesep_singleton : ({x} : set α).infesep = ∞ := subsingleton_singleton.infesep

lemma infesep_Union_mem_option {ι : Type*} (o : option ι) (s : ι → set α) :
  (⋃ i ∈ o, s i).infesep = ⨅ i ∈ o, (s i).infesep := by cases o; simp

lemma infesep_anti (hst : s ⊆ t) : t.infesep ≤ s.infesep :=
le_infesep $ λ x hx y hy, infesep_le_edist_of_mem (hst hx) (hst hy)

lemma infesep_insert_le : (insert x s).infesep ≤ ⨅ (y ∈ s) (hxy : x ≠ y), edist x y :=
begin
  simp_rw le_infi_iff,
  refine λ _ hy hxy, infesep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ hy) hxy
end

lemma le_infesep_pair : edist x y ⊓ edist y x ≤ ({x, y} : set α).infesep :=
begin
  simp_rw [le_infesep_iff, inf_le_iff, mem_insert_iff, mem_singleton_iff],
  rintros a (rfl | rfl) b (rfl | rfl) hab; finish
end

lemma infesep_pair_le_left (hxy : x ≠ y) : ({x, y} : set α).infesep ≤ edist x y :=
infesep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hxy

lemma infesep_pair_le_right (hxy : x ≠ y) : ({x, y} : set α).infesep ≤ edist y x :=
by rw pair_comm; exact infesep_pair_le_left hxy.symm

lemma infesep_pair_eq_inf (hxy : x ≠ y) : ({x, y} : set α).infesep = (edist x y) ⊓ (edist y x) :=
le_antisymm (le_inf (infesep_pair_le_left hxy) (infesep_pair_le_right hxy)) le_infesep_pair

lemma infesep_of_fintype [decidable_eq α] [fintype s] :
  s.infesep = s.to_finset.off_diag.inf (uncurry edist) :=
begin
  refine eq_of_forall_le_iff _,
  simp_rw [le_infesep_iff, finset.le_inf_iff, finset.mem_off_diag, ne.def, mem_to_finset,
           and_imp, prod.forall, uncurry_apply_pair, imp_forall_iff, iff_self, forall_const]
end

lemma infesep_finset [decidable_eq α] {s : finset α} :
  (s : set α).infesep = s.off_diag.inf (uncurry edist) :=
by rw [infesep_of_fintype, finset.to_finset_coe]

lemma finite.infesep [decidable_eq α] (hs : s.finite) :
  s.infesep = hs.to_finset.off_diag.inf (uncurry edist) :=
by { letI := hs.fintype, exact infesep_of_fintype }

lemma nontrivial.infesep_exists_of_finite [finite s] (hs : s.nontrivial) :
∃ (x y ∈ s) (hxy : x ≠ y), s.infesep = edist x y :=
begin
  classical,
  casesI nonempty_fintype s,
  simp_rw infesep_of_fintype,
  rcases finset.exists_mem_eq_inf _ (hs.to_finset_off_diag_nonempty) (uncurry edist)
    with ⟨_, hxy, hed⟩,
  simp_rw [finset.mem_off_diag, mem_to_finset] at hxy,
  exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩
end

lemma finite.infesep_exists_of_nontrivial (hsf : s.finite) (hs : s.nontrivial) :
∃ (x y ∈ s) (hxy : x ≠ y), s.infesep = edist x y :=
by { letI := hsf.fintype, exact hs.infesep_exists_of_finite }

end has_edist

section pseudo_emetric_space
variables [pseudo_emetric_space α] {x y z : α} {s t : set α}

lemma infesep_pair (hxy : x ≠ y) : ({x, y} : set α).infesep = edist x y :=
begin
  nth_rewrite 0 [← min_self (edist x y)],
  convert infesep_pair_eq_inf hxy using 2,
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
  infesep ({x, y, z} : set α) = edist x y ⊓ edist x z ⊓ edist y z :=
by simp_rw [infesep_insert, infi_insert, infi_singleton, infesep_singleton,
            inf_top_eq, cinfi_pos hxy, cinfi_pos hyz, cinfi_pos hxz]

lemma infesep_pi_le_of_le {π : β → Type*} [fintype β] [∀ b, pseudo_emetric_space (π b)]
  {s : Π (b : β), set (π b)} {c : ℝ≥0∞} (h : ∀ b, c ≤ infesep (s b) ) :
  c ≤ infesep (set.pi univ s) :=
begin
  refine le_infesep (λ x hx y hy hxy, _),
  rw mem_univ_pi at hx hy,
  rcases function.ne_iff.mp hxy with ⟨i, hi⟩,
  exact le_trans (le_infesep_iff.1 (h i) _ (hx _) _ (hy _) hi) (edist_le_pi_edist _ _ i)
end

end pseudo_emetric_space

section pseudo_metric_space
variables [pseudo_metric_space α] {s : set α}

theorem subsingleton_of_infesep_eq_top (hs : s.infesep = ∞) : s.subsingleton :=
begin
  rw infesep_top at hs,
  exact λ _ hx _ hy, of_not_not (λ hxy, edist_ne_top _ _ (hs _ hx _ hy hxy))
end

theorem infesep_eq_top_iff : s.infesep = ∞ ↔ s.subsingleton :=
⟨subsingleton_of_infesep_eq_top, subsingleton.infesep⟩

theorem nontrivial.infesep_ne_top (hs : s.nontrivial) : s.infesep ≠ ∞ :=
by { contrapose! hs, rw not_nontrivial_iff, exact subsingleton_of_infesep_eq_top hs }

theorem nontrivial.infesep_lt_top (hs : s.nontrivial) : s.infesep < ∞ :=
by { rw lt_top_iff_ne_top, exact hs.infesep_ne_top }

theorem infesep_lt_top_iff : s.infesep < ∞ ↔ s.nontrivial :=
⟨nontrivial_of_infesep_lt_top, nontrivial.infesep_lt_top⟩

theorem infesep_ne_top_iff : s.infesep ≠ ∞ ↔ s.nontrivial :=
⟨nontrivial_of_infesep_ne_top, nontrivial.infesep_ne_top⟩

lemma le_infesep_of_forall_dist_le {d} (h : ∀ (x y ∈ s) (hxy : x ≠ y), d ≤ dist x y) :
   ennreal.of_real d ≤ s.infesep :=
le_infesep $
λ x hx y hy hxy, (edist_dist x y).symm ▸ ennreal.of_real_le_of_real (h x hx y hy hxy)

end pseudo_metric_space

section emetric_space
variables [emetric_space α] {x y z : α} {s t : set α} {C : ℝ≥0∞} {sC : set ℝ≥0∞}

lemma infesep_pos_of_finite [finite s] : 0 < s.infesep :=
begin
  classical,
  casesI nonempty_fintype s,
  by_cases hs : s.nontrivial,
  { rcases hs.infesep_exists_of_finite with ⟨x, hx, y, hy, hxy, hxy'⟩,
    exact hxy'.symm ▸ edist_pos.2 hxy },
  { rw not_nontrivial_iff at hs,
    exact hs.infesep.symm ▸ with_top.zero_lt_top }
end

lemma relatively_discrete_of_finite [finite s] :
  ∃ C (hC : 0 < C), ∀ (x y ∈ s) (hxy : x ≠ y), C ≤ edist x y :=
by { rw ← infesep_pos, exact infesep_pos_of_finite }

lemma finite.infesep_pos (hs : s.finite) : 0 < s.infesep  :=
by { letI := hs.fintype, exact infesep_pos_of_finite }

lemma finite.relatively_discrete (hs : s.finite) :
  ∃ C (hC : 0 < C), ∀ (x y ∈ s) (hxy : x ≠ y), C ≤ edist x y :=
by { letI := hs.fintype, exact relatively_discrete_of_finite }

end emetric_space

end infesep

section infsep
open_locale ennreal
open set function

/-- The "infimum separation" of a set with an edist function. -/
noncomputable def infsep [has_edist α] (s : set α) : ℝ := ennreal.to_real (s.infesep)

section has_edist
variables [has_edist α] {x y : α} {s : set α}

lemma infsep_zero : s.infsep = 0 ↔ s.infesep = 0 ∨ s.infesep = ∞ :=
by rw [infsep, ennreal.to_real_eq_zero_iff]

lemma infsep_nonneg : 0 ≤ s.infsep := ennreal.to_real_nonneg

lemma infsep_pos : 0 < s.infsep ↔ 0 < s.infesep ∧ s.infesep < ∞ :=
by simp_rw [infsep, ennreal.to_real_pos_iff]

lemma subsingleton.infsep (hs : s.subsingleton) : s.infsep = 0 :=
by { rw [infsep_zero, hs.infesep], right, refl }

lemma nontrivial_of_infsep_pos (hs : 0 < s.infsep) : s.nontrivial :=
by { contrapose hs, rw not_nontrivial_iff at hs, exact hs.infsep ▸ lt_irrefl _ }

lemma infsep_empty : (∅ : set α).infsep = 0 :=
subsingleton_empty.infsep

lemma infsep_singleton : ({x} : set α).infsep = 0 :=
subsingleton_singleton.infsep

lemma infsep_pair_eq_inf_to_real (hxy : x ≠ y) :
  ({x, y} : set α).infsep ≤ (edist x y ⊓ edist y x).to_real :=
by simp_rw [infsep, infesep_pair_eq_inf hxy]

end has_edist

section pseudo_emetric_space
variables [pseudo_emetric_space α] {x y : α} {s : set α}

lemma infsep_pair_eq_to_real : ({x, y} : set α).infsep = (edist x y).to_real :=
begin
  by_cases hxy : x = y,
  { rw hxy, simp only [infsep_singleton, pair_eq_singleton, edist_self, ennreal.zero_to_real] },
  { rw [infsep, infesep_pair hxy] }
end

end pseudo_emetric_space

section pseudo_metric_space
open_locale classical
variables [pseudo_metric_space α] {x y z: α} {s t : set α}

lemma nontrivial.le_infsep_iff {d} (hs : s.nontrivial) :
d ≤ s.infsep ↔ ∀ (x y ∈ s) (hxy : x ≠ y), d ≤ dist x y :=
by simp_rw [infsep, ← ennreal.of_real_le_iff_le_to_real (hs.infesep_ne_top), le_infesep_iff,
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
    rw hs.infsep at hd,
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
by simp only [infsep, infesep_triple hxy hyz hxz, ennreal.to_real_inf, edist_ne_top x y,
             edist_ne_top x z, edist_ne_top y z, dist_edist, ne.def, inf_eq_top_iff,
             and_self, not_false_iff]


lemma nontrivial.infsep_anti (hs : s.nontrivial) (hst : s ⊆ t) : t.infsep ≤ s.infsep :=
ennreal.to_real_mono hs.infesep_ne_top (infesep_anti hst)

lemma infsep_of_fintype [decidable_eq α] [fintype s] :
  s.infsep =  if hs : s.nontrivial
              then s.to_finset.off_diag.inf' hs.to_finset_off_diag_nonempty (uncurry dist)
              else 0 :=
begin
  split_ifs with hs,
  { refine eq_of_forall_le_iff _,
   simp_rw [hs.le_infsep_iff, finset.le_inf'_iff, finset.mem_off_diag, ne.def, mem_to_finset,
           and_imp, prod.forall, uncurry_apply_pair, imp_forall_iff, iff_self, forall_const] },
  { rw not_nontrivial_iff at hs, exact hs.infsep }
end

lemma nontrivial.infsep_of_fintype [decidable_eq α] [fintype s] (hs : s.nontrivial) :
  s.infsep = s.to_finset.off_diag.inf' hs.to_finset_off_diag_nonempty (uncurry dist) :=
by rw [infsep_of_fintype, dif_pos hs]

lemma finite.infsep [decidable_eq α] (hsf : s.finite) :
  s.infsep = if hs : s.nontrivial
             then hsf.to_finset.off_diag.inf' (hsf.to_finset_off_diag_nonempty_of_nontrivial hs)
                  (uncurry dist)
             else 0 := by { letI := hsf.fintype, exact infsep_of_fintype }

lemma finite.infsep_of_nontrivial [decidable_eq α] (hsf : s.finite) (hs : s.nontrivial) :
  s.infsep = hsf.to_finset.off_diag.inf' (hsf.to_finset_off_diag_nonempty_of_nontrivial hs)
  (uncurry dist) := by { letI := hsf.fintype, exact hs.infsep_of_fintype }

lemma infsep_finset [decidable_eq α] {s : finset α}
  : (s : set α).infsep = if hs : s.off_diag.nonempty
                         then s.off_diag.inf' hs (uncurry dist)
                         else 0 :=
begin
  split_ifs with hs,
  { have hs₂ : (s : set α).nontrivial,
    { rcases hs with ⟨⟨x, y⟩, H⟩, rw finset.mem_off_diag at H, exact ⟨x, H.1, y, H.2.1, H.2.2⟩ },
    rw hs₂.infsep_of_fintype, simp_rw finset.to_finset_coe },
  { have hs₂ : (s : set α).subsingleton,
    { simp_rw [set.subsingleton, finset.mem_coe, imp_forall_iff],
      simp_rw [finset.not_nonempty_iff_eq_empty, finset.ext_iff, finset.mem_off_diag,
             finset.not_mem_empty, iff_false, not_and, not_not, prod.forall] at hs,
      exact hs },
    exact hs₂.infsep }
end

lemma infsep_finset_of_off_diag.nonempty [decidable_eq α] {s : finset α} (hs : s.off_diag.nonempty)
  : (s : set α).infsep = s.off_diag.inf' hs (uncurry dist) :=
by rw [infsep_finset, dif_pos hs]

lemma nontrivial.infsep_exists_of_finite [finite s] (hs : s.nontrivial) :
∃ (x y ∈ s) (hxy : x ≠ y), s.infsep = dist x y :=
begin
  classical,
  casesI nonempty_fintype s,
  simp_rw hs.infsep_of_fintype,
  rcases finset.exists_mem_eq_inf' (hs.to_finset_off_diag_nonempty) (uncurry dist)
    with ⟨_, hxy, hed⟩,
  simp_rw [finset.mem_off_diag, mem_to_finset] at hxy,
  exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩
end

lemma finite.infsep_exists_of_nontrivial (hsf : s.finite) (hs : s.nontrivial) :
∃ (x y ∈ s) (hxy : x ≠ y), s.infsep = dist x y :=
by { letI := hsf.fintype, exact hs.infsep_exists_of_finite }

end pseudo_metric_space

section metric_space
variables [metric_space α] {x y z: α} {s t : set α}

lemma infsep_zero_iff_subsingleton_of_finite [finite s] :
  s.infsep = 0 ↔ s.subsingleton :=
begin
  rw [infsep_zero, infesep_eq_top_iff, or_iff_right_iff_imp],
  exact λ H, (infesep_pos_of_finite.ne' H).elim
end

lemma infsep_pos_iff_nontrivial_of_finite [finite s] :
  0 < s.infsep ↔ s.nontrivial :=
begin
  rw [infsep_pos, infesep_lt_top_iff, and_iff_right_iff_imp],
  exact λ _, infesep_pos_of_finite
end

end metric_space

end infsep

end set
