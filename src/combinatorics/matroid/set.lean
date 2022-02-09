
import tactic
import .num_lemmas
import data.set.basic

open_locale classical
noncomputable theory

universes u v w

open finset

namespace set

section basic

variables {α β : Type*} {s s' t t' r r': set α}



/-
Phased out lemmas and definitions:
  * `subset_iff_inter_eq_left`
  * `pairwise_disjoint` definition changed?
    - had `hdj : pairwise_disjoint S` before, can't do it now
    - might need extra bit of information?
  * `set.infinite_mono`
-/

@[simp] lemma absorb_union_inter (s t : set α) : s ∪ (s ∩ t) = s :=
by calc s ∪ (s ∩ t) = (s ∩ univ) ∪ (s ∩ t) : by rw inter_univ
                ... = s : by rw [←inter_distrib_left, union_comm, union_univ, inter_univ ]

@[simp] lemma absorb_inter_union (s t : set α) : s ∩ (s ∪ t) = s :=
by {rw [inter_comm, union_inter_cancel_left], }

lemma inter_distrib_inter_left (s t r : set α) : (s ∩ t) ∩ r = (s ∩ r) ∩ (t ∩ r) :=
by rw [inter_assoc s r, inter_comm r, inter_assoc t, inter_self, inter_assoc]

lemma union_distrib_union_left (s t r : set α) : (s ∪ t) ∪ r = (s ∪ r) ∪ (t ∪ r) :=
by rw [union_assoc s r, union_comm r, union_assoc t, union_self, union_assoc]

lemma union_distrib_union_right (s t r : set α) : s ∪ (t ∪ r) = (s ∪ t) ∪ (s ∪ r) :=
by rw [union_comm s, union_distrib_union_left t r s, union_comm s, union_comm s]

@[simp] lemma inter_right_self (s t : set α) : s ∩ t ∩ t = s ∩ t :=
by rw [inter_assoc, inter_self]

@[simp] lemma union_right_self (s t : set α) : s ∪ t ∪ t = s ∪ t :=
by rw [union_assoc, union_self]

-- lemma subset_iff_inter_eq_left

lemma subset_iff_union_eq_left : (s ⊆ t) ↔ (s ∪ t = t) :=
begin
  rw ← compl_subset_compl,

  sorry,
end
--rw [←compl_subset_compl, subset_iff_inter_eq_left, ←compl_union,
 --           compl_inj_iff, union_comm t s]

lemma subset_iff_union_eq_right : (t ⊆ s) ↔ (s ∪ t = s) :=
by rw [subset_iff_union_eq_left, union_comm]

lemma subset_refl (s : set α) : s ⊆ s :=
by sorry

-- rw [subset_iff_inter_eq_left, inter_self]

lemma subset_ssubset_or_eq : (s ⊆ t) → (s ⊂ t) ∨ s = t :=
λ hst, by {rw or_comm, apply eq_or_ssubset_of_subset hst}

lemma subset_iff_ssubset_or_eq : (s ⊆ t) ↔ (s ⊂ t) ∨ s = t :=
⟨λ h, subset_ssubset_or_eq h, λ h, by {cases h, from h.1, rw h}⟩

lemma ssubset_iff_subset_not_supset : s ⊂ t ↔ s ⊆ t ∧ ¬(t ⊆ s) :=
iff.rfl

lemma ssubset_of_subset_ne : s ⊆ t → s ≠ t → s ⊂ t :=
@lt_of_le_of_ne _ _ s t

lemma ne_of_ssubset : s ⊂ t → s ≠ t :=
ne_of_irrefl

lemma ssubset_irrefl (s : set α) : ¬(s ⊂ s) :=
λ h, by { sorry }--rw ssubset_iff_subset_ne at h, from h.2 rfl}

lemma univ_subset  (hs : univ ⊆ s) : s = univ :=
subset.antisymm (subset_univ s) hs

instance subset_subtype_nonempty : nonempty {t : set α // t ⊆ s} :=
by {apply nonempty_subtype.mpr, from ⟨_,empty_subset _⟩,  }

instance subtype_coe : has_coe {t : set α // t ⊆ s} (set α) := coe_subtype

lemma subset_empty : s ⊆ ∅ → s = ∅ :=
λ hs, subset.antisymm hs (empty_subset s)

lemma ssubset_empty (s : set α) : ¬ s ⊂ ∅ :=
λ h, by { sorry } -- rw ssubset_iff_subset_ne at h, from h.2 (subset_empty h.1)}

lemma empty_of_subset_compl (h : s ⊆ sᶜ) : s = ∅ :=
by sorry --rwa [subset_iff_inter_eq_left, inter_compl_self, eq_comm] at h

lemma disjoint_compl_subset (h : s ∩ t = ∅) : s ⊆ tᶜ :=
by sorry
/-rw [subset_iff_inter_eq_left, ← empty_union (s ∩ tᶜ), ←h,
            ←inter_distrib_left, union_compl_self, inter_univ]-/

lemma subset_compl_disjoint (h : s ⊆ tᶜ) : s ∩ t = ∅ :=
by sorry -- {rw subset_iff_inter_eq_left at h, rw [←h, inter_assoc], simp}

lemma disjoint_iff_subset_compl : s ∩ t = ∅ ↔ s ⊆ tᶜ :=
⟨λ h, disjoint_compl_subset h, λ h, subset_compl_disjoint h⟩

lemma disjoint_iff_inter_compl_eq_left : s ∩ t = ∅ ↔ s ∩ tᶜ = s :=
by sorry --rw [disjoint_iff_subset_compl, subset_iff_inter_eq_left]

lemma disjoint_iff_inter_compl_eq_right : s ∩ t = ∅ ↔ sᶜ ∩ t = t :=
by rw [inter_comm, disjoint_iff_inter_compl_eq_left, inter_comm]

lemma disjoint_iff_diff_eq_left : s ∩ t = ∅ ↔ s \ t = s :=
disjoint_iff_inter_compl_eq_left

lemma subset_iff_diff_empty (s t : set α) : s ⊆ t ↔ s \ t = ∅ :=
by {rw [←compl_compl t, ←disjoint_iff_subset_compl], simp [diff_eq],}

lemma subset_iff_partition (s t : set α) : s ⊆ t ↔ t = s ∪ (t \ s) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { nth_rewrite 0 ←(subset_iff_union_eq_left.mp h),
    rw [diff_eq, union_distrib_left], simp,},
  rw h, simp,
end

lemma subset_iff_disjoint_compl : s ⊆ t ↔ s ∩ tᶜ = ∅ :=
by rw [subset_iff_diff_empty, diff_eq]

lemma disjoint_of_subset_left' (hst : s ⊆ t) (htr : t ∩ r = ∅) : s ∩ r = ∅ :=
by {rw ←disjoint_iff_inter_eq_empty at *, exact disjoint_of_subset_left hst htr}

lemma disjoint_of_subset_right' (hst : s ⊆ t) (hrt : r ∩ t = ∅) : r ∩ s = ∅ :=
by {rw ←disjoint_iff_inter_eq_empty at *, exact disjoint_of_subset_right hst hrt, }

lemma disjoint_of_subsets (hss' : s ⊆ s') (htt' : t ⊆ t') (hst : s' ∩ t' = ∅) :
  s ∩ t = ∅ :=
by {rw ←disjoint_iff_inter_eq_empty at *, exact disjoint_of_subset hss' htt' hst, }

lemma cover_compl_subset :  s ∪ t = univ → sᶜ ⊆ t :=
λ h, by rw [subset_iff_union_eq_left, ←univ_inter (sᶜ ∪ t), ←h,
              ←union_distrib_right, inter_compl_self, empty_union]

lemma compl_inj (h : sᶜ = tᶜ) : s = t :=
by rw [←compl_compl s, ←compl_compl t, h]

lemma compl_compl_inter_left (s t : set α) : (sᶜ ∩ t)ᶜ = s ∪ tᶜ :=
by {nth_rewrite 0 ←(compl_compl t), rw [compl_inter, compl_compl, compl_compl] }

lemma compl_compl_inter_right (s t : set α) : (s ∩ tᶜ)ᶜ = sᶜ ∪ t :=
by {nth_rewrite 0 ←(compl_compl s), rw [compl_inter, compl_compl, compl_compl] }

lemma compl_compl_union_left (s t : set α) : (sᶜ ∪ t)ᶜ = s ∩ tᶜ :=
by {nth_rewrite 0 ←(compl_compl t), rw [compl_union, compl_compl, compl_compl] }

lemma compl_compl_union_right (s t : set α) : (s ∪ tᶜ)ᶜ = sᶜ ∩ t :=
by {nth_rewrite 0 ←(compl_compl s), rw [compl_union, compl_compl, compl_compl] }


lemma compl_partition (s t : set α) : (s ∩ t) ∪ (sᶜ ∩ t) = t :=
by rw [←inter_distrib_right, union_compl_self, univ_inter]

lemma compl_partition_subset  (hst : s ⊆ t) : s ∪ (sᶜ ∩ t) = t :=
by sorry -- {nth_rewrite 0 ←(subset_iff_inter_eq_left.mp hst), exact compl_partition s t}

lemma compl_pair (h : sᶜ = t) : (s = tᶜ) :=
by rw [←h, compl_compl]

lemma compl_pair_iff : (sᶜ = t) ↔ (s = tᶜ) :=
⟨λ h, compl_pair h, λ h, by {rw eq_comm at h, from (compl_pair h).symm}⟩

lemma compl_diff (s t : set α) : (s \ t)ᶜ = sᶜ ∪ t :=
by rw [diff_eq, compl_inter, compl_compl]

@[simp] lemma union_union_compl_self (s t : set α) : (s ∪ t) ∪ tᶜ = univ :=
by rw [union_assoc, union_compl_self, union_univ]

@[simp] lemma inter_inter_compl_self (s t : set α) : (s ∩ t) ∩ tᶜ = ∅ :=
by rw [inter_assoc, inter_compl_self, inter_empty]

@[simp] lemma union_union_compl_right (s t : set α) : s ∪ (t ∪ sᶜ) = univ :=
by rw [←union_assoc, union_comm s, union_union_compl_self]

@[simp] lemma inter_inter_compl_right (s t : set α) : s ∩ (t ∩ sᶜ) = ∅ :=
by rw [←inter_assoc, inter_comm s, inter_inter_compl_self]

lemma inter_union_compl_self (s t : set α) : s ∩ (t ∪ tᶜ) = s :=
by rw [union_compl_self, inter_univ]

lemma subset_own_compl : s ⊆ sᶜ → s = ∅ :=
  λ h, by {rw [subset_iff_union_eq_left,union_compl_self, ←compl_empty, compl_inj_iff] at h,
                rw ←h }

lemma inter_subset_union (s t : set α) : s ∩ t ⊆ s ∪ t :=
  subset.trans (inter_subset_left s t) (subset_union_left s t)

lemma subset_of_inter_mp : s ⊆ t ∩ r → s ⊆ t ∧ s ⊆ r :=
  λ h, ⟨subset.trans h (inter_subset_left _ _), subset.trans h (inter_subset_right _ _)⟩

lemma subset_of_set_and_compl : s ⊆ t → s ⊆ tᶜ → s = ∅ :=
  λ h1 h2, by {have := subset_inter h1 h2, rw inter_compl_self at this,
  exact subset_empty this}

@[trans] lemma subset.lt_of_le_of_lt (_ : s ⊆ t) (_ : t ⊂ r) : s ⊂ r :=
lt_of_le_of_lt ‹s ≤ t› ‹t < r›

@[trans] lemma subset.lt_of_lt_of_le (_ : s ⊂ t) (_ : t ⊆ r) : s ⊂ r :=
lt_of_lt_of_le ‹s < t› ‹t ≤ r›

lemma ssubset_not_supset (h : s ⊂ t) : ¬(t ⊆ s) :=
λ h', ssubset_irrefl _ (subset.lt_of_lt_of_le h h')

lemma subset_not_ssupset (h: s ⊆ t) : ¬(t ⊂ s) :=
λ h', ssubset_irrefl _ (subset.lt_of_le_of_lt h h')

lemma eq_of_subset_not_ssubset  : s ⊆ t → ¬(s ⊂ t) → s = t :=
λ h h', by {simp only [not_and, not_not, set.ssubset_iff_subset_ne] at h', exact h' h}

@[trans] lemma ssubset.trans {s t r : set α} : s ⊂ t → t ⊂ r → s ⊂ r :=
λ hst htr, subset.lt_of_le_of_lt hst.1 htr

lemma ssubset_inter : s ≠ t → s ∩ t ⊂ s ∨ s ∩ t ⊂ t :=
begin
  intro h,
  by_contra a, push_neg at a, simp_rw [set.ssubset_iff_subset_ne, not_and', not_imp_not] at a,
  exact h (eq.trans (a.1 (inter_subset_left s t)).symm (a.2 (inter_subset_right s t)) ),
end

lemma union_union_diff (s t r : set α) : (s ∪ r) ∪ (t \ r) = s ∪ t ∪ r :=
by {rw [diff_eq, union_distrib_left, union_right_comm, union_assoc _ r], simp,}

lemma union_diff_absorb (s t : set α) : s ∪ (t \ s) = s ∪ t :=
by {nth_rewrite 0 ←union_self s, rw [union_union_diff, union_right_comm, union_self]}

@[simp] lemma union_union_inter_compl_self (s t r : set α) : (s ∪ r) ∪ (t ∩ rᶜ) = s ∪ t ∪ r :=
by rw [←diff_eq, union_union_diff]

lemma union_inter_diff (s t r : set α) : (s ∪ r) ∩ (t \ r) = (s ∩ t) \ r :=
by {rw [diff_eq, diff_eq, inter_distrib_right], simp [←inter_assoc, inter_right_comm r t rᶜ] }

lemma subset_of_subset_diff (h : s ⊆ t \ r) : s ⊆ t :=
λ x hx, by {have := h hx, rw mem_diff at this, exact this.1,  }

lemma eq_of_union_eq_inter : s ∪ t = s ∩ t → s = t :=
begin
  intro h, apply subset.antisymm,
  calc s ⊆ (s ∪ t) : subset_union_left _ _ ... = s ∩ t : h ... ⊆ t : inter_subset_right _ _,
  calc t ⊆ (s ∪ t) : subset_union_right _ _ ... = s ∩ t : h ... ⊆ s : inter_subset_left _ _,
end

lemma union_of_disjoint : s ∩ t = ∅ → s ∩ r = ∅ → s ∩ (t ∪ r) = ∅ :=
  λ ht hr, by {rw [inter_distrib_left, ht, hr], simp }

@[simp] lemma diff_union (s t : set α) : (s ∩ t) ∪ (s \ t) = s :=
by rw [diff_eq, ←inter_distrib_left, union_compl_self, inter_univ]

@[simp] lemma inter_diff (s t : set α) : s ∩ (t \ s)  = ∅ :=
by rw [diff_eq, ←inter_assoc, inter_right_comm, inter_compl_self, empty_inter]

@[simp] lemma partition_inter (s t : set α) : (s ∩ t) ∩ (s \ t) = ∅ :=
by rw [inter_assoc, inter_diff, inter_empty]

@[simp] lemma inter_diffs_eq_empty (s t : set α) : (s \ t) ∩ (t \ s) = ∅ :=
by {simp only [diff_eq], rw [inter_assoc, ←inter_assoc tᶜ], simp}

lemma pair_move {s r : set α} (t : set α) (hst : r ⊆ s) : (s \ r) ∪ (t ∪ r) = s ∪ t :=
by {ext, simp, tauto, }

lemma diff_empty_subset (s t : set α) : s \ t = ∅ → s ⊆ t :=
λ hst, by {rw [←diff_union s t, hst, union_empty], apply inter_subset_right}

lemma subset_diff_empty (s t : set α) : s ⊆ t → s \ t = ∅ :=
λ hst, by sorry /-{rw diff_eq, rw subset_iff_inter_eq_left at hst,
           rw [←hst, inter_assoc, inter_compl_self, inter_empty]}-/

lemma diff_empty_iff_subset (s t : set α) : s \ t = ∅ ↔ s ⊆ t :=
by {split, apply diff_empty_subset, apply subset_diff_empty}

lemma subset_diff_disjoint (s t r : set α) : s ⊆ t → s ∩ r = ∅ → s ⊆ t \ r :=
λ hst hsr, by sorry /-{rw [disjoint_iff_subset_compl, subset_iff_inter_eq_left] at hsr,
                rw [diff_eq, subset_iff_inter_eq_left, inter_comm t, ←inter_assoc, hsr,
                      subset_iff_inter_eq_left.mp hst], }-/

lemma ssubset_diff_nonempty : s ⊂ t → (t \ s).nonempty :=
λ hst, set.nonempty_of_ssubset hst

lemma union_diff_of_subset  : s ⊆ t → s ∪ (t \ s) = t :=
λ h, by sorry -- {rw [subset_iff_inter_eq_left, inter_comm] at h, have := diff_union t s, rwa h at this}

lemma diff_eq_self_of_subset_diff (h : s ⊆ r \ t) : s \ t = s :=
by {rw [←disjoint_iff_diff_eq_left, disjoint_iff_subset_compl],
        refine subset.trans h _, simp [diff_eq],  }

@[simp] lemma diff_inter_right_eq_empty (s t : set α) : (t \ s) ∩ s = ∅ :=
by rw [inter_comm, inter_diff]

@[simp] lemma union_diff (s t : set α) : s ∪ (t \ s) = s ∪ t :=
by {rw [diff_eq, union_distrib_left, union_compl_self, inter_univ]}

@[simp] lemma union_diff_diff (s t : set α) : (s ∪ t) \ (t \ s) = s :=
by rw [diff_eq, diff_eq, compl_inter,compl_compl,union_comm,
          ←union_distrib_right, inter_compl_self, empty_union]

lemma diff_self_diff (s t : set α) : s \ (s \ t) = s ∩ t :=
by rw [diff_eq, compl_diff, inter_distrib_left, inter_compl_self, empty_union]

lemma inter_distrib_diff (s t r : set α) : s ∩ (t \ r) = (s ∩ t) \ (s ∩ r) :=
by {rw [diff_eq, diff_eq, compl_inter, inter_distrib_left, inter_right_comm,
                        inter_compl_self, empty_inter, empty_union, ←inter_assoc]}

lemma diff_inter_diff_right (s t r : set α) : (s \ r) ∩ (t \ r) = (s ∩ t) \ r :=
by {ext, tidy,  }

lemma diff_right_comm (s t r : set α) : s \ t \ r = s \ r \ t :=
by simp [diff_eq, inter_right_comm]



@[simp] lemma univ_diff (s : set α) : univ \ s = sᶜ :=
  (compl_eq_univ_diff s).symm

lemma empty_ssubset_nonempty : s.nonempty → ∅ ⊂ s :=
λ h, by {rw ←set.ne_empty_iff_nonempty at h,
          exact ssubset_of_subset_ne (empty_subset s) (ne.symm h)}

lemma nonempty_iff_empty_subset: s.nonempty ↔ ∅ ⊂ s :=
⟨ λ h, empty_ssubset_nonempty h,
  λ h, by {rw ←set.ne_empty_iff_nonempty, exact (ne_of_ssubset h).symm, }⟩

lemma ssubset_compl_commpl.mpr : s ⊂ t → tᶜ ⊂ sᶜ :=
λ h, ssubset_of_subset_ne (compl_subset_compl.mpr h.1)
      (λ h', by {rw (compl_inj h') at h, from ssubset_irrefl _ h})

lemma compl_to_ssubset : sᶜ ⊂ tᶜ → t ⊂ s :=
λ h, by {have := ssubset_compl_commpl.mpr h, repeat {rw compl_compl at this}, exact this }

lemma compl_ssubset_compl_iff : sᶜ ⊂ tᶜ ↔ t ⊂ s :=
by tidy

lemma ssubset_compl_comm : s ⊂ tᶜ ↔ t ⊂ sᶜ :=
by {convert compl_ssubset_compl_iff, rw compl_compl}

lemma compl_ssubset_comm : sᶜ ⊂ t ↔ tᶜ ⊂ s :=
by {convert @compl_ssubset_compl_iff _ s tᶜ, rw compl_compl}

--lemma ssubset_compl_iff_compl_ssubset : s ⊂ tᶜ ↔ sᶜ ⊂ t :=
--by {nth_rewrite 0 ← compl_compl s, rw compl_ssubset_compl_iff,  }

lemma ssubset_univ_of_ne_univ: s ≠ univ → s ⊂ univ :=
λ h, ssubset_of_subset_ne (subset_univ _) h

-- don't know what's going on with S's here, we had `hdj : pairwise_disjoint S`
lemma pairwise_disjoint_inter_sUnion {S S₁ S₂: set (set α)}
(hdj : pairwise_disjoint S) (h₁ : S₁ ⊆ S) (h₂ : S₂ ⊆ S) :
  sUnion (S₁ ∩ S₂) = sUnion S₁ ∩ sUnion S₂ :=
begin
  ext, simp only [mem_inter_iff, mem_sUnion], split,
  { rintros ⟨t,hT,hxt⟩,
  rw ← mem_inter_iff at hT,
  refine ⟨⟨t,hT.1,hxt⟩,⟨t,hT.2,hxt⟩⟩, },
  rintros ⟨⟨t,h,hxt⟩,⟨t',h',hxt'⟩⟩,
  have := (pairwise_disjoint.elim hdj
    (mem_of_mem_of_subset h h₁)
    ((mem_of_mem_of_subset h' h₂)) x hxt hxt'),
  subst this, use t, tidy,
end

lemma infinite_of_finite_diff (hs : s.finite) (ht : t.infinite) :
  (t \ s).infinite :=
λ h, ht (by {refine (hs.union h).subset _, rw set.union_diff_self, apply set.subset_union_right, })

lemma infinite_of_union (hs : s.infinite) (t : set α) :
  (s ∪ t).infinite :=
begin

  sorry,
end
--set.infinite_mono (set.subset_union_left _ _) hs

lemma finite.diff (hs : s.finite) (t : set α) : (s \ t).finite :=
  set.finite.subset hs (set.diff_subset _ _)

lemma finite.inter_left (hs : s.finite) (t : set α) : (s ∩ t).finite :=
  set.finite.subset hs (set.inter_subset_left _ _)

lemma finite.inter_right (ht : t.finite) (s : set α ) : (s ∩ t).finite :=
  set.finite.subset ht (set.inter_subset_right _ _)



lemma subset_insert_iff_subset_or_eq_insert {s t : set α} {a : α}:
  s ⊆ insert a t ↔ (s ⊆ t) ∨ ∃ s' ⊆ t, s = insert a s' :=
begin
  refine ⟨λ h, _, _⟩,
  by_cases ha : a ∈ s,
  { refine or.inr ⟨s \ {a}, λ x, _, _⟩,
    {specialize @h x, tidy, tauto, },
    simp [set.insert_eq_of_mem ha]},
  refine or.inl (λ x hx, _),
  specialize h hx,
  rw set.mem_insert_iff at h,
  rcases h with (rfl | h),
    exact false.elim (ha hx),
    assumption,
  rintros (hst | ⟨s', hs't, rfl⟩),
  { exact subset.trans hst (set.subset_insert _ _)},
  exact set.insert_subset_insert hs't,
end

lemma insert_inj_subset_iff {s t t' : set α} {a : α} (ht : t ⊆ s) (ht' : t' ⊆ s) (hat : a ∉ s ):
  insert a t = insert a t' ↔ t = t' :=
begin
  refine ⟨λ h, _, by {rintro rfl, refl}⟩,
  simp_rw [ext_iff, mem_insert_iff] at h,
  ext x,
  specialize h x, split,
  { intro h',
    obtain (rfl | hx) := h.mp (or.intro_right _ h'),
      exact false.elim (hat (mem_of_mem_of_subset h' ht)),
    assumption, },
  { intro h',
    obtain (rfl | hx) := h.mpr (or.intro_right _ h'),
      exact false.elim (hat (mem_of_mem_of_subset h' ht')),
    assumption, },
end

lemma remove_insert (s : set α) (e : α) :
  insert e (s \ {e})  = insert e s :=
by rw [← union_singleton, diff_union_self, union_singleton]

lemma finite.iff_of_bij_on {s : set α} {t : set β} {f : α → β} (h : bij_on f s t) :
  s.finite ↔ t.finite :=
begin
  refine ⟨λ hs, _, λ ht, _⟩,
  { convert finite.image f hs, rw h.image_eq},
  apply finite_of_finite_image h.inj_on, rwa h.image_eq,
end


end basic


section symm_diff

variables {α : Type*}
/-- the symmetric difference of two sets -/
def symm_diff (s t : set α) : set α := (s \ t) ∪ (t \ s)

lemma symm_diff_assoc (s t r : set α) :
  (s.symm_diff t).symm_diff r = s.symm_diff (t.symm_diff r) :=
by {ext, simp [symm_diff], tauto}


@[simp] lemma symm_diff_self (s : set α): s.symm_diff s = ∅ := by simp [symm_diff]

@[simp] lemma symm_diff_univ (s : set α) : s.symm_diff univ = sᶜ := by simp [symm_diff]

@[simp] lemma symm_diff_empty (s : set α) : s.symm_diff ∅ = s := by simp [symm_diff]

lemma symm_diff_comm (s t : set α) : symm_diff s t = symm_diff t s :=
by {ext, simp [symm_diff], tauto}

lemma symm_diff_alt (s t : set α) : symm_diff s t = (s ∪ t) \ (s ∩ t) :=
by {ext, simp only [symm_diff, mem_inter_eq, mem_union_eq, not_and, mem_diff], tauto}

@[simp] lemma symm_diff_self_right (s t : set α) : (s.symm_diff t).symm_diff t = s :=
by simp [symm_diff_assoc]

lemma symm_diff_eq_iff {s t r: set α} :
  s.symm_diff t = r ↔ s = t.symm_diff r :=
begin
  split, {rintro rfl, rw symm_diff_comm, simp, },
  rintro rfl, simp [symm_diff_comm t],
end

lemma symm_diff_subset_union (s t : set α) : s.symm_diff t ⊆ s ∪ t :=
by {rw symm_diff_alt, apply diff_subset}

lemma diff_subset_symm_diff (s t : set α) : s \ t ⊆ s.symm_diff t :=
λ x hx, by {rw symm_diff_alt, simp at ⊢ hx, tauto}

lemma symm_diff_singleton_mem_eq {s : set α} {x : α} (h : x ∈ s) :
  s.symm_diff {x} = s \ {x} :=
begin
  ext,
  simp only [symm_diff,and_imp, mem_singleton_iff, mem_union_eq, or_iff_left_iff_imp, mem_diff],
  rintros rfl h',
  exact false.elim (h' h),
end

lemma symm_diff_singleton_nonmem_eq {s : set α} {x : α} (h : x ∉ s) :
  s.symm_diff {x} = insert x s :=
begin
  ext y,
  simp only [symm_diff, mem_singleton_iff, mem_union_eq, mem_insert_iff, mem_diff],
  rcases em (y = x) with (rfl | _); tauto,
end

@[simp] lemma symm_diff_eq_self_iff {s t : set α } :
  s.symm_diff t = s ↔ t = ∅ :=
⟨λ h, by rwa [symm_diff_comm, symm_diff_eq_iff, symm_diff_self] at h, by {rintro rfl, simp}⟩

end symm_diff

end set
section sigma

variables {α : Type*} {β : α → Type*}

/-- the set of all pairs `(x,y)` where `x ∈ s` and `y ∈ β x` -/
def set.sigma (s : set α) (t : Π (a : α), set (β a)) : set (sigma β) :=
  set_of (λ x : sigma β, x.1 ∈ s ∧ x.2 ∈ t x.1)

def set.sigma_swap {α β : Type*}: (Σ (a : α), β) → (Σ (b : β), α) :=
  λ p, ⟨p.2, p.1⟩

lemma set.sigma_inter_sigma (s s' : set α) (t t' : Π (a : α), set (β a)) :
  (s.sigma t) ∩ (s'.sigma t') = (s ∩ s').sigma (λ a, (t a) ∩ (t' a)) :=
by {ext, simp [set.sigma], tauto}

lemma set.sigma_inter (s : set α) (t : Π (a : α), set (β a)) (r : set (sigma β)) :
  (s.sigma t) ∩ r = s.sigma (λ a, (t a) ∩ { b ∈ t a | (⟨a,b⟩ : sigma β) ∈ r}) :=
by {ext, simp [set.sigma], tauto}


lemma set.sigma_singleton_eq  (a : α) (t : Π (a : α), set (β a)) :
  ({a} : set α).sigma t = sigma.mk a '' t a :=
begin
  ext x,
  simp only [set.sigma, set.mem_image, set.mem_singleton_iff, set.mem_set_of_eq],
  split,
  { cases x, dsimp only at *,  rintro ⟨rfl, h⟩, exact ⟨_, h, rfl⟩},
  rintro ⟨b, hb, rfl⟩,
  exact ⟨rfl, hb⟩,
end

lemma set.sigma_finite_iff {s : set α} {t : Π a, set (β a)}:
  (s.sigma t).finite ↔ {a ∈ s | (t a).nonempty}.finite ∧ ∀ a ∈ s, (t a).finite :=
begin
  refine ⟨λ hf, ⟨_, λ a ha, _⟩, λ h, _⟩,
  { convert set.finite.image (λ (p : sigma β), p.1) hf,
    ext p,
    simp [set.sigma, set.nonempty_def]},

  { refine @set.finite_of_finite_image _ _ _
      (λ x, (⟨a, x⟩ : sigma β))
      _
      (set.finite.subset hf _),
    { intros x hx y hy hxy, simpa using hxy},
    simp only [set.image_subset_iff],
    exact λ x hx, ⟨ha, hx⟩},
  convert @set.finite.bUnion _ _ _ (λ a _, ({a} : set α).sigma t) h.1 _,
  { ext,
    simp only [set.nonempty_def, exists_prop, set.mem_Union, set.mem_sep_eq,
     set.mem_singleton_iff, set.mem_set_of_eq, set.sigma],
    refine ⟨λ h, ⟨x.1, ⟨⟨h.1, _, h.2⟩, rfl , h.2⟩⟩, λ h, _⟩,
    obtain ⟨a, ⟨has, b, hba⟩, ⟨rfl, ha'⟩⟩ := h,
    exact ⟨has, ha'⟩},
  intros a ha,
  simp only,
  convert set.finite.image (λ (b : β a), (⟨a,b⟩ : sigma β)) (h.2 a ha.1),
  rw set.sigma_singleton_eq,
end


lemma set.sigma_to_finset {s : set α} {t : Π a, set (β a)}
(h : (s.sigma t).finite) :
  h.to_finset = finset.sigma (set.sigma_finite_iff.mp h).1.to_finset
                (λ a : α, dite (a ∈ s) (λ ha, ((set.sigma_finite_iff.mp h).2 a ha).to_finset)
                                       (λ _, finset.empty)) :=
begin
  ext x,
  simp only [set.mem_sep_eq, set.finite.mem_to_finset, finset.mem_sigma, set.nonempty_def],
  split_ifs with h h',
  { simp only [set.finite.mem_to_finset, set.sigma, set.mem_set_of_eq], cases x, tauto},
  rw [set.sigma, set.mem_set_of_eq],
  exact ⟨λ h₁, false.elim (h h₁.1), λ h₁, false.elim (finset.not_mem_empty _ h₁.2)⟩,
end

lemma set.sigma_eq_univ_sigma (s : set α) (t : Π a, set (β a) ):
  s.sigma t = (set.univ : set α).sigma (λ a, ite (a ∈ s) (t a) ∅) :=
begin
  ext x, cases x with a b,
  simp only [set.sigma, true_and, set.mem_univ, set.mem_set_of_eq],
  split_ifs;
  tauto,
end


lemma set.sigma_univ_invert {α β : Type*} (t : α → set β) :
  set.bij_on (set.sigma_swap)
    ((set.univ : set α).sigma t)
    ((set.univ : set β).sigma (λ b, {a : α | b ∈ t a}) ):=
begin
  refine ⟨ λ x hx, _, λ x hx y hy hxy , _, λ x hx, _⟩,
  { rw [set.sigma] at *, simpa using hx},
  { cases x, cases y, simp only [heq_iff_eq, set.sigma_swap] at ⊢ hxy, rwa and_comm,},
  simp only [set.mem_image, sigma.exists],
  rw [set.sigma] at hx ⊢,
  simp only [true_and, set.mem_univ, set.mem_set_of_eq] at hx ⊢,
  exact ⟨x.2, x.1, hx, by {simp only [sigma.eta, set.sigma_swap], }⟩,
end

lemma set.sigma_invert {α β : Type*} (s : set α) (t : α → set β) :
  set.bij_on (set.sigma_swap)
    (s.sigma t)
    ((set.univ : set β).sigma (λ b, {a ∈ s | b ∈ t a}) ) :=
begin
  rw set.sigma_eq_univ_sigma,
  convert set.sigma_univ_invert _ using 1,
  ext x, repeat {rw set.sigma},
  cases x,
  simp only [true_and, set.mem_sep_eq, set.mem_univ, set.mem_set_of_eq],
  split_ifs;
  tauto,
end

end sigma
