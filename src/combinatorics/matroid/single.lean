import .set
-- Singles

open set

universes u v w

open_locale classical
variables {α : Type*}

/-
Phased out lemmas and definitions:
  * `subset_iff_inter_eq_left`
-/

lemma mem_coe_inj_iff {e f : α} :
  ({e} : set α) = ({f}  : set α) ↔ e = f :=
by {exact singleton_eq_singleton_iff}

lemma singleton_nonmem_iff {e : α} {X : set α} :
  e ∉ X ↔ ¬({e} : set α) ⊆ X :=
by rw [not_iff_not, singleton_subset_iff]

lemma singleton_ne_empty (e : α) :
  ({e} : set α) ≠ ∅ :=
λ h, by {rw set.ext_iff at h, exact not_mem_empty e ((h e).mp (by simp))}

@[simp] lemma singleton_nonmem_compl_self (e : α) :
  e ∉ ({e} : set α)ᶜ :=
λ h, by {rw ←singleton_subset_iff at h, from singleton_ne_empty e (subset_own_compl h)}

lemma subset_of_mem_of_subset {e : α} {X Y : set α} (h : e ∈ X) (h' : X ⊆ Y) :
  {e} ⊆ Y :=
singleton_subset_iff.mpr (mem_of_mem_of_subset h h')

lemma union_subset_of_mem_of_mem {e f : α} {X : set α} :
  e ∈ X → f ∈ X → ({e} ∪ {f} : set α) ⊆ X :=
λ he hf, by {refine union_subset _ _, tidy}

lemma union_singleton_subset_of_subset_mem {X Y : set α} {e : α} :
  X ⊆ Y → e ∈ Y → X ∪ {e} ⊆ Y :=
by {rw ←singleton_subset_iff, apply union_subset }

lemma ne_empty_has_mem {X : set α}  :
  X ≠ ∅ → ∃ e, e ∈ X :=
by {rw [ne_empty_iff_nonempty, nonempty_def], from id}

lemma ne_empty_iff_has_mem {X : set α} :
  X ≠ ∅ ↔ ∃ e, e ∈ X :=
⟨λ h, ne_empty_has_mem h, λ h, λ hb, by {cases h with e he, rw hb at he, exact not_mem_empty e he}⟩

lemma ne_univ_iff_has_nonmem {X : set α} :
  X ≠ univ ↔ ∃ e, e ∉ X :=
by {rw [←not_forall, not_iff_not], refine ⟨λ h x, _, λ h, _⟩, rw h, from mem_univ x, ext, tidy}

lemma nested_singletons_eq {e f: α} (hef : ({e} : set α) ⊆ ({f} : set α)) :
   e = f :=
by rwa [singleton_subset_iff, mem_singleton_iff] at hef

lemma nonmem_disjoint {e : α} {X : set α} :
  e ∉ X → ({e} ∩ X : set α) = ∅ :=
by tidy

@[simp] lemma set.sep_eq_empty_iff {P : α → Prop} :
  {x | P x} = ∅ ↔ ∀ x, ¬P x :=
by {rw ext_iff, simp, }

@[simp] lemma set.sep_in_eq_empty_iff {P : α → Prop} {X : set α} :
  {x ∈ X | P x} = ∅ ↔ ∀ x ∈ X, ¬P x :=
by {rw ext_iff, simp, }

lemma set.empty_iff_has_no_mem {X : set α} :
  X = ∅ ↔ ∀ x, x ∉ X :=
by {split, rintro rfl, simp, intro h, ext, simp, exact h x,   }

lemma nonmem_disjoint_iff {e : α} {X : set α} :
  e ∉ X ↔ {e} ∩ X = ∅ :=
by {refine ⟨λ h, nonmem_disjoint h, λ h he, _⟩, sorry}
  /- rw [←singleton_subset_iff, subset_iff_inter_eq_left,h] at he,
  exact singleton_ne_empty e he.symm,}-/

lemma inter_distinct_singles {e f : α} :
  e ≠ f → ({e} ∩ {f} : set α) = ∅ :=
λ hef, nonmem_disjoint (λ h, hef (nested_singletons_eq (singleton_subset_iff.mpr h)))

lemma mem_union_of_mem_left {e : α} {X : set α} (Y : set α) (h : e ∈ X) :
  e ∈ X ∪ Y :=
mem_of_mem_of_subset h (subset_union_left X Y)

lemma mem_union_of_mem_right {e : α} {X : set α} (Y : set α) (h : e ∈ Y) :
  e ∈ X ∪ Y :=
mem_of_mem_of_subset h (subset_union_right X Y)

lemma singleton_nonmem_compl_self_iff {X : set α} {e : α} :
  e ∉ Xᶜ ↔ e ∈ X  :=
by {rw ←mem_compl_iff, rw [compl_compl]}

lemma mem_union_iff {e : α} {X Y : set α} :
  e ∈ X ∪ Y ↔ e ∈ X ∨ e ∈ Y :=
by simp only [mem_union_eq]

lemma nonmem_inter_iff {e : α} {X Y : set α} :
   e ∉ X ∩ Y ↔ e ∉ X ∨ e ∉ Y :=
by rw [←mem_compl_iff, compl_inter, mem_union_iff, mem_compl_iff, mem_compl_iff]

lemma mem_diff_iff {e : α} {X Y : set α} :
  e ∈ X \ Y ↔ e ∈ X ∧ e ∉ Y :=
by simp only [mem_diff]

lemma subset_iff_elems_contained {X Y : set α} :
  X ⊆ Y ↔ ∀ e, e ∈ X → e ∈ Y :=
by refl

lemma mem_of_subset {X Y: set α} {e : α} :
  X ⊆ Y → e ∈ X → e ∈ Y :=
λ h he, subset_iff_elems_contained.mp h e he

lemma nonmem_of_nonmem_diff {X Y : set α} {e : α} :
  e ∉ X \ Y → e ∉ Y → e ∉ X :=
by tidy

lemma nonmem_diff_of_nonmem {X : set α} (Y : set α){e : α} :
  e ∉ X → e ∉ X\Y :=
by tidy

lemma nonmem_diff_of_mem (X : set α) {Y : set α } {e : α} (h : e ∈ Y) :
  e ∉ X \ Y :=
by tidy

lemma nonmem_of_nonmem_supset {s t : set α} {e : α} :
   e ∉ t → s ⊆ t → e ∉ s :=
by tidy

lemma eq_iff_same_elems {X Y : set α} :
  X = Y ↔ ∀ e, e ∈ X ↔ e ∈ Y :=
⟨λ h e, by rw h, λ h, by {ext, from h x}⟩

lemma nonmem_removal (X : set α) (e : α) :
  e ∉ X \ {e} :=
by tidy

lemma subset_of_removal {X Y : set α} {e : α} :
  X ⊆ Y → e ∉ X → X ⊆ Y \ {e} :=
by tidy

lemma subset_of_subset_add_nonmem {X Y: set α} {e : α} :
  X ⊆ Y ∪ {e} → e ∉ X → X ⊆ Y :=
begin
  intros hXY heX,
  sorry,
  /-simp only [subset_iff_inter_eq_left] at hXY ⊢,
  rw [nonmem_disjoint_iff, inter_comm] at heX,
  rw [inter_distrib_left, heX, union_empty] at hXY,
  from hXY,-/
end

lemma removal_subset_of {X Y : set α} {e : α} :
  X ⊆ Y ∪ {e} → X \ {e} ⊆ Y :=
begin
  intro h,
  sorry,
  /-simp only [subset_iff_inter_eq_left, diff_eq] at h ⊢,
  nth_rewrite 1 ← h,
  rw [inter_distrib_left, inter_distrib_right, inter_assoc _ {e}, inter_right_comm _ _ Y],
  simp only [inter_compl_self, union_empty, inter_empty],-/
end

lemma ssub_of_add_compl {X : set α} {e : α} :
  e ∈ Xᶜ → X ⊂ X ∪ {e} :=
begin
  refine λ hXe, ssubset_of_subset_ne (subset_union_left _ _) _, intro h, rw [h, compl_union] at hXe,
  cases hXe, solve_by_elim,
end

lemma ssub_of_add_nonmem {X : set α} {e : α} :
  e ∉ X → X ⊂ X ∪ {e} :=
λ hXe, ssub_of_add_compl (by {rwa mem_compl_iff })

lemma ssubset_of_add_nonmem_iff {X : set α} {e : α} :
  e ∉ X ↔ X ⊂ X ∪ {e} :=
by {refine ⟨λ h, ssub_of_add_nonmem h, λ h, λ hex, _⟩,
    rw [←singleton_subset_iff, subset_iff_union_eq_left, union_comm] at hex,
    rw hex at h,
    exact set.ssubset_irrefl _ h}

lemma ssubset_iff_subset_mem_diff {X Y : set α}:
  X ⊂ Y ↔ (X ⊆ Y) ∧ ∃ y, y ∈ Y ∧ y ∉ X :=
begin
  rw ssubset_iff_subset_not_supset, convert iff.rfl,
  rw [← iff_iff_eq, iff_not_comm, not_exists], tidy,
end

lemma union_mem_singleton {X : set α} {e : α} :
  e ∈ X → X ∪ {e} = X :=
λ h, by {tidy,}

lemma remove_nonmem {X : set α } {e : α} (he : e ∉ X) :
  X \ {e} = X :=
by tidy

lemma mem_diff_ssubset {X Y : set α} :
  X ⊂ Y → ∃ e, e ∈ Y \ X :=
λ h, ssubset_diff_nonempty h

lemma mem_only_larger_ssubset {X Y : set α} :
  X ⊂ Y → ∃ e, e ∈ Y ∧ e ∉ X :=
λ h, by {have := mem_diff_ssubset h, simp_rw mem_diff_iff at this, assumption}

lemma nonmem_of_mem_disjoint {e : α} {X Y : set α} (he : e ∈ X) (hXY : X ∩ Y = ∅) :
  e ∉ Y :=
λ hf, by {have h := set.mem_inter he hf,  rw hXY at h, exact not_mem_empty e h,  }

lemma compl_single_remove {X : set α} {e : α} :
  e ∈ X → (X \ {e})ᶜ = Xᶜ ∪ {e} :=
λ _, by rw [diff_eq, compl_inter, compl_compl]

lemma remove_union_mem_singleton {X : set α} {e : α} :
  e ∈ X → (X \ {e}) ∪ {e} = X :=
λ heX, by {rw [←singleton_subset_iff, subset_iff_union_eq_left,union_comm] at heX,
          rw [diff_eq, union_distrib_right, compl_union_self, inter_univ, heX]}

lemma exists_mem_diff_of_finite_infinite {X Y : set α} (hX : X.finite) (hY : Y.infinite) :
  ∃ e ∈ Y, e ∉ X :=
by {by_contra hn, push_neg at hn, exact hY (hX.subset hn)}

lemma add_remove_nonmem {X : set α} {e : α} :
  e ∉ X → (X ∪ {e}) \ {e} = X :=
begin
  intro h,
  rw [←mem_compl_iff, ←singleton_subset_iff, subset_iff_union_eq_left] at h,
  rw [diff_eq, inter_distrib_right],
  simp only [inter_compl_self, union_empty],
  rw [←compl_compl_inter_left, inter_comm, compl_inj_iff] at h,
  from h,
end

lemma compl_nonempty_iff_exists_nonmem {s : set α}:
  sᶜ.nonempty ↔ ∃ x, x ∉ s :=
by tidy

lemma subset_of_remove_mem_diff {X Y: set α} {e : α} (hXY : X ⊆ Y) (he : e ∈ Y \ X) :
  X ⊆ Y \ {e} :=
begin
  intros x hx, rw [mem_diff, mem_singleton_iff] at *,
  exact ⟨mem_of_mem_of_subset hx hXY, by {rintro ⟨rfl⟩, exact he.2 hx,}⟩,
end

lemma subset_remove_nonmem_of_subset {X Y : set α} {e : α} (hXY : X ⊆ Y) (he : e ∉ X) :
  X ⊆ Y \ {e} :=
λ x hx, by {simp, refine ⟨hXY hx, λ h, _⟩, rw h at hx, exact he hx}


lemma remove_single_subset' (X : set α) (e : α) :
  X \ {e} ⊆ X :=
diff_subset X {e}

lemma nonmem_of_subset_remove_single (X : set α) (e : α) :
  X ⊆ X \ {e} → e ∉ X :=
by {rw diff_eq, tidy}

lemma ne_of_mem_diff {X : set α} {e f: α} (h : e ∈ X \ {f}) :
  e ≠ f :=
λ h', by {rw h' at h, apply nonmem_removal _ _ h,}

lemma ssubset_of_remove_mem {X : set α} {e : α} (heX : e ∈ X) :
   X \ {e} ⊂ X :=
ssubset_of_subset_ne
  (diff_subset _ _)
  (λ h, by {rw [ext_iff] at h, specialize h e, rw mem_diff at h, tauto,  })

lemma add_from_nonempty_diff {X Y : set α} :
  X ⊂ Y ↔ ∃ e : α, e ∉ X ∧ X ∪ {e} ⊆ Y :=
begin
  refine ⟨λ h,_, λ h, ssubset_of_subset_ne _ (λ hne, _)⟩,
  cases nonempty_def.mp (ssubset_diff_nonempty h) with e he,
  { rw mem_diff at he, exact ⟨e, he.2,union_subset h.1 (singleton_subset_iff.mpr he.1)⟩, },
  { rcases h with ⟨e, h, h'⟩, exact subset.trans (subset_union_left _ _) h', },
  rcases h with ⟨e, h,h'⟩,  rw ←hne at h',
  exact set.ssubset_irrefl _ (subset.lt_of_lt_of_le (ssub_of_add_nonmem h) h'),
end

lemma aug_of_ssubset {X Y : set α} :
  X ⊂ Y → ∃ Z (e : α), X ⊆ Z ∧ Z ⊂ Y ∧ Z ∪ {e} = Y :=
begin
  intro hXY,
  rcases mem_only_larger_ssubset hXY with ⟨e, ⟨heY, heX⟩⟩,
  refine ⟨Y \ {e}, e, ⟨subset_of_removal hXY.1 heX ,⟨ _, _⟩ ⟩⟩,
  from ssubset_of_remove_mem heY,
  from remove_union_mem_singleton heY,
end

lemma exchange_comm {X : set α} {e f : α} (hef : e ≠ f):
  (X \ {e}) ∪ {f} = (X ∪ {f}) \ {e} :=
begin
  ext, simp only [mem_union, mem_diff, mem_singleton_iff],
  rcases em (x = e) with (rfl | hxe); rcases em (x = f) with (rfl | hxf),
  exact false.elim (hef rfl), simpa, simpa, tauto,
end

lemma pair_eq_union (e f : α) :
  ({e,f} : set α) = {e} ∪ {f} :=
by {ext, simp, tauto, }

lemma singleton_subset_pair_left (e f : α) :
  ({e} : set α) ⊆ {e,f} :=
λ x, or.intro_left _

lemma singleton_subset_pair_right (e f : α) :
  ({f} : set α) ⊆ {e,f} :=
λ x, or.intro_right _

lemma singleton_ssubset_pair_left {e f : α} (h : e ≠ f) :
  ({e} : set α) ⊂ {e,f} :=
by {rw [pair_comm, ssubset_iff_insert], refine ⟨f,_,set.subset_refl _⟩, tauto, }

lemma singleton_ssubset_pair_right {e f : α} (h : e ≠ f) :
  ({f} : set α) ⊂ {e,f} :=
by {rw [ssubset_iff_insert], refine ⟨e,_,set.subset_refl _⟩, tauto, }

lemma union_singletons_eq_pair {e f : α} :
  ({e} : set α) ∪ ({f} : set α) = {e,f} :=
singleton_union

lemma remove_remove_single (X : set α) (e f : α) :
  X \ {e} \ {f} = X \ {e,f} :=
by rw [diff_diff, union_singletons_eq_pair]

lemma subset_singleton_eq_singleton_or_empty {e : α} {X : set α} :
  X ⊆ {e} → X = ∅ ∨ X = {e} :=
begin
  rw subset_singleton_iff,  intro h',
  by_cases h'' : e ∈ X,
  right,
  { ext, rw ←singleton_subset_iff at h'', exact ⟨λ h, h' _ h, λ h, mem_of_mem_of_subset h h''⟩, },
  left,
  ext, simp only [set.mem_empty_eq, iff_false],
  exact λ h, h'' (by rwa ←(h' _ h)),
end

lemma subset_singleton_iff_self_or_empty {e : α} {X : set α} :
  X ⊆ {e} ↔ X = ∅ ∨ X = {e} :=
begin
  refine ⟨λ h, subset_singleton_eq_singleton_or_empty h, λ h, _⟩,
  rcases h with (rfl | rfl); simp,
end

lemma ssubset_singleton_iff_empty {e : α} {X : set α} :
  X ⊂ {e} ↔ X = ∅ :=
begin
  rw [ssubset_iff_subset_ne, subset_singleton_iff_self_or_empty],
  exact ⟨λ h, by tauto, λ h, ⟨by {left, assumption}, by {rw h, apply (singleton_ne_empty e).symm}⟩⟩,
end

lemma ssubset_pair {e f : α} {X : set α} :
  X ⊂ {e,f} → X = ∅ ∨ (X = {e}) ∨ (X = {f}) :=
begin
  intro h, rw [ssubset_iff_subset_ne, ←union_singletons_eq_pair] at h,
  cases h with hs hne,
  sorry,
  /-rw [subset_iff_inter_eq_left, inter_distrib_left] at hs,
  cases subset_singleton_eq_singleton_or_empty (inter_subset_right X {e}),
  rw [h, empty_union, ←subset_iff_inter_eq_left] at hs,
  cases subset_singleton_eq_singleton_or_empty hs,
  exact or.inl h_1, apply or.inr, exact or.inr h_1,
  rw [inter_comm, ←subset_iff_inter_eq_left] at h, apply or.inr,
  cases subset_singleton_eq_singleton_or_empty (inter_subset_right X {f}),
  rw [h_1, union_empty, ←subset_iff_inter_eq_left] at hs,  exact or.inl (subset.antisymm hs h),
  rw [subset_iff_inter_eq_left, inter_comm] at h,
  rw [h_1, h] at hs, exfalso, exact hne hs.symm,-/
end

lemma pair_subset_iff {e f : α} {X : set α} :
  {e,f} ⊆ X ↔ e ∈ X ∧ f ∈ X :=
by {refine ⟨λ h, ⟨_,_⟩, λ h, λ x hx, _⟩,
  repeat {apply singleton_subset_iff.mp, apply subset.trans _ h, simp, },
  simp only [set.mem_insert_iff, set.mem_singleton_iff] at hx,
  rcases hx with (rfl | rfl); tauto,   }
