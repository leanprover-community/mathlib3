import data.list.nodup_equiv_fin
import data.fintype.basic

namespace list

variable {α : Type*}

@[simp] lemma card_attach [decidable_eq α] (l : list α) :
  fintype.card {x // x ∈ l} = finset.card l.to_finset :=
begin
  rw fintype.card_of_subtype,
  simp
end

lemma card_attach_le [decidable_eq α] (l : list α) :
  fintype.card {x // x ∈ l} ≤ l.length :=
by simpa using to_finset_card_le l

lemma nodup_iff_card_eq_length [decidable_eq α] {l : list α} :
  nodup l ↔ fintype.card {x // x ∈ l} = l.length :=
begin
  classical,
  induction l with hd tl IH,
  { simp },
  { simp only [mem_cons_iff, length, nodup_cons],
    by_cases h : hd ∈ tl,
    { simp only [h, false_iff, not_true, false_and],
      refine (((eq.le _).trans tl.card_attach_le).trans_lt (nat.lt_succ_self _)).ne,
      convert fintype.card_congr _,
      refine (equiv.subtype_equiv_right (λ x, _)).symm,
      refine (or_iff_right_of_imp _).symm,
      rintro rfl,
      exact h },
    { rw [fintype.card_subtype_or_disjoint, add_comm, IH],
      { simp only [h, true_and, add_left_inj, fintype.card_subtype_eq, list.card_attach,
                   not_false_iff],
        convert iff.rfl },
      { rintros x ⟨hx, hx'⟩,
        apply h,
        simpa [hx] using hx' } } }
end

lemma nodup_of_embedding (l : list α) (f : fin l.length ↪ {x // x ∈ l}) :
  nodup l :=
begin
  classical,
  rw list.nodup_iff_card_eq_length,
  refine le_antisymm l.card_attach_le _,
  { rw ←fintype.card_fin l.length,
    exact fintype.card_le_of_embedding f }
end

def perm_perm [decidable_eq α] (l : list α) (hn : nodup l) :
  {l' : list α // l ~ l'} ≃ equiv.perm (fin l.length) :=
{ to_fun := λ l',
    (nodup.nth_le_equiv l hn).trans $
    equiv.trans (equiv.subtype_equiv_right (λ x, l'.prop.mem_iff)) $
    (nodup.nth_le_equiv (l' : list α) (l'.prop.nodup_iff.mp hn)).symm.trans
    (fin.cast l'.prop.length_eq.symm).to_equiv,
  inv_fun := λ f,
    ⟨l.pmap (λ x hx, l.nth_le (f.symm ⟨index_of x l, index_of_lt_length.mpr hx⟩) (fin.is_lt _))
      (λ x hx, hx),
      by { refine (perm_ext hn _).mpr _,
        { refine nodup_pmap (λ x hx y hy h, _) hn,
          rw nodup_iff_nth_le_inj at hn,
          simpa [←fin.ext_iff, ←index_of_inj hx hy] using hn _ _ _ _ h },
        { simp only [mem_pmap],
          intro x,
          split,
          { intro hx,
            refine ⟨l.nth_le (f ⟨index_of x l, index_of_lt_length.mpr hx⟩) (fin.is_lt _),
              nth_le_mem _ _ _, _⟩,
            simp [nth_le_index_of hn] },
          { rintro ⟨x, hx, rfl⟩,
            exact nth_le_mem _ _ _ } } }⟩,
  left_inv := λ l', by {
    cases l' with l' hl,
    simp only [index_of_nth_le, equiv.coe_fn_mk, subtype.coe_mk, fin.coe_mk, mem_pmap,
               subtype.val_eq_coe, nth_le, nth_le_index_of],
    apply ext_le,
    { simpa using hl.length_eq },
    { simp [nth_le_pmap, nth_le_index_of hn] } },
  right_inv := λ f, by {
    ext ⟨n, h⟩,
    have : (pmap (λ (x : α) (hx : x ∈ l), l.nth_le ((equiv.symm f)
      ⟨index_of x l, index_of_lt_length.mpr hx⟩) (fin.is_lt _)) l (λ x hx, hx)).nodup,
    { refine nodup_pmap (λ x hx y hy hxy, _) hn,
      rw nodup_iff_nth_le_inj at hn,
      simpa [←fin.ext_iff, ←index_of_inj hx hy] using hn _ _ _ _ hxy },
    simp [this, fin.is_lt, nth_le_pmap, nth_le_index_of hn] } }

@[simp] lemma perm_perm_self [decidable_eq α] (l : list α) (h : nodup l) :
  perm_perm l h ⟨l, perm.refl _⟩ = equiv.refl _ :=
begin
  ext,
  simp [perm_perm, nth_le_index_of h]
end

lemma nodup_permutations (l : list α) (h : nodup l) :
  nodup (permutations l) :=
begin
  classical,
  refine list.nodup_of_embedding _ _,
  refine (equiv.trans _ ((equiv.subtype_equiv_right _).trans (perm_perm l h)).symm).to_embedding,
  { refine fintype.equiv_of_card_eq _,
    simpa [fintype.card_perm] using length_permutations _ },
  { intro l',
    rw mem_permutations,
    exact ⟨perm.symm, perm.symm⟩ }
end

end list
