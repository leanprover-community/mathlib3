import to_mathlib.data.nat.choose.multinomial
import ring_theory.polynomial.vieta

variables {β γ : Type*}

open finset polynomial
open_locale big_operators

lemma finset.prod_one_add_le_one_add_sum_sum_pow [strict_ordered_comm_semiring γ]
  (s : finset β) {f : β → γ} (hf : ∀ b ∈ s, 0 ≤ f b) :
  ∏ (a : β) in s, (1 + f a) ≤ ∑ n in range (s.card + 1), (s.sum f) ^ n :=
begin
  have : ∏ (a : β) in s, (1 + f a) = eval 1 ((s.val.map f).map (λ r, X + C r)).prod,
  { rw [multiset.map_map, ←finset.prod],
    simp only [eval_prod, eval_add, eval_X, eval_C]},
  rw [this, multiset.prod_X_add_C_eq_sum_esymm, eval_finset_sum],
  simp only [←finset.card_def, multiset.card_map, eval_mul, eval_C, eval_pow, eval_X, one_pow,
             mul_one],
  refine sum_le_sum _,
  simp only [finset.esymm_map_val, mem_range, npow_eq_pow],
  intros,
  classical,
  rw [sum_pow, ←sum_filter_add_sum_filter_not _ (λ t : sym β i, multiset.nodup t.val)],
  refine le_add_of_le_of_nonneg _ (sum_nonneg _),
  { have : ∑ (x : sym β i) in filter (λ (t : sym β i), t.val.nodup) (s.sym i),
      (multiset.map f x.val).prod ≤ ∑ (x : sym β i) in filter (λ (t : sym β i), t.val.nodup)
        (s.sym i), ↑(x.val.multinomial) * (multiset.map f x.val).prod,
    { refine sum_le_sum _,
      simp only [subtype.val_eq_coe, mem_filter, mem_sym_iff, and_imp],
      intros j hs hj,
      have jpos : (1 : γ) ≤ (j : multiset β).multinomial,
      { rw [nat.one_le_cast],
        exact nat.succ_le_of_lt (multiset.multinomial_pos (j : multiset β)) },
      refine le_mul_of_le_mul_of_nonneg_right _ jpos (multiset.prod_nonneg (λ x hx, _)),
      { rw one_mul },
      { simp only [multiset.mem_map, sym.mem_coe] at hx,
        obtain ⟨y, hy, rfl⟩ := hx,
        exact hf _ (hs _ hy) } },
    refine this.trans' (le_of_eq _),
    rw powerset_len_eq_filter,
    refine sum_bij _ _ _ _ _,
    { intros t ht,
      exact ⟨t.val, (mem_filter.mp ht).right⟩ },
    { simp only [mem_filter, mem_powerset, mem_sym_iff, sym.mem_mk, mem_val, and_imp],
      intros t ht hcard,
      exact ⟨λ x hx, ht hx, t.nodup⟩ },
    { simp [finset.prod] },
    { simp },
    { simp only [mem_filter, mem_powerset, subtype.val_eq_coe, mem_sym_iff, and_imp],
      intros t ht htn,
      exact ⟨⟨_, htn⟩, ⟨ht, t.prop⟩, (subtype.coe_eta _ _).symm⟩ } },
  { simp only [subtype.val_eq_coe, mem_filter, mem_sym_iff, and_imp],
    intros j hs hj,
    refine mul_nonneg (nat.cast_nonneg _) (multiset.prod_nonneg _),
    simp only [multiset.mem_map, sym.mem_coe, forall_exists_index, and_imp,
               forall_apply_eq_imp_iff₂],
    exact (λ _ hb, hf _ (hs _ hb)) }
end
