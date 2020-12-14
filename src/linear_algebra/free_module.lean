/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/
import linear_algebra.basis
import linear_algebra.finsupp_vector_space
import ring_theory.principal_ideal_domain

/-! # Free modules

A free `R`-module `M` is a module with a basis over `R`,
equivalently it is an `R`-module linearly equivalent to `ι →₀ R` for some `ι`.
-/

open_locale big_operators

section comm_ring

universes u v

variables {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
variables {ι : Type*} {b : ι → M} (hb : is_basis R b)

lemma exists_is_basis_iff_exists_equiv {ι : Type v} :
  (∃ (b : ι → M), is_basis R b) ↔ nonempty (M ≃ₗ[R] (ι →₀ R)) :=
⟨λ ⟨b, hb⟩, ⟨module_equiv_finsupp hb⟩,
 λ ⟨e⟩, ⟨_, linear_equiv.is_basis finsupp.is_basis_single_one e.symm⟩⟩


lemma not_nonempty_fin_zero : ¬ (nonempty (fin 0)) :=
λ ⟨i⟩, fin_zero_elim i

open submodule.is_principal

-- `n` is the rank of `M` and `m` is the rank of `N`; I copied this unfortunate notation from Dummit and Foote.

section

open finset submodule

lemma filter_mem_of_le [decidable_eq ι] {s t : finset ι} (hst : s ≤ t) :
  s.filter (λ i, i ∈ t) = s :=
le_antisymm (s.filter_subset _) (λ i hi, mem_filter.mpr ⟨hi, hst hi⟩)

lemma filter_mem_of_ge [decidable_eq ι] {s t : finset ι} (hst : t ≤ s) :
  s.filter (λ i, i ∈ t) = t :=
le_antisymm (λ i hi, (finset.mem_filter.mp hi).2) (λ i hi, finset.mem_filter.mpr ⟨hst hi, hi⟩)

lemma sum_ite_mem_of_le [decidable_eq ι] {s t : finset ι} (hst : s ≤ t) (f : ι → M) :
  ∑ i in s, (if i ∈ t then f i else 0) = ∑ i in s, f i :=
by rw [sum_ite, sum_const_zero, filter_mem_of_le hst, add_zero]

lemma sum_ite_mem_of_ge [decidable_eq ι] {s t : finset ι} (hst : t ≤ s) (f : ι → M) :
  ∑ i in s, (if i ∈ t then f i else 0) = ∑ i in t, f i :=
by rw [sum_ite, sum_const_zero, filter_mem_of_ge hst, add_zero]

lemma sum_dite_mem_of_le [decidable_eq ι] {s t : finset ι} (hst : s ≤ t) (f : ∀ i, i ∈ t → M) :
  ∑ i in s, (if h : i ∈ t then f i h else 0) = ∑ i in s.attach, f i (hst i.2) :=
finset.sum_bij (λ i hi, ⟨i, hi⟩)
  (λ i hi, s.mem_attach ⟨i, hi⟩)
  (λ i hi, dif_pos (hst hi))
  (λ i j hi hj h, congr_arg coe h)
  (λ ⟨i, hi⟩ _, ⟨i, hi, rfl⟩)

section

open_locale classical

/-- `s.preimage' f` contains for each `y ∈ s ∩ set.range f` exactly one `x : α` such that `f x = y`. -/
noncomputable def finset.preimage' {α β : Type*} (f : α → β) (s : finset β) : finset α :=
(s.image (function.partial_inv f)).preimage option.some
  (set.inj_on_of_injective (option.some_injective _) _)

lemma apply_eq_of_partial_inv_eq_some {α β : Type*} {f : α → β} {x : α} {y : β}
  (h : function.partial_inv f y = some x) : f x = y :=
begin
  unfold function.partial_inv at h,
  split_ifs at h with h',
  { rw [← classical.some_spec h', h] },
  { contradiction },
end

lemma finset.some_mem_preimage' {α β : Type*} {f : α → β} {s : finset β} {y : β}
  (hys : y ∈ s) (hyf : ∃ x, f x = y) :
  classical.some hyf ∈ s.preimage' f :=
begin
  simp only [finset.preimage', finset.mem_preimage, finset.mem_image],
  use [y, hys],
  exact dif_pos hyf
end

lemma finset.apply_mem_of_mem_preimage' {α β : Type*} {f : α → β} {s : finset β}
  {x : α} (hx : x ∈ s.preimage' f) : f x ∈ s :=
begin
  simp only [finset.preimage', finset.mem_preimage, finset.mem_image] at hx,
  obtain ⟨y, hy, x_eq⟩ := hx,
  cases apply_eq_of_partial_inv_eq_some x_eq,
  exact hy
end

lemma finset.eq_of_mem_preimage' {α β : Type*} {f : α → β} {s : finset β}
  {x x' : α} (hx : x ∈ s.preimage' f) (hx' : x' ∈ s.preimage' f)
  (hf : f x = f x') : x = x' :=
begin
  simp only [finset.preimage', finset.mem_preimage, finset.mem_image] at hx hx',
  obtain ⟨y, hy, x_eq⟩ := hx,
  cases apply_eq_of_partial_inv_eq_some x_eq,
  obtain ⟨y', hy', x'_eq⟩ := hx',
  cases apply_eq_of_partial_inv_eq_some x'_eq,
  apply option.some_injective,
  rw [← x_eq, hf, x'_eq]
end

lemma finset.mem_preimage' {α β : Type*} {f : α → β} {s : finset β} {x : α} :
  x ∈ s.preimage' f ↔ f x ∈ s ∧ ∀ x' ∈ s.preimage' f, f x = f x' → x = x' :=
begin
  split,
  { intros hx,
    use finset.apply_mem_of_mem_preimage' hx,
    intros x' hx' hf,
    exact finset.eq_of_mem_preimage' hx hx' hf },
  { rintros ⟨fx_mem, h⟩,
    have : ∃ a, f a = f x := ⟨x, rfl⟩,
    convert finset.some_mem_preimage' fx_mem this,
    exact h _ (finset.some_mem_preimage' fx_mem _) (classical.some_spec this).symm }
end

lemma finset.exists_mem_preimage' {α β : Type*} {f : α → β} {s : finset β}
  {y : β} (hys : y ∈ s) (hyf : ∃ x, f x = y) : ∃ x ∈ s.preimage' f, f x = y :=
⟨classical.some hyf, finset.some_mem_preimage' hys hyf, classical.some_spec hyf⟩

lemma finset.image_preimage' {α β : Type*} (f : α → β) (s : finset β) :
  (s.preimage' f).image f = s.filter (λ y, ∃ x, f x = y) :=
begin
  ext y,
  simp only [finset.mem_image, finset.mem_filter],
  split,
  { rintros ⟨x, hx, rfl⟩,
    obtain ⟨hfx, uniq⟩ := finset.mem_preimage'.mp hx,
    exact ⟨hfx, x, rfl⟩ },
  { rintros ⟨hys, hyf⟩,
    exact finset.exists_mem_preimage' hys hyf }
end

lemma finset.sum_preimage'' {α β : Type*} (f : α → β) (s : finset β) (g : β → M)
  (hg : ∀ y ∈ s, y ∉ set.range f → g y = 0) :
  ∑ x in s.preimage' f, g (f x) = ∑ y in s, g y :=
begin
  rw [← sum_subset (finset.filter_subset _ s), ← finset.image_preimage' f s, finset.sum_image],
  { intros x hx x' hx' hf, exact finset.eq_of_mem_preimage' hx hx' hf },
  { intros y hys hyf,
    apply hg _ hys,
    contrapose! hyf,
    exact finset.mem_filter.mpr ⟨hys, hyf⟩ }
end

end

lemma dite_smul {p : Prop} [decidable p] (a₁ : p → R) (a₂ : ¬p → R) (b : M) :
  (dite p a₁ a₂) • b = if h : p then a₁ h • b else a₂ h • b :=
by split_ifs; refl

lemma smul_dite {p : Prop} [decidable p] (a : R) (b₁ : p → M) (b₂ : ¬p → M) :
  a • (dite p b₁ b₂) = if h : p then a • b₁ h else a • b₂ h :=
by split_ifs; refl


@[to_additive]
lemma finset.prod_coe {M : Type*} [comm_monoid M] (s : finset ι) (f : (↑s : set ι) → M) :
  ∏ i, f i = ∏ i in s.attach, f i := rfl

lemma finset.linear_independent_iff {s : finset M} :
  linear_independent R (coe : (↑s : set M) → M) ↔ ∀ (g : M → R) (t ⊆ s),
    ∑ x in t, g x • x = 0 → ∀ x ∈ t, g x = 0 :=
begin
  haveI := classical.dec_eq M,
  apply fintype.linear_independent_iff.trans,
  split,
  { intros hs g t ht hg x hx,
    refine trans (if_pos hx).symm (hs (λ x, if x.1 ∈ t then g x else 0) _ ⟨x, ht hx⟩),
    rw [← hg, finset.sum_coe],
    simp only [ite_smul, zero_smul],
    apply trans (@finset.sum_attach _ _ _ _ (λ i, if i ∈ t then g i • i else 0)) _,
    rw sum_ite_mem_of_ge ht },
  { rintros hs g hg ⟨x, hx⟩,
    refine trans (if_pos hx).symm (hs (λ x, if h : x ∈ s then g ⟨x, h⟩ else 0) _ (subset.refl _) _ x hx),
    rw [← hg, finset.sum_coe],
    simp only [dite_smul, zero_smul],
    rw [sum_dite_mem_of_le (le_refl s), finset.sum_congr rfl],
    intros, simp }
end

lemma mem_span_image_iff_exists_sum {b : ι → M} {s : set ι} {x : M} :
  x ∈ span R (b '' s) ↔ ∃ (t : finset ι) (ht : ↑t ⊆ s) (c : ι → R), x = ∑ i in t, c i • b i :=
begin
  haveI := classical.dec_eq ι,
  apply (finsupp.mem_span_iff_total R).trans,
  split,
  { rintros ⟨c, hc, rfl⟩,
    exact ⟨c.support, hc, c, rfl⟩ },
  { rintros ⟨t, ht, c, rfl⟩,
    refine ⟨finsupp.on_finset t (λ i, if i ∈ t then c i else 0) _, _, _⟩,
    { intros i hi,
      contrapose! hi,
      exact if_neg hi },
      { rw finsupp.mem_supported,
        exact set.subset.trans (finset.coe_subset.mpr finsupp.support_on_finset_subset) ht },
      { simp only [finsupp.total_apply, finsupp.on_finset_sum,
        zero_smul, eq_self_iff_true, forall_true_iff],
        exact finset.sum_congr rfl (λ i hi, by rw [if_pos hi]) }}
end

lemma mem_span_range_iff_exists_sum {b : ι → M} {x : M} :
  x ∈ span R (set.range b) ↔ ∃ (t : finset ι) (c : ι → R), x = ∑ i in t, c i • b i :=
by simp [← set.image_univ, mem_span_image_iff_exists_sum]

lemma mem_span_iff_exists_sum {b : set M} {x : M} :
  x ∈ span R b ↔ ∃ (s : finset M) (hs : ↑s ⊆ b) (c : M → R),
    x = ∑ i in s, c i • i :=
by { rw [← set.image_id b, mem_span_image_iff_exists_sum], simp }

end

lemma is_basis.repr_eq_zero (hb : is_basis R b) {x : M} :
  hb.repr x = 0 ↔ x = 0 :=
⟨λ h, (hb.total_repr x).symm.trans (h.symm ▸ (finsupp.total _ _ _ _).map_zero),
 λ h, h.symm ▸ hb.repr.map_zero⟩

lemma finsupp.smul_eq_zero [no_zero_divisors R] {c : R} {f : ι →₀ R} :
  c • f = 0 ↔ c = 0 ∨ f = 0 :=
finsupp.ext_iff.trans
  ⟨λ h, or_iff_not_imp_left.mpr (λ hc, finsupp.ext (λ i, (mul_eq_zero.mp (h i)).resolve_left hc)),
   λ h, by { cases h; simp [h] }⟩

lemma is_basis.smul_eq_zero [no_zero_divisors R] (hb : is_basis R b) {c : R} {x : M} :
  c • x = 0 ↔ c = 0 ∨ x = 0 :=
begin
  split,
  { rw or_iff_not_imp_right,
    intros hcx hx,
    rw [← hb.total_repr x, ← linear_map.map_smul] at hcx,
    have := linear_independent_iff.mp hb.1 (c • hb.repr x) hcx,
    rw finsupp.smul_eq_zero at this,
    exact this.resolve_right (λ hr, hx (hb.repr_eq_zero.mp hr)),
    assumption },
  { rintros (h | h);
    simp [h] }
end

lemma eq_bot_of_rank_eq_zero [no_zero_divisors R] (hb : is_basis R b) (N : submodule R M)
  (rank_le : ∀ (s : finset M) (hs : ∀ x ∈ s, x ∈ N), linear_independent R (coe : (↑s : set M) → M) → s.card ≤ 0) :
  N = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  intros x hx,
  contrapose! rank_le with x_ne,
  refine ⟨{x}, _, _⟩,
  { simpa using hx },
  simp only [nat.zero_lt_one, finset.card_singleton, and_true],
  rw linear_independent_iff',
  rintros t g sum_eq ⟨x', hx'⟩ mem_t,
  simp only [finset.coe_singleton, set.mem_singleton_iff] at hx',
  cases hx',
  clear hx',
  suffices : g ⟨x, hx'⟩ • x = 0,
  { exact (hb.smul_eq_zero.mp this).resolve_right x_ne },
  rw ← sum_eq,
  symmetry,
  apply finset.sum_eq_single,
  { rintros ⟨y, hy⟩ y_mem y_ne,
    simp only [finset.coe_singleton, set.mem_singleton_iff] at hy,
    cases hy,
    contradiction },
  { intros, contradiction },
end

lemma finset.linear_independent_of_subset {s t : finset M} (hs : s ⊆ t)
  (ht : linear_independent R (coe : (↑ t : set M) → M)) :
  linear_independent R (coe : (↑s : set M) → M) :=
begin
  let f : (↑ s : set M) → (↑ t : set M) := λ x, ⟨x.1, hs x.2⟩,
  convert ht.comp f _,
  intros x y h,
  cases x, cases y,
  simpa using h
end

lemma finset.linear_independent_insert [decidable_eq M] {s : finset M} {x : M}
  (hli : linear_independent R (coe : (↑s : set M) → M))
  (x_ortho : (∀ (c : R) (y ∈ submodule.span R (↑s : set M)), c • x + y = (0 : M) → c = 0)) :
  linear_independent R (coe : (↑(insert x s) : set M) → M) :=
begin
  rw finset.linear_independent_iff at hli ⊢,
  rintros g t t_le total_eq y hy,
  by_cases hxt : x ∈ t,
  { have : g x = 0,
    { apply x_ortho (g x) (∑ x in t.erase x, g x • x),
      { refine submodule.sum_mem _ (λ x hx, submodule.smul_mem _ _ (submodule.subset_span _)),
        exact finset.subset_insert_iff.mp t_le hx },
        refine trans _ total_eq,
        conv_rhs { rw ← finset.insert_erase hxt },
        rw finset.sum_insert (finset.not_mem_erase _ _) },
    by_cases hxy : y = x,
    { subst hxy,
      apply x_ortho (g y) (∑ x in t.erase y, g x • x),
      { refine submodule.sum_mem _ (λ x hx, submodule.smul_mem _ _ (submodule.subset_span _)),
        exact finset.subset_insert_iff.mp t_le hx },
      { refine trans _ total_eq,
        conv_rhs { rw ← finset.insert_erase hy },
        rw finset.sum_insert (finset.not_mem_erase _ _) } },
    { apply hli g (t.erase x) (finset.subset_insert_iff.mp t_le) _ _ (finset.mem_erase.mpr ⟨hxy, hy⟩),
      rw [finset.sum_erase, total_eq],
      rw [this, zero_smul ]} },
  { refine hli g t _ total_eq _ hy,
    rwa [finset.subset_insert_iff, finset.erase_eq_of_not_mem hxt] at t_le }
end

lemma finset.mem_span_insert [decidable_eq M] {s : finset M} {x y : M} :
  y ∈ submodule.span R (↑(insert x s) : set M) ↔
    ∃ (c : R) (y' ∈ submodule.span R (↑s : set M)), y = c • x + y' :=
by rw [finset.coe_insert, submodule.mem_span_insert]

end comm_ring

section principal_ideal_domain

open submodule.is_principal

variables {ι : Type*} {R : Type*} {M : Type*} [integral_domain R] [is_principal_ideal_ring R] [add_comm_group M] [module R M] {b : ι → M}

lemma not_mem_of_ortho {x : M} {N : submodule R M}
  (ortho : ∀ (c : R) (y ∈ N), c • x + y = (0 : M) → c = 0) :
  x ∉ N :=
by { intro hx, simpa using ortho (-1) x hx }

lemma ne_zero_of_ortho {x : M} {N : submodule R M}
  (ortho : ∀ (c : R) (y ∈ N), c • x + y = (0 : M) → c = 0) :
  x ≠ 0 :=
mt (λ h, show x ∈ N, from h.symm ▸ N.zero_mem) (not_mem_of_ortho ortho)


lemma induction_on_rank_aux (hb : is_basis R b) (P : submodule R M → Sort*)
  (ih : ∀ (N : submodule R M), (∀ (N' ≤ N) (x ∈ N), (∀ (c : R) (y ∈ N'), c • x + y = (0 : M) → c = 0) → P N') → P N)
  (n : ℕ) (N : submodule R M)
  (rank_le : ∀ (s : finset M) (hs : ∀ x ∈ s, x ∈ N), linear_independent R (coe : (↑s : set M) → M) → s.card ≤ n) :
  P N :=
begin
  haveI : decidable_eq M := classical.dec_eq M,
  have Pbot : P ⊥,
  { apply ih,
    intros N N_le x x_mem x_ortho,
    exfalso,
    simpa using x_ortho 1 0 N.zero_mem },

  induction n with n rank_ih generalizing N,
  { suffices : N = ⊥,
    { rwa this },
    apply eq_bot_of_rank_eq_zero hb _ rank_le },
  apply ih,
  intros N' N'_le x x_mem x_ortho,
  apply rank_ih,
  intros s hs hli,
  refine nat.succ_le_succ_iff.mp (le_trans _ (rank_le (insert x s) _ _)),
  { rw finset.card_insert_of_not_mem,
    intro hx,
    exact not_mem_of_ortho x_ortho (hs _ hx) },
  { intros y hy,
    rcases finset.mem_insert.mp hy with (rfl | mem_s),
    { assumption },
    exact N'_le (hs _ mem_s) },
  { apply finset.linear_independent_insert hli,
    intros c y hy hc,
    apply x_ortho c y _ hc,
    apply submodule.span_le.mpr _ hy,
    exact λ x hx, hs x hx }
end

open_locale matrix

lemma linear_independent.eq_zero_of_smul_eq_zero (hb : linear_independent R b) {c : R} {i}
  (h : c • b i = 0) : c = 0 :=
have finsupp.single i c = 0 := linear_independent_iff.mp hb _ (by rw [finsupp.total_single, h]),
calc c = finsupp.single i c i : by simp
... = 0 : by rw [this, finsupp.zero_apply]

lemma linear_independent.mem_span_iff (hb' : linear_independent R b)
  {s : set ι} {i : ι} :
  (∃ (c : R), c ≠ 0 ∧ c • b i ∈ submodule.span R (b '' s)) ↔ i ∈ s :=
begin
  split,
  { rintro ⟨c, c_ne, hc⟩,
    suffices : ¬ disjoint {i} s,
    { simpa using this },
    intro h,
    refine c_ne (hb'.eq_zero_of_smul_eq_zero (show c • b i = 0, from _)),
    rw [← submodule.mem_bot R, ← disjoint_iff.mp (hb'.disjoint_span_image h), submodule.mem_inf,
        set.image_singleton],
    exact ⟨submodule.mem_span_singleton.mpr ⟨_, rfl⟩, hc⟩ },
  { intro mem_s,
    use [1, one_ne_zero],
    rw one_smul,
    exact submodule.subset_span ⟨i, mem_s, rfl⟩ }
end

lemma is_basis.card_le_card_of_linear_independent
  {ι : Type*} [fintype ι] {b : ι → M} (hb : is_basis R b)
  {ι' : Type*} [fintype ι'] {b' : ι' → M} (hb' : linear_independent R b') :
  fintype.card ι' ≤ fintype.card ι :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq ι',
  haveI := classical.dec_eq R,
  have : ∀ s : finset ι', s = finset.univ ∨ ∃ i : ι,
    (∀ (c : R) (y ∈ submodule.span R (b' '' (↑s : set ι'))), c • b i + y = (0 : M) → c = 0),
  { intros s,
    rw or_iff_not_imp_right,
    intro not_indep,
    simp only [not_exists, not_forall] at not_indep,
    rw finset.eq_univ_iff_forall,
    intros i',
    by_contra hi',
    have : ∀ (c : R), c ≠ 0 → c • b' i' ∉ submodule.span R (b' '' s),
    { intros c,
      rw [← finset.mem_coe, ← hb'.mem_span_iff, not_exists] at hi',
      specialize hi' c,
      rwa not_and at hi' },
    apply this (∏ i, classical.some (not_indep i)),
    { rw finset.prod_ne_zero_iff,
      intros i _,
      exact (classical.some_spec (classical.some_spec (classical.some_spec (classical.some_spec
        (not_indep i))))) },
    have : ∀ i, (∏ (i : ι), classical.some (not_indep i)) • b i ∈ submodule.span R (b' '' s),
    { intro i,
      rw [← finset.insert_erase (finset.mem_univ i), finset.prod_insert (finset.not_mem_erase i _)],
      rw [mul_comm, mul_smul],
      apply submodule.smul_mem _ _ _,
      have := classical.some (classical.some_spec (classical.some_spec (not_indep i))),
      apply (submodule.add_mem_iff_left _ this).mp _,
      convert submodule.zero_mem _,
      exact classical.some (classical.some_spec (classical.some_spec (classical.some_spec (not_indep i)))) },
    rw [← hb.total_repr (b' i'), ← linear_map.map_smul, finsupp.total_apply, finsupp.sum_fintype],
    refine submodule.sum_mem _ (λ j _, _),
    rw [finsupp.smul_apply, smul_eq_mul, mul_comm, mul_smul],
    apply submodule.smul_mem _ _ _,
    exact this j,
    simp },
  have : ∀ s : finset ι', ∃ f : (↑s : set ι') → ι, function.injective f,
  { intro s,
    refine s.induction_on _ _,
    { rw finset.coe_empty,
      refine ⟨λ i, false.elim i.2, λ i, false.elim i.2⟩ },
    { rintros a s ha ⟨f, hf⟩,
      obtain ⟨i, hi⟩ := (this s).resolve_left _,
      sorry, sorry } },
  rw ← finset.card_univ,
  sorry
end

lemma induction_on_rank [fintype ι] (hb : is_basis R b) (P : submodule R M → Sort*)
  (ih : ∀ (N : submodule R M), (∀ (N' ≤ N) (x ∈ N), (∀ (c : R) (y ∈ N'), c • x + y = (0 : M) → c = 0) → P N') → P N)
  (N : submodule R M) : P N :=
induction_on_rank_aux hb P ih (fintype.card ι) N (λ s hs hli,
  by simpa using hb.card_le_card_of_linear_independent hli)

@[simp] lemma fin.cons_zero' {n : ℕ} (C : fin (n + 1) → Type*)
  (hi : 0 < n + 1) (a : C 0) (b : Π (i : fin n), C i.succ) :
  fin.cons a b ⟨0, hi⟩ = a := fin.cons_zero a b

@[simp] lemma fin.cons_succ' {i n : ℕ} (C : fin (n + 1) → Type*)
  (hi : i + 1 < n + 1) (a : C 0) (b : Π (i : fin n), C i.succ) :
  fin.cons a b ⟨i + 1, hi⟩ = b ⟨i, (add_lt_add_iff_right 1).mp hi⟩ :=
fin.cons_succ a b ⟨i, (add_lt_add_iff_right 1).mp hi⟩

lemma submodule.exists_is_basis_fin_zero (N : submodule R (fin 0 → R)) :
  ∃ (bN : fin 0 → N), is_basis R bN :=
begin
  refine ⟨λ _, 0, is_basis_empty not_nonempty_fin_zero _⟩,
  rintro ⟨x, hx⟩,
  ext i,
  exact fin_zero_elim i
end

lemma nonempty_range_map (N : submodule R M) :
  (set.range (λ ϕ, submodule.map ϕ N : (M →ₗ[R] R) → ideal R)).nonempty :=
⟨_, set.mem_range.mpr ⟨0, rfl⟩⟩

/-- The (non-unique) map `ϕ` such that `N.map ϕ` is maximal along the set of `N.map _`. -/
noncomputable def maximal_projection (N : submodule R M) : M →ₗ[R] R :=
have _ := set_has_maximal_iff_noetherian.mpr
  (principal_ideal_ring.is_noetherian_ring : is_noetherian R R) _ (nonempty_range_map N),
have hv' : classical.some this ∈ set.range _ := classical.some (classical.some_spec this),
classical.some hv'

/-- `maximal_projection` has a maximal image. -/
lemma maximal_projection_is_maximal (N : submodule R M) (ϕ : M →ₗ[R] R)
  (hϕ : N.map (maximal_projection N) ≤ N.map ϕ) :
  N.map ϕ = N.map (maximal_projection N) :=
begin
  have h := set_has_maximal_iff_noetherian.mpr
    (principal_ideal_ring.is_noetherian_ring : is_noetherian R R) _ (nonempty_range_map N),
  have h1 := classical.some h,
  have h2 := classical.some_spec h,
  have h21 := classical.some h2,
  have h212 := classical.some_spec (set.mem_range.mp h21),
  have h22 := classical.some_spec h2,
  specialize h22 (N.map ϕ),
  rw ← h212 at h22,
  exact h22 ⟨_, rfl⟩ hϕ,
end

/-- `maximal_gen N` is an element of `N` such that
`maximal_projection N (maximal_gen N)` generates the image of `maximal_projection N`. -/
noncomputable def maximal_gen (N : submodule R M) : M :=
have _ := generator_mem (N.map (maximal_projection N)),
classical.some (submodule.mem_map.mp this)

lemma maximal_gen_mem (N : submodule R M) : maximal_gen N ∈ N :=
have _ := generator_mem (N.map (maximal_projection N)),
(classical.some_spec (submodule.mem_map.mp this)).1

@[simp] lemma maximal_projection_maximal_gen (N : submodule R M) :
  maximal_projection N (maximal_gen N) =
    generator (N.map (maximal_projection N)) :=
have _ := generator_mem (N.map (maximal_projection N)),
(classical.some_spec (submodule.mem_map.mp this)).2

lemma is_basis.ext_elem (hb : is_basis R b) {x y : M}
  (h : ∀ i, hb.repr x i = hb.repr y i) : x = y :=
by { rw [← hb.total_repr x, ← hb.total_repr y], congr' 1, ext i, exact h i }

lemma maximal_gen_ne_zero {b : ι → M} (hb : is_basis R b)
  {N : submodule R M} (hN : N ≠ ⊥) :
  generator (N.map (maximal_projection N)) ≠ 0 :=
begin
  rw [ne.def, submodule.eq_bot_iff] at hN,
  refine mt (λ ha, _) hN,
  intros x hx,
  refine hb.ext_elem (λ i, _),
  have := maximal_projection_is_maximal N ((finsupp.lapply i).comp hb.repr),
  rw (eq_bot_iff_generator_eq_zero _).mpr ha at this,
  rw [linear_map.map_zero, finsupp.zero_apply],
  exact (submodule.eq_bot_iff _).mp (this bot_le) (hb.repr x i) ⟨x, hx, rfl⟩
end

lemma submodule.generator_mem_iff_le {N P : submodule R M} [hN : submodule.is_principal N]:
  generator N ∈ P ↔ N ≤ P :=
begin
  refine ⟨λ h x hx, _, λ h, h (generator_mem N)⟩,
  obtain ⟨a, rfl⟩ := (mem_iff_eq_smul_generator N).mp hx,
  exact P.smul_mem a h
end

lemma generator_dvd_maximal_projection {N : submodule R M} {x : M} (hx : x ∈ N) :
  generator (N.map (maximal_projection N)) ∣ maximal_projection N x :=
begin
  rw [← mem_iff_generator_dvd, submodule.mem_map],
  exact ⟨x, hx, rfl⟩
end

lemma generator_dvd_maximal_gen (N : submodule R M) (ϕ : M →ₗ[R] R) :
  generator (N.map (maximal_projection N)) ∣ ϕ (maximal_gen N) :=
begin
  rw ← mem_iff_generator_dvd,
  set S : ideal R :=
    submodule.span R ({generator (N.map (maximal_projection N)), ϕ (maximal_gen N)} : set R),
  suffices : submodule.map (maximal_projection N) N = S,
  { rw [this, submodule.mem_span_insert],
    exact ⟨0, _, submodule.mem_span_singleton_self _, by rw [zero_smul, zero_add]⟩ },
  have := generator_mem S,
  have le_S : N.map (maximal_projection N) ≤ S :=
    submodule.generator_mem_iff_le.mp (submodule.mem_span_insert.mpr
      ⟨1, 0, submodule.zero_mem _, by rw [one_smul, add_zero]⟩),
  obtain ⟨r₁, d', hd', d_eq⟩ := submodule.mem_span_insert.mp this,
  obtain ⟨r₂, rfl⟩ := submodule.mem_span_singleton.mp hd',
  have : ((r₁ • maximal_projection N) + (r₂ • ϕ)) (maximal_gen N) = generator S,
  { rw [linear_map.add_apply, linear_map.smul_apply, linear_map.smul_apply,
        maximal_projection_maximal_gen, d_eq] },
  have S_le : S ≤ N.map ((r₁ • maximal_projection N) + (r₂ • ϕ)) :=
    submodule.generator_mem_iff_le.mp (submodule.mem_map.mpr
      ⟨maximal_gen N, maximal_gen_mem N, this⟩),
  have := maximal_projection_is_maximal N _ (le_trans le_S S_le),
  rw this at S_le,
  exact le_antisymm le_S S_le
end

@[simp] lemma finset.sum_fin_zero (s : finset (fin 0)) (f : fin 0 → M) :
  ∑ x in s, f x = 0 :=
begin
  refine trans (finset.sum_congr _ (λ _ _, rfl)) finset.sum_empty,
  ext i,
  apply fin_zero_elim i
end

lemma submodule.is_basis_fin_zero_iff {P : submodule R M} {bP : fin 0 → P} :
  is_basis R bP ↔ P = ⊥ :=
begin
  split,
  { intro h,
    rw submodule.eq_bot_iff,
    intros x hx,
    suffices : (⟨x, hx⟩ : P) = 0,
    { exact congr_arg coe this },
    rw [← h.total_repr ⟨x, hx⟩, finsupp.total_apply, finsupp.sum, finset.sum_fin_zero] },
  { rintro rfl,
    split,
    { rw linear_independent_iff',
      intros _ _ _ i,
      exact fin_zero_elim i },
    { rw eq_top_iff,
      rintros ⟨x, hx⟩ -,
      simpa only [(submodule.mem_bot _).mp hx] using submodule.zero_mem _ } }
end

/-

/-- If `M` has a basis, and each submodule of `M` can be decomposed as xR ⊕ another submodule,
then each submodule has a basis. -/
lemma exists_is_basis_induction_aux {n : ℕ} :
  ∀ (P : submodule R M) (b : fin n → P) (hb : is_basis R b)
  (hsub : ∀ N ≤ P, N = ⊥ ∨ ∃ (a : R) (y ∈ P) (P' ≤ P) (N' ≤ N),
    N' ≤ P' ∧ a • y ∈ N ∧ a • y ∉ N' ∧
    (∀ z ∈ P, ∃ (c : R) (y' ∈ P'), c • y + y' = z) ∧
    (∀ z ∈ N, ∃ (c : R) (y' ∈ N'), c • a • y + y' = z))
  (N ≤ P), ∃ (m : ℕ) (bN : fin m → N), is_basis R bN :=
begin
  induction n with n ih; intros P bP hbP hsub N hNP,
  { use 0,
    cases show P = ⊥, from submodule.is_basis_fin_zero_iff.mp hbP,
    cases le_bot_iff.mp hNP,
    exact ⟨bP, hbP⟩ },
  rcases hsub N hNP with (rfl | ⟨a, y, hy, P', hP', N', hN', hN'P', hyN, hyN', hy, hay⟩),
  { exact ⟨0, _, is_basis_empty_bot not_nonempty_fin_zero⟩ },

  obtain ⟨m', bN', hbN'⟩ := ih P' _ _ _ N' hN'P',
  let bN : fin m'.succ → N := fin.cons ⟨a • y, hyN⟩ (λ i, ⟨(bN' i).1, hN' (bN' i).2⟩),
  use [m'.succ, bN],
end

-/

def top_equiv : (⊤ : submodule R M) ≃ₗ[R] M :=
{ to_fun := λ x, x.1,
  inv_fun := λ x, ⟨x, submodule.mem_top⟩,
  left_inv := λ x, by simp,
  right_inv := λ x, by simp,
  map_add' := λ x y, by simp,
  map_smul' := λ c x, by simp }

/-
/-- If `M` has a basis, and each submodule of `M` can be decomposed as xR ⊕ another submodule,
then each submodule has a basis. -/
lemma exists_is_basis_induction {n : ℕ} {b : fin n → M} (hb : is_basis R b)
    (hsub : ∀ (N : submodule R M), N = ⊥ ∨ ∃ (a : R) (y : M) (P : submodule R M) (N' ≤ N),
      N' ≤ P ∧ a • y ∈ N ∧ a • y ∉ N' ∧
      (∀ z, ∃ (c : R) (y' ∈ P), c • y + y' = z) ∧
      (∀ z ∈ N, ∃ (c : R) (y' ∈ N'), c • a • y + y' = z))
    (N : submodule R M) :
    ∃ (m : ℕ) (bN : fin m → N), is_basis R bN :=
begin
  refine exists_is_basis_induction_aux ⊤ _ (top_equiv.symm.is_basis hb) _ _ le_top,
  intros N _,
  rcases hsub N with (hN | ⟨a, y, P, N', hN, hNP, hyN, hyN', hy, hay⟩),
  { exact or.inl hN },
  right,
  refine ⟨a, y, submodule.mem_top, P, le_top, N', hN, hNP, hyN, hyN', _, hay⟩,
  intros z _,
  apply hy
end
-/

lemma exists_generator_smul_eq_maximal_gen [fintype ι] (hb : is_basis R b)
  {N : submodule R M} (hN : N ≠ ⊥):
  ∃ y, generator (N.map (maximal_projection N)) • y = maximal_gen N :=
begin
  let π : ι → (M →ₗ[R] R) :=
  λ i, ⟨λ x, hb.repr x i,
  λ x y, by rw [linear_map.map_add, finsupp.add_apply],
  λ x y, by rw [linear_map.map_smul, finsupp.smul_apply]⟩,
  have π_apply : ∀ i x, π i x = hb.repr x i := λ x i, rfl,

  have ha := maximal_gen_ne_zero hb hN,

  have : ∀ ϕ : M →ₗ[R] R, generator (N.map (maximal_projection N)) ∣ ϕ (maximal_gen N) :=
  generator_dvd_maximal_gen N,
  have : ∀ i, generator (N.map (maximal_projection N)) ∣ π i (maximal_gen N) := λ i, this (π i),
  let c : ι → R := λ i, classical.some (this i),
  have c_spec : ∀ i, π i (maximal_gen N) = generator (N.map (maximal_projection N)) * c i :=
  λ i, classical.some_spec (this i),
  use ∑ i, c i • b i,
  -- TODO: this should be easier!
  simp_rw [finset.smul_sum, ← smul_assoc, smul_eq_mul, ← c_spec, π_apply],
  refine trans _ (hb.total_repr (maximal_gen N)),
  simp only [finsupp.total_apply, finsupp.sum_fintype, eq_self_iff_true, zero_smul, forall_true_iff],
end

lemma finset.linear_independent_image
  {M' : Type*} [decidable_eq M'] [add_comm_group M'] [module R M']
  {s : finset M} (f : M →ₗ[R] M') (hf : function.injective f)
  (hs : linear_independent R (coe : (↑s : set M) → M)) :
  linear_independent R (coe : (↑(s.image f) : set M') → M') :=
begin
  rw finset.linear_independent_iff at hs ⊢,
  intros g t ht total_eq x hx,
  obtain ⟨x, x_mem, rfl⟩ := finset.mem_image.mp (ht hx),
  apply hs (g ∘ f) (t.preimage f (set.inj_on_of_injective hf _)),
  { intros x hx, obtain ⟨y, hy, y_eq⟩ := finset.mem_image.mp (ht (finset.mem_preimage.mp hx)),
    rwa hf y_eq at hy },
  { apply hf,
    simp only [f.map_sum, f.map_zero, f.map_smul, function.comp_apply],
    rw [finset.sum_preimage f t _ (λ x, g x • x), total_eq],
    intros y hy hy',
    obtain ⟨x, hx, rfl⟩ := finset.mem_image.mp (ht hy),
    have : f x ∈ set.range f := set.mem_range.mpr ⟨x, rfl⟩,
    contradiction },
  { exact finset.mem_preimage.mpr hx }
end

-- `n` is the rank of `M` and `m` is the rank of `N`; I copied this unfortunate notation from Dummit and Foote.
/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain. -/
lemma submodule.exists_is_basis {ι : Type*} [fintype ι]
  {b : ι → M} (hb : is_basis R b) (N : submodule R M) :
  ∃ (bN : finset N), is_basis R (λ (x : (↑ bN : set N)), (x : N)) :=
begin
  haveI := classical.dec_eq M,
  refine induction_on_rank hb _ _ N,
  intros N ih,

  -- Either `N` is trivial,
  -- or we can find `a : R`, `y : M` such that `M = y R ⊕ _` and `N = a • y R ⊕ _`.
  by_cases hN : N = ⊥,
  { rw hN,
    use ∅,
    convert is_basis_empty_bot _,
    { ext ⟨i, hi⟩, cases hi },
    { rintro ⟨i, hi⟩, cases hi } },

  -- We claim the following `y` can be a basis element of `M` such that `a • y` is a basis element of `N`.
  obtain ⟨y, y'_eq⟩ := exists_generator_smul_eq_maximal_gen hb hN,

  have ay_mem_N : generator (N.map (maximal_projection N)) • y ∈ N,
  { have : maximal_gen N ∈ N := maximal_gen_mem N,
    rwa ← y'_eq at this },

  obtain ⟨bN', hbN'⟩ := ih ((maximal_projection N).ker ⊓ N) inf_le_right
    (maximal_gen N)
    (maximal_gen_mem N) _,
  have N'_le_ker : ((maximal_projection N).ker ⊓ N) ≤ (maximal_projection N).ker := inf_le_left,
  have N'_le_N : ((maximal_projection N).ker ⊓ N) ≤ N := inf_le_right,
  set bN : finset N := bN'.image (submodule.of_le N'_le_N),
  have bN_li : linear_independent R (coe : (↑bN : set N) → N),
  { apply finset.linear_independent_image (submodule.of_le N'_le_N) _ hbN'.1,
    rintros ⟨x, hx⟩ ⟨x', hx'⟩ (h : (⟨x, N'_le_N hx⟩ : N) = ⟨x', N'_le_N hx'⟩),
    rwa [subtype.mk_eq_mk] at h ⊢ },
  have mem_span_bN : ∀ (y : N), y ∈ submodule.span R (↑bN : set N) ↔ maximal_projection N y = 0,
  { rintros ⟨y, hy⟩,
    simp only [finset.coe_image, submodule.coe_mk,
               submodule.span_image, submodule.mem_map],
    split,
    { rintros ⟨⟨y', hy'⟩, mem_span, map_eq : (⟨y', N'_le_N hy'⟩ : N) = ⟨y, hy⟩⟩,
      have := subtype.mk_eq_mk.mp map_eq,
      subst this,
      exact linear_map.mem_ker.mp (N'_le_ker hy') },
    { intros hy_ker,
      rw ← linear_map.mem_ker at hy_ker,
      refine ⟨⟨y, submodule.mem_inf.mpr ⟨hy_ker, hy⟩⟩, _, _⟩,
      { simpa using hbN'.mem_span ⟨y, submodule.mem_inf.mpr ⟨hy_ker, hy⟩⟩ },
      { ext, simp } } },
  use insert (⟨maximal_gen N, maximal_gen_mem N⟩ : N) bN,
  split,
  { apply finset.linear_independent_insert bN_li,
    intros c y hy hc,
    rw mem_span_bN at hy,
    simpa only [hy, maximal_gen_ne_zero hb hN, maximal_projection_maximal_gen,
        linear_map.map_zero, submodule.coe_smul, add_zero, algebra.id.smul_eq_mul,
        submodule.coe_add, submodule.coe_mk, function.comp_app, or_false,
        submodule.coe_zero, linear_map.map_smul, linear_map.map_add, mul_eq_zero]
        using congr_arg (maximal_projection N ∘ (coe : N → M)) hc },
  { rw eq_top_iff,
    rintro x -,
    simp only [subtype.range_coe_subtype, finset.mem_coe], apply finset.mem_span_insert.mpr,
    obtain ⟨b, hb⟩ : _ ∣ maximal_projection N x := generator_dvd_maximal_projection x.2,
    refine ⟨b, x - b • ⟨_, ay_mem_N⟩, _, _⟩,
    { rw [mem_span_bN, submodule.coe_sub, linear_map.map_sub, hb, submodule.coe_smul, linear_map.map_smul,
          submodule.coe_mk, y'_eq, smul_eq_mul, mul_comm, maximal_projection_maximal_gen, sub_self] },
    { ext, simp only [y'_eq, add_sub_cancel'_right] } },
  { intros c x hx hc,
    have hx' : x ∈ (maximal_projection N).ker := (inf_le_left : _ ⊓ N ≤ _) hx,
    rw linear_map.mem_ker at hx',
    simpa [maximal_gen_ne_zero hb hN, hx'] using congr_arg (maximal_projection N) hc }
end

end principal_ideal_domain
