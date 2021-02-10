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

This file proves a submodule of a free `R`-module of finite rank is also
a free `R`-module of finite rank, if `R` is a principal ideal domain.
-/

open_locale big_operators

section comm_ring

universes u v

variables {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
variables {ι : Type*} {b : ι → M} (hb : is_basis R b)

open submodule.is_principal

/-

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

/-- `s.preimage' f` contains for each `y ∈ s ∩ set.range f`
exactly one `x : α` such that `f x = y`. -/
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
    refine trans _ (hs (λ x, if h : x ∈ s then g ⟨x, h⟩ else 0) _ (subset.refl _) _ x hx),
    { apply (dif_pos hx).symm },
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
-/

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
  (rank_eq : ∀ {m : ℕ} (v : fin m → N),
    linear_independent R (coe ∘ v : fin m → M) → m = 0) :
  N = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  intros x hx,
  contrapose! rank_eq with x_ne,
  refine ⟨1, λ _, ⟨x, hx⟩, _, one_ne_zero⟩,
  rw fintype.linear_independent_iff,
  rintros g sum_eq i,
  fin_cases i,
  simp only [function.const_apply, fin.default_eq_zero, submodule.coe_mk, univ_unique,
             function.comp_const, finset.sum_singleton] at sum_eq,
  exact (hb.smul_eq_zero.mp sum_eq).resolve_right x_ne
end

/-
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
    { apply hli g (t.erase x)
        (finset.subset_insert_iff.mp t_le) _ _
        (finset.mem_erase.mpr ⟨hxy, hy⟩),
      rw [finset.sum_erase, total_eq],
      rw [this, zero_smul] } },
  { refine hli g t _ total_eq _ hy,
    rwa [finset.subset_insert_iff, finset.erase_eq_of_not_mem hxt] at t_le }
end

lemma finset.mem_span_insert [decidable_eq M] {s : finset M} {x y : M} :
  y ∈ submodule.span R (↑(insert x s) : set M) ↔
    ∃ (c : R) (y' ∈ submodule.span R (↑s : set M)), y = c • x + y' :=
by rw [finset.coe_insert, submodule.mem_span_insert]
-/

open submodule

lemma fin.linear_independent_cons {m : ℕ} (x : M) (v : fin m → M)
  (hli : linear_independent R v)
  (x_ortho : (∀ (c : R) (y : submodule.span R (set.range v)), c • x + y = (0 : M) → c = 0)) :
  linear_independent R (fin.cons x v : fin m.succ → M) :=
begin
  rw fintype.linear_independent_iff at hli ⊢,
  rintros g total_eq j,
  have zero_not_mem : (0 : fin m.succ) ∉ finset.univ.image (fin.succ : fin m → fin m.succ),
  { rw finset.mem_image,
    rintro ⟨x, hx, succ_eq⟩,
    exact fin.succ_ne_zero _ succ_eq },
  simp only [submodule.coe_mk, fin.univ_succ, finset.sum_insert zero_not_mem,
             fin.cons_zero, fin.cons_succ,
             forall_true_iff, imp_self, fin.succ_inj, finset.sum_image] at total_eq,
  have : g 0 = 0,
  { refine x_ortho (g 0) ⟨∑ (i : fin m), g i.succ • v i, _⟩ total_eq,
    exact sum_mem _ (λ i _, smul_mem _ _ (subset_span ⟨i, rfl⟩)) },
  refine fin.cases this (λ j, _) j,
  apply hli (λ i, g i.succ),
  simpa only [this, zero_smul, zero_add] using total_eq
end

lemma is_basis.ext_elem (hb : is_basis R b) {x y : M}
(h : ∀ i, hb.repr x i = hb.repr y i) : x = y :=
by { rw [← hb.total_repr x, ← hb.total_repr y], congr' 1, ext i, exact h i }

lemma eq_bot_of_generator_maximal_map_eq_zero (hb : is_basis R b) {N : submodule R M}
  {ϕ : M →ₗ[R] R} (hϕ : ∀ (ψ : M →ₗ[R] R), N.map ϕ ≤ N.map ψ → N.map ψ = N.map ϕ)
  [(N.map ϕ).is_principal] (hgen : generator (N.map ϕ) = 0) : N = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  intros x hx,
  refine hb.ext_elem (λ i, _),
  rw (eq_bot_iff_generator_eq_zero _).mpr hgen at hϕ,
  rw [linear_map.map_zero, finsupp.zero_apply],
  exact (submodule.eq_bot_iff _).mp (hϕ ((finsupp.lapply i).comp hb.repr) bot_le) _ ⟨x, hx, rfl⟩
end

lemma generator_dvd_maximal_projection {N : submodule R M}
  {ϕ : M →ₗ[R] R} (hϕ : ∀ (ψ : M →ₗ[R] R), N.map ϕ ≤ N.map ψ → N.map ψ = N.map ϕ)
  [(N.map ϕ).is_principal] {x : M} (hx : x ∈ N) :
  generator (N.map ϕ) ∣ ϕ x :=
by { rw [← mem_iff_generator_dvd, submodule.mem_map], exact ⟨x, hx, rfl⟩ }

end comm_ring

section integral_domain

variables {ι : Type*} {R : Type*} [integral_domain R]
variables {M : Type*} [add_comm_group M] [module R M] {b : ι → M}

lemma not_mem_of_ortho {x : M} {N : submodule R M}
  (ortho : ∀ (c : R) (y ∈ N), c • x + y = (0 : M) → c = 0) :
  x ∉ N :=
by { intro hx, simpa using ortho (-1) x hx }

lemma ne_zero_of_ortho {x : M} {N : submodule R M}
  (ortho : ∀ (c : R) (y ∈ N), c • x + y = (0 : M) → c = 0) :
  x ≠ 0 :=
mt (λ h, show x ∈ N, from h.symm ▸ N.zero_mem) (not_mem_of_ortho ortho)

/-- If `N` is a submodule with finite rank, do induction on adjoining a linear independent
element to a submodule. -/
def submodule.induction_on_rank_aux (hb : is_basis R b) (P : submodule R M → Sort*)
  (ih : ∀ (N : submodule R M),
    (∀ (N' ≤ N) (x ∈ N), (∀ (c : R) (y ∈ N'), c • x + y = (0 : M) → c = 0) → P N') → P N)
  (n : ℕ) (N : submodule R M)
  (rank_le : ∀ {m : ℕ} (v : fin m → N),
    linear_independent R (coe ∘ v : fin m → M) → m ≤ n) :
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
    apply eq_bot_of_rank_eq_zero hb _ (λ m v hv, nat.le_zero_iff.mp (rank_le v hv)) },
  apply ih,
  intros N' N'_le x x_mem x_ortho,
  apply rank_ih,
  intros m v hli,
  refine nat.succ_le_succ_iff.mp (rank_le (fin.cons ⟨x, x_mem⟩ (λ i, ⟨v i, N'_le (v i).2⟩)) _),
  convert fin.linear_independent_cons x _ hli _,
  { ext i, refine fin.cases _ _ i; simp },
  { intros c y hcy,
    refine x_ortho c y (submodule.span_le.mpr _ y.2) hcy,
    rintros _ ⟨z, rfl⟩,
    exact (v z).2 }
end

/-
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

lemma finset.prod_fin_succ {α : Type*} [comm_monoid α] {n : ℕ}
  (f : fin n.succ → α) : ∏ i, f i = (∏ (i : fin n), f i.succ) * f 0 :=
begin
  simp only [finset.prod_fin_eq_prod_range, finset.prod_range_succ', dif_pos (nat.zero_lt_succ n)],
  congr,
  ext i,
  split_ifs with hi1 hi hi,
  { refl },
  { have := nat.succ_lt_succ_iff.mp hi1,
    contradiction },
  { have := nat.succ_lt_succ_iff.mpr hi,
    contradiction },
  { refl }
end

lemma finset.sum_fin_succ {α : Type*} [add_comm_monoid α] {n : ℕ}
  (f : fin n.succ → α) : ∑ i, f i = (∑ (i : fin n), f i.succ) + f 0 :=
begin
  simp only [finset.sum_fin_eq_sum_range, finset.sum_range_succ', dif_pos (nat.zero_lt_succ n)],
  congr,
  ext i,
  split_ifs with hi1 hi hi,
  { refl },
  { have := nat.succ_lt_succ_iff.mp hi1,
    contradiction },
  { have := nat.succ_lt_succ_iff.mpr hi,
    contradiction },
  { refl }
end
-/

lemma finset.sum_fin_succ_above {α : Type*} [add_comm_monoid α] {n : ℕ} (i : fin n.succ)
  (f : fin n.succ → α) : ∑ j, f j = f i + ∑ (j : fin n), f (i.succ_above j) :=
begin
  rw [← finset.insert_erase (finset.mem_univ i), finset.sum_insert (finset.not_mem_erase i _),
      finset.sum_bij (λ j hj, i.pred_above _ (finset.ne_of_mem_erase hj))],
  { intros j hj, exact finset.mem_univ _ },
  { intros j hj, simp },
  { intros j j' hj hj' h, simpa using congr_arg i.succ_above h },
  { intros j hj,
    refine ⟨i.succ_above j, finset.mem_erase.mpr ⟨i.succ_above_ne j, finset.mem_univ _⟩, _⟩,
    simp },
end

/-- In an `n`-dimensional space, the rank is at most `m`. -/
lemma is_basis.card_le_card_of_linear_independent_aux
  {R : Type*} [integral_domain R]
  (n : ℕ) {m : ℕ} (v : fin m → fin n → R) :
  linear_independent R v → m ≤ n :=
begin
  revert m,
  refine nat.rec_on n _ _,
  { intros m v hv,
    cases m, { refl },
    exfalso,
    have : v 0 = 0,
    { ext i, exact fin_zero_elim i },
    have := hv.ne_zero 0,
    contradiction },
  intros n ih m v hv,
  cases m,
  { exact nat.zero_le _ },

  -- Induction: try deleting a dimension and a vector.
  suffices : ∃ (v' : fin m → fin n → R), linear_independent R v',
  { obtain ⟨v', hv'⟩ := this,
    exact nat.succ_le_succ (ih v' hv') },
  -- Either the `0`th dimension is irrelevant...
  by_cases this : linear_independent R (λ i, v i ∘ fin.succ),
  { exact ⟨_, this.comp fin.succ (fin.succ_injective _)⟩ },
  -- ... or we can write (x, 0, 0, ...) = ∑ i, c i • v i where c i ≠ 0 for some i.
  simp only [fintype.linear_independent_iff, not_forall, not_imp] at this,
  obtain ⟨c, hc, i, hi⟩ := this,
  have hc : ∀ (j : fin n), ∑ (i : fin m.succ), c i * v i j.succ = 0,
  { intro j,
    convert congr_fun hc j,
    rw [@finset.sum_apply (fin n) (λ _, R) _ _ _],
    simp },
  set x := ∑ i', c i' * v i' 0 with x_eq,
  -- We'll show each equation of the form (y, 0, 0, ...) = ∑ i', c' i' • v i' must have c' i ≠ 0.
  use λ i' j', v (i.succ_above i') j'.succ,
  rw fintype.linear_independent_iff at ⊢ hv,
  -- Assume that ∑ i, c' i • v i = (y, 0, 0, ...).
  intros c' hc' i',
  set y := ∑ i', c' i' * v (i.succ_above i') 0 with y_eq,
  have hc' : ∀ (j : fin n), (∑ (i' : fin m), c' i' * v (i.succ_above i') j.succ) = 0,
  { intro j,
    convert congr_fun hc' j,
    rw [@finset.sum_apply (fin n) (λ _, R) _ _ _],
    simp },
  -- Combine these equations to get a linear dependence on the full space.
  have : ∑ i', (y * c i' - x * (@fin.insert_nth _ (λ _, R) i 0 c') i') • v i' = 0,
  { simp only [sub_smul, mul_smul, finset.sum_sub_distrib, ← finset.smul_sum],
    ext j,
    rw [pi.zero_apply, @pi.sub_apply (fin n.succ) (λ _, R) _ _ _ _],
    simp only [finset.sum_apply, pi.smul_apply, smul_eq_mul, sub_eq_zero],
    symmetry,
    rw [finset.sum_fin_succ_above i, fin.insert_nth_apply_same, zero_mul, zero_add, mul_comm],
    simp only [fin.insert_nth_apply_succ_above],
    refine fin.cases _ _ j,
    { simp },
    { intro j,
      rw [hc', hc, zero_mul, mul_zero] } },
  have hyc := hv _ this i,
  simp only [fin.insert_nth_apply_same, mul_zero, sub_zero, mul_eq_zero] at hyc,
  -- Therefore, either `c i = 0` (which contradicts the assumption on `i`) or `y = 0`.
  have hy := hyc.resolve_right hi,
  -- If `y = 0`, then we can extend `c'` to a linear dependence on the full space,
  -- which implies `c'` is trivial.
  convert hv (@fin.insert_nth _ (λ _, R) i 0 c') _ (i.succ_above i'),
  { rw [fin.insert_nth_apply_succ_above] },
  ext j,
  -- After a bit of calculation, we find that `∑ i, c' i • v i = (y, 0, 0, ...) = 0` as promised.
  rw [@finset.sum_apply (fin n.succ) (λ _, R) _ _ _, pi.zero_apply],
  simp only [pi.smul_apply, smul_eq_mul],
  rw [finset.sum_fin_succ_above i, fin.insert_nth_apply_same, zero_mul, zero_add],
  simp only [fin.insert_nth_apply_succ_above],
  refine fin.cases _ _ j,
  { rw [← y_eq, hy] },
  { exact hc' },
end

lemma is_basis.card_le_card_of_linear_independent
  {R : Type*} [integral_domain R] [module R M]
  {ι : Type*} [fintype ι] {b : ι → M} (hb : is_basis R b)
  {ι' : Type*} [fintype ι'] {v : ι' → M} (hv : linear_independent R v) :
  fintype.card ι' ≤ fintype.card ι :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq ι',
  obtain ⟨e⟩ := fintype.equiv_fin ι,
  obtain ⟨e'⟩ := fintype.equiv_fin ι',
  have hb := hb.comp _ e.symm.bijective,
  have hv := (linear_independent_equiv e'.symm).mpr hv,
  have hv := hv.map' _ hb.equiv_fun.ker,
  exact is_basis.card_le_card_of_linear_independent_aux (fintype.card ι) _ hv,
end

/-- If `N` is a submodule in a free, finitely generated module,
do induction on adjoining a linear independent element to a submodule. -/
def submodule.induction_on_rank [fintype ι] (hb : is_basis R b) (P : submodule R M → Sort*)
  (ih : ∀ (N : submodule R M),
    (∀ (N' ≤ N) (x ∈ N), (∀ (c : R) (y ∈ N'), c • x + y = (0 : M) → c = 0) → P N') →
    P N)
  (N : submodule R M) : P N :=
submodule.induction_on_rank_aux hb P ih (fintype.card ι) N (λ s hs hli,
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
  refine ⟨λ _, 0, is_basis_empty (λ h, h.elim fin_zero_elim) _⟩,
  rintro ⟨x, hx⟩,
  ext i,
  exact fin_zero_elim i
end

lemma nonempty_range_map (N : submodule R M) :
  (set.range (λ ϕ, submodule.map ϕ N : (M →ₗ[R] R) → ideal R)).nonempty :=
⟨_, set.mem_range.mpr ⟨0, rfl⟩⟩

open submodule.is_principal

lemma submodule.generator_mem_iff_le {N P : submodule R M} [hN : submodule.is_principal N] :
  generator N ∈ P ↔ N ≤ P :=
begin
  refine ⟨λ h x hx, _, λ h, h (generator_mem N)⟩,
  obtain ⟨a, rfl⟩ := (mem_iff_eq_smul_generator N).mp hx,
  exact P.smul_mem a h
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
lemma fin.linear_independent_cons {n : ℕ} {x : M} {b : fin n → M}
  (hli : linear_independent R b)
  (x_ortho : (∀ (c : R) (y ∈ submodule.span R (set.range b)), c • x + y = (0 : M) → c = 0)) :
  linear_independent R (fin.cons x b : fin n.succ → M) :=
begin
  rw fintype.linear_independent_iff at hli ⊢,
  rintros g total_eq i,
  have : g 0 = 0,
  { apply x_ortho (g 0) (∑ j : fin n, g j.succ • b j),
    { refine submodule.sum_mem _ (λ x hx, submodule.smul_mem _ _ (submodule.subset_span _)),
      exact set.mem_range.mpr ⟨x, rfl⟩ },
    simpa only [finset.sum_fin_succ, add_comm, fin.cons_zero, fin.cons_succ] using total_eq },
  refine fin.cases _ _ i,
  { exact this },
  { intro i,
    apply hli (g ∘ fin.succ),
    simpa only [finset.sum_fin_succ, this, zero_smul, add_zero, fin.cons_succ] using total_eq }
end
-/

/-- The canonical isomorphism between `⊤ : submodule R M` and `M` itself. -/
def submodule.top_equiv : (⊤ : submodule R M) ≃ₗ[R] M :=
{ to_fun := λ x, x.1,
  inv_fun := λ x, ⟨x, submodule.mem_top⟩,
  left_inv := λ x, by simp,
  right_inv := λ x, by simp,
  map_add' := λ x y, by simp,
  map_smul' := λ c x, by simp }

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

end integral_domain

section principal_ideal_domain

open submodule.is_principal

variables {ι : Type*} {R : Type*} [integral_domain R] [is_principal_ideal_ring R]
variables {M : Type*} [add_comm_group M] [module R M] {b : ι → M}

open_locale matrix

/-- The (non-unique) map `ϕ` such that `N.map ϕ` is maximal along the set of `N.map _`. -/
noncomputable def maximal_projection (N : submodule R M) : M →ₗ[R] R :=
have _ := set_has_maximal_iff_noetherian.mpr
  (infer_instance : is_noetherian R R) _ (nonempty_range_map N),
have hv' : classical.some this ∈ set.range _ := classical.some (classical.some_spec this),
classical.some hv'

/-- `maximal_projection` has a maximal image. -/
lemma maximal_projection_is_maximal (N : submodule R M) (ϕ : M →ₗ[R] R)
  (hϕ : N.map (maximal_projection N) ≤ N.map ϕ) :
  N.map ϕ = N.map (maximal_projection N) :=
begin
  have h := set_has_maximal_iff_noetherian.mpr
  (infer_instance : is_noetherian R R) _ (nonempty_range_map N),
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

@[simp]
lemma set.range_fin_cons {α : Type*} {n : ℕ} (x : α) (b : fin n → α) :
  set.range (fin.cons x b : fin n.succ → α) = insert x (set.range b) :=
begin
  ext y,
  simp only [set.mem_range, set.mem_insert_iff],
  split,
  { rintros ⟨i, rfl⟩,
    refine fin.cases (or.inl (fin.cons_zero _ _)) (λ i, or.inr ⟨i, _⟩) i,
    rw fin.cons_succ },
  { rintros (rfl | ⟨i, hi⟩),
    { exact ⟨0, fin.cons_zero _ _⟩ },
    { refine ⟨i.succ, _⟩,
      rw [fin.cons_succ, hi] } }
end

lemma exists_generator_smul_eq_maximal_gen [fintype ι] (hb : is_basis R b)
  {N : submodule R M} :
  ∃ y, generator (N.map (maximal_projection N)) • y = maximal_gen N :=
begin
  let π : ι → (M →ₗ[R] R) :=
  λ i, ⟨λ x, hb.repr x i,
  λ x y, by rw [linear_map.map_add, finsupp.add_apply],
  λ x y, by rw [linear_map.map_smul, finsupp.smul_apply]⟩,
  have π_apply : ∀ i x, π i x = hb.repr x i := λ x i, rfl,

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
  simp only [finsupp.total_apply, finsupp.sum_fintype, eq_self_iff_true, zero_smul, forall_true_iff]
end

lemma mem_span_basis_iff {N : submodule R M} {n : ℕ}
  {bN : fin n → (maximal_projection N).ker ⊓ N} (hbN : is_basis R bN) (y : N) :
  y ∈ submodule.span R (set.range
      (submodule.of_le (inf_le_right : ((maximal_projection N).ker ⊓ N) ≤ N) ∘ bN)) ↔
    maximal_projection N y = 0 :=
begin
  have N'_le_ker : ((maximal_projection N).ker ⊓ N) ≤ (maximal_projection N).ker := inf_le_left,
  obtain ⟨y, hy⟩ := y,
  simp only [set.range_comp, submodule.span_image, submodule.mem_map],
  split,
  { rintros ⟨⟨y', mem_N'⟩, _, map_eq⟩,
    have := subtype.mk_eq_mk.mp map_eq,
    subst this,
    exact linear_map.mem_ker.mp (N'_le_ker mem_N') },
  { intros hy_ker,
    rw ← linear_map.mem_ker at hy_ker,
    refine ⟨⟨y, submodule.mem_inf.mpr ⟨hy_ker, hy⟩⟩, _, _⟩,
    { show _ ∈ submodule.span R (bN '' set.range id),
      simpa using hbN.mem_span ⟨y, submodule.mem_inf.mpr ⟨hy_ker, hy⟩⟩ },
    { ext, simp } }
end

lemma linear_independent_maximal_gen_cons {N : submodule R M} (hN : N ≠ ⊥) {n : ℕ}
  {b : ι → M} (hb : is_basis R b)
  {bN : fin n → (maximal_projection N).ker ⊓ N} (hbN : is_basis R bN) :
  linear_independent R (fin.cons
      ⟨maximal_gen N, maximal_gen_mem N⟩
      (submodule.of_le (inf_le_right : ((maximal_projection N).ker ⊓ N) ≤ N) ∘ bN) :
    fin n.succ → N) :=
begin
  refine fin.linear_independent_cons _ _ (hbN.1.map' _ (submodule.ker_of_le _ _ _)) _,
  intros c y hc,
  have := congr_arg (maximal_projection N ∘ (coe : N → M)) hc,
  squeeze_simp at this,
  exact this.resolve_right (maximal_gen_ne_zero hb hN),
end

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain. -/
lemma submodule.exists_is_basis {ι : Type*} [fintype ι]
  {b : ι → M} (hb : is_basis R b) (N : submodule R M) :
  ∃ (n : ℕ) (bN : fin n → N), is_basis R bN :=
begin
  haveI := classical.dec_eq M,
  refine N.induction_on_rank hb _ _,
  intros N ih,

  -- Let `ϕ` be a maximal projection of `M` onto `R`, in the sense that there is
  -- no `ψ` whose image of `N` is larger than `ϕ`'s image of `N`.
  obtain ⟨ϕ, ϕ_max⟩ : ∃ ϕ : M →ₗ[R] R, ∀ (ψ : M →ₗ[R] R), N.map ϕ ≤ N.map ψ → N.map ψ = N.map ϕ := _,
  -- Since `N.map ϕ` is a `R`-submodule of the PID `R`, it is principal and generated by some `a`.
  have a_mem : generator (N.map ϕ) ∈ N.map ϕ := generator_mem _,

  -- If `a` is zero, then the submodule is trivial. So let's assume `a ≠ 0`, `N ≠ ⊥`
  by_cases N_bot : N = ⊥,
  { rw N_bot,
    refine ⟨0, λ _, 0, is_basis_empty_bot _⟩,
    rintro ⟨i, ⟨⟩⟩ },
  by_cases a_zero : generator (N.map ϕ) = 0,
  { have := eq_bot_of_generator_maximal_map_eq_zero hb ϕ_max a_zero,
    contradiction },

  -- We claim that `ϕ⁻¹ a = y` is a basis element of `M` such that `a • y` is a basis element of `N`.
  obtain ⟨y, y_mem, y'_eq⟩ := a_mem,
  have ay_mem_N : generator (N.map ϕ) • y ∈ N := N.smul_mem _ y_mem,

  -- If `N'` is `ker (ϕ : N → R)`, it is smaller than `N` so by the induction hypothesis,
  -- it has a basis `bN'`.
  have N'_le_ker : (ϕ.ker ⊓ N) ≤ ϕ.ker := inf_le_left,
  have N'_le_N : (ϕ.ker ⊓ N) ≤ N := inf_le_right,
  obtain ⟨nN', bN', hbN'⟩ := ih (ϕ.ker ⊓ N) N'_le_N y y_mem _,
  use nN'.succ,

  use fin.cons ⟨y, y_mem⟩ (submodule.of_le N'_le_N ∘ bN'),
  have bN_li : linear_independent R (submodule.of_le N'_le_N ∘ bN'),
  { apply hbN'.1.map',
    exact submodule.ker_of_le _ _ _ },
  split,
  { apply fin.linear_independent_cons _ _ bN_li,
    intros c z hc,
    have : submodule.span R (set.range (coe ∘ bN')) ≤ ϕ.ker,
    { rw submodule.span_le,
      rintros _ ⟨i, rfl⟩,
      exact N'_le_ker (bN' i).2 },
    have hz : ϕ (z : N) = 0 := linear_map.mem_ker.mp (this sorry),
    have := congr_arg (ϕ ∘ coe) hc,
    simp only [hz, linear_map.map_zero, submodule.coe_smul, add_zero, algebra.id.smul_eq_mul,
               submodule.coe_add, submodule.coe_mk, function.comp_app, submodule.coe_zero,
               linear_map.map_smul, linear_map.map_add, mul_eq_zero] at this,
    exact this.resolve_right (λ h, a_zero (y'_eq.symm.trans h)) },
  { rw eq_top_iff,
    rintro x -,
    rw [set.range_fin_cons, set.range_comp, submodule.mem_span_insert, submodule.span_image],
    obtain ⟨b, hb⟩ : _ ∣ ϕ x := generator_dvd_maximal_projection ϕ_max x.2,
    refine ⟨b, x - b • ⟨_, ay_mem_N⟩, _, _⟩,
    { rw submodule.mem_map, },
    /-
    refine ⟨b, x - b • ⟨_, ay_mem_N⟩, _, _⟩,
    { rw [mem_span_basis_iff hbN', submodule.coe_sub, linear_map.map_sub, hb, submodule.coe_smul,
          linear_map.map_smul, submodule.coe_mk, y'_eq, smul_eq_mul, mul_comm,
          maximal_projection_maximal_gen, sub_self] },
    { ext, simp only [y'_eq, add_sub_cancel'_right] } -/ }

  /-
  have bN_li : linear_independent R (submodule.of_le N'_le_N ∘ bN'),
  { apply hbN'.1.map',
    exact submodule.ker_of_le _ _ _ },
  split,
  { exact linear_independent_maximal_gen_cons hN hb hbN' },
  { rw eq_top_iff,
    rintro x -,
    simp only [set.range_cons],
    rw submodule.mem_span_insert,
     },
  { intros c x hx hc,
    have hx' : x ∈ (maximal_projection N).ker := (inf_le_left : _ ⊓ N ≤ _) hx,
    rw linear_map.mem_ker at hx',
    simpa [maximal_gen_ne_zero hb hN, hx'] using congr_arg (maximal_projection N) hc }
    -/
end

lemma submodule.exists_is_basis_of_le {ι : Type*} [fintype ι]
  {N O : submodule R M} (hNO : N ≤ O) {b : ι → O} (hb : is_basis R b) :
  ∃ (n : ℕ) (b : fin n → N), is_basis R b :=
let ⟨n, bN', hbN'⟩ := submodule.exists_is_basis hb (N.comap O.subtype)
in ⟨n, _, (submodule.comap_subtype_equiv_of_le hNO).is_basis hbN'⟩

lemma submodule.exists_is_basis_of_le_span
  {ι : Type*} [fintype ι] {b : ι → M} (hb : linear_independent R b)
  {N : submodule R M} (le : N ≤ submodule.span R (set.range b)) :
  ∃ (n : ℕ) (b : fin n → N), is_basis R b :=
submodule.exists_is_basis_of_le le (is_basis_span hb)

end principal_ideal_domain

end principal_ideal_domain
