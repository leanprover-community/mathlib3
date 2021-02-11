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
We express "free `R`-module of finite rank" as a module `M` which has a basis
`b : ι → R`, where `ι` is a `fintype`.
We call the cardinality of `ι` the rank of `M` in this file;
it would be equal to `findim R M` if `R` is a field and `M` is a vector space.

## Main results

 - `submodule.induction_on_rank`: if `M` is free and finitely generated,
   if `P` holds for `⊥ : submodule R M` and if `P N` follows from `P N'`
   for all `N'` that are of lower rank, then `P` holds on all submodules

 - `submodule.exists_is_basis`: if `M` is free and finitely generated
   and `R` is a PID, then `N : submodule R M` is free and finitely generated.
   This is the first part of the structure theorem for modules.

## Tags

free module, finitely generated module, rank, structure theorem

-/

open_locale big_operators

section comm_ring

universes u v

variables {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
variables {ι : Type*} {b : ι → M} (hb : is_basis R b)

open submodule.is_principal

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

open submodule

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

-- Note that the converse may not hold if `ϕ` is not injective.
lemma generator_map_dvd_of_mem {N : submodule R M}
  (ϕ : M →ₗ[R] R) [(N.map ϕ).is_principal] {x : M} (hx : x ∈ N) :
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
  convert hli.fin_cons' x _ _,
  { ext i, refine fin.cases _ _ i; simp },
  { intros c y hcy,
    refine x_ortho c y (submodule.span_le.mpr _ y.2) hcy,
    rintros _ ⟨z, rfl⟩,
    exact (v z).2 }
end

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

open submodule.is_principal

end integral_domain

section principal_ideal_domain

open submodule.is_principal

variables {ι : Type*} {R : Type*} [integral_domain R] [is_principal_ideal_ring R]
variables {M : Type*} [add_comm_group M] [module R M] {b : ι → M}

open_locale matrix

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain. -/
theorem submodule.exists_is_basis {ι : Type*} [fintype ι]
  {b : ι → M} (hb : is_basis R b) (N : submodule R M) :
  ∃ (n : ℕ) (bN : fin n → N), is_basis R bN :=
begin
  haveI := classical.dec_eq M,
  refine N.induction_on_rank hb _ _,
  intros N ih,

  -- Let `ϕ` be a maximal projection of `M` onto `R`, in the sense that there is
  -- no `ψ` whose image of `N` is larger than `ϕ`'s image of `N`.
  obtain ⟨ϕ, ϕ_max⟩ : ∃ ϕ : M →ₗ[R] R, ∀ (ψ : M →ₗ[R] R), N.map ϕ ≤ N.map ψ → N.map ψ = N.map ϕ,
  { obtain ⟨P, P_eq, P_max⟩ := set_has_maximal_iff_noetherian.mpr
        (infer_instance : is_noetherian R R) _ (submodule.range_map_nonempty N),
    obtain ⟨ϕ, rfl⟩ := set.mem_range.mp P_eq,
    use ϕ,
    intros ψ hψ,
    exact P_max (N.map ψ) ⟨_, rfl⟩ hψ },
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

  -- We claim that `ϕ⁻¹ a = y` can be taken as basis element of `N`.
  obtain ⟨y, y_mem, ϕy_eq⟩ := a_mem,
  have ϕy_ne_zero := λ h, a_zero (ϕy_eq.symm.trans h),

  -- If `N'` is `ker (ϕ : N → R)`, it is smaller than `N` so by the induction hypothesis,
  -- it has a basis `bN'`.
  have N'_le_ker : (ϕ.ker ⊓ N) ≤ ϕ.ker := inf_le_left,
  have N'_le_N : (ϕ.ker ⊓ N) ≤ N := inf_le_right,
  -- Note that `y` is orthogonal to `N'`.
  have y_ortho_N' : ∀ (c : R) (z : M), z ∈ ϕ.ker ⊓ N → c • y + z = 0 → c = 0,
  { intros c x hx hc,
    have hx' : x ∈ ϕ.ker := (inf_le_left : _ ⊓ N ≤ _) hx,
    rw linear_map.mem_ker at hx',
    simpa [ϕy_ne_zero, hx'] using congr_arg ϕ hc },
  obtain ⟨nN', bN', hbN'⟩ := ih (ϕ.ker ⊓ N) N'_le_N y y_mem y_ortho_N',
  use nN'.succ,

  -- Extend `bN'` with `y`, we'll show it's linear independent and spans `N`.
  use fin.cons ⟨y, y_mem⟩ (submodule.of_le N'_le_N ∘ bN'),
  split,
  { apply (hbN'.1.map' (submodule.of_le N'_le_N) (submodule.ker_of_le _ _ _)).fin_cons' _ _ _,
    intros c z hc,
    apply y_ortho_N' c z (submodule.mem_inf.mpr ⟨_, z.1.2⟩) (congr_arg coe hc),
    have : submodule.span R (set.range (submodule.of_le N'_le_N ∘ bN')) ≤ (ϕ.dom_restrict N).ker,
    { rw submodule.span_le,
      rintros _ ⟨i, rfl⟩,
      exact N'_le_ker (bN' i).2 },
    exact this z.2 },
  { rw eq_top_iff,
    rintro x -,
    rw [fin.range_cons, set.range_comp, submodule.mem_span_insert, submodule.span_image],
    obtain ⟨b, hb⟩ : _ ∣ ϕ x := generator_map_dvd_of_mem ϕ x.2,
    refine ⟨b, x - b • ⟨_, y_mem⟩, _, _⟩,
    { rw submodule.mem_map,
      refine ⟨⟨x - b • _, _⟩, hbN'.mem_span _, rfl⟩,
      refine submodule.mem_inf.mpr ⟨linear_map.mem_ker.mpr _, N.sub_mem x.2 (N.smul_mem _ y_mem)⟩,
      simp [hb, ϕy_eq, mul_comm] },
    { ext, simp only [ϕy_eq, add_sub_cancel'_right] } },
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
