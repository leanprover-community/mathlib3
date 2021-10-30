/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import linear_algebra.finsupp_vector_space
import ring_theory.principal_ideal_domain
import ring_theory.finiteness

/-! # Free modules over PID

A free `R`-module `M` is a module with a basis over `R`,
equivalently it is an `R`-module linearly equivalent to `ι →₀ R` for some `ι`.

This file proves a submodule of a free `R`-module of finite rank is also
a free `R`-module of finite rank, if `R` is a principal ideal domain (PID),
i.e. we have instances `[is_domain R] [is_principal_ideal_ring R]`.
We express "free `R`-module of finite rank" as a module `M` which has a basis
`b : ι → R`, where `ι` is a `fintype`.
We call the cardinality of `ι` the rank of `M` in this file;
it would be equal to `finrank R M` if `R` is a field and `M` is a vector space.

## Main results

In this section, `M` is a free and finitely generated `R`-module, and
`N` is a submodule of `M`.

 - `submodule.induction_on_rank`: if `P` holds for `⊥ : submodule R M` and if
  `P N` follows from `P N'` for all `N'` that are of lower rank, then `P` holds
   on all submodules

 - `submodule.exists_basis_of_pid`: if `R` is a PID, then `N : submodule R M` is
   free and finitely generated. This is the first part of the structure theorem
   for modules.

- `submodule.smith_normal_form`: if `R` is a PID, then `M` has a basis
  `bM` and `N` has a basis `bN` such that `bN i = a i • bM i`.
  Equivalently, a linear map `f : M →ₗ M` with `range f = N` can be written as
  a matrix in Smith normal form, a diagonal matrix with the coefficients `a i`
  along the diagonal.

## Tags

free module, finitely generated module, rank, structure theorem

-/

open_locale big_operators

universes u v

section ring

variables {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M]
variables {ι : Type*} (b : basis ι R M)

open submodule.is_principal submodule

lemma eq_bot_of_generator_maximal_map_eq_zero (b : basis ι R M) {N : submodule R M}
  {ϕ : M →ₗ[R] R} (hϕ : ∀ (ψ : M →ₗ[R] R), N.map ϕ ≤ N.map ψ → N.map ψ = N.map ϕ)
  [(N.map ϕ).is_principal] (hgen : generator (N.map ϕ) = 0) : N = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  intros x hx,
  refine b.ext_elem (λ i, _),
  rw (eq_bot_iff_generator_eq_zero _).mpr hgen at hϕ,
  rw [linear_equiv.map_zero, finsupp.zero_apply],
  exact (submodule.eq_bot_iff _).mp (hϕ ((finsupp.lapply i) ∘ₗ ↑b.repr) bot_le) _ ⟨x, hx, rfl⟩
end

lemma eq_bot_of_generator_maximal_submodule_image_eq_zero {N O : submodule R M} (b : basis ι R O)
  (hNO : N ≤ O)
  {ϕ : O →ₗ[R] R} (hϕ : ∀ (ψ : O →ₗ[R] R), ϕ.submodule_image N ≤ ψ.submodule_image N →
    ψ.submodule_image N = ϕ.submodule_image N)
  [(ϕ.submodule_image N).is_principal] (hgen : generator (ϕ.submodule_image N) = 0) :
  N = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  intros x hx,
  refine congr_arg coe (show (⟨x, hNO hx⟩ : O) = 0, from b.ext_elem (λ i, _)),
  rw (eq_bot_iff_generator_eq_zero _).mpr hgen at hϕ,
  rw [linear_equiv.map_zero, finsupp.zero_apply],
  refine (submodule.eq_bot_iff _).mp (hϕ ((finsupp.lapply i) ∘ₗ ↑b.repr) bot_le) _ _,
  exact (linear_map.mem_submodule_image_of_le hNO).mpr ⟨x, hx, rfl⟩
end

end ring

section is_domain

variables {ι : Type*} {R : Type*} [comm_ring R] [is_domain R]
variables {M : Type*} [add_comm_group M] [module R M] {b : ι → M}

open submodule.is_principal set submodule

lemma dvd_generator_iff {I : ideal R} [I.is_principal] {x : R} (hx : x ∈ I) :
  x ∣ generator I ↔ I = ideal.span {x} :=
begin
  conv_rhs { rw [← span_singleton_generator I] },
  erw [ideal.span_singleton_eq_span_singleton, ← dvd_dvd_iff_associated, ← mem_iff_generator_dvd],
  exact ⟨λ h, ⟨hx, h⟩, λ h, h.2⟩
end

end is_domain

section principal_ideal_domain

open submodule.is_principal set submodule

variables {ι : Type*} {R : Type*} [comm_ring R] [is_domain R] [is_principal_ideal_ring R]
variables {M : Type*} [add_comm_group M] [module R M] {b : ι → M}

open submodule.is_principal

lemma generator_maximal_submodule_image_dvd {N O : submodule R M} (hNO : N ≤ O)
  {ϕ : O →ₗ[R] R} (hϕ : ∀ (ψ : O →ₗ[R] R), ϕ.submodule_image N ≤ ψ.submodule_image N →
    ψ.submodule_image N = ϕ.submodule_image N)
  [(ϕ.submodule_image N).is_principal]
  (y : M) (yN : y ∈ N) (ϕy_eq : ϕ ⟨y, hNO yN⟩ = generator (ϕ.submodule_image N))
  (ψ : O →ₗ[R] R) : generator (ϕ.submodule_image N) ∣ ψ ⟨y, hNO yN⟩ :=
begin
  let a : R := generator (ϕ.submodule_image N),
  let d : R := is_principal.generator (submodule.span R {a, ψ ⟨y, hNO yN⟩}),
  have d_dvd_left : d ∣ a := (mem_iff_generator_dvd _).mp
    (subset_span (mem_insert _ _)),
  have d_dvd_right : d ∣ ψ ⟨y, hNO yN⟩ := (mem_iff_generator_dvd _).mp
    (subset_span (mem_insert_of_mem _ (mem_singleton _))),
  refine dvd_trans _ d_dvd_right,
  rw [dvd_generator_iff, ideal.span,
      ← span_singleton_generator (submodule.span R {a, ψ ⟨y, hNO yN⟩})],
  obtain ⟨r₁, r₂, d_eq⟩ : ∃ r₁ r₂ : R, d = r₁ * a + r₂ * ψ ⟨y, hNO yN⟩,
  { obtain ⟨r₁, r₂', hr₂', hr₁⟩ := mem_span_insert.mp (is_principal.generator_mem
      (submodule.span R {a, ψ ⟨y, hNO yN⟩})),
    obtain ⟨r₂, rfl⟩ := mem_span_singleton.mp hr₂',
    exact ⟨r₁, r₂, hr₁⟩ },
  let ψ' : O →ₗ[R] R := r₁ • ϕ + r₂ • ψ,
  have : span R {d} ≤ ψ'.submodule_image N,
  { rw [span_le, singleton_subset_iff, set_like.mem_coe, linear_map.mem_submodule_image_of_le hNO],
    refine ⟨y, yN, _⟩,
    change r₁ * ϕ ⟨y, hNO yN⟩ + r₂ * ψ ⟨y, hNO yN⟩ = d,
    rw [d_eq, ϕy_eq] },
  refine le_antisymm (this.trans (le_of_eq _))
    (ideal.span_singleton_le_span_singleton.mpr d_dvd_left),
  rw span_singleton_generator,
  refine hϕ ψ' (le_trans _ this),
  rw [← span_singleton_generator (ϕ.submodule_image N)],
  exact ideal.span_singleton_le_span_singleton.mpr d_dvd_left,
  { exact subset_span (mem_insert _ _) }
end

/-- The induction hypothesis of `submodule.basis_of_pid` and `submodule.smith_normal_form`.

Basically, it says: let `N ≤ M` be a pair of submodules, then we can find a pair of
submodules `N' ≤ M'` of strictly smaller rank, whose basis we can extend to get a basis
of `N` and `M`. Moreover, if the basis for `M'` is up to scalars a basis for `N'`,
then the basis we find for `M` is up to scalars a basis for `N`.

For `basis_of_pid` we only need the first half and can fix `M = ⊤`,
for `smith_normal_form` we need the full statement,
but must also feed in a basis for `M` using `basis_of_pid` to keep the induction going.
-/
lemma submodule.basis_of_pid_aux [fintype ι] {O : Type*} [add_comm_group O] [module R O]
  (M N : submodule R O) (b'M : basis ι R M) (N_bot : N ≠ ⊥) (N_le_M : N ≤ M) :
  ∃ (y ∈ M) (a : R) (hay : a • y ∈ N) (M' ≤ M) (N' ≤ N) (N'_le_M' : N' ≤ M')
    (y_ortho_M' : ∀ (c : R) (z : O), z ∈ M' → c • y + z = 0 → c = 0)
    (ay_ortho_N' : ∀ (c : R) (z : O), z ∈ N' → c • a • y + z = 0 → c = 0),
  ∀ (n') (bN' : basis (fin n') R N'), ∃ (bN : basis (fin (n' + 1)) R N),
  ∀ (m') (hn'm' : n' ≤ m') (bM' : basis (fin m') R M'),
  ∃ (hnm : (n' + 1) ≤ (m' + 1)) (bM : basis (fin (m' + 1)) R M),
  ∀ (as : fin n' → R) (h : ∀ (i : fin n'), (bN' i : O) = as i • (bM' (fin.cast_le hn'm' i) : O)),
  ∃ (as' : fin (n' + 1) → R),
  ∀ (i : fin (n' + 1)), (bN i : O) = as' i • (bM (fin.cast_le hnm i) : O) :=
begin
  -- Let `ϕ` be a maximal projection of `M` onto `R`, in the sense that there is
  -- no `ψ` whose image of `N` is larger than `ϕ`'s image of `N`.
  have : ∃ ϕ : M →ₗ[R] R, ∀ (ψ : M →ₗ[R] R),
    ϕ.submodule_image N ≤ ψ.submodule_image N → ψ.submodule_image N = ϕ.submodule_image N,
  { obtain ⟨P, P_eq, P_max⟩ := set_has_maximal_iff_noetherian.mpr
        (infer_instance : is_noetherian R R) _
        (show (set.range (λ ψ : M →ₗ[R] R, ψ.submodule_image N)).nonempty,
         from ⟨_, set.mem_range.mpr ⟨0, rfl⟩⟩),
    obtain ⟨ϕ, rfl⟩ := set.mem_range.mp P_eq,
    exact ⟨ϕ, λ ψ hψ, P_max _ ⟨_, rfl⟩ hψ⟩ },
  let ϕ := this.some,
  have ϕ_max := this.some_spec,
  -- Since `ϕ(N)` is a `R`-submodule of the PID `R`,
  -- it is principal and generated by some `a`.
  let a := generator (ϕ.submodule_image N),
  have a_mem : a ∈ ϕ.submodule_image N := generator_mem _,

  -- If `a` is zero, then the submodule is trivial. So let's assume `a ≠ 0`, `N ≠ ⊥`.
  by_cases a_zero : a = 0,
  { have := eq_bot_of_generator_maximal_submodule_image_eq_zero b'M N_le_M ϕ_max a_zero,
    contradiction },

  -- We claim that `ϕ⁻¹ a = y` can be taken as basis element of `N`.
  obtain ⟨y, yN, ϕy_eq⟩ := (linear_map.mem_submodule_image_of_le N_le_M).mp a_mem,
  have ϕy_ne_zero : ϕ ⟨y, N_le_M yN⟩ ≠ 0 := λ h, a_zero (ϕy_eq.symm.trans h),
  -- Write `y` as `a • y'` for some `y'`.
  have hdvd : ∀ i, a ∣ b'M.coord i ⟨y, N_le_M yN⟩ :=
    λ i, generator_maximal_submodule_image_dvd N_le_M ϕ_max y yN ϕy_eq (b'M.coord i),
  choose c hc using hdvd,
  let y' : O := ∑ i, c i • b'M i,
  have y'M : y' ∈ M := M.sum_mem (λ i _, M.smul_mem (c i) (b'M i).2),
  have mk_y' : (⟨y', y'M⟩ : M) = ∑ i, c i • b'M i :=
    subtype.ext (show y' = M.subtype _,
      by { simp only [linear_map.map_sum, linear_map.map_smul], refl }),
  have a_smul_y' : a • y' = y,
  { refine congr_arg coe (show (a • ⟨y', y'M⟩ : M) = ⟨y, N_le_M yN⟩, from _),
    rw [← b'M.sum_repr ⟨y, N_le_M yN⟩, mk_y', finset.smul_sum],
    refine finset.sum_congr rfl (λ i _, _),
    rw [← mul_smul, ← hc], refl },
  -- We found an `y` and an `a`!
  refine ⟨y', y'M, a, a_smul_y'.symm ▸ yN, _⟩,

  have ϕy'_eq : ϕ ⟨y', y'M⟩ = 1 := mul_left_cancel₀ a_zero
  (calc a • ϕ ⟨y', y'M⟩ = ϕ ⟨a • y', _⟩ : (ϕ.map_smul a ⟨y', y'M⟩).symm
                    ... = ϕ ⟨y, N_le_M yN⟩ : by simp only [a_smul_y']
                    ... = a : ϕy_eq
                    ... = a * 1 : (mul_one a).symm),
  have ϕy'_ne_zero : ϕ ⟨y', y'M⟩ ≠ 0 := by simpa only [ϕy'_eq] using one_ne_zero,

  -- `M' := ker (ϕ : M → R)` is smaller than `M` and `N' := ker (ϕ : N → R)` is smaller than `N`.
  let M' : submodule R O := ϕ.ker.map M.subtype,
  let N' : submodule R O := (ϕ.comp (of_le N_le_M)).ker.map N.subtype,
  have M'_le_M : M' ≤ M := M.map_subtype_le ϕ.ker,
  have N'_le_M' : N' ≤ M',
  { intros x hx,
    simp only [mem_map, linear_map.mem_ker] at hx ⊢,
    obtain ⟨⟨x, xN⟩, hx, rfl⟩ := hx,
    exact ⟨⟨x, N_le_M xN⟩, hx, rfl⟩ },
  have N'_le_N : N' ≤ N := N.map_subtype_le (ϕ.comp (of_le N_le_M)).ker,
  -- So fill in those results as well.
  refine ⟨M', M'_le_M, N', N'_le_N, N'_le_M', _⟩,

  -- Note that `y'` is orthogonal to `M'`.
  have y'_ortho_M' : ∀ (c : R) z ∈ M', c • y' + z = 0 → c = 0,
  { intros c x xM' hc,
    obtain ⟨⟨x, xM⟩, hx', rfl⟩ := submodule.mem_map.mp xM',
    rw linear_map.mem_ker at hx',
    have hc' : (c • ⟨y', y'M⟩ + ⟨x, xM⟩ : M) = 0 := subtype.coe_injective hc,
    simpa only [linear_map.map_add, linear_map.map_zero, linear_map.map_smul, smul_eq_mul, add_zero,
                mul_eq_zero, ϕy'_ne_zero, hx', or_false] using congr_arg ϕ hc' },
  -- And `a • y'` is orthogonal to `N'`.
  have ay'_ortho_N' : ∀ (c : R) z ∈ N', c • a • y' + z = 0 → c = 0,
  { intros c z zN' hc,
    refine (mul_eq_zero.mp (y'_ortho_M' (a * c) z (N'_le_M' zN') _)).resolve_left a_zero,
    rw [mul_comm, mul_smul, hc] },

  -- So we can extend a basis for `N'` with `y`
  refine ⟨y'_ortho_M', ay'_ortho_N', λ n' bN', ⟨_, _⟩⟩,
  { refine basis.mk_fin_cons_of_le y yN bN' N'_le_N _ _,
    { intros c z zN' hc,
      refine ay'_ortho_N' c z zN' _,
      rwa ← a_smul_y' at hc },
    { intros z zN,
      obtain ⟨b, hb⟩ : _ ∣ ϕ ⟨z, N_le_M zN⟩ := generator_submodule_image_dvd_of_mem N_le_M ϕ zN,
      refine ⟨-b, submodule.mem_map.mpr ⟨⟨_, N.sub_mem zN (N.smul_mem b yN)⟩, _, _⟩⟩,
      { refine linear_map.mem_ker.mpr (show ϕ (⟨z, N_le_M zN⟩ - b • ⟨y, N_le_M yN⟩) = 0, from _),
        rw [linear_map.map_sub, linear_map.map_smul, hb, ϕy_eq, smul_eq_mul,
            mul_comm, sub_self] },
      { simp only [sub_eq_add_neg, neg_smul], refl } } },
  -- And extend a basis for `M'` with `y'`
  intros m' hn'm' bM',
  refine ⟨nat.succ_le_succ hn'm', _, _⟩,
  { refine basis.mk_fin_cons_of_le y' y'M bM' M'_le_M y'_ortho_M' _,
    intros z zM,
    refine ⟨-ϕ ⟨z, zM⟩, ⟨⟨z, zM⟩ - (ϕ ⟨z, zM⟩) • ⟨y', y'M⟩, linear_map.mem_ker.mpr _, _⟩⟩,
    { rw [linear_map.map_sub, linear_map.map_smul, ϕy'_eq, smul_eq_mul, mul_one, sub_self] },
    { rw [linear_map.map_sub, linear_map.map_smul, sub_eq_add_neg, neg_smul], refl } },

  -- It remains to show the extended bases are compatible with each other.
  intros as h,
  refine ⟨fin.cons a as, _⟩,
  intro i,
  rw [basis.coe_mk_fin_cons_of_le, basis.coe_mk_fin_cons_of_le],
  refine fin.cases _ (λ i, _) i,
  { simp only [fin.cons_zero, fin.cast_le_zero],
    exact a_smul_y'.symm },
  { rw fin.cast_le_succ, simp only [fin.cons_succ, coe_of_le, h i] }
end

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

This is a `lemma` to make the induction a bit easier. To actually access the basis,
see `submodule.basis_of_pid`.

See also the stronger version `submodule.smith_normal_form`.
-/
lemma submodule.nonempty_basis_of_pid {ι : Type*} [fintype ι]
  (b : basis ι R M) (N : submodule R M) :
  ∃ (n : ℕ), nonempty (basis (fin n) R N) :=
begin
  haveI := classical.dec_eq M,
  refine N.induction_on_rank b _ _,
  intros N ih,
  let b' := (b.reindex (fintype.equiv_fin ι)).map (linear_equiv.of_top _ rfl).symm,
  by_cases N_bot : N = ⊥,
  { subst N_bot, exact ⟨0, ⟨basis.empty _⟩⟩ },
  obtain ⟨y, -, a, hay, M', -, N', N'_le_N, -, -, ay_ortho, h'⟩ :=
    submodule.basis_of_pid_aux ⊤ N b' N_bot le_top,
  obtain ⟨n', ⟨bN'⟩⟩ := ih N' N'_le_N _ hay ay_ortho,
  obtain ⟨bN, hbN⟩ := h' n' bN',
  exact ⟨n' + 1, ⟨bN⟩⟩
end

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

See also the stronger version `submodule.smith_normal_form`.
-/
noncomputable def submodule.basis_of_pid {ι : Type*} [fintype ι]
  (b : basis ι R M) (N : submodule R M) :
  Σ (n : ℕ), (basis (fin n) R N) :=
⟨_, (N.nonempty_basis_of_pid b).some_spec.some⟩

lemma submodule.basis_of_pid_bot {ι : Type*} [fintype ι] (b : basis ι R M) :
  submodule.basis_of_pid b ⊥ = ⟨0, basis.empty _⟩ :=
begin
  obtain ⟨n, b'⟩ := submodule.basis_of_pid b ⊥,
  let e : fin n ≃ fin 0 := b'.index_equiv (basis.empty _ : basis (fin 0) R (⊥ : submodule R M)),
  have : n = 0 := by simpa using fintype.card_eq.mpr ⟨e⟩,
  subst this,
  exact sigma.eq rfl (basis.eq_of_apply_eq $ fin_zero_elim)
end

/-- A submodule inside a free `R`-submodule of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

See also the stronger version `submodule.smith_normal_form_of_le`.
-/
noncomputable def submodule.basis_of_pid_of_le {ι : Type*} [fintype ι]
  {N O : submodule R M} (hNO : N ≤ O) (b : basis ι R O) :
  Σ (n : ℕ), basis (fin n) R N :=
let ⟨n, bN'⟩ := submodule.basis_of_pid b (N.comap O.subtype)
in ⟨n, bN'.map (submodule.comap_subtype_equiv_of_le hNO)⟩

/-- A submodule inside the span of a linear independent family is a free `R`-module of finite rank,
if `R` is a principal ideal domain. -/
noncomputable def submodule.basis_of_pid_of_le_span
  {ι : Type*} [fintype ι] {b : ι → M} (hb : linear_independent R b)
  {N : submodule R M} (le : N ≤ submodule.span R (set.range b)) :
  Σ (n : ℕ), basis (fin n) R N :=
submodule.basis_of_pid_of_le le (basis.span hb)

variable {M}

/-- A finite type torsion free module over a PID is free. -/
noncomputable def module.free_of_finite_type_torsion_free [fintype ι] {s : ι → M}
  (hs : span R (range s) = ⊤) [no_zero_smul_divisors R M] :
  Σ (n : ℕ), basis (fin n) R M :=
begin
  classical,
  -- We define `N` as the submodule spanned by a maximal linear independent subfamily of `s`
  have := exists_maximal_independent R s,
  let I : set ι := this.some,
  obtain ⟨indepI : linear_independent R (s ∘ coe : I → M),
    hI : ∀ i ∉ I, ∃ a : R, a ≠ 0 ∧ a • s i ∈ span R (s '' I)⟩ := this.some_spec,

  let N := span R (range $ (s ∘ coe : I → M)), -- same as `span R (s '' I)` but more convenient
  let sI : I → N := λ i, ⟨s i.1, subset_span (mem_range_self i)⟩, -- `s` restricted to `I`
  let sI_basis : basis I R N, -- `s` restricted to `I` is a basis of `N`
    from basis.span indepI,
  -- Our first goal is to build `A ≠ 0` such that `A • M ⊆ N`
  have exists_a : ∀ i : ι, ∃ a : R, a ≠ 0 ∧ a • s i ∈ N,
  { intro i,
    by_cases hi : i ∈ I,
    { use [1, zero_ne_one.symm],
      rw one_smul,
      exact subset_span (mem_range_self (⟨i, hi⟩ : I)) },
    { simpa [image_eq_range s I] using hI i hi } },
  choose a ha ha' using exists_a,
  let A := ∏ i, a i,
  have hA : A ≠ 0,
  { rw finset.prod_ne_zero_iff,
    simpa using ha },
  -- `M ≃ A • M` because `M` is torsion free and `A ≠ 0`
  let φ : M →ₗ[R] M := linear_map.lsmul R M A,
  have : φ.ker = ⊥,
    from linear_map.ker_lsmul hA,
  let ψ : M ≃ₗ[R] φ.range := linear_equiv.of_injective φ (linear_map.ker_eq_bot.mp this),
  have : φ.range ≤ N, -- as announced, `A • M ⊆ N`
  { suffices : ∀ i, φ (s i) ∈ N,
    { rw [linear_map.range_eq_map, ← hs, φ.map_span_le],
      rintros _ ⟨i, rfl⟩, apply this },
    intro i,
    calc (∏ j, a j) • s i = (∏ j in {i}ᶜ, a j) • a i • s i :
                                                 by rw [fintype.prod_eq_prod_compl_mul i, mul_smul]
                      ... ∈ N  : N.smul_mem _ (ha' i) },
  -- Since a submodule of a free `R`-module is free, we get that `A • M` is free
  obtain ⟨n, b : basis (fin n) R φ.range⟩ := submodule.basis_of_pid_of_le this sI_basis,
  -- hence `M` is free.
  exact ⟨n, b.map ψ.symm⟩
end

/-- A finite type torsion free module over a PID is free. -/
noncomputable def module.free_of_finite_type_torsion_free' [module.finite R M]
  [no_zero_smul_divisors R M] :
  Σ (n : ℕ), basis (fin n) R M :=
module.free_of_finite_type_torsion_free module.finite.exists_fin.some_spec.some_spec

section smith_normal

/-- A Smith normal form basis for a submodule `N` of a module `M` consists of
bases for `M` and `N` such that the inclusion map `N → M` can be written as a
(rectangular) matrix with `a` along the diagonal: in Smith normal form. -/
@[nolint has_inhabited_instance]
structure basis.smith_normal_form (N : submodule R M) (ι : Type*) (n : ℕ) :=
(bM : basis ι R M)
(bN : basis (fin n) R N)
(f : fin n ↪ ι)
(a : fin n → R)
(snf : ∀ i, (bN i : M) = a i • bM (f i))

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

See `submodule.smith_normal_form_of_le` for a version of this theorem that returns
a `basis.smith_normal_form`.

This is a strengthening of `submodule.basis_of_pid_of_le`.
-/
theorem submodule.exists_smith_normal_form_of_le [fintype ι]
  (b : basis ι R M) (N O : submodule R M) (N_le_O : N ≤ O) :
  ∃ (n o : ℕ) (hno : n ≤ o) (bO : basis (fin o) R O) (bN : basis (fin n) R N) (a : fin n → R),
    ∀ i, (bN i : M) = a i • bO (fin.cast_le hno i) :=
begin
  revert N,
  refine induction_on_rank b _ _ O,
  intros M ih N N_le_M,
  obtain ⟨m, b'M⟩ := M.basis_of_pid b,
  by_cases N_bot : N = ⊥,
  { subst N_bot,
    exact ⟨0, m, nat.zero_le _, b'M, basis.empty _, fin_zero_elim, fin_zero_elim⟩ },

  obtain ⟨y, hy, a, hay, M', M'_le_M, N', N'_le_N, N'_le_M', y_ortho, ay_ortho, h⟩ :=
    submodule.basis_of_pid_aux M N b'M N_bot N_le_M,
  obtain ⟨n', m', hn'm', bM', bN', as', has'⟩ := ih M' M'_le_M y hy y_ortho N' N'_le_M',
  obtain ⟨bN, h'⟩ := h n' bN',
  obtain ⟨hmn, bM, h''⟩ := h' m' hn'm' bM',
  obtain ⟨as, has⟩ := h'' as' has',
  exact ⟨_, _, hmn, bM, bN, as, has⟩
end

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

See `submodule.exists_smith_normal_form_of_le` for a version of this theorem that doesn't
need to map `N` into a submodule of `O`.

This is a strengthening of `submodule.basis_of_pid_of_le`.
-/
noncomputable def submodule.smith_normal_form_of_le [fintype ι]
  (b : basis ι R M) (N O : submodule R M) (N_le_O : N ≤ O) :
  Σ (o n : ℕ), basis.smith_normal_form (N.comap O.subtype) (fin o) n :=
begin
  choose n o hno bO bN a snf using N.exists_smith_normal_form_of_le b O N_le_O,
  refine ⟨o, n, bO, bN.map (comap_subtype_equiv_of_le N_le_O).symm, (fin.cast_le hno).to_embedding,
          a, λ i, _⟩,
  ext,
  simp only [snf, basis.map_apply, submodule.comap_subtype_equiv_of_le_symm_apply_coe_coe,
      submodule.coe_smul_of_tower, rel_embedding.coe_fn_to_embedding]
end

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

This is a strengthening of `submodule.basis_of_pid`.

See also `ideal.smith_normal_form`, which moreover proves that the dimension of
an ideal is the same as the dimension of the whole ring.
-/
noncomputable def submodule.smith_normal_form [fintype ι] (b : basis ι R M) (N : submodule R M) :
  Σ (n : ℕ), basis.smith_normal_form N ι n :=
let ⟨m, n, bM, bN, f, a, snf⟩ := N.smith_normal_form_of_le b ⊤ le_top,
    bM' := bM.map (linear_equiv.of_top _ rfl),
    e := bM'.index_equiv b in
⟨n, bM'.reindex e, bN.map (comap_subtype_equiv_of_le le_top), f.trans e.to_embedding, a,
 λ i, by simp only [snf, basis.map_apply, linear_equiv.of_top_apply, submodule.coe_smul_of_tower,
                    submodule.comap_subtype_equiv_of_le_apply_coe, coe_coe, basis.reindex_apply,
                    equiv.to_embedding_apply, function.embedding.trans_apply,
                    equiv.symm_apply_apply]⟩

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.

See `ideal.exists_smith_normal_form` for a version of this theorem that doesn't
need to map `I` into a submodule of `R`.

This is a strengthening of `submodule.basis_of_pid`.
-/
noncomputable def ideal.smith_normal_form
  [fintype ι] {S : Type*} [comm_ring S] [is_domain S] [algebra R S]
  (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  basis.smith_normal_form (I.restrict_scalars R) ι (fintype.card ι) :=
let ⟨n, bS, bI, f, a, snf⟩ := (I.restrict_scalars R).smith_normal_form b in
have eq : _ := ideal.rank_eq bS hI (bI.map ((restrict_scalars_equiv R S S I).restrict_scalars _)),
let e : fin n ≃ fin (fintype.card ι) := fintype.equiv_of_card_eq (by rw [eq, fintype.card_fin]) in
⟨bS, bI.reindex e, e.symm.to_embedding.trans f, a ∘ e.symm, λ i,
  by simp only [snf, basis.coe_reindex, function.embedding.trans_apply, equiv.to_embedding_apply]⟩

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.

See also `ideal.smith_normal_form` for a version of this theorem that returns
a `basis.smith_normal_form`.
-/
theorem ideal.exists_smith_normal_form
  [fintype ι] {S : Type*} [comm_ring S] [is_domain S] [algebra R S]
  (b : basis ι R S) (I : ideal S) (hI : I ≠ ⊥) :
  ∃ (b' : basis ι R S) (a : ι → R) (ab' : basis ι R I),
  ∀ i, (ab' i : S) = a i • b' i :=
let ⟨bS, bI, f, a, snf⟩ := I.smith_normal_form b hI,
    e : fin (fintype.card ι) ≃ ι := equiv.of_bijective f
      ((fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, fintype.card_fin _⟩) in
have fe : ∀ i, f (e.symm i) = i := e.apply_symm_apply,
⟨bS, a ∘ e.symm, (bI.reindex e).map ((restrict_scalars_equiv _ _ _ _).restrict_scalars R), λ i,
  by simp only [snf, fe, basis.map_apply, linear_equiv.restrict_scalars_apply,
    submodule.restrict_scalars_equiv_apply, basis.coe_reindex]⟩

end smith_normal

end principal_ideal_domain

/-- A set of linearly independent vectors in a module `M` over a semiring `S` is also linearly
independent over a subring `R` of `K`. -/
lemma linear_independent.restrict_scalars_algebras {R S M ι : Type*} [comm_semiring R] [semiring S]
  [add_comm_monoid M] [algebra R S] [module R M] [module S M] [is_scalar_tower R S M]
  (hinj : function.injective (algebra_map R S)) {v : ι → M} (li : linear_independent S v) :
  linear_independent R v :=
linear_independent.restrict_scalars (by rwa algebra.algebra_map_eq_smul_one' at hinj) li
