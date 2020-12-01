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

lemma exists_is_basis_iff_exists_equiv {ι : Type v} :
  (∃ (b : ι → M), is_basis R b) ↔ nonempty (M ≃ₗ[R] (ι →₀ R)) :=
⟨λ ⟨b, hb⟩, ⟨module_equiv_finsupp hb⟩,
 λ ⟨e⟩, ⟨_, linear_equiv.is_basis finsupp.is_basis_single_one e.symm⟩⟩

end comm_ring

section principal_ideal_domain

variables {ι : Type*} {R : Type*} {M : Type*} [integral_domain R] [is_principal_ideal_ring R] [add_comm_group M] [module R M] {b : ι → M}

lemma not_nonempty_fin_zero : ¬ (nonempty (fin 0)) :=
λ ⟨i⟩, fin_zero_elim i

open submodule.is_principal

-- `n` is the rank of `M` and `m` is the rank of `N`; I copied this unfortunate notation from Dummit and Foote.

lemma mem_span_iff_exists_sum {b : set M} {x : M} :
  x ∈ submodule.span R b ↔ ∃ (s : finset M) (hs : ↑s ⊆ b) (c : M → R),
    x = ∑ i in s, c i • i :=
begin
  classical,
  split,
  { intro h,
    refine submodule.span_induction h _ _ _ _,
    { intros x hx,
      refine ⟨{x}, _, λ _, 1, _⟩,
      { simpa using hx },
      { simp } },
    { refine ⟨∅, _, λ _, 1, _⟩,
      { simp },
      { simp } },
    { rintro x y ⟨sx, hsx, cx, rfl⟩ ⟨sy, hsy, cy, rfl⟩,
      refine ⟨sx ∪ sy, _, λ i, (if i ∈ sx then cx i else 0) + if i ∈ sy then cy i else 0, _⟩,
      { simpa using and.intro hsx hsy },
      { sorry } },
    { rintro a x ⟨sx, hsx, cx, rfl⟩,
      refine ⟨sx, hsx, a • cx, _⟩,
      simp [finset.smul_sum, ← smul_assoc] } },
  { rintros ⟨s, hs, c, rfl⟩,
    apply submodule.sum_mem _ _,
    intros i hi,
    apply submodule.smul_mem _ _ _,
    exact submodule.subset_span (hs hi) }
end

lemma mem_span_range_iff_exists_sum {ι : Type*} [fintype ι] {b : ι → M} {x : M} :
  x ∈ submodule.span R (set.range b) ↔ ∃ (c : ι → R), x = ∑ i, c i • b i :=
by library_search

@[simp] lemma fin.cons_zero' {n : ℕ} (C : fin (n + 1) → Type*)
  (hi : 0 < n + 1) (a : C 0) (b : Π (i : fin n), C i.succ) :
  fin.cons a b ⟨0, hi⟩ = a := fin.cons_zero a b

@[simp] lemma fin.cons_succ' {i n : ℕ} (C : fin (n + 1) → Type*)
  (hi : i + 1 < n + 1) (a : C 0) (b : Π (i : fin n), C i.succ) :
  fin.cons a b ⟨i + 1, hi⟩ = b ⟨i, (add_lt_add_iff_right 1).mp hi⟩ :=
fin.cons_succ a b ⟨i, (add_lt_add_iff_right 1).mp hi⟩

lemma is_basis.fin_cons {n : ℕ} {x : M} {b : fin n → M} :
  is_basis R (fin.cons x b : fin n.succ → M) ↔
    (linear_independent R b ∧
     (∀ a : R, a • x ∈ submodule.span R (set.range b) → a = 0) ∧
     ∀ y : M, ∃ (a : R) (z ∈ submodule.span R (set.range b)), y = a • x + z) :=
begin
  rw ← and_assoc,
  apply and_congr,
  { rw [linear_independent_iff'', linear_independent_iff''],
    refine ⟨λ h, ⟨_, _⟩, λ h, _⟩,
    { intros s g hs hg i,
      rw [← h (s.image fin.succ) (fin.cons 0 g : fin n.succ → R) _ _ i.succ, fin.cons_succ],
      { simp only [finset.mem_image, not_exists],
        intros i,
        refine i.cases _ _,
        { intros, apply fin.cons_zero },
        { intros i hi,
          rw fin.cons_succ,
          exact hs i (λ h, hi _ h rfl) } },
      { simpa } },
    { intros a ha,
      obtain ⟨c, hx⟩ := mem_span_range_iff_exists_sum.mp ha,
      rw [← h finset.univ (fin.cons a (-c)) _ _ 0, fin.cons_zero],
      { rintro i hi,
        cases hi (finset.mem_univ i) },
      { rw [finset.sum_fin_eq_sum_range, finset.sum_range_succ', dif_pos n.zero_lt_succ],
        simp only [fin.cons_zero', fin.cons_succ', add_lt_add_iff_right],
        rw [finset.sum_dite, finset.sum_const_zero, add_zero],
        sorry } },
    { intros s g hs hg i,
      sorry } },
  { sorry },
end

lemma submodule.exists_is_basis_fin_zero (N : submodule R (fin 0 → R)) :
  ∃ (bN : fin 0 → N), is_basis R bN :=
begin
  refine ⟨λ _, 0, is_basis_empty not_nonempty_fin_zero _⟩,
  rintro ⟨x, hx⟩,
  ext i,
  exact fin_zero_elim i
end

/-- `hom_images N` is the set of all `R`-ideals that are the image of a submodule `N ≤ M` -/
def hom_images (N : submodule R M) : set (ideal R) :=
set.range (λ ϕ, N.map ϕ : (M →ₗ[R] R) → ideal R)

lemma nonempty_hom_images (N : submodule R M) : (hom_images N).nonempty :=
⟨_, set.mem_range.mpr ⟨0, rfl⟩⟩

/-- The (non-unique) map `ϕ` such that `N.map ϕ` is maximal along the set of `N.map _`. -/
noncomputable def maximal_projection (N : submodule R M) : M →ₗ[R] R :=
have _ := set_has_maximal_iff_noetherian.mpr
  (principal_ideal_ring.is_noetherian_ring : is_noetherian R R) _ (nonempty_hom_images N),
classical.some (set.mem_range.mp (classical.some (classical.some_spec this)))

/-- `maximal_projection` has a maximal image. -/
lemma maximal_projection_is_maximal (N : submodule R M) (ϕ : M →ₗ[R] R)
  (hϕ : N.map (maximal_projection N) ≤ N.map ϕ) : N.map ϕ = N.map (maximal_projection N) :=
begin
  have h := set_has_maximal_iff_noetherian.mpr
    (principal_ideal_ring.is_noetherian_ring : is_noetherian R R) _ (nonempty_hom_images N),
  have h1 := classical.some h,
  have h2 := classical.some_spec h,
  have h21 := classical.some h2,
  have h212 := classical.some_spec (set.mem_range.mp h21),
  have h22 := classical.some_spec h2,
  specialize h22 (N.map ϕ),
  rw ← h212 at h22,
  exact h22 ⟨_, rfl⟩ hϕ
end

/-- `maximal_gen N` is an element of `N` such that `maximal_projection N (maximal_gen N)` generates the image of `maximal_projection N`. -/
noncomputable def maximal_gen (N : submodule R M) : N :=
⟨classical.some (generator_mem (N.map (maximal_projection N))),
 (classical.some_spec (generator_mem (N.map (maximal_projection N)))).1⟩

@[simp] lemma maximal_projection_maximal_gen (N : submodule R M) :
  maximal_projection N (maximal_gen N) = generator (N.map (maximal_projection N)) :=
(classical.some_spec (generator_mem (N.map (maximal_projection N)))).2

lemma is_basis.ext_elem (hb : is_basis R b) {x y : M}
  (h : ∀ i, hb.repr x i = hb.repr y i) : x = y :=
by { rw [← hb.total_repr x, ← hb.total_repr y], congr' 1, ext i, exact h i }

lemma maximal_gen_ne_zero (hb : is_basis R b) {N : submodule R M} (hN : N ≠ ⊥) :
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
      ⟨maximal_gen N, (maximal_gen N).2, this⟩),
  have := maximal_projection_is_maximal N _ (le_trans le_S S_le),
  rw this at S_le,
  exact le_antisymm le_S S_le
end

/-- A submodule of `fin n → R` is also a free `R`-module of rank `m ≤ n`,
if `R` is a principal ideal domain. -/
lemma submodule.exists_is_basis_fin_aux {n : ℕ} (N : submodule R (fin n → R)) :
  ∃ (m : ℕ) (bN : fin m → N), is_basis R bN :=
begin
  induction n with n ih,
  { exact ⟨0, submodule.exists_is_basis_fin_zero N⟩ },

  -- The idea is to keep subtracting out a basis element of `M` and `N`,
  -- until we run out of basis elements for `N` (or for `M`, which implies we have run out for `N`).
  let π : fin n.succ → ((fin n.succ → R) →ₗ[R] R) :=
    λ i, ⟨λ x, x i, λ x y, pi.add_apply x y i, λ x y, pi.smul_apply y i x⟩,
  have π_apply : ∀ i x, π i x = x i := λ x i, rfl,

  -- Either `N` is trivial,
  -- or we can find `a : R`, `y : M` such that `M = y R ⊕ _` and `N = a • y R ⊕ _`.
  by_cases hN : N = ⊥,
  { rw hN,
    exact ⟨0, _, is_basis_empty_bot not_nonempty_fin_zero⟩ },

  have ha := maximal_gen_ne_zero (pi.is_basis_fun _ _) hN,

  have : ∀ ϕ : (fin n.succ → R) →ₗ[R] R, generator (N.map (maximal_projection N)) ∣ ϕ (maximal_gen N) :=
    generator_dvd_maximal_gen N,
  have : ∀ i, generator (N.map (maximal_projection N)) ∣ π i (maximal_gen N) := λ i, this (π i),
  let b : fin n.succ → R := λ i, classical.some (this i),
  have b_spec : ∀ i, π i (maximal_gen N) = generator (N.map (maximal_projection N)) * b i :=
    λ i, classical.some_spec (this i),
  -- We claim the following `y` can be a basis element of `M` such that `a • y` is a basis element of `N`.
  set y := ∑ i, b i • linear_map.std_basis R (λ _, R) i 1 with y_def,
  -- TODO: this should be easier!
  have y'_eq : ↑(maximal_gen N) = generator (N.map (maximal_projection N)) • y,
  { simp_rw [y_def, finset.smul_sum, ← smul_assoc, smul_eq_mul, ← b_spec, π_apply,
             ← pi.is_basis_fun_repr _ _ ↑(maximal_gen N)],
    apply ((pi.is_basis_fun R (fin n.succ)).total_repr (maximal_gen N)).symm.trans _,
    rw [finsupp.total_apply, finsupp.sum_fintype],
    simp },
  have ay_mem_N : generator (N.map (maximal_projection N)) • y ∈ N,
  { have : ↑(maximal_gen N) ∈ N := (maximal_gen N).2,
    rwa y'_eq at this },

  have : maximal_projection N y = 1,
  { apply mul_left_cancel' ha,
    conv_rhs { rw [mul_one, ← maximal_projection_maximal_gen N, y'_eq, linear_map.map_smul, smul_eq_mul] } },

  obtain ⟨m, bN'', hbN''⟩ : ∃ m (bN'' : fin m → ((maximal_projection N).dom_restrict N).ker), is_basis R bN'',
  { sorry },
  let bN' : fin m → N := λ i, ⟨bN'' i, _⟩,
  refine ⟨m.succ,
          fin.cons ⟨generator (N.map (maximal_projection N)) • y, ay_mem_N⟩ bN',
          is_basis.fin_cons.mpr ⟨_, _, _⟩⟩,
          
end

-- `n` is the rank of `M` and `m` is the rank of `N`; I copied this unfortunate notation from Dummit and Foote.
/-- A submodule of a free `R`-module of rank `n` is also a free `R`-module of rank `m ≤ n`,
if `R` is a principal ideal domain. -/
lemma submodule.exists_is_basis_fin {n : ℕ} (N : submodule R M)
  {b : fin n → M} (hb : is_basis R b) :
  ∃ (m : ℕ) (bN : fin m → N), is_basis R bN :=
sorry

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain. -/
lemma submodule.exists_is_basis {ι : Type*} [fintype ι]
  {b : ι → M} (hb : is_basis R b) (N : submodule R M) :
  ∃ (bN : finset N), is_basis R (λ (x : (↑ bN : set N)), (x : N)) :=
sorry

end principal_ideal_domain
