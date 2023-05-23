/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import linear_algebra.matrix.charpoly.coeff
import linear_algebra.matrix.to_lin

/-!

# Calyley-Hamilton theorem for f.g. modules.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a fixed finite spanning set `b : ι → M` of a `R`-module `M`, we say that a matrix `M`
represents an endomorphism `f : M →ₗ[R] M` if the matrix as an endomorphism of `ι → R` commutes
with `f` via the projection `(ι → R) →ₗ[R] M` given by `b`.

We show that every endomorphism has a matrix representation, and if `f.range ≤ I • ⊤` for some
ideal `I`, we may furthermore obtain a matrix representation whose entries fall in `I`.

This is used to conclude the Cayley-Hamilton theorem for f.g. modules over arbitrary rings.
-/

variables {ι : Type*} [fintype ι]
variables {M : Type*} [add_comm_group M] (R : Type*) [comm_ring R] [module R M] (I : ideal R)
variables (b : ι → M) (hb : submodule.span R (set.range b) = ⊤)

open_locale big_operators
open_locale polynomial

/-- The composition of a matrix (as an endomporphism of `ι → R`) with the projection
`(ι → R) →ₗ[R] M`.  -/
def pi_to_module.from_matrix [decidable_eq ι] : matrix ι ι R →ₗ[R] (ι → R) →ₗ[R] M :=
(linear_map.llcomp R _ _ _ (fintype.total R R b)).comp alg_equiv_matrix'.symm.to_linear_map

lemma pi_to_module.from_matrix_apply [decidable_eq ι] (A : matrix ι ι R) (w : ι → R) :
  pi_to_module.from_matrix R b A w = fintype.total R R b (A.mul_vec w) := rfl

lemma pi_to_module.from_matrix_apply_single_one [decidable_eq ι] (A : matrix ι ι R) (j : ι) :
  pi_to_module.from_matrix R b A (pi.single j 1) = ∑ (i : ι), A i j • b i :=
begin
  rw [pi_to_module.from_matrix_apply, fintype.total_apply, matrix.mul_vec_single],
  simp_rw [mul_one]
end

/-- The endomorphisms of `M` acts on `(ι → R) →ₗ[R] M`, and takes the projection
to a `(ι → R) →ₗ[R] M`. -/
def pi_to_module.from_End : (module.End R M) →ₗ[R] (ι → R) →ₗ[R] M :=
linear_map.lcomp _ _ (fintype.total R R b)

lemma pi_to_module.from_End_apply (f : module.End R M) (w : ι → R) :
  pi_to_module.from_End R b f w = f (fintype.total R R b w) := rfl

lemma pi_to_module.from_End_apply_single_one [decidable_eq ι] (f : module.End R M) (i : ι) :
  pi_to_module.from_End R b f (pi.single i 1) = f (b i) :=
begin
  rw pi_to_module.from_End_apply,
  congr,
  convert fintype.total_apply_single R b i 1,
  rw one_smul,
end

lemma pi_to_module.from_End_injective (hb : submodule.span R (set.range b) = ⊤) :
  function.injective (pi_to_module.from_End R b) :=
begin
  intros x y e,
  ext m,
  obtain ⟨m, rfl⟩ : m ∈ (fintype.total R R b).range,
  { rw (fintype.range_total R b).trans hb, trivial },
  exact (linear_map.congr_fun e m : _)
end

section

variables {R} [decidable_eq ι]

/-- We say that a matrix represents an endomorphism of `M` if the matrix acting on `ι → R` is
equal to `f` via the projection `(ι → R) →ₗ[R] M` given by a fixed (spanning) set.  -/
def matrix.represents (A : matrix ι ι R) (f : module.End R M) : Prop :=
pi_to_module.from_matrix R b A = pi_to_module.from_End R b f

variables {b}

lemma matrix.represents.congr_fun {A : matrix ι ι R} {f : module.End R M}
  (h : A.represents b f) (x) :
  fintype.total R R b (A.mul_vec x) = f (fintype.total R R b x) :=
linear_map.congr_fun h x

lemma matrix.represents_iff {A : matrix ι ι R} {f : module.End R M} :
  A.represents b f ↔
    ∀ x, fintype.total R R b (A.mul_vec x) = f (fintype.total R R b x) :=
⟨λ e x, e.congr_fun x, λ H, linear_map.ext $ λ x, H x⟩

lemma matrix.represents_iff' {A : matrix ι ι R} {f : module.End R M} :
  A.represents b f ↔ ∀ j, ∑ (i : ι), A i j • b i = f (b j) :=
begin
  split,
  { intros h i,
    have := linear_map.congr_fun h (pi.single i 1),
    rwa [pi_to_module.from_End_apply_single_one,
      pi_to_module.from_matrix_apply_single_one] at this },
  { intros h,
    ext,
    simp_rw [linear_map.comp_apply, linear_map.coe_single, pi_to_module.from_End_apply_single_one,
      pi_to_module.from_matrix_apply_single_one],
    apply h }
end

lemma matrix.represents.mul {A A' : matrix ι ι R} {f f' : module.End R M}
  (h : A.represents b f) (h' : matrix.represents b A' f') :
  (A * A').represents b (f * f') :=
begin
  delta matrix.represents pi_to_module.from_matrix at ⊢,
  rw [linear_map.comp_apply, alg_equiv.to_linear_map_apply, map_mul],
  ext,
  dsimp [pi_to_module.from_End],
  rw [← h'.congr_fun, ← h.congr_fun],
  refl,
end

lemma matrix.represents.one : (1 : matrix ι ι R).represents b 1 :=
begin
  delta matrix.represents pi_to_module.from_matrix,
  rw [linear_map.comp_apply, alg_equiv.to_linear_map_apply, map_one],
  ext,
  refl
end

lemma matrix.represents.add {A A' : matrix ι ι R} {f f' : module.End R M}
  (h : A.represents b f) (h' : matrix.represents b A' f') :
  (A + A').represents b (f + f') :=
begin
  delta matrix.represents at ⊢ h h', rw [map_add, map_add, h, h'],
end

lemma matrix.represents.zero :
  (0 : matrix ι ι R).represents b 0 :=
begin
  delta matrix.represents, rw [map_zero, map_zero],
end

lemma matrix.represents.smul {A : matrix ι ι R} {f : module.End R M}
  (h : A.represents b f) (r : R) :
  (r • A).represents b (r • f) :=
begin
  delta matrix.represents at ⊢ h, rw [map_smul, map_smul, h],
end

lemma matrix.represents.eq {A : matrix ι ι R} {f f' : module.End R M}
  (h : A.represents b f) (h' : A.represents b f') : f = f' :=
pi_to_module.from_End_injective R b hb (h.symm.trans h')

variables (b R)

/-- The subalgebra of `matrix ι ι R` that consists of matrices that actually represent
endomorphisms on `M`. -/
def matrix.is_representation : subalgebra R (matrix ι ι R) :=
{ carrier := { A | ∃ f : module.End R M, A.represents b f },
  mul_mem' := λ A₁ A₂ ⟨f₁, e₁⟩ ⟨f₂, e₂⟩, ⟨f₁ * f₂, e₁.mul e₂⟩,
  one_mem' := ⟨1, matrix.represents.one⟩,
  add_mem' := λ A₁ A₂ ⟨f₁, e₁⟩ ⟨f₂, e₂⟩, ⟨f₁ + f₂, e₁.add e₂⟩,
  zero_mem' := ⟨0, matrix.represents.zero⟩,
  algebra_map_mem' := λ r, ⟨r • 1, matrix.represents.one.smul r⟩ }

/-- The map sending a matrix to the endomorphism it represents. This is an `R`-algebra morphism. -/
noncomputable
def matrix.is_representation.to_End : matrix.is_representation R b →ₐ[R] module.End R M :=
{ to_fun := λ A, A.2.some,
  map_one' := (1 : matrix.is_representation R b).2.some_spec.eq hb matrix.represents.one,
  map_mul' := λ A₁ A₂, (A₁ * A₂).2.some_spec.eq hb (A₁.2.some_spec.mul A₂.2.some_spec),
  map_zero' := (0 : matrix.is_representation R b).2.some_spec.eq hb matrix.represents.zero,
  map_add' := λ A₁ A₂, (A₁ + A₂).2.some_spec.eq hb (A₁.2.some_spec.add A₂.2.some_spec),
  commutes' := λ r, (r • 1 : matrix.is_representation R b).2.some_spec.eq
    hb (matrix.represents.one.smul r) }

lemma matrix.is_representation.to_End_represents (A : matrix.is_representation R b) :
  (A : matrix ι ι R).represents b (matrix.is_representation.to_End R b hb A) :=
A.2.some_spec

lemma matrix.is_representation.eq_to_End_of_represents (A : matrix.is_representation R b)
  {f : module.End R M} (h : (A : matrix ι ι R).represents b f) :
    matrix.is_representation.to_End R b hb A = f :=
A.2.some_spec.eq hb h

lemma matrix.is_representation.to_End_exists_mem_ideal
  (f : module.End R M) (I : ideal R) (hI : f.range ≤ I • ⊤) :
  ∃ M, matrix.is_representation.to_End R b hb M = f ∧ ∀ i j, M.1 i j ∈ I :=
begin
  have : ∀ x, f x ∈ (ideal.finsupp_total ι M I b).range,
  { rw [ideal.range_finsupp_total, hb], exact λ x, hI (f.mem_range_self x) },
  choose bM' hbM',
  let A : matrix ι ι R := λ i j, bM' (b j) i,
  have : A.represents b f,
  { rw matrix.represents_iff',
    dsimp [A],
    intro j,
    specialize hbM' (b j),
    rwa ideal.finsupp_total_apply_eq_of_fintype at hbM' },
  exact ⟨⟨A, f, this⟩, matrix.is_representation.eq_to_End_of_represents R b hb ⟨A, f, this⟩ this,
    λ i j, (bM' (b j) i).prop⟩,
end

lemma matrix.is_representation.to_End_surjective :
  function.surjective (matrix.is_representation.to_End R b hb) :=
begin
  intro f,
  obtain ⟨M, e, -⟩ := matrix.is_representation.to_End_exists_mem_ideal R b hb f ⊤ _,
  exact ⟨M, e⟩,
  simp,
end

end

/--
The **Cayley-Hamilton Theorem** for f.g. modules over arbitrary rings states that for each
`R`-endomorphism `φ` of an `R`-module `M` such that `φ(M) ≤ I • M` for some ideal `I`, there
exists some `n` and some `aᵢ ∈ Iⁱ` such that `φⁿ + a₁ φⁿ⁻¹ + ⋯ + aₙ = 0`.

This is the version found in Eisenbud 4.3, which is slightly weaker than Matsumura 2.1
(this lacks the constraint on `n`), and is slightly stronger than Atiyah-Macdonald 2.4.
-/
lemma linear_map.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul
  [module.finite R M] (f : module.End R M) (I : ideal R) (hI : f.range ≤ I • ⊤) :
  ∃ p : R[X],
    p.monic ∧ (∀ k, p.coeff k ∈ I ^ (p.nat_degree - k)) ∧ polynomial.aeval f p = 0 :=
begin
  classical,
  casesI subsingleton_or_nontrivial R,
  { exactI ⟨0, polynomial.monic_of_subsingleton _, by simp⟩ },
  obtain ⟨s : finset M, hs : submodule.span R (s : set M) = ⊤⟩ := module.finite.out,
  obtain ⟨A, rfl, h⟩ := matrix.is_representation.to_End_exists_mem_ideal R (coe : s → M)
    (by rw [subtype.range_coe_subtype, finset.set_of_mem, hs]) f I hI,
  refine ⟨A.1.charpoly, A.1.charpoly_monic, _, _⟩,
  { rw A.1.charpoly_nat_degree_eq_dim,
    exact coeff_charpoly_mem_ideal_pow h },
  { rw [polynomial.aeval_alg_hom_apply, ← map_zero (matrix.is_representation.to_End R coe _)],
    congr' 1,
    ext1,
    rw [polynomial.aeval_subalgebra_coe, subtype.val_eq_coe, matrix.aeval_self_charpoly,
      subalgebra.coe_zero] },
  { apply_instance }
end

lemma linear_map.exists_monic_and_aeval_eq_zero [module.finite R M]
  (f : module.End R M) : ∃ p : R[X], p.monic ∧ polynomial.aeval f p = 0 :=
(linear_map.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul R f ⊤ (by simp)).imp
  (λ p h, h.imp_right and.elim_right)
