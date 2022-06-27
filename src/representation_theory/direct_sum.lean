/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.character

open_locale direct_sum

instance finite_dimensional.direct_sum
  {k ι : Type*} [division_ring k] [fintype ι] (V : ι → Type*)
  [Π i : ι, add_comm_group (V i)]
  [Π i : ι, module k (V i)]
  [Π i : ι, finite_dimensional k (V i)] :
  finite_dimensional k (direct_sum ι V) :=
begin
  have b := λ i : ι, finite_dimensional.fin_basis k (V i),
  have B := dfinsupp.basis b,
  apply finite_dimensional.of_fintype_basis B
end

/-- Direct sum commutes with the product (composition) of the linear maps on each constituent
space. -/
theorem dfinsupp.map_range.linear_map_mul
  {ι k : Type*} [semiring k] {V : ι → Type*}
  [Π i : ι, add_comm_monoid (V i)] [Π i : ι, module k (V i)]
  (f : Π i : ι, V i →ₗ[k] V i) (g : Π i : ι, V i →ₗ[k] V i) :
  dfinsupp.map_range.linear_map (λ i : ι, f i * g i)
    = dfinsupp.map_range.linear_map f * dfinsupp.map_range.linear_map g :=
begin
  have : (λ i : ι, f i * g i) = λ i : ι, (f i).comp (g i),
  by {ext, refl},
  rw [this, linear_map.mul_eq_comp],
  apply dfinsupp.map_range.linear_map_comp
end

/-- Direct sum of representations -/
def representation.direct_sum
  {k G ι : Type*} {V : ι → Type*} [comm_semiring k] [monoid G]
  [Π i : ι, add_comm_monoid (V i)] [Π i : ι, module k (V i)]
  (ρV : Π i : ι, representation k G (V i)) :
  representation k G (⨁ i : ι, V i) :=
⟨λ g, dfinsupp.map_range.linear_map (λ i : ι, (ρV i g)),
by {
  simp,
  have : (λ i : ι, (1 : V i →ₗ[k] V i)) = λ i : ι, linear_map.id,
  by {ext, refl},
  rw this,
  simp,
  refl
  },
by {
  simp,
  intros,
  apply dfinsupp.map_range.linear_map_mul
}⟩

@[simp]
theorem representation.direct_sum_apply
  {k G ι : Type*} {V : ι → Type*} [comm_semiring k] [monoid G]
  [Π i : ι, add_comm_monoid (V i)] [Π i : ι, module k (V i)]
  (ρV : Π i : ι, representation k G (V i)) (g : G) :
  representation.direct_sum ρV g = dfinsupp.map_range.linear_map (λ i : ι, (ρV i g)) := rfl

/-- Direct sum of `FinVect`s as a `FinVect` -/
def FinVect.direct_sum
  {k ι : Type*} [field k] [fintype ι] (V : ι → FinVect k)
  [Π i : ι, finite_dimensional k (V i)] :
  FinVect k :=
⟨
  {
    carrier := direct_sum ι (λ i, V i),
    is_add_comm_group := direct_sum.add_comm_group (λ i, V i),
    is_module := direct_sum.module
  },
  by apply finite_dimensional.direct_sum
⟩

/-- Direct sum of `fdRep`s as a `fdRep` -/
def fdRep.direct_sum
  {k G ι : Type*} [field k] [monoid G] [fintype ι] (V : ι → fdRep k G) :
  fdRep k G :=
fdRep.of (representation.direct_sum (λ i : ι, (V i).ρ))

@[simp]
theorem fdRep.direct_sum_coe
  {k G ι : Type*} [field k] [monoid G] [fintype ι] (V : ι → fdRep k G) :
  ↥(fdRep.direct_sum V) = direct_sum ι (λ i : ι, V i) := rfl

@[simp]
theorem fdRep.direct_sum_apply
  {k G ι : Type*} [field k] [monoid G] [fintype ι] (V : ι → fdRep k G) (g : G):
  (fdRep.direct_sum V).ρ g = dfinsupp.map_range.linear_map (λ i : ι, ((V i).ρ g)) := rfl

/-- Direct sum of matrices is a block-diagonal matrix. -/
def matrix.direct_sum
  {ι k : Type*} [decidable_eq ι] [semiring k] {n : ι → Type*}
  (M : Π i : ι, matrix (n i) (n i) k) :
  matrix (Σ i : ι, n i) (Σ i : ι, n i) k :=
λ x y, by {
  cases x with i x_i,
  cases y with j x_j,
  by_cases i = j,
  rw ←h at x_j,
  exact M i x_i x_j,
  exact 0
}

theorem matrix.direct_sum_apply
  {ι k : Type*} [decidable_eq ι] [semiring k] {n : ι → Type*}
  (M : Π i : ι, matrix (n i) (n i) k) (x y : Σ i : ι, n i) :
  matrix.direct_sum M x y
    = dite (x.1 = y.1)
    (λ (h : x.1 = y.1), M x.1 x.2 (cast (congr_arg n h.symm) y.2))
    (λ (h : ¬x.1 = y.1), 0) :=
begin
  cases x with i x_i,
  cases y with j x_j,
  unfold matrix.direct_sum,
  simp
end

theorem matrix.direct_sum_diag
  {ι k : Type*} [decidable_eq ι] [semiring k] {n : ι → Type*}
  (M : Π i : ι, matrix (n i) (n i) k) (x : Σ i : ι, n i) :
  matrix.direct_sum M x x = M x.1 x.2 x.2 :=
begin
  rw matrix.direct_sum_apply,
  simp
end

/-- Trace of direct sum matrix is sum of traces of constituent matrices. -/
theorem matrix.trace_direct_sum
  {ι k : Type*} [fintype ι] [decidable_eq ι] [semiring k]
  {n : ι → Type*} [Π i : ι, fintype (n i)]
  (M : Π i : ι, matrix (n i) (n i) k) :
  (matrix.direct_sum M).trace = finset.univ.sum (λ i : ι, (M i).trace) :=
begin
  unfold matrix.trace,
  rw finset.sum_sigma',
  simp,
  congr,
  ext,
  rw matrix.direct_sum_diag
end

theorem direct_sum.to_matrix_case_eq
  {ι k : Type*} [fintype ι] [decidable_eq ι] [comm_semiring k]
  {V : ι → Type*} [Π i : ι, add_comm_monoid (V i)] [Π i : ι, module k (V i)]
  (f : Π i : ι, V i →ₗ[k] V i)
  {n : ι → Type*} [Π i : ι, fintype (n i)] [Π i : ι, decidable_eq (n i)]
  (b : Π i : ι, basis (n i) k (V i)) (x y : Σ i : ι, n i) (h : x.1 = y.1) :
  linear_map.to_matrix (dfinsupp.basis b) (dfinsupp.basis b) (dfinsupp.map_range.linear_map f) x y
    = matrix.direct_sum (λ i : ι, linear_map.to_matrix (b i) (b i) (f i)) x y :=
begin
  rw matrix.direct_sum_apply,
  rw linear_map.to_matrix_apply,
  unfold dfinsupp.basis,
  simp,
  simp_rw h,
  simp,
  rw linear_map.to_matrix_apply,
  congr,
  cases x,
  cases y,
  dsimp only at *,
  subst h,
  refl
end

/-- Matrix of direct sum linear map is direct sum of individual `linear_map.to_matrix`. -/
theorem direct_sum.to_matrix
  {ι k : Type*} [fintype ι] [decidable_eq ι] [comm_semiring k]
  {V : ι → Type*} [Π i : ι, add_comm_monoid (V i)] [Π i : ι, module k (V i)]
  (f : Π i : ι, V i →ₗ[k] V i)
  {n : ι → Type*} [Π i : ι, fintype (n i)] [Π i : ι, decidable_eq (n i)]
  (b : Π i : ι, basis (n i) k (V i)) :
  linear_map.to_matrix (dfinsupp.basis b) (dfinsupp.basis b) (dfinsupp.map_range.linear_map f)
    = matrix.direct_sum (λ i : ι, linear_map.to_matrix (b i) (b i) (f i)) :=
begin
  ext x y,
  by_cases x.1 = y.1,
  apply direct_sum.to_matrix_case_eq,
  exact h,
  { rw matrix.direct_sum_apply,
    rw linear_map.to_matrix_apply,
    unfold dfinsupp.basis,
    cases x,
    cases y,
    dsimp only at *,
    split_ifs,
    simp,
    split_ifs,
    dsimp only at h_1,
    exact absurd h_1.symm h,
    simp }
end

/-- Trace of direct sum matrix is sum of traces of constituent matrices. Matrices are given as
linear maps with assumed finite basis. -/
theorem direct_sum.fintype_trace
  {ι k : Type*} [fintype ι] [decidable_eq ι] [comm_semiring k]
  {V : ι → Type*} [Π i : ι, add_comm_monoid (V i)] [Π i : ι, module k (V i)]
  (f : Π i : ι, V i →ₗ[k] V i)
  {n : ι → Type*} [Π i : ι, fintype (n i)] [Π i : ι, decidable_eq (n i)]
  (b : Π i : ι, basis (n i) k (V i)) :
  linear_map.trace k (⨁ i : ι, V i) (dfinsupp.map_range.linear_map f)
    = finset.univ.sum (λ (i : ι), linear_map.trace k (V i) (f i)) :=
begin
  rw @linear_map.trace_eq_matrix_trace k _ (⨁ i : ι, V i) _ _ _ _ _
    (dfinsupp.basis b) (dfinsupp.map_range.linear_map f),
  rw direct_sum.to_matrix,
  rw matrix.trace_direct_sum,
  congr,
  ext i,
  rw @linear_map.trace_eq_matrix_trace k _ (V i) _ _ _ _ _
end

/-- Character of the (finite) direct sum representation is the sum of characters of the individual
representations. -/
theorem fdRep.char_direct_sum
  {k G ι : Type*} [field k] [monoid G] [fintype ι] [decidable_eq ι] (V : ι → fdRep k G) (g : G) :
  (fdRep.direct_sum V).character g = finset.univ.sum (λ i : ι, (V i).character g) :=
begin
  unfold fdRep.character,
  simp,
  have : linear_map.trace k (fdRep.direct_sum V)
    (dfinsupp.map_range.linear_map (λ (i : ι), (V i).ρ g))
    = linear_map.trace k (direct_sum ι (λ i : ι, V i))
    (dfinsupp.map_range.linear_map (λ (i : ι), (V i).ρ g)),
  refl,
  rw this,
  have b := λ i : ι, finite_dimensional.fin_basis k (V i),
  rw @direct_sum.fintype_trace _ _ _ _ _ (λ i : ι, V i) _ _ _ _ _ _ b
end
