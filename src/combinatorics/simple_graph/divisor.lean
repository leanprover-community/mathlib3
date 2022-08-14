/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.degree_sum
import combinatorics.simple_graph.matrix.laplacian
import linear_algebra.matrix.to_linear_equiv

/-!
# Divisors of simple graphs

A *divisor* of a graph `G` with vertices `α` is a function `α → ℤ` up to chip-firing equivalence.

## Tags

divisor, simple graph, chip firing, sandpile
-/

namespace function
variables {α β M₁ M₂ : Type*}

namespace surjective

/-- A type endowed with `0`, `1`, `+` is an additive commutative group with one, if it admits a
surjective map that preserves `0`, `1`, and `+` to an additive commutative group with one. -/
@[reducible] -- See note [reducible non-instances]
protected def add_comm_monoid_with_one [has_zero M₂] [has_one M₂] [has_add M₂] [has_smul ℕ M₂]
  [has_nat_cast M₂] [add_comm_monoid_with_one M₁] (f : M₁ → M₂) (hf : surjective f) (zero : f 0 = 0)
  (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (nat_cast : ∀ n : ℕ, f n = n) :
  add_comm_monoid_with_one M₂ :=
{ ..hf.add_monoid_with_one f zero one add nsmul nat_cast, ..hf.add_comm_monoid f zero add nsmul }

/-- A type endowed with `0`, `1`, `+` is an additive commutative group with one, if it admits a
surjective map that preserves `0`, `1`, and `+` to an additive commutative group with one. -/
@[reducible] -- See note [reducible non-instances]
protected def add_comm_group_with_one [has_zero M₂] [has_one M₂] [has_add M₂] [has_neg M₂]
  [has_sub M₂] [has_smul ℕ M₂] [has_smul ℤ M₂] [has_nat_cast M₂] [has_int_cast M₂]
  [add_comm_group_with_one M₁] (f : M₁ → M₂) (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (- x) = - f x)
  (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n)
  (int_cast : ∀ n : ℤ, f n = n) :
  add_comm_group_with_one M₂ :=
{ ..hf.add_group_with_one f zero one add neg sub nsmul zsmul nat_cast int_cast,
  ..hf.add_comm_group f zero add neg sub nsmul zsmul }

end surjective

/-- Push forward a preorder. -/
def injective.map [preorder α] (f : α → β) (hf : surjective f) : preorder β :=
{ le := relation.map (≤) f f,
  lt := relation.map (<) f f,
  le_refl := hf.forall.2 $ λ a, ⟨a, a, le_rfl, rfl, rfl⟩,
  le_trans := hf.forall₃.2 $ λ a b c, begin
    rintro ⟨a, a, _⟩,
    sorry
  end,
  lt_iff_le_not_le := sorry }

end function

namespace add_con
variables {G : Type*}

instance [add_monoid_with_one G] (c : add_con G) : has_one c.quotient := ⟨(1 : G)⟩
instance [add_monoid_with_one G] (c : add_con G) : has_nat_cast c.quotient :=
⟨λ n, ((n : G) : c.quotient)⟩
instance [add_group_with_one G] (c : add_con G) : has_int_cast c.quotient :=
⟨λ n, ((n : G) : c.quotient)⟩

instance add_monoid_with_one [add_monoid_with_one G] (c : add_con G) :
  add_monoid_with_one c.quotient :=
function.surjective.add_monoid_with_one _ quotient.surjective_quotient_mk' rfl rfl (λ _ _, rfl)
  (λ _ _, rfl)  (λ _, rfl)

instance add_comm_monoid_with_one [add_comm_monoid_with_one G] (c : add_con G) :
  add_comm_monoid_with_one c.quotient :=
function.surjective.add_comm_monoid_with_one _ quotient.surjective_quotient_mk' rfl rfl (λ _ _, rfl)
  (λ _ _, rfl)  (λ _, rfl)

instance add_group_with_one [add_group_with_one G] (c : add_con G) :
  add_group_with_one c.quotient :=
function.surjective.add_group_with_one _ quotient.surjective_quotient_mk' rfl rfl (λ _ _, rfl)
  (λ _, rfl)  (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _, rfl)

instance add_comm_group_with_one [add_comm_group_with_one G] (c : add_con G) :
  add_comm_group_with_one c.quotient :=
function.surjective.add_comm_group_with_one _ quotient.surjective_quotient_mk' rfl rfl (λ _ _, rfl)
  (λ _, rfl)  (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _, rfl)

end add_con

namespace quotient_add_group
variables {G : Type*}

instance add_group_with_one [add_group_with_one G] (N : add_subgroup G) [add_subgroup.normal N] :
  add_group_with_one (G ⧸ N) :=
(quotient_add_group.con N).add_group_with_one

instance add_comm_group_with_one [add_comm_group_with_one G] (N : add_subgroup G)
  [add_subgroup.normal N] :
  add_comm_group_with_one (G ⧸ N) :=
(quotient_add_group.con N).add_comm_group_with_one

end quotient_add_group

namespace submodule.quotient
variables {R M : Type*} [ring R]

instance add_comm_group_with_one [add_comm_group_with_one M] [module R M] (p : submodule R M) :
  add_comm_group_with_one (M ⧸ p) :=
quotient_add_group.add_comm_group_with_one p.to_add_subgroup

end submodule.quotient

open finset function fintype (card)
open_locale big_operators

noncomputable theory

namespace simple_graph
variables {α : Type*} [decidable_eq α] [fintype α] (G : simple_graph α) [decidable_rel G.adj]

/-- A *divisor* of the graph `G` is an equivalence class of formal sums of vertices of `G` under
linear equivalence. This is also known as the Picard group. -/
@[derive add_comm_group_with_one]
def divisor : Type* :=
(α → ℤ) ⧸ (matrix.to_lin (pi.basis_fun ℤ _) (pi.basis_fun ℤ _) $ G.laplacian ℤ).ker

variables {G}

namespace divisor
variables {f g : α → ℤ} {d e : G.divisor}

/-- The divisor corresponding to a formal sum. -/
def mk : (α → ℤ) →+ G.divisor := quotient_add_group.mk' _

lemma mk_surjective : surjective (mk : (α → ℤ) → G.divisor) := surjective_quot_mk _

@[simp] lemma mk_zero : (mk 0 : G.divisor) = 0 := rfl
@[simp] lemma mk_one : (mk 1 : G.divisor) = 1 := rfl
@[simp] lemma neg_mk (f : α → ℤ) : (-mk f : G.divisor) = mk (-f) := rfl
@[simp] lemma mk_add_mk (f g : α → ℤ) : (mk f + mk g : G.divisor) = mk (f + g) := rfl
@[simp] lemma mk_sub_mk (f g : α → ℤ) : (mk f - mk g : G.divisor) = mk (f - g) := rfl
@[simp] lemma mk_nsmul (f : α → ℤ) (n : ℕ) : (mk (n • f) : G.divisor) = n • mk f := rfl
@[simp] lemma mk_zsmul (f : α → ℤ) (n : ℤ) : (mk (n • f) : G.divisor) = n • mk f := rfl
@[simp] lemma mk_nat_cast (n : ℕ) : (mk n : G.divisor) = n := rfl
@[simp] lemma mk_int_cast (n : ℤ) : (mk n : G.divisor) = n := rfl

/-- The degree of a divisor is the sum of its coefficients. -/
def degree : G.divisor →+ ℤ := quotient_add_group.lift _
{ to_fun := λ f : α → ℤ, ∑ a, f a,
  map_zero' := sum_eq_zero $ λ _ _, rfl,
  map_add' := λ f g, sum_add_distrib } $ begin
  rintro f hf,
  simp only [submodule.mem_to_add_subgroup, linear_map.mem_ker, matrix.to_lin, linear_map.to_matrix] at hf,
  simp only [linear_equiv.trans_symm, linear_map.to_matrix'_symm, linear_equiv.trans_apply,
    linear_equiv.arrow_congr_symm_apply, basis.equiv_fun_apply, matrix.to_lin'_apply,
    basis.equiv_fun_symm_apply, pi.basis_fun_apply, zsmul_eq_mul] at hf,
  sorry
end

@[simp] lemma degree_mk (f : α → ℤ) : (mk f : G.divisor).degree = ∑ a, f a := rfl

@[simp] lemma degree_of_is_empty [is_empty α] : ∀ d : G.divisor, d.degree = 0 :=
mk_surjective.forall.2 $ λ f, by simp

variable (G)

lemma exists_degree_eq [nonempty α] (n : ℤ) : ∃ d : G.divisor, d.degree = n :=
‹nonempty α›.elim $ λ a, ⟨mk (pi.single a n), by simp⟩

variables {G}

instance : has_le G.divisor := ⟨λ a b, ∃ a', a = mk a' ∧ ∃ b', b = mk b' ∧ a' ≤ b'⟩
instance : has_lt G.divisor := ⟨λ a b, ∃ a', a = mk a' ∧ ∃ b', b = mk b' ∧ a' < b'⟩

lemma degree_le_degree : d ≤ e → d.degree ≤ e.degree :=
by { rintro ⟨a, rfl, b, rfl, h⟩, exact fintype.sum_mono h }

lemma degree_lt_degree : d < e → d.degree < e.degree :=
by { rintro ⟨a, rfl, b, rfl, h⟩, exact fintype.sum_strict_mono h }

instance : preorder G.divisor :=
{ le_refl := λ a, quot.induction_on a $ λ a, ⟨a, rfl, a, rfl, le_rfl⟩,
  le_trans := λ a b c, begin
    rintro ⟨a, rfl, b, rfl, hab⟩ ⟨b', hb', c, rfl, hbc⟩,
    sorry
  end,
  lt_iff_le_not_le := sorry,
  ..divisor.has_le, ..divisor.has_lt }

lemma degree_mono : monotone (degree : G.divisor → ℤ) := λ _ _, degree_le_degree
lemma degree_strict_mono : strict_mono (degree : G.divisor → ℤ) := λ _ _, degree_lt_degree

@[simp] lemma degree_one : (1 : G.divisor).degree = card α :=
(sum_const 1).trans $ nat.smul_one_eq_coe _

@[simp] lemma degree_nat_cast (n : ℕ) : (n : G.divisor).degree = card α * n :=
(sum_const (n : ℤ)).trans $ nsmul_eq_mul _ _

@[simp] lemma degree_int_cast (n : ℤ) : (n : G.divisor).degree = card α * n :=
(sum_const n).trans $ nsmul_eq_mul _ _

/-- The rank of a divisor `d` is the greatest `n` such that all divisors of degree `n` are less than
`d`. -/
noncomputable def rank (d : G.divisor) : ℤ := Sup {n : ℤ | ∀ ⦃e : G.divisor⦄, e.degree = n → e ≤ d}

lemma rank_set_nonempty (hG : G.preconnected) (d : G.divisor) :
  {n : ℤ | ∀ ⦃e : G.divisor⦄, e.degree = n → e ≤ d}.nonempty := sorry --quite hard

@[simp] lemma rank_of_is_empty [is_empty α] (d : G.divisor) : d.rank = 0 := sorry

lemma rank_le_degree (hG : G.preconnected) (d : G.divisor) : d.rank ≤ d.degree :=
begin
  casesI is_empty_or_nonempty α,
  { simp },
  refine cSup_le (d.rank_set_nonempty hG) (λ n hn, _),
  obtain ⟨e, rfl⟩ := exists_degree_eq G n,
  exact degree_mono (hn rfl),
end

@[simp] lemma rank_zero : (0 : G.divisor).rank = 0 := sorry
@[simp] lemma le_rank_one : 1 ≤ (1 : G.divisor).rank := sorry
@[simp] lemma le_rank_nat_cast (n : ℕ) : (n : ℤ) ≤ (n : G.divisor).rank := sorry
@[simp] lemma le_rank_int_cast (n : ℤ) : n ≤ (n : G.divisor).rank := sorry

end divisor

open divisor

variables (G)

lemma gonality_aux : ∃ (n : ℕ) (d : G.divisor), 0 < d.rank ∧ d.degree = n :=
⟨card α, 1, zero_lt_one.trans_le le_rank_one, degree_one⟩

open_locale classical

/-- The gonality of a graph is the minimum degree of a divisor of positive rank. -/
noncomputable def gonality : ℕ := nat.find G.gonality_aux

/-- The genus of a graph is its first Betti number, namely the number of eges minus the number of
vertices plus one. -/
def genus : ℤ := G.edge_finset.card - card α + 1

/-- The canonical divisor of a graph. -/
def canonical_divisor : G.divisor := divisor.mk $ λ a, G.degree a - 2

local attribute [-simp] set.to_finset_card

@[simp] lemma degree_canonical_divisor : G.canonical_divisor.degree = 2 * G.genus - 2 :=
by simp [canonical_divisor, genus, ←nat.cast_sum, sum_degrees_eq_twice_card_edges, mul_add, mul_sub,
  mul_comm, card_univ]

end simple_graph
