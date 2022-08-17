/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.order
import combinatorics.graph.multi.connectivity
import combinatorics.graph.multi.degree
import data.int.order
import linear_algebra.quotient

/-!
# Divisors of simple graphs

A *divisor* of a graph `G` with vertices `α` is a function `G → ℤ`.

## Tags

divisor, simple graph, chip firing, sandpile
-/

local attribute [-simp] set.to_finset_card

namespace function
variables {α β M₁ M₂ : Type*}

attribute [reducible] surjective.add_group_with_one

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

namespace multigraph
variables (G : multigraph) [locally_finite G]

/-- The Picard group of the graph `G` is the quotient of divisors of `G` by the image of the
Laplacian. -/
@[derive add_comm_group_with_one] def picard_group : Type* := (G → ℤ) ⧸ (G.laplacian ℤ ℤ).range

variables {G}

namespace picard_group
variables {f g : G → ℤ} {d e : G.picard_group}

/-- The picard_group corresponding to a formal sum. -/
def mk : (G → ℤ) →+ G.picard_group := quotient_add_group.mk' _

lemma mk_surjective : surjective (mk : (G → ℤ) → G.picard_group) := surjective_quot_mk _

@[simp] lemma mk_zero : (mk 0 : G.picard_group) = 0 := rfl
@[simp] lemma mk_one : (mk 1 : G.picard_group) = 1 := rfl
@[simp] lemma mk_neg (f : G → ℤ) : (mk (-f) : G.picard_group) = -mk f := rfl
@[simp] lemma mk_add (f g : G → ℤ) : (mk (f + g) : G.picard_group) = mk f + mk g := rfl
@[simp] lemma mk_sub (f g : G → ℤ) : (mk (f - g) : G.picard_group) = mk f - mk g := rfl
@[simp, nolint simp_nf]
lemma mk_nsmul (f : G → ℤ) (n : ℕ) : (mk (n • f) : G.picard_group) = n • mk f := rfl
@[simp, nolint simp_nf]
lemma mk_zsmul (f : G → ℤ) (n : ℤ) : (mk (n • f) : G.picard_group) = n • mk f := rfl
@[simp, nolint simp_nf] lemma mk_nat_cast (n : ℕ) : (mk n : G.picard_group) = n := rfl
@[simp, nolint simp_nf] lemma mk_int_cast (n : ℤ) : (mk n : G.picard_group) = n := rfl

instance : inhabited G.picard_group := ⟨0⟩

instance : has_le G.picard_group := ⟨λ a b, ∃ a', a = mk a' ∧ ∃ b', b = mk b' ∧ a' ≤ b'⟩
instance : has_lt G.picard_group := ⟨λ a b, ∃ a', a = mk a' ∧ ∃ b', b = mk b' ∧ a' < b'⟩

variables [fintype G]

/-- The degree of a divisor is the sum of its coefficients. -/
def degree : G.picard_group →+ ℤ := quotient_add_group.lift _
{ to_fun := λ f : G → ℤ, ∑ a, f a,
  map_zero' := sum_eq_zero $ λ _ _, rfl,
  map_add' := λ f g, sum_add_distrib } $ by { rintro _ ⟨f, rfl⟩, exact sum_laplacian _ _ _ }

@[simp] lemma degree_mk (f : G → ℤ) : (mk f : G.picard_group).degree = ∑ a, f a := rfl

@[simp] lemma degree_of_is_empty [is_empty G] : ∀ d : G.picard_group, d.degree = 0 :=
mk_surjective.forall.2 $ λ f, by simp

variable (G)

lemma exists_degree_eq [nonempty G] (n : ℤ) : ∃ d : G.picard_group, d.degree = n :=
by { classical, exact ‹nonempty G›.elim (λ a, ⟨mk (pi.single a n), by simp⟩) }

variables {G}

lemma degree_le_degree : d ≤ e → d.degree ≤ e.degree :=
by { rintro ⟨a, rfl, b, rfl, h⟩, exact fintype.sum_mono h }

lemma degree_lt_degree : d < e → d.degree < e.degree :=
by { rintro ⟨a, rfl, b, rfl, h⟩, exact fintype.sum_strict_mono h }

instance : preorder G.picard_group :=
{ le_refl := λ a, quot.induction_on a $ λ a, ⟨a, rfl, a, rfl, le_rfl⟩,
  le_trans := λ a b c, begin
    rintro ⟨a, rfl, b, rfl, hab⟩ ⟨b', hb', c, rfl, hbc⟩,
    sorry
  end,
  lt_iff_le_not_le := sorry,
  ..picard_group.has_le, ..picard_group.has_lt }

lemma degree_mono : monotone (degree : G.picard_group → ℤ) := λ _ _, degree_le_degree
lemma degree_strict_mono : strict_mono (degree : G.picard_group → ℤ) := λ _ _, degree_lt_degree

@[simp] lemma degree_one : (1 : G.picard_group).degree = card G :=
(sum_const 1).trans $ nat.smul_one_eq_coe _

@[simp] lemma degree_nat_cast (n : ℕ) : (n : G.picard_group).degree = card G * n :=
(sum_const (n : ℤ)).trans $ nsmul_eq_mul _ _

@[simp] lemma degree_int_cast (n : ℤ) : (n : G.picard_group).degree = card G * n :=
(sum_const n).trans $ nsmul_eq_mul _ _

/-- The rank of a divisor `d` is the greatest `n` such that all divisors of degree `n` are less than
`d`. -/
noncomputable def rank (d : G.picard_group) : ℤ :=
Sup {n : ℤ | ∀ ⦃e : G.picard_group⦄, e.degree = n → e ≤ d}

lemma rank_set_nonempty (hG : G.preconnected) (d : G.picard_group) :
  {n : ℤ | ∀ ⦃e : G.picard_group⦄, e.degree = n → e ≤ d}.nonempty := sorry --quite hard

@[simp] lemma rank_of_is_empty [is_empty G] (d : G.picard_group) : d.rank = 0 := sorry

lemma rank_le_degree (hG : G.preconnected) (d : G.picard_group) : d.rank ≤ d.degree :=
begin
  casesI is_empty_or_nonempty G,
  { simp },
  refine cSup_le (d.rank_set_nonempty hG) (λ n hn, _),
  obtain ⟨e, rfl⟩ := exists_degree_eq G n,
  exact degree_mono (hn rfl),
end

@[simp] lemma rank_zero : (0 : G.picard_group).rank = 0 := sorry
@[simp] lemma le_rank_one : 1 ≤ (1 : G.picard_group).rank := sorry
@[simp] lemma le_rank_nat_cast (n : ℕ) : (n : ℤ) ≤ (n : G.picard_group).rank := sorry
@[simp] lemma le_rank_int_cast (n : ℤ) : n ≤ (n : G.picard_group).rank := sorry

end picard_group

open picard_group

variables (G)

/-- The canonical divisor of a graph. -/
def canonical_divisor : G.picard_group := picard_group.mk $ λ a, G.degree a - 2

variables [fintype G]

lemma gonality_aux : ∃ (n : ℕ) (d : G.picard_group), 0 < d.rank ∧ d.degree = n :=
⟨card G, 1, zero_lt_one.trans_le le_rank_one, degree_one⟩

open_locale classical

/-- The gonality of a graph is the minimum degree of a picard_group of positive rank. -/
noncomputable def gonality : ℕ := nat.find G.gonality_aux

@[simp] lemma degree_canonical_divisor [fintype G.E] :
  G.canonical_divisor.degree = 2 * G.genus - 2 := sorry
-- by simp [canonical_divisor, genus, ←nat.cast_sum, sum_degrees_eq_twice_card_edges, mul_add,
--   mul_sub, mul_comm, card_univ]

end multigraph
