/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import algebra.direct_sum.algebra
import data.mv_polynomial
import ring_theory.polynomial.homogeneous

/-! # Typeclass for commutative graded ring
-/

open_locale direct_sum big_operators

section graded_ring

variables {R : Type*} [ring R] {ι : Type*} [decidable_eq ι]
  (A : ι → add_subgroup R)

/-- The canonical embedding from `⨁ i, A i` to `R`-/
def direct_sum.add_subgroup_coe : (⨁ i, A i) →+ R :=
direct_sum.to_add_monoid (λ i, (A i).subtype)

variables (R) [add_comm_monoid ι]

/-- A graded ring is a `ring R` such that `R` can be decomposed into a collection of
  `add_subgroups R` indexed by `ι` such that the connonical map `R → ⨁ i, A i` is a bijective map
  respecting multiplication, i.e. product of an element of degree `i` and an element of degree `j`
  is an element of degree `i + j`.
-/
class graded_ring :=
( decompose : R → ⨁ i, A i)
( left_inv : function.left_inverse decompose (direct_sum.add_subgroup_coe A) )
( right_inv : function.right_inverse decompose (direct_sum.add_subgroup_coe A) )
( one_degree_zero : (1 : R) ∈ A 0 )
( mul_respect_grading : ∀ {i j : ι} {a b : R}, a ∈ A i → b ∈ A j → a * b ∈ A (i + j))

lemma graded_ring.is_internal  [graded_ring R A] : direct_sum.add_subgroup_is_internal A :=
⟨graded_ring.left_inv.injective, graded_ring.right_inv.surjective⟩

instance gsemiring.of_ring_is_internally_graded [graded_ring R A] :
  direct_sum.gsemiring (λ i, A i) :=
direct_sum.gsemiring.of_add_subgroups A
  (graded_ring.one_degree_zero) (λ i j ai aj, graded_ring.mul_respect_grading ai.2 aj.2)

/--If `R` is graded by `ι` with degree `i` component `A i`, then `(⨁ i, A i ≃+* R)`-/
def recompose [graded_ring R A] : (⨁ i, A i) ≃+* R :=
let f : (⨁ i, A i) →+* R :=
  direct_sum.to_semiring (λ i, (A i).subtype) rfl (λ _ _ _ _, rfl) in
{ to_fun := f,
  inv_fun := graded_ring.decompose,
  left_inv := graded_ring.left_inv,
  right_inv := graded_ring.right_inv,
  map_mul' := ring_hom.map_mul _,
  map_add' := ring_hom.map_add _, }

/-- The projection maps of graded ring-/
def graded_ring.proj [graded_ring R A] (i : ι) (r : R) : R :=
  (@graded_ring.decompose R _  ι _ A _  _ r i).val

lemma graded_ring.proj_mem [graded_ring R A] (i : ι) (r : R) :
  graded_ring.proj R A i r ∈ A i := (@graded_ring.decompose R _  ι _ A _  _ r i).2

/-- The support of `r` is the `finset` where `proj R A i r ≠ 0 ↔ i ∈ r.support`-/
def graded_ring.support [graded_ring R A] [Π (i : ι) (x : (λ (i : ι), ↥(A i)) i), decidable (x ≠ 0)]
  (r : R) : finset ι :=
(@graded_ring.decompose R _ ι _ A _ _ r).support

lemma graded_ring.mem_support_iff [graded_ring R A]
  [Π (i : ι) (x : (λ (i : ι), ↥(A i)) i), decidable (x ≠ 0)]  (r : R) (i : ι) :
i ∈ graded_ring.support R A r ↔ (graded_ring.proj R A i r ≠ 0) :=
⟨λ hi, begin
  contrapose! hi,
  unfold graded_ring.support,
  unfold graded_ring.proj at hi,
  simp only [not_not, ne.def, dfinsupp.mem_support_to_fun, subtype.val_eq_coe] at hi ⊢,
  have : ↑((graded_ring.decompose r) i) = ↑(⟨0, add_subgroup.zero_mem (A i)⟩ : A i),
  exact hi,
  exact subtype.coe_injective this,
end, λ hi, begin
  unfold graded_ring.proj at hi,
  unfold graded_ring.support,
  simp only [ne.def, dfinsupp.mem_support_to_fun],
  intro rid, rw rid at hi,
  simp only [eq_self_iff_true, not_true, ne.def, add_subgroup.coe_zero, subtype.val_eq_coe] at hi,
  exact hi,
end⟩

end graded_ring

section mv_polynomial
open mv_polynomial direct_sum

variables (R : Type*) [comm_ring R] (σ : Type*)
  [Π (i : ℕ) (x : (λ i, ((homogeneous_submodule σ R i).to_add_subgroup)) i), decidable (x ≠ 0)]

private noncomputable def decompose (p : mv_polynomial σ R) :
  ⨁ i, (homogeneous_submodule σ R i).to_add_subgroup :=
∑ i in finset.range (p.total_degree + 1),
    of (λ i : ℕ, (homogeneous_submodule σ R i).to_add_subgroup) i ⟨(homogeneous_component i p),
     by { simp only [submodule.mem_to_add_subgroup, mem_homogeneous_submodule],
           apply homogeneous_component_is_homogeneous}⟩

private lemma homogeneous_component_of_direct_sum
  (i : ℕ) (x : ⨁ i, (homogeneous_submodule σ R i).to_add_subgroup) :
homogeneous_component i (add_subgroup_coe _ x) = x i :=
begin
  rw [eq_sum_of _ x, add_monoid_hom.map_sum, linear_map.map_sum, add_subgroup_coe],
  simp_rw to_add_monoid_of,
  simp only [add_subgroup.coe_subtype, submodule.coe_sum, dfinsupp.finset_sum_apply],
  apply finset.sum_congr rfl, intros j hj,
  rw homogeneous_component_homogeneous_polynomial i j,
  split_ifs,
  { rw [h, of_eq_same] },
  { rw of_eq_of_ne, refl, intro rid, exact h rid.symm },
  { simp only [mem_homogeneous_submodule], apply (x j).2 },
end

noncomputable instance mv_polynomial_is_graded : graded_ring (mv_polynomial σ R)
  (λ i : ℕ, (homogeneous_submodule σ R i).to_add_subgroup) :=
{ decompose := decompose R σ,
  left_inv := λ x, begin
    rw decompose,
    simp_rw [homogeneous_component_of_direct_sum],
    conv_rhs { rw direct_sum.eq_sum_of _ x },
    have set_eq :
      finset.range
        ((add_subgroup_coe (λ i, (homogeneous_submodule σ R i).to_add_subgroup) x).total_degree + 1)
      = x.support ∪ (finset.range ((add_subgroup_coe
          (λ i, (homogeneous_submodule σ R i).to_add_subgroup) x).total_degree + 1) \ x.support),
    { rw finset.union_sdiff_of_subset,
      intros a ha, simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_range] at ha ⊢,
      rw lt_iff_not_ge, intro rid, rw ge_iff_le at rid,
      have := homogeneous_component_eq_zero _ _ rid,
      rw homogeneous_component_of_direct_sum at this, apply ha,
      simp only [submodule.coe_eq_zero] at this, exact this, },
    rw [set_eq, finset.sum_union],
    have :
      ∑ k in finset.range
        ((add_subgroup_coe
          (λ i, (homogeneous_submodule σ R i).to_add_subgroup) x).total_degree + 1) \ x.support,
        (of (λ i, ↥((homogeneous_submodule σ R i).to_add_subgroup)) k) ⟨↑(x k), _⟩ = 0,
    { rw ←finset.sum_const_zero, apply finset.sum_congr rfl, intros i hi,
      simp only [set_like.eta, not_not, finset.mem_sdiff, ne.def, dfinsupp.mem_support_to_fun,
        finset.mem_range] at hi ⊢,
      rw hi.2, simp only [add_monoid_hom.map_zero], },
    rw [this, add_zero],
    apply finset.sum_congr, ext, simp only [dfinsupp.mem_support_to_fun],
    intros i hi, congr, simp only [set_like.eta],
    refine disjoint_sdiff_self_right,
  end,
  right_inv := λ p, begin
    rw [decompose, add_monoid_hom.map_sum],
    have :
      ∑ (x : ℕ) in finset.range (p.total_degree + 1),
        add_subgroup_coe _ ((of (λ i, ↥((homogeneous_submodule σ R i).to_add_subgroup)) x)
       ⟨(homogeneous_component x) p, _⟩) =
      ∑ x in finset.range (p.total_degree + 1),
        direct_sum.to_add_monoid _ ((of (λ i, ↥((homogeneous_submodule σ R i).to_add_subgroup)) x)
       ⟨(homogeneous_component x) p, _⟩) := rfl,
    rw this, simp_rw [to_add_monoid_of],
    conv_rhs { rw ←sum_homogeneous_component p }, apply finset.sum_congr rfl (λ _ _, rfl),
  end,
  one_degree_zero := begin
    simp only [mem_homogeneous_submodule, submodule.mem_to_add_subgroup],
    exact is_homogeneous_one σ R,
  end,
  mul_respect_grading := λ i j p q hp hq, begin
    simp only [mem_homogeneous_submodule, submodule.mem_to_add_subgroup],
    apply homogeneous_submodule_mul i j,
    apply submodule.mul_mem_mul; assumption,
  end }

end mv_polynomial
