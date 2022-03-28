import ring_theory.graded_algebra.basic
import data.mv_polynomial.basic

section mv_polynomial

open mv_polynomial direct_sum
open_locale direct_sum big_operators

variables (R : Type*) [comm_ring R] (σ : Type*)
  [Π (i : ℕ) (x : homogeneous_submodule σ R i), decidable (x ≠ 0)]

noncomputable def decompose (p : mv_polynomial σ R) :
  ⨁ i, (homogeneous_submodule σ R i) :=
∑ i in finset.range (p.total_degree + 1), of (λ i, (homogeneous_submodule σ R i)) i
  ⟨(homogeneous_component i p), homogeneous_component_is_homogeneous i _⟩

lemma homogeneous_component_of_direct_sum
  (i : ℕ) (x : ⨁ i, homogeneous_submodule σ R i) :
homogeneous_component i (submodule_coe _ x) = x i :=
begin
  rw [←sum_support_of _ x, linear_map.map_sum, linear_map.map_sum],
  simp_rw [submodule_coe_of],
  simp only [add_subgroup.coe_subtype, submodule.coe_sum, dfinsupp.finset_sum_apply],
  apply finset.sum_congr rfl,
  intros j hj,
  rw homogeneous_component_homogeneous_polynomial i j,
  split_ifs,
  { rw [h, of_eq_same]  },
  { rw of_eq_of_ne _ _ _ _ (ne.symm h), refl },
  { simp only [mem_homogeneous_submodule],
    convert (x j).2 },
end

lemma left_inv (x) :
  (decompose R σ) (submodule_coe (λ (i : ℕ), homogeneous_submodule σ R i) x) = x :=
begin
  rw decompose,
  simp_rw [homogeneous_component_of_direct_sum],
  conv_rhs { rw ←direct_sum.sum_support_of _ x },
  rw [show finset.range ((submodule_coe _ x).total_degree + 1) = x.support ∪
      ((finset.range ((submodule_coe _ x).total_degree + 1)) \ x.support), begin
      rw finset.union_sdiff_of_subset,
      intros a ha,
      simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_range] at ha ⊢,
      contrapose! ha,
      have := homogeneous_component_eq_zero _ _ ha,
      rw [homogeneous_component_of_direct_sum, ← subtype.val_eq_coe] at this,
      rw [subtype.ext_iff_val, this],
      refl
    end, finset.sum_union, show ∑ (j : ℕ) in finset.range (((submodule_coe _) x).total_degree + 1) \
      dfinsupp.support x,
      (of (λ (i : ℕ), ↥(homogeneous_submodule σ R i)) j) ⟨(x j), _⟩ = 0, from _, add_zero,
    finset.sum_congr rfl (λ i hi, _)],
  { simp, },
  { rw ←finset.sum_const_zero,
    apply finset.sum_congr rfl (λ i hi, _),
    simp only [set_like.eta, not_not, finset.mem_sdiff, ne.def, dfinsupp.mem_support_to_fun,
      finset.mem_range] at hi ⊢,
    rw [hi.2, map_zero], },
  { exact disjoint_sdiff_self_right },
end

lemma right_inv (x) : submodule_coe _ (decompose R σ x) = x :=
begin
  rw [decompose, linear_map.map_sum],
  conv_rhs { rw ← sum_homogeneous_component x },
  apply finset.sum_congr rfl (λ _ _, _),
  rw submodule_coe_of,
  refl,
end

noncomputable instance mv_polynomial_is_graded :
  graded_algebra (λ i : ℕ, (homogeneous_submodule σ R i)) :=
{ one_mem := is_homogeneous_one σ R,
  mul_mem := λ i j x y hx hy, is_homogeneous.mul hx hy,
  decompose' := decompose R σ,
  left_inv := λ x, by apply left_inv R σ,
  right_inv := λ x, by apply right_inv R σ }

end mv_polynomial
