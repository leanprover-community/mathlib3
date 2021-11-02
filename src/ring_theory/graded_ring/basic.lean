/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import algebra.direct_sum.algebra
import algebra.direct_sum.module

/-! # Typeclass for graded ring
For definition of a ring `R` being graded by `A : ι → add_subgroup R`, see doc string of
`graded_ring`.

- `graded_ring.decompose : R → ⨁ i, A i` and `graded_ring.recompose : ⨁ i, A i → R` are the ring
isomorphism between `R` and `⨁ i, A i` if `R` is graded by `A`.
- `graded_ring.complete_lattice.independent` states that the `A` is independent in the sense that
for any `i : ι`, `A i` and `⨆ (j ≠ i), A j` intersect trivially. The most noticable consequence of
this is that `A i` and `A j` intersects trivally for distinct `i` and `j`.
- `graded_ring.proj R A i r` is the degree `i : ι` component of `r : R`.
- `graded_ring.support R A r` is the `finset ι` containing the `i : ι` such that the degree `i`
component of `r` is not zero.
- `is_homogeneous R A x` states that `x ∈ A i` for some `i : ι`.
- `homogeneous_element R A` is the subtype of `R` of all `x` such that `is_homogeneous R A x`.
- `mv_polynomial_is_graded` provides an instance saying that `mv_polynomial R σ` is ring graded by
its homogeneous components.
-/

open_locale direct_sum big_operators

section graded_ring
variables (R : Type*) [ring R] {ι : Type*} (A : ι → add_subgroup R)
  [decidable_eq ι] [add_comm_monoid ι]

/-- A graded ring is a `ring R` such that `R` can be decomposed into a collection of
  `add_subgroups R` indexed by `ι` such that the connonical map `R → ⨁ i, A i` is a bijective map
  respecting multiplication, i.e. product of an element of degree `i` and an element of degree `j`
  is an element of degree `i + j`.
-/
class graded_ring.core :=
( one_degree_zero : (1 : R) ∈ A 0 )
( mul_respect_grading : ∀ {i j : ι} {a b : R}, a ∈ A i → b ∈ A j → a * b ∈ A (i + j))

/-- See above-/
class graded_ring extends graded_ring.core R A :=
( decompose : R → ⨁ i, A i)
( left_inv : function.left_inverse decompose (direct_sum.add_subgroup_coe A) )
( right_inv : function.right_inverse decompose (direct_sum.add_subgroup_coe A) )

lemma graded_ring.is_internal [graded_ring R A] : direct_sum.add_subgroup_is_internal A :=
⟨graded_ring.left_inv.injective, graded_ring.right_inv.surjective⟩


variable [graded_ring.core R A]

instance gsemiring.of_ring_is_internally_graded :
  direct_sum.gsemiring (λ i, A i) :=
direct_sum.gsemiring.of_add_subgroups A
  (graded_ring.core.one_degree_zero) (λ i j ai aj, graded_ring.core.mul_respect_grading ai.2 aj.2)

/-- The cannonical ring isomorphism between `⨁ i, A i` and `R`-/
def direct_sum.subgroup_coe_ring_hom : (⨁ i, A i) →+* R :=
  direct_sum.to_semiring (λ i, (A i).subtype) rfl (λ _ _ _ _, rfl)

variable [graded_ring R A]

/--If `R` is graded by `ι` with degree `i` component `A i`, then `(⨁ i, A i ≃+* R)`-/
def graded_ring.recompose : (⨁ i, A i) ≃+* R :=
{ to_fun := direct_sum.subgroup_coe_ring_hom R A,
  inv_fun := graded_ring.decompose,
  left_inv := graded_ring.left_inv,
  right_inv := graded_ring.right_inv,
  map_mul' := ring_hom.map_mul _,
  map_add' := ring_hom.map_add _, }

@[simp] lemma graded_ring.decompose_def :
  graded_ring.decompose = (graded_ring.recompose R A).symm := rfl

@[simp] lemma graded_ring.recompose_of {i : ι} (x : A i) :
  graded_ring.recompose R A (direct_sum.of _ i x) = x := dfinsupp.lift_add_hom_apply_single _ _ _

lemma graded_ring.complete_lattice.independent :
  complete_lattice.independent (λ i, A i) :=
direct_sum.add_subgroup_is_internal.independent R A (graded_ring.is_internal R A)

/-- The projection maps of graded ring-/
def graded_ring.proj (i : ι) : R →+ R :=
(A i).subtype.comp $
  (dfinsupp.eval_add_monoid_hom i).comp $
  (graded_ring.recompose R A).symm.to_add_monoid_hom

lemma graded_ring.proj_apply (i : ι) (r : R) :
  graded_ring.proj _ A i r = (graded_ring.decompose r : ⨁ i, A i) i := rfl

lemma graded_ring.proj_mem (i : ι) (r : R) :
  graded_ring.proj R A i r ∈ A i := (@graded_ring.decompose R _ ι A _ _ _ r i).2

/-- The support of `r` is the `finset` where `proj R A i r ≠ 0 ↔ i ∈ r.support`-/
def graded_ring.support [Π (i : ι) (x : (λ (i : ι), ↥(A i)) i), decidable (x ≠ 0)]
  (r : R) : finset ι :=
(@graded_ring.decompose R _ ι A _ _ _ r).support

lemma graded_ring.proj_recompose (a : ⨁ i, A i) (i : ι) :
  graded_ring.proj R A i (graded_ring.recompose R A a) =
  graded_ring.recompose R A (direct_sum.of _ i (a i)) :=
begin
  unfold graded_ring.proj,
  simp only [add_monoid_hom.coe_comp, add_subgroup.coe_subtype, function.comp_app,
    graded_ring.recompose_of, set_like.coe_eq_coe],
  erw ring_equiv.symm_apply_apply, refl,
end

variable [Π (i : ι) (x : (λ (i : ι), ↥(A i)) i), decidable (x ≠ 0)]

lemma graded_ring.mem_support_iff
  (r : R) (i : ι) :
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
  intro rid,
  simp only [add_monoid_hom.coe_comp, add_subgroup.coe_subtype, function.comp_app, ne.def] at hi,
  erw rid at hi,
  simp only [eq_self_iff_true, not_true, ne.def, add_subgroup.coe_zero, subtype.val_eq_coe] at hi,
  exact hi,
end⟩

lemma graded_ring.as_sum (r : R) :
  r = ∑ i in graded_ring.support R A r, graded_ring.proj R A i r :=
begin
  conv_lhs { rw [←@graded_ring.right_inv R _ ι A _ _ _ r,
    ←direct_sum.sum_support_of _ (@graded_ring.decompose R _ ι A _ _ _ r),
    add_monoid_hom.map_sum], },
  unfold graded_ring.support,
  unfold graded_ring.proj,
  apply finset.sum_congr, ext, simp only [dfinsupp.mem_support_to_fun],
  intros i hi, simp only [ne.def, dfinsupp.mem_support_to_fun, subtype.val_eq_coe] at hi ⊢,
  unfold direct_sum.add_subgroup_coe,
  rw direct_sum.to_add_monoid_of, refl,
end

lemma graded_ring.mul_proj (r r' : R) (i : ι) :
  graded_ring.proj R A i (r * r') =
  ∑ ij in finset.filter (λ ij : ι × ι, ij.1 + ij.2 = i)
    ((graded_ring.support R A r).product (graded_ring.support R A r')),
    (graded_ring.proj R A ij.1 r) * (graded_ring.proj R A ij.2 r') :=
begin
  have set_eq : (graded_ring.support R A r).product (graded_ring.support R A r') =
  finset.filter (λ ij : ι × ι, ij.1 + ij.2 = i) _ ∪
  finset.filter (λ ij : ι × ι, ij.1 + ij.2 ≠ i) _ := (finset.filter_union_filter_neg_eq _ _).symm,
  conv_lhs { rw [graded_ring.as_sum R A r, graded_ring.as_sum R A r', finset.sum_mul_sum,
    add_monoid_hom.map_sum, set_eq] },
  rw finset.sum_union,
  suffices : ∑ (x : ι × ι) in finset.filter (λ (ij : ι × ι), ij.fst + ij.snd ≠ i)
    ((graded_ring.support R A r).product (graded_ring.support R A r')),
  (graded_ring.proj R A i) ((graded_ring.proj R A x.fst) r * (graded_ring.proj R A x.snd) r') = 0,
  rw [this, add_zero], apply finset.sum_congr rfl,
  rintros ⟨j, k⟩ h, simp only [finset.mem_filter, finset.mem_product] at h ⊢,
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h,
  rw ←h₃,
  obtain ⟨a, rfl⟩ := (graded_ring.recompose R A).bijective.surjective r,
  obtain ⟨b, rfl⟩ := (graded_ring.recompose R A).bijective.surjective r',
  rw [graded_ring.proj_recompose, graded_ring.proj_recompose, ←ring_equiv.map_mul,
    direct_sum.of_mul_of, graded_ring.proj_recompose],
  congr, rw [direct_sum.of_eq_same],

  apply finset.sum_eq_zero, rintros ⟨j, k⟩ h,
  simp only [ne.def, finset.mem_filter, finset.mem_product] at h ⊢,
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h,
  obtain ⟨a, rfl⟩ := (graded_ring.recompose R A).bijective.surjective r,
  obtain ⟨b, rfl⟩ := (graded_ring.recompose R A).bijective.surjective r',
  rw [graded_ring.proj_recompose, graded_ring.proj_recompose, ←ring_equiv.map_mul,
    direct_sum.of_mul_of, graded_ring.proj_recompose, direct_sum.of_eq_of_ne],
  simp only [ring_equiv.map_zero, add_monoid_hom.map_zero], intro rid, exact h₃ rid,

  rw [finset.disjoint_iff_inter_eq_empty, finset.eq_empty_iff_forall_not_mem],
  rintros ⟨j, k⟩ rid,
  simp only [ne.def, finset.mem_filter, finset.mem_inter, finset.mem_product] at rid,
  rcases rid with ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩, exact h₂ h₁,
end

lemma graded_ring.proj_homogeneous_element {x : R} {i : ι} (hx : x ∈ A i) :
  graded_ring.proj R A i x = x :=
begin
  have dis := graded_ring.complete_lattice.independent R A i,
  rw [disjoint_iff, add_subgroup.eq_bot_iff_forall] at dis,

  by_cases mem_supp : i ∈ graded_ring.support R A x,

  have := calc
      x = ∑ i in graded_ring.support R A x, (graded_ring.proj R A i) x
        : graded_ring.as_sum R A x
    ... = (∑ j in (graded_ring.support R A x).erase i, (graded_ring.proj R A j) x)
        + graded_ring.proj R A i x
        : _,
  have eq₁ : (∑ j in (graded_ring.support R A x).erase i, (graded_ring.proj R A j x))
      =  x - (graded_ring.proj R A i x), symmetry, rw sub_eq_iff_eq_add, exact this,

  have mem₁ : ∑ j in (graded_ring.support R A x).erase i, (graded_ring.proj R A j) x ∈ A i,
  { rw eq₁, apply add_subgroup.sub_mem, exact hx, apply graded_ring.proj_mem, },

  have mem₂ : (∑ j in (graded_ring.support R A x).erase i, (graded_ring.proj R A j) x)
    ∈ (⨆ (j ≠ i), A j : add_subgroup R),
  { refine add_subgroup.sum_mem _ _,
    intros k hk, simp only [ne.def, finset.mem_erase] at hk,
    apply add_subgroup.mem_supr_of_mem k,
    refine @add_subgroup.mem_Sup_of_mem R _ _ (A k) _ (graded_ring.proj R A k x)
      (graded_ring.proj_mem R A k x),
    rw set.mem_range, use hk.1, },

  specialize dis _ (add_subgroup.mem_inf.mpr ⟨mem₁, mem₂⟩),
  rw [dis, zero_add] at this, exact this.symm,
  rw finset.sum_erase_add, exact mem_supp,

  have h : (∑ j in (graded_ring.support R A x).erase i, (graded_ring.proj R A j) x)
    ∈ (⨆ (j ≠ i), A j : add_subgroup R),
  { refine add_subgroup.sum_mem _ _,
    intros k hk, simp only [ne.def, finset.mem_erase] at hk,
    apply add_subgroup.mem_supr_of_mem k,
    refine @add_subgroup.mem_Sup_of_mem R _ _ (A k) _ (graded_ring.proj R A k x)
      (graded_ring.proj_mem R A k x),
    rw set.mem_range, use hk.1, },
  rw [finset.erase_eq_of_not_mem, ←graded_ring.as_sum R A x] at h,
  specialize dis _ (add_subgroup.mem_inf.mpr ⟨hx, h⟩),
  rw dis, simp only [add_monoid_hom.map_zero], exact mem_supp,
end

lemma graded_ring.proj_homogeneous_element_of_ne {x : R} {i j : ι} (hx : x ∈ A i) (hij : i ≠ j):
  graded_ring.proj R A j x = 0 :=
begin
  rw ←graded_ring.proj_homogeneous_element R A hx,
  obtain ⟨a, rfl⟩ := (graded_ring.recompose R A).bijective.surjective x,
  rw [graded_ring.proj_recompose, graded_ring.proj_recompose, direct_sum.of_eq_of_ne,
    add_monoid_hom.map_zero, ring_equiv.map_zero], exact hij,
end

end graded_ring
