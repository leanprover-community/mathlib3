/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import algebra.direct_sum.algebra
import data.mv_polynomial
import ring_theory.polynomial.homogeneous

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
class graded_ring :=
( decompose : R → ⨁ i, A i)
( left_inv : function.left_inverse decompose (direct_sum.add_subgroup_coe A) )
( right_inv : function.right_inverse decompose (direct_sum.add_subgroup_coe A) )
( one_degree_zero : (1 : R) ∈ A 0 )
( mul_respect_grading : ∀ {i j : ι} {a b : R}, a ∈ A i → b ∈ A j → a * b ∈ A (i + j))

variable [graded_ring R A]

lemma graded_ring.is_internal : direct_sum.add_subgroup_is_internal A :=
⟨graded_ring.left_inv.injective, graded_ring.right_inv.surjective⟩

instance gsemiring.of_ring_is_internally_graded :
  direct_sum.gsemiring (λ i, A i) :=
direct_sum.gsemiring.of_add_subgroups A
  (graded_ring.one_degree_zero) (λ i j ai aj, graded_ring.mul_respect_grading ai.2 aj.2)

/--If `R` is graded by `ι` with degree `i` component `A i`, then `(⨁ i, A i ≃+* R)`-/
def graded_ring.recompose : (⨁ i, A i) ≃+* R :=
let f : (⨁ i, A i) →+* R :=
  direct_sum.to_semiring (λ i, (A i).subtype) rfl (λ _ _ _ _, rfl) in
{ to_fun := f,
  inv_fun := graded_ring.decompose,
  left_inv := graded_ring.left_inv,
  right_inv := graded_ring.right_inv,
  map_mul' := ring_hom.map_mul _,
  map_add' := ring_hom.map_add _, }

lemma graded_ring.trivial_inter (i : ι) :
   disjoint (A i) (Sup {a | ∃ j ≠ i, A j = a}) :=
begin
  by_cases empty_iota : {a | ∃ j ≠ i, A j = a}.nonempty,
  have := complete_lattice.independent_def''.mp
    (@direct_sum.submodule_is_internal.independent ι _ ℤ R _ _ _
      (λ i, add_subgroup.to_int_submodule (A i)) _) i,
  rw [disjoint_iff] at this ⊢, dsimp at this,
  rw add_subgroup.eq_bot_iff_forall,
  rw submodule.eq_bot_iff at this,
  intros x hx,
  obtain ⟨hx₁, hx₂⟩ := hx,
  apply this, split, exact hx₁,
  simp only [set_like.mem_coe, add_subgroup.coe_to_add_submonoid, ne.def] at hx₂ ⊢,

  have eq₁ : Sup {a | ∃ (j : ι) (H : ¬j = i), add_subgroup.to_int_submodule (A j) = a} =
    add_subgroup.to_int_submodule (Sup {a : add_subgroup R | ∃ (j : ι) (H : ¬j = i), A j = a}),
  { rw order_iso.map_cSup', congr, ext C, split; intros H,
    obtain ⟨j, hj₁, hj₂⟩ := H,
    use add_subgroup.to_int_submodule.symm C,
    split, refine ⟨j, hj₁, _⟩, rw ←hj₂,
    simp only [add_subgroup.to_int_submodule_to_add_subgroup, add_subgroup.to_int_submodule_symm],
    simp only [submodule.to_add_subgroup_to_int_submodule, add_subgroup.to_int_submodule_symm],

    obtain ⟨B, hB⟩ := H,
    obtain ⟨⟨j, hj₁, hj₂⟩, hB₂⟩ := hB,
    use j, use hj₁, rw [hj₂, hB₂],
    exact empty_iota,
    simp only [order_top.bdd_above], },

  rw eq₁,refine hx₂, rw direct_sum.submodule_is_internal.to_add_subgroup,
  simp_rw [add_subgroup.to_int_submodule_to_add_subgroup],
  exact graded_ring.is_internal R A,

  rw [set.not_nonempty_iff_eq_empty] at empty_iota,
  rw [empty_iota, Sup_empty], simp only [disjoint_bot_right],
end

lemma graded_ring.complete_lattice.independent :
  complete_lattice.independent (λ i, A i) :=
  complete_lattice.independent_def''.mpr (λ i, graded_ring.trivial_inter R A i)

/-- The projection maps of graded ring-/
def graded_ring.proj (i : ι) : R →+ R :=
(A i).subtype.comp $
  (dfinsupp.eval_add_monoid_hom i).comp $
  (graded_ring.recompose R A).symm.to_add_monoid_hom

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
  unfold graded_ring.proj, simp only [add_monoid_hom.coe_mk, subtype.val_eq_coe],
  have : graded_ring.decompose ((graded_ring.recompose R A) a) = a :=
    (graded_ring.recompose R A).symm_apply_apply a,
  rw this,
  unfold graded_ring.recompose,
  simp only [direct_sum.to_semiring_of, add_subgroup.coe_subtype, ring_equiv.coe_mk],
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
  intro rid, simp only [add_monoid_hom.coe_mk, ne.def, subtype.val_eq_coe] at hi, rw rid at hi,
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

section homogeneous_element
open_locale pointwise

variables (R : Type*) [ring R] {ι : Type*} (A : ι → add_subgroup R)

/-- An element `r : R` is said to be homogeneous if there is some
`i : ι` such that `r ∈ A i`-/
def is_homogeneous (r : R) : Prop := ∃ i, r ∈ A i

/--We collect all homogeneneous elements into a subtype `homogeneous_element` -/
def homogeneous_element : Type* := {r // is_homogeneous R A r}

instance homogeneous_element.has_mul [add_comm_monoid ι] [decidable_eq ι] [graded_ring R A] :
  has_mul (homogeneous_element R A) :=
{ mul := λ x y, ⟨x.1 * y.1, begin
  obtain ⟨i, hi⟩ := x.2,
  obtain ⟨j, hj⟩ := y.2,
  use (i + j), exact graded_ring.mul_respect_grading hi hj,
end ⟩ }

/--lifting is a `mul_hom`-/
def homogeneous_element.coe_mul_hom [decidable_eq ι] [add_comm_monoid ι] [graded_ring R A] :
  mul_hom (homogeneous_element R A) R :=
{ to_fun := λ r, r.1,
  map_mul' := λ x y, begin
    cases x, cases y, simp only [subtype.val_eq_coe], refl,
  end }

instance lift_homogeneous_element [decidable_eq ι] [add_comm_monoid ι] [graded_ring R A]
  : has_lift (homogeneous_element R A) R :=
{ lift := homogeneous_element.coe_mul_hom R A }


instance lift_homogeneous_set [decidable_eq ι] [add_comm_monoid ι]
  [graded_ring R A] :
  has_lift (set (homogeneous_element R A)) (set R) :=
{ lift := λ S, (homogeneous_element.coe_mul_hom R A) '' S }

variables [add_comm_monoid ι] [decidable_eq ι]

instance homogeneous_element_inhabited [graded_ring R A] : inhabited (homogeneous_element R A) :=
⟨⟨1, ⟨0, graded_ring.one_degree_zero⟩⟩⟩

end homogeneous_element

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
  rw [←sum_support_of _ x, add_monoid_hom.map_sum, linear_map.map_sum, add_subgroup_coe],
  simp_rw to_add_monoid_of,
  simp only [add_subgroup.coe_subtype, submodule.coe_sum, dfinsupp.finset_sum_apply],
  apply finset.sum_congr rfl, intros j hj,
  rw homogeneous_component_homogeneous_polynomial i j,
  split_ifs,
  { rw [h, of_eq_same] },
  { rw of_eq_of_ne, refl, intro rid, exact h rid.symm },
  { simp only [mem_homogeneous_submodule], apply (x j).2 },
end

@[nolint fails_quickly]
noncomputable instance mv_polynomial_is_graded : graded_ring (mv_polynomial σ R)
  (λ i : ℕ, (homogeneous_submodule σ R i).to_add_subgroup) :=
{ decompose := decompose R σ,
  left_inv := λ x, begin
    rw decompose,
    simp_rw [homogeneous_component_of_direct_sum],
    conv_rhs { rw ←direct_sum.sum_support_of _ x },
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
