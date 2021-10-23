import topology.opens
import ring_theory.ideal.prod
import linear_algebra.finsupp
import algebra.punit_instances
import ring_theory.homogeneous_ideal
import algebra.direct_sum.ring


noncomputable theory
open_locale classical direct_sum big_operators
open direct_sum

variables {ι : Type*} [linear_ordered_cancel_add_comm_monoid ι]
  {A : ι → Type*} [Π i, add_comm_group (A i)] [gcomm_semiring A]

local notation ι`⁺` := {i : ι // 0 < i}

private def irrelavent_ideal_embedding : (⨁ i : ι⁺, A i.val) →+ (⨁ i, A i) :=
{ to_fun := λ x, ∑ i in x.support, of A i.val (x i),
  map_add' := λ x y, begin
    have set_eq₁ : x.support = { i ∈ x.support | x i = - y i } ∪ { i ∈ x.support | x i ≠ - y i },
    { ext, split; intro h;
      simp only [ne.def, finset.mem_union, dfinsupp.mem_support_to_fun,
        finset.sep_def, finset.mem_filter] at h ⊢,
      rw [←and_or_distrib_left], refine ⟨h, or_not⟩,
      rw [←and_or_distrib_left] at h, exact h.1, },
    have set_eq₀ : (x + y).support = {i ∈ (x.support ∪ y.support) | x i ≠ - y i},
    { ext, split; intro h;
      simp only [add_apply, ne.def, finset.mem_union, dfinsupp.mem_support_to_fun, finset.sep_def,
        finset.mem_filter] at h ⊢, split,
      rw ←not_and_distrib, intro rid,
      rw [rid.1, rid.2, zero_add] at h, exact h rfl,
      intro rid, rw [rid, neg_add_eq_zero] at h, exact h rfl,
      intro rid, apply h.2, rw add_eq_zero_iff_eq_neg at rid, exact rid, },
    have set_eq₀' : (x + y).support = {i ∈ x.support | x i ≠ - y i} ∪ {i ∈ y.support | x i ≠ - y i},
    { rw set_eq₀, ext,
      rw [finset.sep_def, finset.filter_union, ←finset.sep_def, ←finset.sep_def], },
    have set_eq₂ : y.support = { i ∈ y.support | x i = - y i } ∪ { i ∈ y.support | x i ≠ - y i },
    { ext, split; intro h;
      simp only [ne.def, finset.mem_union, dfinsupp.mem_support_to_fun,
        finset.sep_def, finset.mem_filter] at h ⊢,
      rw [←and_or_distrib_left], refine ⟨h, or_not⟩,
      rw [←and_or_distrib_left] at h, exact h.1, },
    have set_eq₃ : { i ∈ x.support | x i = - y i } = { i ∈ y.support | x i = - y i},
    { ext, split; intro h;
      simp only [ne.def, dfinsupp.mem_support_to_fun, finset.sep_def, finset.mem_filter] at h ⊢;
      refine ⟨_, h.2⟩; intro rid, rw [rid, neg_zero] at h, exact h.1 h.2,
      rw rid at h, apply h.1, refine neg_eq_zero.mp h.2.symm, },

    rw [set_eq₀'],
    rw calc
            ∑ i in {i ∈ x.support | x i ≠ -y i} ∪ {i ∈ y.support | x i ≠ -y i},
              (of A i.val) ((x + y) i)
          = ∑ i in {i ∈ x.support | x i ≠ -y i}, of A i.val ((x + y) i)
          + ∑ i in {i ∈ y.support | x i ≠ -y i}, of A i.val ((x + y) i)
          - ∑ i in {i ∈ x.support | x i ≠ -y i} ∩ {i ∈ y.support | x i ≠ - y i},
              of A i.val ((x + y) i) : _ --(1)
      ... = ∑ i in {i ∈ x.support | x i ≠ -y i}, (of A i.val (x i) + of A i.val (y i))
          + ∑ i in {i ∈ y.support | x i ≠ -y i}, (of A i.val (x i) + of A i.val (y i))
          - ∑ i in {i ∈ x.support | x i ≠ -y i} ∩ {i ∈ y.support | x i ≠ -y i},
              (of A i.val (x i) + of A i.val (y i)) : _ --(2)
      ... = _ : by rw [finset.sum_add_distrib, finset.sum_add_distrib, finset.sum_add_distrib],

    rw show ∀ a b c d e f : ⨁ i, A i, (a + b) + (c + d) - (e + f) = (a + d) + ((b - f) + (c - e)),
      by {intros, ring},
    rw show ∑ x in {i ∈ dfinsupp.support x | x i ≠ -y i}, (of A x.val) (y x) -
            ∑ x in {i ∈ dfinsupp.support x | x i ≠ -y i} ∩ {i ∈ dfinsupp.support y | x i ≠ -y i},
        (of A x.val) (y x) = 0, from _, --(3)
    rw show ∑ x_1 in {i ∈ dfinsupp.support y | x i ≠ -y i}, (of A x_1.val) (x x_1) -
            ∑ x_1 in {i ∈ dfinsupp.support x | x i ≠ -y i} ∩ {i ∈ dfinsupp.support y | x i ≠ -y i},
      (of A x_1.val) (x x_1) = 0, from _, --(4)
    rw [zero_add, add_zero],
    conv_rhs { rw [set_eq₁, set_eq₂, set_eq₃], },
    rw [finset.sum_union, finset.sum_union],
    conv_rhs { rw show ∀ a b c d : ⨁ i, A i, a + b + (c + d) = (a + c) + (b + d),
      by { intros, ring } },
    rw [←finset.sum_add_distrib],
    rw show ∑ x_1 in {i ∈ dfinsupp.support y | x i = -y i},
              (of A x_1.val (x x_1) + of A x_1.val (y x_1)) =
            ∑ j in {i ∈ dfinsupp.support y | x i = -y i}, 0, from _, --(5)
    rw [finset.sum_const_zero, zero_add],

    -- (5)
    apply finset.sum_congr rfl,
    rintros j hj,
    simp only [ne.def, dfinsupp.mem_support_to_fun, finset.sep_def, finset.mem_filter] at hj,
    rw hj.2, simp only [add_monoid_hom.map_neg, add_left_neg],

    -- disjointness
    rw [finset.disjoint_iff_inter_eq_empty, finset.eq_empty_iff_forall_not_mem],
    intros j hj,
    simp only [ne.def, dfinsupp.mem_support_to_fun, finset.sep_def, finset.mem_filter,
    finset.mem_inter] at hj, exact hj.2.2 hj.1.2,

    rw [finset.disjoint_iff_inter_eq_empty, finset.eq_empty_iff_forall_not_mem],
    intros j hj,
    simp only [ne.def, dfinsupp.mem_support_to_fun, finset.sep_def, finset.mem_filter,
    finset.mem_inter] at hj, exact hj.2.2 hj.1.2,

    -- (4)
    rw sub_eq_zero, symmetry,
    rw finset.sum_subset_zero_on_sdiff, exact finset.inter_subset_right _ _,
    intros j hj, simp only [not_and, finset.sdiff_inter_self_right, not_not, finset.mem_sdiff,
      ne.def, dfinsupp.mem_support_to_fun, finset.sep_def, finset.mem_filter] at hj,
    have eq₀ : x j = 0, by_contra rid, exact hj.1.2 (hj.2 rid), rw [eq₀, add_monoid_hom.map_zero],
    intros, refl,

    -- (3)
    rw sub_eq_zero, symmetry,
    rw finset.sum_subset_zero_on_sdiff, exact finset.inter_subset_left _ _,
    intros j hj, simp only [not_and, finset.sdiff_inter_self_left, not_not, finset.mem_sdiff,
      ne.def, dfinsupp.mem_support_to_fun, finset.sep_def, finset.mem_filter] at hj,
    have eq₀ : y j = 0, by_contra rid, exact hj.1.2 (hj.2 rid), rw [eq₀, add_monoid_hom.map_zero],
    intros, refl,

    -- (1)
    rw [eq_sub_iff_add_eq, finset.sum_union_inter], ring_nf,

    -- (2)
    congr; simp only [add_monoid_hom.map_add, add_apply],
  end,
  map_zero' := by rw [direct_sum.support_zero, finset.sum_empty], }

def irrelavent_ideal : ideal (⨁ i, A i) :=
{ carrier :=  irrelavent_ideal_embedding '' set.univ,
  add_mem' := λ x y hx hy, begin
    simp only [set.image_univ, set.mem_range] at hx hy ⊢,
    obtain ⟨x', hx⟩ := hx,
    obtain ⟨y', hy⟩ := hy,
    use x' + y', simp only [add_monoid_hom.map_add, hx, hy],
  end,
  zero_mem' := ⟨0, ⟨set.mem_univ 0, add_monoid_hom.map_zero _⟩⟩,
  smul_mem' := λ c x hx, begin
    simp only [set.image_univ, set.mem_range, algebra.id.smul_eq_mul] at hx ⊢,
    obtain ⟨y, hy⟩ := hx,
    sorry,
  end }
