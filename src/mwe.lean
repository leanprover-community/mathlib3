import algebra.big_operators.pi
import algebra.big_operators.order
import data.set.pointwise.big_operators
import data.set.intervals.pi
import measure_theory.measure.haar_of_basis

open set
open_locale pointwise big_operators

namespace fintype
variables {ι : Type*} {α : ι → Type*} [decidable_eq ι] [fintype ι] [Π i, comm_monoid (α i)]

@[to_additive] lemma prod_pi_mul_single (f : Π i, α i) : ∏ i, pi.mul_single i (f i) = f :=
begin
  ext i,
  rw [prod_apply, finset.prod_eq_single_of_mem _ (finset.mem_univ _), pi.mul_single_eq_same],
  exact λ j _ hij, pi.mul_single_eq_of_ne' hij _,
end

end fintype

namespace set
variables {ι : Type*} {α : ι → Type*} [decidable_eq ι] [fintype ι] [Π i, ordered_comm_monoid (α i)]

@[to_additive] lemma prod_Icc_mul_single_mul_single (f g : Π i, α i) :
  ∏ i, Icc (pi.mul_single i (f i)) (pi.mul_single i (g i)) = Icc f g :=
begin
  ext,
  simp only [set.mem_finset_prod, finset.mem_univ, forall_true_left, exists_prop,
    ←pi.image_mul_single_Icc],
  refine ⟨_, λ hx, ⟨λ i, pi.mul_single i (x i), λ i, mem_image_of_mem _ ⟨hx.1 _, hx.2 _⟩,
    fintype.prod_pi_mul_single _⟩⟩,
  rintro ⟨g, hg, rfl⟩,
  change ∀ i, _ at hg,
  choose t ht htg using hg,
  obtain rfl : _ = g := funext htg,
  rw [fintype.prod_pi_mul_single t, ←set.pi_univ_Icc],
  exact λ i _, ht _,
end

@[to_additive] lemma prod_Icc_mul_single_one (f : Π i, α i) :
  ∏ i, Icc (pi.mul_single i (f i)) 1 = Icc f 1 :=
by simpa using prod_Icc_mul_single_mul_single f 1

@[to_additive] lemma prod_Icc_one_mul_single (g : Π i, α i) :
  ∏ i, Icc 1 (pi.mul_single i (g i)) = Icc 1 g :=
by simpa using prod_Icc_mul_single_mul_single 1 g

end set

section ordered_comm_monoid
variables {ι α : Type*} [ordered_comm_monoid α]

@[to_additive] lemma prod_Ici_subset (s : finset ι) (f : ι → α) :
  ∏ i in s, Ici (f i) ⊆ Ici (∏ i in s, f i) :=
begin
  simp_rw [subset_def, set.mem_finset_prod],
  rintro _ ⟨g, hg, rfl⟩,
  exact finset.prod_le_prod' @hg,
end

@[to_additive] lemma prod_Iic_subset (s : finset ι) (f : ι → α) :
  ∏ i in s, Iic (f i) ⊆ Iic (∏ i in s, f i) :=
begin
  simp_rw [subset_def, set.mem_finset_prod],
  rintro _ ⟨g, hg, rfl⟩,
  exact finset.prod_le_prod' @hg,
end

@[to_additive] lemma prod_Icc_subset (s : finset ι) (f g : ι → α) :
  ∏ i in s, Icc (f i) (g i) ⊆ Icc (∏ i in s, f i) (∏ i in s, g i) :=
begin
  simp_rw [subset_def, set.mem_finset_prod],
  rintro _ ⟨g, hg, rfl⟩,
  exact ⟨finset.prod_le_prod' $ λ i hi, (hg hi).1, finset.prod_le_prod' $ λ i hi, (hg hi).2⟩,
end

end ordered_comm_monoid

namespace finset
variables {ι α : Type*} [comm_monoid α] [decidable_eq α] {s : finset ι} {f : ι → finset α} {a : α}

-- TODO: Rename `finset.mem_sum`
-- TODO: Make arguments to `set.mem_finset_prod` implicit
@[to_additive] lemma mem_finset_prod :
  a ∈ ∏ i in s, f i ↔ ∃ (g : ι → α) (hg : ∀ {i : ι}, i ∈ s → g i ∈ f i), ∏ i in s, g i = a :=
by { simp_rw ←mem_coe, push_cast, exact set.mem_finset_prod _ _ _ }

end finset

namespace set
variables {ι α : Type*} [comm_monoid α]

@[to_additive]
lemma finset_prod_image_pi (s : finset ι) (S : ι → set α) :
  (λ f : ι → α, ∏ i in s, f i) '' (s : set ι).pi S = ∏ i in s, S i :=
begin
  ext,
  simp_rw [set.mem_finset_prod, set.mem_image, set.mem_pi, exists_prop, finset.mem_coe],
end

end set

variables {ι E F : Type*} {α : ι → Type*} [fintype ι] [add_comm_group E] [module ℝ E]
  [add_comm_group F] [module ℝ F]

example (v : ι → E) :
  (λ a : ι → ℝ, finset.univ.sum (a • v)) ''
    univ.pi (λ (i : ι), Icc 0 1) = ∑ i, (λ a : ℝ, a • v i) '' Icc 0 1 :=
begin
  ext,
  simp only [set.mem_finset_sum, pi.smul_apply', mem_image, pi_univ_Icc, mem_Icc, finset.mem_univ,
    forall_true_left, exists_prop],
end

-- TODO: Use semi-implicit arguments in `set.mem_finset_sum`
lemma parallelepiped_eq_sum_segment (v : ι → E) : parallelepiped v = ∑ i, segment ℝ 0 (v i) :=
begin
  simp_rw [parallelepiped, segment_eq_image, smul_zero, zero_add, ←set.pi_univ_Icc,
    pi.zero_apply, pi.one_apply, ←finset.coe_univ, ←pi.smul_apply', set.finset_sum_image_pi,
    finset.coe_univ],
  sorry
end
