import data.real.ennreal
import topology.metric_space.basic
import linear_algebra.affine_space.ordered

variables {ι α M : Type*}

open set (univ ord_connected pi) function finset (hiding univ pi)
open_locale big_operators

def box_subadditive_on [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  (f : (ι → α) → (ι → α) → M) (s : set (ι → α)) :=
∀ ⦃lo : ι → α⦄ (hlo : lo ∈ s) ⦃hi : ι → α⦄ (hhi : hi ∈ s) ⦃i x⦄,
  lo i ≤ x → x ≤ hi i → f lo hi ≤ f lo (update hi i x) + f (update lo i x) hi

namespace box_subadditive_on

section ordered_monoid

variables [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  {f : (ι → α) → (ι → α) → M} {s : set (ι → α)} [ord_connected s] {lo mid hi : ι → α}

lemma le_sum_finset_subboxes (h : box_subadditive_on f s) (hlo : lo ∈ s) (hhi : hi ∈ s)
  (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) (t : finset ι) :
  f lo hi ≤ ∑ t' in t.powerset, f (t'.piecewise mid lo) (t'.piecewise hi $ t.piecewise mid hi) :=
begin
  induction t using finset.induction_on with j t hj iht, { simp [le_rfl] },
  simp only [sum_powerset_insert hj, piecewise_insert, ← sum_add_distrib],
  refine trans iht (sum_le_sum $ λ t' ht', _),
  rw [mem_powerset] at ht',
  have hj' : j ∉ t' := λ hj', hj (ht' hj'),
  have hmid : mid ∈ s := set.mem_of_le_of_le hlo hhi h₁ h₂,
  convert h _ _ _ _;
    try { simp only [update_piecewise_of_not_mem _ _ _ hj, update_piecewise_of_not_mem _ _ _ hj',
                      update_idem, update_eq_self, piecewise_eq_of_not_mem _ _ _ hj,
                      piecewise_eq_of_not_mem _ _ _ hj', h₁ j, h₂ j] },
  apply_rules [set.mem_of_le_of_le hlo hmid, le_piecewise_of_le_of_le, piecewise_le_of_le_of_le];
    refl',
  apply_rules [set.mem_of_le_of_le hmid hhi, le_piecewise_of_le_of_le, piecewise_le_of_le_of_le];
    refl'
end

variables [fintype ι]

lemma le_sum_subboxes (h : box_subadditive_on f s) (hlo : lo ∈ s) (hhi : hi ∈ s)
  (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
  f lo hi ≤ ∑ t : finset ι, f (t.piecewise mid lo) (t.piecewise hi mid) :=
by simpa using le_sum_finset_subboxes h hlo hhi h₁ h₂ finset.univ

end ordered_monoid

section preorder

variables {R : Type*} [decidable_eq ι] [fintype ι] [preorder α]
  [canonically_linear_ordered_comm_semiring R]
  {f g : (ι → α) → (ι → α) → R} {s : set (ι → α)} [ord_connected s] {lo mid hi : ι → α}

lemma exists_subbox_mul_lt_of_mul_lt (hf : box_subadditive_on f s)
  (hg : @box_subadditive_on ι α (order_dual R) _ _ _ g s) (hlo : lo ∈ s) (hhi : hi ∈ s)
  (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) {c : R} (hlt : c * g lo hi < f lo hi) :
  ∃ t : finset ι, c * g (t.piecewise mid lo) (t.piecewise hi mid) <
    f (t.piecewise mid lo) (t.piecewise hi mid) :=
begin
  contrapose! hlt,
  calc f lo hi ≤ ∑ t : finset ι, f (t.piecewise mid lo) (t.piecewise hi mid) :
    hf.le_sum_subboxes hlo hhi h₁ h₂
  ... ≤ ∑ t : finset ι, c * g (t.piecewise mid lo) (t.piecewise hi mid) :
    sum_le_sum (λ t _, hlt t)
  ... = c * ∑ t : finset ι, g (t.piecewise mid lo) (t.piecewise hi mid) :
    mul_sum.symm
  ... ≤ c * g lo hi :
    canonically_ordered_semiring.mul_le_mul_left' (hg.le_sum_subboxes hlo hhi h₁ h₂) c
end

end preorder

variables {R : Type*} [decidable_eq ι] [fintype ι] [canonically_linear_ordered_comm_semiring R]

def aux_set (s : set (ι → ℝ)) (f g : (ι → ℝ) → (ι → ℝ) → R) (c : R) :
  set ((ι → ℝ) × (ι → ℝ)) :=
{p | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≤ p.2 ∧ c * g p.1 p.2 < f p.1 p.2}

def next (s : set (ι → ℝ)) [ord_connected s] (f g : (ι → ℝ) → (ι → ℝ) → R)
  (hf : box_subadditive_on f s) (hg : @box_subadditive_on ι ℝ (order_dual R) _ _ _ g s) (c : R)
  (p : aux_set s f g c) : {p' : aux_set s f g c // dist p'.1.1 p'.1.2 = dist p.1.1 p.1.2 / 2 } :=
begin
  let mid : ι → ℝ := midpoint ℝ p.1.1 p.1.2,
--   have h₁ : p.1.1 ≤ mid := left_le_midpoint.2 _,
  
end



end box_subadditive_on
