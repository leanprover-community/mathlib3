
/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import data.mv_polynomial.comm_ring
import data.set.finite
import ring_theory.polynomial.homogeneous
import ring_theory.polynomial.basic
import order.symm_diff
import tactic.omega
-- import home_finder

/-!
# Homogenization
## Main definitions
* `mv_polynomial.homogenization`
## Main statements
* foo_bar_unique
## Notation
## Implementation details
* We homogenize polynomials over a given ground set of variables, rather than adjoining an extra
  variable to give the user more choice in the type of the polynomials involved.
## References
* [F. Bar, *Quuxes*][]
## Tags
-/

variables {R ι : Type*} [comm_semiring R]

open polynomial finset mv_polynomial

open_locale big_operators
noncomputable theory
namespace mv_polynomial

section finsupp

-- TODO can any assumptions be weakened
-- TODO version with monoid hom?
lemma finsupp.sum_update_add {α β : Type*} [add_comm_monoid α] [add_comm_monoid β]
  (f : ι →₀ α) (i : ι) (a : α) (g : ι → α → β) (hg : ∀ i, g i 0 = 0)
  (hgg : ∀ (a : ι) (b₁ b₂ : α), g a (b₁ + b₂) = g a b₁ + g a b₂) :
  (f.update i a).sum g + g i (f i) = f.sum g + g i a :=
begin
  simp_rw finsupp.update_eq_erase_add_single,
  rw finsupp.sum_add_index (λ i _, hg i) (λ i _, hgg i),
  conv_rhs {rw ← finsupp.update_self f i},
  rw finsupp.update_eq_erase_add_single,
  rw finsupp.sum_add_index (λ i _, hg i) (λ i _, hgg i),
  rw add_assoc,
  rw add_assoc,
  congr' 1,
  rw add_comm,
  rw finsupp.sum_single_index (hg _),
  rw finsupp.sum_single_index (hg _),
end

end finsupp

/-- The homogenization of a multivariate polynomial at a single variable. -/
def homogenization (i : ι) (p : mv_polynomial ι R) :
  mv_polynomial ι R :=
-- ∑ j in p.support, monomial (j + finsupp.single i (p.total_degree - (j i))) (p.coeff j)
finsupp.map_domain (λ j, j + finsupp.single i (p.total_degree - j.sum (λ _ m, m))) p


namespace finsupp
open finsupp

@[simp] lemma support_map_domain {α β M : Type*} [add_comm_monoid M]
  (f : α ↪ β) (v : α →₀ M) : (finsupp.map_domain f v).support ⊆ v.support.map f :=
begin
  classical,
  rw finsupp.map_domain,
  refine finset.subset.trans finsupp.support_sum _,
  simp only [finsupp.mem_support_iff, finset.bUnion_subset_iff_forall_subset, ne.def],
  intros x hx,
  apply finset.subset.trans finsupp.support_single_subset,
  simp [hx],
end

lemma map_domain_apply' {α β M : Type*} [add_comm_monoid M] (S : set α) {f : α → β} (x : α →₀ M)
  (hS : (x.support : set α) ⊆ S) (hf : set.inj_on f S) {a : α} (ha : a ∈ S) :
  finsupp.map_domain f x (f a) = x a :=
begin
  classical,
  rw finsupp.map_domain,
  simp only [finsupp.sum_apply],
  rw finsupp.sum,
  simp_rw finsupp.single_apply,
  have : ∀ (a_1 : α) (ha1 : a_1 ∈ x.support),
    (if f a_1 = f a then x a_1 else 0) = (if f a_1 = f a then x a else 0),
  { intros a_1 ha_1,
    split_ifs with hh,
    rw hf _ ha hh,
    exact hS ha_1,
    refl, },
  conv in (ite _ _ _)
  { rw [this _ H], },
  by_cases ha : a ∈ x.support,
  rw ← finset.add_sum_erase _ _ ha,
  simp only [if_true, eq_self_iff_true],
  convert add_zero _,
  have : ∀ i ∈ x.support.erase a, f i ≠ f a,
  { intros i hi,
    have hix : i ∈ x.support,
    exact finset.mem_of_mem_erase hi,
    have hia : i ≠ a,
    exact finset.ne_of_mem_erase hi,
    exact hia ∘ (hf (hS hix) (hS ha)), },
  conv in (ite _ _ _)
  { rw if_neg (this x H), },
  simp only [finset.sum_const_zero],
  simp at ha,
  simp [ha],
end

lemma map_domain_inj_on {α β M : Type*} [add_comm_monoid M] (S : set α) {f : α → β}
  (hf : set.inj_on f S) :
  set.inj_on (finsupp.map_domain f : (α →₀ M) → (β →₀ M)) {w | (w.support : set α) ⊆ S} :=
begin
  intros v₁ hv₁ v₂ hv₂ eq,
  ext a,
  have : finsupp.map_domain f v₁ (f a) = finsupp.map_domain f v₂ (f a), { rw eq },
  rw [set.mem_set_of_eq] at hv₁ hv₂,
  classical,
  have hu : (v₁.support ∪ v₂.support : set α) ⊆ S := set.union_subset hv₁ hv₂,
  by_cases h : a ∈ v₁.support ∪ v₂.support,
  { rwa [map_domain_apply' S _ hv₁ hf _,
         map_domain_apply' S _ hv₂ hf _] at this,
    { apply hu,
      exact_mod_cast h, },
    { apply hu,
      exact_mod_cast h, }, },
  { simp only [decidable.not_or_iff_and_not, mem_union, not_not, finsupp.mem_support_iff] at h,
    simp [h], },
  -- rw [finsupp.map_domain_apply hf, finsupp.map_domain_apply hf] at this,
end
end finsupp


-- lemma support_homogenization [decidable_eq ι] (i : ι) (p : mv_polynomial ι R)
--   (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) : (p.homogenization i).support = p.support.image
--     (λ (j : ι →₀ ℕ), j + finsupp.single i (p.total_degree - j.sum (λ (_x : ι) (m : ℕ), m))) :=
-- begin
--   rw homogenization,
--   apply finsupp.support_map_domain _ _ _,
-- end

@[simp]
lemma homogenization_zero (i : ι) : (0 : mv_polynomial ι R).homogenization i = 0 :=
by simp [homogenization]

-- TODO this is probably useless
-- lemma map_domain_one {α β M : Type*} [has_zero β] [has_zero α] [has_one M]
--   [add_comm_monoid M] {f : α → β} (hf : f 0 = 0) :
--   finsupp.map_domain f (finsupp.single 0 1 : α →₀ M) = (finsupp.single 0 1 : β →₀ M) :=
-- by simp [hf]

-- TODO maybe instead prove this via is_homogeneous_one
@[simp]
lemma homogenization_one (i : ι) : (1 : mv_polynomial ι R).homogenization i = 1 :=
begin
  simp only [homogenization, total_degree_one, zero_tsub, add_zero, finsupp.single_zero],
  erw finsupp.map_domain_single,
  -- erw map_domain_one,
  refl,
end

@[simp]
lemma homogenization_C (i : ι) (c : R) : (C c : mv_polynomial ι R).homogenization i = C c :=
begin
  simp only [homogenization, total_degree_C, zero_tsub],
  convert finsupp.map_domain_single,
  rw single_eq_monomial,
  have : (0 : ι →₀ ℕ) i = 0,
  { simp only [finsupp.coe_zero, pi.zero_apply], },
  rw [← this],
  simp,
end

@[simp]
lemma homogenization_monomial (i : ι) (s : ι →₀ ℕ) (r : R) :
  (monomial s r : mv_polynomial ι R).homogenization i = monomial s r :=
begin
  by_cases hr : r = 0,
  { simp [hr], },
  erw [homogenization, finsupp.map_domain_single, single_eq_monomial, total_degree_monomial _ hr,
    tsub_self],
  simp,
end

-- TODO name this
lemma aux {i : ι} {p : mv_polynomial ι R} {x : ι →₀ ℕ} (hp : x ∈ p.support) :
  (x + finsupp.single i (p.total_degree - x.sum (λ _ m, m))).sum (λ _ m, m) = p.total_degree :=
begin
  rw finsupp.sum_add_index,
  rw [finsupp.sum_single_index],
  rw [add_tsub_cancel_iff_le],
  exact finset.le_sup hp,
  refl,
  intros, refl,
  intros, refl,
end

lemma is_homogeneous_homogenization (i : ι) (p : mv_polynomial ι R) :
  (p.homogenization i).is_homogeneous p.total_degree :=
begin
  letI := classical.dec_eq ι,
  rw homogenization,
  intros d hd,
  rw [finsupp.map_domain, finsupp.sum, coeff_sum] at hd,
  simp_rw [single_eq_monomial, coeff_monomial] at hd,
  contrapose! hd,
  have : ∀ (x : ι →₀ ℕ) (hx : x ∈ p.support),
    ¬ x + finsupp.single i (p.total_degree - x.sum (λ (_x : ι) (m : ℕ), m)) = d,
  { intros x hx hh,
    apply hd,
    rw ← hh,
    change (x + finsupp.single i (p.total_degree - x.sum (λ _ m, m))).sum (λ _ m, m) = _,
    rw aux hx, },
  conv in (ite _ _ _)
  { rw [if_neg (this x H)], },
  simp,
end

lemma homogenization_of_is_homogeneous (n : ℕ) (i : ι) (p : mv_polynomial ι R)
  (hp : p.is_homogeneous n) : p.homogenization i = p :=
begin
  by_cases hpn : p = 0,
  { simp [hpn], },
  rw homogenization,
  have := (hp.total_degree hpn).symm,
  subst this,
  rw is_homogeneous at hp,
  have : ∀ x (hx : x ∈ p.support),
    (λ (j : ι →₀ ℕ), j + finsupp.single i (p.total_degree - j.sum (λ (_x : ι) (m : ℕ), m))) x = x,
  { intros x hx,
    simp only [add_right_eq_self, finsupp.single_eq_same, tsub_eq_zero_iff_le, finsupp.single_tsub,
      finsupp.single_le_iff],
    rw ← hp (mem_support_iff.mp hx),
    exact le_refl _, },
  rw finsupp.map_domain_congr this,
  -- simp,
  erw finsupp.map_domain_id,
  -- TODO there should be a simp lemma version of this for λ x, x so simp works
end

lemma homogenization_idempotent (i : ι) (p : mv_polynomial ι R) :
  (p.homogenization i).homogenization i = p.homogenization i :=
begin
  classical,
  apply homogenization_of_is_homogeneous p.total_degree,
  exact is_homogeneous_homogenization _ _,
end


-- TODO should these hjp assumptions be phrased using `degree_of` or `vars`?
lemma homogenization_ne_zero_of_ne_zero (i : ι) {p : mv_polynomial ι R} (hp : p ≠ 0)
  (hjp : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) : p.homogenization i ≠ 0 :=
begin
  intro h,
  apply hp,
  have : set.inj_on (λ j : ι →₀ ℕ, j + finsupp.single i (p.total_degree - j.sum (λ _ m, m)))
          {w | w i = 0},
  { intros t ht y hy hh,
    simp only [set.mem_set_of_eq] at hh hy ht,
    ext a,
    have : (t + finsupp.single i (p.total_degree - t.sum (λ _ m, m))) a =
           (y + finsupp.single i (p.total_degree - y.sum (λ _ m, m))) a,
    { rw hh, },
    simp only [finsupp.coe_add, pi.add_apply] at this,
    classical,
    rw [finsupp.single_apply, finsupp.single_apply] at this,
    split_ifs at this with hia,
    { rw [← hia, ht, hy], },
    { simpa, }, },
  refine finsupp.map_domain_inj_on _ this _ (by simp) h,
  intros x hx,
  rw [set.mem_set_of_eq, hjp x hx],
  -- refine finsupp.map_domain_injective _ h,
  -- intros x y hxy,
  -- simp at hxy,
  -- -- TODO something like this but this isnt exactly true
  -- admit,
end

-- TODO this can follow from previous
lemma total_degree_homogenization (i : ι) (p : mv_polynomial ι R)
  (h : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) :
  (p.homogenization i).total_degree = p.total_degree :=
begin
  classical,
  by_cases hp : p = 0,
  { simp [hp], },
  apply is_homogeneous.total_degree,
  refine is_homogeneous_homogenization _ _,
  exact homogenization_ne_zero_of_ne_zero _ hp h,
  -- rw total_degree,
  -- have : (homogenization i p).support.nonempty,
  -- { simp [homogenization],
  --   admit,
  --    },
  -- rw ← finset.sup'_eq_sup this,
  -- rw finset.nonempty.sup'_eq_cSup_image,
  -- suffices : (λ (s : ι →₀ ℕ), s.sum (λ (n : ι) (e : ℕ), e)) '' ↑((homogenization i p).support) =
  --   {p.total_degree},
  -- { simp [this], },
  -- refine set.eq_singleton_iff_unique_mem.mpr _,
  -- split,
  -- { simp, admit, },
  -- { simp, admit, },
end

section leading_terms
-- TODO is this the best def?
/-- The sum of the monomials of highest degree of a multivariate polynomial. -/
def leading_terms (p : mv_polynomial ι R) : mv_polynomial ι R :=
homogeneous_component p.total_degree p

lemma leading_terms_apply (p : mv_polynomial ι R) : p.leading_terms =
  ∑ d in p.support.filter (λ d, ∑ i in d.support, d i = p.total_degree), monomial d (coeff d p) :=
homogeneous_component_apply _ _
-- (p.support.filter (λ s : ι →₀ ℕ, s.sum (λ _ e, e) = p.total_degree)).sum $
--   λ s, monomial s (p.coeff s)

@[simp]
lemma leading_terms_zero : (0 : mv_polynomial ι R).leading_terms = 0 :=
by simp [leading_terms]

lemma finset.filter_eq_self_iff {α : Type*} (S : finset α) (h : α → Prop) [decidable_pred h] :
  S.filter h = S ↔ ∀ s ∈ S, h s :=
begin
  cases S,
  simp only [finset.filter, finset.mem_mk, multiset.filter_eq_self],
end

-- TODO for non-zero polys this is true that p.lead = p iff p.is_homogenous n for a fixed n
-- TODO generalize to p.homog comp = n
lemma leading_terms_eq_self_iff_is_homogeneous (p : mv_polynomial ι R) :
  p.leading_terms = p ↔ p.is_homogeneous p.total_degree :=
begin
  split; intro h,
  { rw is_homogeneous,
    contrapose! h,
    rcases h with ⟨h_w, h_h₁, h_h₂⟩,
    rw [leading_terms, ne.def, mv_polynomial.ext_iff],
    push_neg,
    use h_w,
    classical,
    change ¬ h_w.sum (λ (_x : ι) (e : ℕ), e) = p.total_degree at h_h₂,
    simp only [h_h₁.symm, coeff_homogeneous_component, exists_prop, and_true, ne.def, not_false_iff,
      not_forall, ite_eq_left_iff],
    convert h_h₂, },
  { rw [leading_terms_apply],
    rw (_ : p.support.filter (λ (s : ι →₀ ℕ), ∑ (i : ι) in s.support, s i = p.total_degree)
            = p.support),
    { rw support_sum_monomial_coeff p, },
    { rw finset.filter_eq_self_iff,
      intros s hs,
      rw [mem_support_iff] at hs,
      rw ← h hs, }, },
end

@[simp]
lemma leading_terms_C (r : R) : (C r : mv_polynomial ι R).leading_terms = C r :=
begin
  rw leading_terms_eq_self_iff_is_homogeneous,
  convert is_homogeneous_C _ _,
  simp,
end

@[simp]
lemma leading_terms_monomial (s : ι →₀ ℕ) (r : R) : (monomial s r).leading_terms = monomial s r :=
begin
  by_cases hr : r = 0,
  { simp [hr], },
  rw leading_terms_eq_self_iff_is_homogeneous,
  convert is_homogeneous_monomial _ _ _ _,
  simpa [total_degree_monomial _ hr]
end

section dangerous_instance
local attribute [instance] mv_polynomial.unique
@[simp]
lemma leading_terms_X (s : ι) : (X s : mv_polynomial ι R).leading_terms = X s :=
begin
  nontriviality R,
  rw leading_terms_eq_self_iff_is_homogeneous,
  convert is_homogeneous_X _ _,
  exact total_degree_X _,
end
end dangerous_instance

lemma is_homogeneous_leading_terms (p : mv_polynomial ι R) :
  p.leading_terms.is_homogeneous p.total_degree :=
homogeneous_component_is_homogeneous (total_degree p) p

lemma exists_coeff_ne_zero_total_degree {p : mv_polynomial ι R} (hp : p ≠ 0) :
  ∃ (v : ι →₀ ℕ), v.sum (λ _ e, e) = p.total_degree ∧ p.coeff v ≠ 0 :=
begin
  obtain ⟨b, hb₁, hb₂⟩ := p.support.exists_mem_eq_sup (finsupp.support_nonempty_iff.mpr hp)
    (λ (m : ι →₀ ℕ), m.to_multiset.card),
  use b,
  split,
  { rw ← total_degree_eq p at hb₂,
    rw hb₂,
    dsimp, -- TODO break this out as a lemma
    funext m,
    exact (finsupp.card_to_multiset _).symm, },
  { exact mem_support_iff.mp hb₁, },
end

-- TODO mathlib
@[simp] lemma support_eq_empty {f : mv_polynomial ι R} : f.support = ∅ ↔ f = 0 :=
finsupp.support_eq_empty

lemma support_add_eq [decidable_eq ι] {g₁ g₂ : mv_polynomial ι R}
  (h : disjoint g₁.support g₂.support) : (g₁ + g₂).support = g₁.support ∪ g₂.support :=
finsupp.support_add_eq h

lemma add_ne_zero_of_ne_zero_of_support_disjoint [decidable_eq ι] (p q : mv_polynomial ι R)
  (hp : p ≠ 0) (h : disjoint p.support q.support) : p + q ≠ 0 :=
begin
  contrapose! hp,
  have := congr_arg support hp,
  rw [support_zero, support_add_eq h, finset.union_eq_empty_iff, -- TODO should this be simp?
    mv_polynomial.support_eq_empty] at this,
  exact this.left,
end

lemma support_sum_monomial_eq [decidable_eq R] (S : finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R) :
  support (∑ v in S, monomial v (f v)) = S.filter (λ v, f v ≠ 0) :=
begin
  letI := classical.dec_eq ι,
  induction S using finset.induction with s S hs hsi,
  { simp, },
  rw [finset.sum_insert hs, support_add_eq],
  { rw [hsi, filter_congr_decidable, filter_insert, support_monomial],
    split_ifs with h;
    { simp [h, insert_eq], }, },
  { apply disjoint_of_subset_left support_monomial_subset,
    simp [hsi, hs], },
end

lemma support_sum_monomial_subset (S : finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R) :
  support (∑ v in S, monomial v (f v)) ⊆ S :=
begin
  classical,
  rw support_sum_monomial_eq,
  apply filter_subset,
end

lemma sum_monomial_ne_zero_of_exists_mem_ne_zero (S : finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → R)
  (h : ∃ (s) (hs : s ∈ S), f s ≠ 0) : ∑ (s : ι →₀ ℕ) in S, monomial s (f s) ≠ 0 :=
begin
  classical,
  simp only [← support_eq_empty, support_sum_monomial_eq, filter_congr_decidable, ne.def],
  rcases h with ⟨s, h_S, h_s⟩,
  exact ne_empty_of_mem (mem_filter.mpr ⟨h_S, h_s⟩),
end

lemma leading_terms_ne_zero {p : mv_polynomial ι R} (hp : p ≠ 0) : p.leading_terms ≠ 0 :=
begin
  classical,
  rw leading_terms_apply,
  apply sum_monomial_ne_zero_of_exists_mem_ne_zero,
  simp only [exists_prop, mem_support_iff, finset.mem_filter],
  convert exists_coeff_ne_zero_total_degree hp,
  ext v,
  change v.sum (λ (_x : ι) (e : ℕ), e) with v.support.sum v,
  simp [and_comm],
end

@[simp]
lemma total_degree_homogenous_component_of_ne_zero {n : ℕ} {p : mv_polynomial ι R}
  (hp : homogeneous_component n p ≠ 0) :
  (homogeneous_component n p).total_degree = n :=
is_homogeneous.total_degree (homogeneous_component_is_homogeneous n p) hp

@[simp]
lemma total_degree_leading_terms (p : mv_polynomial ι R) :
  p.leading_terms.total_degree = p.total_degree :=
begin
  by_cases hp : p = 0,
  { simp [hp], },
  exact total_degree_homogenous_component_of_ne_zero (leading_terms_ne_zero hp),
end

-- TODO generalize this to homogeneous component idempotent?
lemma leading_terms_idempotent (p : mv_polynomial ι R) :
  p.leading_terms.leading_terms = p.leading_terms :=
begin
  rw [leading_terms_eq_self_iff_is_homogeneous, total_degree_leading_terms],
  exact is_homogeneous_leading_terms p,
end

-- TODO lol this isn't true
-- lemma homogeneous_component_mul (m n : ℕ) (p q : mv_polynomial ι R) :
--   homogeneous_component (m + n) (p * q) = homogeneous_component m p * homogeneous_component n q :=
-- begin
--   admit,
-- end

lemma coeff_leading_terms (p : mv_polynomial ι R) (d : ι →₀ ℕ) :
  coeff d p.leading_terms = if ∑ i in d.support, d i = p.total_degree then coeff d p else 0 :=
coeff_homogeneous_component _ _ _

lemma support_homogeneous_component (n : ℕ) (p : mv_polynomial ι R) :
  (homogeneous_component n p).support = p.support.filter (λ d, d.sum (λ _ m, m) = n) :=
begin
  rw homogeneous_component,
  simp only [finsupp.restrict_dom_apply, submodule.subtype_apply, function.comp_app,
    linear_map.coe_comp, set.mem_set_of_eq],
  erw ← finsupp.support_filter,
  refl,
end

lemma support_homogeneous_component_subset (n : ℕ) (p : mv_polynomial ι R) :
  (homogeneous_component n p).support ⊆ p.support :=
begin
  rw support_homogeneous_component,
  exact finset.filter_subset _ _,
end

lemma support_leading_terms (p : mv_polynomial ι R) :
  p.leading_terms.support = p.support.filter (λ d, d.sum (λ _ m, m) = p.total_degree) :=
support_homogeneous_component _ _

lemma support_leading_terms_subset (p : mv_polynomial ι R) : p.leading_terms.support ⊆ p.support :=
support_homogeneous_component_subset _ _

lemma eq_leading_terms_add (p : mv_polynomial ι R) (hp : p.total_degree ≠ 0) :
  ∃ p_rest : mv_polynomial ι R,
    p = p.leading_terms + p_rest ∧ p_rest.total_degree < p.total_degree :=
begin
  letI := classical.dec_eq ι,
  existsi (∑ (v : ι →₀ ℕ) in p.support \ p.leading_terms.support, (monomial v) (coeff v p)),
  split,
  { nth_rewrite 0 p.leading_terms.as_sum,
    have : ∀ (x : ι →₀ ℕ) (hx : x ∈ p.leading_terms.support), x.support.sum x = p.total_degree,
    { intros x hx,
      rw support_leading_terms at hx,
      simp at hx,
      exact hx.2, },
    simp_rw coeff_leading_terms,
    conv in (ite _ _ _)
    { rw [if_pos (this x H)], },
    have : p.leading_terms.support ⊆ p.support,
    from support_leading_terms_subset _,
    have : p.leading_terms.support ∩ p.support = p.leading_terms.support,
    { rw finset.inter_eq_left_iff_subset,
      exact this },
    nth_rewrite 0 ← this,
    rw [finset.inter_comm, finset.sum_inter_add_sum_diff],
    exact p.as_sum, },
  { rw [total_degree, finset.sup_lt_iff],
    intros b hb,
    rw support_leading_terms at hb,
    rw ← finset.filter_not at hb, -- TODO this was also hard to find maybe a negated version is good
    have := support_sum_monomial_subset _ _ hb,
    simp only [finset.mem_filter] at this,
    cases this,
    rw total_degree,
    exact lt_of_le_of_ne (finset.le_sup this_left) this_right,
    rw [bot_eq_zero],
    exact pos_iff_ne_zero.mpr hp, },
end

lemma leading_terms_add_of_total_degree_lt (p q : mv_polynomial ι R)
  (h : q.total_degree < p.total_degree) : (p + q).leading_terms = p.leading_terms :=
by rw [leading_terms, leading_terms, total_degree_add_eq_left_of_total_degree_lt h,
  linear_map.map_add, homogeneous_component_eq_zero _ q h, add_zero]

-- lemma C_mul_eq_smul {r : R} (p : mv_polynomial ι R) : C r * p = r • p :=
-- by rw [C_eq_smul_one, algebra.smul_mul_assoc, one_mul]

lemma no_zero_smul_divisors.eq_zero_or_eq_zero_iff_smul_eq_zero (R M : Type*) [has_zero R]
  [has_zero M] [smul_with_zero R M] [no_zero_smul_divisors R M] {c : R} {x : M} :
  c • x = 0 ↔ c = 0 ∨ x = 0 :=
begin
  split; intro h,
  exact eq_zero_or_eq_zero_of_smul_eq_zero h,
  cases h;
  simp [h],
end

--TODO this generalized lemma when distrib_mul_action_with_zero exists?
-- lemma support_smul_eq {α M R : Type*} {_ : monoid_with_zero R} [add_monoid M]
--   [distrib_mul_action_with_zero R M] [no_zero_smul_divisors R M] {b : R} (hb : b ≠ 0) {g : α →₀ M} :
--   (b • g).support = g.support :=
-- begin
--   ext a,
--   simp [finsupp.smul_apply, mem_support_iff, ne.def],
--   simp,
--   rw no_zero_smul_divisors.eq_zero_or_eq_zero_iff_smul_eq_zero,
-- end

-- haveI : no_zero_smul_divisors R (mv_polynomial ι R), --TODO add this instance
--TODO maybe this for leading terms and homog
-- lemma homogeneous_s_monomial_mul [no_zero_divisors R] (p : mv_polynomial ι R) (r : R) (x : ι →₀ ℕ) :
  -- (p * monomial x r).leading_terms = p.leading_terms * monomial x r :=
  --TODO also maybe an smul version
@[simp]
lemma leading_terms_C_mul [no_zero_smul_divisors R R] (p : mv_polynomial ι R) (r : R) :
  (C r * p).leading_terms = C r * p.leading_terms :=
begin
  by_cases hr : r = 0,
  { simp [hr], },
  have : (C r * p).support = p.support,
  { rw C_mul',
    exact finsupp.support_smul_eq hr, },
  rw [leading_terms, leading_terms, total_degree, this, homogeneous_component_C_mul],
  refl,
end

lemma eq_C_of_total_degree_zero {p : mv_polynomial ι R} (hp : p.total_degree = 0) :
  ∃ r : R, p = C r :=
begin
  letI := classical.dec_eq ι,
  erw finset.sup_eq_bot_iff at hp,
  simp only [mem_support_iff] at hp,
  use coeff 0 p,
  ext,
  by_cases hm : m = 0,
  { simp [hm], },
  rw [coeff_C, if_neg (ne.symm hm)],
  classical,
  by_contradiction h,
  specialize hp m h,
  apply hm,
  rw finsupp.sum at hp, -- TODO this and line below could be a lemma, finsupp.sum_eq_zero_iff?
  simp only [not_imp_self, bot_eq_zero, finsupp.mem_support_iff, finset.sum_eq_zero_iff] at hp,
  ext,
  simp [hp],
end

-- TODO can things be generalized to no_zero_divisors (would require an instance for mv_poly)
-- sadly this adds some imports and requirements not needed in rest of file
@[simp]
lemma leading_terms_mul {S : Type*} [comm_ring S] [is_domain S] (p q : mv_polynomial ι S) :
  (p * q).leading_terms = p.leading_terms * q.leading_terms :=
begin
  by_cases hp : p.total_degree = 0,
  { rcases eq_C_of_total_degree_zero hp with ⟨rp, rfl⟩,
    rw [leading_terms_C_mul, leading_terms_C], },
  by_cases hq : q.total_degree = 0,
  { rcases eq_C_of_total_degree_zero hq with ⟨rq, rfl⟩,
    rw [mul_comm, leading_terms_C_mul, leading_terms_C, mul_comm], },
  have : (p.leading_terms * q.leading_terms).total_degree = p.total_degree + q.total_degree,
  { rw is_homogeneous.total_degree,
    apply is_homogeneous.mul (is_homogeneous_leading_terms p) (is_homogeneous_leading_terms q),
    apply mul_ne_zero,
    { apply leading_terms_ne_zero, -- TODO maybe this can be a lemma ne_zero_of_total_degree_ne_zero
      intro hh,
      subst hh,
      simpa, },
    { apply leading_terms_ne_zero, -- TODO maybe this can be a lemma ne_zero_of_total_degree_ne_zero
      intro hh,
      subst hh,
      simpa, }, },
  rcases eq_leading_terms_add p hp with ⟨wp, hp, tp⟩,
  rw hp,
  rcases eq_leading_terms_add q hq with ⟨wq, hq, tq⟩,
  rw hq,
  simp only [add_mul, mul_add],
  rw [add_assoc, leading_terms_add_of_total_degree_lt, leading_terms_add_of_total_degree_lt,
    leading_terms_add_of_total_degree_lt, leading_terms_idempotent, leading_terms_idempotent,
    leading_terms_eq_self_iff_is_homogeneous],
  { convert is_homogeneous.mul (is_homogeneous_leading_terms _) (is_homogeneous_leading_terms _), },
  { rwa total_degree_leading_terms, },
  { rwa total_degree_leading_terms, },
  { rw this,
    calc _ ≤ max (wp * q.leading_terms).total_degree (p.leading_terms * wq + wp * wq).total_degree :
              total_degree_add _ _
       ... ≤ max (wp * q.leading_terms).total_degree
              (max (p.leading_terms * wq).total_degree (wp * wq).total_degree) :
                max_le_max (le_refl _) (total_degree_add _ _)
       ... ≤ max (wp.total_degree + q.leading_terms.total_degree)
              (max (p.leading_terms * wq).total_degree (wp * wq).total_degree) :
                max_le_max (total_degree_mul _ _) (le_refl _)
       ... ≤ max (wp.total_degree + q.leading_terms.total_degree)
              (max (p.leading_terms.total_degree + wq.total_degree)
                (wp.total_degree + wq.total_degree)) :
                  max_le_max (le_refl _) (max_le_max (total_degree_mul _ _) (total_degree_mul _ _))
       ... < p.total_degree + q.total_degree : _,
    simp only [total_degree_leading_terms, max_lt_iff, add_lt_add_iff_right, add_lt_add_iff_left],
    exact ⟨tp, tq, add_lt_add tp tq⟩, },
end

lemma total_degree_mul_eq {S : Type*} [comm_ring S] [is_domain S] {p q : mv_polynomial ι S}
  (hp : p ≠ 0) (hq : q ≠ 0) : (p * q).total_degree = p.total_degree + q.total_degree :=
begin
  rw [← total_degree_leading_terms, ← total_degree_leading_terms p, ← total_degree_leading_terms q,
    leading_terms_mul, is_homogeneous.total_degree],
  apply is_homogeneous.mul;
  simp [is_homogeneous_leading_terms],
  apply mul_ne_zero (leading_terms_ne_zero hp) (leading_terms_ne_zero hq),
end

end leading_terms

lemma homogenization_add_of_total_degree_eq (i : ι) (p q : mv_polynomial ι R)
  (h : p.total_degree = q.total_degree) (hpq : p.total_degree = (p + q).total_degree) :
  (p + q).homogenization i = p.homogenization i + q.homogenization i :=
by simp only [homogenization, finsupp.map_domain_add, ←h, ←hpq]

lemma auxx (f s p q fs ss : ℕ) (hp : fs ≤ p) (hp : ss ≤ q) :
  f + s + (p + q - (fs + ss)) = f + (p - fs) + (s + (q - ss)) := by omega

lemma homogenization_mul {S : Type*} [comm_ring S] [is_domain S] (i : ι) (p q : mv_polynomial ι S) :
  -- TODO is this cond needed?
  --(hp : ∀ j ∈ p.support, (j : ι → ℕ) i = 0) (hq : ∀ j ∈ q.support, (j : ι → ℕ) i = 0) :
  (p * q).homogenization i = p.homogenization i * q.homogenization i :=
begin
  by_cases hp : p = 0,
  { simp [hp], },
  by_cases hq : q = 0,
  { simp [hq], },
  rw [homogenization, homogenization, homogenization, total_degree_mul_eq hp hq,
    ← finsupp.sum_single p, ← finsupp.sum_single q, finsupp.map_domain_sum, finsupp.map_domain_sum],
  erw [finset.sum_mul_sum, finset.sum_mul_sum],
  simp only [finsupp.single_add, finsupp.sum_single, monomial_mul],
  rw finsupp.map_domain_finset_sum,
  apply finset.sum_congr rfl,
  intros a ha,
  simp only [finset.mem_product] at ha,
  rw [finsupp.map_domain_single, finsupp.map_domain_single],
  simp_rw [single_eq_monomial],
  simp only [finsupp.single_add, monomial_mul],
  erw finsupp.map_domain_single,
  congr' 1,
  rw finsupp.sum_add_index,
  simp only [finsupp.single_add, finsupp.single_tsub],
  ext j,
  simp only [pi.add_apply, finsupp.coe_add, finsupp.coe_tsub, pi.sub_apply],
  classical,
  refine auxx _ _ _ _ _ _ _ _,
  { rw finsupp.single_apply,
    split_ifs,
    { simp only [h, finsupp.single_eq_same],
      convert finset.le_sup ha.left,
      congr, }, -- TODO what is going on here?
    { simp, }, },
  { rw finsupp.single_apply,
    split_ifs,
    { simp only [h, finsupp.single_eq_same],
      convert finset.le_sup ha.right,
      congr, }, -- TODO what is going on here?
    { simp, }, },
  { intros i _, refl, },
  { intro i, simp, },
end

section dangerous_instance
local attribute [instance] mv_polynomial.unique

@[simp]
lemma homogenization_X_add_C {i j : ι} (r : R) :
  (X j + C r : mv_polynomial ι R).homogenization i = X j + C r * X i :=
begin
  nontriviality R,
  have : (X j + C r).total_degree = 1,
  { rw total_degree_add_eq_left_of_total_degree_lt,
    { exact total_degree_X _, },
    { simp only [total_degree_C, total_degree_X, nat.lt_one_iff], }, },
  erw [homogenization, finsupp.map_domain_add, finsupp.map_domain_single,
    finsupp.map_domain_single],
  simp only [tsub_zero, finsupp.sum_zero_index, finsupp.sum_single_index, this, add_zero,
    finsupp.single_zero, zero_add, single_eq_monomial],
  rw [X, X],
  congr,
  rw [monomial_eq_C_mul_X, pow_one],
  refl,
end

@[simp]
lemma homogenization_X_sub_C {R : Type*} [comm_ring R] {i j : ι} (r : R) :
  (X j - C r : mv_polynomial ι R).homogenization i = X j - C r * X i :=
by rw [sub_eq_add_neg, sub_eq_add_neg, ← C_neg, homogenization_X_add_C,
  C_neg, neg_mul]

lemma support_X_pow [nontrivial R] (s : ι) (n : ℕ) :
  (X s ^ n : mv_polynomial ι R).support = {finsupp.single s n} :=
begin
  classical,
  rw [X, monomial_pow, support_monomial, if_neg, finsupp.smul_single', mul_one],
  { rw [one_pow],
    exact one_ne_zero, },
end

@[simp]
lemma homogenization_X_pow_add_C {i j : ι} {n : ℕ} (hn : 0 < n) (r : R) :
  (X j ^ n + C r : mv_polynomial ι R).homogenization i = X j ^ n + C r * X i ^ n :=
begin
  nontriviality R,
  have : (X j ^ n + C r).total_degree = n,
  { rw total_degree_add_eq_left_of_total_degree_lt,
    { exact total_degree_X_pow _ _, },
    { simp only [total_degree_C, total_degree_X_pow, hn], }, },
  erw [homogenization, finsupp.map_domain_add],
  erw add_monoid_algebra.single_pow,
  erw [finsupp.map_domain_single,
    finsupp.map_domain_single],
  simp only [tsub_zero, finsupp.sum_zero_index, finsupp.sum_single_index, zero_add,
    single_eq_monomial, one_pow, mul_one, finsupp.smul_single', finsupp.single_tsub],
  congr,
  { rw total_degree_add_eq_left_of_total_degree_lt,
    simp [one_ne_zero],
    simp [one_ne_zero, hn], },
  { convert monomial_eq_C_mul_X,
    rw monomial_eq_C_mul_X,
    simp [this], },
end

@[simp]
lemma homogenization_X_pow_sub_C {R : Type*} [comm_ring R] {i j : ι} {n : ℕ} (hn : 0 < n) (r : R) :
  (X j ^ n - C r : mv_polynomial ι R).homogenization i = X j ^ n - C r * X i ^ n :=
by rw [sub_eq_add_neg, sub_eq_add_neg, ← C_neg, homogenization_X_pow_add_C hn,
  C_neg, neg_mul]

@[simp]
lemma homogenization_X_pow_sub_one {R : Type*} [comm_ring R] {i j : ι} {n : ℕ} (hn : 0 < n) :
  (X j ^ n - 1 : mv_polynomial ι R).homogenization i = X j ^ n - X i ^ n :=
begin
  convert homogenization_X_pow_sub_C hn _,
  simp,
end

@[simp]
lemma homogenization_X_pow_add_one {i j : ι} {n : ℕ} (hn : 0 < n) :
  (X j ^ n + 1 : mv_polynomial ι R).homogenization i = X j ^ n + X i ^ n :=
begin
  convert homogenization_X_pow_add_C hn _,
  simp,
end

end dangerous_instance

end mv_polynomial

namespace mv_polynomial
section

-- generalized version of the unprimed version
lemma support_sum_monomial_subset' [decidable_eq ι] {α : Type*} (S : finset α) (g : α → ι →₀ ℕ)
  (f : α → R) : support (∑ v in S, monomial (g v) (f v)) ⊆ S.image g :=
begin
  letI := classical.dec_eq α,
  induction S using finset.induction with s S hs hsi,
  { simp, },
  { rw finset.sum_insert hs,
    apply finset.subset.trans support_add,
    apply finset.union_subset,
    { apply finset.subset.trans support_monomial_subset _,
      rw finset.image_insert,
      convert finset.subset_union_left _ (finset.image g S), },
    { apply finset.subset.trans hsi _,
      rw finset.image_insert,
      exact finset.subset_insert (g s) (finset.image g S), }, },
end
open_locale pointwise

lemma support_mul' [decidable_eq ι] (p q : mv_polynomial ι R) :
  (p * q).support ⊆ p.support + q.support :=
begin
  -- TODO this was really hard to find, maybe needs a docstring or alias?
  rw [p.as_sum, q.as_sum, finset.sum_mul_sum],
  simp_rw [monomial_mul],
  rw [support_sum_monomial_coeff, support_sum_monomial_coeff],
  exact finset.subset.trans (support_sum_monomial_subset' _ _ _) (finset.subset.refl _),
end

section
open_locale pointwise

@[simp] lemma support_one : (1 : mv_polynomial ι R).support ⊆ 0 :=
finsupp.support_single_subset

@[simp] lemma support_one_of_nontrivial [nontrivial R] : (1 : mv_polynomial ι R).support = 0 :=
finsupp.support_single_ne_zero one_ne_zero

end

variable [decidable_eq ι]
lemma support_prod (P : finset (mv_polynomial ι R)) : (P.prod id).support ⊆ P.sum support :=
begin
  classical,
  induction P using finset.induction with p S hS hSi,
  { simp [support_X], },
  rw [finset.prod_insert hS, finset.sum_insert hS],
  simp only [id.def],
  refine finset.subset.trans (support_mul' _ _) _,
  convert finset.add_subset_add (finset.subset.refl _) hSi,
end

end

lemma prod_contains_no (i : ι) (P : finset (mv_polynomial ι R))
  (hp : ∀ (p : mv_polynomial ι R) (hp : p ∈ P) (j) (hjp : j ∈ p.support), (j : ι → ℕ) i = 0)
  (j) (hjp : j ∈ (P.prod id).support) :
  (j : ι → ℕ) i = 0 :=
begin
  classical,
  induction P using finset.induction with p S hS hSi generalizing j,
  { simp only [mem_support_iff, finset.prod_empty] at hjp,
    have : j = 0,
    sorry,
    simp [this], },
  { have := support_prod _ hjp,
    rw finset.prod_insert hS at hjp,
    rw finset.sum_insert hS at this,
    rw finset.mem_add at this,
    rcases this with ⟨y, z, hy, hz, hh⟩,
    rw ← hh,
    have := hp _ (finset.mem_insert_self p S) _ hy,
    simp only [pi.add_apply, add_eq_zero_iff, finsupp.coe_add],
    rw hSi _ z _,
    { rw this,
      simp, },
    { intros p hpp j hj,
      exact hp p (finset.mem_insert_of_mem hpp) j hj, },
    sorry,
    -- TODO probably need more lemmas for this still
    -- apply support_prod,
  },
  -- TODO this proof should be simple with `support_prod` we know j is in
  -- { simp only [finset.prod_insert hS, id.def, ne.def] at hjp,
  --   apply hSi, },
end


open_locale big_operators
lemma homogenization_prod {σ S : Type*} [comm_ring S] [is_domain S] (i : ι)
  (P : σ → mv_polynomial ι S) (L : finset σ) :
  (∏ l in L, P l).homogenization i = ∏ l in L, (P l).homogenization i :=
begin
  classical,
  induction L using finset.induction with p S hS hSi,
  { simp, },
  simp only [finset.prod_insert hS],
  rw homogenization_mul,
  rw hSi,
end

lemma homogenization_prod_id {S : Type*} [comm_ring S] [is_domain S] (i : ι)
  (P : finset (mv_polynomial ι S)) :
  (P.prod id).homogenization i = P.prod (λ p, p.homogenization i) :=
begin
  classical,
  induction P using finset.induction with p S hS hSi,
  { simp, },
  simp only [finset.prod_insert hS],
  rw homogenization_mul,
  rw hSi,
  rw [id.def],
end

end mv_polynomial
