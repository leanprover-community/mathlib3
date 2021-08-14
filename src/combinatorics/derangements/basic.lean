/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
import dynamics.fixed_points.basic
import group_theory.perm.option

/-!
# Derangements on types

In this file we define `derangements α`, the set of derangements on a type `α`.

We also define:

* some related predicates: e.g.,

  - `only_possible_fixed_point f a`: either `f` has no fixed points, or `a` is the only fixed point;

  - `exactly_one_fixed_point f a`: `f` has exactly one fixed point, which is `a`;

* equivalences involving various subtypes of `perm α` and `derangements α`: e.g.,

  - `derangements_equiv_sigma_opfp`: an equivalence between `derangements (option α)` and the
    sigma-type `Σ a : α, {f : perm α // only_possible_fixed_point f a}`.
-/

open equiv function

/- Same as `(equiv.refl _)^.set.compl .symm.trans (subtype_equiv_right $ by simp)` but with better
unfolding -/
/-- Permutations on `sᶜ` are equivalent to permutations that fix `s` pointwise. -/
protected def perm.compl_equiv {α : Type*} (s : set α) [decidable_pred (∈ s)] :
  perm (sᶜ : set α) ≃ {f : perm α // ∀ a ∈ s, f a = a} :=
{ to_fun := λ f, ⟨f.of_subtype, λ a ha, f.of_subtype_apply_of_not_mem (λ h, h ha)⟩,
  inv_fun := λ ⟨f, hf⟩, (f : perm α).subtype_perm
    (λ a, ⟨λ ha hfa, ha (f.injective (hf _ hfa) ▸ hfa),  λ hfa ha, (hf a ha ▸ hfa) ha⟩),
  left_inv := equiv.perm.subtype_perm_of_subtype,
  right_inv := begin
    rintro ⟨f, hf⟩,
    exact subtype.ext (equiv.perm.of_subtype_subtype_perm _ $ λ a hfa ha, hfa $ hf _ ha),
  end }

/-- A permutation is a derangement if it has no fixed points. -/
def derangements (α : Type*) : set (perm α) := {f : perm α | ∀ x : α, f x ≠ x}

/-- If `α` is equivalent to `β`, then `derangements α` is equivalent to `derangements β`. -/
def equiv.derangements_congr {α β : Type*} (e : α ≃ β) : (derangements α ≃ derangements β) :=
e.perm_congr.subtype_equiv $ λ f, e.forall_congr $ λ x, by simp

namespace derangements

section fixed_points
variables {α : Type*} [decidable_eq α]

lemma mem_derangements_iff_fixed_points_eq_empty {f : perm α} :
  f ∈ derangements α ↔ fixed_points f = ∅ :=
set.eq_empty_iff_forall_not_mem.symm

/-- Derangements on `sᶜ` are equivalent to permutations whose set of fixed points is `s`. -/
protected def compl_equiv (s : set α) [decidable_pred (∈ s)] :
  derangements (sᶜ : set α) ≃ {f : perm α // fixed_points f = s} :=
calc
  derangements (sᶜ : set α)
      ≃ {f : {f : perm α // s ⊆ fixed_points f} // fixed_points f ⊆ s}
      : begin
        refine (perm.compl_equiv s).subtype_equiv (λ f, ⟨λ hf a hfa, _, _⟩),
        { by_contra ha,
          refine hf ⟨a, ha⟩ (subtype.ext _),
          rw [mem_fixed_points, is_fixed_pt, perm.compl_equiv] at hfa,
          dsimp at hfa,
          rwa equiv.perm.of_subtype_apply_of_mem at hfa },
        rintro hf ⟨a, ha⟩ hfa,
        refine ha (hf _),
        rw [mem_fixed_points, is_fixed_pt, perm.compl_equiv],
        dsimp,
        rw [equiv.perm.of_subtype_apply_of_mem _, hfa, subtype.coe_mk],
      end
  ... ≃ {f : perm α // ∃ (h : s ⊆ fixed_points f), fixed_points f ⊆ s}
      : subtype_subtype_equiv_subtype_exists _ _
  ... ≃ {f : perm α // fixed_points f = s}
      : subtype_equiv_right (λ f, by rw [exists_prop, set.subset.antisymm_iff, and_comm])

open_locale classical

/-- The set of permutations that fix at most `a` is equivalent to the sum of:
    - derangements on `α`
    - derangements on `α` minus `a`. -/
def opfp_equiv_sum_derangements (a : α) :
  {f : perm α // fixed_points f ⊆ {a}} ≃ (derangements ({a}ᶜ : set α)) ⊕ derangements α :=
calc
  {f : perm α // fixed_points f ⊆ {a}}
      ≃ {f : {f : perm α // fixed_points f ⊆ {a}} // a ∈ fixed_points f}
        ⊕ {f : {f : perm α // fixed_points f ⊆ {a}} // a ∉ fixed_points f}
      : equiv.sum_compl _ _
  ... ≃ {f : perm α // fixed_points f ⊆ {a} ∧ a ∈ fixed_points f}
        ⊕ {f : perm α // fixed_points f ⊆ {a} ∧ a ∉ fixed_points f}
      : begin
        refine equiv.sum_congr _ _,
        convert subtype_subtype_equiv_subtype_inter _ _,
        ext f,
      end
  ... ≃ {f : perm α // fixed_points f = {a}} ⊕ {f : perm α // fixed_points f = ∅}
      : subtype_or_equiv _ _ begin
        rintro f h,
        refine (set.singleton_nonempty a).ne_empty (by rw [←h.1, h.2]),
      end
  ... ≃ (derangements _) ⊕ derangements α
      : sorry

open_locale classical
/-- The set of permutations that fix at most `a` is equivalent to the sum of:
    - derangements on `α`
    - derangements on `α` minus `a`. -/
def opfp_equiv_sum_derangements' (a : α) :
  {f : perm α // fixed_points f ⊆ {a}} ≃ (derangements ({a}ᶜ : set α)) ⊕ derangements α :=
calc
  {f : perm α // fixed_points f ⊆ {a}}
      ≃ {f : perm α // fixed_points f = {a} ∨ fixed_points f = ∅}
      : subtype_equiv_right (λ f, by rw [set.subset_singleton_iff_eq, or_comm])
  ... ≃ {f : perm α // fixed_points f = {a}} ⊕ {f : perm α // fixed_points f = ∅}
      : subtype_or_equiv _ _ begin
        rintro f h,
        refine (set.singleton_nonempty a).ne_empty (by rw [←h.1, h.2]),
      end
  ... ≃ (derangements _) ⊕ derangements α
      : sorry

end fixed_points

section option

variables {α : Type*} [decidable_eq α]

/-- The set of permutations `f` such that the preimage of `(a, f)` under
    `perm.decompose_option` is a derangement. -/
def remove_none.fiber (a : option α) : set (perm α) :=
  {f : perm α | (a, f) ∈ equiv.perm.decompose_option '' derangements (option α)}

lemma remove_none.mem_fiber (a : option α) (f : perm α) :
  f ∈ remove_none.fiber a ↔
  ∃ F : perm (option α), F ∈ derangements (option α) ∧ F none = a ∧ remove_none F = f :=
  by simp [remove_none.fiber, derangements]

lemma remove_none.fiber_none_eq_empty : remove_none.fiber (@none α) = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  intros f hyp,
  rw remove_none.mem_fiber at hyp,
  rcases hyp with ⟨F, F_derangement, F_none, _⟩,
  exact F_derangement none F_none
end

/-- For any `a : α`, the fiber over `some a` is the set of permutations
    where `a` is the only possible fixed point. -/
lemma remove_none.fiber_eq_opfp (a : α) :
  (remove_none.fiber (some a)) = {f : perm α | fixed_points f ⊆ {a}} :=
begin
  ext f,
  split,
  { rw remove_none.mem_fiber,
    rintro ⟨F, F_derangement, F_none, rfl⟩ x x_fixed,
    apply_fun some at x_fixed,
    cases Fx : F (some x) with y,
    { rw remove_none_none F Fx at x_fixed, rw ←option.some_inj, rwa x_fixed at F_none },
    { exfalso, rw remove_none_some F ⟨y, Fx⟩ at x_fixed, exact F_derangement _ x_fixed } },
  { intro h_opfp,
    use equiv.perm.decompose_option.symm (some a, f),
    split,
    { simp only [equiv.perm.decompose_option_symm_apply],
      intro x,
      apply_fun (swap none (some a)),
      simp only [equiv.swap_apply_self, equiv.perm.coe_mul],
      cases x,
      { simp },
      { simp only [equiv_functor.map_equiv_apply, equiv_functor.map,
                    option.map_eq_map, option.map_some'],
        by_cases x_vs_a : x = a,
        { rw [x_vs_a, swap_apply_right], apply option.some_ne_none },
        { have ne_1 : some x ≠ none := option.some_ne_none _,
          have ne_2 : some x ≠ some a := (option.some_injective α).ne_iff.mpr x_vs_a,
          rw swap_apply_of_ne_of_ne ne_1 ne_2,
          rw (option.some_injective α).ne_iff,
          intro contra,
          exact x_vs_a (h_opfp x contra) } } },
    { rw apply_symm_apply } }
end

/-- The set of derangements on `option α` is equivalent to the union over `a : α`
    of "permutations with `a` the only possible fixed point". -/
def derangements_equiv_sigma_opfp :
  derangements (option α) ≃ Σ a : α, {f : perm α | fixed_points f ⊆ {a}} :=
begin
  have fiber_none_is_false : (remove_none.fiber (@none α)) -> false,
  { rw remove_none.fiber_none_eq_empty, exact is_empty.false },

  calc derangements (option α)
      ≃ equiv.perm.decompose_option '' derangements (option α)   : equiv.image _ _
  ... ≃ Σ (a : option α), ↥(remove_none.fiber a)                 : set_prod_equiv_sigma _
  ... ≃ Σ (a : α), ↥(remove_none.fiber (some a))
          : sigma_option_equiv_of_some _ fiber_none_is_false
  ... ≃ Σ (a : α), {f : perm α | only_possible_fixed_point f a}
          : by simp_rw remove_none.fiber_eq_opfp,
end

/-- The set of derangements on `option α` is equivalent to the union over all `a : α` of
    "derangements on `α` ⊕ derangements on `{a}ᶜ`". -/
def derangements_recursion_equiv :
  derangements (option α) ≃ Σ a : α, (derangements (({a}ᶜ : set α) : Type _) ⊕ derangements α) :=
begin
  refine derangements_equiv_sigma_opfp.trans (sigma_congr_right opfp_equiv_sum_derangements),
end

end option

end derangements
