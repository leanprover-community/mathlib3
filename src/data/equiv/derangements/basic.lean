/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
import data.equiv.basic
import data.equiv.option
import group_theory.perm.option

import tactic.equiv_rw

/-!
# Derangements on types

In this file we define a predicate and its corresponding set:

* `is_derangement f`: whether the permutation `f` has no fixed points.

* `derangements α`: the set of derangements on a type `α`.

Then we define

* some related predicates: e.g.,

  - `only_possible_fixed_point f a`: either `f` has no fixed points, or `a` is the only fixed point;

  - `exactly_one_fixed_point f a`: `f` has exactly one fixed point, which is `a`;

* equivalences involving various subtypes of `perm α` and `derangements α`: e.g.,

  - `derangements_equiv_sigma_opfp`: an equivalence between `derangements (option α)` and the
    sigma-type `Σ a : α, {f : perm α // only_possible_fixed_point f a}`.
-/

open equiv

section definitions

/-- A permutation is a derangement if it has no fixed points. -/
def is_derangement {α : Type*} (f : perm α) : Prop := (∀ x : α, f x ≠ x)

/-- The set of derangements on `α`. -/
def derangements (α : Type*) : set (perm α) := {f : perm α | is_derangement f}

/-- The permutation `f` has at most one fixed point, `a`. -/
def only_possible_fixed_point {α : Type*} (f : perm α) (a : α) : Prop := ∀ x : α, f x = x → x = a

/-- The permutation `f` has exactly one fixed point, `a`. -/
def exactly_one_fixed_point {α : Type*} (f : perm α) (a : α) : Prop := ∀ x : α, f x = x ↔ x = a

end definitions

-- TODO there's just a single lemma here for now, but i can imagine other lemmas living here
section TODO_name

/-- If `α` is equivalent to `β`, then `derangements α` is equivalent to `derangements β`. -/
def derangement_congr {α β : Type*} (e : α ≃ β) : (derangements α ≃ derangements β) :=
begin
  refine subtype_equiv (perm_congr e) _,
  intro f,
  simp only [derangements, is_derangement, perm_congr_apply, set.mem_set_of_eq],
  split,
  { contrapose!,
    rintro ⟨y, hy_fixed⟩,
    use e.symm y,
    apply e.injective,
    simp [hy_fixed] },
  { contrapose!,
    rintro ⟨x, hx_fixed⟩,
    use e x,
    simp [hx_fixed] }
end

end TODO_name

section fixed_points

variables {α : Type*}

lemma eofp_iff_opfp_and_eq (a : α) (f : perm α) :
  exactly_one_fixed_point f a ↔ only_possible_fixed_point f a ∧ f a = a :=
begin
  split,
  { intro h_eofp, exact ⟨λ x, (h_eofp x).mp, (h_eofp a).mpr rfl⟩ },
  { rintros ⟨h_opfp, fa_eq_a⟩ x,
    split,
    { exact h_opfp x },
    { rintro ⟨rfl⟩, exact fa_eq_a }}
end

lemma derangement_iff_opfp_and_ne (a : α) (f : perm α) :
  is_derangement f ↔ only_possible_fixed_point f a ∧ f a ≠ a :=
begin
  unfold is_derangement only_possible_fixed_point,
  split,
  { intro h_derangement,
    split,
    { intros x x_fixed, exfalso, exact h_derangement x x_fixed },
    { exact h_derangement a }},
  { rintros ⟨h_opfp, fa_ne_a⟩ x x_fixed,
    specialize h_opfp x x_fixed,
    rw h_opfp at x_fixed,
    exact fa_ne_a x_fixed }
end

/-- The set of permutations with `a` the only fixed point is equivalent to the set of derangements
    on `{a}ᶜ`. -/
def eofp_equiv_derangements_except_for [decidable_eq α] (a : α) :
  {f : perm α | exactly_one_fixed_point f a} ≃ derangements ({a}ᶜ : set α) :=
begin
  let key_equiv : {f : perm α | f a = a} ≃ perm ({a}ᶜ : set α),
  { transitivity {f : perm α // ∀ x : ({a} : set α), f x = (equiv.refl _) x},
    { apply subtype_equiv_right, simp },
    { exact equiv.set.compl (equiv.refl _) }},

  transitivity {f : {f : perm α // f a = a} // only_possible_fixed_point f.val a},
  { apply equiv.trans _ (subtype_subtype_equiv_subtype_exists _ _).symm,
    apply subtype_equiv_right,
    intro f,
    simp only [exists_prop, set.mem_set_of_eq],
    rw and_comm,
    exact eofp_iff_opfp_and_eq _ _ },
  { refine subtype_equiv key_equiv _,
    rintro ⟨f, _⟩,
    simp [key_equiv, equiv.set.compl, derangements, is_derangement,
          only_possible_fixed_point, not_imp_not] }
end

end fixed_points

section option

variables {α : Type*}

lemma remove_none_fixed_pt (f : perm (option α)) (x : α) :
  (remove_none f) x = x ↔ f (some x) = some x ∨ (f none = some x ∧ f (some x) = none) :=
begin
  -- allows remove_none_XXX lemmas to work
  rw ← option.some_inj,
  cases fx : f (some x) with y,
  { rw remove_none_none f fx, simp },
  { rw [remove_none_some f ⟨y, fx⟩, fx], simp }
end

-- TODO I defined this predicate `foo` and the corresponding set, but it's only
-- used in the proof of `derangements_equiv_sigma_opfp`. Should it be completely
-- folded into that proof?
-- For now it's just called "foo" cause IDK whether to fold it in or not.
-- TODO match or option.elim?
def foo (a : option α) (f : perm α) : Prop := match a with
| none := false
| (some a) := only_possible_fixed_point f a
end

lemma foo_lemma (f : perm (option α)) : is_derangement f ↔ foo (f none) (remove_none f) :=
begin
  cases f_none : f none with a,
  -- if f none is none, then the RHS is false, and this simplifies to "show f is not a derangement"
  { simp only [is_derangement, foo, iff_false, not_forall, not_not],
    use ⟨none, f_none⟩ },
  -- otherwise we have to do actual proof
  { simp only [foo, only_possible_fixed_point, is_derangement],
    split,
    -- (after contrapose): if (remove_none f) has a fixed point x ≠ a, then it's a fixed point
    -- of f as well
    { contrapose!,
      rintro ⟨x, x_fixed, x_ne_a⟩,
      rw remove_none_fixed_pt at x_fixed,
      rcases x_fixed with (x_fixed | ⟨fnone_eq_x, fx_eq_none⟩),
      -- either x was already a fixed point, which is easy...
      { use ⟨some x, x_fixed⟩ },
      -- ... or f swapped x and none, which is a contradiction
      { exfalso,
        have : some x = some a := by cc,
        exact x_ne_a (option.some_inj.mp this) }},
    -- (after contrapose): if f has a fixed point, then there is a fixed point of (remove_none f),
    -- which isn't equal to a
    { contrapose!,
      rintro ⟨x, x_fixed⟩,
      -- since f none = some a, we know x can't be none
      cases x,
      { exfalso,
        exact option.some_ne_none a (by cc) },
      -- so we have a fixed point (some x), it remains to show it's still a fixed point, and that
      -- it's not equal to a
      { use x,
        rw remove_none_fixed_pt,
        split,
        { left, assumption },
        { intro x_eq_a,
          have : f (some x) = f none := by cc,
          exact option.some_ne_none x (f.injective (this)) }}}}
end

-- TODO is the set better like this? or should i replace it with a union over (a : α)?
def foo_set : set (option α × perm α) := {af : option α × perm α | foo af.fst af.snd}

variables [decidable_eq α]

lemma foo_set_eq : equiv.perm.decompose_option '' derangements (option α) = foo_set :=
begin
  -- rearrange it so that we have derangements (option α) = (...)⁻¹' foo_set
  symmetry,
  rw ← equiv.preimage_eq_iff_eq_image,
  ext f,
  exact (foo_lemma f).symm,
end

-- TODO this kinda makes more sense as a subset of `α × perm α`, but the proof was easier this way.
/-- The set of derangements on `option α` is equivalent to the union of "permutations with either
    no fixed points, `a` as the only fixed point", over all `a : α`. -/
def derangements_equiv_sigma_opfp :
  derangements (option α) ≃ Σ a : α, {f : perm α // only_possible_fixed_point f a} :=
begin
  -- TODO why do i need the @ to get it to infer α?
  let fiber : option α → set (perm α) := λ a : option α, {f : perm α | (a, f) ∈ (@foo_set α)},

  have fiber_imp_some : ∀ a : option α, (fiber a) → a.is_some,
  { rintros a ⟨f, f_foo⟩,
    cases a,
    { exfalso, simp [foo_set, fiber] at f_foo, assumption },
    { simp }},

  have fiber_equiv_opfp : ∀ a : α, (fiber a) ≃ {f : perm α // only_possible_fixed_point f a},
  { intro a, refl },

  -- TODO how are calc blocks this big formatted?
  calc derangements (option α)
      ≃ equiv.perm.decompose_option '' derangements (option α)   : equiv.image _ _
  ... ≃ foo_set                                                  : equiv.set_congr foo_set_eq
  ... ≃ Σ (a : option α), ↥(fiber a)                             : set_prod_equiv_sigma _
  ... ≃ Σ (a : {a' : option α // a'.is_some}), ↥(fiber a)
          : (sigma_subtype_equiv_of_subset _ _ fiber_imp_some).symm
  ... ≃ Σ (a : α), ↥(fiber a)
          : sigma_congr_left' (option_is_some_equiv α)
  ... ≃ Σ (a : α), {f : perm α // only_possible_fixed_point f a}
          : sigma_congr_right fiber_equiv_opfp,
end

/-- The set of derangements on `option α` is equivalent to the union over all `a : α` of
    "derangements on `α` ⊕ derangements on `{a}ᶜ`". -/
def derangements_recursion_equiv :
  derangements (option α) ≃ Σ a : α, (derangements (({a}ᶜ : set α) : Type _) ⊕ derangements α) :=
begin
  equiv_rw derangements_equiv_sigma_opfp,
  apply sigma_congr_right,
  intro a,
  equiv_rw (equiv.sum_compl (λ f : {f : perm α // _}, f.val a = a)).symm,
  refine sum_congr _ _,
  {
    equiv_rw (eofp_equiv_derangements_except_for a).symm,
    simp_rw (eofp_iff_opfp_and_eq a),
    exact subtype_subtype_equiv_subtype_inter _ (λ f : perm α, f a = a),
    apply_instance,
  },
  {
    unfold derangements,
    simp_rw (derangement_iff_opfp_and_ne a),
    exact subtype_subtype_equiv_subtype_inter _ (λ f : perm α, f a ≠ a),
  },

  apply_instance,  -- TODO why does this goal exist? seems to come from equiv_rw
end

end option
