/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.pi.lex
import data.finsupp.witnesses

/-!
# Lexicographic order on finitely supported functions

This file defines the lexicographic order on `finsupp`.
-/

variables {α N : Type*}

namespace finsupp

section N_has_zero
variables [has_zero N]

/-- The lexicographic relation on `α →₀ N`, where `α` is ordered by `r`,
  and `N` is ordered by `s`. -/
protected def lex (r : α → α → Prop) (s : N → N → Prop) (x y : α →₀ N) : Prop :=
pi.lex r (λ _, s) x y

instance [has_lt α] [has_lt N] : has_lt (lex (α →₀ N)) := ⟨finsupp.lex (<) (<)⟩

instance lex.is_strict_order [linear_order α] [partial_order N] :
  is_strict_order (lex (α →₀ N)) (<) :=
let i : is_strict_order (lex (α → N)) (<) := pi.lex.is_strict_order in
{ irrefl := to_lex.surjective.forall.2 $ λ a, @irrefl _ _ i.to_is_irrefl a,
  trans := to_lex.surjective.forall₃.2 $ λ a b c, @trans _ _ i.to_is_trans a b c }

variables [linear_order α]

/--  The partial order on `finsupp`s obtained by the lexicographic ordering.
`finsupp.lex.linear_order` is the proof that this partial order is in fact linear. -/
instance lex.partial_order [partial_order N] : partial_order (lex (α →₀ N)) :=
partial_order.lift (λ x, to_lex ⇑(of_lex x)) finsupp.coe_fn_injective--fun_like.coe_injective

variable [linear_order N]

/--  The linear order on `finsupp`s obtained by the lexicographic ordering. -/
noncomputable instance lex.linear_order : linear_order (lex (α →₀ N)) :=
{ le_total := to_lex.surjective.forall₂.2 $ λ f g, begin
    cases (f.diff g).eq_empty_or_nonempty,
    { exact or.inl (finsupp.diff_eq_empty.mp h).le },
    { cases le_or_lt (of_lex f ((f.diff g).min' h)) (of_lex g ((f.diff g).min' h)) with mf mg,
      work_on_goal 1 { refine or.inl (or.inr _),
        rcases finset.mem_filter.mp (finset.min'_mem _ h) with ⟨-, h⟩,
        refine ⟨_, λ j hj, _, mf.lt_of_ne h⟩ },
      work_on_goal 2 { refine or.inr (or.inr ⟨_, λ j hj, eq.symm _, mg⟩) },
      all_goals { by_cases js : j ∈ f.support ∪ g.support,
        { contrapose! hj,
          exact finset.min'_le _ _ (finset.mem_filter.mpr ⟨js, hj⟩) },
        { simp only [finset.mem_union, not_or_distrib, finsupp.mem_support_iff, not_not] at js,
          simp only [js, of_lex_to_lex, pi.to_lex_apply] } } },
    end,
  decidable_le := by { classical, apply_instance },
  ..lex.partial_order }

lemma lex.le_of_forall_le {a b : lex (α →₀ N)} (h : ∀ i, of_lex a i ≤ of_lex b i) : a ≤ b :=
le_of_not_lt (λ ⟨i, hi⟩, (h i).not_lt hi.2)

lemma lex.le_of_of_lex_le {a b : lex (α →₀ N)} (h : of_lex a ≤ of_lex b) : a ≤ b :=
lex.le_of_forall_le h

lemma to_lex_monotone : monotone (@to_lex (α →₀ N)) :=
λ _ _, lex.le_of_forall_le

end N_has_zero

/--  This is a technical result.  Likely, you will need one of the consequences of this lemma.  -/
lemma apply_min'_lt_apply_min'_of_le [linear_order α] [linear_order N] [has_zero N]
  {f g : α →₀ N} (h : (f.diff g).nonempty) (ab : to_lex f ≤ to_lex g) :
  f ((f.diff g).min' h) < g ((f.diff g).min' h) :=
begin
  rcases ab with ab | ⟨x, ltx, abx⟩,
  { exact (not_ne_iff.mpr (fun_like.coe_fn_eq.mp ab) (nonempty_diff_iff.mp h)).elim },
  convert abx,
  repeat { refine le_antisymm (finset.min'_le _ _ _) _,
    { simp only [diff, ne.def, finset.mem_filter, finset.mem_union, mem_support_iff],
      exact ⟨abx.ne.ne_or_ne 0, abx.ne⟩ },
    { refine finset.le_min' _ _ _ (λ y hy, _),
      contrapose! hy,
      simpa only [mem_diff, ne.def, not_not] using ltx _ hy } }
end

/--  This is a technical result.  Likely, you will need one of the consequences of this lemma.  -/
lemma apply_min'_lt_apply_min'_iff [linear_order α] [linear_order N] [has_zero N] {f g : α →₀ N} :
  to_lex f ≤ to_lex g ↔ dite (f.diff g).nonempty
    (λ h, f ((f.diff g).min' h) < g ((f.diff g).min' h)) (λ _, true) :=
begin
  split_ifs with h h,
  { refine ⟨apply_min'_lt_apply_min'_of_le _, λ h', _⟩,
    refine le_of_lt ⟨((f.diff g).min' h), λ j hj, _, h'⟩,
    refine not_ne_iff.mp (mem_diff.not.mp _),
    contrapose! hj,
    exact finset.min'_le _ _ hj },
  { rw [nonempty_diff_iff, not_not] at h,
    simp [h] }
end

lemma apply_to_lex_lt_iff_apply_wit_lt [nonempty α] [linear_order α] [linear_order N] [has_zero N]
  {f g : (α →₀ N)} :
  to_lex f < to_lex g ↔ f (f.wit g) < g (f.wit g) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw ← min'_eq_wit_of_ne (id h.ne : f ≠ g),
    exact apply_min'_lt_apply_min'_of_le (nonempty_diff_iff.mpr h.ne) h.le },
  { refine lt_of_le_of_ne (apply_min'_lt_apply_min'_iff.mpr _) _,
    rwa [dif_pos, min'_eq_wit_of_ne],
    repeat { refine coe_fn_inj.not.mp (function.ne_iff.mpr ⟨_, h.ne⟩) } }
end

lemma to_lex_le_iff_apply_wit_le [nonempty α] [linear_order α] [linear_order N] [has_zero N]
  {f g : (α →₀ N)} :
  to_lex f ≤ to_lex g ↔ f (f.wit g) ≤ g (f.wit g) :=
not_iff_not.mp (by simp only [not_le, apply_to_lex_lt_iff_apply_wit_lt, wit_comm])

lemma le_iff_of_lex_apply_wit_le [nonempty α] [linear_order α] [linear_order N] [has_zero N]
  {f g : lex (α →₀ N)} :
  f ≤ g ↔ of_lex f (f.wit g) ≤ of_lex g (f.wit g) :=
by simp [of_lex, to_lex, ← to_lex_le_iff_apply_wit_le]

lemma apply_eq_of_lt_wit [nonempty α] [linear_order α] [linear_order N] [has_zero N]
  {f g : (α →₀ N)} {x : α} (hx : x < f.wit g) :
  f x = g x :=
begin
  refine le_antisymm _ _;
  contrapose! hx;
  refine wit_le _,
  exacts [hx.ne', hx.ne],
end

variables [linear_order α] [linear_order N] [add_left_cancel_monoid N] [covariant_class N N (+) (≤)]

instance : covariant_class (to_lex (α →₀ N)) (to_lex (α →₀ N))
  ((+) : (α →₀ N) → (α →₀ N) → (α →₀ N)) $
  @has_le.le (to_lex (α →₀ N)) $ by { haveI : linear_order (to_lex (α →₀ N)) := lex.linear_order,
                                      apply_instance } :=
{ elim := λ f g h gh, begin
    by_cases iα : nonempty α,
    { resetI,
      refine le_iff_of_lex_apply_wit_le.mpr _,
      simpa only [wit_add_left, equiv.coe_refl, id.def, coe_add, pi.add_apply] using
        add_le_add_left (le_iff_of_lex_apply_wit_le.mp gh) _ },
    { rw subsingleton_iff.mp ⟨λ f g, ext (λ x, (iα ⟨x⟩).elim)⟩ h g }
  end }

end finsupp
