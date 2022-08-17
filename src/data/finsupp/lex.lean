/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.pi.lex
import data.finsupp.order
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

See `finsupp.lex.linear_order` for a proof that this partial order is in fact linear. -/
instance lex.partial_order [partial_order N] : partial_order (lex (α →₀ N)) :=
partial_order.lift (λ x, to_lex ⇑(of_lex x)) finsupp.coe_fn_injective--fun_like.coe_injective

variable [linear_order N]

/-  The "decidable fields" of `lex.linear_order` are proved by appealing to `classical` reasoning.
It may be possible to get a constructive version of this instance, but this seems to require a
possibly long detour and I (DT) am not sure of the details. -/
/--  The linear order on `finsupp`s obtained by the lexicographic ordering. -/
noncomputable instance lex.linear_order : linear_order (lex (α →₀ N)) :=
{ le_total := to_lex.surjective.forall₂.2 $ λ f g, begin
    cases (f.diff g).eq_empty_or_nonempty with he he,
    { exact or.inl (finsupp.diff_eq_empty.mp he).le },
    { cases he with a ha,
      haveI : inhabited α := ⟨a⟩,
      cases le_or_lt (f (f.wit g)) (g (f.wit g)) with mf mg,
      { refine or.inl (or.inr ⟨f.wit g, λ j hj, apply_eq_of_le_wit hj, mf.lt_of_ne _⟩),
        exact wit_eq_wit_iff.not.mpr (nonempty_diff_iff.mp ⟨_, ha⟩) },
      { exact or.inr (or.inr ⟨g.wit f, λ j hj, apply_eq_of_le_wit hj, (by rwa wit_comm at mg)⟩) } }
    end,
  decidable_le := by { classical, apply_instance },
  decidable_eq := by apply_instance,
  ..lex.partial_order }

lemma lex.le_of_forall_le {a b : lex (α →₀ N)} (h : ∀ i, of_lex a i ≤ of_lex b i) : a ≤ b :=
le_of_not_lt (λ ⟨i, hi⟩, (h i).not_lt hi.2)

lemma lex.le_of_of_lex_le {a b : lex (α →₀ N)} (h : of_lex a ≤ of_lex b) : a ≤ b :=
lex.le_of_forall_le h

lemma to_lex_monotone : monotone (@to_lex (α →₀ N)) :=
λ _ _, lex.le_of_forall_le

end N_has_zero

/--  This is a technical result.  Likely, you will need one of the consequences of this lemma.  -/
lemma apply_wit_lt_apply_wit_of_le [inhabited α] [linear_order α] [linear_order N] [has_zero N]
  {f g : α →₀ N} (fg : to_lex f < to_lex g) :
  f (f.wit g) < g (f.wit g) :=
begin
  rcases fg with ⟨x, ltx, fgx⟩,
  { convert fgx;
    exact wit_eq_of_ne_of_forall fgx.ne ltx }
end

lemma to_lex_le_iff_apply_wit_le [inhabited α] [linear_order α] [linear_order N] [has_zero N]
  {f g : α →₀ N} :
  to_lex f ≤ to_lex g ↔ f ((f.wit g)) ≤ g ((f.wit g)) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases eq_or_ne f g with rfl | fg,
    { exact le_rfl },
    { exact (apply_wit_lt_apply_wit_of_le (h.lt_of_ne fg)).le } },
  { contrapose! h,
    rw wit_comm,
    exact apply_wit_lt_apply_wit_of_le h }
end

lemma to_lex_lt_iff_apply_wit_lt [inhabited α] [linear_order α] [linear_order N] [has_zero N]
  {f g : (α →₀ N)} :
  to_lex f < to_lex g ↔ f (f.wit g) < g (f.wit g) :=
not_iff_not.mp (by simp only [to_lex_le_iff_apply_wit_le, wit_comm, not_lt])

lemma le_iff_of_lex_apply_wit_le [inhabited α] [linear_order α] [linear_order N] [has_zero N]
  {f g : lex (α →₀ N)} :
  f ≤ g ↔ of_lex f (f.wit g) ≤ of_lex g (f.wit g) :=
by simp [of_lex, to_lex, ← to_lex_le_iff_apply_wit_le]

lemma apply_eq_of_lt_wit [inhabited α] [linear_order α] [linear_order N] [has_zero N]
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
    { cases iα with x,
      haveI : inhabited α := {default := x},
      refine le_iff_of_lex_apply_wit_le.mpr _,
      simpa only [wit_add_left, equiv.coe_refl, id.def, coe_add, pi.add_apply] using
        add_le_add_left (le_iff_of_lex_apply_wit_le.mp gh) _ },
    { rw subsingleton_iff.mp ⟨λ f g, ext (λ x, (iα ⟨x⟩).elim)⟩ h g }
  end }

end finsupp
