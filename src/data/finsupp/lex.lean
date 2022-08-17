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

instance [has_lt α] [has_lt N] : has_lt (lex (α →₀ N)) :=
⟨λ f g, finsupp.lex (<) (<) (of_lex f) (of_lex g)⟩

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

/-- Auxiliary helper to case split computably. There is no need for this to be public, as it
can be written with `or.by_cases` on `lt_trichotomy` once the instances below are constructed. -/
private def lt_trichotomy_rec {P : lex (α →₀ N) → lex (α →₀ N) → Sort*}
  (h_lt : Π {f g}, to_lex f < to_lex g → P (to_lex f) (to_lex g))
  (h_eq : Π {f g}, to_lex f = to_lex g → P (to_lex f) (to_lex g))
  (h_gt : Π {f g}, to_lex g < to_lex f → P (to_lex f) (to_lex g)) :
    ∀ f g, P f g  :=
lex.rec $ λ f, lex.rec $ λ g,
  match _, rfl : ∀ y, (f.diff g).min = y → _ with
  | ⊤, h := h_eq (finsupp.diff_eq_empty.mp (finset.min_eq_top.mp h))
  | (wit : α), h :=
    have hne : f wit ≠ g wit := mem_diff.mp (finset.mem_of_min h),
    if hwit : f wit < g wit then
      h_lt ⟨wit, λ j hj, mem_diff.not_left.mp (not_mem_of_lt_min hj h), hwit⟩
    else
      have hwit' : g wit < f wit := hne.lt_or_lt.resolve_left hwit,
      h_gt ⟨wit, by exact λ j hj, begin
        refine mem_diff.not_left.mp (not_mem_of_lt_min hj _),
        rwa diff_comm,
      end, hwit'⟩
  end

instance lex.decidable_le : @decidable_rel (lex (α →₀ N)) (≤) :=
lt_trichotomy_rec
  (λ f g h, is_true $ or.inr h)
  (λ f g h, is_true $ or.inl $ congr_arg _ h)
  (λ f g h, is_false $ λ h', (lt_irrefl _ (h.trans_le h')).elim)

instance lex.decidable_lt : @decidable_rel (lex (α →₀ N)) (<) :=
lt_trichotomy_rec
  (λ f g h, is_true h)
  (λ f g h, is_false h.not_lt)
  (λ f g h, is_false h.asymm)

/--  The linear order on `finsupp`s obtained by the lexicographic ordering. -/
instance lex.linear_order : linear_order (lex (α →₀ N)) :=
{ le_total := lt_trichotomy_rec
    (λ f g h, or.inl h.le)
    (λ f g h, or.inl h.le)
    (λ f g h, or.inr h.le),
  decidable_lt := by apply_instance,
  decidable_le := by apply_instance,
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
