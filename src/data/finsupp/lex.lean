/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.pi.lex
import data.finsupp.order
import data.finsupp.ne_locus

/-!
# Lexicographic order on finitely supported functions

This file defines the lexicographic order on `finsupp`.
-/

variables {α N : Type*}

namespace finsupp

section N_has_zero
variables [has_zero N]

/-- `finsupp.lex r s` is the lexicographic relation on `α →₀ N`, where `α` is ordered by `r`,
and `N` is ordered by `s`.

The type synonym `_root_.lex (α →₀ N)` has an order given by `finsupp.lex (<) (<)`.
-/
protected def lex (r : α → α → Prop) (s : N → N → Prop) (x y : α →₀ N) : Prop :=
pi.lex r (λ _, s) x y

lemma _root_.pi.lex_eq_finsupp_lex {r : α → α → Prop} {s : N → N → Prop} (a b : α →₀ N) :
  pi.lex r (λ _, s) (a : α → N) (b : α → N) = finsupp.lex r s a b :=
rfl

lemma lex_def {r : α → α → Prop} {s : N → N → Prop} {a b : α →₀ N} :
  finsupp.lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s (a j) (b j) := iff.rfl

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
  match _, rfl : ∀ y, (f.ne_locus g).min = y → _ with
  | ⊤, h := h_eq (finsupp.ne_locus_eq_empty.mp (finset.min_eq_top.mp h))
  | (wit : α), h :=
    have hne : f wit ≠ g wit := mem_ne_locus.mp (finset.mem_of_min h),
    hne.lt_or_lt.by_cases
      (λ hwit, h_lt ⟨wit, λ j hj, mem_ne_locus.not_left.mp (finset.not_mem_of_lt_min hj h), hwit⟩)
      (λ hwit, h_gt ⟨wit, by exact λ j hj, begin
        refine mem_ne_locus.not_left.mp (finset.not_mem_of_lt_min hj _),
        rwa ne_locus_comm,
      end, hwit⟩)
  end

@[irreducible] instance lex.decidable_le : @decidable_rel (lex (α →₀ N)) (≤) :=
lt_trichotomy_rec
  (λ f g h, is_true $ or.inr h)
  (λ f g h, is_true $ or.inl $ congr_arg _ h)
  (λ f g h, is_false $ λ h', (lt_irrefl _ (h.trans_le h')).elim)

@[irreducible] instance lex.decidable_lt : @decidable_rel (lex (α →₀ N)) (<) :=
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

lemma lt_of_forall_lt_of_lt (a b : lex (α →₀ N)) (i : α) :
  (∀ j < i, of_lex a j = of_lex b j) → of_lex a i < of_lex b i → a < b :=
λ h1 h2, ⟨i, h1, h2⟩

end N_has_zero

section covariants
variables [linear_order α] [add_monoid N] [linear_order N]

/-!  We are about to sneak in a hypothesis that might appear to be too strong.
We assume `covariant_class` with *strict* inequality `<` also when proving the one with the
*weak* inequality `≤`.  This is actually necessary: addition on `lex (α →₀ N)` may fail to be
monotone, when it is "just" monotone on `N`. -/
section left
variables [covariant_class N N (+) (<)]

instance lex.covariant_class_lt_left : covariant_class (lex (α →₀ N)) (lex (α →₀ N)) (+) (<) :=
⟨λ f g h ⟨a, lta, ha⟩, ⟨a, λ j ja, congr_arg ((+) _) (lta j ja), add_lt_add_left ha _⟩⟩

instance lex.covariant_class_le_left : covariant_class (lex (α →₀ N)) (lex (α →₀ N)) (+) (≤) :=
has_add.to_covariant_class_left _

end left

section right
variables [covariant_class N N (function.swap (+)) (<)]

instance lex.covariant_class_lt_right :
  covariant_class (lex (α →₀ N)) (lex (α →₀ N)) (function.swap (+)) (<) :=
⟨λ f g h ⟨a, lta, ha⟩, ⟨a, λ j ja, congr_arg (+ (of_lex f j)) (lta j ja), add_lt_add_right ha _⟩⟩

instance lex.covariant_class_le_right :
  covariant_class (lex (α →₀ N)) (lex (α →₀ N)) (function.swap (+)) (≤) :=
has_add.to_covariant_class_right _

end right

end covariants

end finsupp
