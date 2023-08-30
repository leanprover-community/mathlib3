/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyan Xu
-/
import data.dfinsupp.order
import data.dfinsupp.ne_locus
import order.well_founded_set

/-!
# Lexicographic order on finitely supported dependent functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the lexicographic order on `dfinsupp`.
-/

variables {ι : Type*} {α : ι → Type*}

namespace dfinsupp

section has_zero

variable [Π i, has_zero (α i)]

/-- `dfinsupp.lex r s` is the lexicographic relation on `Π₀ i, α i`, where `ι` is ordered by `r`,
and `α i` is ordered by `s i`.
The type synonym `lex (Π₀ i, α i)` has an order given by `dfinsupp.lex (<) (λ i, (<))`.
-/
protected def lex (r : ι → ι → Prop) (s : Π i, α i → α i → Prop) (x y : Π₀ i, α i) : Prop :=
pi.lex r s x y

lemma _root_.pi.lex_eq_dfinsupp_lex {r : ι → ι → Prop} {s : Π i, α i → α i → Prop}
  (a b : Π₀ i, α i) : pi.lex r s (a : Π i, α i) b = dfinsupp.lex r s a b := rfl

lemma lex_def {r : ι → ι → Prop} {s : Π i, α i → α i → Prop} {a b : Π₀ i, α i} :
  dfinsupp.lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s j (a j) (b j) := iff.rfl

instance [has_lt ι] [Π i, has_lt (α i)] : has_lt (lex (Π₀ i, α i)) :=
⟨λ f g, dfinsupp.lex (<) (λ i, (<)) (of_lex f) (of_lex g)⟩

lemma lex_lt_of_lt_of_preorder [Π i, preorder (α i)] (r) [is_strict_order ι r]
  {x y : Π₀ i, α i} (hlt : x < y) : ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
begin
  obtain ⟨hle, j, hlt⟩ := pi.lt_def.1 hlt, classical,
  have : (x.ne_locus y : set ι).well_founded_on r := (x.ne_locus y).finite_to_set.well_founded_on,
  obtain ⟨i, hi, hl⟩ := this.has_min {i | x i < y i} ⟨⟨j, mem_ne_locus.2 hlt.ne⟩, hlt⟩,
  exact ⟨i, λ k hk, ⟨hle k, of_not_not $ λ h,
    hl ⟨k, mem_ne_locus.2 (ne_of_not_le h).symm⟩ ((hle k).lt_of_not_le h) hk⟩, hi⟩,
end

lemma lex_lt_of_lt [Π i, partial_order (α i)] (r) [is_strict_order ι r]
  {x y : Π₀ i, α i} (hlt : x < y) : pi.lex r (λ i, (<)) x y :=
by { simp_rw [pi.lex, le_antisymm_iff], exact lex_lt_of_lt_of_preorder r hlt }

instance lex.is_strict_order [linear_order ι] [Π i, partial_order (α i)] :
  is_strict_order (lex (Π₀ i, α i)) (<) :=
let i : is_strict_order (lex (Π i, α i)) (<) := pi.lex.is_strict_order in
{ irrefl := to_lex.surjective.forall.2 $ λ a, @irrefl _ _ i.to_is_irrefl a,
  trans := to_lex.surjective.forall₃.2 $ λ a b c, @trans _ _ i.to_is_trans a b c }

variables [linear_order ι]

/-- The partial order on `dfinsupp`s obtained by the lexicographic ordering.
See `dfinsupp.lex.linear_order` for a proof that this partial order is in fact linear. -/
instance lex.partial_order [Π i, partial_order (α i)] : partial_order (lex (Π₀ i, α i)) :=
partial_order.lift (λ x, to_lex ⇑(of_lex x)) dfinsupp.coe_fn_injective

section linear_order

variable [Π i, linear_order (α i)]

/-- Auxiliary helper to case split computably. There is no need for this to be public, as it
can be written with `or.by_cases` on `lt_trichotomy` once the instances below are constructed. -/
private def lt_trichotomy_rec {P : lex (Π₀ i, α i) → lex (Π₀ i, α i) → Sort*}
  (h_lt : Π {f g}, to_lex f < to_lex g → P (to_lex f) (to_lex g))
  (h_eq : Π {f g}, to_lex f = to_lex g → P (to_lex f) (to_lex g))
  (h_gt : Π {f g}, to_lex g < to_lex f → P (to_lex f) (to_lex g)) :
  Π f g, P f g :=
lex.rec $ λ f, lex.rec $ λ g,
  match _, rfl : ∀ y, (f.ne_locus g).min = y → _ with
  | ⊤, h := h_eq (ne_locus_eq_empty.mp $ finset.min_eq_top.mp h)
  | (wit : ι), h := (mem_ne_locus.mp $ finset.mem_of_min h).lt_or_lt.by_cases
      (λ hwit, h_lt ⟨wit, λ j hj, not_mem_ne_locus.mp (finset.not_mem_of_lt_min hj h), hwit⟩)
      (λ hwit, h_gt ⟨wit, λ j hj, not_mem_ne_locus.mp
        (finset.not_mem_of_lt_min hj $ by rwa ne_locus_comm), hwit⟩)
  end

@[irreducible] instance lex.decidable_le : @decidable_rel (lex (Π₀ i, α i)) (≤) :=
lt_trichotomy_rec
  (λ f g h, is_true $ or.inr h)
  (λ f g h, is_true $ or.inl $ congr_arg _ h)
  (λ f g h, is_false $ λ h', (lt_irrefl _ (h.trans_le h')).elim)

@[irreducible] instance lex.decidable_lt : @decidable_rel (lex (Π₀ i, α i)) (<) :=
lt_trichotomy_rec
  (λ f g h, is_true h)
  (λ f g h, is_false h.not_lt)
  (λ f g h, is_false h.asymm)

/--  The linear order on `dfinsupp`s obtained by the lexicographic ordering. -/
instance lex.linear_order : linear_order (lex (Π₀ i, α i)) :=
{ le_total := lt_trichotomy_rec
    (λ f g h, or.inl h.le)
    (λ f g h, or.inl h.le)
    (λ f g h, or.inr h.le),
  decidable_lt := by apply_instance,
  decidable_le := by apply_instance,
  decidable_eq := by apply_instance,
  ..lex.partial_order }

end linear_order

variable [Π i, partial_order (α i)]

lemma to_lex_monotone : monotone (@to_lex (Π₀ i, α i)) :=
λ a b h, le_of_lt_or_eq $ or_iff_not_imp_right.2 $ λ hne, by classical; exact
  ⟨finset.min' _ (nonempty_ne_locus_iff.2 hne),
    λ j hj, not_mem_ne_locus.1 (λ h, (finset.min'_le _ _ h).not_lt hj),
    (h _).lt_of_ne (mem_ne_locus.1 $ finset.min'_mem _ _)⟩

lemma lt_of_forall_lt_of_lt (a b : lex (Π₀ i, α i)) (i : ι) :
  (∀ j < i, of_lex a j = of_lex b j) → of_lex a i < of_lex b i → a < b :=
λ h1 h2, ⟨i, h1, h2⟩

end has_zero

section covariants
variables [linear_order ι] [Π i, add_monoid (α i)] [Π i, linear_order (α i)]

/-!  We are about to sneak in a hypothesis that might appear to be too strong.
We assume `covariant_class` with *strict* inequality `<` also when proving the one with the
*weak* inequality `≤`.  This is actually necessary: addition on `lex (Π₀ i, α i)` may fail to be
monotone, when it is "just" monotone on `α i`. -/
section left
variables [Π i, covariant_class (α i) (α i) (+) (<)]

instance lex.covariant_class_lt_left :
  covariant_class (lex (Π₀ i, α i)) (lex (Π₀ i, α i)) (+) (<) :=
⟨λ f g h ⟨a, lta, ha⟩, ⟨a, λ j ja, congr_arg ((+) _) (lta j ja), add_lt_add_left ha _⟩⟩

instance lex.covariant_class_le_left :
  covariant_class (lex (Π₀ i, α i)) (lex (Π₀ i, α i)) (+) (≤) := has_add.to_covariant_class_left _

end left

section right
variables [Π i, covariant_class (α i) (α i) (function.swap (+)) (<)]

instance lex.covariant_class_lt_right :
  covariant_class (lex (Π₀ i, α i)) (lex (Π₀ i, α i)) (function.swap (+)) (<) :=
⟨λ f g h ⟨a, lta, ha⟩, ⟨a, λ j ja, congr_arg (+ (of_lex f j)) (lta j ja), add_lt_add_right ha _⟩⟩

instance lex.covariant_class_le_right :
  covariant_class (lex (Π₀ i, α i)) (lex (Π₀ i, α i)) (function.swap (+)) (≤) :=
has_add.to_covariant_class_right _

end right

end covariants

end dfinsupp
