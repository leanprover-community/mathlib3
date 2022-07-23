/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import order.succ_pred.basic

/-!
# Successor and predecessor limits

We define the predicate `order.is_succ_limit` for "successor limits", values that aren't successors,
except possibly of themselves. We define `order.is_pred_limit` analogously, and prove basic results.

We also define `succ_pred_archimedean` orders, as `succ_order`s and `pred_order`s where `succ`
iterated to an element gives all the greater ones, and `pred` iterated to an element gives all the
smaller ones. We then show that in a partial order, either condition implies the other.

## Todo

The plan is to eventually replace `ordinal.is_limit` and `cardinal.is_limit` with the common
predicate `order.is_succ_limit`.
-/

variables {α : Type*} {a b : α}

open function set

/-! ### Successor limits -/

namespace order
section preorder
variables [preorder α] [succ_order α]

/-- A successor limit is a value that isn't a successor, except possibly of itself. -/
def is_succ_limit (a : α) : Prop := ∀ b, succ b = a → is_max b

protected lemma is_succ_limit.is_max (h : is_succ_limit (succ a)) : is_max a := h a rfl

lemma not_is_succ_limit_succ_of_not_is_max (ha : ¬ is_max a) : ¬ is_succ_limit (succ a) :=
λ h, ha (h a rfl)

protected lemma _root_.is_min.is_succ_limit (h : is_min a) : is_succ_limit a :=
by { rintros b rfl, exact max_of_succ_le (h $ le_succ b) }

lemma is_succ_limit_of_succ_ne (h : ∀ b, succ b ≠ a) : is_succ_limit a := λ b hb, (h _ hb).elim

lemma not_is_succ_limit_iff : ¬ is_succ_limit a ↔ ∃ b, ¬ is_max b ∧ succ b = a :=
by simp [is_succ_limit, and_comm]

/-- See `order.not_is_succ_limit_iff` for a version that states that `a` is a successor of a value
other than itself. -/
lemma mem_range_succ_of_not_is_succ_limit (h : ¬ is_succ_limit a) : a ∈ range (@succ α _ _) :=
by { cases not_is_succ_limit_iff.1 h with b hb, exact ⟨b, hb.2⟩ }

lemma is_succ_limit_of_succ_lt (H : ∀ a < b, succ a < b) : is_succ_limit b :=
by { rintros a rfl, by_contra ha, exact (H a $ lt_succ_of_not_is_max ha).false }

/-- A value can be built by building it on successors and successor limits.

Note that you need a partial order for data built using this to behave nicely on successors. -/
@[elab_as_eliminator] noncomputable def is_succ_limit_rec_on {C : α → Sort*} (b)
  (hs : Π a, ¬ is_max a → C (succ a)) (hl : Π a, is_succ_limit a → C a) : C b :=
begin
  by_cases hb : is_succ_limit b,
  { exact hl b hb },
  { have H := classical.some_spec (not_is_succ_limit_iff.1 hb),
    rw ←H.2,
    exact hs _ H.1 }
end

lemma is_succ_limit_rec_on_limit {C : α → Sort*} (hs : Π a, ¬ is_max a → C (succ a))
  (hl : Π a, is_succ_limit a → C a) (hb : is_succ_limit b) :
  @is_succ_limit_rec_on α _ _ C b hs hl = hl b hb :=
by { classical, exact dif_pos hb }

/-- A predecessor function for a `succ_order`. We have `pred' a = a` for a successor limit `a`, and
`pred' (succ a) = a` when `a` is not maximal.

When working in a succ-archimedean partial order, this can be used to build an `is_pred_archimdean`
instance: see `order.succ_order.to_is_pred_archimedean`.

Note that this is only nicely behaved on partial orders. -/
noncomputable def pred' (a : α) : α := is_succ_limit_rec_on a (λ b _, b) (λ b _, b)

lemma pred'_of_limit : is_succ_limit a → pred' a = a := is_succ_limit_rec_on_limit _ _

alias pred'_of_limit ← is_succ_limit.pred'_eq

lemma pred'_le (b : α) : pred' b ≤ b :=
begin
  change dite _ _ _ ≤ b,
  split_ifs,
  { exact le_rfl },
  { convert le_succ _,
    exact (classical.some_spec $ not_is_succ_limit_iff.1 h).2.symm }
end

section no_max_order
variables [no_max_order α]

lemma is_succ_limit.succ_ne (h : is_succ_limit a) (b) : succ b ≠ a := λ hb, not_is_max b (h b hb)

@[simp] lemma not_is_succ_limit_succ (a : α) : ¬ is_succ_limit (succ a) := λ h, h.succ_ne _ rfl

lemma is_succ_limit_iff_succ_ne : is_succ_limit a ↔ ∀ b, succ b ≠ a :=
⟨is_succ_limit.succ_ne, is_succ_limit_of_succ_ne⟩

lemma not_is_succ_limit_iff' : ¬ is_succ_limit a ↔ a ∈ range (@succ α _ _) :=
by { simp_rw [is_succ_limit_iff_succ_ne, not_forall, not_ne_iff], refl }

end no_max_order

section order_bot
variable [order_bot α]

lemma is_succ_limit_bot : is_succ_limit (⊥ : α) := is_min_bot.is_succ_limit

@[simp] lemma pred'_bot : pred' (⊥ : α) = ⊥ := is_succ_limit_bot.pred'_eq

end order_bot
end preorder

section partial_order
variables [partial_order α] [succ_order α]

lemma is_succ_limit.succ_lt (hb : is_succ_limit b) (ha : a < b) : succ a < b :=
begin
  by_cases h : is_max a,
  { rwa h.succ_eq },
  { rw [lt_iff_le_and_ne, succ_le_iff_of_not_is_max h],
    refine ⟨ha, λ hab, _⟩,
    subst hab,
    exact (h hb.is_max).elim }
end

lemma is_succ_limit.succ_lt_iff (hb : is_succ_limit b) : succ a < b ↔ a < b :=
⟨λ h, (le_succ a).trans_lt h, hb.succ_lt⟩

lemma is_succ_limit_iff_succ_lt : is_succ_limit b ↔ ∀ a < b, succ a < b :=
⟨λ hb a, hb.succ_lt, is_succ_limit_of_succ_lt⟩

lemma is_succ_limit_rec_on_succ' {C : α → Sort*} (hs : Π a, ¬ is_max a → C (succ a))
  (hl : Π a, is_succ_limit a → C a) {b : α} (hb : ¬ is_max b) :
  @is_succ_limit_rec_on α _ _ C (succ b) hs hl = hs b hb :=
begin
  have hb' := not_is_succ_limit_succ_of_not_is_max hb,
  have H := classical.some_spec (not_is_succ_limit_iff.1 hb'),
  rw is_succ_limit_rec_on,
  simp only [cast_eq_iff_heq, hb', not_false_iff, eq_mpr_eq_cast, dif_neg],
  congr,
  { exact (succ_eq_succ_iff_of_not_is_max H.1 hb).1 H.2 },
  { apply proof_irrel_heq }
end

lemma pred'_succ_of_not_is_max : ¬ is_max a → pred' (succ a) = a := is_succ_limit_rec_on_succ' _ _

lemma le_pred'_of_lt : a < b → a ≤ pred' b :=
begin
  refine is_succ_limit_rec_on b (λ c hc hc', _) (λ c hc hc', _),
  { rw pred'_succ_of_not_is_max hc,
    exact le_of_lt_succ hc' },
  { rw pred'_of_limit hc,
    exact hc'.le }
end

lemma le_of_pred'_lt : pred' a < b → a ≤ b :=
begin
  refine is_succ_limit_rec_on a (λ c hc hc', _) (λ c hc hc', _),
  { rw pred'_succ_of_not_is_max hc at hc',
    exact succ_le_of_lt hc' },
  { rw pred'_of_limit hc at hc',
    exact hc'.le }
end

lemma le_succ_pred' (a : α) : a ≤ succ (pred' a) :=
begin
  refine is_succ_limit_rec_on a (λ a ha, _) (λ a ha, _),
  { rw pred'_succ_of_not_is_max ha },
  { rw pred'_of_limit ha,
    exact le_succ a }
end

section no_max_order
variables [no_max_order α]

@[simp] lemma is_succ_limit_rec_on_succ {C : α → Sort*} (hs : Π a, ¬ is_max a → C (succ a))
  (hl : Π a, is_succ_limit a → C a) (b : α) :
  @is_succ_limit_rec_on α _ _ C (succ b) hs hl = hs b (not_is_max b) :=
is_succ_limit_rec_on_succ' _ _ _

@[simp] lemma pred'_succ (a : α) : pred' (succ a) = a := pred'_succ_of_not_is_max (not_is_max a)

end no_max_order
end partial_order

/-! ### Predecessor limits -/

section preorder
variables [preorder α] [pred_order α]

/-- A predecessor limit is a value that isn't a predecessor, except possibly of itself. -/
def is_pred_limit (a : α) : Prop := ∀ b, pred b = a → is_min b

protected lemma is_pred_limit.is_min (h : is_pred_limit (pred a)) : is_min a := h a rfl

lemma not_is_pred_limit_pred_of_not_is_min (ha : ¬ is_min a) : ¬ is_pred_limit (pred a) :=
λ h, ha (h a rfl)

protected lemma _root_.is_max.is_pred_limit : is_max a → is_pred_limit a :=
@is_min.is_succ_limit αᵒᵈ a _ _

lemma is_pred_limit_of_pred_ne (h : ∀ b, pred b ≠ a) : is_pred_limit a := λ b hb, (h _ hb).elim

lemma not_is_pred_limit_iff : ¬ is_pred_limit a ↔ ∃ b, ¬ is_min b ∧ pred b = a :=
@not_is_succ_limit_iff αᵒᵈ _ _ _

/-- See `order.not_is_pred_limit_iff` for a version that states that `a` is a predecessor of a value
other than itself. -/
lemma mem_range_pred_of_not_is_pred_limit : ¬ is_pred_limit a → a ∈ range (@pred α _ _) :=
@mem_range_succ_of_not_is_succ_limit αᵒᵈ _ _ _

lemma is_pred_limit_of_lt_pred : (∀ b > a, a < pred b) → is_pred_limit a :=
@is_succ_limit_of_succ_lt αᵒᵈ a _ _

/-- A value can be built by building it on predecessors and predecessor limits.

Note that you need a partial order for data built using this to behave nicely on successors. -/
@[elab_as_eliminator] noncomputable def is_pred_limit_rec_on : Π {C : α → Sort*} (b)
  (hs : Π a, ¬ is_min a → C (pred a)) (hl : Π a, is_pred_limit a → C a), C b :=
@is_succ_limit_rec_on αᵒᵈ _ _

lemma is_pred_limit_rec_on_limit : Π {C : α → Sort*} (hs : Π a, ¬ is_min a → C (pred a))
  (hl : Π a, is_pred_limit a → C a) (hb : is_pred_limit b),
  @is_pred_limit_rec_on α _ _ C b hs hl = hl b hb :=
@is_succ_limit_rec_on_limit αᵒᵈ b _ _

/-- A successor function for a `pred_order`. We have `succ' a = a` for a predecessor limit `a`, and
`succ' (pred a) = a` where `a` is not minimal.

When working in a pred-archimedean partial order, this can be used to build an `is_succ_archimdean`
instance: see `order.pred_order.to_is_succ_archimedean`.

Note that this is only nicely behaved on partial orders. -/
noncomputable def succ' : α → α := @pred' αᵒᵈ _ _

lemma succ'_of_limit : is_pred_limit a → succ' a = a := @pred'_of_limit αᵒᵈ _ _ _

alias succ'_of_limit ← is_pred_limit.succ'_eq

lemma le_succ' : ∀ b : α, b ≤ succ' b := @pred'_le αᵒᵈ _ _

section no_min_order
variables [no_min_order α]

lemma is_pred_limit.pred_ne (h : is_pred_limit a) (b) : pred b ≠ a := λ hb, not_is_min b (h b hb)

@[simp] lemma not_is_pred_limit_pred (a : α) : ¬ is_pred_limit (pred a) := λ h, h.pred_ne _ rfl

lemma is_pred_limit_iff_pred_ne : is_pred_limit a ↔ ∀ b, pred b ≠ a :=
@is_succ_limit_iff_succ_ne αᵒᵈ a _ _ _

lemma not_is_pred_limit_iff' : ¬ is_pred_limit a ↔ a ∈ range (@pred α _ _) :=
@not_is_succ_limit_iff' αᵒᵈ a _ _ _

end no_min_order

section order_top
variable [order_top α]

lemma is_pred_limit_top : is_pred_limit (⊤ : α) := is_max_top.is_pred_limit

@[simp] lemma succ'_top : succ' (⊤ : α) = ⊤ := @pred'_bot αᵒᵈ _ _ _

end order_top
end preorder

section partial_order
variables [partial_order α] [pred_order α]

lemma is_pred_limit.lt_pred : ∀ (ha : is_pred_limit a), a < b → a < pred b :=
@is_succ_limit.succ_lt αᵒᵈ b a _ _

lemma is_pred_limit.lt_pred_iff : ∀ (ha : is_pred_limit a), a < pred b ↔ a < b :=
@is_succ_limit.succ_lt_iff αᵒᵈ b a _ _

lemma is_pred_limit_iff_lt_pred : is_pred_limit a ↔ ∀ b > a, a < pred b :=
@is_succ_limit_iff_succ_lt αᵒᵈ a _ _

lemma is_pred_limit_rec_on_pred' : ∀ {C : α → Sort*} (hs : Π a, ¬ is_min a → C (pred a))
  (hl : Π a, is_pred_limit a → C a) {b : α} (hb : ¬ is_min b),
  @is_pred_limit_rec_on α _ _ C (pred b) hs hl = hs b hb :=
@is_succ_limit_rec_on_succ' αᵒᵈ _ _

lemma succ'_pred_of_not_is_min : ¬ is_min a → succ' (pred a) = a :=
@pred'_succ_of_not_is_max αᵒᵈ _ _ _

lemma succ'_le_of_lt : a < b → succ' a ≤ b := @le_pred'_of_lt αᵒᵈ _ _ _ _

lemma le_of_lt_succ' : a < succ' b → a ≤ b := @le_of_pred'_lt αᵒᵈ _ _ _ _

lemma pred_succ'_le : ∀ a : α, pred (succ' a) ≤ a := @le_succ_pred' αᵒᵈ _ _

section no_min_order
variables [no_min_order α]

@[simp] lemma is_pred_limit_rec_on_pred : ∀ {C : α → Sort*} (hs : Π a, ¬ is_min a → C (pred a))
  (hl : Π a, is_pred_limit a → C a) {b : α},
  @is_pred_limit_rec_on α _ _ C (pred b) hs hl = hs b (not_is_min b) :=
@is_succ_limit_rec_on_succ αᵒᵈ _ _ _

@[simp] lemma succ'_pred : ∀ a : α, succ' (pred a) = a := @pred'_succ αᵒᵈ _ _ _

end no_min_order
end partial_order
end order

open order

/-! ### Archimedeanness -/

/-- A `succ_order` and `pred_order` is succ-pred archimedean if one can go from any two comparable
elements by iterating `succ` or `pred`.

In a partial order, either condition implies the other: see `order.succ_pred_archimedean_of_succ`
and `order.succ_pred_archimedean_of_pred`. -/
class succ_pred_archimedean (α : Type*) [preorder α] [succ_order α] [pred_order α] : Prop :=
(exists_succ_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, succ^[n] a = b)
(exists_pred_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, pred^[n] b = a)

export succ_pred_archimedean (exists_succ_iterate_of_le)
export succ_pred_archimedean (exists_pred_iterate_of_le)

section preorder
variables [preorder α] [succ_order α] [pred_order α] [succ_pred_archimedean α]

instance : succ_pred_archimedean αᵒᵈ :=
⟨λ a b h, by convert exists_pred_iterate_of_le h.of_dual,
  λ a b h, by convert exists_succ_iterate_of_le h.of_dual⟩

section succ_lemmas

lemma has_le.le.exists_succ_iterate (h : a ≤ b) : ∃ n, succ^[n] a = b :=
exists_succ_iterate_of_le h

lemma exists_succ_iterate_iff_le : (∃ n, succ^[n] a = b) ↔ a ≤ b :=
begin
  refine ⟨_, exists_succ_iterate_of_le⟩,
  rintro ⟨n, rfl⟩,
  exact id_le_iterate_of_id_le le_succ n a,
end

-- We prove this using only the `exists_succ_iterate_of_le` assumption.
@[elab_as_eliminator] private lemma succ.rec_aux {α : Type*} [preorder α] [succ_order α]
  {P : α → Prop} {m : α} (H : ∀ a b : α, a ≤ b → ∃ n, succ^[n] a = b) (h0 : P m)
  (h1 : ∀ n, m ≤ n → P n → P (succ n)) ⦃n : α⦄ (hmn : m ≤ n) : P n :=
begin
  obtain ⟨n, rfl⟩ := H m n hmn, clear hmn,
  induction n with n ih,
  { exact h0 },
  { rw [function.iterate_succ_apply'], exact h1 _ (id_le_iterate_of_id_le le_succ n m) ih }
end

/-- Induction principle on a type with a `succ_order` for all elements above a given element `m`. -/
@[elab_as_eliminator] lemma succ.rec {P : α → Prop} {m : α} : ∀ (h0 : P m)
  (h1 : ∀ n, m ≤ n → P n → P (succ n)) ⦃n : α⦄ (hmn : m ≤ n), P n :=
succ.rec_aux $ λ a b, exists_succ_iterate_of_le

lemma succ.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) {a b : α} (h : a ≤ b) :
  p a ↔ p b :=
begin
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate,
  exact iterate.rec (λ b, p a ↔ p b) (λ c hc, hc.trans (hsucc _)) iff.rfl n,
end

lemma is_succ_limit.is_min_of_no_max [no_max_order α] (h : is_succ_limit a) : is_min a :=
λ b hb, begin
  rcases hb.exists_succ_iterate with ⟨_ | n, rfl⟩,
  { exact le_rfl },
  { rw iterate_succ_apply' at h,
    exact (not_is_succ_limit_succ _ h).elim }
end

@[simp] lemma is_succ_limit_iff_of_no_max [no_max_order α] : is_succ_limit a ↔ is_min a :=
⟨is_succ_limit.is_min_of_no_max, is_min.is_succ_limit⟩

lemma not_is_succ_limit_of_no_max [no_min_order α] [no_max_order α] : ¬ is_succ_limit a := by simp

end succ_lemmas

section pred_lemmas

lemma has_le.le.exists_pred_iterate (h : a ≤ b) : ∃ n, pred^[n] b = a :=
exists_pred_iterate_of_le h

lemma exists_pred_iterate_iff_le : (∃ n, pred^[n] b = a) ↔ a ≤ b :=
@exists_succ_iterate_iff_le αᵒᵈ _ _ _ _ _ _

/-- Induction principle on a type with a `pred_order` for all elements below a given element `m`. -/
@[elab_as_eliminator] lemma pred.rec {P : α → Prop} {m : α}
  (h0 : P m) (h1 : ∀ n, n ≤ m → P n → P (pred n)) ⦃n : α⦄ (hmn : n ≤ m) : P n :=
@succ.rec αᵒᵈ _ _ _ _ _ _ h0 h1 _ hmn

lemma pred.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) {a b : α} (h : a ≤ b) :
  p a ↔ p b :=
(@succ.rec_iff αᵒᵈ _ _ _ _ _ hsucc _ _ h).symm

protected lemma is_pred_limit.is_max_of_no_min [no_min_order α] : is_pred_limit a → is_max a :=
@is_succ_limit.is_min_of_no_max αᵒᵈ a _ _ _ _ _

@[simp] lemma is_pred_limit_iff_of_no_min [no_min_order α] : is_pred_limit a ↔ is_max a :=
@is_succ_limit_iff_of_no_max αᵒᵈ a _ _ _ _ _

lemma not_is_pred_limit_of_no_min [no_min_order α] [no_max_order α] : ¬ is_pred_limit a :=
by simp

end pred_lemmas
end preorder

section partial_order
variables [partial_order α] [succ_order α] [pred_order α] [succ_pred_archimedean α]

section succ_lemmas

-- We prove this using only the `exists_succ_iterate_of_le` assumption.
private lemma is_succ_limit.is_min_aux {α : Type*} [partial_order α] [succ_order α] {a : α}
  (H : ∀ a b : α, a ≤ b → ∃ n, succ^[n] a = b) (h : is_succ_limit a) : is_min a :=
λ b hb, begin
  revert h,
  refine succ.rec_aux H (λ _, le_rfl) (λ c hbc H hc, _) hb,
  have := hc.is_max.succ_eq,
  rw this at hc ⊢,
  exact H hc
end

protected lemma is_succ_limit.is_min : is_succ_limit a → is_min a :=
is_succ_limit.is_min_aux $ λ a b, exists_succ_iterate_of_le

@[simp] lemma is_succ_limit_iff : is_succ_limit a ↔ is_min a :=
⟨is_succ_limit.is_min, is_min.is_succ_limit⟩

lemma not_is_succ_limit [no_min_order α] : ¬ is_succ_limit a := by simp

-- We prove this using only the `exists_succ_iterate_of_le` assumption.
private lemma min_of_le_pred'_aux {α : Type*} [partial_order α] [succ_order α] {a : α}
  (H : ∀ a b : α, a ≤ b → ∃ n, succ^[n] a = b) : a ≤ pred' a → is_min a :=
begin
  refine is_succ_limit_rec_on a (λ b hb hb', _) (λ a h _, is_succ_limit.is_min_aux H h),
  rw pred'_succ_of_not_is_max hb at hb',
  exact (hb'.not_lt $ lt_succ_of_not_is_max hb).elim
end

lemma min_of_le_pred' : a ≤ pred' a → is_min a :=
min_of_le_pred'_aux $ λ a b, exists_succ_iterate_of_le

-- We prove this using only the `exists_succ_iterate_of_le` assumption.
private noncomputable def succ_order.to_pred_order_aux {α : Type*} [partial_order α] [succ_order α]
  (H : ∀ a b : α, a ≤ b → ∃ n, succ^[n] a = b) : pred_order α :=
{ pred := pred',
  pred_le := pred'_le,
  min_of_le_pred := λ a, min_of_le_pred'_aux H,
  le_pred_of_lt := λ a b, le_pred'_of_lt,
  le_of_pred_lt := λ a b, le_of_pred'_lt }

/-- Builds a `pred_order` from a `succ_order` via `order.pred'`. -/
noncomputable def succ_order.to_pred_order : pred_order α :=
{ pred := pred', ..succ_order.to_pred_order_aux $ λ a b, exists_succ_iterate_of_le }

-- We prove this using only the `exists_succ_iterate_of_le` assumption.
private lemma pred'_eq_pred_aux {α : Type*} [partial_order α] [succ_order α] [pred_order α]
  (H : ∀ a b : α, a ≤ b → ∃ n, succ^[n] a = b) : @pred' α _ _ = pred :=
show @pred α _ (succ_order.to_pred_order_aux H) = pred, by congr

@[simp] lemma pred'_eq_pred : @pred' α _ _ = pred :=
pred'_eq_pred_aux $ λ a b, exists_succ_iterate_of_le

-- We prove this using only the `exists_succ_iterate_of_le` assumption.
private lemma exists_pred'_iterate_of_le_aux {α : Type*} [partial_order α] [succ_order α]
  [pred_order α] (H : ∀ a b : α, a ≤ b → ∃ n, succ^[n] a = b) {a b : α} (h : a ≤ b) :
  ∃ n : ℕ, pred'^[n] b = a :=
begin
  cases H a b h with n hn,
  induction n with n IH generalizing a b,
  { exact ⟨0, hn.symm⟩ },
  { rw iterate_succ_apply' at hn,
    by_cases hs : is_max (succ^[n] a),
    { rw hs.succ_eq at hn,
      exact IH h hn },
    { rcases eq_or_lt_of_le h with rfl | h,
      { exact ⟨0, rfl⟩ },
      { apply_fun pred' at hn,
        rw pred'_succ_of_not_is_max hs at hn,
        cases IH (le_pred'_of_lt h) hn with m hm,
        exact ⟨m + 1, hm⟩ } } }
end

lemma exists_pred'_iterate_of_le : a ≤ b → ∃ n : ℕ, pred'^[n] b = a :=
exists_pred'_iterate_of_le_aux $ λ a b, exists_succ_iterate_of_le

/-- A partial order is succ-pred archimedean if it satisfies `exists_succ_iterate_of_le`. -/
lemma succ_pred_archimedean_of_succ {α : Type*} [partial_order α] [succ_order α] [pred_order α]
  (H : ∀ a b : α, a ≤ b → ∃ n, succ^[n] a = b) : succ_pred_archimedean α :=
⟨H, by { rw ←pred'_eq_pred_aux H, exact λ a b, exists_pred'_iterate_of_le_aux H }⟩

end succ_lemmas

section pred_lemmas

protected lemma is_pred_limit.is_max : is_pred_limit a → is_max a :=
@is_succ_limit.is_min αᵒᵈ a _ _ _ _

@[simp] lemma is_pred_limit_iff : is_pred_limit a ↔ is_max a :=
@is_succ_limit_iff αᵒᵈ a _ _ _ _

lemma not_is_pred_limit [no_max_order α] : ¬ is_pred_limit a := by simp

lemma max_of_succ'_le : succ' a ≤ a → is_max a := @min_of_le_pred' αᵒᵈ _ _ _ _ _

/-- Builds a `succ_order` from a `pred_order` via `order.succ'`. -/
noncomputable def pred_order.to_succ_order : succ_order α :=
{ succ := succ',
  le_succ := le_succ',
  max_of_succ_le := λ a, max_of_succ'_le,
  succ_le_of_lt := λ a b, succ'_le_of_lt,
  le_of_lt_succ := λ a b, le_of_lt_succ' }

@[simp] lemma succ'_eq_succ : @succ' α _ _ = succ := @pred'_eq_pred αᵒᵈ _ _ _ _

lemma exists_succ'_iterate_of_le : a ≤ b → ∃ n : ℕ, succ'^[n] a = b :=
@exists_pred'_iterate_of_le αᵒᵈ _ _ _ _ _ _

/-- A partial order is succ-pred archimedean if it satisfies `exists_pred_iterate_of_le`. -/
lemma succ_pred_archimedean_of_pred {α : Type*} [partial_order α] [succ_order α] [pred_order α]
  (H : ∀ a b : α, a ≤ b → ∃ n, pred^[n] b = a) : succ_pred_archimedean α :=
begin
  letI := @succ_pred_archimedean_of_succ αᵒᵈ _ _ _ (λ a b, H b a),
  convert @order_dual.succ_pred_archimedean αᵒᵈ _ _ _ _
end

end pred_lemmas
end partial_order

section linear_order
variables [linear_order α] [succ_order α] [pred_order α] [succ_pred_archimedean α]

section succ_lemmas

lemma exists_succ_iterate_or : (∃ n, succ^[n] a = b) ∨ ∃ n, succ^[n] b = a :=
(le_total a b).imp exists_succ_iterate_of_le exists_succ_iterate_of_le

lemma succ.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) (a b : α) : p a ↔ p b :=
(le_total a b).elim (succ.rec_iff hsucc) (λ h, (succ.rec_iff hsucc h).symm)

end succ_lemmas

section pred_lemmas

lemma exists_pred_iterate_or : (∃ n, pred^[n] b = a) ∨ ∃ n, pred^[n] a = b :=
(le_total a b).imp exists_pred_iterate_of_le exists_pred_iterate_of_le

lemma pred.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) (a b : α) : p a ↔ p b :=
(le_total a b).elim (pred.rec_iff hsucc) (λ h, (pred.rec_iff hsucc h).symm)

end pred_lemmas
end linear_order

section is_well_order
variables [linear_order α] [succ_order α] [pred_order α]

@[priority 100]
instance is_well_order.lt.to_succ_pred_archimedean [h : is_well_order α (<)] :
  succ_pred_archimedean α :=
succ_pred_archimedean_of_pred $ λ a, begin
  refine well_founded.fix h.wf (λ b ih hab, _),
  replace hab := hab.eq_or_lt,
  rcases hab with rfl | hab,
  { exact ⟨0, rfl⟩ },
  cases le_or_lt b (pred b) with hb hb,
  { cases (min_of_le_pred hb).not_lt hab },
  obtain ⟨k, hk⟩ := ih (pred b) hb (le_pred_of_lt hab),
  refine ⟨k + 1, _⟩,
  rw [iterate_add_apply, iterate_one, hk],
end

@[priority 100]
instance is_well_order.gt.to_succ_pred_archimedean [is_well_order α (>)] :
  succ_pred_archimedean α :=
by convert @order_dual.succ_pred_archimedean αᵒᵈ _ _ _ _

end is_well_order

section bounded
variables [preorder α] [succ_order α] [pred_order α] [succ_pred_archimedean α]

section order_bot
variable [order_bot α]

lemma succ.rec_bot (p : α → Prop) (hbot : p ⊥) (hsucc : ∀ a, p a → p (succ a)) (a : α) : p a :=
succ.rec hbot (λ x _ h, hsucc x h) (bot_le : ⊥ ≤ a)

end order_bot

section order_top
variable [order_top α]

lemma pred.rec_top (p : α → Prop) (htop : p ⊤) (hpred : ∀ a, p a → p (pred a)) (a : α) : p a :=
pred.rec htop (λ x _ h, hpred x h) (le_top : a ≤ ⊤)

end order_top
end bounded
