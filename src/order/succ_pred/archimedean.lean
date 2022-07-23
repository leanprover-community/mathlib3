/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Violeta Hernández Palacios
-/

import order.succ_pred.limit

/-!
# Successor-predecessor archimedean orders

We define `succ_pred_archimedean` orders, as `succ_order`s and `pred_order`s where `succ` iterated
to an element gives all the greater ones, and `pred` iterated to an element gives all the smaller
ones.

## Main results

- `order.succ_order.to_pred_order`: in a partial order satisfying `exists_succ_iterate_of_le`, the
  predecessor function given by `order.pred'` forms a `pred_order`.
- `order.pred_order.to_succ_order`: in a partial order satisfying `exists_pred_iterate_of_le`, the
  successor function given by `order.succ'` forms a `succ_order`.
- `succ_pred_archimedean_of_succ`: a `succ_order` and `pred_order` satisfying `exists_succ_of_le` is
  `succ_pred_archimedean`.
- `succ_pred_archimedean_of_pred`: a `succ_order` and `pred_order` satisfying `exists_pred_of_le` is
  `succ_pred_archimedean`.
-/

variables {α : Type*} {a b : α}

open function order

/-! ### Archimedeanness -/

/-- A `succ_order` and `pred_order` is succ-pred archimedean if one can go from any two comparable
elements by iterating `succ` or `pred`.

In a partial order, either condition implies the other: see `succ_pred_archimedean_of_succ`
and `succ_pred_archimedean_of_pred`. -/
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

/-- Given a partial `succ_order` satisfying `exists_succ_iterate_of_le`, one can use `order.pred'`
to build a `pred_order` instance. This order is also succ-pred archimedean, see
`succ_pred_archimedean_of_succ`. -/
noncomputable def order.succ_order.to_pred_order {α : Type*} [partial_order α] [succ_order α]
  (H : ∀ a b : α, a ≤ b → ∃ n, succ^[n] a = b) : pred_order α :=
{ pred := pred',
  pred_le := pred'_le,
  min_of_le_pred := λ a, min_of_le_pred'_aux H,
  le_pred_of_lt := λ a b, le_pred'_of_lt,
  le_of_pred_lt := λ a b, le_of_pred'_lt }

-- We prove this using only the `exists_succ_iterate_of_le` assumption.
private lemma pred'_eq_pred_aux {α : Type*} [partial_order α] [succ_order α] [pred_order α]
  (H : ∀ a b : α, a ≤ b → ∃ n, succ^[n] a = b) : @pred' α _ _ = pred :=
show @pred α _ (order.succ_order.to_pred_order H) = pred, by congr

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

/-- Given a partial `pred_order` satisfying `exists_pred_iterate_of_le`, one can use `order.succ'`
to build a `succ_order` instance. This order is also succ-pred archimedean, see
`order.succ_pred_archimedean_of_pred`. -/
noncomputable def order.pred_order.to_succ_order {α : Type*} [partial_order α] [pred_order α]
  (H : ∀ a b : α, a ≤ b → ∃ n, pred^[n] b = a) : succ_order α :=
{ succ := succ',
  le_succ := le_succ',
  max_of_succ_le := λ a, @min_of_le_pred'_aux αᵒᵈ _ _ a $ λ a b, H b a,
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
