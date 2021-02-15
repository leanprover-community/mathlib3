/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.nat.basic
import data.equiv.denumerable
import order.rel_iso
import logic.function.iterate

namespace rel_embedding

variables {α : Type*} {r : α → α → Prop} [is_strict_order α r]

/-- If `f` is a strictly `r`-increasing sequence, then this returns `f` as an order embedding. -/
def nat_lt (f : ℕ → α) (H : ∀ n:ℕ, r (f n) (f (n+1))) :
  ((<) : ℕ → ℕ → Prop) ↪r r :=
of_monotone f $ λ a b h, begin
  induction b with b IH, {exact (nat.not_lt_zero _ h).elim},
  cases nat.lt_succ_iff_lt_or_eq.1 h with h e,
  { exact trans (IH h) (H _) },
  { subst b, apply H }
end

@[simp]
lemma nat_lt_apply {f : ℕ → α} {H : ∀ n:ℕ, r (f n) (f (n+1))} {n : ℕ} : nat_lt f H n = f n := rfl

/-- If `f` is a strictly `r`-decreasing sequence, then this returns `f` as an order embedding. -/
def nat_gt (f : ℕ → α) (H : ∀ n:ℕ, r (f (n+1)) (f n)) :
  ((>) : ℕ → ℕ → Prop) ↪r r :=
by haveI := is_strict_order.swap r; exact rel_embedding.swap (nat_lt f H)

theorem well_founded_iff_no_descending_seq :
  well_founded r ↔ ¬ nonempty (((>) : ℕ → ℕ → Prop) ↪r r) :=
⟨λ ⟨h⟩ ⟨⟨f, o⟩⟩,
  suffices ∀ a, acc r a → ∀ n, a ≠ f n, from this (f 0) (h _) 0 rfl,
  λ a ac, begin
    induction ac with a _ IH, intros n h, subst a,
    exact IH (f (n+1)) (o.2 (nat.lt_succ_self _)) _ rfl
  end,
λ N, ⟨λ a, classical.by_contradiction $ λ na,
  let ⟨f, h⟩ := classical.axiom_of_choice $
    show ∀ x : {a // ¬ acc r a}, ∃ y : {a // ¬ acc r a}, r y.1 x.1,
    from λ ⟨x, h⟩, classical.by_contradiction $ λ hn, h $
      ⟨_, λ y h, classical.by_contradiction $ λ na, hn ⟨⟨y, na⟩, h⟩⟩ in
  N ⟨nat_gt (λ n, (f^[n] ⟨a, na⟩).1) $ λ n,
    by { rw [function.iterate_succ'], apply h }⟩⟩⟩

end rel_embedding

namespace nat

variables (s : set ℕ) [decidable_pred s] [infinite s]
/-- An order embedding from `ℕ` to itself with a specified range -/
def order_embedding_of_set : ℕ ↪o ℕ :=
(rel_embedding.order_embedding_of_lt_embedding
  (rel_embedding.nat_lt (nat.subtype.of_nat s) (λ n, nat.subtype.lt_succ_self _))).trans
  (order_embedding.subtype s)

/-- `nat.subtype.of_nat` as an order isomorphism between `ℕ` and an infinite decidable subset. -/
noncomputable def subtype.order_iso_of_nat  :
  ℕ ≃o s :=
rel_iso.of_surjective (rel_embedding.order_embedding_of_lt_embedding
  (rel_embedding.nat_lt (nat.subtype.of_nat s) (λ n, nat.subtype.lt_succ_self _)))
  nat.subtype.of_nat_surjective

variable {s}

@[simp]
lemma order_embedding_of_set_apply {n : ℕ} : order_embedding_of_set s n = subtype.of_nat s n :=
rfl

@[simp]
lemma subtype.order_iso_of_nat_apply {n : ℕ} :
  subtype.order_iso_of_nat s n = subtype.of_nat s n :=
by { simp [subtype.order_iso_of_nat] }

@[simp]
lemma order_embedding_of_set_range : set.range (nat.order_embedding_of_set s) = s :=
begin
  ext x,
  rw [set.mem_range, nat.order_embedding_of_set],
  split; intro h,
  { rcases h with ⟨y, rfl⟩,
    simp },
  { refine ⟨(nat.subtype.order_iso_of_nat s).symm ⟨x, h⟩, _⟩,
    simp only [rel_embedding.coe_trans, rel_embedding.order_embedding_of_lt_embedding_apply,
      rel_embedding.nat_lt_apply, function.comp_app, order_embedding.coe_subtype],
    rw [← subtype.order_iso_of_nat_apply, order_iso.apply_symm_apply, subtype.coe_mk] }
end

end nat
