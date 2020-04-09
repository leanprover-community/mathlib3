/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Yury Kudryashov
-/
import data.list.pairwise

universes u v

open nat

variables {α : Type u} {β : Type v}

namespace list

/- chain relation (conjunction of R a b ∧ R b c ∧ R c d ...) -/

run_cmd tactic.mk_iff_of_inductive_prop `list.chain `list.chain_iff

variable {R : α → α → Prop}

theorem rel_of_chain_cons {a b : α} {l : list α}
  (p : chain R a (b::l)) : R a b :=
(chain_cons.1 p).1

theorem chain_of_chain_cons {a b : α} {l : list α}
  (p : chain R a (b::l)) : chain R b l :=
(chain_cons.1 p).2

theorem chain.imp' {S : α → α → Prop}
  (HRS : ∀ ⦃a b⦄, R a b → S a b) {a b : α} (Hab : ∀ ⦃c⦄, R a c → S b c)
  {l : list α} (p : chain R a l) : chain S b l :=
by induction p with _ a c l r p IH generalizing b; constructor;
   [exact Hab r, exact IH (@HRS _)]

theorem chain.imp {S : α → α → Prop}
  (H : ∀ a b, R a b → S a b) {a : α} {l : list α} (p : chain R a l) : chain S a l :=
p.imp' H (H a)

theorem chain.iff {S : α → α → Prop}
  (H : ∀ a b, R a b ↔ S a b) {a : α} {l : list α} : chain R a l ↔ chain S a l :=
⟨chain.imp (λ a b, (H a b).1), chain.imp (λ a b, (H a b).2)⟩

theorem chain.iff_mem {a : α} {l : list α} :
  chain R a l ↔ chain (λ x y, x ∈ a :: l ∧ y ∈ l ∧ R x y) a l :=
⟨λ p, by induction p with _ a b l r p IH; constructor;
  [exact ⟨mem_cons_self _ _, mem_cons_self _ _, r⟩,
   exact IH.imp (λ a b ⟨am, bm, h⟩,
    ⟨mem_cons_of_mem _ am, mem_cons_of_mem _ bm, h⟩)],
 chain.imp (λ a b h, h.2.2)⟩

theorem chain_singleton {a b : α} : chain R a [b] ↔ R a b :=
by simp only [chain_cons, chain.nil, and_true]

theorem chain_split {a b : α} {l₁ l₂ : list α} : chain R a (l₁++b::l₂) ↔
  chain R a (l₁++[b]) ∧ chain R b l₂ :=
by induction l₁ with x l₁ IH generalizing a;
simp only [*, nil_append, cons_append, chain.nil, chain_cons, and_true, and_assoc]

theorem chain_map (f : β → α) {b : β} {l : list β} :
  chain R (f b) (map f l) ↔ chain (λ a b : β, R (f a) (f b)) b l :=
by induction l generalizing b; simp only [map, chain.nil, chain_cons, *]

theorem chain_of_chain_map {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, S (f a) (f b) → R a b) {a : α} {l : list α}
  (p : chain S (f a) (map f l)) : chain R a l :=
((chain_map f).1 p).imp H

theorem chain_map_of_chain {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, R a b → S (f a) (f b)) {a : α} {l : list α}
  (p : chain R a l) : chain S (f a) (map f l) :=
(chain_map f).2 $ p.imp H

theorem chain_of_pairwise {a : α} {l : list α} (p : pairwise R (a::l)) : chain R a l :=
begin
  cases pairwise_cons.1 p with r p', clear p,
  induction p' with b l r' p IH generalizing a, {exact chain.nil},
  simp only [chain_cons, forall_mem_cons] at r,
  exact chain_cons.2 ⟨r.1, IH r'⟩
end

theorem chain_iff_pairwise (tr : transitive R) {a : α} {l : list α} :
  chain R a l ↔ pairwise R (a::l) :=
⟨λ c, begin
  induction c with b b c l r p IH, {exact pairwise_singleton _ _},
  apply IH.cons _, simp only [mem_cons_iff, forall_mem_cons', r, true_and],
  show ∀ x ∈ l, R b x, from λ x m, (tr r (rel_of_pairwise_cons IH m)),
end, chain_of_pairwise⟩

theorem chain_iff_nth_le {R} : ∀ {a : α} {l : list α},
  chain R a l ↔ (∀ h : 0 < length l, R a (nth_le l 0 h)) ∧ (∀ i (h : i < length l - 1),
    R (nth_le l i (lt_of_lt_pred h)) (nth_le l (i+1) (lt_pred_iff.mp h)))
| a [] := by simp
| a (b :: t) :=
begin
  rw [chain_cons, chain_iff_nth_le],
  split,
  { rintros ⟨R, ⟨h0, h⟩⟩,
    split,
    { intro w, exact R, },
    { intros i w,
      cases i,
      { apply h0, },
      { convert h i _ using 1,
        simp only [succ_eq_add_one, add_succ_sub_one, add_zero, length, add_lt_add_iff_right] at w,
        exact lt_pred_iff.mpr w, } } },
  { rintros ⟨h0, h⟩, split,
    { apply h0, simp, },
    { split,
      { apply h 0, },
      { intros i w, convert h (i+1) _,
        exact lt_pred_iff.mp w, } } },
end

theorem chain'.imp {S : α → α → Prop}
  (H : ∀ a b, R a b → S a b) {l : list α} (p : chain' R l) : chain' S l :=
by cases l; [trivial, exact p.imp H]

theorem chain'.iff {S : α → α → Prop}
  (H : ∀ a b, R a b ↔ S a b) {l : list α} : chain' R l ↔ chain' S l :=
⟨chain'.imp (λ a b, (H a b).1), chain'.imp (λ a b, (H a b).2)⟩

theorem chain'.iff_mem : ∀ {l : list α}, chain' R l ↔ chain' (λ x y, x ∈ l ∧ y ∈ l ∧ R x y) l
| [] := iff.rfl
| (x::l) :=
  ⟨λ h, (chain.iff_mem.1 h).imp $ λ a b ⟨h₁, h₂, h₃⟩, ⟨h₁, or.inr h₂, h₃⟩,
   chain'.imp $ λ a b h, h.2.2⟩

@[simp] theorem chain'_nil : chain' R [] := trivial

@[simp] theorem chain'_singleton (a : α) : chain' R [a] := chain.nil

theorem chain'_split {a : α} : ∀ {l₁ l₂ : list α}, chain' R (l₁++a::l₂) ↔
  chain' R (l₁++[a]) ∧ chain' R (a::l₂)
| []      l₂ := (and_iff_right (chain'_singleton a)).symm
| (b::l₁) l₂ := chain_split

theorem chain'_map (f : β → α) {l : list β} :
  chain' R (map f l) ↔ chain' (λ a b : β, R (f a) (f b)) l :=
by cases l; [refl, exact chain_map _]

theorem chain'_of_chain'_map {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, S (f a) (f b) → R a b) {l : list α}
  (p : chain' S (map f l)) : chain' R l :=
((chain'_map f).1 p).imp H

theorem chain'_map_of_chain' {S : β → β → Prop} (f : α → β)
  (H : ∀ a b : α, R a b → S (f a) (f b)) {l : list α}
  (p : chain' R l) : chain' S (map f l) :=
(chain'_map f).2 $ p.imp H

theorem pairwise.chain' : ∀ {l : list α}, pairwise R l → chain' R l
| [] _ := trivial
| (a::l) h := chain_of_pairwise h

theorem chain'_iff_pairwise (tr : transitive R) : ∀ {l : list α},
  chain' R l ↔ pairwise R l
| [] := (iff_true_intro pairwise.nil).symm
| (a::l) := chain_iff_pairwise tr

@[simp] theorem chain'_cons {x y l} : chain' R (x :: y :: l) ↔ R x y ∧ chain' R (y :: l) :=
chain_cons

theorem chain'.cons {x y l} (h₁ : R x y) (h₂ : chain' R (y :: l)) :
  chain' R (x :: y :: l) :=
chain'_cons.2 ⟨h₁, h₂⟩

theorem chain'.tail : ∀ {l} (h : chain' R l), chain' R l.tail
| []            _ := trivial
| [x]           _ := trivial
| (x :: y :: l) h := (chain'_cons.mp h).right

theorem chain'_pair {x y} : chain' R [x, y] ↔ R x y :=
by simp only [chain'_singleton, chain'_cons, and_true]

theorem chain'_reverse : ∀ {l}, chain' R (reverse l) ↔ chain' (flip R) l
| [] := iff.rfl
| [a] := by simp only [chain'_singleton, reverse_singleton]
| (a :: b :: l) := by rw [chain'_cons, reverse_cons, reverse_cons, append_assoc, cons_append,
    nil_append, chain'_split, ← reverse_cons, @chain'_reverse (b :: l), and_comm, chain'_pair, flip]

theorem chain'_iff_nth_le {R} : ∀ {l : list α},
  chain' R l ↔ ∀ i (h : i < length l - 1),
    R (nth_le l i (lt_of_lt_pred h)) (nth_le l (i+1) (lt_pred_iff.mp h))
| [] := by simp
| (a :: nil) := by simp
| (a :: b :: t) :=
begin
  rw [chain'_cons, chain'_iff_nth_le],
  split,
  { rintros ⟨R, h⟩ i w,
    cases i,
    { exact R, },
    { convert h i _ using 1,
      simp only [succ_eq_add_one, add_succ_sub_one, add_zero, length, add_lt_add_iff_right] at w,
      simpa using w, },
   },
  { rintros h, split,
    { apply h 0, simp, },
    { intros i w, convert h (i+1) _,
      simp only [add_zero, length, add_succ_sub_one] at w,
      simpa using w, }
    },
end

end list
