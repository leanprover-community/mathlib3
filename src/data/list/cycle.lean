/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.list.rotate
import tactic.slim_check

/-!
# Cycles of a list

Lists have an equivalence relation of whether they are rotational permutations of one another.
This relation is defined as `is_rotated`.

A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.

Based on this, we define the quotient of lists by the rotation relation, called `cycle`.
We define a permutation from a `s : cycle α` by lifting `form_perm` into the quotient.

-/

namespace list

variables {α : Type*} [decidable_eq α]

def next: Π (l : list α) (x : α) (h : x ∈ l), α
| []             _ h := by simpa using h
| [y]            _ _ := y
| (y :: z :: xs) x h := if hx : x = y then z else
  if x = (y :: z :: xs).last (cons_ne_nil _ _) then y
    else next (z :: xs) x (by simpa [hx] using h)

def prev : Π (l : list α) (x : α) (h : x ∈ l), α
| []             _ h := by simpa using h
| [y]            _ _ := y
| (y :: z :: xs) x h := if hx : x = y then (last (z :: xs) (cons_ne_nil _ _)) else
  if x = z then y else prev (z :: xs) x (by simpa [hx] using h)

variables (l : list α) (x : α) (h : x ∈ l)

@[simp] lemma next_singleton (x y : α) (h : x ∈ [y]) :
  next [y] x h = y := rfl

@[simp] lemma prev_singleton (x y : α) (h : x ∈ [y]) :
  prev [y] x h = y := rfl

lemma next_cons_cons_eq' (y z : α) (h : x ∈ (y :: z :: l)) (hx : x = y) :
  next (y :: z :: l) x h = z :=
by rw [next, dif_pos hx]

@[simp] lemma next_cons_cons_eq (z : α) (h : x ∈ (x :: z :: l)) :
  next (x :: z :: l) x h = z :=
next_cons_cons_eq' l x x z h rfl

lemma next_last_cons (y : α) (h : x ∈ (y :: l)) (hx : x = last (y :: l) (cons_ne_nil _ _))
  (hy : x ≠ y) :
  next (y :: l) x h = y :=
begin
  cases l,
  { simp },
  { rw [next, dif_neg hy, if_pos hx] }
end

lemma prev_last_cons' (y : α) (h : x ∈ (y :: l)) (hx : x = y) :
  prev (y :: l) x h = last (y :: l) (cons_ne_nil _ _) :=
begin
  cases l;
  simp [prev, hx]
end

@[simp] lemma prev_last_cons (h : x ∈ (x :: l)) :
  prev (x :: l) x h = last (x :: l) (cons_ne_nil _ _) :=
prev_last_cons' l x x h rfl

lemma prev_cons_cons_eq' (y z : α) (h : x ∈ (y :: z :: l)) (hx : x = y) :
  prev (y :: z :: l) x h = last (z :: l) (cons_ne_nil _ _) :=
by rw [prev, dif_pos hx]

@[simp] lemma prev_cons_cons_eq (z : α) (h : x ∈ (x :: z :: l)) :
  prev (x :: z :: l) x h = last (z :: l) (cons_ne_nil _ _) :=
prev_cons_cons_eq' l x x z h rfl

include h

lemma next_mem : l.next x h ∈ l :=
begin
  cases l with hd tl,
  { simpa using h },
  induction tl with hd' tl hl generalizing hd,
  { simp },
  { by_cases hx : x = hd,
    { simp [hx] },
    { rw [next, dif_neg hx],
      split_ifs with hm,
      { exact mem_cons_self _ _ },
      { exact mem_cons_of_mem _ (hl _ _) } } }
end

lemma prev_mem : l.prev x h ∈ l :=
begin
  cases l with hd tl,
  { simpa using h },
  induction tl with hd' tl hl generalizing hd,
  { simp },
  { by_cases hx : x = hd,
    { simp only [hx, prev_cons_cons_eq],
      exact mem_cons_of_mem _ (last_mem _) },
    { rw [prev, dif_neg hx],
      split_ifs with hm,
      { exact mem_cons_self _ _ },
      { exact mem_cons_of_mem _ (hl _ _) } } }
end

end list

open list

def cycle (α : Type*) : Type* := quotient (is_rotated.setoid α)

namespace cycle

variables {α : Type*}

instance : has_coe (list α) (cycle α) := ⟨quot.mk _⟩

@[simp] lemma coe_eq_coe {l₁ l₂ : list α} : (l₁ : cycle α) = l₂ ↔ (l₁ ~r l₂) :=
@quotient.eq _ (is_rotated.setoid _) _ _

@[simp] lemma mk_eq_coe (l : list α) :
  quot.mk _ l = (l : cycle α) := rfl

def mem (a : α) (s : cycle α) : Prop :=
quot.lift_on s (λ l, a ∈ l) (λ l₁ l₂ (e : l₁ ~r l₂), propext $ e.mem_iff)

instance : has_mem α (cycle α) := ⟨mem⟩

@[simp] lemma mem_coe_iff {a : α} {l : list α} :
  a ∈ (l : cycle α) ↔ a ∈ l := iff.rfl

instance [decidable_eq α] : decidable_eq (cycle α) :=
λ s₁ s₂, quotient.rec_on_subsingleton₂' s₁ s₂ (λ l₁ l₂,
  decidable_of_iff' _ quotient.eq')

def reverse (s : cycle α) : cycle α :=
quot.map reverse (λ l₁ l₂ (e : l₁ ~r l₂), e.reverse) s

lemma coe_reverse (l : list α) :
  (l.reverse : cycle α) = reverse l := rfl

@[simp] lemma mem_reverse_iff {a : α} {s : cycle α} :
  a ∈ s.reverse ↔ a ∈ s :=
quot.induction_on s (λ _, mem_reverse)

def length (s : cycle α) : ℕ :=
quot.lift_on s length (λ l₁ l₂ (e : l₁ ~r l₂), e.perm.length_eq)

@[simp] lemma length_coe (l : list α) :
  length (l : cycle α) = l.length := rfl

@[simp] lemma length_reverse (s : cycle α) :
  s.reverse.length = s.length :=
quot.induction_on s length_reverse

def subsingleton (s : cycle α) : Prop :=
s.length ≤ 1

lemma length_subsingleton_iff {s : cycle α} :
  subsingleton s ↔ length s ≤ 1 := iff.rfl

@[simp] lemma subsingleton_reverse_iff {s : cycle α} :
  s.reverse.subsingleton ↔ s.subsingleton :=
by simp [length_subsingleton_iff]

def nontrivial (s : cycle α) : Prop := ∃ (x y : α) (h : x ≠ y), x ∈ s ∧ y ∈ s

@[simp] lemma nontrivial_reverse_iff {s : cycle α} :
  s.reverse.nontrivial ↔ s.nontrivial :=
by simp [nontrivial]

lemma length_nontrivial {s : cycle α} (h : nontrivial s) :
  2 ≤ length s :=
begin
  obtain ⟨x, y, hxy, hx, hy⟩ := h,
  induction s using quot.induction_on with l,
  rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩),
  { simpa using hx },
  { simp only [mem_coe_iff, mk_eq_coe, mem_singleton] at hx hy,
    simpa [hx, hy] using hxy },
  { simp [bit0] }
end

def nodup (s : cycle α) : Prop :=
quot.lift_on s nodup (λ l₁ l₂ (e : l₁ ~r l₂), propext $ e.nodup_iff)

@[simp] lemma nodup_coe_iff {l : list α} :
  nodup (l : cycle α) ↔ l.nodup := iff.rfl

@[simp] lemma nodup_reverse_iff {s : cycle α} :
  s.reverse.nodup ↔ s.nodup :=
quot.induction_on s (λ _, nodup_reverse)

lemma subsingleton.nodup {s : cycle α} (h : subsingleton s) :
  nodup s :=
begin
  induction s using quot.induction_on with l,
  cases l with hd tl,
  { simp },
  { have : tl = [] := by simpa [subsingleton, length_eq_zero] using h,
    simp [this] }
end

instance [decidable_eq α] {s : cycle α} : decidable (nodup s) :=
quot.rec_on_subsingleton s (λ (l : list α), list.nodup_decidable l)

end cycle
