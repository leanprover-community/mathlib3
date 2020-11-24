/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import order.basic
import data.finset
import data.multiset.finset_ops

/-!
# Antichains
Investigating the structure of finsets in a partial order.
We define antichains.

## Main definitions
* `antichain` is a family of sets where no set is a subset of another.
-/

open partial_order

universe u

open_locale classical
noncomputable theory

variable {α : Type u}

section
variables [partial_order α] [decidable_eq α] [fintype α]

/--
A set of elements of a partial order forms an antichain if no two elements
`A` and `B` are ordered `A < B`.
-/
def antichain (𝒜 : finset α) : Prop := ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, a ≤ b → a = b

lemma antichain_mem (A : finset α) (hA : antichain A) (a : α) :
  a ∈ A → ∀ b ∈ A, a ≤ b → a = b :=
begin
  intros ha b hb hab,
  exact hA a ha b hb hab
end

theorem subset_antichain (A B : finset α) (ha : antichain A) (hb : B ⊆ A) :
  antichain B :=
begin
  intros a ha2 b hb2 hab,
  apply ha a (finset.mem_of_subset hb ha2) b (finset.mem_of_subset hb hb2) hab,
end


def antichain_join (A B : finset α) :
  set α := { a | a ∈ A ∪ B ∧ ∀ b ∈ A ∪ B, a ≤ b → a = b}

variables (A B : finset α) [antichain A] [antichain B]

def antichain.join (A B : finset α):
  finset α := (A ∪ B).filter (λ a, a ∈ antichain_join A B)

def antichain.meet (A B : finset α) : finset α := A ∩ B

theorem join_antichain (A B : finset α) (ha : antichain A) (hb : antichain B) :
  antichain (antichain.join A B) :=
begin
  intros a ha2 b hb2 hle,

  unfold antichain.join at ha2,
  rw finset.mem_filter at ha2,
  rcases ha2 with ⟨hamem, ⟨ha1, ha2⟩⟩,

  unfold antichain.join at hb2,
  rw finset.mem_filter at hb2,
  rcases hb2 with ⟨hbmem, ⟨hb1, hb2⟩⟩,

  apply ha2 b hb1 hle,
end

theorem meet_antichain (A B : finset α) (ha : antichain A) (hb : antichain B) :
  antichain (antichain.meet A B) :=
begin
  intros a ha2 b hb2 hle,
  apply ha a (finset.mem_inter.1 ha2).1 b (finset.mem_inter.1 hb2).1 hle,
end





end
