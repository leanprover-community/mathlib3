/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark.
-/
import algebra.big_operators

/-!
# Bigraphs
This file gives a basic theory of bigraphs suitable for simple double counting arguments.

## Implementation notes
We considered extending `rel`. On a cursory inspection,
it didn't seem like any of the API we provide overlapped with the API `rel` provides.

We use `uncurried` under the hood to think of the data of a bigraph as a set of ordered pairs.
`uncurried` should generally not appear in expressions in simp-normal form.
-/
open_locale classical big_operators
noncomputable theory

universes u v
variables (α : Type u) (β : Type v)

@[ext] structure bigraph :=
(left_carrier : finset α)
(right_carrier : finset β)
(adj : α → β → Prop)

variables {α} {β} (G : bigraph α β)

namespace bigraph

def uncurried : (α × β) → Prop := function.uncurry (G.adj)

@[simp] lemma uncurried_apply (x : α × β) : (uncurried G) x = G.adj x.fst x.snd:=
by rw [uncurried, function.uncurry]

def swap_inputs (E : α → β → Prop) : β → α → Prop :=
  function.curry ((function.uncurry E) ∘ prod.swap)

@[simp] lemma swap_inputs' (E : α → β → Prop) (a : α) (b : β) :
  swap_inputs E b a = E a b:=
by simp [swap_inputs, function.uncurry, function.curry]

@[simp] lemma swap_inputs_invol (E : α → β → Prop):
  swap_inputs (swap_inputs E)=E:=
by ext; simp

def swap : bigraph β α :=
{ left_carrier:= G.right_carrier,
  right_carrier := G.left_carrier,
  adj := swap_inputs G.adj }

@[simp] lemma left_carrier_swap : G.swap.left_carrier= G.right_carrier := rfl

@[simp] lemma right_carrier_swap : G.swap.right_carrier = G.left_carrier := rfl

@[simp] lemma adj_swap : G.swap.adj = swap_inputs G.adj := rfl

@[simp] lemma swap_swap : G.swap.swap = G := by ext; simp [swap]

def edges : finset (α × β) := finset.filter (uncurried G) (finset.product G.left_carrier G.right_carrier)

-- i think mem_edges_iff is a more standard name in the library? not sure.
@[simp] lemma mem_edges (x : α × β) : x ∈ edges G ↔ (x.fst ∈ G.left_carrier ∧ x.snd ∈ G.right_carrier) ∧ G.adj x.fst x.snd :=
by { unfold edges, simp }

def card_edges : ℕ := (edges G).card

lemma mem_edges_swap (x : β × α) :
  x ∈ edges G.swap ↔ x.swap ∈ edges G := by { simp, tauto }

lemma edges_swap : edges G.swap = finset.image prod.swap (edges G) :=
begin
  ext, rw [finset.mem_image, mem_edges_swap],
  split, { intro h1, use [a.swap, h1], simp },
  rintro ⟨ _, _, rfl⟩, rwa prod.swap_swap,
end

@[simp]
lemma card_edges_symm (G : bigraph α β) : card_edges G.swap = card_edges G :=
begin
  change (edges (swap G)).card = (edges G).card,
  apply nat.le_antisymm,
  { rw edges_swap, apply finset.card_image_le },
  convert finset.card_image_le, rotate 2, { exact prod.swap },
  rw ← edges_swap, simp,
end

def left_fiber (b : β) : finset α :=
  finset.filter (λ (a1:α), (uncurried G) (a1, b)) G.left_carrier

def right_fiber (a : α) : finset β :=
  finset.filter (λ (b1 : β), (uncurried G) (a, b1)) G.right_carrier

def left_fiber' (b : β) : finset (α × β) := finset.image (λ a:α, (a,b)) (left_fiber G b)

def right_fiber' (a : α) : finset (α × β) := finset.image (λ b:β, (a,b)) (right_fiber G a)

@[simp] lemma mem_left_fiber (b : β) {x : α} :
x ∈ (left_fiber G b) ↔ x ∈ G.left_carrier ∧ G.adj x b := by { unfold left_fiber, simp }

@[simp] lemma mem_right_fiber (a : α) {x : β} :
x ∈ (right_fiber G a) ↔ x ∈ G.right_carrier ∧ G.adj a x := by { unfold right_fiber, simp }

@[simp] lemma left_fiber_swap (a : α) :
left_fiber G.swap a = right_fiber G a := by { ext, simp }

@[simp] lemma right_fiber_swap (b : β) :
right_fiber G.swap b = left_fiber G b := by { ext, simp }

@[simp] lemma mem_left_fiber' (b : β) (x : α × β) :
x ∈ (left_fiber' G b) ↔ (x.fst ∈ G.left_carrier ∧ x.snd = b) ∧ G.adj x.fst x.snd :=
by rw left_fiber'; tidy

-- can the following be proven with swap and the above?
@[simp] lemma mem_right_fiber' (a : α) (x : α × β) :
x ∈ (right_fiber' G a) ↔ (x.fst = a ∧ x.snd ∈ G.right_carrier) ∧ G.adj x.fst x.snd :=
by rw right_fiber'; tidy

-- i'm now confused about the properties of our simp normal form.
-- Do we always want to get swap out of G.swap?
@[simp] lemma left_fiber'_swap (a : α) :
left_fiber' G.swap a = finset.image prod.swap (right_fiber' G a) :=
begin
  have h : right_fiber' G a = finset.image (prod.mk a) (right_fiber G a) := rfl,
  rw [h, finset.image_image],
  have h2 : left_fiber' G.swap a = finset.image (λ b:β,(b,a)) (left_fiber G.swap a) := rfl,
  simp [h2]; refl,
end

@[simp] lemma right_fiber'_swap (b : β):
  right_fiber' G.swap b = finset.image prod.swap (left_fiber' G b):=
by rw [left_fiber', finset.image_image, right_fiber', right_fiber_swap]; refl

@[simp] lemma card_left_fiber_eq_card_left_fiber' (b : β) :
  (left_fiber G b).card = (left_fiber' G b).card :=
by { symmetry, apply finset.card_image_of_injective, intros _ _, simp }

lemma disjoint_left_fiber' {b1 b2 : β} (h : b1 ≠ b2):
  disjoint (left_fiber' G b1) (left_fiber' G b2):=
begin
  rw finset.disjoint_iff_inter_eq_empty, ext,
  simp only [and_imp, finset.not_mem_empty, mem_left_fiber', not_and, iff_false, finset.mem_inter],
  rintros _ rfl _ _ _, contradiction,
end

-- is this a useful simp lemma if reversed?
lemma edges_eq_bind_left_fibers :
  edges G = (G.right_carrier).bind (λ (b : β), left_fiber' G b) :=
begin
  ext, simp only [exists_prop, mem_left_fiber', mem_edges, finset.mem_bind],
  split, { rw and_imp, intros, use a.snd, tauto },
  simp only [and_imp, exists_imp_distrib],
  rintros _ _ _ rfl, tauto,
end

lemma edges_eq_bind_right_fibers :
  edges G = (G.left_carrier).bind (λ (a : α), right_fiber' G a):=
begin
  rw [← swap_swap G, edges_swap, edges_eq_bind_left_fibers, finset.bind_image],
  simp only [right_carrier_swap, swap_swap, left_fiber'_swap],
  congr, ext, rw [finset.image_image, prod.swap_swap_eq, finset.image_id],
end

theorem sum_left_fibers :
  card_edges G = ∑ b in G.right_carrier, (left_fiber G b).card :=
begin
  rw card_edges,
  convert finset.card_bind _,
  swap, { simp }, { simp [edges_eq_bind_left_fibers] }, { apply_instance },
  intros _ _ _ _ h, exact disjoint_left_fiber' _ h,
end

theorem sum_right_fibers :
  card_edges G = ∑ a in G.left_carrier, (right_fiber G a).card :=
by { simp_rw ← left_fiber_swap, rw ← card_edges_symm, apply sum_left_fibers }

def left_regular (d : ℕ) : Prop :=
  ∀ b ∈ G.right_carrier, (left_fiber G b).card = d

def right_regular (d : ℕ) : Prop :=
  ∀ a ∈ G.left_carrier, (right_fiber G a).card = d

def left_unique : Prop :=
  ∀ b ∈ G.right_carrier, ∃!(a : α), a ∈ G.left_carrier ∧ G.adj a b

def right_unique : Prop :=
  ∀ a ∈ G.left_carrier, ∃!(b : β), b ∈ G.right_carrier ∧ G.adj a b

@[simp] lemma right_regular_swap (d : ℕ) : right_regular G.swap d ↔ left_regular G d :=
by simp [left_regular, right_regular]

@[simp] lemma left_regular_swap (d : ℕ) : left_regular G.swap d ↔ right_regular G d :=
by simp [left_regular, right_regular]

@[simp] lemma right_unique_swap : right_unique G.swap ↔ left_unique G :=
by simp [left_unique, right_unique]

@[simp] lemma left_unique_swap : left_unique G.swap ↔ right_unique G :=
by simp [left_unique, right_unique]

@[simp] lemma left_unique_one_reg : left_unique G ↔ left_regular G 1 :=
begin
  apply forall_congr, intro, apply imp_congr_right,
  simp_rw [finset.card_eq_one], simp [finset.singleton_iff_unique_mem],
end

@[simp] lemma right_unique_one_reg : right_unique G ↔ right_regular G 1 :=
by rw [← left_unique_swap, ← left_regular_swap]; apply left_unique_one_reg

theorem card_edges_of_lreg {l : ℕ} (hl : left_regular G l) : card_edges G = l * G.right_carrier.card:=
by rwa [sum_left_fibers, mul_comm l, finset.sum_const_nat]

theorem card_edges_of_rreg {r : ℕ} (hr : right_regular G r) : card_edges G = r * G.left_carrier.card :=
by rwa [sum_right_fibers, mul_comm r, finset.sum_const_nat]

theorem card_edges_of_lunique (h : left_unique G) : card_edges G = G.right_carrier.card :=
by { rw left_unique_one_reg at h, convert card_edges_of_lreg _ h, simp }

theorem card_edges_of_runique (h : right_unique G) : card_edges G = G.left_carrier.card :=
by { rw right_unique_one_reg at h, convert card_edges_of_rreg _ h, simp }

theorem double_count_of_lreg_rreg {l r : ℕ} (hl : left_regular G l) (hr : right_regular G r) :
r * G.left_carrier.card = l * G.right_carrier.card :=
by rwa [← card_edges_of_rreg _ hr, ← card_edges_of_lreg]

theorem card_eq_of_lunique_runique (hl : left_unique G) (hr : right_unique G ) :
G.left_carrier.card = G.right_carrier.card :=
begin
  rw right_unique_one_reg at hr, rw left_unique_one_reg at hl,
  convert double_count_of_lreg_rreg _ hl hr; simp,
end
variables (adj : α → β → Prop) (A : finset α) {B1 B2 : finset β}
-- The following lemmas may be generalized by saying stuff about lattice homormopshims.

lemma edges_disjoint_of_eq_disj_eq (hB : disjoint B1 B2) :
  disjoint (edges ⟨A, B1, adj⟩) (edges ⟨A, B2, adj⟩) :=
begin
  apply finset.disjoint_filter_filter, rw finset.disjoint_iff_ne,
  rintros a _ _ _ rfl,
  rw finset.mem_product at *, rw finset.disjoint_iff_ne at hB,
  apply hB a.snd _ a.snd; tauto,
end

lemma edges_union {A : finset α} {B1 B2 : finset β} :
  edges ⟨ A, B1 ∪ B2, adj⟩ = edges ⟨A, B1, adj⟩ ∪ edges ⟨A, B2, adj⟩ :=
begin
  erw ← finset.filter_union,
  suffices : A.product (B1 ∪ B2) = A.product B1 ∪ A.product B2, { rw ← this, refl },
  ext, simp [ finset.mem_union, finset.mem_product]; tauto,
end

theorem card_edges_add_of_eq_disj_union_eq {A : finset α} {B1 B2 : finset β} (h : disjoint B1 B2) :
card_edges ⟨A, B1 ∪ B2, adj⟩ = card_edges ⟨A, B1, adj⟩ + card_edges ⟨A, B2, adj⟩ :=
by { rw [card_edges, edges_union], simp [edges_disjoint_of_eq_disj_eq, h], refl }

end bigraph
