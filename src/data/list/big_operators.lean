/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel
-/
import data.list.basic

/-!
# Sums and products from lists

This file provides basic results about `list.prod` and `list.sum`, which calculate the product and
sum of elements of a list. These are defined in [`data.list.defs`](./data/list/defs).
-/

variables {ι α β γ : Type*}

namespace list
section monoid
variables [monoid α] {l l₁ l₂ : list α} {a : α}

@[simp, to_additive]
lemma prod_nil : ([] : list α).prod = 1 := rfl

@[to_additive]
lemma prod_singleton : [a].prod = a := one_mul a

@[simp, to_additive]
lemma prod_cons : (a :: l).prod = a * l.prod :=
calc (a :: l).prod = foldl (*) (a * 1) l : by simp only [list.prod, foldl_cons, one_mul, mul_one]
  ... = _ : foldl_assoc

@[simp, to_additive]
lemma prod_append : (l₁ ++ l₂).prod = l₁.prod * l₂.prod :=
calc (l₁ ++ l₂).prod = foldl (*) (foldl (*) 1 l₁ * 1) l₂ : by simp [list.prod]
  ... = l₁.prod * l₂.prod : foldl_assoc

@[to_additive]
lemma prod_concat : (l.concat a).prod = l.prod * a :=
by rw [concat_eq_append, prod_append, prod_cons, prod_nil, mul_one]

@[simp, to_additive]
lemma prod_join {l : list (list α)} : l.join.prod = (l.map list.prod).prod :=
by induction l; [refl, simp only [*, list.join, map, prod_append, prod_cons]]

/-- If zero is an element of a list `L`, then `list.prod L = 0`. If the domain is a nontrivial
monoid with zero with no divisors, then this implication becomes an `iff`, see
`list.prod_eq_zero_iff`. -/
lemma prod_eq_zero {M₀ : Type*} [monoid_with_zero M₀] {L : list M₀} (h : (0 : M₀) ∈ L) :
  L.prod = 0 :=
begin
  induction L with a L ihL,
  { exact absurd h (not_mem_nil _) },
  { rw prod_cons,
    cases (mem_cons_iff _ _ _).1 h with ha hL,
    exacts [mul_eq_zero_of_left ha.symm _, mul_eq_zero_of_right _ (ihL hL)] }
end

/-- Product of elements of a list `L` equals zero if and only if `0 ∈ L`. See also
`list.prod_eq_zero` for an implication that needs weaker typeclass assumptions. -/
@[simp] lemma prod_eq_zero_iff {M₀ : Type*} [monoid_with_zero M₀] [nontrivial M₀]
  [no_zero_divisors M₀] {L : list M₀} :
  L.prod = 0 ↔ (0 : M₀) ∈ L :=
begin
  induction L with a L ihL,
  { simp },
  { rw [prod_cons, mul_eq_zero, ihL, mem_cons_iff, eq_comm] }
end

lemma prod_ne_zero {M₀ : Type*} [monoid_with_zero M₀] [nontrivial M₀] [no_zero_divisors M₀]
  {L : list M₀} (hL : (0 : M₀) ∉ L) : L.prod ≠ 0 :=
mt prod_eq_zero_iff.1 hL

@[to_additive]
lemma prod_eq_foldr : l.prod = foldr (*) 1 l :=
list.rec_on l rfl $ λ a l ihl, by rw [prod_cons, foldr_cons, ihl]

@[to_additive]
lemma prod_hom_rel [monoid β] (l : list ι) {r : α → β → Prop} {f : ι → α} {g : ι → β} (h₁ : r 1 1)
  (h₂ : ∀ ⦃i a b⦄, r a b → r (f i * a) (g i * b)) :
  r (l.map f).prod (l.map g).prod :=
list.rec_on l h₁ (λ a l hl, by simp only [map_cons, prod_cons, h₂ hl])

@[to_additive]
lemma prod_hom [monoid β] (l : list α) (f : α →* β) :
  (l.map f).prod = f l.prod :=
by { simp only [prod, foldl_map, f.map_one.symm],
  exact l.foldl_hom _ _ _ 1 f.map_mul }

@[to_additive]
lemma prod_hom₂ [monoid β] [monoid γ] (l : list ι) (f : α → β → γ)
  (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι → α) (f₂ : ι → β) :
  (l.map $ λ i, f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod :=
begin
  simp only [prod, foldl_map],
  convert l.foldl_hom₂ (λ a b, f a b) _ _ _ _ _ (λ a b i, _),
  { exact hf'.symm },
  { exact hf _ _ _ _ }
end

@[to_additive]
lemma prod_is_unit [monoid β] : Π {L : list β} (u : ∀ m ∈ L, is_unit m), is_unit L.prod
| [] _ := by simp
| (h :: t) u :=
begin
  simp only [list.prod_cons],
  exact is_unit.mul (u h (mem_cons_self h t)) (prod_is_unit (λ m mt, u m (mem_cons_of_mem h mt)))
end

@[simp, to_additive]
lemma prod_take_mul_prod_drop :
  ∀ (L : list α) (i : ℕ), (L.take i).prod * (L.drop i).prod = L.prod
| [] i := by simp
| L 0 := by simp
| (h :: t) (n+1) := by { dsimp, rw [prod_cons, prod_cons, mul_assoc, prod_take_mul_prod_drop] }

@[simp, to_additive]
lemma prod_take_succ :
  ∀ (L : list α) (i : ℕ) (p), (L.take (i + 1)).prod = (L.take i).prod * L.nth_le i p
| [] i p := by cases p
| (h :: t) 0 _ := by simp
| (h :: t) (n+1) _ := by { dsimp, rw [prod_cons, prod_cons, prod_take_succ, mul_assoc] }

/-- A list with product not one must have positive length. -/
@[to_additive]
lemma length_pos_of_prod_ne_one (L : list α) (h : L.prod ≠ 1) : 0 < L.length :=
by { cases L, { simp at h, cases h }, { simp } }

@[to_additive]
lemma prod_update_nth : ∀ (L : list α) (n : ℕ) (a : α),
  (L.update_nth n a).prod =
    (L.take n).prod * (if n < L.length then a else 1) * (L.drop (n + 1)).prod
| (x :: xs) 0     a := by simp [update_nth]
| (x :: xs) (i+1) a := by simp [update_nth, prod_update_nth xs i a, mul_assoc]
| []      _     _ := by simp [update_nth, (nat.zero_le _).not_lt]

open mul_opposite

lemma _root_.mul_opposite.op_list_prod : ∀ (l : list α), op (l.prod) = (l.map op).reverse.prod
| [] := rfl
| (x :: xs) := by rw [list.prod_cons, list.map_cons, list.reverse_cons', list.prod_concat, op_mul,
                      _root_.mul_opposite.op_list_prod]

lemma _root_.mul_opposite.unop_list_prod (l : list αᵐᵒᵖ) :
  (l.prod).unop = (l.map unop).reverse.prod :=
by rw [← op_inj, op_unop, mul_opposite.op_list_prod, map_reverse, map_map, reverse_reverse,
  op_comp_unop, map_id]

end monoid

section group
variables [group α]

/-- This is the `list.prod` version of `mul_inv_rev` -/
@[to_additive "This is the `list.sum` version of `add_neg_rev`"]
lemma prod_inv_reverse : ∀ (L : list α), L.prod⁻¹ = (L.map (λ x, x⁻¹)).reverse.prod
| [] := by simp
| (x :: xs) := by simp [prod_inv_reverse xs]

/-- A non-commutative variant of `list.prod_reverse` -/
@[to_additive "A non-commutative variant of `list.sum_reverse`"]
lemma prod_reverse_noncomm : ∀ (L : list α), L.reverse.prod = (L.map (λ x, x⁻¹)).prod⁻¹ :=
by simp [prod_inv_reverse]

/-- Counterpart to `list.prod_take_succ` when we have an inverse operation -/
@[simp, to_additive /-"Counterpart to `list.sum_take_succ` when we have an negation operation"-/]
lemma prod_drop_succ :
  ∀ (L : list α) (i : ℕ) (p), (L.drop (i + 1)).prod = (L.nth_le i p)⁻¹ * (L.drop i).prod
| [] i p := false.elim (nat.not_lt_zero _ p)
| (x :: xs) 0 p := by simp
| (x :: xs) (i + 1) p := prod_drop_succ xs i _

end group

section comm_group
variables [comm_group α]

/-- This is the `list.prod` version of `mul_inv` -/
@[to_additive "This is the `list.sum` version of `add_neg`"]
lemma prod_inv : ∀ (L : list α), L.prod⁻¹ = (L.map (λ x, x⁻¹)).prod
| [] := by simp
| (x :: xs) := by simp [mul_comm, prod_inv xs]

/-- Alternative version of `list.prod_update_nth` when the list is over a group -/
@[to_additive /-"Alternative version of `list.sum_update_nth` when the list is over a group"-/]
lemma prod_update_nth' (L : list α) (n : ℕ) (a : α) :
  (L.update_nth n a).prod =
    L.prod * (if hn : n < L.length then (L.nth_le n hn)⁻¹ * a else 1) :=
begin
  refine (prod_update_nth L n a).trans _,
  split_ifs with hn hn,
  { rw [mul_comm _ a, mul_assoc a, prod_drop_succ L n hn, mul_comm _ (drop n L).prod,
      ← mul_assoc (take n L).prod, prod_take_mul_prod_drop, mul_comm a, mul_assoc] },
  { simp only [take_all_of_le (le_of_not_lt hn), prod_nil, mul_one,
      drop_eq_nil_of_le ((le_of_not_lt hn).trans n.le_succ)] }
end

end comm_group

lemma eq_of_sum_take_eq [add_left_cancel_monoid α] {L L' : list α} (h : L.length = L'.length)
  (h' : ∀ i ≤ L.length, (L.take i).sum = (L'.take i).sum) : L = L' :=
begin
  apply ext_le h (λ i h₁ h₂, _),
  have : (L.take (i + 1)).sum = (L'.take (i + 1)).sum := h' _ (nat.succ_le_of_lt h₁),
  rw [sum_take_succ L i h₁, sum_take_succ L' i h₂, h' i (le_of_lt h₁)] at this,
  exact add_left_cancel this
end

lemma monotone_sum_take [canonically_ordered_add_monoid α] (L : list α) :
  monotone (λ i, (L.take i).sum) :=
begin
  apply monotone_nat_of_le_succ (λ n, _),
  by_cases h : n < L.length,
  { rw sum_take_succ _ _ h,
    exact le_self_add },
  { push_neg at h,
    simp [take_all_of_le h, take_all_of_le (le_trans h (nat.le_succ _))] }
end

@[to_additive sum_nonneg]
lemma one_le_prod_of_one_le [ordered_comm_monoid α] {l : list α} (hl₁ : ∀ x ∈ l, (1 : α) ≤ x) :
  1 ≤ l.prod :=
begin
  induction l with hd tl ih,
  { simp },
  rw prod_cons,
  exact one_le_mul (hl₁ hd (mem_cons_self hd tl)) (ih (λ x h, hl₁ x (mem_cons_of_mem hd h))),
end

@[to_additive sum_pos]
lemma one_lt_prod_of_one_lt [ordered_comm_monoid α] :
  ∀ (l : list α) (hl : ∀ x ∈ l, (1 : α) < x) (hl₂ : l ≠ []), 1 < l.prod
| [] _ h := (h rfl).elim
| [b] h _ := by simpa using h
| (a :: b :: l) hl₁ hl₂ :=
begin
  simp only [forall_eq_or_imp, list.mem_cons_iff _ a] at hl₁,
  rw list.prod_cons,
  apply one_lt_mul_of_lt_of_le' hl₁.1,
  apply le_of_lt ((b :: l).one_lt_prod_of_one_lt hl₁.2 (l.cons_ne_nil b)),
end
@[to_additive]
lemma single_le_prod [ordered_comm_monoid α] {l : list α} (hl₁ : ∀ x ∈ l, (1 : α) ≤ x) :
  ∀ x ∈ l, x ≤ l.prod :=
begin
  induction l,
  { simp },
  simp_rw [prod_cons, forall_mem_cons] at ⊢ hl₁,
  split,
  { exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2) },
  { exact λ x H, le_mul_of_one_le_of_le hl₁.1 (l_ih hl₁.right x H) },
end

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
lemma all_one_of_le_one_le_of_prod_eq_one [ordered_comm_monoid α]
  {l : list α} (hl₁ : ∀ x ∈ l, (1 : α) ≤ x) (hl₂ : l.prod = 1) {x : α} (hx : x ∈ l) :
  x = 1 :=
le_antisymm (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)

lemma sum_eq_zero_iff [canonically_ordered_add_monoid α] (l : list α) :
  l.sum = 0 ↔ ∀ x ∈ l, x = (0 : α) :=
⟨all_zero_of_le_zero_le_of_sum_eq_zero (λ _ _, zero_le _),
begin
  induction l,
  { simp },
  { intro h,
    rw [sum_cons, add_eq_zero_iff],
    rw forall_mem_cons at h,
    exact ⟨h.1, l_ih h.2⟩ },
end⟩

/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
lemma length_le_sum_of_one_le (L : list ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.sum :=
begin
  induction L with j L IH h, { simp },
  rw [sum_cons, length, add_comm],
  exact add_le_add (h _ (set.mem_insert _ _)) (IH (λ i hi, h i (set.mem_union_right _ hi)))
end

/-- A list with positive sum must have positive length. -/
-- This is an easy consequence of `length_pos_of_sum_ne_zero`, but often useful in applications.
lemma length_pos_of_sum_pos [ordered_cancel_add_comm_monoid α] (L : list α) (h : 0 < L.sum) :
  0 < L.length :=
length_pos_of_sum_ne_zero L h.ne'

-- TODO: develop theory of tropical rings
lemma sum_le_foldr_max [add_monoid α] [add_monoid β] [linear_order β] (f : α → β)
  (h0 : f 0 ≤ 0) (hadd : ∀ x y, f (x + y) ≤ max (f x) (f y)) (l : list α) :
  f l.sum ≤ (l.map f).foldr max 0 :=
begin
  induction l with hd tl IH,
  { simpa using h0 },
  simp only [list.sum_cons, list.foldr_map, le_max_iff, list.foldr] at IH ⊢,
  cases le_or_lt (f tl.sum) (f hd),
  { left,
    refine (hadd _ _).trans _,
    simpa using h },
  { right,
    refine (hadd _ _).trans _,
    simp only [IH, max_le_iff, and_true, h.le.trans IH] }
end

@[simp, to_additive]
lemma prod_erase [decidable_eq α] [comm_monoid α] {a} :
  ∀ {l : list α}, a ∈ l → a * (l.erase a).prod = l.prod
| (b :: l) h :=
  begin
    obtain rfl | ⟨ne, h⟩ := decidable.list.eq_or_ne_mem_of_mem h,
    { simp only [list.erase, if_pos, prod_cons] },
    { simp only [list.erase, if_neg (mt eq.symm ne), prod_cons, prod_erase h, mul_left_comm a b] }
  end

lemma dvd_prod [comm_monoid α] {a} {l : list α} (ha : a ∈ l) : a ∣ l.prod :=
let ⟨s, t, h⟩ := mem_split ha in
by { rw [h, prod_append, prod_cons, mul_left_comm], exact dvd_mul_right _ _ }

@[simp] lemma sum_const_nat (m n : ℕ) : sum (list.repeat m n) = m * n :=
by induction n; [refl, simp only [*, repeat_succ, sum_cons, nat.mul_succ, add_comm]]

lemma dvd_sum [comm_semiring α] {a} {l : list α} (h : ∀ x ∈ l, a ∣ x) : a ∣ l.sum :=
begin
  induction l with x l ih,
  { exact dvd_zero _ },
  { rw [list.sum_cons],
    exact dvd_add (h _ (mem_cons_self _ _)) (ih (λ x hx, h x (mem_cons_of_mem _ hx))) }
end

lemma exists_lt_of_sum_lt [linear_ordered_cancel_add_comm_monoid β] {l : list α} (f g : α → β)
  (h : (l.map f).sum < (l.map g).sum) :
  ∃ x ∈ l, f x < g x :=
begin
  induction l with x l,
  { exact (lt_irrefl _ h).elim },
  obtain h' | h' := lt_or_le (f x) (g x),
  { exact ⟨x, mem_cons_self _ _, h'⟩ },
  simp at h,
  obtain ⟨y, h1y, h2y⟩ := l_ih (lt_of_add_lt_add_left (h.trans_le $ add_le_add_right h' _)),
  exact ⟨y, mem_cons_of_mem x h1y, h2y⟩,
end

lemma exists_le_of_sum_le [linear_ordered_cancel_add_comm_monoid β] {l : list α} (hl : l ≠ [])
  (f g : α → β) (h : (l.map f).sum ≤ (l.map g).sum) :
  ∃ x ∈ l, f x ≤ g x :=
begin
  cases l with x l,
  { contradiction },
  obtain h' | h' := le_or_lt (f x) (g x),
  { exact ⟨x, mem_cons_self _ _, h'⟩ },
  obtain ⟨y, h1y, h2y⟩ := exists_lt_of_sum_lt f g _,
  exact ⟨y, mem_cons_of_mem x h1y, le_of_lt h2y⟩, simp at h,
  exact lt_of_add_lt_add_left (h.trans_lt $ add_lt_add_right h' _),
end

/-- We'd like to state this as `L.head * L.tail.prod = L.prod`, but because `L.head` relies on an
inhabited instance to return a garbage value on the empty list, this is not possible.
Instead, we write the statement in terms of `(L.nth 0).get_or_else 1` and state the lemma for `ℕ` as
 -/
@[to_additive]
lemma nth_zero_mul_tail_prod [monoid α] (l : list α) :
  (l.nth 0).get_or_else 1 * l.tail.prod = l.prod :=
by cases l; simp

/-- Same as `nth_zero_mul_tail_prod`, but avoiding the `list.head` garbage complication by requiring
the list to be nonempty. -/
@[to_additive]
lemma head_mul_tail_prod_of_ne_nil [monoid α] [inhabited α] (l : list α) (h : l ≠ []) :
  l.head * l.tail.prod = l.prod :=
by cases l; [contradiction, simp]

/-- The product of a list of positive natural numbers is positive,
and likewise for any nontrivial ordered semiring. -/
lemma prod_pos [ordered_semiring α] [nontrivial α] (l : list α) (h : ∀ a ∈ l, (0 : α) < a) :
  0 < l.prod :=
begin
  induction l with a l ih,
  { simp },
  { rw prod_cons,
    exact mul_pos (h _ $ mem_cons_self _ _) (ih $ λ a ha, h a $ mem_cons_of_mem _ ha) }
end

/-!
Several lemmas about sum/head/tail for `list ℕ`.
These are hard to generalize well, as they rely on the fact that `default ℕ = 0`.
If desired, we could add a class stating that `default α = 0`.
-/

/-- This relies on `default ℕ = 0`. -/
lemma head_add_tail_sum (L : list ℕ) : L.head + L.tail.sum = L.sum :=
by { cases L, { simp, refl }, { simp } }

/-- This relies on `default ℕ = 0`. -/
lemma head_le_sum (L : list ℕ) : L.head ≤ L.sum := nat.le.intro (head_add_tail_sum L)

/-- This relies on `default ℕ = 0`. -/
lemma tail_sum (L : list ℕ) : L.tail.sum = L.sum - L.head :=
by rw [← head_add_tail_sum L, add_comm, add_tsub_cancel_right]

section alternating
variables {G : Type*} [comm_group G]

@[simp, to_additive] lemma alternating_prod_nil : alternating_prod ([] : list G) = 1 := rfl

@[simp, to_additive] lemma alternating_prod_singleton (g : G) : alternating_prod [g] = g := rfl

@[simp, to_additive alternating_sum_cons_cons']
lemma alternating_prod_cons_cons (g h : G) (l : list G) :
  alternating_prod (g :: h :: l) = g * h⁻¹ * alternating_prod l := rfl

lemma alternating_sum_cons_cons {G : Type*} [add_comm_group G] (g h : G) (l : list G) :
  alternating_sum (g :: h :: l) = g - h + alternating_sum l :=
by rw [sub_eq_add_neg, alternating_sum]

end alternating

@[to_additive]
lemma _root_.monoid_hom.map_list_prod [monoid α] [monoid β] (f : α →* β) (l : list α) :
  f l.prod = (l.map f).prod :=
(l.prod_hom f).symm

open mul_opposite

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements -/
lemma _root_.monoid_hom.unop_map_list_prod {α β : Type*} [monoid α] [monoid β] (f : α →* βᵐᵒᵖ)
  (l : list α) :
  unop (f l.prod) = (l.map (unop ∘ f)).reverse.prod :=
by rw [f.map_list_prod l, unop_list_prod, list.map_map]

@[to_additive]
lemma prod_map_hom [monoid β] [monoid γ] (L : list α) (f : α → β) (g : β →* γ) :
  (L.map (g ∘ f)).prod = g ((L.map f).prod) :=
by {rw g.map_list_prod, exact congr_arg _ (map_map _ _ _).symm}

lemma sum_map_mul_left [semiring α] (L : list β) (f : β → α) (r : α) :
  (L.map (λ b, r * f b)).sum = r * (L.map f).sum :=
sum_map_hom L f $ add_monoid_hom.mul_left r

lemma sum_map_mul_right [semiring α] (L : list β) (f : β → α) (r : α) :
  (L.map (λ b, f b * r)).sum = (L.map f).sum * r :=
sum_map_hom L f $ add_monoid_hom.mul_right r

end list
