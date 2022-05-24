/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
import algebra.group_power
import data.list.forall2

/-!
# Sums and products from lists

This file provides basic results about `list.prod`, `list.sum`, which calculate the product and sum
of elements of a list and `list.alternating_prod`, `list.alternating_sum`, their alternating
counterparts. These are defined in [`data.list.defs`](./defs).
-/

variables {ι α M N P M₀ G R : Type*}

namespace list
section monoid
variables [monoid M] [monoid N] [monoid P] {l l₁ l₂ : list M} {a : M}

@[simp, to_additive]
lemma prod_nil : ([] : list M).prod = 1 := rfl

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
by rw [concat_eq_append, prod_append, prod_singleton]

@[simp, to_additive]
lemma prod_join {l : list (list M)} : l.join.prod = (l.map list.prod).prod :=
by induction l; [refl, simp only [*, list.join, map, prod_append, prod_cons]]

@[to_additive]
lemma prod_eq_foldr : l.prod = foldr (*) 1 l :=
list.rec_on l rfl $ λ a l ihl, by rw [prod_cons, foldr_cons, ihl]

@[simp, priority 500, to_additive]
theorem prod_repeat (a : M) (n : ℕ) : (repeat a n).prod = a ^ n :=
begin
  induction n with n ih,
  { rw pow_zero, refl },
  { rw [list.repeat_succ, list.prod_cons, ih, pow_succ] }
end

@[to_additive sum_eq_card_nsmul]
lemma prod_eq_pow_card (l : list M) (m : M) (h : ∀ (x ∈ l), x = m) :
  l.prod = m ^ l.length :=
by rw [← prod_repeat, ← list.eq_repeat.mpr ⟨rfl, h⟩]

@[to_additive]
lemma prod_hom_rel (l : list ι) {r : M → N → Prop} {f : ι → M} {g : ι → N} (h₁ : r 1 1)
  (h₂ : ∀ ⦃i a b⦄, r a b → r (f i * a) (g i * b)) :
  r (l.map f).prod (l.map g).prod :=
list.rec_on l h₁ (λ a l hl, by simp only [map_cons, prod_cons, h₂ hl])

@[to_additive]
lemma prod_hom (l : list M) {F : Type*} [monoid_hom_class F M N] (f : F) :
  (l.map f).prod = f l.prod :=
by { simp only [prod, foldl_map, ← map_one f],
  exact l.foldl_hom _ _ _ 1 (map_mul f) }

@[to_additive]
lemma prod_hom₂ (l : list ι) (f : M → N → P)
  (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι → M) (f₂ : ι → N) :
  (l.map $ λ i, f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod :=
begin
  simp only [prod, foldl_map],
  convert l.foldl_hom₂ (λ a b, f a b) _ _ _ _ _ (λ a b i, _),
  { exact hf'.symm },
  { exact hf _ _ _ _ }
end

@[simp, to_additive]
lemma prod_map_mul {α : Type*} [comm_monoid α] {l : list ι} {f g : ι → α} :
  (l.map $ λ i, f i * g i).prod = (l.map f).prod * (l.map g).prod :=
l.prod_hom₂ (*) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]
lemma prod_map_hom (L : list ι) (f : ι → M) {G : Type*} [monoid_hom_class G M N] (g : G) :
  (L.map (g ∘ f)).prod = g ((L.map f).prod) :=
by rw [← prod_hom, map_map]

@[to_additive]
lemma prod_is_unit : Π {L : list M} (u : ∀ m ∈ L, is_unit m), is_unit L.prod
| [] _ := by simp
| (h :: t) u :=
begin
  simp only [list.prod_cons],
  exact is_unit.mul (u h (mem_cons_self h t)) (prod_is_unit (λ m mt, u m (mem_cons_of_mem h mt)))
end

@[simp, to_additive]
lemma prod_take_mul_prod_drop :
  ∀ (L : list M) (i : ℕ), (L.take i).prod * (L.drop i).prod = L.prod
| [] i := by simp
| L 0 := by simp
| (h :: t) (n+1) := by { dsimp, rw [prod_cons, prod_cons, mul_assoc, prod_take_mul_prod_drop] }

@[simp, to_additive]
lemma prod_take_succ :
  ∀ (L : list M) (i : ℕ) (p), (L.take (i + 1)).prod = (L.take i).prod * L.nth_le i p
| [] i p := by cases p
| (h :: t) 0 _ := by simp
| (h :: t) (n+1) _ := by { dsimp, rw [prod_cons, prod_cons, prod_take_succ, mul_assoc] }

/-- A list with product not one must have positive length. -/
@[to_additive "A list with sum not zero must have positive length."]
lemma length_pos_of_prod_ne_one (L : list M) (h : L.prod ≠ 1) : 0 < L.length :=
by { cases L, { contrapose h, simp }, { simp } }

/-- A list with product greater than one must have positive length. -/
@[to_additive length_pos_of_sum_pos "A list with positive sum must have positive length."]
lemma length_pos_of_one_lt_prod [preorder M] (L : list M) (h : 1 < L.prod) :
  0 < L.length :=
length_pos_of_prod_ne_one L h.ne'

/-- A list with product less than one must have positive length. -/
@[to_additive "A list with negative sum must have positive length."]
lemma length_pos_of_prod_lt_one [preorder M] (L : list M) (h : L.prod < 1) :
  0 < L.length :=
length_pos_of_prod_ne_one L h.ne

@[to_additive]
lemma prod_update_nth : ∀ (L : list M) (n : ℕ) (a : M),
  (L.update_nth n a).prod =
    (L.take n).prod * (if n < L.length then a else 1) * (L.drop (n + 1)).prod
| (x :: xs) 0     a := by simp [update_nth]
| (x :: xs) (i+1) a := by simp [update_nth, prod_update_nth xs i a, mul_assoc]
| []      _     _ := by simp [update_nth, (nat.zero_le _).not_lt]

open mul_opposite

/-- We'd like to state this as `L.head * L.tail.prod = L.prod`, but because `L.head` relies on an
inhabited instance to return a garbage value on the empty list, this is not possible.
Instead, we write the statement in terms of `(L.nth 0).get_or_else 1`.
-/
@[to_additive "We'd like to state this as `L.head + L.tail.sum = L.sum`, but because `L.head`
relies on an inhabited instance to return a garbage value on the empty list, this is not possible.
Instead, we write the statement in terms of `(L.nth 0).get_or_else 0`."]
lemma nth_zero_mul_tail_prod (l : list M) : (l.nth 0).get_or_else 1 * l.tail.prod = l.prod :=
by cases l; simp

/-- Same as `nth_zero_mul_tail_prod`, but avoiding the `list.head` garbage complication by requiring
the list to be nonempty. -/
@[to_additive "Same as `nth_zero_add_tail_sum`, but avoiding the `list.head` garbage complication
by requiring the list to be nonempty."]
lemma head_mul_tail_prod_of_ne_nil [inhabited M] (l : list M) (h : l ≠ []) :
  l.head * l.tail.prod = l.prod :=
by cases l; [contradiction, simp]

@[to_additive]
lemma _root_.commute.list_prod_right (l : list M) (y : M) (h : ∀ (x ∈ l), commute y x) :
  commute y l.prod :=
begin
  induction l with z l IH,
  { simp },
  { rw list.ball_cons at h,
    rw list.prod_cons,
    exact commute.mul_right h.1 (IH h.2), }
end

@[to_additive]
lemma _root_.commute.list_prod_left (l : list M) (y : M) (h : ∀ (x ∈ l), commute x y) :
  commute l.prod y  :=
(commute.list_prod_right _ _ $ λ x hx, (h _ hx).symm).symm

lemma _root_.commute.list_sum_right [non_unital_non_assoc_semiring R] (a : R) (l : list R)
  (h : ∀ b ∈ l, commute a b) :
  commute a l.sum :=
begin
  induction l with x xs ih,
  { exact commute.zero_right _, },
  { rw sum_cons,
    exact (h _ $ mem_cons_self _ _).add_right (ih $ λ j hj, h _ $ mem_cons_of_mem _ hj) }
end

lemma _root_.commute.list_sum_left [non_unital_non_assoc_semiring R] (b : R) (l : list R)
  (h : ∀ a ∈ l, commute a b) :
  commute l.sum b :=
(commute.list_sum_right _ _ $ λ x hx, (h _ hx).symm).symm

@[to_additive sum_le_sum] lemma forall₂.prod_le_prod' [preorder M]
  [covariant_class M M (function.swap (*)) (≤)] [covariant_class M M (*) (≤)]
  {l₁ l₂ : list M} (h : forall₂ (≤) l₁ l₂) : l₁.prod ≤ l₂.prod :=
begin
  induction h with a b la lb hab ih ih',
  { refl },
  { simpa only [prod_cons] using mul_le_mul' hab ih' }
end

/-- If `l₁` is a sublist of `l₂` and all elements of `l₂` are greater than or equal to one, then
`l₁.prod ≤ l₂.prod`. One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 1 ≤ a` instead
of `∀ a ∈ l₂, 1 ≤ a` but this lemma is not yet in `mathlib`. -/
@[to_additive sum_le_sum "If `l₁` is a sublist of `l₂` and all elements of `l₂` are nonnegative,
then `l₁.sum ≤ l₂.sum`. One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 0 ≤ a` instead
of `∀ a ∈ l₂, 0 ≤ a` but this lemma is not yet in `mathlib`."]
lemma sublist.prod_le_prod' [preorder M] [covariant_class M M (function.swap (*)) (≤)]
  [covariant_class M M (*) (≤)] {l₁ l₂ : list M} (h : l₁ <+ l₂) (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) :
  l₁.prod ≤ l₂.prod :=
begin
  induction h, { refl },
  case cons : l₁ l₂ a ih ih'
  { simp only [prod_cons, forall_mem_cons] at h₁ ⊢,
    exact (ih' h₁.2).trans (le_mul_of_one_le_left' h₁.1) },
  case cons2 : l₁ l₂ a ih ih'
  { simp only [prod_cons, forall_mem_cons] at h₁ ⊢,
    exact mul_le_mul_left' (ih' h₁.2) _ }
end

@[to_additive sum_le_sum] lemma sublist_forall₂.prod_le_prod' [preorder M]
  [covariant_class M M (function.swap (*)) (≤)] [covariant_class M M (*) (≤)]
  {l₁ l₂ : list M} (h : sublist_forall₂ (≤) l₁ l₂) (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) :
  l₁.prod ≤ l₂.prod :=
let ⟨l, hall, hsub⟩ := sublist_forall₂_iff.1 h
in hall.prod_le_prod'.trans $ hsub.prod_le_prod' h₁

@[to_additive sum_le_sum] lemma prod_le_prod' [preorder M]
  [covariant_class M M (function.swap (*)) (≤)] [covariant_class M M (*) (≤)]
  {l : list ι} {f g : ι → M} (h : ∀ i ∈ l, f i ≤ g i) :
  (l.map f).prod ≤ (l.map g).prod :=
forall₂.prod_le_prod' $ by simpa

@[to_additive sum_lt_sum] lemma prod_lt_prod'
  [preorder M] [covariant_class M M (*) (<)] [covariant_class M M (*) (≤)]
  [covariant_class M M (function.swap (*)) (<)] [covariant_class M M (function.swap (*)) (≤)]
  {l : list ι} (f g : ι → M) (h₁ : ∀ i ∈ l, f i ≤ g i) (h₂ : ∃ i ∈ l, f i < g i) :
  (l.map f).prod < (l.map g).prod :=
begin
  induction l with i l ihl, { rcases h₂ with ⟨_, ⟨⟩, _⟩ },
  simp only [ball_cons, bex_cons, map_cons, prod_cons] at h₁ h₂ ⊢,
  cases h₂,
  exacts [mul_lt_mul_of_lt_of_le h₂ (prod_le_prod' h₁.2),
    mul_lt_mul_of_le_of_lt h₁.1 $ ihl h₁.2 h₂]
end

@[to_additive] lemma prod_lt_prod_of_ne_nil
  [preorder M] [covariant_class M M (*) (<)] [covariant_class M M (*) (≤)]
  [covariant_class M M (function.swap (*)) (<)] [covariant_class M M (function.swap (*)) (≤)]
  {l : list ι} (hl : l ≠ []) (f g : ι → M) (hlt : ∀ i ∈ l, f i < g i) :
  (l.map f).prod < (l.map g).prod :=
prod_lt_prod' f g (λ i hi, (hlt i hi).le) $ (exists_mem_of_ne_nil l hl).imp $ λ i hi, ⟨hi, hlt i hi⟩

@[to_additive sum_le_card_nsmul]
lemma prod_le_pow_card [preorder M]
  [covariant_class M M (function.swap (*)) (≤)] [covariant_class M M (*) (≤)]
  (l : list M) (n : M) (h : ∀ (x ∈ l), x ≤ n) :
  l.prod ≤ n ^ l.length :=
by simpa only [map_id'', map_const, prod_repeat] using prod_le_prod' h

@[to_additive card_nsmul_le_sum]
lemma pow_card_le_prod [preorder M]
  [covariant_class M M (function.swap (*)) (≤)] [covariant_class M M (*) (≤)]
  (l : list M) (n : M) (h : ∀ (x ∈ l), n ≤ x) :
  n ^ l.length ≤ l.prod :=
@prod_le_pow_card Mᵒᵈ _ _ _ _ l n h

@[to_additive exists_lt_of_sum_lt] lemma exists_lt_of_prod_lt' [linear_order M]
  [covariant_class M M (function.swap (*)) (≤)] [covariant_class M M (*) (≤)] {l : list ι}
  (f g : ι → M) (h : (l.map f).prod < (l.map g).prod) :
  ∃ i ∈ l, f i < g i :=
by { contrapose! h, exact prod_le_prod' h }

@[to_additive exists_le_of_sum_le]
lemma exists_le_of_prod_le' [linear_order M] [covariant_class M M (*) (<)]
  [covariant_class M M (*) (≤)] [covariant_class M M (function.swap (*)) (<)]
  [covariant_class M M (function.swap (*)) (≤)] {l : list ι} (hl : l ≠ [])
  (f g : ι → M) (h : (l.map f).prod ≤ (l.map g).prod) :
  ∃ x ∈ l, f x ≤ g x :=
by { contrapose! h, exact prod_lt_prod_of_ne_nil hl _ _ h }

@[to_additive sum_nonneg]
lemma one_le_prod_of_one_le [preorder M] [covariant_class M M (*) (≤)] {l : list M}
  (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) :
  1 ≤ l.prod :=
begin
  -- We don't use `pow_card_le_prod` to avoid assumption
  -- [covariant_class M M (function.swap (*)) (≤)]
  induction l with hd tl ih, { refl },
  rw prod_cons,
  exact one_le_mul (hl₁ hd (mem_cons_self hd tl)) (ih (λ x h, hl₁ x (mem_cons_of_mem hd h)))
end

end monoid

section monoid_with_zero

variables [monoid_with_zero M₀]

/-- If zero is an element of a list `L`, then `list.prod L = 0`. If the domain is a nontrivial
monoid with zero with no divisors, then this implication becomes an `iff`, see
`list.prod_eq_zero_iff`. -/
lemma prod_eq_zero {L : list M₀} (h : (0 : M₀) ∈ L) : L.prod = 0 :=
begin
  induction L with a L ihL,
  { exact absurd h (not_mem_nil _) },
  { rw prod_cons,
    cases (mem_cons_iff _ _ _).1 h with ha hL,
    exacts [mul_eq_zero_of_left ha.symm _, mul_eq_zero_of_right _ (ihL hL)] }
end

/-- Product of elements of a list `L` equals zero if and only if `0 ∈ L`. See also
`list.prod_eq_zero` for an implication that needs weaker typeclass assumptions. -/
@[simp] lemma prod_eq_zero_iff [nontrivial M₀] [no_zero_divisors M₀] {L : list M₀} :
  L.prod = 0 ↔ (0 : M₀) ∈ L :=
begin
  induction L with a L ihL,
  { simp },
  { rw [prod_cons, mul_eq_zero, ihL, mem_cons_iff, eq_comm] }
end

lemma prod_ne_zero [nontrivial M₀] [no_zero_divisors M₀] {L : list M₀} (hL : (0 : M₀) ∉ L) :
  L.prod ≠ 0 :=
mt prod_eq_zero_iff.1 hL

end monoid_with_zero

section group
variables [group G]

/-- This is the `list.prod` version of `mul_inv_rev` -/
@[to_additive "This is the `list.sum` version of `add_neg_rev`"]
lemma prod_inv_reverse : ∀ (L : list G), L.prod⁻¹ = (L.map (λ x, x⁻¹)).reverse.prod
| [] := by simp
| (x :: xs) := by simp [prod_inv_reverse xs]

/-- A non-commutative variant of `list.prod_reverse` -/
@[to_additive "A non-commutative variant of `list.sum_reverse`"]
lemma prod_reverse_noncomm : ∀ (L : list G), L.reverse.prod = (L.map (λ x, x⁻¹)).prod⁻¹ :=
by simp [prod_inv_reverse]

/-- Counterpart to `list.prod_take_succ` when we have an inverse operation -/
@[simp, to_additive /-"Counterpart to `list.sum_take_succ` when we have an negation operation"-/]
lemma prod_drop_succ :
  ∀ (L : list G) (i : ℕ) (p), (L.drop (i + 1)).prod = (L.nth_le i p)⁻¹ * (L.drop i).prod
| [] i p := false.elim (nat.not_lt_zero _ p)
| (x :: xs) 0 p := by simp
| (x :: xs) (i + 1) p := prod_drop_succ xs i _

end group

section comm_group
variables [comm_group G]

/-- This is the `list.prod` version of `mul_inv` -/
@[to_additive "This is the `list.sum` version of `add_neg`"]
lemma prod_inv : ∀ (L : list G), L.prod⁻¹ = (L.map (λ x, x⁻¹)).prod
| [] := by simp
| (x :: xs) := by simp [mul_comm, prod_inv xs]

/-- Alternative version of `list.prod_update_nth` when the list is over a group -/
@[to_additive /-"Alternative version of `list.sum_update_nth` when the list is over a group"-/]
lemma prod_update_nth' (L : list G) (n : ℕ) (a : G) :
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

@[to_additive]
lemma eq_of_prod_take_eq [left_cancel_monoid M] {L L' : list M} (h : L.length = L'.length)
  (h' : ∀ i ≤ L.length, (L.take i).prod = (L'.take i).prod) : L = L' :=
begin
  apply ext_le h (λ i h₁ h₂, _),
  have : (L.take (i + 1)).prod = (L'.take (i + 1)).prod := h' _ (nat.succ_le_of_lt h₁),
  rw [prod_take_succ L i h₁, prod_take_succ L' i h₂, h' i (le_of_lt h₁)] at this,
  convert mul_left_cancel this
end

@[to_additive]
lemma monotone_prod_take [canonically_ordered_monoid M] (L : list M) :
  monotone (λ i, (L.take i).prod) :=
begin
  apply monotone_nat_of_le_succ (λ n, _),
  cases lt_or_le n L.length with h h,
  { rw prod_take_succ _ _ h,
    exact le_self_mul },
  { simp [take_all_of_le h, take_all_of_le (le_trans h (nat.le_succ _))] }
end

@[to_additive sum_pos]
lemma one_lt_prod_of_one_lt [ordered_comm_monoid M] :
  ∀ (l : list M) (hl : ∀ x ∈ l, (1 : M) < x) (hl₂ : l ≠ []), 1 < l.prod
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
lemma single_le_prod [ordered_comm_monoid M] {l : list M} (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) :
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
lemma all_one_of_le_one_le_of_prod_eq_one [ordered_comm_monoid M]
  {l : list M} (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) (hl₂ : l.prod = 1) {x : M} (hx : x ∈ l) :
  x = 1 :=
le_antisymm (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)

@[to_additive] lemma prod_eq_one_iff [canonically_ordered_monoid M] (l : list M) :
  l.prod = 1 ↔ ∀ x ∈ l, x = (1 : M) :=
⟨all_one_of_le_one_le_of_prod_eq_one (λ _ _, one_le _),
  λ h, by rw [eq_repeat.2 ⟨rfl, h⟩, prod_repeat, one_pow]⟩

/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
lemma length_le_sum_of_one_le (L : list ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.sum :=
begin
  induction L with j L IH h, { simp },
  rw [sum_cons, length, add_comm],
  exact add_le_add (h _ (set.mem_insert _ _)) (IH (λ i hi, h i (set.mem_union_right _ hi)))
end

-- TODO: develop theory of tropical rings
lemma sum_le_foldr_max [add_monoid M] [add_monoid N] [linear_order N] (f : M → N)
  (h0 : f 0 ≤ 0) (hadd : ∀ x y, f (x + y) ≤ max (f x) (f y)) (l : list M) :
  f l.sum ≤ (l.map f).foldr max 0 :=
begin
  induction l with hd tl IH,
  { simpa using h0 },
  simp only [list.sum_cons, list.foldr_map, list.foldr] at IH ⊢,
  exact (hadd _ _).trans (max_le_max le_rfl IH)
end

@[simp, to_additive]
lemma prod_erase [decidable_eq M] [comm_monoid M] {a} :
  ∀ {l : list M}, a ∈ l → a * (l.erase a).prod = l.prod
| (b :: l) h :=
  begin
    obtain rfl | ⟨ne, h⟩ := decidable.list.eq_or_ne_mem_of_mem h,
    { simp only [list.erase, if_pos, prod_cons] },
    { simp only [list.erase, if_neg (mt eq.symm ne), prod_cons, prod_erase h, mul_left_comm a b] }
  end

lemma dvd_prod [comm_monoid M] {a} {l : list M} (ha : a ∈ l) : a ∣ l.prod :=
let ⟨s, t, h⟩ := mem_split ha in
by { rw [h, prod_append, prod_cons, mul_left_comm], exact dvd_mul_right _ _ }

@[simp] lemma sum_const_nat (m n : ℕ) : sum (list.repeat m n) = m * n :=
by induction n; [refl, simp only [*, repeat_succ, sum_cons, nat.mul_succ, add_comm]]

lemma dvd_sum [semiring R] {a} {l : list R} (h : ∀ x ∈ l, a ∣ x) : a ∣ l.sum :=
begin
  induction l with x l ih,
  { exact dvd_zero _ },
  { rw [list.sum_cons],
    exact dvd_add (h _ (mem_cons_self _ _)) (ih (λ x hx, h x (mem_cons_of_mem _ hx))) }
end

/-- The product of a list of positive natural numbers is positive,
and likewise for any nontrivial ordered semiring. -/
lemma prod_pos [ordered_semiring R] [nontrivial R] (l : list R) (h : ∀ a ∈ l, (0 : R) < a) :
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
If desired, we could add a class stating that `default = 0`.
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
section
variables [has_one α] [has_mul α] [has_inv α]

@[simp, to_additive] lemma alternating_prod_nil : alternating_prod ([] : list α) = 1 := rfl
@[simp, to_additive] lemma alternating_prod_singleton (a : α) : alternating_prod [a] = a := rfl

@[to_additive] lemma alternating_prod_cons_cons' (a b : α) (l : list α) :
  alternating_prod (a :: b :: l) = a * b⁻¹ * alternating_prod l := rfl

end

@[to_additive] lemma alternating_prod_cons_cons [div_inv_monoid α] (a b : α) (l : list α) :
  alternating_prod (a :: b :: l) = a / b * alternating_prod l :=
by rw [div_eq_mul_inv, alternating_prod_cons_cons']

variables [comm_group α]

@[to_additive] lemma alternating_prod_cons' :
  ∀ (a : α) (l : list α), alternating_prod (a :: l) = a * (alternating_prod l)⁻¹
| a [] := by rw [alternating_prod_nil, inv_one, mul_one, alternating_prod_singleton]
| a (b :: l) :=
by rw [alternating_prod_cons_cons', alternating_prod_cons' b l, mul_inv, inv_inv, mul_assoc]

@[simp, to_additive] lemma alternating_prod_cons (a : α) (l : list α) :
  alternating_prod (a :: l) = a / alternating_prod l :=
by rw [div_eq_mul_inv, alternating_prod_cons']

@[to_additive]
lemma alternating_prod_append : ∀ l₁ l₂ : list α,
  alternating_prod (l₁ ++ l₂) = alternating_prod l₁ * alternating_prod l₂ ^ (-1 : ℤ) ^ length l₁
| [] l₂ := by simp
| (a :: l₁) l₂ := by simp_rw [cons_append, alternating_prod_cons, alternating_prod_append,
  length_cons, pow_succ, neg_mul, one_mul, zpow_neg, ←div_eq_mul_inv, div_div]

@[to_additive]
lemma alternating_prod_reverse :
  ∀ l : list α, alternating_prod (reverse l) = alternating_prod l ^ (-1 : ℤ) ^ (length l + 1)
| [] := by simp only [alternating_prod_nil, one_zpow, reverse_nil]
| (a :: l) :=
begin
  simp_rw [reverse_cons, alternating_prod_append, alternating_prod_reverse,
    alternating_prod_singleton, alternating_prod_cons, length_reverse, length, pow_succ, neg_mul,
    one_mul, zpow_neg, inv_inv],
  rw [mul_comm, ←div_eq_mul_inv, div_zpow],
end

end alternating

lemma sum_map_mul_left [non_unital_non_assoc_semiring R] (L : list ι) (f : ι → R) (r : R) :
  (L.map (λ b, r * f b)).sum = r * (L.map f).sum :=
sum_map_hom L f $ add_monoid_hom.mul_left r

lemma sum_map_mul_right [non_unital_non_assoc_semiring R] (L : list ι) (f : ι → R) (r : R) :
  (L.map (λ b, f b * r)).sum = (L.map f).sum * r :=
sum_map_hom L f $ add_monoid_hom.mul_right r

end list

namespace mul_opposite

open list
variables [monoid M]

lemma op_list_prod : ∀ (l : list M), op (l.prod) = (l.map op).reverse.prod
| [] := rfl
| (x :: xs) := by rw [list.prod_cons, list.map_cons, list.reverse_cons', list.prod_concat, op_mul,
                      op_list_prod]

lemma _root_.mul_opposite.unop_list_prod (l : list Mᵐᵒᵖ) :
  (l.prod).unop = (l.map unop).reverse.prod :=
by rw [← op_inj, op_unop, mul_opposite.op_list_prod, map_reverse, map_map, reverse_reverse,
  op_comp_unop, map_id]

end mul_opposite

section monoid_hom

variables [monoid M] [monoid N]

@[to_additive]
lemma map_list_prod {F : Type*} [monoid_hom_class F M N] (f : F)
  (l : list M) : f l.prod = (l.map f).prod :=
(l.prod_hom f).symm

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements. -/
lemma unop_map_list_prod {F : Type*} [monoid_hom_class F M Nᵐᵒᵖ] (f : F) (l : list M) :
  (f l.prod).unop = (l.map (mul_opposite.unop ∘ f)).reverse.prod :=
by rw [map_list_prod f l, mul_opposite.unop_list_prod, list.map_map]

namespace monoid_hom

/-- Deprecated, use `_root_.map_list_prod` instead. -/
@[to_additive "Deprecated, use `_root_.map_list_sum` instead."]
protected lemma map_list_prod (f : M →* N) (l : list M) :
  f l.prod = (l.map f).prod :=
map_list_prod f l

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements.

Deprecated, use `_root_.unop_map_list_prod` instead. -/
protected lemma unop_map_list_prod (f : M →* Nᵐᵒᵖ) (l : list M) :
  (f l.prod).unop = (l.map (mul_opposite.unop ∘ f)).reverse.prod :=
unop_map_list_prod f l

end monoid_hom

end monoid_hom
