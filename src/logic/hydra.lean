/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import data.finsupp.multiset
import order.game_add
import data.dfinsupp.lex

/-!
# Termination of a hydra game

This file deals with the following version of the hydra game: each head of the hydra is
labelled by an element in a type `α`, and when you cut off one head with label `a`, it
grows back an arbitrary but finite number of heads, all labelled by elements smaller than
`a` with respect to a well-founded relation `r` on `α`. We show that no matter how (in
what order) you choose cut off the heads, the game always terminates, i.e. all heads will
eventually be cut off (but of course it can last arbitrarily long, i.e. takes an
arbitrary finite number of steps).

This result is stated as the well-foundedness of the `cut_expand` relation defined in
this file: we model the heads of the hydra as a multiset of elements of `α`, and the
valid "moves" of the game are modelled by the relation `cut_expand r` on `multiset α`:
`cut_expand r s' s` is true iff `s'` is obtained by removing one head `a ∈ s` and
adding back an arbitrary multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

We follow the proof by Peter LeFanu Lumsdaine at https://mathoverflow.net/a/229084/3332.

TODO: formalize the relations corresponding to more powerful (e.g. Kirby–Paris and Buchholz)
hydras, and prove their well-foundedness.
-/

namespace dfinsupp

variables {ι : Type*} {α : ι → Type*} [hz : Π i, has_zero (α i)]
include hz

/-- Merge two finitely supported functions `x y : Π₀ i, α i`; at every coordinate `a : α`, use the
  predicate `p` to decide whether to take the value of `x` or the value of `y`. -/
noncomputable def merge (p : ι → Prop) (x y : Π₀ i, α i) : Π₀ i, α i :=
by classical; exactI mk (x.support ∪ y.support) (λ i, if p i then x i else y i)

lemma merge_apply (p : ι → Prop) (x y : Π₀ i, α i) (i : ι) :
  merge p x y i = if p i then x i else y i :=
mk_apply.trans begin
  split_ifs with h h' h', refl, refl,
  all_goals { rw [eq_comm, ← not_mem_support_iff], rw finset.not_mem_union at h },
  exacts [h.1, h.2],
end

open relation prod
variables (r : ι → ι → Prop) (s : Π i, α i → α i → Prop)

lemma lex_fibration : fibration
  (inv_image (game_add (dfinsupp.lex r s) (dfinsupp.lex r s)) snd)
  (dfinsupp.lex r s)
  (λ x, merge x.1 x.2.1 x.2.2) :=
begin
  rintro ⟨p, x₁, x₂⟩ x ⟨i, hr, hs⟩,
  simp_rw [merge_apply] at hs hr,
  split_ifs at hs, classical,
  work_on_goal 1
  { refine ⟨⟨λ j, r j i → p j, merge (λ j, r j i) x₁ x, x₂⟩, game_add.fst ⟨i, _⟩, _⟩ },
  work_on_goal 3
  { refine ⟨⟨λ j, r j i ∧ p j, x₁, merge (λ j, r j i) x₂ x⟩, game_add.snd ⟨i, _⟩, _⟩ },
  swap 3, iterate 2
  { simp_rw merge_apply,
    refine ⟨λ j h, if_pos h, _⟩,
    convert hs,
    refine ite_eq_right_iff.2 (λ h', (hr i h').symm ▸ _),
    rw if_neg h <|> rw if_pos h },
  all_goals { ext j, simp_rw merge_apply, split_ifs with h₁ h₂ },
  { rw [hr j h₂, if_pos (h₁ h₂)] },
  { refl },
  { rw not_imp at h₁, rw [hr j h₁.1, if_neg h₁.2] },
  { rw [hr j h₁.1, if_pos h₁.2] },
  { rw [hr j h₂, if_neg (λ h', h₁ ⟨h₂, h'⟩)] },
  { refl },
end

lemma merge_single_erase (x : Π₀ i, α i) (i : ι) :
  merge (λ j, j = i) (single i (x i)) (x.erase i) = x :=
begin
  ext j, rw merge_apply, split_ifs,
  { rw [h, single_eq_same] }, { exact erase_ne h },
end

lemma lex.acc_of_single_erase {x : Π₀ i, α i} (i : ι)
  (hs : acc (dfinsupp.lex r s) (single i (x i)))
  (hu : acc (dfinsupp.lex r s) (x.erase i)) : acc (dfinsupp.lex r s) x :=
begin
  classical, rw ← merge_single_erase x i,
  convert acc.of_fibration _ (lex_fibration r s) _,
  work_on_goal 4 { refine ⟨_, _, _⟩ }, iterate 3 { refl },
  exact inv_image.accessible snd (hs.prod_game_add hu),
end

variable (hbot : ∀ ⦃i a⦄, ¬ s i a 0)
include hbot

lemma lex.acc_zero : acc (dfinsupp.lex r s) 0 := acc.intro 0 $ λ x ⟨_, _, h⟩, (hbot h).elim

lemma lex.acc_of_single (x : Π₀ i, α i) :
  (∀ i ∈ x.support, acc (dfinsupp.lex r s) $ single i (x i)) → acc (dfinsupp.lex r s) x :=
begin
  generalize ht : x.support = t, revert x, classical,
  induction t using finset.induction with b t hb ih,
  { intros x ht, rw support_eq_empty.1 ht, exact λ _, lex.acc_zero r s hbot },
  refine λ x ht h, lex.acc_of_single_erase r s b (h b $ t.mem_insert_self b) _,
  refine ih _ (by rw [support_erase, ht, finset.erase_insert hb]) (λ a ha, _),
  rw [erase_ne (ha.ne_of_not_mem hb)],
  exact h a (finset.mem_insert_of_mem ha),
end

variable (hs : ∀ i, well_founded (s i))
include hs

lemma lex.acc_single {i : ι} (a : α i)
  (hi : acc (rᶜ ⊓ (≠)) i) : acc (dfinsupp.lex r s) (single i a) :=
begin
  revert a, induction hi with i hi ih,
  refine λ a, (hs i).induction a (λ a ha, _),
  refine acc.intro _ (λ x, _),
  rintro ⟨k, hr, hs⟩, classical,
  rw single_apply at hs,
  split_ifs at hs with hik,
  swap, { exact (hbot hs).elim }, subst hik,
  refine lex.acc_of_single r s hbot x (λ j hj, _),
  obtain rfl | hij := eq_or_ne i j, { exact ha _ hs },
  by_cases r j i,
  { rw [hr j h, single_eq_of_ne hij, single_zero], exact lex.acc_zero r s hbot },
  { exact ih _ ⟨h, hij.symm⟩ _ },
end

lemma lex.acc (x : Π₀ i, α i)
  (h : ∀ i ∈ x.support, acc (rᶜ ⊓ (≠)) i) : acc (dfinsupp.lex r s) x :=
lex.acc_of_single r s hbot x $ λ i hi, lex.acc_single r s hbot hs _ (h i hi)

theorem lex.well_founded (hr : well_founded $ rᶜ ⊓ (≠)) : well_founded (dfinsupp.lex r s) :=
⟨λ x, lex.acc r s hbot hs x $ λ i _, hr.apply i⟩

theorem lex.well_founded' [is_trichotomous ι r]
  (hr : well_founded r.swap) : well_founded (dfinsupp.lex r s) :=
lex.well_founded r s hbot hs $ subrelation.wf
  (λ i j h, ((@is_trichotomous.trichotomous ι r _ i j).resolve_left h.1).resolve_left h.2) hr

omit hz hbot hs

instance lex.well_founded_lt [has_lt ι] [is_trichotomous ι (<)] [hι : well_founded_gt ι]
  [Π i, canonically_ordered_add_monoid (α i)]
  [hα : ∀ i, well_founded_lt (α i)] : well_founded_lt (lex (Π₀ i, α i)) :=
⟨lex.well_founded' (<) (λ i, (<)) (λ i a, (zero_le a).not_lt) (λ i, (hα i).wf) hι.wf⟩

/- instance vs. general -/
/- pi.lex (finite linear(?)) vs. finsupp.lex -/
/- product order -/

end dfinsupp

namespace finsupp

variables {ι α : Type*} [hz : has_zero α] (r : ι → ι → Prop) (s : α → α → Prop)
  (hbot : ∀ ⦃a⦄, ¬ s a 0) (hs : well_founded s)
include hbot hs

lemma lex.acc (x : ι →₀ α) (h : ∀ i ∈ x.support, acc (rᶜ ⊓ (≠)) i) : acc (finsupp.lex r s) x :=
begin
  rw lex_eq_inv_image_dfinsupp_lex,
  refine inv_image.accessible finsupp.to_dfinsupp (dfinsupp.lex.acc r _ (λ i, hbot) (λ i, hs) _ _),
  simpa only [to_dfinsupp_support] using h,
end

theorem lex.well_founded (hr : well_founded $ rᶜ ⊓ (≠)) : well_founded (finsupp.lex r s) :=
⟨λ x, lex.acc r s hbot hs x $ λ i _, hr.apply i⟩

theorem lex.well_founded' [is_trichotomous ι r]
  (hr : well_founded r.swap) : well_founded (finsupp.lex r s) :=
(lex_eq_inv_image_dfinsupp_lex r s).symm ▸
  inv_image.wf _ (dfinsupp.lex.well_founded' r _ (λ i, hbot) (λ i, hs) hr)

omit hbot hs

instance lex.well_founded_lt [has_lt ι] [is_trichotomous ι (<)] [hι : well_founded_gt ι]
  [canonically_ordered_add_monoid α] [hα : well_founded_lt α] : well_founded_lt (lex (ι →₀ α)) :=
⟨lex.well_founded' (<) (<) (λ a, (zero_le a).not_lt) hα.wf hι.wf⟩

/- product order -/

end finsupp

namespace relation

open multiset prod

variables {α β : Type*}

/-- The relation that specifies valid moves in our hydra game. `cut_expand r s' s`
  means that `s'` is obtained by removing one head `a ∈ s` and adding back an arbitrary
  multiset `t` of heads such that all `a' ∈ t` satisfy `r a' a`.

  This is most directly translated into `s' = s.erase a + t`, but `multiset.erase` requires
  `decidable_eq α`, so we use the equivalent condition `s' + {a} = s + t` instead, which
  is also easier to verify for explicit multisets `s'`, `s` and `t`.

  We also don't include the condition `a ∈ s` because `s' + {a} = s + t` already
  guarantees `a ∈ s + t`, and if `r` is irreflexive then `a ∉ t`, which is the
  case when `r` is well-founded, the case we are primarily interested in.

  The lemma `relation.cut_expand_iff` below converts between this convenient definition
  and the direct translation when `r` is irreflexive. -/
def cut_expand {α} (r : α → α → Prop) (s' s : multiset α) : Prop :=
∃ (t : multiset α) (a : α), (∀ a' ∈ t, r a' a) ∧ s' + {a} = s + t

variables {α : Type*} {r : α → α → Prop}

theorem cut_expand_eq_inv_image_lex : cut_expand r = inv_image (finsupp.lex r (<)) to_finsupp :=
begin

end

theorem cut_expand_singleton {s x} (h : ∀ x' ∈ s, r x' x) : cut_expand r s {x} :=
⟨s, x, h, add_comm s _⟩

theorem cut_expand_singleton_singleton {x' x} (h : r x' x) : cut_expand r {x'} {x} :=
cut_expand_singleton (λ a h, by rwa mem_singleton.1 h)

theorem cut_expand_add_left {t u} (s) : cut_expand r (s + t) (s + u) ↔ cut_expand r t u :=
exists₂_congr $ λ _ _, and_congr iff.rfl $ by rw [add_assoc, add_assoc, add_left_cancel_iff]

lemma cut_expand_iff [decidable_eq α] [is_irrefl α r] {s' s : multiset α} :
  cut_expand r s' s ↔ ∃ (t : multiset α) a, (∀ a' ∈ t, r a' a) ∧ a ∈ s ∧ s' = s.erase a + t :=
begin
  simp_rw [cut_expand, add_singleton_eq_iff],
  refine exists₂_congr (λ t a, ⟨_, _⟩),
  { rintro ⟨ht, ha, rfl⟩,
    obtain (h|h) := mem_add.1 ha,
    exacts [⟨ht, h, t.erase_add_left_pos h⟩, (@irrefl α r _ a (ht a h)).elim] },
  { rintro ⟨ht, h, rfl⟩,
    exact ⟨ht, mem_add.2 (or.inl h), (t.erase_add_left_pos h).symm⟩ },
end

theorem not_cut_expand_zero [is_irrefl α r] (s) : ¬ cut_expand r s 0 :=
by { classical, rw cut_expand_iff, rintro ⟨_, _, _, ⟨⟩, _⟩ }

/-- For any relation `r` on `α`, multiset addition `multiset α × multiset α → multiset α` is a
  fibration between the game sum of `cut_expand r` with itself and `cut_expand r` itself. -/
lemma cut_expand_fibration (r : α → α → Prop) :
  fibration (game_add (cut_expand r) (cut_expand r)) (cut_expand r) (λ s, s.1 + s.2) :=
begin
  rintro ⟨s₁, s₂⟩ s ⟨t, a, hr, he⟩, dsimp at he ⊢,
  classical, obtain ⟨ha, rfl⟩ := add_singleton_eq_iff.1 he,
  rw [add_assoc, mem_add] at ha, obtain (h|h) := ha,
  { refine ⟨(s₁.erase a + t, s₂), game_add.fst ⟨t, a, hr, _⟩, _⟩,
    { rw [add_comm, ← add_assoc, singleton_add, cons_erase h] },
    { rw [add_assoc s₁, erase_add_left_pos _ h, add_right_comm, add_assoc] } },
  { refine ⟨(s₁, (s₂ + t).erase a), game_add.snd ⟨t, a, hr, _⟩, _⟩,
    { rw [add_comm, singleton_add, cons_erase h] },
    { rw [add_assoc, erase_add_right_pos _ h] } },
end

/-- A multiset is accessible under `cut_expand` if all its singleton subsets are,
  assuming `r` is irreflexive. -/
lemma acc_of_singleton [is_irrefl α r] {s : multiset α} :
  (∀ a ∈ s, acc (cut_expand r) {a}) → acc (cut_expand r) s :=
begin
  refine multiset.induction _ _ s,
  { exact λ _, acc.intro 0 $ λ s h, (not_cut_expand_zero s h).elim },
  { intros a s ih hacc, rw ← s.singleton_add a,
    exact ((hacc a $ s.mem_cons_self a).prod_game_add $ ih $ λ a ha,
      hacc a $ mem_cons_of_mem ha).of_fibration _ (cut_expand_fibration r) },
end

/-- A singleton `{a}` is accessible under `cut_expand r` if `a` is accessible under `r`,
  assuming `r` is irreflexive. -/
lemma _root_.acc.cut_expand [is_irrefl α r] {a : α} (hacc : acc r a) : acc (cut_expand r) {a} :=
begin
  induction hacc with a h ih,
  refine acc.intro _ (λ s, _),
  classical, rw cut_expand_iff,
  rintro ⟨t, a, hr, rfl|⟨⟨⟩⟩, rfl⟩,
  refine acc_of_singleton (λ a', _),
  rw [erase_singleton, zero_add],
  exact ih a' ∘ hr a',
end

/-- `cut_expand r` is well-founded when `r` is. -/
theorem _root_.well_founded.cut_expand (hr : well_founded r) : well_founded (cut_expand r) :=
⟨by { letI h := hr.is_irrefl, exact λ s, acc_of_singleton $ λ a _, (hr.apply a).cut_expand }⟩

end relation
