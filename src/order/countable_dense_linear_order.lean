/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import order.ideal
import data.finset

/-!
# The back and forth method and countable dense linear orders

## Results

Suppose `α β` are linear orders, with `α` countable and `β` dense, nonempty, without endpoints.
Then there is an order embedding `α ↪ β`. If in addition `α` is dense, nonempty, without
endpoints and `β` is countable, then we can upgrade this to an order isomorhpism `α ≃ β`.

The idea for both results is to consider "partial isomorphisms", which
identify a finite subset of `α` with a finite subset of `β`, and prove that
for any such partial isomorphism `f` and `a : α`, we can extend `f` to
include `a` in its domain.

## References

https://en.wikipedia.org/wiki/Back-and-forth_method

## Tags

back and forth, dense, countable, order

-/

noncomputable theory
open_locale classical

namespace order

/-- Suppose `α` is a nonempty dense linear order without endpoints, and
    suppose `lo`, `hi`, are finite subssets with all of `lo` strictly
    before `hi`. Then there is an element of `α` strictly between `lo`
    and `hi`. -/
lemma exists_between_finsets {α : Type*} [linear_order α]
  [densely_ordered α] [no_bot_order α] [no_top_order α] [nonem : nonempty α]
  (lo hi : finset α) (lo_lt_hi : ∀ (x ∈ lo) (y ∈ hi), x < y) :
  ∃ m : α, (∀ x ∈ lo, x < m) ∧ (∀ y ∈ hi, m < y) :=
if nlo : lo.nonempty then
  if nhi : hi.nonempty then -- both sets are nonempty, use densely_ordered
    exists.elim (exists_between (lo_lt_hi _ (finset.max'_mem _ nlo) _ (finset.min'_mem _ nhi)))
      (λ m hm, ⟨m, λ x hx, lt_of_le_of_lt (finset.le_max' lo x hx) hm.1,
                   λ y hy, lt_of_lt_of_le hm.2 (finset.min'_le hi y hy)⟩)
  else -- upper set is empty, use no_top_order
    exists.elim (no_top (finset.max' lo nlo)) (λ m hm,
    ⟨m, λ x hx, lt_of_le_of_lt (finset.le_max' lo x hx) hm,
        λ y hy, (nhi ⟨y, hy⟩).elim⟩)
else
  if nhi : hi.nonempty then -- lower set is empty, use no_bot_order
    exists.elim (no_bot (finset.min' hi nhi)) (λ m hm,
    ⟨m, λ x hx, (nlo ⟨x, hx⟩).elim,
        λ y hy, lt_of_lt_of_le hm (finset.min'_le hi y hy)⟩)
  else -- both sets are empty, use nonempty
    nonem.elim (λ m,
    ⟨m, λ x hx, (nlo ⟨x, hx⟩).elim,
        λ y hy, (nhi ⟨y, hy⟩).elim⟩)

variables (α β : Type*) [linear_order α] [linear_order β]

/-- The type of partial order isomorphisms between `α` and `β` defined on finite subsets.
    A partial order isomorphism is encoded as a finite subset of `α × β`, consisting
    of pairs which should be identified. -/
def partial_iso : Type* :=
{ f : finset (α × β) // ∀ (p q ∈ f),
  cmp (prod.fst p) (prod.fst q) = cmp (prod.snd p) (prod.snd q) }

namespace partial_iso

instance : inhabited (partial_iso α β) := ⟨⟨∅, λ p q h, h.elim⟩⟩
instance : preorder (partial_iso α β) := subtype.preorder _

variables {α β}

lemma exists_across [densely_ordered β] [no_bot_order β] [no_top_order β] [nonempty β]
  (f : partial_iso α β) (a : α) :
  ∃ b : β, ∀ (p ∈ f.val), cmp (prod.fst p) a = cmp (prod.snd p) b :=
begin
  by_cases h : ∃ b, (a, b) ∈ f.val,
  { cases h with b hb, exact ⟨b, λ p hp, f.property _ _ hp hb⟩, },
  cases exists_between_finsets ((f.val.filter $ λ p : α × β, p.fst < a).image prod.snd)
                   ((f.val.filter $ λ p : α × β, a < p.fst).image prod.snd) _
    with b hb,
  swap,
  { intros x hx y hy,
    rw finset.mem_image at hx hy,
    rcases hx with ⟨p, hp1, rfl⟩,
    rcases hy with ⟨q, hq1, rfl⟩,
    rw finset.mem_filter at hp1 hq1,
    rw ←lt_iff_lt_of_cmp_eq_cmp (f.property _ _ hp1.1 hq1.1),
    exact lt_trans hp1.right hq1.right, },
  use b,
  rintros ⟨p1, p2⟩ hp,
  have : p1 ≠ a := λ he, h ⟨p2, he ▸ hp⟩,
  cases lt_or_gt_of_ne this with hl hr,
  { have : p1 < a ∧ p2 < b := ⟨hl, hb.1 _ (finset.mem_image.mpr ⟨(p1, p2),
                        finset.mem_filter.mpr ⟨hp, hl⟩, rfl⟩)⟩,
    rw [←cmp_eq_lt_iff, ←cmp_eq_lt_iff] at this, cc, },
  { have : a < p1 ∧ b < p2 := ⟨hr, hb.2 _ (finset.mem_image.mpr ⟨(p1, p2),
                        finset.mem_filter.mpr ⟨hp, hr⟩, rfl⟩)⟩,
    rw [←cmp_eq_gt_iff, ←cmp_eq_gt_iff] at this, cc, },
end

/-- The set of partial isomorphism defined at `a : α`, together with a proof that any
    partial isomorphism can be extended to one defined at `a`. -/
def defined_at_left [densely_ordered β] [no_bot_order β] [no_top_order β] [nonempty β]
  (a : α) : cofinal (partial_iso α β) :=
{ carrier := λ f, ∃ b : β, (a, b) ∈ f.val,
  mem_gt :=
  begin
    intro f,
    cases exists_across f a with b a_b,
    refine ⟨ ⟨insert (a,b) f.val, _⟩,
      ⟨b, finset.mem_insert_self _ _⟩, finset.subset_insert _ _⟩,
    intros p q hp hq,
    rw finset.mem_insert at hp hq,
    rcases hp with rfl | pf;
    rcases hq with rfl | qf,
    { simp },
    { rw cmp_eq_cmp_symm, exact a_b _ qf },
    { exact a_b _ pf },
    { exact f.property _ _ pf qf },
  end }

/-- A partial isomorphism between `α` and `β` is also a partial isomorphism between `β` and `α`. -/
protected def comm : partial_iso α β → partial_iso β α :=
subtype.map (finset.image (equiv.prod_comm _ _)) $ λ f hf p q hp hq,
  eq.symm $ hf ((equiv.prod_comm α β).symm p) ((equiv.prod_comm α β).symm q)
(by { rw [←finset.mem_coe, finset.coe_image, equiv.image_eq_preimage] at hp,
  rwa ←finset.mem_coe })
(by { rw [←finset.mem_coe, finset.coe_image, equiv.image_eq_preimage] at hq,
  rwa ←finset.mem_coe })

/-- The set of partial isomorphism defined on `b : β `, together with a proof that any
    partial isomorphism can be extended to include `b`. We prove this by symmetry. -/
def defined_at_right [densely_ordered α] [no_bot_order α] [no_top_order α] [nonempty α]
(b : β) : cofinal (partial_iso α β) :=
{ carrier := λ f, ∃ a, (a, b) ∈ f.val,
  mem_gt :=
  begin
    intro f,
    rcases (defined_at_left b).mem_gt (partial_iso.comm f) with ⟨f', ⟨a, ha⟩, hl⟩,
    use partial_iso.comm f',
    split,
    { use a,
      change (a, b) ∈ f'.val.image _,
      rw [←finset.mem_coe, finset.coe_image, equiv.image_eq_preimage],
      exact ha },
    { change _ ⊆ f'.val.image _,
      rw [←finset.coe_subset, finset.coe_image, equiv.subset_image],
      change f.val.image _ ⊆ _ at hl,
      rwa [←finset.coe_subset, finset.coe_image] at hl }
  end }

end partial_iso
open partial_iso

variables (α β)

/-- Any countable linear order embeds in any nonempty dense linear order without endpoints. -/
def embedding_from_countable_to_dense
[encodable α] [densely_ordered β] [no_bot_order β] [no_top_order β] [nonempty β] :
  α ↪o β :=
let our_ideal : ideal (partial_iso α β) :=
  ideal_of_cofinals (default _) defined_at_left in
have exists_right : ∀ (a : α), ∃ (b : β) (f ∈ our_ideal), (a, b) ∈ subtype.val f :=
  begin
    intro a,
    rcases cofinal_meets_ideal_of_cofinals (default _) defined_at_left a
      with ⟨f, ⟨b, hb⟩, hf⟩,
    exact ⟨b, f, hf, hb⟩,
  end,
order_embedding.of_strict_mono (λ a, classical.some (exists_right a))
begin
  intros a b,
  refine (lt_iff_lt_of_cmp_eq_cmp _).mp,
  rcases classical.some_spec (exists_right a) with ⟨f, hf, ha⟩,
  rcases classical.some_spec (exists_right b) with ⟨g, hg, hb⟩,
  rcases our_ideal.directed _ hf _ hg
    with ⟨m, hm, fm, gm⟩,
  exact m.property (a, _) (b, _) (fm ha) (gm hb)
end

/-- Any two countable dense, nonempty linear orders without endpoints are order isomorphic. --/
def iso_of_countable_dense
[encodable α] [densely_ordered α] [no_bot_order α] [no_top_order α] [nonempty α]
[encodable β] [densely_ordered β] [no_bot_order β] [no_top_order β] [nonempty β]
  : α ≃o β :=
let to_cofinal : α ⊕ β → cofinal (partial_iso α β) :=
  λ p, sum.rec_on p defined_at_left defined_at_right in
let our_ideal : ideal (partial_iso α β) :=
  ideal_of_cofinals (default _) to_cofinal in
have exists_right : ∀ (a : α), ∃ (b : β) (f ∈ our_ideal), (a, b) ∈ subtype.val f :=
  begin
    intro a,
    rcases cofinal_meets_ideal_of_cofinals (default _) to_cofinal (sum.inl a)
      with ⟨f, ⟨b, hb⟩, hf⟩,
    exact ⟨b, f, hf, hb⟩,
  end,
have exists_left : ∀ (b : β), ∃ (a : α) (f ∈ our_ideal), (a, b) ∈ subtype.val f :=
  begin
    intro b,
    rcases cofinal_meets_ideal_of_cofinals (default _) to_cofinal (sum.inr b)
      with ⟨f, ⟨a, ha⟩, hf⟩,
    exact ⟨a, f, hf, ha⟩,
  end,
order_iso.of_cmp_eq_cmp (λ a, classical.some (exists_right a))
                        (λ b, classical.some (exists_left b))
begin
  intros a b,
  rcases classical.some_spec (exists_right a) with ⟨f, hf, ha⟩,
  rcases classical.some_spec (exists_left b) with ⟨g, hg, hb⟩,
  rcases our_ideal.directed _ hf _ hg
    with ⟨m, hm, fm, gm⟩,
  exact m.property (a, _) (_, b) (fm ha) (gm hb)
end

end order
