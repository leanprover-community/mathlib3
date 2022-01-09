/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
import combinatorics.hall.finite
import topology.category.Top.limits

/-!
# Hall's Marriage Theorem

Given a list of finite subsets $X_1, X_2, \dots, X_n$ of some given set
$S$, P. Hall in [Hall1935] gave a necessary and sufficient condition for
there to be a list of distinct elements $x_1, x_2, \dots, x_n$ with
$x_i\in X_i$ for each $i$: it is when for each $k$, the union of every
$k$ of these subsets has at least $k$ elements.

Rather than a list of finite subsets, one may consider indexed families
`t : ι → finset α` of finite subsets with `ι` a `fintype`, and then the list
of distinct representatives is given by an injective function `f : ι → α`
such that `∀ i, f i ∈ t i`, called a *matching*.
This version is formalized as `finset.all_card_le_bUnion_card_iff_exists_injective'`
in a separate module.

The theorem can be generalized to remove the constraint that `ι` be a `fintype`.
As observed in [Halpern1966], one may use the constrained version of the theorem
in a compactness argument to remove this constraint.
The formulation of compactness we use is that inverse limits of nonempty finite sets
are nonempty (`nonempty_sections_of_fintype_inverse_system`), which uses the
Tychonoff theorem.
The core of this module is constructing the inverse system: for every finite subset `ι'` of
`ι`, we can consider the matchings on the restriction of the indexed family `t` to `ι'`.

## Main statements

* `finset.all_card_le_bUnion_card_iff_exists_injective` is in terms of `t : ι → finset α`.
* `fintype.all_card_le_rel_image_card_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` such that `rel.image r {a}` is a finite set for all `a : α`.
* `fintype.all_card_le_filter_rel_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` on finite types, with the Hall condition given in terms of
  `finset.univ.filter`.

## Todo

* The statement of the theorem in terms of bipartite graphs is in preparation.

## Tags

Hall's Marriage Theorem, indexed families
-/

open finset

universes u v

/-- The sup directed order on finsets.

TODO: remove when #9200 is merged.  There are two ways `finset α` can
get a `small_category` instance (used in
`hall_matchings_functor`). The first is from the preorder on `finset
α` and the second is from this `directed_order`. These categories
should be the same, but there is a defeq issue. -/
def hall_finset_directed_order (α : Type u) : directed_order (finset α) :=
⟨λ s t, by { classical, exact ⟨s ∪ t, subset_union_left s t, subset_union_right s t⟩ }⟩

local attribute [instance] hall_finset_directed_order

/-- The set of matchings for `t` when restricted to a `finset` of `ι`. -/
def hall_matchings_on {ι : Type u} {α : Type v} (t : ι → finset α) (ι' : finset ι) :=
{f : ι' → α | function.injective f ∧ ∀ x, f x ∈ t x}

/-- Given a matching on a finset, construct the restriction of that matching to a subset. -/
def hall_matchings_on.restrict {ι : Type u} {α : Type v}
  (t : ι → finset α) {ι' ι'' : finset ι} (h : ι' ⊆ ι'')
  (f : hall_matchings_on t ι'') : hall_matchings_on t ι' :=
begin
  refine ⟨λ i, f.val ⟨i, h i.property⟩, _⟩,
  cases f.property with hinj hc,
  refine ⟨_, λ i, hc ⟨i, h i.property⟩⟩,
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hh,
  simpa only [subtype.mk_eq_mk] using hinj hh,
end

/-- When the Hall condition is satisfied, the set of matchings on a finite set is nonempty.
This is where `finset.all_card_le_bUnion_card_iff_exists_injective'` comes into the argument. -/
lemma hall_matchings_on.nonempty {ι : Type u} {α : Type v} [decidable_eq α]
  (t : ι → finset α) (h : (∀ (s : finset ι), s.card ≤ (s.bUnion t).card))
  (ι' : finset ι) : nonempty (hall_matchings_on t ι') :=
begin
  classical,
  refine ⟨classical.indefinite_description _ _⟩,
  apply (all_card_le_bUnion_card_iff_exists_injective' (λ (i : ι'), t i)).mp,
  intro s',
  convert h (s'.image coe) using 1,
  simp only [card_image_of_injective s' subtype.coe_injective],
  rw image_bUnion,
  congr,
end

/--
This is the `hall_matchings_on` sets assembled into a directed system.
-/
-- TODO: This takes a long time to elaborate for an unknown reason.
def hall_matchings_functor {ι : Type u} {α : Type v} (t : ι → finset α) :
  (finset ι)ᵒᵖ ⥤ Type (max u v) :=
{ obj := λ ι', hall_matchings_on t ι'.unop,
  map := λ ι' ι'' g f, hall_matchings_on.restrict t (category_theory.le_of_hom g.unop) f }

noncomputable instance hall_matchings_on.fintype {ι : Type u} {α : Type v}
  (t : ι → finset α) (ι' : finset ι) :
  fintype (hall_matchings_on t ι') :=
begin
  classical,
  rw hall_matchings_on,
  let g : hall_matchings_on t ι' → (ι' → ι'.bUnion t),
  { rintro f i,
    refine ⟨f.val i, _⟩,
    rw mem_bUnion,
    exact ⟨i, i.property, f.property.2 i⟩ },
  apply fintype.of_injective g,
  intros f f' h,
  simp only [g, function.funext_iff, subtype.val_eq_coe] at h,
  ext a,
  exact h a,
end

/--
This is the version of **Hall's Marriage Theorem** in terms of indexed
families of finite sets `t : ι → finset α`.  It states that there is a
set of distinct representatives if and only if every union of `k` of the
sets has at least `k` elements.

Recall that `s.bUnion t` is the union of all the sets `t i` for `i ∈ s`.

This theorem is bootstrapped from `finset.all_card_le_bUnion_card_iff_exists_injective'`,
which has the additional constraint that `ι` is a `fintype`.
-/
theorem finset.all_card_le_bUnion_card_iff_exists_injective
  {ι : Type u} {α : Type v} [decidable_eq α] (t : ι → finset α) :
  (∀ (s : finset ι), s.card ≤ (s.bUnion t).card) ↔
    (∃ (f : ι → α), function.injective f ∧ ∀ x, f x ∈ t x) :=
begin
  split,
  { intro h,
    /- Set up the functor -/
    haveI : ∀ (ι' : (finset ι)ᵒᵖ), nonempty ((hall_matchings_functor t).obj ι') :=
      λ ι', hall_matchings_on.nonempty t h ι'.unop,
    classical,
    haveI : Π (ι' : (finset ι)ᵒᵖ), fintype ((hall_matchings_functor t).obj ι') := begin
      intro ι',
      rw [hall_matchings_functor],
      apply_instance,
    end,
    /- Apply the compactness argument -/
    obtain ⟨u, hu⟩ := nonempty_sections_of_fintype_inverse_system (hall_matchings_functor t),
    /- Interpret the resulting section of the inverse limit -/
    refine ⟨_, _, _⟩,
    { /- Build the matching function from the section -/
      exact λ i, (u (opposite.op ({i} : finset ι))).val
                 ⟨i, by simp only [opposite.unop_op, mem_singleton]⟩, },
    { /- Show that it is injective -/
      intros i i',
      have subi : ({i} : finset ι) ⊆ {i,i'} := by simp,
      have subi' : ({i'} : finset ι) ⊆ {i,i'} := by simp,
      have le : ∀ {s t : finset ι}, s ⊆ t → s ≤ t := λ _ _ h, h,
      rw [←hu (category_theory.hom_of_le (le subi)).op,
          ←hu (category_theory.hom_of_le (le subi')).op],
      let uii' := u (opposite.op ({i,i'} : finset ι)),
      exact λ h, subtype.mk_eq_mk.mp (uii'.property.1 h), },
    { /- Show that it maps each index to the corresponding finite set -/
      intro i,
      apply (u (opposite.op ({i} : finset ι))).property.2, }, },
  { /- The reverse direction is a straightforward cardinality argument -/
    rintro ⟨f, hf₁, hf₂⟩ s,
    rw ←finset.card_image_of_injective s hf₁,
    apply finset.card_le_of_subset,
    intro _,
    rw [finset.mem_image, finset.mem_bUnion],
    rintros ⟨x, hx, rfl⟩,
    exact ⟨x, hx, hf₂ x⟩, },
end

/-- Given a relation such that the image of every singleton set is finite, then the image of every
finite set is finite. -/
instance {α : Type u} {β : Type v} [decidable_eq β]
  (r : α → β → Prop) [∀ (a : α), fintype (rel.image r {a})]
  (A : finset α) : fintype (rel.image r A) :=
begin
  have h : rel.image r A = (A.bUnion (λ a, (rel.image r {a}).to_finset) : set β),
  { ext, simp [rel.image], },
  rw [h],
  apply finset_coe.fintype,
end

/--
This is a version of **Hall's Marriage Theorem** in terms of a relation
between types `α` and `β` such that `α` is finite and the image of
each `x : α` is finite (it suffices for `β` to be finite; see
`fintype.all_card_le_filter_rel_iff_exists_injective`).  There is
a transversal of the relation (an injective function `α → β` whose graph is
a subrelation of the relation) iff every subset of
`k` terms of `α` is related to at least `k` terms of `β`.

Note: if `[fintype β]`, then there exist instances for `[∀ (a : α), fintype (rel.image r {a})]`.
-/
theorem fintype.all_card_le_rel_image_card_iff_exists_injective
  {α : Type u} {β : Type v} [decidable_eq β]
  (r : α → β → Prop) [∀ (a : α), fintype (rel.image r {a})] :
  (∀ (A : finset α), A.card ≤ fintype.card (rel.image r A)) ↔
    (∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x)) :=
begin
  let r' := λ a, (rel.image r {a}).to_finset,
  have h : ∀ (A : finset α), fintype.card (rel.image r A) = (A.bUnion r').card,
  { intro A,
    rw ←set.to_finset_card,
    apply congr_arg,
    ext b,
    simp [rel.image], },
  have h' : ∀ (f : α → β) x, r x (f x) ↔ f x ∈ r' x,
  { simp [rel.image], },
  simp only [h, h'],
  apply finset.all_card_le_bUnion_card_iff_exists_injective,
end

/--
This is a version of **Hall's Marriage Theorem** in terms of a relation to a finite type.
There is a transversal of the relation (an injective function `α → β` whose graph is a subrelation
of the relation) iff every subset of `k` terms of `α` is related to at least `k` terms of `β`.

It is like `fintype.all_card_le_rel_image_card_iff_exists_injective` but uses `finset.filter`
rather than `rel.image`.
-/
/- TODO: decidable_pred makes Yael sad. When an appropriate decidable_rel-like exists, fix it. -/
theorem fintype.all_card_le_filter_rel_iff_exists_injective
  {α : Type u} {β : Type v} [fintype β]
  (r : α → β → Prop) [∀ a, decidable_pred (r a)] :
  (∀ (A : finset α), A.card ≤ (univ.filter (λ (b : β), ∃ a ∈ A, r a b)).card) ↔
    (∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x)) :=
begin
  haveI := classical.dec_eq β,
  let r' := λ a, univ.filter (λ b, r a b),
  have h : ∀ (A : finset α), (univ.filter (λ (b : β), ∃ a ∈ A, r a b)) = (A.bUnion r'),
  { intro A,
    ext b,
    simp, },
  have h' : ∀ (f : α → β) x, r x (f x) ↔ f x ∈ r' x,
  { simp, },
  simp_rw [h, h'],
  apply finset.all_card_le_bUnion_card_iff_exists_injective,
end
