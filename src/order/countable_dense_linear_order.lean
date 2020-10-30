/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import order.ideal
import data.finset

/-

  For linear orders α β with α countable and β dense,
  we prove that α embeds in β.
    If additionally β is countable and α is dense,
  then we get an order isomorphism.

-/

noncomputable theory
open_locale classical
open order

section cmp

variables {α : Type*} [linear_order α] (x y : α)

@[simp] lemma cmp_eq_lt_iff : cmp x y = ordering.lt ↔ x < y :=
ordering.compares.eq_lt $ cmp_compares x y

@[simp] lemma cmp_eq_eq_iff : cmp x y = ordering.eq ↔ x = y :=
ordering.compares.eq_eq $ cmp_compares x y

@[simp] lemma cmp_eq_gt_iff : cmp x y = ordering.gt ↔ y < x :=
ordering.compares.eq_gt $ cmp_compares x y

@[simp] lemma cmp_self_eq_eq : cmp x x = ordering.eq :=
(ordering.compares.eq_eq (cmp_compares x x)).mpr rfl

variables {x y} {β : Type*} [linear_order β] {x' y' : β}

lemma cmp_eq_cmp_symm : cmp x y = cmp x' y' ↔ cmp y x = cmp y' x' :=
by { split, rw [←cmp_swap _ y, ←cmp_swap _ y'], cc,
  rw [←cmp_swap _ x, ←cmp_swap _ x'], cc, }

lemma lt_iff_lt_of_cmp_eq (h : cmp x y = cmp x' y') : x < y ↔ x' < y' :=
by rw [←cmp_eq_lt_iff, ←cmp_eq_lt_iff, h]

lemma gt_iff_gt_of_cmp_eq (h : cmp x y = cmp x' y') : x ≤ y ↔ x' ≤ y' :=
begin
  suffices : ¬ y < x ↔ ¬ y' < x',
  { push_neg at this, assumption },
  rw not_iff_not,
  apply lt_iff_lt_of_cmp_eq,
  rwa cmp_eq_cmp_symm,
end

end cmp

section orderiso

variables {α : Type*} {β : Type*} [linear_order α] [linear_order β]
  (f : α → β) (g : β → α)

/-- To construct an order isomorphism between decidable linear orders `α` and `β`, it
  suffices to construct maps `f : α → β`, `g : β → α`, satisfying
  `∀ (a : α) (b : β), cmp a (g b) = cmp (f a) b`. We think of this as a two-sided Galois
  adjunction. -/
def order_iso_of_cmp_eq_cmp (adj : ∀ (a : α) (b : β), cmp a (g b) = cmp (f a) b) :
  α ≃o β :=
{ to_fun := f,
  inv_fun := g,
  left_inv := begin
    intro a,
    suffices : cmp a (g $ f a) = ordering.eq,
    { symmetry, simpa using this },
    rw adj, simp,
  end,
  right_inv := begin
    intro b,
    suffices : cmp (f $ g b) b = ordering.eq,
    { simpa using this },
    rw ←adj, simp,
  end,
  map_rel_iff' := begin
    intros x y,
    apply gt_iff_gt_of_cmp_eq,
    suffices : y = g (f y),
    { convert adj x (f y), },
    suffices : cmp y (g $ f y) = ordering.eq,
    { simpa using this },
    rw adj, simp,
  end }

end orderiso

section swap

lemma swap_eq_iff {α β} {p : α × β} {q : β × α} : p.swap = q ↔ p = q.swap :=
begin
  split,
  { intro h, rw [←h, prod.swap_swap] },
  { intro h, rw [h, prod.swap_swap] }
end

lemma mem_swap {α β} [decidable_eq α] [decidable_eq β] {s : finset $ α × β} {p : β × α} :
  p ∈ s.image prod.swap ↔ p.swap ∈ s :=
begin
  rw finset.mem_image,
  exact ⟨λ ⟨q, h, he⟩, swap_eq_iff.mp he ▸ h, λ h, ⟨p.swap, h, prod.swap_swap p⟩⟩,
end

lemma sub_swap_iff {α β} [decidable_eq α] [decidable_eq β] {s : finset (α × β)}
  {t : finset $ β × α} : s ⊆ t.image prod.swap ↔ s.image prod.swap ⊆ t :=
begin
  rw [finset.subset_iff, finset.subset_iff],
  split,
  { intros h p hp,
    rw mem_swap at hp,
    specialize h hp,
    rwa [mem_swap, prod.swap_swap] at h, },
  { intros h p hp,
    rw mem_swap,
    apply h,
    rwa [mem_swap, prod.swap_swap], }
end

end swap

-- For any finsets lo, hi, with all elements of lo less than those of hi,
-- there is an element m that separates them.
lemma separation {α : Type*} [linear_order α]
  [densely_ordered α] [no_bot_order α] [no_top_order α] [nonem : nonempty α]
  (lo hi : finset α) (lo_lt_hi : ∀ (x ∈ lo) (y ∈ hi), x < y) :
  ∃ m : α, (∀ x ∈ lo, x < m) ∧ (∀ y ∈ hi, m < y) :=
if nlo : lo.nonempty then
  if nhi : hi.nonempty then -- both sets are nonempty, use density
    exists.elim (exists_between (lo_lt_hi _ (finset.max'_mem _ nlo) _ (finset.min'_mem _ nhi)))
      (λ m hm, ⟨m, λ x hx, lt_of_le_of_lt (finset.le_max' lo x hx) hm.1,
                   λ y hy, lt_of_lt_of_le hm.2 (finset.min'_le hi y hy)⟩)
  else -- upper set is empty, use no_top
    exists.elim (no_top (finset.max' lo nlo)) (λ m hm,
    ⟨m, λ x hx, lt_of_le_of_lt (finset.le_max' lo x hx) hm,
        λ y hy, (nhi ⟨y, hy⟩).elim⟩)
else -- lower set is empty, use no_bot
  if nhi : hi.nonempty then
    exists.elim (no_bot (finset.min' hi nhi)) (λ m hm,
    ⟨m, λ x hx, (nlo ⟨x, hx⟩).elim,
        λ y hy, lt_of_lt_of_le hm (finset.min'_le hi y hy)⟩)
  else -- both sets are empty, use nonempty
    nonem.elim (λ m,
    ⟨m, λ x hx, (nlo ⟨x, hx⟩).elim,
        λ y hy, (nhi ⟨y, hy⟩).elim⟩)

variables (α : Type*) [linear_order α]
  (β : Type*) [linear_order β]

/-- The type of partial order isomorphism between `α` and `β` defined on finite subsets.
    A partial order isomorphism is encoded as a finite subset of `α × β`, consisting
    of pairs which should be identified. -/
def partial_iso : Type _ :=
{ f : finset (α × β) // ∀ (p q ∈ f),
  cmp (prod.fst p) (prod.fst q) = cmp (prod.snd p) (prod.snd q) }

instance : inhabited (partial_iso α β) :=
{ default := ⟨∅, λ p q h, h.elim⟩ }

instance : preorder (partial_iso α β) :=
subtype.preorder _

variables {α β}

/-- A partial isomorphism between `α` and `β` is also a partial isomorphism between `β` and `α`. -/
def partial_iso.symm (f : partial_iso α β) : partial_iso β α :=
{ val := f.val.image prod.swap,
  property := λ p q hp hq, eq.symm $ f.property _ _ (mem_swap.mp hp) (mem_swap.mp hq), }

variables [densely_ordered β] [no_bot_order β] [no_top_order β] [nonempty β]

lemma exists_sep (f : partial_iso α β) (a : α) :
  ∃ b : β, ∀ (p ∈ f.val), cmp (prod.fst p) a = cmp (prod.snd p) b :=
begin
  by_cases h : ∃ b, (a, b) ∈ f.val,
  { cases h with b hb,
    exact ⟨b, λ p hp, f.property _ _ hp hb⟩, },
  cases separation ((f.val.filter $ λ p : α × β, p.fst < a).image prod.snd)
                   ((f.val.filter $ λ p : α × β, a < p.fst).image prod.snd) _
    with b hb,
  swap,
  { intros x hx y hy,
    rw finset.mem_image at hx hy,
    rcases hx with ⟨p, hp1, hp2⟩,
    rcases hy with ⟨q, hq1, hq2⟩,
    rw finset.mem_filter at hp1 hq1,
    rw [←hp2, ←hq2, ←lt_iff_lt_of_cmp_eq (f.property _ _ hp1.1 hq1.1)],
    exact lt_trans hp1.right hq1.right, },
  use b,
  rintros ⟨p1, p2⟩ hp,
  have : p1 ≠ a := λ he, h ⟨p2, he ▸ hp⟩,
  cases lt_or_gt_of_ne this with hl hr,
  { suffices : p1 < a ∧ p2 < b,
      rw [←cmp_eq_lt_iff, ←cmp_eq_lt_iff] at this, cc,
    refine ⟨hl, _⟩,
    apply hb.1,
    rw finset.mem_image,
    use ⟨p1, p2⟩,
    rw finset.mem_filter,
    exact ⟨⟨hp, hl⟩, rfl⟩, },
  { suffices : a < p1 ∧ b < p2,
      rw [←cmp_eq_gt_iff, ←cmp_eq_gt_iff] at this, cc,
    refine ⟨hr, _⟩,
    apply hb.2,
    rw finset.mem_image,
    use ⟨p1, p2⟩,
    rw finset.mem_filter,
    exact ⟨⟨hp, hr⟩, rfl⟩, },
end

/-- The set of partial isomorphism defined on `a : α`, together with a proof that any
    partial isomorphism can be extended to include `a`. -/
def cofinal_left_ins (a : α) : cofinal (partial_iso α β) :=
{ carrier := λ f : partial_iso α β, ∃ b : β, (a, b) ∈ f.val,
  mem_gt :=
  begin
    intro f,
    cases exists_sep f a with b a_b,
    use insert (a,b) f.val,
    { intros p q hp hq,
      rw finset.mem_insert at hp hq,
      cases hp with ha pf;
      cases hq with hb qf,
      { rw [ha, hb], simp },
      { rw [ha, cmp_eq_cmp_symm], exact a_b _ qf, },
      { rw hb, exact a_b _ pf, },
      { exact f.property _ _ pf qf, }, },
    split,
    { use b, apply finset.mem_insert_self, },
    { apply finset.subset_insert, }
  end }

section assume_α_also_dense

variables [densely_ordered α] [no_bot_order α] [no_top_order α] [nonempty α]

/-- The set of partial isomorphism defined on `b : β `, together with a proof that any
    partial isomorphism can be extended to include `b`. We prove this 'by symmetry'. -/
def cofinal_right_ins (b : β) : cofinal (partial_iso α β) :=
{ carrier := λ f, ∃ a, (a, b) ∈ f.val,
  mem_gt :=
  begin
    intro f,
    rcases (cofinal_left_ins b).mem_gt (partial_iso.symm f) with ⟨f', ⟨a, ha⟩, hl⟩,
    use partial_iso.symm f',
    refine ⟨⟨a, mem_swap.mpr ha⟩, _⟩,
    exact sub_swap_iff.mpr hl,
  end, }

variables (α β)

/-- A family of cofinal constraints, indexed by the sum-type `α ⊕ β`. Together these conditions
    ensure that we get a total isomorphism. -/
def to_cofinal : α ⊕ β → cofinal (partial_iso α β)
| (sum.inl a) := cofinal_left_ins a
| (sum.inr b) := cofinal_right_ins b

variables [encodable α] [encodable β]

/-- A set of partial isomorphisms whose limit is a total isomorphism. -/
def our_ideal : ideal (partial_iso α β) := ideal_of_cofinals (default _) (to_cofinal α β)

variables {α}

lemma exists_right (a : α) : ∃ (b : β) (f ∈ our_ideal α β), (a, b) ∈ subtype.val f :=
begin
  rcases cofinal_meets_ideal_of_cofinals (default _) (to_cofinal α β) (sum.inl a)
    with ⟨f, ⟨b, hb⟩, hf⟩,
  exact ⟨b, f, hf, hb⟩,
end

variables (α) {β}

lemma exists_left (b : β) : ∃ (a : α) (f ∈ our_ideal α β), (a, b) ∈ subtype.val f :=
begin
  rcases cofinal_meets_ideal_of_cofinals (default _) (to_cofinal α β) (sum.inr b)
    with ⟨f, ⟨a, ha⟩, hf⟩,
  exact ⟨a, f, hf, ha⟩,
end

variables {α}

/-- The limit of our ideal, as map `α → β`. -/
def left_to_right : α → β := λ a, classical.some (exists_right β a)
/-- The limit of our ideal, as map `β → α`. -/
def right_to_left : β → α := λ b, classical.some (exists_left α b)

lemma adj (a : α) (b : β) : cmp a (right_to_left b) = cmp (left_to_right a) b :=
begin
  rcases classical.some_spec (exists_right β a) with ⟨f, hf, ha⟩,
  rcases classical.some_spec (exists_left α b) with ⟨g, hg, hb⟩,
  rcases (our_ideal α β).directed _ hf _ hg
    with ⟨m, hm, fm, gm⟩,
  exact m.property (a, left_to_right a) (right_to_left b, b) (fm ha) (gm hb),
end

def iso_of_countable_dlo : α ≃o β :=
order_iso_of_cmp_eq_cmp _ _ adj

end assume_α_also_dense

variable [encodable α]

variables (α β)
def our_ideal' : ideal (partial_iso α β) := ideal_of_cofinals (default _) cofinal_left_ins
variables {α β}

lemma exists_left' (a : α) : ∃ (b : β) (f ∈ our_ideal' α β), (a, b) ∈ subtype.val f :=
begin
  rcases cofinal_meets_ideal_of_cofinals (default _ : partial_iso α β) cofinal_left_ins a with
    ⟨f, ⟨b, hb⟩, hf⟩,
  exact ⟨b, f, hf, hb⟩,
end

def order_embedding_of_codomain_dlo_of_countable_domain : α ↪o β :=
{ to_fun := λ a, classical.some (exists_left' a),
  inj' := sorry,
  map_rel_iff' := sorry }
