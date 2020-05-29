import order.rasiowa_sikorski
import data.finset

noncomputable theory
open_locale classical

section cmp

variables {α : Type*} [decidable_linear_order α] (x y : α)

@[simp] lemma cmp_eq_lt_iff : cmp x y = ordering.lt ↔ x < y :=
ordering.compares.eq_lt $ cmp_compares x y

@[simp] lemma cmp_eq_eq_iff : cmp x y = ordering.eq ↔ x = y :=
ordering.compares.eq_eq $ cmp_compares x y

@[simp] lemma cmp_eq_gt_iff : cmp x y = ordering.gt ↔ x > y :=
ordering.compares.eq_gt $ cmp_compares x y

@[simp] lemma cmp_self_eq_eq : cmp x x = ordering.eq :=
(ordering.compares.eq_eq (cmp_compares x x)).mpr rfl

variables {x y} {β : Type*} [decidable_linear_order β] {x' y' : β}

lemma cmp_eq_cmp_symm : cmp x y = cmp x' y' ↔ cmp y x = cmp y' x' :=
by { split, rw [←cmp_swap _ y, ←cmp_swap _ y'], cc,
  rw [←cmp_swap _ x, ←cmp_swap _ x'], cc, }

lemma lt_iff_lt_of_cmp_eq (h : cmp x y = cmp x' y') :
  x < y ↔ x' < y' :=
by rw [←cmp_eq_lt_iff, ←cmp_eq_lt_iff, h]

lemma gt_iff_gt_of_cmp_eq (h : cmp x y = cmp x' y') :
  x ≤ y ↔ x' ≤ y' :=
begin
  suffices : ¬ y < x ↔ ¬ y' < x',
  { push_neg at this, assumption },
  rw not_iff_not,
  apply lt_iff_lt_of_cmp_eq,
  rwa cmp_eq_cmp_symm,
end

end cmp

section orderiso

variables {α : Type*} {β : Type*} [decidable_linear_order α] [decidable_linear_order β]
  (f : α → β) (g : β → α)

def order_iso_of_cmp_eq_cmp (adj : ∀ a b, cmp a (g b) = cmp (f a) b) :
  ((≤) : α → α → Prop) ≃o ((≤) : β → β → Prop) :=
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
  ord' := begin
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

lemma sub_swap_iff {α β} [decidable_eq α] [decidable_eq β] {s : finset $ α × β}
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
lemma separation {α : Type*} [decidable_linear_order α]
  [densely_ordered α] [no_bot_order α] [no_top_order α] [nonem : nonempty α]
  (lo hi : finset α) (lo_lt_hi : ∀ (x ∈ lo) (y ∈ hi), x < y) :
  ∃ m : α, (∀ x ∈ lo, x < m) ∧ (∀ y ∈ hi, m < y) :=
if nlo : lo.nonempty then
  if nhi : hi.nonempty then
    exists.elim (dense (lo_lt_hi _ (finset.max'_mem _ nlo) _ (finset.min'_mem _ nhi))) (λ m hm,
    ⟨m, λ x hx, lt_of_le_of_lt (finset.le_max' lo nlo x hx) hm.1,
        λ y hy, lt_of_lt_of_le hm.2 (finset.min'_le hi nhi y hy)⟩)
  else
    exists.elim (no_top (finset.max' lo nlo)) (λ m hm,
    ⟨m, λ x hx, lt_of_le_of_lt (finset.le_max' lo nlo x hx) hm,
        λ y hy, (nhi ⟨y, hy⟩).elim⟩)
else
  if nhi : hi.nonempty then
    exists.elim (no_bot (finset.min' hi nhi)) (λ m hm,
    ⟨m, λ x hx, (nlo ⟨x, hx⟩).elim,
        λ y hy, lt_of_lt_of_le hm (finset.min'_le hi nhi y hy)⟩)
  else
    nonem.elim (λ m,
    ⟨m, λ x hx, (nlo ⟨x, hx⟩).elim,
        λ y hy, (nhi ⟨y, hy⟩).elim⟩)

variables (α : Type*) [decidable_linear_order α]
  [densely_ordered α] [no_bot_order α] [no_top_order α] [nonempty α]
  (β : Type*) [decidable_linear_order β]
  [densely_ordered β] [no_bot_order β] [no_top_order β] [nonempty β]

/-- The type of endpoint-preserving order-isomorphisms between finite subsets of α and β. -/
def partial_iso : Type _ :=
{ funset : finset (α × β) // ∀ (p q ∈ funset),
  cmp (prod.fst p) (prod.fst q) = cmp (prod.snd p) (prod.snd q) }

instance : inhabited (partial_iso α β) :=
{ default := ⟨∅, λ p q h, h.elim⟩ }

instance : preorder (partial_iso α β) :=
{ le := λ f g, f.val ⊆ g.val,
  le_refl := λ f, finset.subset.refl _,
  le_trans := λ f g h, finset.subset.trans }

variables {α β}

def pswap (f : partial_iso α β) : partial_iso β α :=
{ val := f.val.image prod.swap,
  property := λ p q hp hq, eq.symm $ f.property _ _ (mem_swap.mp hp) (mem_swap.mp hq), }

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
  { suffices : p1 > a ∧ p2 > b,
      rw [←cmp_eq_gt_iff, ←cmp_eq_gt_iff] at this, cc,
    refine ⟨hr, _⟩,
    apply hb.2,
    rw finset.mem_image,
    use ⟨p1, p2⟩,
    rw finset.mem_filter,
    exact ⟨⟨hp, hr⟩, rfl⟩, },
end

def cofinal_left_ins (a : α) : { D : set (partial_iso α β) // cofinal D } :=
{ val := λ f : partial_iso α β, ∃ b : β, (a, b) ∈ f.val,
  property :=
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

def cofinal_right_ins (b : β) : { D : set (partial_iso α β) // cofinal D} :=
{ val := λ f, ∃ a, (a, b) ∈ f.val,
  property :=
  begin
    intro f,
    rcases (cofinal_left_ins b).property (pswap f) with ⟨f', ⟨a, ha⟩, hl⟩,
    use pswap f',
    refine ⟨⟨a, mem_swap.mpr ha⟩, _⟩,
    exact sub_swap_iff.mpr hl,
  end, }

variables (α β)

def to_cofinal : α ⊕ β → { D : set (partial_iso α β) // cofinal D}
| (sum.inl a) := cofinal_left_ins a
| (sum.inr b) := cofinal_right_ins b

variables [encodable α] [encodable β]

def my_cofilter : set (partial_iso α β) := rasiowa_sikorski.witness (default _) (to_cofinal α β)

variables {α}

lemma exists_right (a : α) : ∃ (b : β) (f ∈ my_cofilter α β), (a, b) ∈ subtype.val f :=
begin
  rcases rasiowa_sikorski.meets (default _) (to_cofinal α β) (sum.inl a) with ⟨f, hf, b, hb⟩,
  exact ⟨b, f, hf, hb⟩,
end

variables (α) {β}

lemma exists_left (b : β) : ∃ (a : α) (f ∈ my_cofilter α β), (a, b) ∈ subtype.val f :=
begin
  rcases rasiowa_sikorski.meets (default _) (to_cofinal α β) (sum.inr b) with ⟨f, hf, a, ha⟩,
  exact ⟨a, f, hf, ha⟩,
end

variables {α}

def α_to_β : α → β := λ a, classical.some (exists_right β a)
def β_to_α : β → α := λ b, classical.some (exists_left α b)

lemma adj (a : α) (b : β) : cmp a (β_to_α b) = cmp (α_to_β a) b :=
begin
  rcases classical.some_spec (exists_right β a) with ⟨f, hf, ha⟩,
  rcases classical.some_spec (exists_left α b) with ⟨g, hg, hb⟩,
  rcases rasiowa_sikorski.directed_on (default _) (to_cofinal α β) _ hf _ hg
    with ⟨m, hm, fm, gm⟩,
  exact m.property (a, α_to_β a) (β_to_α b, b) (fm ha) (gm hb),
end
