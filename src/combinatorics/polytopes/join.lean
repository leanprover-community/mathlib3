import combinatorics.polytopes.basic

-- Just a test... this entire thing might go maybe.

universe u

-- Yaël: Here's the one instance I would provide:

instance {α β : Type*} [preorder α] [order_bot α] [grade_order α] [preorder β] [order_bot β]
  [grade_order β] : grade_order (α × β) :=
{ grade := λ a, grade a.fst + grade a.snd,
  grade_bot := begin
    convert (zero_add _).trans grade_bot,
    exact grade_bot,
  end,
  strict_mono := begin
    sorry
  end,
  hcovers := sorry }

namespace polytope

-- generalize to two universes?
def join (α β : Type u) : Type u := α × β

notation α ` ⋈ `:50 β:50 := join α β

namespace join

instance {α β : Type u} [has_le α] [has_le β] : has_le (α ⋈ β) :=
prod.has_le α β

instance {α β : Type u} [preorder α] [preorder β] : preorder (α ⋈ β) :=
prod.preorder α β

instance {α β : Type u} [partial_order α] [partial_order β] : partial_order (α ⋈ β) :=
prod.partial_order α β

instance {α β : Type u} [has_le α] [order_bot α] [has_le β] [order_bot β] : order_bot (α ⋈ β) :=
prod.order_bot α β

instance {α β : Type u} [has_le α] [order_top α] [has_le β] [order_top β] : order_top (α ⋈ β) :=
prod.order_top α β

lemma lt_iff_lt_either {α β : Type u} [partial_order α] [partial_order β] (a b : α ⋈ β) :
  a < b ↔ a.fst < b.fst ∧ a.snd ≤ b.snd ∨ a.fst ≤ b.fst ∧ a.snd < b.snd :=
begin
  split,
    { intro h,
      cases le_of_lt h with h₁ h₂,
      cases eq_or_lt_of_le h₁ with h₁' h₁',
      cases eq_or_lt_of_le h₂ with h₂' h₂',
      exact ((ne_of_lt h) (prod.ext h₁' h₂')).elim,
      exact or.inr ⟨h₁, h₂'⟩,
      exact or.inl ⟨h₁', h₂⟩ },
  intro h,
  rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩,
    { rw lt_iff_le_and_ne,
      refine ⟨⟨le_of_lt hl, hr⟩, λ h, _⟩,
      rw h at hl,
      exact (ne_of_lt hl) rfl },
  rw lt_iff_le_and_ne,
  refine ⟨⟨hl, le_of_lt hr⟩, λ h, _⟩,
  rw h at hr,
  exact (ne_of_lt hr) rfl,
end

section

variables {α β : Type u} [partial_order α] [partial_order β] {a b : α ⋈ β}

@[simp]
lemma le_of_le_and_le : a.fst ≤ b.fst → a.snd ≤ b.snd → a ≤ b :=
λ hlt hle, ⟨hlt, hle⟩

@[simp]
lemma lt_of_lt_and_le : a.fst < b.fst → a.snd ≤ b.snd → a < b :=
λ hlt hle, (lt_iff_lt_either _ _).mpr (or.inl ⟨hlt, hle⟩)

@[simp]
lemma lt_of_le_and_lt : a.fst ≤ b.fst → a.snd < b.snd → a < b :=
λ hle hlt, (lt_iff_lt_either _ _).mpr (or.inr ⟨hle, hlt⟩)

end

lemma cover_iff_cover_either {α β : Type u} [partial_order α] [partial_order β] (a b : α ⋈ β) :
  a ⋖ b ↔ a.fst ⋖ b.fst ∧ a.snd = b.snd ∨ a.fst = b.fst ∧ a.snd ⋖ b.snd :=
begin
  split,
    { rintro ⟨hl, hr⟩,
      have hlt := λ hf hs, (hr ⟨a.fst, b.snd⟩ ⟨lt_of_le_and_lt (le_refl _) hs, lt_of_lt_and_le hf (le_refl _)⟩),
      rcases (lt_iff_lt_either _ _).mp hl with ⟨hf, hs⟩ | ⟨hf, hs⟩,
        { refine or.inl ⟨⟨hf, λ c ⟨hcl, hcr⟩, hr ⟨c, b.snd⟩ ⟨lt_of_lt_and_le hcl hs, lt_of_lt_and_le hcr (le_refl _)⟩⟩, _⟩,
          cases eq_or_lt_of_le hs with hs hs, { exact hs },
          exact (hlt hf hs).elim },
      refine or.inr ⟨_, ⟨hs, λ c ⟨hcl, hcr⟩, hr ⟨a.fst, c⟩ ⟨ lt_of_le_and_lt (le_of_eq rfl) hcl, lt_of_le_and_lt hf hcr⟩ ⟩⟩,
      cases eq_or_lt_of_le hf with hf hf, { exact hf },
      exact (hlt hf hs).elim },
  intro h,
  cases h with h h, {
    split, {
      exact lt_of_lt_and_le h.left.left (le_of_eq h.right),
    },
    intros z hz,
    apply h.left.right z.fst,
    cases hz with hzl hzr,
      rw lt_iff_lt_either at hzl,
      rw lt_iff_lt_either at hzr,
      cases hzl with hzl hzl, {
        use hzl.left,
        cases hzr with hzr hzr, {
          use hzr.left,
        },
        exfalso,sorry,
      },
      sorry,
        },
sorry
end

instance {α β : Type u} [preorder α] [graded α] [preorder β] [graded β] : graded (α ⋈ β) :=
{ grade := λ a, graded.grade a.fst + graded.grade a.snd,
  grade_bot := begin
    have : (⊥ : α ⋈ β).fst = (⊥ : α) := rfl,
    rw this,
    have : (⊥ : α ⋈ β).snd = (⊥ : β) := rfl,
    rw this,
    repeat { rw graded.grade_bot },
  end,
  strict_mono := begin
    sorry
  end,
  hcovers := sorry }

end join

end polytope
