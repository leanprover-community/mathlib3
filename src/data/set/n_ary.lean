/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import data.set.prod

/-!
# N-ary images of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `finset.image₂`, the binary image of finsets. This is the finset version of
`set.image2`. This is mostly useful to define pointwise operations.

## Notes

This file is very similar to the n-ary section of `data.set.basic`, to `order.filter.n_ary` and to
`data.option.n_ary`. Please keep them in sync.

We do not define `finset.image₃` as its only purpose would be to prove properties of `finset.image₂`
and `set.image2` already fulfills this task.
-/

open function

namespace set
variables {α α' β β' γ γ' δ δ' ε ε' : Type*} {f f' : α → β → γ} {g g' : α → β → γ → δ}
variables {s s' : set α} {t t' : set β} {u u' : set γ} {a a' : α} {b b' : β} {c c' : γ} {d d' : δ}


/-- The image of a binary function `f : α → β → γ` as a function `set α → set β → set γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`.-/
def image2 (f : α → β → γ) (s : set α) (t : set β) : set γ :=
{c | ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c }

@[simp] lemma mem_image2 : c ∈ image2 f s t ↔ ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c := iff.rfl

lemma mem_image2_of_mem (ha : a ∈ s) (hb : b ∈ t) : f a b ∈ image2 f s t := ⟨a, b, ha, hb, rfl⟩

lemma mem_image2_iff (hf : injective2 f) : f a b ∈ image2 f s t ↔ a ∈ s ∧ b ∈ t :=
⟨ by { rintro ⟨a', b', ha', hb', h⟩, rcases hf h with ⟨rfl, rfl⟩, exact ⟨ha', hb'⟩ },
  λ ⟨ha, hb⟩, mem_image2_of_mem ha hb⟩

/-- image2 is monotone with respect to `⊆`. -/
lemma image2_subset (hs : s ⊆ s') (ht : t ⊆ t') : image2 f s t ⊆ image2 f s' t' :=
by { rintro _ ⟨a, b, ha, hb, rfl⟩, exact mem_image2_of_mem (hs ha) (ht hb) }

lemma image2_subset_left (ht : t ⊆ t') : image2 f s t ⊆ image2 f s t' := image2_subset subset.rfl ht

lemma image2_subset_right (hs : s ⊆ s') : image2 f s t ⊆ image2 f s' t :=
image2_subset hs subset.rfl

lemma image_subset_image2_left (hb : b ∈ t) : (λ a, f a b) '' s ⊆ image2 f s t :=
ball_image_of_ball $ λ a ha, mem_image2_of_mem ha hb

lemma image_subset_image2_right (ha : a ∈ s) : f a '' t ⊆ image2 f s t :=
ball_image_of_ball $ λ b, mem_image2_of_mem ha

lemma forall_image2_iff {p : γ → Prop} :
  (∀ z ∈ image2 f s t, p z) ↔ ∀ (x ∈ s) (y ∈ t), p (f x y) :=
⟨λ h x hx y hy, h _ ⟨x, y, hx, hy, rfl⟩, λ h z ⟨x, y, hx, hy, hz⟩, hz ▸ h x hx y hy⟩

@[simp] lemma image2_subset_iff {u : set γ} :
  image2 f s t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), f x y ∈ u :=
forall_image2_iff

variables (f)

@[simp] lemma image_prod : (λ x : α × β, f x.1 x.2) '' s ×ˢ t = image2 f s t :=
ext $ λ a,
⟨ by { rintro ⟨_, _, rfl⟩, exact ⟨_, _, (mem_prod.1 ‹_›).1, (mem_prod.1 ‹_›).2, rfl⟩ },
  by { rintro ⟨_, _, _, _, rfl⟩, exact ⟨(_, _), ⟨‹_›, ‹_›⟩, rfl⟩ }⟩

@[simp] lemma image_uncurry_prod (s : set α) (t : set β) : uncurry f '' s ×ˢ t = image2 f s t :=
image_prod _

@[simp] lemma image2_mk_eq_prod : image2 prod.mk s t = s ×ˢ t := ext $ by simp

@[simp] lemma image2_curry (f : α × β → γ) (s : set α) (t : set β) :
  image2 (λ a b, f (a, b)) s t = f '' s ×ˢ t :=
by simp [←image_uncurry_prod, uncurry]

variables {f}

lemma image2_union_left : image2 f (s ∪ s') t = image2 f s t ∪ image2 f s' t :=
begin
  ext c,
  split,
  { rintro ⟨a, b, ha | ha, hb, rfl⟩; [left, right]; exact ⟨_, _, ‹_›, ‹_›, rfl⟩ },
  { rintro (⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩); refine ⟨_, _, _, ‹_›, rfl⟩;
    simp [mem_union, *] }
end

lemma image2_union_right : image2 f s (t ∪ t') = image2 f s t ∪ image2 f s t' :=
begin
  ext c,
  split,
  { rintro ⟨a, b, ha, h1b|h2b, rfl⟩;[left, right]; exact ⟨_, _, ‹_›, ‹_›, rfl⟩ },
  { rintro (⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩); refine ⟨_, _, ‹_›, _, rfl⟩;
    simp [mem_union, *] }
end

lemma image2_inter_left (hf : injective2 f) : image2 f (s ∩ s') t = image2 f s t ∩ image2 f s' t :=
by simp_rw [←image_uncurry_prod, inter_prod, image_inter hf.uncurry]

lemma image2_inter_right (hf : injective2 f) : image2 f s (t ∩ t') = image2 f s t ∩ image2 f s t' :=
by simp_rw [←image_uncurry_prod, prod_inter, image_inter hf.uncurry]

@[simp] lemma image2_empty_left : image2 f ∅ t = ∅ := ext $ by simp
@[simp] lemma image2_empty_right : image2 f s ∅ = ∅ := ext $ by simp

lemma nonempty.image2 : s.nonempty → t.nonempty → (image2 f s t).nonempty :=
λ ⟨a, ha⟩ ⟨b, hb⟩, ⟨_, mem_image2_of_mem ha hb⟩

@[simp] lemma image2_nonempty_iff : (image2 f s t).nonempty ↔ s.nonempty ∧ t.nonempty :=
⟨λ ⟨_, a, b, ha, hb, _⟩, ⟨⟨a, ha⟩, b, hb⟩, λ h, h.1.image2 h.2⟩

lemma nonempty.of_image2_left (h : (image2 f s t).nonempty) : s.nonempty :=
(image2_nonempty_iff.1 h).1

lemma nonempty.of_image2_right (h : (image2 f s t).nonempty) : t.nonempty :=
(image2_nonempty_iff.1 h).2

@[simp] lemma image2_eq_empty_iff : image2 f s t = ∅ ↔ s = ∅ ∨ t = ∅ :=
by simp_rw [←not_nonempty_iff_eq_empty, image2_nonempty_iff, not_and_distrib]

lemma image2_inter_subset_left : image2 f (s ∩ s') t ⊆ image2 f s t ∩ image2 f s' t :=
by { rintro _ ⟨a, b, ⟨h1a, h2a⟩, hb, rfl⟩, split; exact ⟨_, _, ‹_›, ‹_›, rfl⟩ }

lemma image2_inter_subset_right : image2 f s (t ∩ t') ⊆ image2 f s t ∩ image2 f s t' :=
by { rintro _ ⟨a, b, ha, ⟨h1b, h2b⟩, rfl⟩, split; exact ⟨_, _, ‹_›, ‹_›, rfl⟩ }

@[simp] lemma image2_singleton_left : image2 f {a} t = f a '' t := ext $ λ x, by simp
@[simp] lemma image2_singleton_right : image2 f s {b} = (λ a, f a b) '' s := ext $ λ x, by simp

lemma image2_singleton : image2 f {a} {b} = {f a b} := by simp

@[congr] lemma image2_congr (h : ∀ (a ∈ s) (b ∈ t), f a b = f' a b) :
  image2 f s t = image2 f' s t :=
by { ext, split; rintro ⟨a, b, ha, hb, rfl⟩; refine ⟨a, b, ha, hb, by rw h a ha b hb⟩ }

/-- A common special case of `image2_congr` -/
lemma image2_congr' (h : ∀ a b, f a b = f' a b) : image2 f s t = image2 f' s t :=
image2_congr (λ a _ b _, h a b)

/-- The image of a ternary function `f : α → β → γ → δ` as a function
  `set α → set β → set γ → set δ`. Mathematically this should be thought of as the image of the
  corresponding function `α × β × γ → δ`.
-/
def image3 (g : α → β → γ → δ) (s : set α) (t : set β) (u : set γ) : set δ :=
{d | ∃ a b c, a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d }

@[simp] lemma mem_image3 : d ∈ image3 g s t u ↔ ∃ a b c, a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d :=
iff.rfl

lemma image3_mono (hs : s ⊆ s') (ht : t ⊆ t') (hu : u ⊆ u') : image3 g s t u ⊆ image3 g s' t' u' :=
λ x, Exists₃.imp $ λ a b c ⟨ha, hb, hc, hx⟩, ⟨hs ha, ht hb, hu hc, hx⟩

@[congr] lemma image3_congr (h : ∀ (a ∈ s) (b ∈ t) (c ∈ u), g a b c = g' a b c) :
  image3 g s t u = image3 g' s t u :=
by { ext x,
     split; rintro ⟨a, b, c, ha, hb, hc, rfl⟩; exact ⟨a, b, c, ha, hb, hc, by rw h a ha b hb c hc⟩ }

/-- A common special case of `image3_congr` -/
lemma image3_congr' (h : ∀ a b c, g a b c = g' a b c) : image3 g s t u = image3 g' s t u :=
image3_congr (λ a _ b _ c _, h a b c)

lemma image2_image2_left (f : δ → γ → ε) (g : α → β → δ) :
  image2 f (image2 g s t) u = image3 (λ a b c, f (g a b) c) s t u :=
begin
  ext, split,
  { rintro ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩, refine ⟨a, b, c, ha, hb, hc, rfl⟩ },
  { rintro ⟨a, b, c, ha, hb, hc, rfl⟩, refine ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩ }
end

lemma image2_image2_right (f : α → δ → ε) (g : β → γ → δ) :
  image2 f s (image2 g t u) = image3 (λ a b c, f a (g b c)) s t u :=
begin
  ext, split,
  { rintro ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩, refine ⟨a, b, c, ha, hb, hc, rfl⟩ },
  { rintro ⟨a, b, c, ha, hb, hc, rfl⟩, refine ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩ }
end

lemma image_image2 (f : α → β → γ) (g : γ → δ) :
  g '' image2 f s t = image2 (λ a b, g (f a b)) s t :=
begin
  ext, split,
  { rintro ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩, refine ⟨a, b, ha, hb, rfl⟩ },
  { rintro ⟨a, b, ha, hb, rfl⟩, refine ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩ }
end

lemma image2_image_left (f : γ → β → δ) (g : α → γ) :
  image2 f (g '' s) t = image2 (λ a b, f (g a) b) s t :=
begin
  ext, split,
  { rintro ⟨_, b, ⟨a, ha, rfl⟩, hb, rfl⟩, refine ⟨a, b, ha, hb, rfl⟩ },
  { rintro ⟨a, b, ha, hb, rfl⟩, refine ⟨_, b, ⟨a, ha, rfl⟩, hb, rfl⟩ }
end

lemma image2_image_right (f : α → γ → δ) (g : β → γ) :
  image2 f s (g '' t) = image2 (λ a b, f a (g b)) s t :=
begin
  ext, split,
  { rintro ⟨a, _, ha, ⟨b, hb, rfl⟩, rfl⟩, refine ⟨a, b, ha, hb, rfl⟩ },
  { rintro ⟨a, b, ha, hb, rfl⟩, refine ⟨a, _, ha, ⟨b, hb, rfl⟩, rfl⟩ }
end

lemma image2_swap (f : α → β → γ) (s : set α) (t : set β) :
  image2 f s t = image2 (λ a b, f b a) t s :=
by { ext, split; rintro ⟨a, b, ha, hb, rfl⟩; refine ⟨b, a, hb, ha, rfl⟩ }

@[simp] lemma image2_left (h : t.nonempty) : image2 (λ x y, x) s t = s :=
by simp [nonempty_def.mp h, ext_iff]

@[simp] lemma image2_right (h : s.nonempty) : image2 (λ x y, y) s t = t :=
by simp [nonempty_def.mp h, ext_iff]

lemma image2_assoc {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
  (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
  image2 f (image2 g s t) u = image2 f' s (image2 g' t u) :=
by simp only [image2_image2_left, image2_image2_right, h_assoc]

lemma image2_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : image2 f s t = image2 g t s :=
(image2_swap _ _ _).trans $ by simp_rw h_comm

lemma image2_left_comm {f : α → δ → ε} {g : β → γ → δ} {f' : α → γ → δ'} {g' : β → δ' → ε}
  (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
  image2 f s (image2 g t u) = image2 g' t (image2 f' s u) :=
by { rw [image2_swap f', image2_swap f], exact image2_assoc (λ _ _ _, h_left_comm _ _ _) }

lemma image2_right_comm {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'} {g' : δ' → β → ε}
  (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
  image2 f (image2 g s t) u = image2 g' (image2 f' s u) t :=
by { rw [image2_swap g, image2_swap g'], exact image2_assoc (λ _ _ _, h_right_comm _ _ _) }

lemma image_image2_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
  (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) :
  (image2 f s t).image g = image2 f' (s.image g₁) (t.image g₂) :=
by simp_rw [image_image2, image2_image_left, image2_image_right, h_distrib]

/-- Symmetric statement to `set.image2_image_left_comm`. -/
lemma image_image2_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
  (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) :
  (image2 f s t).image g = image2 f' (s.image g') t :=
(image_image2_distrib h_distrib).trans $ by rw image_id'

/-- Symmetric statement to `set.image_image2_right_comm`. -/
lemma image_image2_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
  (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) :
  (image2 f s t).image g = image2 f' s (t.image g') :=
(image_image2_distrib h_distrib).trans $ by rw image_id'

/-- Symmetric statement to `set.image_image2_distrib_left`. -/
lemma image2_image_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
  (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) :
  image2 f (s.image g) t = (image2 f' s t).image g' :=
(image_image2_distrib_left $ λ a b, (h_left_comm a b).symm).symm

/-- Symmetric statement to `set.image_image2_distrib_right`. -/
lemma image_image2_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
  (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) :
  image2 f s (t.image g) = (image2 f' s t).image g' :=
(image_image2_distrib_right $ λ a b, (h_right_comm a b).symm).symm

/-- The other direction does not hold because of the `s`-`s` cross terms on the RHS. -/
lemma image2_distrib_subset_left {f : α → δ → ε} {g : β → γ → δ} {f₁ : α → β → β'} {f₂ : α → γ → γ'}
  {g' : β' → γ' → ε} (h_distrib : ∀ a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
  image2 f s (image2 g t u) ⊆ image2 g' (image2 f₁ s t) (image2 f₂ s u) :=
begin
  rintro _ ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩,
  rw h_distrib,
  exact mem_image2_of_mem (mem_image2_of_mem ha hb) (mem_image2_of_mem ha hc),
end

/-- The other direction does not hold because of the `u`-`u` cross terms on the RHS. -/
lemma image2_distrib_subset_right {f : δ → γ → ε} {g : α → β → δ} {f₁ : α → γ → α'}
  {f₂ : β → γ → β'} {g' : α' → β' → ε} (h_distrib : ∀ a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
  image2 f (image2 g s t) u ⊆ image2 g' (image2 f₁ s u) (image2 f₂ t u) :=
begin
  rintro _ ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩,
  rw h_distrib,
  exact mem_image2_of_mem (mem_image2_of_mem ha hc) (mem_image2_of_mem hb hc),
end

lemma image_image2_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
  (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
  (image2 f s t).image g = image2 f' (t.image g₁) (s.image g₂) :=
by { rw image2_swap f, exact image_image2_distrib (λ _ _, h_antidistrib _ _) }

/-- Symmetric statement to `set.image2_image_left_anticomm`. -/
lemma image_image2_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
  (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) :
  (image2 f s t).image g = image2 f' (t.image g') s :=
(image_image2_antidistrib h_antidistrib).trans $ by rw image_id'

/-- Symmetric statement to `set.image_image2_right_anticomm`. -/
lemma image_image2_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
  (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) :
  (image2 f s t).image g = image2 f' t (s.image g') :=
(image_image2_antidistrib h_antidistrib).trans $ by rw image_id'

/-- Symmetric statement to `set.image_image2_antidistrib_left`. -/
lemma image2_image_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
  (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
  image2 f (s.image g) t = (image2 f' t s).image g' :=
(image_image2_antidistrib_left $ λ a b, (h_left_anticomm b a).symm).symm

/-- Symmetric statement to `set.image_image2_antidistrib_right`. -/
lemma image_image2_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
  (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
  image2 f s (t.image g) = (image2 f' t s).image g' :=
(image_image2_antidistrib_right $ λ a b, (h_right_anticomm b a).symm).symm

/-- If `a` is a left identity for `f : α → β → β`, then `{a}` is a left identity for
`set.image2 f`. -/
lemma image2_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (t : set β) :
  image2 f {a} t = t :=
by rw [image2_singleton_left, show f a = id, from funext h, image_id]

/-- If `b` is a right identity for `f : α → β → α`, then `{b}` is a right identity for
`set.image2 f`. -/
lemma image2_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (s : set α) :
  image2 f s {b} = s :=
by rw [image2_singleton_right, funext h, image_id']

end set
