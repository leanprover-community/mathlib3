/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.prod

/-!
# N-ary images of finsets

This file defines `finset.image₂`, the binary image of finsets. This is the finset version of
`set.image2`. This is mostly useful to define pointwise operations.

## Notes

This file is very similar to the n-ary section of `data.set.basic` and to `order.filter.n_ary`.
Please keep them in sync.

We do not define `finset.image₃` as its only purpose would be to prove properties of `finset.image₂`
and `set.image2` already fulfills this task.
-/

open function set

namespace finset

variables {α α' β β' γ γ' δ δ' ε ε' : Type*}
  [decidable_eq α'] [decidable_eq β'] [decidable_eq γ] [decidable_eq γ'] [decidable_eq δ]
  [decidable_eq δ'] [decidable_eq ε] [decidable_eq ε']
  {f f' : α → β → γ} {g g' : α → β → γ → δ} {s s' : finset α} {t t' : finset β} {u u' : finset γ}
  {a a' : α} {b b' : β} {c : γ}

/-- The image of a binary function `f : α → β → γ` as a function `finset α → finset β → finset γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def image₂ (f : α → β → γ) (s : finset α) (t : finset β) : finset γ :=
(s.product t).image $ uncurry f

@[simp] lemma mem_image₂ : c ∈ image₂ f s t ↔ ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c :=
by simp [image₂, and_assoc]

@[simp, norm_cast] lemma coe_image₂ (f : α → β → γ) (s : finset α) (t : finset β) :
  (image₂ f s t : set γ) = set.image2 f s t :=
set.ext $ λ _, mem_image₂

lemma card_image₂_le (f : α → β → γ) (s : finset α) (t : finset β) :
  (image₂ f s t).card ≤ s.card * t.card :=
card_image_le.trans_eq $ card_product _ _

lemma card_image₂ (hf : injective2 f) (s : finset α) (t : finset β) :
  (image₂ f s t).card = s.card * t.card :=
(card_image_of_injective _ hf.uncurry).trans $ card_product _ _

lemma mem_image₂_of_mem (ha : a ∈ s) (hb : b ∈ t) : f a b ∈ image₂ f s t :=
mem_image₂.2 ⟨a, b, ha, hb, rfl⟩

lemma mem_image₂_iff (hf : injective2 f) : f a b ∈ image₂ f s t ↔ a ∈ s ∧ b ∈ t :=
by rw [←mem_coe, coe_image₂, mem_image2_iff hf, mem_coe, mem_coe]

lemma image₂_subset (hs : s ⊆ s') (ht : t ⊆ t') : image₂ f s t ⊆ image₂ f s' t' :=
by { rw [←coe_subset, coe_image₂, coe_image₂], exact image2_subset hs ht }

lemma image₂_subset_left (ht : t ⊆ t') : image₂ f s t ⊆ image₂ f s t' := image₂_subset subset.rfl ht

lemma image₂_subset_right (hs : s ⊆ s') : image₂ f s t ⊆ image₂ f s' t :=
image₂_subset hs subset.rfl

lemma image_subset_image₂_left (hb : b ∈ t) : (λ a, f a b) '' s ⊆ image₂ f s t :=
ball_image_of_ball $ λ a ha, mem_image₂_of_mem ha hb

lemma image_subset_image₂_right (ha : a ∈ s) : f a '' t ⊆ image₂ f s t :=
ball_image_of_ball $ λ b, mem_image₂_of_mem ha

lemma forall_image₂_iff {p : γ → Prop} : (∀ z ∈ image₂ f s t, p z) ↔ ∀ (x ∈ s) (y ∈ t), p (f x y) :=
by simp_rw [←mem_coe, coe_image₂, forall_image2_iff]

@[simp] lemma image₂_subset_iff : image₂ f s t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), f x y ∈ u :=
forall_image₂_iff

@[simp] lemma image₂_nonempty_iff : (image₂ f s t).nonempty ↔ s.nonempty ∧ t.nonempty :=
by { rw [←coe_nonempty, coe_image₂], exact image2_nonempty_iff }

lemma nonempty.image₂ (hs : s.nonempty) (ht : t.nonempty) : (image₂ f s t).nonempty :=
image₂_nonempty_iff.2 ⟨hs, ht⟩

lemma nonempty.of_image₂_left (h : (image₂ f s t).nonempty) : s.nonempty :=
(image₂_nonempty_iff.1 h).1

lemma nonempty.of_image₂_right (h : (image₂ f s t).nonempty) : t.nonempty :=
(image₂_nonempty_iff.1 h).2

@[simp] lemma image₂_empty_left : image₂ f ∅ t = ∅ := coe_injective $ by simp
@[simp] lemma image₂_empty_right : image₂ f s ∅ = ∅ := coe_injective $ by simp
@[simp] lemma image₂_eq_empty_iff : image₂ f s t = ∅ ↔ s = ∅ ∨ t = ∅ :=
by simp_rw [←not_nonempty_iff_eq_empty, image₂_nonempty_iff, not_and_distrib]

@[simp] lemma image₂_singleton_left : image₂ f {a} t = t.image (f a) := ext $ λ x, by simp
@[simp] lemma image₂_singleton_right : image₂ f s {b} = s.image (λ a, f a b) := ext $ λ x, by simp

lemma image₂_singleton : image₂ f {a} {b} = {f a b} := by simp

lemma image₂_union_left [decidable_eq α] : image₂ f (s ∪ s') t = image₂ f s t ∪ image₂ f s' t :=
coe_injective $ by { push_cast, exact image2_union_left }

lemma image₂_union_right [decidable_eq β] : image₂ f s (t ∪ t') = image₂ f s t ∪ image₂ f s t' :=
coe_injective $ by { push_cast, exact image2_union_right }

lemma image₂_inter_subset_left [decidable_eq α] :
  image₂ f (s ∩ s') t ⊆ image₂ f s t ∩ image₂ f s' t :=
coe_subset.1 $ by { push_cast, exact image2_inter_subset_left }

lemma image₂_inter_subset_right [decidable_eq β] :
  image₂ f s (t ∩ t') ⊆ image₂ f s t ∩ image₂ f s t' :=
coe_subset.1 $ by { push_cast, exact image2_inter_subset_right }

lemma image₂_congr (h : ∀ (a ∈ s) (b ∈ t), f a b = f' a b) : image₂ f s t = image₂ f' s t :=
coe_injective $ by { push_cast, exact image2_congr h }

/-- A common special case of `image₂_congr` -/
lemma image₂_congr' (h : ∀ a b, f a b = f' a b) : image₂ f s t = image₂ f' s t :=
image₂_congr $ λ a _ b _, h a b

lemma subset_image₂ {s : set α} {t : set β} (hu : ↑u ⊆ image2 f s t) :
  ∃ (s' : finset α) (t' : finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ image₂ f s' t' :=
begin
  apply finset.induction_on' u,
  { exact ⟨∅, ∅, set.empty_subset _, set.empty_subset _, empty_subset _⟩ },
  rintro a u ha _ _ ⟨s', t', hs, hs', h⟩,
  obtain ⟨x, y, hx, hy, ha⟩ := hu ha,
  haveI := classical.dec_eq α,
  haveI := classical.dec_eq β,
  refine ⟨insert x s', insert y t', _⟩,
  simp_rw [coe_insert, set.insert_subset],
  exact ⟨⟨hx, hs⟩, ⟨hy, hs'⟩, insert_subset.2 ⟨mem_image₂.2 ⟨x, y, mem_insert_self _ _,
    mem_insert_self _ _, ha⟩, h.trans $ image₂_subset (subset_insert _ _) $ subset_insert _ _⟩⟩,
end

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `finset.image₂` of those operations.

The proof pattern is `image₂_lemma operation_lemma`. For example, `image₂_comm mul_comm` proves that
`image₂ (*) f g = image₂ (*) g f` in a `comm_semigroup`.
-/

lemma image_image₂ (f : α → β → γ) (g : γ → δ) :
  (image₂ f s t).image g = image₂ (λ a b, g (f a b)) s t :=
coe_injective $ by { push_cast, exact image_image2 _ _ }

lemma image₂_image_left (f : γ → β → δ) (g : α → γ) :
  image₂ f (s.image g) t = image₂ (λ a b, f (g a) b) s t :=
coe_injective $ by { push_cast, exact image2_image_left _ _ }

lemma image₂_image_right (f : α → γ → δ) (g : β → γ) :
  image₂ f s (t.image g) = image₂ (λ a b, f a (g b)) s t :=
coe_injective $ by { push_cast, exact image2_image_right _ _ }

lemma image₂_swap (f : α → β → γ) (s : finset α) (t : finset β) :
  image₂ f s t = image₂ (λ a b, f b a) t s :=
coe_injective $ by { push_cast, exact image2_swap _ _ _ }

@[simp] lemma image₂_left [decidable_eq α] (h : t.nonempty) : image₂ (λ x y, x) s t = s :=
coe_injective $ by { push_cast, exact image2_left h }

@[simp] lemma image₂_right [decidable_eq β] (h : s.nonempty) : image₂ (λ x y, y) s t = t :=
coe_injective $ by { push_cast, exact image2_right h }

lemma image₂_assoc {γ : Type*} {u : finset γ} {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε}
  {g' : β → γ → ε'} (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
  image₂ f (image₂ g s t) u = image₂ f' s (image₂ g' t u) :=
coe_injective $ by { push_cast, exact image2_assoc h_assoc }

lemma image₂_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : image₂ f s t = image₂ g t s :=
(image₂_swap _ _ _).trans $ by simp_rw h_comm

lemma image₂_left_comm {γ : Type*} {u : finset γ} {f : α → δ → ε} {g : β → γ → δ} {f' : α → γ → δ'}
  {g' : β → δ' → ε} (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
  image₂ f s (image₂ g t u) = image₂ g' t (image₂ f' s u) :=
coe_injective $ by { push_cast, exact image2_left_comm h_left_comm }

lemma image₂_right_comm {γ : Type*} {u : finset γ} {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'}
  {g' : δ' → β → ε} (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
  image₂ f (image₂ g s t) u = image₂ g' (image₂ f' s u) t :=
coe_injective $ by { push_cast, exact image2_right_comm h_right_comm }

lemma image_image₂_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
  (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) :
  (image₂ f s t).image g = image₂ f' (s.image g₁) (t.image g₂) :=
coe_injective $ by { push_cast, exact image_image2_distrib h_distrib }

/-- Symmetric of `finset.image₂_image_left_comm`. -/
lemma image_image₂_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
  (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) :
  (image₂ f s t).image g = image₂ f' (s.image g') t :=
coe_injective $ by { push_cast, exact image_image2_distrib_left h_distrib }

/-- Symmetric of `finset.image_image₂_right_comm`. -/
lemma image_image₂_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
  (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) :
  (image₂ f s t).image g = image₂ f' s (t.image g') :=
coe_injective $ by { push_cast, exact image_image2_distrib_right h_distrib }

/-- Symmetric of `finset.image_image₂_distrib_left`. -/
lemma image₂_image_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
  (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) :
  image₂ f (s.image g) t = (image₂ f' s t).image g' :=
(image_image₂_distrib_left $ λ a b, (h_left_comm a b).symm).symm

/-- Symmetric of `finset.image_image₂_distrib_right`. -/
lemma image_image₂_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
  (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) :
  image₂ f s (t.image g) = (image₂ f' s t).image g' :=
(image_image₂_distrib_right $ λ a b, (h_right_comm a b).symm).symm

/-- The other direction does not hold because of the `s`-`s` cross terms on the RHS. -/
lemma image₂_distrib_subset_left {γ : Type*} {u : finset γ} {f : α → δ → ε} {g : β → γ → δ}
  {f₁ : α → β → β'} {f₂ : α → γ → γ'} {g' : β' → γ' → ε}
  (h_distrib : ∀ a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
  image₂ f s (image₂ g t u) ⊆ image₂ g' (image₂ f₁ s t) (image₂ f₂ s u) :=
coe_subset.1 $ by { push_cast, exact set.image2_distrib_subset_left h_distrib }

/-- The other direction does not hold because of the `u`-`u` cross terms on the RHS. -/
lemma image₂_distrib_subset_right {γ : Type*} {u : finset γ} {f : δ → γ → ε} {g : α → β → δ}
  {f₁ : α → γ → α'} {f₂ : β → γ → β'} {g' : α' → β' → ε}
  (h_distrib : ∀ a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
  image₂ f (image₂ g s t) u ⊆ image₂ g' (image₂ f₁ s u) (image₂ f₂ t u) :=
coe_subset.1 $ by { push_cast, exact set.image2_distrib_subset_right h_distrib }

lemma image_image₂_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
  (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
  (image₂ f s t).image g = image₂ f' (t.image g₁) (s.image g₂) :=
by { rw image₂_swap f, exact image_image₂_distrib (λ _ _, h_antidistrib _ _) }

/-- Symmetric of `finset.image₂_image_left_anticomm`. -/
lemma image_image₂_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
  (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) :
  (image₂ f s t).image g = image₂ f' (t.image g') s :=
coe_injective $ by { push_cast, exact image_image2_antidistrib_left h_antidistrib }

/-- Symmetric of `finset.image_image₂_right_anticomm`. -/
lemma image_image₂_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
  (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) :
  (image₂ f s t).image g = image₂ f' t (s.image g') :=
coe_injective $ by { push_cast, exact image_image2_antidistrib_right h_antidistrib }

/-- Symmetric of `finset.image_image₂_antidistrib_left`. -/
lemma image₂_image_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
  (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
  image₂ f (s.image g) t = (image₂ f' t s).image g' :=
(image_image₂_antidistrib_left $ λ a b, (h_left_anticomm b a).symm).symm

/-- Symmetric of `finset.image_image₂_antidistrib_right`. -/
lemma image_image₂_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
  (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
  image₂ f s (t.image g) = (image₂ f' t s).image g' :=
(image_image₂_antidistrib_right $ λ a b, (h_right_anticomm b a).symm).symm

end finset
