/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.filter.prod

/-!
# N-ary maps of filter

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the binary and ternary maps of filters. This is mostly useful to define pointwise
operations on filters.

## Main declarations

* `filter.map₂`: Binary map of filters.
* `filter.map₃`: Ternary map of filters.

## Notes

This file is very similar to `data.set.n_ary`, `data.finset.n_ary` and `data.option.n_ary`. Please
keep them in sync.
-/

open function set
open_locale filter

namespace filter
variables {α α' β β' γ γ' δ δ' ε ε' : Type*} {m : α → β → γ} {f f₁ f₂ : filter α}
  {g g₁ g₂ : filter β} {h h₁ h₂ : filter γ} {s s₁ s₂ : set α} {t t₁ t₂ : set β} {u : set γ}
  {v : set δ} {a : α} {b : β} {c : γ}

/-! ### `filter.map₂` -/

/-- The image of a binary function `m : α → β → γ` as a function `filter α → filter β → filter γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def map₂ (m : α → β → γ) (f : filter α) (g : filter β) : filter γ :=
{ sets := {s | ∃ (u ∈ f) (v ∈ g), image2 m u v ⊆ s},
  univ_sets := ⟨univ, univ_sets _, univ, univ_sets _, subset_univ _⟩,
  sets_of_superset := λ s t ⟨u, hu, v, hv, hs⟩ hst, ⟨u, hu, v, hv, hs.trans hst⟩,
  inter_sets := λ s t ⟨us, hus, vs, hvs, hs⟩ ⟨ut, hut, vt, hvt, ht⟩,
    ⟨us ∩ ut, inter_mem hus hut, vs ∩ vt, inter_mem hvs hvt, subset_inter
      ((image2_subset (inter_subset_left _ _) (inter_subset_left _ _)).trans hs)
      ((image2_subset (inter_subset_right _ _) (inter_subset_right _ _)).trans ht)⟩ }

@[simp] lemma mem_map₂_iff : u ∈ map₂ m f g ↔ ∃ (s ∈ f) (t ∈ g), image2 m s t ⊆ u := iff.rfl

lemma image2_mem_map₂ (hs : s ∈ f) (ht : t ∈ g) : image2 m s t ∈ map₂ m f g :=
⟨_, hs, _, ht, subset.rfl⟩

lemma map_prod_eq_map₂ (m : α → β → γ) (f : filter α) (g : filter β) :
  map (λ p : α × β, m p.1 p.2) (f ×ᶠ g) = map₂ m f g :=
begin
  ext s,
  simp only [mem_map, mem_prod_iff, prod_subset_iff, mem_preimage, mem_map₂_iff, image2_subset_iff]
end

lemma map_prod_eq_map₂' (m : α × β → γ) (f : filter α) (g : filter β) :
  map m (f ×ᶠ g) = map₂ (λ a b, m (a, b)) f g :=
by { refine eq.trans _ (map_prod_eq_map₂ (curry m) f g), ext, simp }

@[simp] lemma map₂_mk_eq_prod (f : filter α) (g : filter β) : map₂ prod.mk f g = f ×ᶠ g :=
by simp only [← map_prod_eq_map₂, map_id', prod.mk.eta]

@[simp] lemma map₂_curry (m : α × β → γ) (f : filter α) (g : filter β) :
  map₂ (curry m) f g = (f ×ᶠ g).map m :=
(map_prod_eq_map₂' _ _ _).symm

@[simp] lemma map_uncurry_prod (m : α → β → γ) (f : filter α) (g : filter β) :
  (f ×ᶠ g).map (uncurry m) = map₂ m f g :=
map_prod_eq_map₂ _ _ _

lemma map₂_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : map₂ m f₁ g₁ ≤ map₂ m f₂ g₂ :=
λ _ ⟨s, hs, t, ht, hst⟩, ⟨s, hf hs, t, hg ht, hst⟩

lemma map₂_mono_left (h : g₁ ≤ g₂) : map₂ m f g₁ ≤ map₂ m f g₂ := map₂_mono subset.rfl h
lemma map₂_mono_right (h : f₁ ≤ f₂) : map₂ m f₁ g ≤ map₂ m f₂ g := map₂_mono h subset.rfl

@[simp] lemma le_map₂_iff {h : filter γ} :
  h ≤ map₂ m f g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → image2 m s t ∈ h :=
⟨λ H s hs t ht, H $ image2_mem_map₂ hs ht, λ H u ⟨s, hs, t, ht, hu⟩, mem_of_superset (H hs ht) hu⟩

@[simp] lemma map₂_eq_bot_iff : map₂ m f g = ⊥ ↔ f = ⊥ ∨ g = ⊥ :=
by simp only [← map_prod_eq_map₂, map_eq_bot_iff, prod_eq_bot]

@[simp] lemma map₂_bot_left : map₂ m ⊥ g = ⊥ := map₂_eq_bot_iff.2 $ or.inl rfl

@[simp] lemma map₂_bot_right : map₂ m f ⊥ = ⊥ := map₂_eq_bot_iff.2 $ or.inr rfl

@[simp] lemma map₂_ne_bot_iff : (map₂ m f g).ne_bot ↔ f.ne_bot ∧ g.ne_bot :=
by { simp_rw ne_bot_iff, exact map₂_eq_bot_iff.not.trans not_or_distrib }

lemma ne_bot.map₂ (hf : f.ne_bot) (hg : g.ne_bot) : (map₂ m f g).ne_bot :=
map₂_ne_bot_iff.2 ⟨hf, hg⟩

lemma ne_bot.of_map₂_left (h : (map₂ m f g).ne_bot) : f.ne_bot := (map₂_ne_bot_iff.1 h).1
lemma ne_bot.of_map₂_right (h : (map₂ m f g).ne_bot) : g.ne_bot := (map₂_ne_bot_iff.1 h).2

lemma map₂_sup_left : map₂ m (f₁ ⊔ f₂) g = map₂ m f₁ g ⊔ map₂ m f₂ g :=
by simp only [← map_prod_eq_map₂, sup_prod, map_sup]

lemma map₂_sup_right : map₂ m f (g₁ ⊔ g₂) = map₂ m f g₁ ⊔ map₂ m f g₂ :=
by simp only [← map_prod_eq_map₂, prod_sup, map_sup]

lemma map₂_inf_subset_left : map₂ m (f₁ ⊓ f₂) g ≤ map₂ m f₁ g ⊓ map₂ m f₂ g :=
le_inf (map₂_mono_right inf_le_left) (map₂_mono_right inf_le_right)

lemma map₂_inf_subset_right : map₂ m f (g₁ ⊓ g₂) ≤ map₂ m f g₁ ⊓ map₂ m f g₂ :=
le_inf (map₂_mono_left inf_le_left) (map₂_mono_left inf_le_right)

@[simp] lemma map₂_pure_left : map₂ m (pure a) g = g.map (λ b, m a b) :=
by simp only [← map_prod_eq_map₂, pure_prod, map_map]

@[simp] lemma map₂_pure_right : map₂ m f (pure b) = f.map (λ a, m a b) :=
by simp only [← map_prod_eq_map₂, prod_pure, map_map]

lemma map₂_pure : map₂ m (pure a) (pure b) = pure (m a b) := by rw [map₂_pure_right, map_pure]

lemma map₂_swap (m : α → β → γ) (f : filter α) (g : filter β) :
  map₂ m f g = map₂ (λ a b, m b a) g f :=
by { ext u, split; rintro ⟨s, hs, t, ht, hu⟩; refine ⟨t, ht, s, hs, by rwa image2_swap⟩ }

@[simp] lemma map₂_left (h : g.ne_bot) : map₂ (λ x y, x) f g = f :=
by rw [← map_prod_eq_map₂, map_fst_prod]

@[simp] lemma map₂_right (h : f.ne_bot) : map₂ (λ x y, y) f g = g := by rw [map₂_swap, map₂_left h]

lemma map_map₂ (m : α → β → γ) (n : γ → δ) : (map₂ m f g).map n = map₂ (λ a b, n (m a b)) f g :=
by simp only [← map_prod_eq_map₂, map_map]

lemma map₂_map_left (m : γ → β → δ) (n : α → γ) :
  map₂ m (f.map n) g = map₂ (λ a b, m (n a) b) f g :=
by { rw [← map_prod_eq_map₂, ← map_prod_eq_map₂, prod_map_left, map_map], refl }

lemma map₂_map_right (m : α → γ → δ) (n : β → γ) :
  map₂ m f (g.map n) = map₂ (λ a b, m a (n b)) f g :=
by rw [map₂_swap, map₂_map_left, map₂_swap]

/-! ### `filter.map₃` -/

/-- The image of a ternary function `m : α → β → γ → δ` as a function
`filter α → filter β → filter γ → filter δ`. Mathematically this should be thought of as the image
of the corresponding function `α × β × γ → δ`. -/
def map₃ (m : α → β → γ → δ) (f : filter α) (g : filter β) (h : filter γ) : filter δ :=
{ sets := {s | ∃ (u ∈ f) (v ∈ g) (w ∈ h), image3 m u v w ⊆ s},
  univ_sets := ⟨univ, univ_mem, univ, univ_mem, univ, univ_mem, subset_univ _⟩,
  sets_of_superset := λ s t ⟨u, hu, v, hv, w, hw, hs⟩ hst,
    ⟨u, hu, v, hv, w, hw, hs.trans hst⟩,
  inter_sets := λ s t ⟨us, hus, vs, hvs, ws, hws, hs⟩ ⟨ut, hut, vt, hvt, wt, hwt, ht⟩,
    ⟨us ∩ ut, inter_mem hus hut, vs ∩ vt, inter_mem hvs hvt, ws ∩ wt, inter_mem hws hwt,
      by refine subset_inter ((image3_mono _ _ _).trans hs) ((image3_mono _ _ _).trans ht);
        apply_rules [inter_subset_left, inter_subset_right]⟩ }

lemma map₂_map₂_left (m : δ → γ → ε) (n : α → β → δ) :
  map₂ m (map₂ n f g) h = map₃ (λ a b c, m (n a b) c) f g h :=
begin
  ext w,
  split,
  { rintro ⟨s, ⟨u, hu, v, hv, hs⟩, t, ht, hw⟩,
    refine ⟨u, hu, v, hv, t, ht, _⟩,
    rw ← image2_image2_left,
    exact (image2_subset_right hs).trans hw },
  { rintro ⟨s, hs, t, ht, u, hu, hw⟩,
    exact ⟨_, image2_mem_map₂ hs ht, u, hu, by rwa image2_image2_left⟩ }
end

lemma map₂_map₂_right (m : α → δ → ε) (n : β → γ → δ) :
  map₂ m f (map₂ n g h) = map₃ (λ a b c, m a (n b c)) f g h :=
begin
  ext w,
  split,
  { rintro ⟨s, hs, t, ⟨u, hu, v, hv, ht⟩, hw⟩,
    refine ⟨s, hs, u, hu, v, hv, _⟩,
    rw ← image2_image2_right,
    exact (image2_subset_left ht).trans hw },
  { rintro ⟨s, hs, t, ht, u, hu, hw⟩,
    exact ⟨s, hs, _, image2_mem_map₂ ht hu, by rwa image2_image2_right⟩ }
end

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `filter.map₂` of those operations.

The proof pattern is `map₂_lemma operation_lemma`. For example, `map₂_comm mul_comm` proves that
`map₂ (*) f g = map₂ (*) g f` in a `comm_semigroup`.
-/

lemma map₂_assoc {m : δ → γ → ε} {n : α → β → δ} {m' : α → ε' → ε} {n' : β → γ → ε'}
  {h : filter γ} (h_assoc : ∀ a b c, m (n a b) c = m' a (n' b c)) :
  map₂ m (map₂ n f g) h = map₂ m' f (map₂ n' g h) :=
by simp only [map₂_map₂_left, map₂_map₂_right, h_assoc]

lemma map₂_comm {n : β → α → γ} (h_comm : ∀ a b, m a b = n b a) : map₂ m f g = map₂ n g f :=
(map₂_swap _ _ _).trans $ by simp_rw h_comm

lemma map₂_left_comm {m : α → δ → ε} {n : β → γ → δ} {m' : α → γ → δ'} {n' : β → δ' → ε}
  (h_left_comm : ∀ a b c, m a (n b c) = n' b (m' a c)) :
  map₂ m f (map₂ n g h) = map₂ n' g (map₂ m' f h) :=
by { rw [map₂_swap m', map₂_swap m], exact map₂_assoc (λ _ _ _, h_left_comm _ _ _) }

lemma map₂_right_comm {m : δ → γ → ε} {n : α → β → δ} {m' : α → γ → δ'} {n' : δ' → β → ε}
  (h_right_comm : ∀ a b c, m (n a b) c = n' (m' a c) b) :
  map₂ m (map₂ n f g) h = map₂ n' (map₂ m' f h) g :=
by { rw [map₂_swap n, map₂_swap n'], exact map₂_assoc (λ _ _ _, h_right_comm _ _ _) }

lemma map_map₂_distrib {n : γ → δ} {m' : α' → β' → δ} {n₁ : α → α'} {n₂ : β → β'}
  (h_distrib : ∀ a b, n (m a b) = m' (n₁ a) (n₂ b)) :
  (map₂ m f g).map n = map₂ m' (f.map n₁) (g.map n₂) :=
by simp_rw [map_map₂, map₂_map_left, map₂_map_right, h_distrib]

/-- Symmetric statement to `filter.map₂_map_left_comm`. -/
lemma map_map₂_distrib_left {n : γ → δ} {m' : α' → β → δ} {n' : α → α'}
  (h_distrib : ∀ a b, n (m a b) = m' (n' a) b) :
  (map₂ m f g).map n = map₂ m' (f.map n') g :=
map_map₂_distrib h_distrib

/-- Symmetric statement to `filter.map_map₂_right_comm`. -/
lemma map_map₂_distrib_right {n : γ → δ} {m' : α → β' → δ} {n' : β → β'}
  (h_distrib : ∀ a b, n (m a b) = m' a (n' b)) :
  (map₂ m f g).map n = map₂ m' f (g.map n') :=
map_map₂_distrib h_distrib

/-- Symmetric statement to `filter.map_map₂_distrib_left`. -/
lemma map₂_map_left_comm {m : α' → β → γ} {n : α → α'} {m' : α → β → δ} {n' : δ → γ}
  (h_left_comm : ∀ a b, m (n a) b = n' (m' a b)) :
  map₂ m (f.map n) g = (map₂ m' f g).map n' :=
(map_map₂_distrib_left $ λ a b, (h_left_comm a b).symm).symm

/-- Symmetric statement to `filter.map_map₂_distrib_right`. -/
lemma map_map₂_right_comm {m : α → β' → γ} {n : β → β'} {m' : α → β → δ} {n' : δ → γ}
  (h_right_comm : ∀ a b, m a (n b) = n' (m' a b)) :
  map₂ m f (g.map n) = (map₂ m' f g).map n' :=
(map_map₂_distrib_right $ λ a b, (h_right_comm a b).symm).symm

/-- The other direction does not hold because of the `f`-`f` cross terms on the RHS. -/
lemma map₂_distrib_le_left {m : α → δ → ε} {n : β → γ → δ} {m₁ : α → β → β'} {m₂ : α → γ → γ'}
  {n' : β' → γ' → ε} (h_distrib : ∀ a b c, m a (n b c) = n' (m₁ a b) (m₂ a c)) :
  map₂ m f (map₂ n g h) ≤ map₂ n' (map₂ m₁ f g) (map₂ m₂ f h) :=
begin
  rintro s ⟨t₁, ⟨u₁, hu₁, v, hv, ht₁⟩, t₂, ⟨u₂, hu₂, w, hw, ht₂⟩, hs⟩,
  refine ⟨u₁ ∩ u₂, inter_mem hu₁ hu₂, _, image2_mem_map₂ hv hw, _⟩,
  refine (image2_distrib_subset_left h_distrib).trans ((image2_subset _ _).trans hs),
  { exact (image2_subset_right $ inter_subset_left _ _).trans ht₁ },
  { exact (image2_subset_right $ inter_subset_right _ _).trans ht₂ }
end

/-- The other direction does not hold because of the `h`-`h` cross terms on the RHS. -/
lemma map₂_distrib_le_right {m : δ → γ → ε} {n : α → β → δ} {m₁ : α → γ → α'}
  {m₂ : β → γ → β'} {n' : α' → β' → ε} (h_distrib : ∀ a b c, m (n a b) c = n' (m₁ a c) (m₂ b c)) :
  map₂ m (map₂ n f g) h ≤ map₂ n' (map₂ m₁ f h) (map₂ m₂ g h) :=
begin
  rintro s ⟨t₁, ⟨u, hu, w₁, hw₁, ht₁⟩, t₂, ⟨v, hv, w₂, hw₂, ht₂⟩, hs⟩,
  refine ⟨_, image2_mem_map₂ hu hv, w₁ ∩ w₂, inter_mem hw₁ hw₂, _⟩,
  refine (image2_distrib_subset_right h_distrib).trans ((image2_subset _ _).trans hs),
  { exact (image2_subset_left $ inter_subset_left _ _).trans ht₁ },
  { exact (image2_subset_left $ inter_subset_right _ _).trans ht₂ }
end

lemma map_map₂_antidistrib {n : γ → δ} {m' : β' → α' → δ} {n₁ : β → β'} {n₂ : α → α'}
  (h_antidistrib : ∀ a b, n (m a b) = m' (n₁ b) (n₂ a)) :
  (map₂ m f g).map n = map₂ m' (g.map n₁) (f.map n₂) :=
by { rw map₂_swap m, exact map_map₂_distrib (λ _ _, h_antidistrib _ _) }

/-- Symmetric statement to `filter.map₂_map_left_anticomm`. -/
lemma map_map₂_antidistrib_left {n : γ → δ} {m' : β' → α → δ} {n' : β → β'}
  (h_antidistrib : ∀ a b, n (m a b) = m' (n' b) a) :
  (map₂ m f g).map n = map₂ m' (g.map n') f :=
map_map₂_antidistrib h_antidistrib

/-- Symmetric statement to `filter.map_map₂_right_anticomm`. -/
lemma map_map₂_antidistrib_right {n : γ → δ} {m' : β → α' → δ} {n' : α → α'}
  (h_antidistrib : ∀ a b, n (m a b) = m' b (n' a)) :
  (map₂ m f g).map n = map₂ m' g (f.map n') :=
map_map₂_antidistrib h_antidistrib

/-- Symmetric statement to `filter.map_map₂_antidistrib_left`. -/
lemma map₂_map_left_anticomm {m : α' → β → γ} {n : α → α'} {m' : β → α → δ} {n' : δ → γ}
  (h_left_anticomm : ∀ a b, m (n a) b = n' (m' b a)) :
  map₂ m (f.map n) g = (map₂ m' g f).map n' :=
(map_map₂_antidistrib_left $ λ a b, (h_left_anticomm b a).symm).symm

/-- Symmetric statement to `filter.map_map₂_antidistrib_right`. -/
lemma map_map₂_right_anticomm {m : α → β' → γ} {n : β → β'} {m' : β → α → δ} {n' : δ → γ}
  (h_right_anticomm : ∀ a b, m a (n b) = n' (m' b a)) :
  map₂ m f (g.map n) = (map₂ m' g f).map n' :=
(map_map₂_antidistrib_right $ λ a b, (h_right_anticomm b a).symm).symm

/-- If `a` is a left identity for `f : α → β → β`, then `pure a` is a left identity for
`filter.map₂ f`. -/
lemma map₂_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (l : filter β) :
  map₂ f (pure a) l = l :=
by rw [map₂_pure_left, show f a = id, from funext h, map_id]

/-- If `b` is a right identity for `f : α → β → α`, then `pure b` is a right identity for
`filter.map₂ f`. -/
lemma map₂_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (l : filter α) :
  map₂ f l (pure b) = l :=
by rw [map₂_pure_right, funext h, map_id']

end filter
