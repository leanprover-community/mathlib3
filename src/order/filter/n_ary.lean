/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.filter.basic

/-!
# N-ary maps of filter

This file defines the binary and ternary maps of filters. This is mostly useful to define pointwise
operations on filters.

## Main declarations

* `filter.map₂`: Binary map of filters.
* `filter.map₃`: Ternary map of filters.

## Notes

This file is very similar to the n-ary section of `data.set.basic` and to `data.finset.n_ary`.
Please keep them in sync.
-/

open function set
open_locale filter

namespace filter
variables {α α' β β' γ γ' δ δ' ε ε' : Type*} {m : α → β → γ} {f f₁ f₂ : filter α}
  {g g₁ g₂ : filter β} {h h₁ h₂ : filter γ} {s s₁ s₂ : set α} {t t₁ t₂ : set β} {u : set γ}
  {v : set δ} {a : α} {b : β} {c : γ}

/-- The image of a binary function `m : α → β → γ` as a function `filter α → filter β → filter γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def map₂ (m : α → β → γ) (f : filter α) (g : filter β) : filter γ :=
{ sets := {s | ∃ u v, u ∈ f ∧ v ∈ g ∧ image2 m u v ⊆ s},
  univ_sets := ⟨univ, univ, univ_sets _, univ_sets _, subset_univ _⟩,
  sets_of_superset := λ s t hs hst,
    Exists₂.imp (λ u v, and.imp_right $ and.imp_right $ λ h, subset.trans h hst) hs,
  inter_sets := λ s t,
  begin
    simp only [exists_prop, mem_set_of_eq, subset_inter_iff],
    rintro ⟨s₁, s₂, hs₁, hs₂, hs⟩ ⟨t₁, t₂, ht₁, ht₂, ht⟩,
    exact ⟨s₁ ∩ t₁, s₂ ∩ t₂, inter_sets f hs₁ ht₁, inter_sets g hs₂ ht₂,
      (image2_subset (inter_subset_left _ _) $ inter_subset_left _ _).trans hs,
      (image2_subset (inter_subset_right _ _) $ inter_subset_right _ _).trans ht⟩,
  end }

@[simp] lemma mem_map₂_iff : u ∈ map₂ m f g ↔ ∃ s t, s ∈ f ∧ t ∈ g ∧ image2 m s t ⊆ u := iff.rfl

lemma image2_mem_map₂ (hs : s ∈ f) (ht : t ∈ g) : image2 m s t ∈ map₂ m f g :=
⟨_, _, hs, ht, subset.rfl⟩

lemma map_prod_eq_map₂ (m : α → β → γ) (f : filter α) (g : filter β) :
  filter.map (λ p : α × β, m p.1 p.2) (f ×ᶠ g) = map₂ m f g :=
begin
  ext s,
  split,
  { intro hmem,
    rw filter.mem_map_iff_exists_image at hmem,
    obtain ⟨s', hs', hsub⟩ := hmem,
    rw filter.mem_prod_iff at hs',
    obtain ⟨t, ht, t', ht', hsub'⟩ := hs',
    refine ⟨t, t', ht, ht', _⟩,
    rw ← set.image_prod,
    exact subset_trans (set.image_subset (λ (p : α × β), m p.fst p.snd) hsub') hsub },
  { intro hmem,
    rw mem_map₂_iff at hmem,
    obtain ⟨t, t', ht, ht', hsub⟩ := hmem,
    rw ← set.image_prod at hsub,
    rw filter.mem_map_iff_exists_image,
    exact ⟨t ×ˢ t', filter.prod_mem_prod ht ht', hsub⟩ },
end

lemma map_prod_eq_map₂' (m : α × β → γ) (f : filter α) (g : filter β) :
  filter.map m (f ×ᶠ g) = map₂ (λ a b, m (a, b)) f g :=
by { refine eq.trans _ (map_prod_eq_map₂ (curry m) f g), ext, simp }

-- lemma image2_mem_map₂_iff (hm : injective2 m) : image2 m s t ∈ map₂ m f g ↔ s ∈ f ∧ t ∈ g :=
-- ⟨by { rintro ⟨u, v, hu, hv, h⟩, rw image2_subset_image2_iff hm at h,
--   exact ⟨mem_of_superset hu h.1, mem_of_superset hv h.2⟩ }, λ h, image2_mem_map₂ h.1 h.2⟩

lemma map₂_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : map₂ m f₁ g₁ ≤ map₂ m f₂ g₂ :=
λ _ ⟨s, t, hs, ht, hst⟩, ⟨s, t, hf hs, hg ht, hst⟩

lemma map₂_mono_left (h : g₁ ≤ g₂) : map₂ m f g₁ ≤ map₂ m f g₂ := map₂_mono subset.rfl h
lemma map₂_mono_right (h : f₁ ≤ f₂) : map₂ m f₁ g ≤ map₂ m f₂ g := map₂_mono h subset.rfl

@[simp] lemma le_map₂_iff {h : filter γ} :
  h ≤ map₂ m f g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → image2 m s t ∈ h :=
⟨λ H s hs t ht, H $ image2_mem_map₂ hs ht, λ H u ⟨s, t, hs, ht, hu⟩, mem_of_superset (H hs ht) hu⟩

@[simp] lemma map₂_bot_left : map₂ m ⊥ g = ⊥ :=
empty_mem_iff_bot.1 ⟨∅, univ, trivial, univ_mem, (image2_empty_left).subset⟩

@[simp] lemma map₂_bot_right : map₂ m f ⊥ = ⊥ :=
empty_mem_iff_bot.1 ⟨univ, ∅, univ_mem, trivial, (image2_empty_right).subset⟩

@[simp] lemma map₂_eq_bot_iff : map₂ m f g = ⊥ ↔ f = ⊥ ∨ g = ⊥ :=
begin
  simp only [←empty_mem_iff_bot, mem_map₂_iff, subset_empty_iff, image2_eq_empty_iff],
  split,
  { rintro ⟨s, t, hs, ht, rfl | rfl⟩,
    { exact or.inl hs },
    { exact or.inr ht } },
  { rintro (h | h),
    { exact ⟨_, _, h, univ_mem, or.inl rfl⟩ },
    { exact ⟨_, _, univ_mem, h, or.inr rfl⟩ } }
end

@[simp] lemma map₂_ne_bot_iff : (map₂ m f g).ne_bot ↔ f.ne_bot ∧ g.ne_bot :=
by { simp_rw ne_bot_iff, exact map₂_eq_bot_iff.not.trans not_or_distrib }

lemma ne_bot.map₂ (hf : f.ne_bot) (hg : g.ne_bot) : (map₂ m f g).ne_bot :=
map₂_ne_bot_iff.2 ⟨hf, hg⟩

lemma ne_bot.of_map₂_left (h : (map₂ m f g).ne_bot) : f.ne_bot := (map₂_ne_bot_iff.1 h).1
lemma ne_bot.of_map₂_right (h : (map₂ m f g).ne_bot) : g.ne_bot := (map₂_ne_bot_iff.1 h).2

lemma map₂_sup_left : map₂ m (f₁ ⊔ f₂) g = map₂ m f₁ g ⊔ map₂ m f₂ g :=
begin
  ext u,
  split,
  { rintro ⟨s, t, ⟨h₁, h₂⟩, ht, hu⟩,
    exact ⟨mem_of_superset (image2_mem_map₂ h₁ ht) hu,
      mem_of_superset (image2_mem_map₂ h₂ ht) hu⟩ },
  { rintro ⟨⟨s₁, t₁, hs₁, ht₁, hu₁⟩, s₂, t₂, hs₂, ht₂, hu₂⟩,
    refine ⟨s₁ ∪ s₂, t₁ ∩ t₂, union_mem_sup hs₁ hs₂, inter_mem ht₁ ht₂, _⟩,
    rw image2_union_left,
    exact union_subset ((image2_subset_left $ inter_subset_left _ _).trans hu₁)
      ((image2_subset_left $ inter_subset_right _ _).trans hu₂) }
end

lemma map₂_sup_right : map₂ m f (g₁ ⊔ g₂) = map₂ m f g₁ ⊔ map₂ m f g₂ :=
begin
  ext u,
  split,
  { rintro ⟨s, t, hs, ⟨h₁, h₂⟩, hu⟩,
    exact ⟨mem_of_superset (image2_mem_map₂ hs h₁) hu,
      mem_of_superset (image2_mem_map₂ hs h₂) hu⟩ },
  { rintro ⟨⟨s₁, t₁, hs₁, ht₁, hu₁⟩, s₂, t₂, hs₂, ht₂, hu₂⟩,
    refine ⟨s₁ ∩ s₂, t₁ ∪ t₂, inter_mem hs₁ hs₂, union_mem_sup ht₁ ht₂, _⟩,
    rw image2_union_right,
    exact union_subset ((image2_subset_right $ inter_subset_left _ _).trans hu₁)
      ((image2_subset_right $ inter_subset_right _ _).trans hu₂) }
end

lemma map₂_inf_subset_left : map₂ m (f₁ ⊓ f₂) g ≤ map₂ m f₁ g ⊓ map₂ m f₂ g :=
le_inf (map₂_mono_right inf_le_left) (map₂_mono_right inf_le_right)

lemma map₂_inf_subset_right : map₂ m f (g₁ ⊓ g₂) ≤ map₂ m f g₁ ⊓ map₂ m f g₂ :=
le_inf (map₂_mono_left inf_le_left) (map₂_mono_left inf_le_right)

@[simp] lemma map₂_pure_left : map₂ m (pure a) g = g.map (λ b, m a b) :=
filter.ext $ λ u, ⟨λ ⟨s, t, hs, ht, hu⟩,
  mem_of_superset (image_mem_map ht) ((image_subset_image2_right $ mem_pure.1 hs).trans hu),
    λ h, ⟨{a}, _, singleton_mem_pure, h, by rw [image2_singleton_left, image_subset_iff]⟩⟩

@[simp] lemma map₂_pure_right : map₂ m f (pure b) = f.map (λ a, m a b) :=
filter.ext $ λ u, ⟨λ ⟨s, t, hs, ht, hu⟩,
  mem_of_superset (image_mem_map hs) ((image_subset_image2_left $ mem_pure.1 ht).trans hu),
    λ h, ⟨_, {b}, h, singleton_mem_pure, by rw [image2_singleton_right, image_subset_iff]⟩⟩

lemma map₂_pure : map₂ m (pure a) (pure b) = pure (m a b) := by rw [map₂_pure_right, map_pure]

lemma map₂_swap (m : α → β → γ) (f : filter α) (g : filter β) :
  map₂ m f g = map₂ (λ a b, m b a) g f :=
by { ext u, split; rintro ⟨s, t, hs, ht, hu⟩; refine ⟨t, s, ht, hs, by rwa image2_swap⟩ }

@[simp] lemma map₂_left (h : g.ne_bot) : map₂ (λ x y, x) f g = f :=
begin
  ext u,
  refine ⟨_, λ hu, ⟨_, _, hu, univ_mem, (image2_left $ h.nonempty_of_mem univ_mem).subset⟩⟩,
  rintro ⟨s, t, hs, ht, hu⟩,
  rw image2_left (h.nonempty_of_mem ht) at hu,
  exact mem_of_superset hs hu,
end

@[simp] lemma map₂_right (h : f.ne_bot) : map₂ (λ x y, y) f g = g := by rw [map₂_swap, map₂_left h]

/-- The image of a ternary function `m : α → β → γ → δ` as a function
`filter α → filter β → filter γ → filter δ`. Mathematically this should be thought of as the image
of the corresponding function `α × β × γ → δ`. -/
def map₃ (m : α → β → γ → δ) (f : filter α) (g : filter β) (h : filter γ) : filter δ :=
{ sets := {s | ∃ u v w, u ∈ f ∧ v ∈ g ∧ w ∈ h ∧ image3 m u v w ⊆ s},
  univ_sets := ⟨univ, univ, univ, univ_sets _, univ_sets _, univ_sets _, subset_univ _⟩,
  sets_of_superset := λ s t hs hst, Exists₃.imp
    (λ u v w, and.imp_right $ and.imp_right $ and.imp_right $ λ h, subset.trans h hst) hs,
  inter_sets := λ s t,
  begin
    simp only [exists_prop, mem_set_of_eq, subset_inter_iff],
    rintro ⟨s₁, s₂, s₃, hs₁, hs₂, hs₃, hs⟩ ⟨t₁, t₂, t₃, ht₁, ht₂, ht₃, ht⟩,
    exact ⟨s₁ ∩ t₁, s₂ ∩ t₂, s₃ ∩ t₃, inter_mem hs₁ ht₁, inter_mem hs₂ ht₂, inter_mem hs₃ ht₃,
      (image3_mono (inter_subset_left _ _) (inter_subset_left _ _) $ inter_subset_left _ _).trans
        hs,
      (image3_mono (inter_subset_right _ _) (inter_subset_right _ _) $ inter_subset_right _ _).trans
        ht⟩,
  end }

lemma map₂_map₂_left (m : δ → γ → ε) (n : α → β → δ) :
  map₂ m (map₂ n f g) h = map₃ (λ a b c, m (n a b) c) f g h :=
begin
  ext w,
  split,
  { rintro ⟨s, t, ⟨u, v, hu, hv, hs⟩, ht, hw⟩,
    refine ⟨u, v, t, hu, hv, ht, _⟩,
    rw ←image2_image2_left,
    exact (image2_subset_right hs).trans hw },
  { rintro ⟨s, t, u, hs, ht, hu, hw⟩,
    exact ⟨_, u, image2_mem_map₂ hs ht, hu, by rwa image2_image2_left⟩ }
end

lemma map₂_map₂_right (m : α → δ → ε) (n : β → γ → δ) :
  map₂ m f (map₂ n g h) = map₃ (λ a b c, m a (n b c)) f g h :=
begin
  ext w,
  split,
  { rintro ⟨s, t, hs, ⟨u, v, hu, hv, ht⟩, hw⟩,
    refine ⟨s, u, v, hs, hu, hv, _⟩,
    rw ←image2_image2_right,
    exact (image2_subset_left ht).trans hw },
  { rintro ⟨s, t, u, hs, ht, hu, hw⟩,
    exact ⟨s, _, hs, image2_mem_map₂ ht hu, by rwa image2_image2_right⟩ }
end

lemma map_map₂ (m : α → β → γ) (n : γ → δ) : (map₂ m f g).map n = map₂ (λ a b, n (m a b)) f g :=
filter.ext $ λ u, exists₂_congr $ λ s t, by rw [←image_subset_iff, image_image2]

lemma map₂_map_left (m : γ → β → δ) (n : α → γ) :
  map₂ m (f.map n) g = map₂ (λ a b, m (n a) b) f g :=
begin
  ext u,
  split,
  { rintro ⟨s, t, hs, ht, hu⟩,
    refine ⟨_, t, hs, ht, _⟩,
    rw ←image2_image_left,
    exact (image2_subset_right $ image_preimage_subset _ _).trans hu },
  { rintro ⟨s, t, hs, ht, hu⟩,
    exact ⟨_, t, image_mem_map hs, ht, by rwa image2_image_left⟩ }
end

lemma map₂_map_right (m : α → γ → δ) (n : β → γ) :
  map₂ m f (g.map n) = map₂ (λ a b, m a (n b)) f g :=
by rw [map₂_swap, map₂_map_left, map₂_swap]

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

/-- Symmetric of `filter.map₂_map_left_comm`. -/
lemma map_map₂_distrib_left {n : γ → δ} {m' : α' → β → δ} {n' : α → α'}
  (h_distrib : ∀ a b, n (m a b) = m' (n' a) b) :
  (map₂ m f g).map n = map₂ m' (f.map n') g :=
map_map₂_distrib h_distrib

/-- Symmetric of `filter.map_map₂_right_comm`. -/
lemma map_map₂_distrib_right {n : γ → δ} {m' : α → β' → δ} {n' : β → β'}
  (h_distrib : ∀ a b, n (m a b) = m' a (n' b)) :
  (map₂ m f g).map n = map₂ m' f (g.map n') :=
map_map₂_distrib h_distrib

/-- Symmetric of `filter.map_map₂_distrib_left`. -/
lemma map₂_map_left_comm {m : α' → β → γ} {n : α → α'} {m' : α → β → δ} {n' : δ → γ}
  (h_left_comm : ∀ a b, m (n a) b = n' (m' a b)) :
  map₂ m (f.map n) g = (map₂ m' f g).map n' :=
(map_map₂_distrib_left $ λ a b, (h_left_comm a b).symm).symm

/-- Symmetric of `filter.map_map₂_distrib_right`. -/
lemma map_map₂_right_comm {m : α → β' → γ} {n : β → β'} {m' : α → β → δ} {n' : δ → γ}
  (h_right_comm : ∀ a b, m a (n b) = n' (m' a b)) :
  map₂ m f (g.map n) = (map₂ m' f g).map n' :=
(map_map₂_distrib_right $ λ a b, (h_right_comm a b).symm).symm

/-- The other direction does not hold because of the `f`-`f` cross terms on the RHS. -/
lemma map₂_distrib_le_left {m : α → δ → ε} {n : β → γ → δ} {m₁ : α → β → β'} {m₂ : α → γ → γ'}
  {n' : β' → γ' → ε} (h_distrib : ∀ a b c, m a (n b c) = n' (m₁ a b) (m₂ a c)) :
  map₂ m f (map₂ n g h) ≤ map₂ n' (map₂ m₁ f g) (map₂ m₂ f h) :=
begin
  rintro s ⟨t₁, t₂, ⟨u₁, v, hu₁, hv, ht₁⟩, ⟨u₂, w, hu₂, hw, ht₂⟩, hs⟩,
  refine ⟨u₁ ∩ u₂, _, inter_mem hu₁ hu₂, image2_mem_map₂ hv hw, _⟩,
  refine (image2_distrib_subset_left h_distrib).trans ((image2_subset _ _).trans hs),
  { exact (image2_subset_right $ inter_subset_left _ _).trans ht₁ },
  { exact (image2_subset_right $ inter_subset_right _ _).trans ht₂ }
end

/-- The other direction does not hold because of the `h`-`h` cross terms on the RHS. -/
lemma map₂_distrib_le_right {m : δ → γ → ε} {n : α → β → δ} {m₁ : α → γ → α'}
  {m₂ : β → γ → β'} {n' : α' → β' → ε} (h_distrib : ∀ a b c, m (n a b) c = n' (m₁ a c) (m₂ b c)) :
  map₂ m (map₂ n f g) h ≤ map₂ n' (map₂ m₁ f h) (map₂ m₂ g h) :=
begin
  rintro s ⟨t₁, t₂, ⟨u, w₁, hu, hw₁, ht₁⟩, ⟨v, w₂, hv, hw₂, ht₂⟩, hs⟩,
  refine ⟨_, w₁ ∩ w₂, image2_mem_map₂ hu hv, inter_mem hw₁ hw₂, _⟩,
  refine (image2_distrib_subset_right h_distrib).trans ((image2_subset _ _).trans hs),
  { exact (image2_subset_left $ inter_subset_left _ _).trans ht₁ },
  { exact (image2_subset_left $ inter_subset_right _ _).trans ht₂ }
end

lemma map_map₂_antidistrib {n : γ → δ} {m' : β' → α' → δ} {n₁ : β → β'} {n₂ : α → α'}
  (h_antidistrib : ∀ a b, n (m a b) = m' (n₁ b) (n₂ a)) :
  (map₂ m f g).map n = map₂ m' (g.map n₁) (f.map n₂) :=
by { rw map₂_swap m, exact map_map₂_distrib (λ _ _, h_antidistrib _ _) }

/-- Symmetric of `filter.map₂_map_left_anticomm`. -/
lemma map_map₂_antidistrib_left {n : γ → δ} {m' : β' → α → δ} {n' : β → β'}
  (h_antidistrib : ∀ a b, n (m a b) = m' (n' b) a) :
  (map₂ m f g).map n = map₂ m' (g.map n') f :=
map_map₂_antidistrib h_antidistrib

/-- Symmetric of `filter.map_map₂_right_anticomm`. -/
lemma map_map₂_antidistrib_right {n : γ → δ} {m' : β → α' → δ} {n' : α → α'}
  (h_antidistrib : ∀ a b, n (m a b) = m' b (n' a)) :
  (map₂ m f g).map n = map₂ m' g (f.map n') :=
map_map₂_antidistrib h_antidistrib

/-- Symmetric of `filter.map_map₂_antidistrib_left`. -/
lemma map₂_map_left_anticomm {m : α' → β → γ} {n : α → α'} {m' : β → α → δ} {n' : δ → γ}
  (h_left_anticomm : ∀ a b, m (n a) b = n' (m' b a)) :
  map₂ m (f.map n) g = (map₂ m' g f).map n' :=
(map_map₂_antidistrib_left $ λ a b, (h_left_anticomm b a).symm).symm

/-- Symmetric of `filter.map_map₂_antidistrib_right`. -/
lemma map_map₂_right_anticomm {m : α → β' → γ} {n : β → β'} {m' : β → α → δ} {n' : δ → γ}
  (h_right_anticomm : ∀ a b, m a (n b) = n' (m' b a)) :
  map₂ m f (g.map n) = (map₂ m' g f).map n' :=
(map_map₂_antidistrib_right $ λ a b, (h_right_anticomm b a).symm).symm

end filter
