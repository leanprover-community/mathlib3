/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.filter.n_ary

open set
open_locale filter

namespace filter

variables {α β γ : Type*}

/-- The applicative sequentiation operation. This is not induced by the bind operation. -/
def seq (f : filter (α → β)) (g : filter α) : filter β := map₂ (λ m, m) f g

/-- The `seq` induced by `filter.bind` is less than or equal to `filter.seq`. In fact, it is
striclty in some cases.

TODO: add an example. -/
lemma bind_map_le_seq (f : filter (α → β)) (l : filter α) :
  f.bind (λ m , map m l) ≤ f.seq l :=
λ s ⟨u, v, hu, hv, huv⟩, flip mem_of_superset huv $ mem_bind'.2 $ mem_of_superset hu $
  λ m hm, mem_map.2 $ mem_of_superset hv (λ x hx, ⟨m, x, hm, hx, rfl⟩)

lemma mem_seq_def {f : filter (α → β)} {g : filter α} {s : set β} :
  s ∈ f.seq g ↔ (∃ u ∈ f, ∃ t ∈ g, ∀ x ∈ u, ∀ y ∈ t, (x : α → β) y ∈ s) :=
by simp only [seq, mem_map₂_iff, exists_prop, exists_and_distrib_left, image2_subset_iff]

lemma mem_seq_iff {f : filter (α → β)} {g : filter α} {s : set β} :
  s ∈ f.seq g ↔ (∃ u ∈ f, ∃ t ∈ g, set.seq u t ⊆ s) :=
by simp only [mem_seq_def, seq_subset, exists_prop, iff_self]

lemma mem_map_seq_iff {f : filter α} {g : filter β} {m : α → β → γ} {s : set γ} :
  s ∈ (f.map m).seq g ↔ (∃ (u ∈ f) (t ∈ g), ∀ x ∈ u, ∀ y ∈ t, m x y ∈ s) :=
by simp only [seq, mem_map₂_iff, map₂_map_left, image2_subset_iff, exists_and_distrib_left,
  exists_prop]

lemma seq_mem_seq {f : filter (α → β)} {g : filter α} {s : set (α → β)} {t : set α}
  (hs : s ∈ f) (ht : t ∈ g) : s.seq t ∈ f.seq g :=
mem_seq_iff.2 ⟨s, hs, t, ht, subset.rfl⟩

lemma le_seq {f : filter (α → β)} {g : filter α} {h : filter β}
  (hh : ∀ t ∈ f, ∀ u ∈ g, set.seq t u ∈ h) : h ≤ seq f g :=
λ s ⟨t, u, ht, hu, hs⟩, mem_of_superset (hh _ ht _ hu) $
  λ b ⟨m, hm, a, ha, eq⟩, hs ⟨m, a, hm, ha, eq⟩

@[mono] lemma seq_mono {f₁ f₂ : filter (α → β)} {g₁ g₂ : filter α}
  (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.seq g₁ ≤ f₂.seq g₂ :=
le_seq $ λ s hs t ht, seq_mem_seq (hf hs) (hg ht)

@[simp] lemma pure_seq_eq_map (g : α → β) (f : filter α) : seq (pure g) f = f.map g :=
by simp [seq]

@[simp] lemma seq_pure (f : filter (α → β)) (a : α) : seq f (pure a) = map (λ g : α → β, g a) f :=
by simp [seq]

@[simp] lemma seq_assoc (x : filter α) (g : filter (α → β)) (h : filter (β → γ)) :
  seq h (seq g x) = seq (seq (map (∘) h) g) x :=
by simp_rw [seq, map₂_map_left, map₂_map₂_right, map₂_map₂_left]

lemma prod_map_seq_comm (f : filter α) (g : filter β) :
  seq (map prod.mk f) g = seq (map (λ b a, (a, b)) g) f :=
by simp only [seq, map₂_map_left, map₂_swap prod.mk]

lemma map₂_eq_seq (m : α → β → γ) (f : filter α) (g : filter β) : map₂ m f g = (f.map m).seq g :=
by rw [seq, map₂_map_left]

lemma prod_eq_seq {f : filter α} {g : filter β} : f ×ᶠ g = (f.map prod.mk).seq g  :=
by rw [← map₂_eq_seq, map₂_mk_eq_prod]

end filter
