/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import order.filter.extr
import topology.continuous_on

/-!
# Local extrema of functions on topological spaces

## Main definitions

This file defines special versions of `is_*_filter f a l`, `*=min/max/extr`,
from `order/filter/extr` for two kinds of filters: `nhds_within` and `nhds`.
These versions are called `is_local_*_on` and `is_local_*`, respectively.

## Main statements

Many lemmas in this file restate those from `order/filter/extr`, and you can find
a detailed documentation there. These convenience lemmas are provided only to make the dot notation
return propositions of expected types, not just `is_*_filter`.

Here is the list of statements specific to these two types of filters:

* `is_local_*.on`, `is_local_*_on.on_subset`: restrict to a subset;
* `is_local_*_on.inter` : intersect the set with another one;
* `is_*_on.localize` : a global extremum is a local extremum too.
* `is_[local_]*_on.is_local_*` : if we have `is_local_*_on f s a` and `s ∈ 𝓝 a`,
  then we have `is_local_* f a`.

-/

universes u v w x

variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α]

open set filter
open_locale topological_space filter

section preorder

variables [preorder β] [preorder γ] (f : α → β) (s : set α) (a : α)

/-- `is_local_min_on f s a` means that `f a ≤ f x` for all `x ∈ s` in some neighborhood of `a`. -/
def is_local_min_on := is_min_filter f (𝓝[s] a) a

/-- `is_local_max_on f s a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
def is_local_max_on := is_max_filter f (𝓝[s] a) a

/-- `is_local_extr_on f s a` means `is_local_min_on f s a ∨ is_local_max_on f s a`. -/
def is_local_extr_on := is_extr_filter f (𝓝[s] a) a

/-- `is_local_min f a` means that `f a ≤ f x` for all `x` in some neighborhood of `a`. -/
def is_local_min := is_min_filter f (𝓝 a) a

/-- `is_local_max f a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
def is_local_max := is_max_filter f (𝓝 a) a

/-- `is_local_extr_on f s a` means `is_local_min_on f s a ∨ is_local_max_on f s a`. -/
def is_local_extr := is_extr_filter f (𝓝 a) a

variables {f s a}

lemma is_local_extr_on.elim {p : Prop} :
  is_local_extr_on f s a → (is_local_min_on f s a → p) → (is_local_max_on f s a → p) → p :=
or.elim

lemma is_local_extr.elim {p : Prop} :
  is_local_extr f a → (is_local_min f a → p) → (is_local_max f a → p) → p :=
or.elim

/-! ### Restriction to (sub)sets -/

lemma is_local_min.on (h : is_local_min f a) (s) : is_local_min_on f s a :=
h.filter_inf _

lemma is_local_max.on (h : is_local_max f a) (s) : is_local_max_on f s a :=
h.filter_inf _

lemma is_local_extr.on (h : is_local_extr f a) (s) : is_local_extr_on f s a :=
h.filter_inf _

lemma is_local_min_on.on_subset {t : set α} (hf : is_local_min_on f t a) (h : s ⊆ t) :
  is_local_min_on f s a :=
hf.filter_mono $ nhds_within_mono a h

lemma is_local_max_on.on_subset {t : set α} (hf : is_local_max_on f t a) (h : s ⊆ t) :
  is_local_max_on f s a :=
hf.filter_mono $ nhds_within_mono a h

lemma is_local_extr_on.on_subset {t : set α} (hf : is_local_extr_on f t a) (h : s ⊆ t) :
  is_local_extr_on f s a :=
hf.filter_mono $ nhds_within_mono a h

lemma is_local_min_on.inter (hf : is_local_min_on f s a) (t) : is_local_min_on f (s ∩ t) a :=
hf.on_subset (inter_subset_left s t)

lemma is_local_max_on.inter (hf : is_local_max_on f s a) (t) : is_local_max_on f (s ∩ t) a :=
hf.on_subset (inter_subset_left s t)

lemma is_local_extr_on.inter (hf : is_local_extr_on f s a) (t) : is_local_extr_on f (s ∩ t) a :=
hf.on_subset (inter_subset_left s t)

lemma is_min_on.localize (hf : is_min_on f s a) : is_local_min_on f s a :=
hf.filter_mono $ inf_le_right

lemma is_max_on.localize (hf : is_max_on f s a) : is_local_max_on f s a :=
hf.filter_mono $ inf_le_right

lemma is_extr_on.localize (hf : is_extr_on f s a) : is_local_extr_on f s a :=
hf.filter_mono $ inf_le_right

lemma is_local_min_on.is_local_min (hf : is_local_min_on f s a) (hs : s ∈ 𝓝 a) : is_local_min f a :=
have 𝓝 a ≤ 𝓟 s, from le_principal_iff.2 hs,
hf.filter_mono $ le_inf (le_refl _) this

lemma is_local_max_on.is_local_max (hf : is_local_max_on f s a) (hs : s ∈ 𝓝 a) : is_local_max f a :=
have 𝓝 a ≤ 𝓟 s, from le_principal_iff.2 hs,
hf.filter_mono $ le_inf (le_refl _) this

lemma is_local_extr_on.is_local_extr (hf : is_local_extr_on f s a) (hs : s ∈ 𝓝 a) :
  is_local_extr f a :=
hf.elim (λ hf, (hf.is_local_min hs).is_extr) (λ hf, (hf.is_local_max hs).is_extr)

lemma is_min_on.is_local_min (hf : is_min_on f s a) (hs : s ∈ 𝓝 a) : is_local_min f a :=
hf.localize.is_local_min hs

lemma is_max_on.is_local_max (hf : is_max_on f s a) (hs : s ∈ 𝓝 a) : is_local_max f a :=
hf.localize.is_local_max hs

lemma is_extr_on.is_local_extr (hf : is_extr_on f s a) (hs : s ∈ 𝓝 a) : is_local_extr f a :=
hf.localize.is_local_extr hs

lemma is_local_min_on.not_nhds_le_map [topological_space β]
  (hf : is_local_min_on f s a) [ne_bot (𝓝[Iio (f a)] (f a))] :
  ¬𝓝 (f a) ≤ map f (𝓝[s] a) :=
λ hle,
have ∀ᶠ y in 𝓝[Iio (f a)] (f a), f a ≤ y,
  from (eventually_map.2 hf).filter_mono (inf_le_left.trans hle),
let ⟨y, hy⟩ := (this.and self_mem_nhds_within).exists in hy.1.not_lt hy.2

lemma is_local_max_on.not_nhds_le_map [topological_space β]
  (hf : is_local_max_on f s a) [ne_bot (𝓝[Ioi (f a)] (f a))] :
  ¬𝓝 (f a) ≤ map f (𝓝[s] a) :=
@is_local_min_on.not_nhds_le_map α (order_dual β) _ _ _ _ _ ‹_› hf ‹_›

lemma is_local_extr_on.not_nhds_le_map [topological_space β]
  (hf : is_local_extr_on f s a) [ne_bot (𝓝[Iio (f a)] (f a))] [ne_bot (𝓝[Ioi (f a)] (f a))] :
  ¬𝓝 (f a) ≤ map f (𝓝[s] a) :=
hf.elim (λ h, h.not_nhds_le_map) (λ h, h.not_nhds_le_map)

/-! ### Constant -/

lemma is_local_min_on_const {b : β} : is_local_min_on (λ _, b) s a := is_min_filter_const
lemma is_local_max_on_const {b : β} : is_local_max_on (λ _, b) s a := is_max_filter_const
lemma is_local_extr_on_const {b : β} : is_local_extr_on (λ _, b) s a := is_extr_filter_const

lemma is_local_min_const {b : β} : is_local_min (λ _, b) a := is_min_filter_const
lemma is_local_max_const {b : β} : is_local_max (λ _, b) a := is_max_filter_const
lemma is_local_extr_const {b : β} : is_local_extr (λ _, b) a := is_extr_filter_const

/-! ### Composition with (anti)monotone functions -/

lemma is_local_min.comp_mono (hf : is_local_min f a) {g : β → γ} (hg : monotone g) :
  is_local_min (g ∘ f) a :=
hf.comp_mono hg

lemma is_local_max.comp_mono (hf : is_local_max f a) {g : β → γ} (hg : monotone g) :
  is_local_max (g ∘ f) a :=
hf.comp_mono hg

lemma is_local_extr.comp_mono (hf : is_local_extr f a) {g : β → γ} (hg : monotone g) :
  is_local_extr (g ∘ f) a :=
hf.comp_mono hg

lemma is_local_min.comp_antitone (hf : is_local_min f a) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_local_max (g ∘ f) a :=
hf.comp_antitone hg

lemma is_local_max.comp_antitone (hf : is_local_max f a) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_local_min (g ∘ f) a :=
hf.comp_antitone hg

lemma is_local_extr.comp_antitone (hf : is_local_extr f a) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_local_extr (g ∘ f) a :=
hf.comp_antitone hg

lemma is_local_min_on.comp_mono (hf : is_local_min_on f s a) {g : β → γ} (hg : monotone g) :
  is_local_min_on (g ∘ f) s a :=
hf.comp_mono hg

lemma is_local_max_on.comp_mono (hf : is_local_max_on f s a) {g : β → γ} (hg : monotone g) :
  is_local_max_on (g ∘ f) s a :=
hf.comp_mono hg

lemma is_local_extr_on.comp_mono (hf : is_local_extr_on f s a) {g : β → γ} (hg : monotone g) :
  is_local_extr_on (g ∘ f) s a :=
hf.comp_mono hg

lemma is_local_min_on.comp_antitone (hf : is_local_min_on f s a) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_local_max_on (g ∘ f) s a :=
hf.comp_antitone hg

lemma is_local_max_on.comp_antitone (hf : is_local_max_on f s a) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_local_min_on (g ∘ f) s a :=
hf.comp_antitone hg

lemma is_local_extr_on.comp_antitone (hf : is_local_extr_on f s a) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_local_extr_on (g ∘ f) s a :=
hf.comp_antitone hg

lemma is_local_min.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_local_min f a) {g : α → γ} (hg : is_local_min g a) :
  is_local_min (λ x, op (f x) (g x)) a :=
hf.bicomp_mono hop hg

lemma is_local_max.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_local_max f a) {g : α → γ} (hg : is_local_max g a) :
  is_local_max (λ x, op (f x) (g x)) a :=
hf.bicomp_mono hop hg

-- No `extr` version because we need `hf` and `hg` to be of the same kind

lemma is_local_min_on.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_local_min_on f s a) {g : α → γ} (hg : is_local_min_on g s a) :
  is_local_min_on (λ x, op (f x) (g x)) s a :=
hf.bicomp_mono hop hg

lemma is_local_max_on.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_local_max_on f s a) {g : α → γ} (hg : is_local_max_on g s a) :
  is_local_max_on (λ x, op (f x) (g x)) s a :=
hf.bicomp_mono hop hg

/-! ### Composition with `continuous_at` -/

lemma is_local_min.comp_continuous [topological_space δ] {g : δ → α} {b : δ}
  (hf : is_local_min f (g b)) (hg : continuous_at g b) :
  is_local_min (f ∘ g) b :=
hg hf

lemma is_local_max.comp_continuous [topological_space δ] {g : δ → α} {b : δ}
  (hf : is_local_max f (g b)) (hg : continuous_at g b) :
  is_local_max (f ∘ g) b :=
hg hf

lemma is_local_extr.comp_continuous [topological_space δ] {g : δ → α} {b : δ}
  (hf : is_local_extr f (g b)) (hg : continuous_at g b) :
  is_local_extr (f ∘ g) b :=
hf.comp_tendsto hg

lemma is_local_min.comp_continuous_on [topological_space δ] {s : set δ} {g : δ → α} {b : δ}
  (hf : is_local_min f (g b)) (hg : continuous_on g s) (hb : b ∈ s) :
  is_local_min_on (f ∘ g) s b :=
hf.comp_tendsto (hg b hb)

lemma is_local_max.comp_continuous_on [topological_space δ] {s : set δ} {g : δ → α} {b : δ}
  (hf : is_local_max f (g b)) (hg : continuous_on g s) (hb : b ∈ s) :
  is_local_max_on (f ∘ g) s b :=
hf.comp_tendsto (hg b hb)

lemma is_local_extr.comp_continuous_on [topological_space δ] {s : set δ} (g : δ → α) {b : δ}
  (hf : is_local_extr f (g b)) (hg : continuous_on g s) (hb : b ∈ s) :
  is_local_extr_on (f ∘ g) s b :=
hf.elim (λ hf, (hf.comp_continuous_on hg hb).is_extr)
  (λ hf, (is_local_max.comp_continuous_on hf hg hb).is_extr)

lemma is_local_min_on.comp_continuous_on [topological_space δ] {t : set α} {s : set δ} {g : δ → α}
  {b : δ} (hf : is_local_min_on f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : continuous_on g s)
  (hb : b ∈ s) :
  is_local_min_on (f ∘ g) s b :=
hf.comp_tendsto (tendsto_nhds_within_mono_right (image_subset_iff.mpr hst)
  (continuous_within_at.tendsto_nhds_within_image (hg b hb)))

lemma is_local_max_on.comp_continuous_on [topological_space δ] {t : set α} {s : set δ} {g : δ → α}
  {b : δ} (hf : is_local_max_on f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : continuous_on g s)
  (hb : b ∈ s) :
  is_local_max_on (f ∘ g) s b :=
hf.comp_tendsto (tendsto_nhds_within_mono_right (image_subset_iff.mpr hst)
  (continuous_within_at.tendsto_nhds_within_image (hg b hb)))

lemma is_local_extr_on.comp_continuous_on [topological_space δ] {t : set α} {s : set δ} (g : δ → α)
  {b : δ} (hf : is_local_extr_on f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : continuous_on g s)
  (hb : b ∈ s) :
  is_local_extr_on (f ∘ g) s b :=
hf.elim (λ hf, (hf.comp_continuous_on hst hg hb).is_extr)
  (λ hf, (is_local_max_on.comp_continuous_on hf hst hg hb).is_extr)

end preorder

/-! ### Pointwise addition -/
section ordered_add_comm_monoid

variables [ordered_add_comm_monoid β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_local_min.add (hf : is_local_min f a) (hg : is_local_min g a) :
  is_local_min (λ x, f x + g x) a :=
hf.add hg

lemma is_local_max.add (hf : is_local_max f a) (hg : is_local_max g a) :
  is_local_max (λ x, f x + g x) a :=
hf.add hg

lemma is_local_min_on.add (hf : is_local_min_on f s a) (hg : is_local_min_on g s a) :
  is_local_min_on (λ x, f x + g x) s a :=
hf.add hg

lemma is_local_max_on.add (hf : is_local_max_on f s a) (hg : is_local_max_on g s a) :
  is_local_max_on (λ x, f x + g x) s a :=
hf.add hg

end ordered_add_comm_monoid

/-! ### Pointwise negation and subtraction -/

section ordered_add_comm_group

variables [ordered_add_comm_group β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_local_min.neg (hf : is_local_min f a) : is_local_max (λ x, -f x) a :=
hf.neg

lemma is_local_max.neg (hf : is_local_max f a) : is_local_min (λ x, -f x) a :=
hf.neg

lemma is_local_extr.neg (hf : is_local_extr f a) : is_local_extr (λ x, -f x) a :=
hf.neg

lemma is_local_min_on.neg (hf : is_local_min_on f s a) : is_local_max_on (λ x, -f x) s a :=
hf.neg

lemma is_local_max_on.neg (hf : is_local_max_on f s a) : is_local_min_on (λ x, -f x) s a :=
hf.neg

lemma is_local_extr_on.neg (hf : is_local_extr_on f s a) : is_local_extr_on (λ x, -f x) s a :=
hf.neg

lemma is_local_min.sub (hf : is_local_min f a) (hg : is_local_max g a) :
  is_local_min (λ x, f x - g x) a :=
hf.sub hg

lemma is_local_max.sub (hf : is_local_max f a) (hg : is_local_min g a) :
  is_local_max (λ x, f x - g x) a :=
hf.sub hg

lemma is_local_min_on.sub (hf : is_local_min_on f s a) (hg : is_local_max_on g s a) :
  is_local_min_on (λ x, f x - g x) s a :=
hf.sub hg

lemma is_local_max_on.sub (hf : is_local_max_on f s a) (hg : is_local_min_on g s a) :
  is_local_max_on (λ x, f x - g x) s a :=
hf.sub hg

end ordered_add_comm_group


/-! ### Pointwise `sup`/`inf` -/

section semilattice_sup

variables [semilattice_sup β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_local_min.sup (hf : is_local_min f a) (hg : is_local_min g a) :
  is_local_min (λ x, f x ⊔ g x) a :=
hf.sup hg

lemma is_local_max.sup (hf : is_local_max f a) (hg : is_local_max g a) :
  is_local_max (λ x, f x ⊔ g x) a :=
hf.sup hg

lemma is_local_min_on.sup (hf : is_local_min_on f s a) (hg : is_local_min_on g s a) :
  is_local_min_on (λ x, f x ⊔ g x) s a :=
hf.sup hg

lemma is_local_max_on.sup (hf : is_local_max_on f s a) (hg : is_local_max_on g s a) :
  is_local_max_on (λ x, f x ⊔ g x) s a :=
hf.sup hg

end semilattice_sup

section semilattice_inf

variables [semilattice_inf β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_local_min.inf (hf : is_local_min f a) (hg : is_local_min g a) :
  is_local_min (λ x, f x ⊓ g x) a :=
hf.inf hg

lemma is_local_max.inf (hf : is_local_max f a) (hg : is_local_max g a) :
  is_local_max (λ x, f x ⊓ g x) a :=
hf.inf hg

lemma is_local_min_on.inf (hf : is_local_min_on f s a) (hg : is_local_min_on g s a) :
  is_local_min_on (λ x, f x ⊓ g x) s a :=
hf.inf hg

lemma is_local_max_on.inf (hf : is_local_max_on f s a) (hg : is_local_max_on g s a) :
  is_local_max_on (λ x, f x ⊓ g x) s a :=
hf.inf hg

end semilattice_inf

/-! ### Pointwise `min`/`max` -/

section linear_order

variables [linear_order β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_local_min.min (hf : is_local_min f a) (hg : is_local_min g a) :
  is_local_min (λ x, min (f x) (g x)) a :=
hf.min hg

lemma is_local_max.min (hf : is_local_max f a) (hg : is_local_max g a) :
  is_local_max (λ x, min (f x) (g x)) a :=
hf.min hg

lemma is_local_min_on.min (hf : is_local_min_on f s a) (hg : is_local_min_on g s a) :
  is_local_min_on (λ x, min (f x) (g x)) s a :=
hf.min hg

lemma is_local_max_on.min (hf : is_local_max_on f s a) (hg : is_local_max_on g s a) :
  is_local_max_on (λ x, min (f x) (g x)) s a :=
hf.min hg

lemma is_local_min.max (hf : is_local_min f a) (hg : is_local_min g a) :
  is_local_min (λ x, max (f x) (g x)) a :=
hf.max hg

lemma is_local_max.max (hf : is_local_max f a) (hg : is_local_max g a) :
  is_local_max (λ x, max (f x) (g x)) a :=
hf.max hg

lemma is_local_min_on.max (hf : is_local_min_on f s a) (hg : is_local_min_on g s a) :
  is_local_min_on (λ x, max (f x) (g x)) s a :=
hf.max hg

lemma is_local_max_on.max (hf : is_local_max_on f s a) (hg : is_local_max_on g s a) :
  is_local_max_on (λ x, max (f x) (g x)) s a :=
hf.max hg

end linear_order

section eventually

/-! ### Relation with `eventually` comparisons of two functions -/

variables [preorder β] {s : set α}

lemma filter.eventually_le.is_local_max_on {f g : α → β} {a : α} (hle : g ≤ᶠ[𝓝[s] a] f)
  (hfga : f a = g a) (h : is_local_max_on f s a) : is_local_max_on g s a :=
hle.is_max_filter hfga h

lemma is_local_max_on.congr {f g : α → β} {a : α} (h : is_local_max_on f s a)
  (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) : is_local_max_on g s a :=
h.congr heq $ heq.eq_of_nhds_within hmem

lemma filter.eventually_eq.is_local_max_on_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
  (hmem : a ∈ s) : is_local_max_on f s a ↔ is_local_max_on g s a :=
heq.is_max_filter_iff $ heq.eq_of_nhds_within hmem

lemma filter.eventually_le.is_local_min_on {f g : α → β} {a : α} (hle : f ≤ᶠ[𝓝[s] a] g)
  (hfga : f a = g a) (h : is_local_min_on f s a) : is_local_min_on g s a :=
hle.is_min_filter hfga h

lemma is_local_min_on.congr {f g : α → β} {a : α} (h : is_local_min_on f s a)
  (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) : is_local_min_on g s a :=
h.congr heq $ heq.eq_of_nhds_within hmem

lemma filter.eventually_eq.is_local_min_on_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
  (hmem : a ∈ s) : is_local_min_on f s a ↔ is_local_min_on g s a :=
heq.is_min_filter_iff $ heq.eq_of_nhds_within hmem

lemma is_local_extr_on.congr {f g : α → β} {a : α} (h : is_local_extr_on f s a)
  (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) : is_local_extr_on g s a :=
h.congr heq $ heq.eq_of_nhds_within hmem

lemma filter.eventually_eq.is_local_extr_on_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g)
  (hmem : a ∈ s) : is_local_extr_on f s a ↔ is_local_extr_on g s a :=
heq.is_extr_filter_iff $ heq.eq_of_nhds_within hmem

lemma filter.eventually_le.is_local_max {f g : α → β} {a : α} (hle : g ≤ᶠ[𝓝 a] f) (hfga : f a = g a)
  (h : is_local_max f a) : is_local_max g a :=
hle.is_max_filter hfga h

lemma is_local_max.congr {f g : α → β} {a : α} (h : is_local_max f a) (heq : f =ᶠ[𝓝 a] g) :
  is_local_max g a :=
h.congr heq heq.eq_of_nhds

lemma filter.eventually_eq.is_local_max_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
  is_local_max f a ↔ is_local_max g a :=
heq.is_max_filter_iff heq.eq_of_nhds

lemma filter.eventually_le.is_local_min {f g : α → β} {a : α} (hle : f ≤ᶠ[𝓝 a] g) (hfga : f a = g a)
  (h : is_local_min f a) : is_local_min g a :=
hle.is_min_filter hfga h

lemma is_local_min.congr {f g : α → β} {a : α} (h : is_local_min f a) (heq : f =ᶠ[𝓝 a] g) :
  is_local_min g a :=
h.congr heq heq.eq_of_nhds

lemma filter.eventually_eq.is_local_min_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
  is_local_min f a ↔ is_local_min g a :=
heq.is_min_filter_iff heq.eq_of_nhds

lemma is_local_extr.congr {f g : α → β} {a : α} (h : is_local_extr f a) (heq : f =ᶠ[𝓝 a] g) :
  is_local_extr g a :=
h.congr heq heq.eq_of_nhds

lemma filter.eventually_eq.is_local_extr_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
  is_local_extr f a ↔ is_local_extr g a :=
heq.is_extr_filter_iff heq.eq_of_nhds

end eventually
