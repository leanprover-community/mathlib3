/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

(Least / Greatest) upper / lower bounds
-/
import order.complete_lattice
open set lattice

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {a a₁ a₂ : α} {b b₁ b₂ : β} {s t : set α}

section preorder

variables [preorder α] [preorder β] {f : α → β}

def upper_bounds (s : set α) : set α := { x | ∀a ∈ s, a ≤ x }
def lower_bounds (s : set α) : set α := { x | ∀a ∈ s, x ≤ a }
def is_least (s : set α) (a : α) : Prop := a ∈ s ∧ a ∈ lower_bounds s
def is_greatest (s : set α) (a : α) : Prop := a ∈ s ∧ a ∈ upper_bounds s
def is_lub (s : set α) : α → Prop := is_least (upper_bounds s)
def is_glb (s : set α) : α → Prop := is_greatest (lower_bounds s)

lemma upper_bounds_mono (h₁ : a₁ ≤ a₂) (h₂ : a₁ ∈ upper_bounds s) : a₂ ∈ upper_bounds s :=
λ a h, le_trans (h₂ _ h) h₁

lemma lower_bounds_mono (h₁ : a₂ ≤ a₁) (h₂ : a₁ ∈ lower_bounds s) : a₂ ∈ lower_bounds s :=
λ a h, le_trans h₁ (h₂ _ h)

lemma mem_upper_bounds_image (Hf : monotone f) (Ha : a ∈ upper_bounds s) :
  f a ∈ upper_bounds (f '' s) :=
ball_image_of_ball (assume x H, Hf (Ha _ ‹x ∈ s›))

lemma mem_lower_bounds_image (Hf : monotone f) (Ha : a ∈ lower_bounds s) :
  f a ∈ lower_bounds (f '' s) :=
ball_image_of_ball (assume x H, Hf (Ha _ ‹x ∈ s›))

lemma is_lub_singleton {a : α} : is_lub {a} a :=
by simp [is_lub, is_least, upper_bounds, lower_bounds] {contextual := tt}

lemma is_glb_singleton {a : α} : is_glb {a} a :=
by simp [is_glb, is_greatest, upper_bounds, lower_bounds] {contextual := tt}

end preorder

section partial_order
variables [partial_order α]

lemma eq_of_is_least_of_is_least (Ha : is_least s a₁) (Hb : is_least s a₂) : a₁ = a₂ :=
le_antisymm (Ha.right _ Hb.left) (Hb.right _ Ha.left)

lemma is_least_iff_eq_of_is_least (Ha : is_least s a₁) : is_least s a₂ ↔ a₁ = a₂ :=
iff.intro (eq_of_is_least_of_is_least Ha) (assume h, h ▸ Ha)

lemma eq_of_is_greatest_of_is_greatest (Ha : is_greatest s a₁) (Hb : is_greatest s a₂) : a₁ = a₂ :=
le_antisymm (Hb.right _ Ha.left) (Ha.right _ Hb.left)

lemma is_greatest_iff_eq_of_is_greatest (Ha : is_greatest s a₁) : is_greatest s a₂ ↔ a₁ = a₂ :=
iff.intro (eq_of_is_greatest_of_is_greatest Ha) (assume h, h ▸ Ha)

lemma eq_of_is_lub_of_is_lub : is_lub s a₁ → is_lub s a₂ → a₁ = a₂ :=
eq_of_is_least_of_is_least

lemma is_lub_iff_eq_of_is_lub : is_lub s a₁ → (is_lub s a₂ ↔ a₁ = a₂) :=
is_least_iff_eq_of_is_least

lemma is_lub_le_iff (h : is_lub s a₁) : a₁ ≤ a₂ ↔ a₂ ∈ upper_bounds s :=
⟨λ hl, upper_bounds_mono hl h.1, h.2 _⟩

lemma le_is_glb_iff (h : is_glb s a₁) : a₂ ≤ a₁ ↔ a₂ ∈ lower_bounds s :=
⟨λ hl, lower_bounds_mono hl h.1, h.2 _⟩

lemma eq_of_is_glb_of_is_glb : is_glb s a₁ → is_glb s a₂ → a₁ = a₂ :=
eq_of_is_greatest_of_is_greatest

lemma is_glb_iff_eq_of_is_glb : is_glb s a₁ → (is_glb s a₂ ↔ a₁ = a₂) :=
is_greatest_iff_eq_of_is_greatest

lemma ne_empty_of_is_lub [no_bot_order α] (hs : is_lub s a) : s ≠ ∅ :=
let ⟨a', ha'⟩ := no_bot a in
assume h,
have a ≤ a', from hs.right _ (by simp [upper_bounds, h]),
lt_irrefl a $ lt_of_le_of_lt this ha'

lemma ne_empty_of_is_glb [no_top_order α] (hs : is_glb s a) : s ≠ ∅ :=
let ⟨a', ha'⟩ := no_top a in
assume h,
have a' ≤ a, from hs.right _ (by simp [lower_bounds, h]),
lt_irrefl a $ lt_of_lt_of_le ha' this

end partial_order

section lattice

lemma is_glb_empty [order_top α] : is_glb ∅ (⊤:α) :=
by simp [is_glb, is_greatest, lower_bounds, upper_bounds]

lemma is_lub_empty [order_bot α] : is_lub ∅ (⊥:α) :=
by simp [is_lub, is_least, lower_bounds, upper_bounds]

lemma is_lub_union_sup [semilattice_sup α] (hs : is_lub s a₁) (ht : is_lub t a₂) :
  is_lub (s ∪ t) (a₁ ⊔ a₂) :=
⟨assume c h, h.cases_on (le_sup_left_of_le ∘ hs.left c) (le_sup_right_of_le ∘ ht.left c),
  assume c hc, sup_le
    (hs.right _ $ assume d hd, hc _ $ or.inl hd) (ht.right _ $ assume d hd, hc _ $ or.inr hd)⟩

lemma is_glb_union_inf [semilattice_inf α] (hs : is_glb s a₁) (ht : is_glb t a₂) :
  is_glb (s ∪ t) (a₁ ⊓ a₂) :=
⟨assume c h, h.cases_on (inf_le_left_of_le ∘ hs.left c) (inf_le_right_of_le ∘ ht.left c),
  assume c hc, le_inf
    (hs.right _ $ assume d hd, hc _ $ or.inl hd) (ht.right _ $ assume d hd, hc _ $ or.inr hd)⟩

lemma is_lub_insert_sup [semilattice_sup α] (h : is_lub s a₁) : is_lub (insert a₂ s) (a₂ ⊔ a₁) :=
by rw [insert_eq]; exact is_lub_union_sup is_lub_singleton h

lemma is_lub_iff_sup_eq [semilattice_sup α] : is_lub {a₁, a₂} a ↔ a₂ ⊔ a₁ = a :=
is_lub_iff_eq_of_is_lub $ is_lub_insert_sup $ is_lub_singleton

lemma is_glb_insert_inf [semilattice_inf α] (h : is_glb s a₁) : is_glb (insert a₂ s) (a₂ ⊓ a₁) :=
by rw [insert_eq]; exact is_glb_union_inf is_glb_singleton h

lemma is_glb_iff_inf_eq [semilattice_inf α] : is_glb {a₁, a₂} a ↔ a₂ ⊓ a₁ = a :=
is_glb_iff_eq_of_is_glb $ is_glb_insert_inf $ is_glb_singleton

end lattice

section linear_order
variables [linear_order α]

lemma lt_is_lub_iff (h : is_lub s a₁) : a₂ < a₁ ↔ ∃ a ∈ s, a₂ < a :=
by haveI := classical.dec;
   simpa [upper_bounds, not_ball] using
   not_congr (@is_lub_le_iff _ _ a₂ _ _ h)

lemma is_glb_lt_iff (h : is_glb s a₁) : a₁ < a₂ ↔ ∃ a ∈ s, a < a₂ :=
by haveI := classical.dec;
   simpa [lower_bounds, not_ball] using
   not_congr (@le_is_glb_iff _ _ a₂ _ _ h)

end linear_order

section complete_lattice
variables [complete_lattice α] {f : ι → α}

lemma is_lub_Sup : is_lub s (Sup s) := ⟨assume x, le_Sup, assume x, Sup_le⟩

lemma is_lub_supr : is_lub (range f) (⨆j, f j) :=
have is_lub (range f) (Sup (range f)), from is_lub_Sup,
by rwa [Sup_range] at this

lemma is_lub_iff_supr_eq : is_lub (range f) a ↔ (⨆j, f j) = a := is_lub_iff_eq_of_is_lub is_lub_supr
lemma is_lub_iff_Sup_eq : is_lub s a ↔ Sup s = a := is_lub_iff_eq_of_is_lub is_lub_Sup

lemma is_glb_Inf : is_glb s (Inf s) := ⟨assume a, Inf_le, assume a, le_Inf⟩

lemma is_glb_infi : is_glb (range f) (⨅j, f j) :=
have is_glb (range f) (Inf (range f)), from is_glb_Inf,
by rwa [Inf_range] at this

lemma is_glb_iff_infi_eq : is_glb (range f) a ↔ (⨅j, f j) = a := is_glb_iff_eq_of_is_glb is_glb_infi
lemma is_glb_iff_Inf_eq : is_glb s a ↔ Inf s = a := is_glb_iff_eq_of_is_glb is_glb_Inf

end complete_lattice
