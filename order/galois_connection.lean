/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Galois connections - order theoretic adjoints.
-/
import order.bounds
open function set lattice

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {a a₁ a₂ : α} {b b₁ b₂ : β}

/-- A Galois connection is a pair of functions `l` and `u` satisfying
  `l a ≤ b ↔ a ≤ u b`. They are closely connected to adjoint functors
  in category theory. -/
def galois_connection [preorder α] [preorder β] (l : α → β) (u : β → α) := ∀a b, l a ≤ b ↔ a ≤ u b

namespace galois_connection

section
variables [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u)

lemma monotone_intro (hu : monotone u) (hl : monotone l)
  (hul : ∀ a, a ≤ u (l a)) (hlu : ∀ a, l (u a) ≤ a) : galois_connection l u :=
assume a b, ⟨assume h, le_trans (hul _) (hu h), assume h, le_trans (hl h) (hlu _)⟩

include gc

lemma l_le {a : α} {b : β} : a ≤ u b → l a ≤ b :=
(gc _ _).mpr

lemma le_u {a : α} {b : β} : l a ≤ b → a ≤ u b :=
(gc _ _).mp

lemma le_u_l (a) : a ≤ u (l a) :=
gc.le_u $ le_refl _

lemma l_u_le (a) : l (u a) ≤ a :=
gc.l_le $ le_refl _

lemma monotone_u : monotone u :=
assume a b H, gc.le_u (le_trans (gc.l_u_le a) H)

lemma monotone_l : monotone l :=
assume a b H, gc.l_le (le_trans H (gc.le_u_l b))

lemma upper_bounds_l_image_subset {s : set α} : upper_bounds (l '' s) ⊆ u ⁻¹' upper_bounds s :=
assume b hb c, assume : c ∈ s, gc.le_u (hb _ (mem_image_of_mem _ ‹c ∈ s›))

lemma lower_bounds_u_image_subset {s : set β} : lower_bounds (u '' s) ⊆ l ⁻¹' lower_bounds s :=
assume a ha c, assume : c ∈ s, gc.l_le (ha _ (mem_image_of_mem _ ‹c ∈ s›))

lemma is_lub_l_image {s : set α} {a : α} (h : is_lub s a) : is_lub (l '' s) (l a) :=
⟨mem_upper_bounds_image gc.monotone_l $ and.elim_left ‹is_lub s a›,
  assume b hb, gc.l_le $ and.elim_right ‹is_lub s a› _ $ gc.upper_bounds_l_image_subset hb⟩

lemma is_glb_u_image {s : set β} {b : β} (h : is_glb s b) : is_glb (u '' s) (u b) :=
⟨mem_lower_bounds_image gc.monotone_u $ and.elim_left ‹is_glb s b›,
  assume a ha, gc.le_u $ and.elim_right ‹is_glb s b› _ $ gc.lower_bounds_u_image_subset ha⟩

lemma is_glb_l {a : α} : is_glb { b | a ≤ u b } (l a) :=
⟨assume b, gc.l_le, assume b h, h _ $ gc.le_u_l _⟩

lemma is_lub_u {b : β} : is_lub { a | l a ≤ b } (u b) :=
⟨assume b, gc.le_u, assume b h, h _ $ gc.l_u_le _⟩

end

section partial_order
variables [partial_order α] [partial_order β] {l : α → β} {u : β → α} (gc : galois_connection l u)
include gc

lemma u_l_u_eq_u : u ∘ l ∘ u = u :=
funext (assume x, le_antisymm (gc.monotone_u (gc.l_u_le _)) (gc.le_u_l _))

lemma l_u_l_eq_l : l ∘ u ∘ l = l :=
funext (assume x, le_antisymm (gc.l_u_le _) (gc.monotone_l (gc.le_u_l _)))

end partial_order

section order_top
variables [order_top α] [order_top β] {l : α → β} {u : β → α} (gc : galois_connection l u)
include gc

lemma u_top : u ⊤ = ⊤ :=
eq_of_is_glb_of_is_glb (gc.is_glb_u_image is_glb_empty) $ by simp [is_glb_empty, image_empty]

end order_top

section order_bot
variables [order_bot α] [order_bot β] {l : α → β} {u : β → α} (gc : galois_connection l u)
include gc

lemma l_bot : l ⊥ = ⊥ :=
eq_of_is_lub_of_is_lub (gc.is_lub_l_image is_lub_empty) $ by simp [is_lub_empty, image_empty]

end order_bot

section semilattice_sup
variables [semilattice_sup α] [semilattice_sup β] {l : α → β} {u : β → α} (gc : galois_connection l u)
include gc

lemma l_sup : l (a₁ ⊔ a₂) = l a₁ ⊔ l a₂ :=
have {l a₂, l a₁} = l '' {a₂, a₁}, by simp [image_insert_eq, image_singleton],
eq.symm $ is_lub_iff_sup_eq.mp $
  by rw [this]; exact gc.is_lub_l_image (is_lub_insert_sup is_lub_singleton)

end semilattice_sup

section semilattice_inf
variables [semilattice_inf α] [semilattice_inf β] {l : α → β} {u : β → α} (gc : galois_connection l u)
include gc

lemma u_inf : u (b₁ ⊓ b₂) = u b₁ ⊓ u b₂ :=
have {u b₂, u b₁} = u '' {b₂, b₁}, by simp [image_insert_eq, image_singleton],
eq.symm $ is_glb_iff_inf_eq.mp $
  by rw [this]; exact gc.is_glb_u_image (is_glb_insert_inf is_glb_singleton)

end semilattice_inf

section complete_lattice
variables [complete_lattice α] [complete_lattice β] {l : α → β} {u : β → α} (gc : galois_connection l u)
include gc

lemma l_supr {f : ι → α} : l (supr f) = (⨆i, l (f i)) :=
eq.symm $ is_lub_iff_supr_eq.mp $ show is_lub (range (l ∘ f)) (l (supr f)),
  by rw [range_comp, ← Sup_range]; exact gc.is_lub_l_image is_lub_Sup

lemma u_infi {f : ι → β} : u (infi f) = (⨅i, u (f i)) :=
eq.symm $ is_glb_iff_infi_eq.mp $ show is_glb (range (u ∘ f)) (u (infi f)),
  by rw [range_comp, ← Inf_range]; exact gc.is_glb_u_image is_glb_Inf

end complete_lattice

section complete_lattice
variables [complete_lattice α] [complete_lattice β] {l : α → β} {u : β → α} (gc : galois_connection l u)
include gc

lemma l_Sup {s : set α} : l (Sup s) = (⨆a∈s, l a) :=
by simp [Sup_eq_supr, gc.l_supr]

lemma u_Inf {s : set β} : u (Inf s) = (⨅a∈s, u a) :=
by simp [Inf_eq_infi, gc.u_infi]

end complete_lattice

/- Constructing Galois connections -/
section constructions

protected lemma id [pα : preorder α] : @galois_connection α α pα pα id id :=
assume a b, iff.intro (λx, x) (λx, x)

protected lemma compose [preorder α] [preorder β] [preorder γ]
  (l1 : α → β) (u1 : β → α) (l2 : β → γ) (u2 : γ → β)
  (gc1 : galois_connection l1 u1) (gc2 : galois_connection l2 u2) :
  galois_connection (l2 ∘ l1) (u1 ∘ u2) :=
by intros a b; rw [gc2, gc1]

protected lemma dual [pα : preorder α] [pβ : preorder β]
  {l : α → β} {u : β → α} (gc : galois_connection l u) :
  @galois_connection (order_dual β) (order_dual α) _ _ u l :=
assume a b, (gc _ _).symm

protected lemma dfun {ι : Type u} {α : ι → Type v} {β : ι → Type w}
  [∀i, preorder (α i)] [∀i, preorder (β i)]
  (l : Πi, α i → β i) (u : Πi, β i → α i) (gc : ∀i, galois_connection (l i) (u i)) :
  @galois_connection (Π i, α i) (Π i, β i) _ _ (λa i, l i (a i)) (λb i, u i (b i)) :=
assume a b, forall_congr $ assume i, gc i (a i) (b i)

end constructions

end galois_connection

namespace nat

lemma galois_connection_mul_div {k : ℕ} (h : k > 0) : galois_connection (λn, n * k) (λn, n / k) :=
assume x y, (le_div_iff_mul_le x y h).symm

end nat

/-- A Galois insertion is a Galois connection where `l ∘ u = id`. It also contains a constructive
choice function, to give better definitional equalities when lifting order structures. -/
structure galois_insertion {α β : Type*} [preorder α] [preorder β] (l : α → β) (u : β → α) :=
(choice : Πx:α, u (l x) ≤ x → β)
(gc : galois_connection l u)
(le_l_u : ∀x, x ≤ l (u x))
(choice_eq : ∀a h, choice a h = l a)

/-- Lift the bottom along a Galois connection -/
def galois_connection.lift_order_bot {α β : Type*} [order_bot α] [partial_order β]
  {l : α → β} {u : β → α} (gc : galois_connection l u) :
  order_bot β :=
{ bot    := l ⊥,
  bot_le := assume b, gc.l_le $ bot_le,
  .. ‹partial_order β› }

namespace galois_insertion
open lattice
variables [partial_order β] {l : α → β} {u : β → α}

lemma l_u_eq [preorder α] (gi : galois_insertion l u) (b : β) : l (u b) = b :=
le_antisymm (gi.gc.l_u_le _) (gi.le_l_u _)

/-- Lift the suprema along a Galois insertion -/
def lift_semilattice_sup [semilattice_sup α] (gi : galois_insertion l u) : semilattice_sup β :=
{ sup := λa b, l (u a ⊔ u b),
  le_sup_left  := assume a b, le_trans (gi.le_l_u a) $ gi.gc.monotone_l $ le_sup_left,
  le_sup_right := assume a b, le_trans (gi.le_l_u b) $ gi.gc.monotone_l $ le_sup_right,
  sup_le       := assume a b c hac hbc, gi.gc.l_le $ sup_le (gi.gc.monotone_u hac) (gi.gc.monotone_u hbc),
  .. ‹partial_order β› }

/-- Lift the infima along a Galois insertion -/
def lift_semilattice_inf [semilattice_inf α] (gi : galois_insertion l u) : semilattice_inf β :=
{ inf := λa b, gi.choice (u a ⊓ u b) $
    (le_inf (gi.gc.monotone_u $ gi.gc.l_le $ inf_le_left) (gi.gc.monotone_u $ gi.gc.l_le $ inf_le_right)),
  inf_le_left  := by simp only [gi.choice_eq]; exact assume a b, gi.gc.l_le inf_le_left,
  inf_le_right := by simp only [gi.choice_eq]; exact assume a b, gi.gc.l_le inf_le_right,
  le_inf       := by simp only [gi.choice_eq]; exact assume a b c hac hbc,
    le_trans (gi.le_l_u a) $ gi.gc.monotone_l $ le_inf (gi.gc.monotone_u hac) (gi.gc.monotone_u hbc),
  .. ‹partial_order β› }

/-- Lift the suprema and infima along a Galois insertion -/
def lift_lattice [lattice α] (gi : galois_insertion l u) : lattice β :=
{ .. gi.lift_semilattice_sup, .. gi.lift_semilattice_inf }

/-- Lift the top along a Galois insertion -/
def lift_order_top [order_top α] (gi : galois_insertion l u) : order_top β :=
{ top    := gi.choice ⊤ $ le_top,
  le_top := by simp only [gi.choice_eq]; exact assume b, le_trans (gi.le_l_u b) (gi.gc.monotone_l le_top),
  .. ‹partial_order β› }

/-- Lift the top, bottom, suprema, and infima along a Galois insertion -/
def lift_bounded_lattice [bounded_lattice α] (gi : galois_insertion l u) : bounded_lattice β :=
{ .. gi.lift_lattice, .. gi.lift_order_top, .. gi.gc.lift_order_bot }

/-- Lift all suprema and infima along a Galois insertion -/
def lift_complete_lattice [complete_lattice α] (gi : galois_insertion l u) : complete_lattice β :=
{ Sup := λs, l (⨆ b∈s, u b),
  Sup_le := assume s a hs, gi.gc.l_le $ supr_le $ assume b, supr_le $ assume hb, gi.gc.monotone_u $ hs _ hb,
  le_Sup := assume s a ha, le_trans (gi.le_l_u a) $ gi.gc.monotone_l $ le_supr_of_le a $ le_supr_of_le ha $ le_refl _,
  Inf := λs, gi.choice (⨅ b∈s, u b) $ le_infi $ assume b, le_infi $ assume hb,
    gi.gc.monotone_u $ gi.gc.l_le $ infi_le_of_le b $ infi_le_of_le hb $ le_refl _,
  Inf_le := by simp only [gi.choice_eq]; exact
    assume s a ha, gi.gc.l_le $ infi_le_of_le a $ infi_le_of_le ha $ le_refl _,
  le_Inf := by simp only [gi.choice_eq]; exact
    assume s a hs, le_trans (gi.le_l_u a) $ gi.gc.monotone_l $ le_infi $ assume b,
    show u a ≤ ⨅ (H : b ∈ s), u b, from le_infi $ assume hb, gi.gc.monotone_u $ hs _ hb,
  .. gi.lift_bounded_lattice }

end galois_insertion
