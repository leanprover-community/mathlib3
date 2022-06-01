/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.complete_lattice
import order.synonym

/-!
# Galois connections, insertions and coinsertions

Galois connections are order theoretic adjoints, i.e. a pair of functions `u` and `l`,
such that `∀ a b, l a ≤ b ↔ a ≤ u b`.

## Main definitions

* `galois_connection`: A Galois connection is a pair of functions `l` and `u` satisfying
  `l a ≤ b ↔ a ≤ u b`. They are special cases of adjoint functors in category theory,
  but do not depend on the category theory library in mathlib.
* `galois_insertion`: A Galois insertion is a Galois connection where `l ∘ u = id`
* `galois_coinsertion`: A Galois coinsertion is a Galois connection where `u ∘ l = id`

## Implementation details

Galois insertions can be used to lift order structures from one type to another.
For example if `α` is a complete lattice, and `l : α → β`, and `u : β → α` form a Galois insertion,
then `β` is also a complete lattice. `l` is the lower adjoint and `u` is the upper adjoint.

An example of a Galois insertion is in group theory. If `G` is a group, then there is a Galois
insertion between the set of subsets of `G`, `set G`, and the set of subgroups of `G`,
`subgroup G`. The lower adjoint is `subgroup.closure`, taking the `subgroup` generated by a `set`,
and the upper adjoint is the coercion from `subgroup G` to `set G`, taking the underlying set
of a subgroup.

Naively lifting a lattice structure along this Galois insertion would mean that the definition
of `inf` on subgroups would be `subgroup.closure (↑S ∩ ↑T)`. This is an undesirable definition
because the intersection of subgroups is already a subgroup, so there is no need to take the
closure. For this reason a `choice` function is added as a field to the `galois_insertion`
structure. It has type `Π S : set G, ↑(closure S) ≤ S → subgroup G`. When `↑(closure S) ≤ S`, then
`S` is already a subgroup, so this function can be defined using `subgroup.mk` and not `closure`.
This means the infimum of subgroups will be defined to be the intersection of sets, paired
with a proof that intersection of subgroups is a subgroup, rather than the closure of the
intersection.
-/

open function order_dual set

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {κ : ι → Sort*} {a a₁ a₂ : α}
  {b b₁ b₂ : β}

/-- A Galois connection is a pair of functions `l` and `u` satisfying
  `l a ≤ b ↔ a ≤ u b`. They are special cases of adjoint functors in category theory,
    but do not depend on the category theory library in mathlib. -/
def galois_connection [preorder α] [preorder β] (l : α → β) (u : β → α) := ∀ a b, l a ≤ b ↔ a ≤ u b

/-- Makes a Galois connection from an order-preserving bijection. -/
theorem order_iso.to_galois_connection [preorder α] [preorder β] (oi : α ≃o β) :
  galois_connection oi oi.symm :=
λ b g, oi.rel_symm_apply.symm

namespace galois_connection

section
variables [preorder α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u)

lemma monotone_intro (hu : monotone u) (hl : monotone l)
  (hul : ∀ a, a ≤ u (l a)) (hlu : ∀ a, l (u a) ≤ a) : galois_connection l u :=
λ a b, ⟨λ h, (hul _).trans (hu h), λ h, (hl h).trans (hlu _)⟩

include gc

protected lemma dual {l : α → β} {u : β → α} (gc : galois_connection l u) :
  galois_connection (order_dual.to_dual ∘ u ∘ order_dual.of_dual)
    (order_dual.to_dual ∘ l ∘ order_dual.of_dual) :=
λ a b, (gc b a).symm

lemma le_iff_le {a : α} {b : β} : l a ≤ b ↔ a ≤ u b :=
gc _ _

lemma l_le {a : α} {b : β} : a ≤ u b → l a ≤ b :=
(gc _ _).mpr

lemma le_u {a : α} {b : β} : l a ≤ b → a ≤ u b :=
(gc _ _).mp

lemma le_u_l (a) : a ≤ u (l a) :=
gc.le_u $ le_rfl

lemma l_u_le (a) : l (u a) ≤ a :=
gc.l_le $ le_rfl

lemma monotone_u : monotone u :=
λ a b H, gc.le_u ((gc.l_u_le a).trans H)

lemma monotone_l : monotone l :=
gc.dual.monotone_u.dual

lemma upper_bounds_l_image (s : set α) : upper_bounds (l '' s) = u ⁻¹' upper_bounds s :=
set.ext $ λ b, by simp [upper_bounds, gc _ _]

lemma lower_bounds_u_image (s : set β) : lower_bounds (u '' s) = l ⁻¹' lower_bounds s :=
gc.dual.upper_bounds_l_image s

lemma bdd_above_l_image {s : set α} : bdd_above (l '' s) ↔ bdd_above s :=
⟨λ ⟨x, hx⟩, ⟨u x, by rwa [gc.upper_bounds_l_image] at hx⟩, gc.monotone_l.map_bdd_above⟩

lemma bdd_below_u_image {s : set β} : bdd_below (u '' s) ↔ bdd_below s :=
gc.dual.bdd_above_l_image

lemma is_lub_l_image {s : set α} {a : α} (h : is_lub s a) : is_lub (l '' s) (l a) :=
⟨gc.monotone_l.mem_upper_bounds_image h.left,
  λ b hb, gc.l_le $ h.right $ by rwa [gc.upper_bounds_l_image] at hb⟩

lemma is_glb_u_image {s : set β} {b : β} (h : is_glb s b) : is_glb (u '' s) (u b) :=
gc.dual.is_lub_l_image h

lemma is_least_l {a : α} : is_least {b | a ≤ u b} (l a) :=
⟨gc.le_u_l _, λ b hb, gc.l_le hb⟩

lemma is_greatest_u {b : β} : is_greatest {a | l a ≤ b} (u b) :=
gc.dual.is_least_l

lemma is_glb_l {a : α} : is_glb {b | a ≤ u b} (l a) := gc.is_least_l.is_glb

lemma is_lub_u {b : β} : is_lub { a | l a ≤ b } (u b) := gc.is_greatest_u.is_lub

/-- If `(l, u)` is a Galois connection, then the relation `x ≤ u (l y)` is a transitive relation.
If `l` is a closure operator (`submodule.span`, `subgroup.closure`, ...) and `u` is the coercion to
`set`, this reads as "if `U` is in the closure of `V` and `V` is in the closure of `W` then `U` is
in the closure of `W`". -/
lemma le_u_l_trans {x y z : α} (hxy : x ≤ u (l y)) (hyz : y ≤ u (l z)) :
  x ≤ u (l z) :=
hxy.trans (gc.monotone_u $ gc.l_le hyz)

lemma l_u_le_trans {x y z : β} (hxy : l (u x) ≤ y) (hyz : l (u y) ≤ z) :
  l (u x) ≤ z :=
(gc.monotone_l $ gc.le_u hxy).trans hyz

end

section partial_order
variables [partial_order α] [preorder β] {l : α → β} {u : β → α} (gc : galois_connection l u)
include gc

lemma u_l_u_eq_u (b : β) : u (l (u b)) = u b :=
(gc.monotone_u (gc.l_u_le _)).antisymm (gc.le_u_l _)

lemma u_l_u_eq_u' : u ∘ l ∘ u = u := funext gc.u_l_u_eq_u

lemma u_unique {l' : α → β} {u' : β → α} (gc' : galois_connection l' u')
  (hl : ∀ a, l a = l' a) {b : β} : u b = u' b :=
le_antisymm (gc'.le_u $ hl (u b) ▸ gc.l_u_le _)
  (gc.le_u $ (hl (u' b)).symm ▸ gc'.l_u_le _)

/-- If there exists a `b` such that `a = u a`, then `b = l a` is one such element. -/
lemma exists_eq_u (a : α) : (∃ b : β, a = u b) ↔ a = u (l a) :=
⟨λ ⟨S, hS⟩, hS.symm ▸ (gc.u_l_u_eq_u _).symm, λ HI, ⟨_, HI⟩ ⟩

lemma u_eq {z : α} {y : β} :
  u y = z ↔ ∀ x, x ≤ z ↔ l x ≤ y :=
begin
  split,
  { rintros rfl x,
    exact (gc x y).symm },
  { intros H,
    exact ((H $ u y).mpr (gc.l_u_le y)).antisymm ((gc _ _).mp $ (H z).mp le_rfl) }
end

end partial_order

section partial_order
variables [preorder α] [partial_order β] {l : α → β} {u : β → α} (gc : galois_connection l u)
include gc

lemma l_u_l_eq_l (a : α) : l (u (l a)) = l a :=
(gc.l_u_le _).antisymm (gc.monotone_l (gc.le_u_l _))

lemma l_u_l_eq_l' : l ∘ u ∘ l = l := funext gc.l_u_l_eq_l

lemma l_unique {l' : α → β} {u' : β → α} (gc' : galois_connection l' u')
  (hu : ∀ b, u b = u' b) {a : α} : l a = l' a :=
le_antisymm (gc.l_le $ (hu (l' a)).symm ▸ gc'.le_u_l _)
  (gc'.l_le $ hu (l a) ▸ gc.le_u_l _)

/-- If there exists an `a` such that `b = l a`, then `a = u b` is one such element. -/
lemma exists_eq_l (b : β) : (∃ a : α, b = l a) ↔ b = l (u b) :=
⟨λ ⟨S, hS⟩, hS.symm ▸ (gc.l_u_l_eq_l _).symm, λ HI, ⟨_, HI⟩ ⟩

lemma l_eq  {x : α} {z : β} :
  l x = z ↔ ∀ y, z ≤ y ↔ x ≤ u y :=
begin
  split,
  { rintros rfl y,
    exact gc x y },
  { intros H,
    exact ((gc _ _).mpr $ (H z).mp le_rfl).antisymm ((H $ l x).mpr (gc.le_u_l x)) }
end

end partial_order

section order_top
variables [partial_order α] [preorder β] [order_top α] [order_top β] {l : α → β} {u : β → α}
  (gc : galois_connection l u)
include gc

lemma u_top : u ⊤ = ⊤ := top_unique $ gc.le_u le_top

end order_top

section order_bot
variables [preorder α] [partial_order β] [order_bot α] [order_bot β] {l : α → β} {u : β → α}
  (gc : galois_connection l u)
include gc

lemma l_bot : l ⊥ = ⊥ := gc.dual.u_top

end order_bot

section semilattice_sup
variables [semilattice_sup α] [semilattice_sup β] {l : α → β} {u : β → α}
  (gc : galois_connection l u)
include gc

lemma l_sup : l (a₁ ⊔ a₂) = l a₁ ⊔ l a₂ :=
(gc.is_lub_l_image is_lub_pair).unique $ by simp only [image_pair, is_lub_pair]

end semilattice_sup

section semilattice_inf
variables [semilattice_inf α] [semilattice_inf β] {l : α → β} {u : β → α}
  (gc : galois_connection l u)
include gc

lemma u_inf : u (b₁ ⊓ b₂) = u b₁ ⊓ u b₂ := gc.dual.l_sup

end semilattice_inf

section complete_lattice
variables [complete_lattice α] [complete_lattice β] {l : α → β} {u : β → α}
  (gc : galois_connection l u)
include gc

lemma l_supr {f : ι → α} : l (supr f) = ⨆ i, l (f i) :=
eq.symm $ is_lub.supr_eq $ show is_lub (range (l ∘ f)) (l (supr f)),
  by rw [range_comp, ← Sup_range]; exact gc.is_lub_l_image (is_lub_Sup _)

lemma l_supr₂ {f : Π i, κ i → α} : l (⨆ i j, f i j) = ⨆ i j, l (f i j) := by simp_rw gc.l_supr

lemma u_infi {f : ι → β} : u (infi f) = ⨅ i, u (f i) := gc.dual.l_supr
lemma u_infi₂ {f : Π i, κ i → β} : u (⨅ i j, f i j) = ⨅ i j, u (f i j) := gc.dual.l_supr₂

lemma l_Sup {s : set α} : l (Sup s) = ⨆ a ∈ s, l a := by simp only [Sup_eq_supr, gc.l_supr]
lemma u_Inf {s : set β} : u (Inf s) = ⨅ a ∈ s, u a := gc.dual.l_Sup

end complete_lattice

section linear_order
variables [linear_order α] [linear_order β] {l : α → β} {u : β → α}
  (gc : galois_connection l u)

lemma lt_iff_lt {a : α} {b : β} : b < l a ↔ u b < a := lt_iff_lt_of_le_iff_le (gc a b)

end linear_order

/- Constructing Galois connections -/
section constructions

protected lemma id [pα : preorder α] : @galois_connection α α pα pα id id :=
λ a b, iff.intro (λ x, x) (λ x, x)

protected lemma compose [preorder α] [preorder β] [preorder γ]
  {l1 : α → β} {u1 : β → α} {l2 : β → γ} {u2 : γ → β}
  (gc1 : galois_connection l1 u1) (gc2 : galois_connection l2 u2) :
  galois_connection (l2 ∘ l1) (u1 ∘ u2) :=
by intros a b; rw [gc2, gc1]

protected lemma dfun {ι : Type u} {α : ι → Type v} {β : ι → Type w}
  [∀ i, preorder (α i)] [∀ i, preorder (β i)]
  (l : Πi, α i → β i) (u : Πi, β i → α i) (gc : ∀ i, galois_connection (l i) (u i)) :
  galois_connection (λ (a : Π i, α i) i, l i (a i)) (λ b i, u i (b i)) :=
λ a b, forall_congr $ λ i, gc i (a i) (b i)

end constructions

lemma l_comm_of_u_comm
  {X : Type*} [preorder X] {Y : Type*} [preorder Y]
  {Z : Type*} [preorder Z] {W : Type*} [partial_order W]
  {lYX : X → Y} {uXY : Y → X} (hXY : galois_connection lYX uXY)
  {lWZ : Z → W} {uZW : W → Z} (hZW : galois_connection lWZ uZW)
  {lWY : Y → W} {uYW : W → Y} (hWY : galois_connection lWY uYW)
  {lZX : X → Z} {uXZ : Z → X} (hXZ : galois_connection lZX uXZ)
  (h : ∀ w, uXZ (uZW w) = uXY (uYW w)) {x : X} : lWZ (lZX x) = lWY (lYX x) :=
(hXZ.compose hZW).l_unique (hXY.compose hWY) h

lemma u_comm_of_l_comm
  {X : Type*} [partial_order X] {Y : Type*} [preorder Y]
  {Z : Type*} [preorder Z] {W : Type*} [preorder W]
  {lYX : X → Y} {uXY : Y → X} (hXY : galois_connection lYX uXY)
  {lWZ : Z → W} {uZW : W → Z} (hZW : galois_connection lWZ uZW)
  {lWY : Y → W} {uYW : W → Y} (hWY : galois_connection lWY uYW)
  {lZX : X → Z} {uXZ : Z → X} (hXZ : galois_connection lZX uXZ)
  (h : ∀ x, lWZ (lZX x) = lWY (lYX x)) {w : W} : uXZ (uZW w) = uXY (uYW w) :=
(hXZ.compose hZW).u_unique (hXY.compose hWY) h

lemma l_comm_iff_u_comm
  {X : Type*} [partial_order X] {Y : Type*} [preorder Y]
  {Z : Type*} [preorder Z] {W : Type*} [partial_order W]
  {lYX : X → Y} {uXY : Y → X} (hXY : galois_connection lYX uXY)
  {lWZ : Z → W} {uZW : W → Z} (hZW : galois_connection lWZ uZW)
  {lWY : Y → W} {uYW : W → Y} (hWY : galois_connection lWY uYW)
  {lZX : X → Z} {uXZ : Z → X} (hXZ : galois_connection lZX uXZ) :
  (∀ w : W, uXZ (uZW w) = uXY (uYW w)) ↔ ∀ x : X, lWZ (lZX x) = lWY (lYX x) :=
⟨hXY.l_comm_of_u_comm hZW hWY hXZ, hXY.u_comm_of_l_comm hZW hWY hXZ⟩

end galois_connection

namespace order_iso

variables [preorder α] [preorder β]

@[simp] lemma bdd_above_image (e : α ≃o β) {s : set α} : bdd_above (e '' s) ↔ bdd_above s :=
e.to_galois_connection.bdd_above_l_image

@[simp] lemma bdd_below_image (e : α ≃o β) {s : set α} : bdd_below (e '' s) ↔ bdd_below s :=
e.dual.bdd_above_image

@[simp] lemma bdd_above_preimage (e : α ≃o β) {s : set β} : bdd_above (e ⁻¹' s) ↔ bdd_above s :=
by rw [← e.bdd_above_image, e.image_preimage]

@[simp] lemma bdd_below_preimage (e : α ≃o β) {s : set β} : bdd_below (e ⁻¹' s) ↔ bdd_below s :=
by rw [← e.bdd_below_image, e.image_preimage]

end order_iso

namespace nat

lemma galois_connection_mul_div {k : ℕ} (h : 0 < k) : galois_connection (λ n, n * k) (λ n, n / k) :=
λ x y, (le_div_iff_mul_le x y h).symm

end nat

/-- A Galois insertion is a Galois connection where `l ∘ u = id`. It also contains a constructive
choice function, to give better definitional equalities when lifting order structures. Dual
to `galois_coinsertion` -/
@[nolint has_inhabited_instance]
structure galois_insertion {α β : Type*} [preorder α] [preorder β] (l : α → β) (u : β → α) :=
(choice : Πx : α, u (l x) ≤ x → β)
(gc : galois_connection l u)
(le_l_u : ∀ x, x ≤ l (u x))
(choice_eq : ∀ a h, choice a h = l a)

/-- A constructor for a Galois insertion with the trivial `choice` function. -/
def galois_insertion.monotone_intro {α β : Type*} [preorder α] [preorder β] {l : α → β} {u : β → α}
  (hu : monotone u) (hl : monotone l) (hul : ∀ a, a ≤ u (l a)) (hlu : ∀ b, l (u b) = b) :
  galois_insertion l u :=
{ choice := λ x _, l x,
  gc := galois_connection.monotone_intro hu hl hul (λ b, le_of_eq (hlu b)),
  le_l_u := λ b, le_of_eq $ (hlu b).symm,
  choice_eq := λ _ _, rfl }

/-- Makes a Galois insertion from an order-preserving bijection. -/
protected def order_iso.to_galois_insertion [preorder α] [preorder β] (oi : α ≃o β) :
  galois_insertion oi oi.symm :=
{ choice := λ b h, oi b,
  gc := oi.to_galois_connection,
  le_l_u := λ g, le_of_eq (oi.right_inv g).symm,
  choice_eq := λ b h, rfl }

/-- Make a `galois_insertion l u` from a `galois_connection l u` such that `∀ b, b ≤ l (u b)` -/
def galois_connection.to_galois_insertion {α β : Type*} [preorder α] [preorder β]
  {l : α → β} {u : β → α} (gc : galois_connection l u) (h : ∀ b, b ≤ l (u b)) :
  galois_insertion l u :=
{ choice := λ x _, l x,
  gc := gc,
  le_l_u := h,
  choice_eq := λ _ _, rfl }

/-- Lift the bottom along a Galois connection -/
def galois_connection.lift_order_bot {α β : Type*} [preorder α] [order_bot α] [partial_order β]
  {l : α → β} {u : β → α} (gc : galois_connection l u) :
  order_bot β :=
{ bot    := l ⊥,
  bot_le := λ b, gc.l_le $ bot_le }

namespace galois_insertion

variables {l : α → β} {u : β → α}

lemma l_u_eq [preorder α] [partial_order β] (gi : galois_insertion l u) (b : β) :
  l (u b) = b :=
(gi.gc.l_u_le _).antisymm (gi.le_l_u _)

lemma left_inverse_l_u [preorder α] [partial_order β] (gi : galois_insertion l u) :
  left_inverse l u :=
gi.l_u_eq

lemma l_surjective [preorder α] [partial_order β] (gi : galois_insertion l u) :
  surjective l :=
gi.left_inverse_l_u.surjective

lemma u_injective [preorder α] [partial_order β] (gi : galois_insertion l u) :
  injective u :=
gi.left_inverse_l_u.injective

lemma l_sup_u [semilattice_sup α] [semilattice_sup β] (gi : galois_insertion l u) (a b : β) :
  l (u a ⊔ u b) = a ⊔ b :=
calc l (u a ⊔ u b) = l (u a) ⊔ l (u b) : gi.gc.l_sup
               ... = a ⊔ b : by simp only [gi.l_u_eq]

lemma l_supr_u [complete_lattice α] [complete_lattice β] (gi : galois_insertion l u)
  {ι : Sort x} (f : ι → β) :
  l (⨆ i, u (f i)) = ⨆ i, (f i) :=
calc l (⨆ (i : ι), u (f i)) = ⨆ (i : ι), l (u (f i)) : gi.gc.l_supr
                        ... = ⨆ (i : ι), f i : congr_arg _ $ funext $ λ i, gi.l_u_eq (f i)

lemma l_bsupr_u [complete_lattice α] [complete_lattice β] (gi : galois_insertion l u)
  {ι : Sort x} {p : ι → Prop} (f : Π i (hi : p i), β) :
  l (⨆ i hi, u (f i hi)) = ⨆ i hi, f i hi :=
by simp only [supr_subtype', gi.l_supr_u]

lemma l_Sup_u_image [complete_lattice α] [complete_lattice β] (gi : galois_insertion l u)
  (s : set β) : l (Sup (u '' s)) = Sup s :=
by rw [Sup_image, gi.l_bsupr_u, Sup_eq_supr]

lemma l_inf_u [semilattice_inf α] [semilattice_inf β] (gi : galois_insertion l u) (a b : β) :
  l (u a ⊓ u b) = a ⊓ b :=
calc l (u a ⊓ u b) = l (u (a ⊓ b)) : congr_arg l gi.gc.u_inf.symm
               ... = a ⊓ b : by simp only [gi.l_u_eq]

lemma l_infi_u [complete_lattice α] [complete_lattice β] (gi : galois_insertion l u)
  {ι : Sort x} (f : ι → β) :
  l (⨅ i, u (f i)) = ⨅ i, f i :=
calc l (⨅ (i : ι), u (f i)) = l (u (⨅ (i : ι), (f i))) : congr_arg l gi.gc.u_infi.symm
                        ... = ⨅ (i : ι), f i : gi.l_u_eq _

lemma l_binfi_u [complete_lattice α] [complete_lattice β] (gi : galois_insertion l u)
  {ι : Sort x} {p : ι → Prop} (f : Π i (hi : p i), β) :
  l (⨅ i hi, u (f i hi)) = ⨅ i hi, f i hi :=
by simp only [infi_subtype', gi.l_infi_u]

lemma l_Inf_u_image [complete_lattice α] [complete_lattice β] (gi : galois_insertion l u)
  (s : set β) : l (Inf (u '' s)) = Inf s :=
by rw [Inf_image, gi.l_binfi_u, Inf_eq_infi]

lemma l_infi_of_ul_eq_self [complete_lattice α] [complete_lattice β] (gi : galois_insertion l u)
  {ι : Sort x} (f : ι → α) (hf : ∀ i, u (l (f i)) = f i) :
  l (⨅ i, f i) = ⨅ i, l (f i) :=
calc l (⨅ i, (f i)) =  l ⨅ (i : ι), (u (l (f i))) : by simp [hf]
                ... = ⨅ i, l (f i) : gi.l_infi_u _

lemma l_binfi_of_ul_eq_self [complete_lattice α] [complete_lattice β] (gi : galois_insertion l u)
  {ι : Sort x} {p : ι → Prop} (f : Π i (hi : p i), α) (hf : ∀ i hi, u (l (f i hi)) = f i hi) :
  l (⨅ i hi, f i hi) = ⨅ i hi, l (f i hi) :=
by { rw [infi_subtype', infi_subtype'], exact gi.l_infi_of_ul_eq_self _ (λ _, hf _ _) }

lemma u_le_u_iff [preorder α] [preorder β] (gi : galois_insertion l u) {a b} :
  u a ≤ u b ↔ a ≤ b :=
⟨λ h, (gi.le_l_u _).trans (gi.gc.l_le h),
    λ h, gi.gc.monotone_u h⟩

lemma strict_mono_u [preorder α] [preorder β] (gi : galois_insertion l u) : strict_mono u :=
strict_mono_of_le_iff_le $ λ _ _, gi.u_le_u_iff.symm

lemma is_lub_of_u_image [preorder α] [preorder β] (gi : galois_insertion l u) {s : set β} {a : α}
  (hs : is_lub (u '' s) a) : is_lub s (l a) :=
⟨λ x hx, (gi.le_l_u x).trans $ gi.gc.monotone_l $ hs.1 $ mem_image_of_mem _ hx,
  λ x hx, gi.gc.l_le $ hs.2 $ gi.gc.monotone_u.mem_upper_bounds_image hx⟩

lemma is_glb_of_u_image [preorder α] [preorder β] (gi : galois_insertion l u) {s : set β} {a : α}
  (hs : is_glb (u '' s) a) : is_glb s (l a) :=
⟨λ x hx, gi.gc.l_le $ hs.1 $ mem_image_of_mem _ hx,
  λ x hx, (gi.le_l_u x).trans $ gi.gc.monotone_l $ hs.2 $
    gi.gc.monotone_u.mem_lower_bounds_image hx⟩

section lift

variables [partial_order β]

/-- Lift the suprema along a Galois insertion -/
@[reducible] -- See note [reducible non instances]
def lift_semilattice_sup [semilattice_sup α] (gi : galois_insertion l u) : semilattice_sup β :=
{ sup := λ a b, l (u a ⊔ u b),
  le_sup_left  := λ a b, (gi.le_l_u a).trans $ gi.gc.monotone_l $ le_sup_left,
  le_sup_right := λ a b, (gi.le_l_u b).trans $ gi.gc.monotone_l $ le_sup_right,
  sup_le       := λ a b c hac hbc,
    gi.gc.l_le $ sup_le (gi.gc.monotone_u hac) (gi.gc.monotone_u hbc),
  .. ‹partial_order β› }

/-- Lift the infima along a Galois insertion -/
@[reducible] -- See note [reducible non instances]
def lift_semilattice_inf [semilattice_inf α] (gi : galois_insertion l u) : semilattice_inf β :=
{ inf := λ a b, gi.choice (u a ⊓ u b) $
    (le_inf (gi.gc.monotone_u $ gi.gc.l_le $ inf_le_left)
      (gi.gc.monotone_u $ gi.gc.l_le $ inf_le_right)),
  inf_le_left  := by simp only [gi.choice_eq]; exact λ a b, gi.gc.l_le inf_le_left,
  inf_le_right := by simp only [gi.choice_eq]; exact λ a b, gi.gc.l_le inf_le_right,
  le_inf       := by simp only [gi.choice_eq]; exact λ a b c hac hbc,
    (gi.le_l_u a).trans $ gi.gc.monotone_l $ le_inf (gi.gc.monotone_u hac) (gi.gc.monotone_u hbc),
  .. ‹partial_order β› }

/-- Lift the suprema and infima along a Galois insertion -/
@[reducible] -- See note [reducible non instances]
def lift_lattice [lattice α] (gi : galois_insertion l u) : lattice β :=
{ .. gi.lift_semilattice_sup, .. gi.lift_semilattice_inf }

/-- Lift the top along a Galois insertion -/
@[reducible] -- See note [reducible non instances]
def lift_order_top [preorder α] [order_top α] (gi : galois_insertion l u) : order_top β :=
{ top    := gi.choice ⊤ $ le_top,
  le_top := by simp only [gi.choice_eq]; exact λ b, (gi.le_l_u b).trans (gi.gc.monotone_l le_top) }

/-- Lift the top, bottom, suprema, and infima along a Galois insertion -/
@[reducible] -- See note [reducible non instances]
def lift_bounded_order [preorder α] [bounded_order α]
  (gi : galois_insertion l u) : bounded_order β :=
{ .. gi.lift_order_top, .. gi.gc.lift_order_bot }

/-- Lift all suprema and infima along a Galois insertion -/
@[reducible] -- See note [reducible non instances]
def lift_complete_lattice [complete_lattice α] (gi : galois_insertion l u) : complete_lattice β :=
{ Sup := λ s, l (Sup (u '' s)),
  Sup_le := λ s, (gi.is_lub_of_u_image (is_lub_Sup _)).2,
  le_Sup := λ s, (gi.is_lub_of_u_image (is_lub_Sup _)).1,
  Inf := λ s, gi.choice (Inf (u '' s)) $ (is_glb_Inf _).2 $ gi.gc.monotone_u.mem_lower_bounds_image
    (gi.is_glb_of_u_image $ is_glb_Inf _).1,
  Inf_le := λ s, by { rw gi.choice_eq, exact (gi.is_glb_of_u_image (is_glb_Inf _)).1 },
  le_Inf := λ s, by { rw gi.choice_eq, exact (gi.is_glb_of_u_image (is_glb_Inf _)).2 },
  .. gi.lift_bounded_order,
  .. gi.lift_lattice }

end lift

end galois_insertion

/-- A Galois coinsertion is a Galois connection where `u ∘ l = id`. It also contains a constructive
choice function, to give better definitional equalities when lifting order structures. Dual to
`galois_insertion` -/
@[nolint has_inhabited_instance]
structure galois_coinsertion [preorder α] [preorder β] (l : α → β) (u : β → α) :=
(choice : Πx : β, x ≤ l (u x) → α)
(gc : galois_connection l u)
(u_l_le : ∀ x, u (l x) ≤ x)
(choice_eq : ∀ a h, choice a h = u a)

/-- Make a `galois_insertion` between `αᵒᵈ` and `βᵒᵈ` from a `galois_coinsertion` between `α` and
`β`. -/
def galois_coinsertion.dual [preorder α] [preorder β] {l : α → β} {u : β → α} :
  galois_coinsertion l u → galois_insertion (to_dual ∘ u ∘ of_dual) (to_dual ∘ l ∘ of_dual) :=
λ x, ⟨x.1, x.2.dual, x.3, x.4⟩

/-- Make a `galois_coinsertion` between `αᵒᵈ` and `βᵒᵈ` from a `galois_insertion` between `α` and
`β`. -/
def galois_insertion.dual [preorder α] [preorder β] {l : α → β} {u : β → α} :
  galois_insertion l u → galois_coinsertion (to_dual ∘ u ∘ of_dual) (to_dual ∘ l ∘ of_dual) :=
λ x, ⟨x.1, x.2.dual, x.3, x.4⟩

/-- Make a `galois_insertion` between `α` and `β` from a `galois_coinsertion` between `αᵒᵈ` and
`βᵒᵈ`. -/
def galois_coinsertion.of_dual [preorder α] [preorder β] {l : αᵒᵈ → βᵒᵈ} {u : βᵒᵈ → αᵒᵈ} :
  galois_coinsertion l u → galois_insertion (of_dual ∘ u ∘ to_dual) (of_dual ∘ l ∘ to_dual) :=
λ x, ⟨x.1, x.2.dual, x.3, x.4⟩

/-- Make a `galois_coinsertion` between `α` and `β` from a `galois_insertion` between `αᵒᵈ` and
`βᵒᵈ`. -/
def galois_insertion.of_dual [preorder α] [preorder β] {l : αᵒᵈ → βᵒᵈ} {u : βᵒᵈ → αᵒᵈ} :
  galois_insertion l u → galois_coinsertion (of_dual ∘ u ∘ to_dual) (of_dual ∘ l ∘ to_dual) :=
λ x, ⟨x.1, x.2.dual, x.3, x.4⟩

/-- Makes a Galois coinsertion from an order-preserving bijection. -/
protected def order_iso.to_galois_coinsertion [preorder α] [preorder β] (oi : α ≃o β) :
  galois_coinsertion oi oi.symm :=
{ choice := λ b h, oi.symm b,
  gc := oi.to_galois_connection,
  u_l_le := λ g, le_of_eq (oi.left_inv g),
  choice_eq := λ b h, rfl }

/-- A constructor for a Galois coinsertion with the trivial `choice` function. -/
def galois_coinsertion.monotone_intro [preorder α] [preorder β] {l : α → β} {u : β → α}
  (hu : monotone u) (hl : monotone l) (hlu : ∀ b, l (u b) ≤ b)
  (hul : ∀ a, u (l a) = a) :
  galois_coinsertion l u :=
(galois_insertion.monotone_intro hl.dual hu.dual hlu hul).of_dual

/-- Make a `galois_coinsertion l u` from a `galois_connection l u` such that `∀ b, b ≤ l (u b)` -/
def galois_connection.to_galois_coinsertion {α β : Type*} [preorder α] [preorder β]
  {l : α → β} {u : β → α} (gc : galois_connection l u) (h : ∀ a, u (l a) ≤ a) :
  galois_coinsertion l u :=
{ choice := λ x _, u x,
  gc := gc,
  u_l_le := h,
  choice_eq := λ _ _, rfl }

/-- Lift the top along a Galois connection -/
def galois_connection.lift_order_top {α β : Type*} [partial_order α] [preorder β] [order_top β]
  {l : α → β} {u : β → α} (gc : galois_connection l u) :
  order_top α :=
{ top    := u ⊤,
  le_top := λ b, gc.le_u $ le_top }

namespace galois_coinsertion

variables {l : α → β} {u : β → α}

lemma u_l_eq [partial_order α] [preorder β] (gi : galois_coinsertion l u) (a : α) :
  u (l a) = a :=
gi.dual.l_u_eq a

lemma u_l_left_inverse [partial_order α] [preorder β] (gi : galois_coinsertion l u) :
  left_inverse u l :=
gi.u_l_eq

lemma u_surjective [partial_order α] [preorder β] (gi : galois_coinsertion l u) :
  surjective u :=
gi.dual.l_surjective

lemma l_injective [partial_order α] [preorder β] (gi : galois_coinsertion l u) :
  injective l :=
gi.dual.u_injective

lemma u_inf_l [semilattice_inf α] [semilattice_inf β] (gi : galois_coinsertion l u) (a b : α) :
  u (l a ⊓ l b) = a ⊓ b :=
gi.dual.l_sup_u a b

lemma u_infi_l [complete_lattice α] [complete_lattice β] (gi : galois_coinsertion l u)
  {ι : Sort x} (f : ι → α) :
  u (⨅ i, l (f i)) = ⨅ i, (f i) :=
gi.dual.l_supr_u _

lemma u_Inf_l_image [complete_lattice α] [complete_lattice β] (gi : galois_coinsertion l u)
  (s : set α) : u (Inf (l '' s)) = Inf s :=
gi.dual.l_Sup_u_image _

lemma u_sup_l [semilattice_sup α] [semilattice_sup β] (gi : galois_coinsertion l u) (a b : α) :
  u (l a ⊔ l b) = a ⊔ b :=
gi.dual.l_inf_u _ _

lemma u_supr_l [complete_lattice α] [complete_lattice β] (gi : galois_coinsertion l u)
  {ι : Sort x} (f : ι → α) :
  u (⨆ i, l (f i)) = ⨆ i, (f i) :=
gi.dual.l_infi_u _

lemma u_bsupr_l [complete_lattice α] [complete_lattice β] (gi : galois_coinsertion l u)
  {ι : Sort x} {p : ι → Prop} (f : Π i (hi : p i), α) :
  u (⨆ i hi, l (f i hi)) = ⨆ i hi, f i hi :=
gi.dual.l_binfi_u _

lemma u_Sup_l_image [complete_lattice α] [complete_lattice β] (gi : galois_coinsertion l u)
  (s : set α) : u (Sup (l '' s)) = Sup s :=
gi.dual.l_Inf_u_image _

lemma u_supr_of_lu_eq_self [complete_lattice α] [complete_lattice β] (gi : galois_coinsertion l u)
  {ι : Sort x} (f : ι → β) (hf : ∀ i, l (u (f i)) = f i) :
  u (⨆ i, (f i)) = ⨆ i, u (f i) :=
gi.dual.l_infi_of_ul_eq_self _ hf

lemma u_bsupr_of_lu_eq_self [complete_lattice α] [complete_lattice β] (gi : galois_coinsertion l u)
  {ι : Sort x} {p : ι → Prop} (f : Π i (hi : p i), β) (hf : ∀ i hi, l (u (f i hi)) = f i hi) :
  u (⨆ i hi, f i hi) = ⨆ i hi, u (f i hi) :=
gi.dual.l_binfi_of_ul_eq_self _ hf

lemma l_le_l_iff [preorder α] [preorder β] (gi : galois_coinsertion l u) {a b} :
  l a ≤ l b ↔ a ≤ b :=
gi.dual.u_le_u_iff

lemma strict_mono_l [preorder α] [preorder β] (gi : galois_coinsertion l u) : strict_mono l :=
λ a b h, gi.dual.strict_mono_u h

lemma is_glb_of_l_image [preorder α] [preorder β] (gi : galois_coinsertion l u) {s : set α} {a : β}
  (hs : is_glb (l '' s) a) : is_glb s (u a) :=
gi.dual.is_lub_of_u_image hs

lemma is_lub_of_l_image [preorder α] [preorder β] (gi : galois_coinsertion l u) {s : set α} {a : β}
  (hs : is_lub (l '' s) a) : is_lub s (u a) :=
gi.dual.is_glb_of_u_image hs


section lift

variables [partial_order α]

/-- Lift the infima along a Galois coinsertion -/
@[reducible] -- See note [reducible non instances]
def lift_semilattice_inf [semilattice_inf β] (gi : galois_coinsertion l u) : semilattice_inf α :=
{ inf := λ a b, u (l a ⊓ l b),
  .. ‹partial_order α›, .. @order_dual.semilattice_inf _ gi.dual.lift_semilattice_sup }

/-- Lift the suprema along a Galois coinsertion -/
@[reducible] -- See note [reducible non instances]
def lift_semilattice_sup [semilattice_sup β] (gi : galois_coinsertion l u) : semilattice_sup α :=
{ sup := λ a b, gi.choice (l a ⊔ l b) $
    (sup_le (gi.gc.monotone_l $ gi.gc.le_u $ le_sup_left)
      (gi.gc.monotone_l $ gi.gc.le_u $ le_sup_right)),
  .. ‹partial_order α›, .. @order_dual.semilattice_sup _ gi.dual.lift_semilattice_inf }

/-- Lift the suprema and infima along a Galois coinsertion -/
@[reducible] -- See note [reducible non instances]
def lift_lattice [lattice β] (gi : galois_coinsertion l u) : lattice α :=
{ .. gi.lift_semilattice_sup, .. gi.lift_semilattice_inf }

/-- Lift the bot along a Galois coinsertion -/
@[reducible] -- See note [reducible non instances]
def lift_order_bot [preorder β] [order_bot β] (gi : galois_coinsertion l u) : order_bot α :=
{ bot    := gi.choice ⊥ $ bot_le,
  .. @order_dual.order_bot _ _ gi.dual.lift_order_top }

/-- Lift the top, bottom, suprema, and infima along a Galois coinsertion -/
@[reducible] -- See note [reducible non instances]
def lift_bounded_order [preorder β] [bounded_order β]
  (gi : galois_coinsertion l u) : bounded_order α :=
{ .. gi.lift_order_bot, .. gi.gc.lift_order_top }

/-- Lift all suprema and infima along a Galois coinsertion -/
@[reducible] -- See note [reducible non instances]
def lift_complete_lattice [complete_lattice β] (gi : galois_coinsertion l u) : complete_lattice α :=
{ Inf := λ s, u (Inf (l '' s)),
  Sup := λ s, gi.choice (Sup (l '' s)) _,
  .. @order_dual.complete_lattice _ gi.dual.lift_complete_lattice }

end lift

end galois_coinsertion

/-- If `α` is a partial order with bottom element (e.g., `ℕ`, `ℝ≥0`), then
`λ o : with_bot α, o.get_or_else ⊥` and coercion form a Galois insertion. -/
def with_bot.gi_get_or_else_bot [preorder α] [order_bot α] :
  galois_insertion (λ o : with_bot α, o.get_or_else ⊥) coe :=
{ gc := λ a b, with_bot.get_or_else_bot_le_iff,
  le_l_u := λ a, le_rfl,
  choice := λ o ho, _,
  choice_eq := λ _ _, rfl }
