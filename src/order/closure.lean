/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import data.set_like.basic
import order.preorder_hom
import order.galois_connection
import tactic.monotonicity

/-!
# Closure operators between preorders

We define (bundled) closure operators on a preorder as monotone (increasing), extensive
(inflationary) and idempotent functions.
We define closed elements for the operator as elements which are fixed by it.

Lower adjoints to a function between preorders `u : β → α` allow to generalise closure operators to
situations where the closure operator we are dealing with naturally decomposes as `u ∘ l` where `l`
is a worthy function to have on its own. Typical examples include
`l : set G → subgroup G := subgroup.closure`, `u : subgroup G → set G := coe`, where `G` is a group.
This shows there is a close connection between closure operators, lower adjoints and Galois
connections/insertions: every Galois connection induces a lower adjoint which itself induces a
closure operator by composition (see `galois_connection.lower_adjoint` and
`lower_adjoint.closure_operator`), and every closure operator on a partial order induces a Galois
insertion from the set of closed elements to the underlying type (see `closure_operator.gi`).

## Main definitions

* `closure_operator`: A closure operator is a monotone function `f : α → α` such that
  `∀ x, x ≤ f x` and `∀ x, f (f x) = f x`.
* `lower_adjoint`: A lower adjoint to `u : β → α` is a function `l : α → β` such that `l` and `u`
  form a Galois connection.

## Implementation details

Although `lower_adjoint` is technically a generalisation of `closure_operator` (by defining
`to_fun := id`), it is desirable to have both as otherwise `id`s would be carried all over the
place when using concrete closure operators such as `convex_hull`.

`lower_adjoint` really is a semibundled `structure` version of `galois_connection`.

## References

* https://en.wikipedia.org/wiki/Closure_operator#Closure_operators_on_partially_ordered_sets
-/

universe u

/-! ### Closure operator -/

variable (α : Type*)

/-- A closure operator on the preorder `α` is a monotone function which is extensive (every `x`
is less than its closure) and idempotent. -/
structure closure_operator [preorder α] extends α →ₘ α :=
(le_closure' : ∀ x, x ≤ to_fun x)
(idempotent' : ∀ x, to_fun (to_fun x) = to_fun x)

namespace closure_operator

instance [preorder α] : has_coe_to_fun (closure_operator α) (λ _, α → α) := ⟨λ c, c.to_fun⟩

/-- See Note [custom simps projection] -/
def simps.apply [preorder α] (f : closure_operator α) : α → α := f

initialize_simps_projections closure_operator (to_preorder_hom_to_fun → apply, -to_preorder_hom)

section partial_order
variable [partial_order α]

/-- The identity function as a closure operator. -/
@[simps]
def id : closure_operator α :=
{ to_preorder_hom := preorder_hom.id,
  le_closure' := λ _, le_rfl,
  idempotent' := λ _, rfl }

instance : inhabited (closure_operator α) := ⟨id α⟩

variables {α} (c : closure_operator α)

@[ext] lemma ext :
  ∀ (c₁ c₂ : closure_operator α), (c₁ : α → α) = (c₂ : α → α) → c₁ = c₂
| ⟨⟨c₁, _⟩, _, _⟩ ⟨⟨c₂, _⟩, _, _⟩ h := by { congr, exact h }

/-- Constructor for a closure operator using the weaker idempotency axiom: `f (f x) ≤ f x`. -/
@[simps]
def mk' (f : α → α) (hf₁ : monotone f) (hf₂ : ∀ x, x ≤ f x) (hf₃ : ∀ x, f (f x) ≤ f x) :
  closure_operator α :=
{ to_fun := f,
  monotone' := hf₁,
  le_closure' := hf₂,
  idempotent' := λ x, (hf₃ x).antisymm (hf₁ (hf₂ x)) }

/-- Convenience constructor for a closure operator using the weaker minimality axiom:
`x ≤ f y → f x ≤ f y`, which is sometimes easier to prove in practice. -/
@[simps]
def mk₂ (f : α → α) (hf : ∀ x, x ≤ f x) (hmin : ∀ ⦃x y⦄, x ≤ f y → f x ≤ f y) :
  closure_operator α :=
{ to_fun := f,
  monotone' := λ x y hxy, hmin (hxy.trans (hf y)),
  le_closure' := hf,
  idempotent' := λ x, (hmin le_rfl).antisymm (hf _) }

/-- Expanded out version of `mk₂`. `p` implies being closed. This constructor should be used when
you already know a sufficient condition for being closed and using `mem_mk₃_closed` will avoid you
the (slight) hassle of having to prove it both inside and outside the constructor. -/
@[simps]
def mk₃ (f : α → α) (p : α → Prop) (hf : ∀ x, x ≤ f x) (hfp : ∀ x, p (f x))
  (hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y) :
  closure_operator α :=
mk₂ f hf (λ x y hxy, hmin hxy (hfp y))

/-- This lemma shows that the image of `x` of a closure operator built from the `mk₃` constructor
respects `p`, the property that was fed into it. -/
lemma closure_mem_mk₃ {f : α → α} {p : α → Prop} {hf : ∀ x, x ≤ f x} {hfp : ∀ x, p (f x)}
  {hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y} (x : α) :
  p (mk₃ f p hf hfp hmin x) :=
hfp x

/-- Analogue of `closure_le_closed_iff_le` but with the `p` that was fed into the `mk₃` constructor.
-/
lemma closure_le_mk₃_iff {f : α → α} {p : α → Prop} {hf : ∀ x, x ≤ f x} {hfp : ∀ x, p (f x)}
  {hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y} {x y : α} (hxy : x ≤ y) (hy : p y) :
  mk₃ f p hf hfp hmin x ≤ y :=
hmin hxy hy

@[mono] lemma monotone : monotone c := c.monotone'

/-- Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationarity. -/
lemma le_closure (x : α) : x ≤ c x := c.le_closure' x

@[simp] lemma idempotent (x : α) : c (c x) = c x := c.idempotent' x

lemma le_closure_iff (x y : α) : x ≤ c y ↔ c x ≤ c y :=
⟨λ h, c.idempotent y ▸ c.monotone h, λ h, (c.le_closure x).trans h⟩

/-- An element `x` is closed for the closure operator `c` if it is a fixed point for it. -/
def closed : set α := λ x, c x = x

lemma mem_closed_iff (x : α) : x ∈ c.closed ↔ c x = x := iff.rfl

lemma mem_closed_iff_closure_le (x : α) : x ∈ c.closed ↔ c x ≤ x :=
⟨le_of_eq, λ h, h.antisymm (c.le_closure x)⟩

lemma closure_eq_self_of_mem_closed {x : α} (h : x ∈ c.closed) : c x = x := h

@[simp] lemma closure_is_closed (x : α) : c x ∈ c.closed := c.idempotent x

/-- The set of closed elements for `c` is exactly its range. -/
lemma closed_eq_range_close : c.closed = set.range c :=
set.ext $ λ x, ⟨λ h, ⟨x, h⟩, by { rintro ⟨y, rfl⟩, apply c.idempotent }⟩

/-- Send an `x` to an element of the set of closed elements (by taking the closure). -/
def to_closed (x : α) : c.closed := ⟨c x, c.closure_is_closed x⟩

@[simp] lemma closure_le_closed_iff_le (x : α) {y : α} (hy : c.closed y) : c x ≤ y ↔ x ≤ y :=
by rw [←c.closure_eq_self_of_mem_closed hy, ←le_closure_iff]

/-- A closure operator is equal to the closure operator obtained by feeding `c.closed` into the
`mk₃` constructor. -/
lemma eq_mk₃_closed (c : closure_operator α) :
  c = mk₃ c c.closed c.le_closure c.closure_is_closed
  (λ x y hxy hy, (c.closure_le_closed_iff_le x hy).2 hxy) :=
by { ext, refl }

/-- The property `p` fed into the `mk₃` constructor implies being closed. -/
lemma mem_mk₃_closed {f : α → α} {p : α → Prop} {hf : ∀ x, x ≤ f x} {hfp : ∀ x, p (f x)}
  {hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y} {x : α} (hx : p x) :
  x ∈ (mk₃ f p hf hfp hmin).closed :=
(hmin (le_refl _) hx).antisymm (hf _)

end partial_order

variable {α}

section order_top
variables [order_top α] (c : closure_operator α)

@[simp] lemma closure_top : c ⊤ = ⊤ :=
le_top.antisymm (c.le_closure _)

lemma top_mem_closed : ⊤ ∈ c.closed :=
c.closure_top

end order_top

lemma closure_inf_le [semilattice_inf α] (c : closure_operator α) (x y : α) :
  c (x ⊓ y) ≤ c x ⊓ c y :=
c.monotone.map_inf_le _ _

section semilattice_sup
variables [semilattice_sup α] (c : closure_operator α)

lemma closure_sup_closure_le (x y : α) :
  c x ⊔ c y ≤ c (x ⊔ y) :=
c.monotone.le_map_sup _ _

lemma closure_sup_closure_left (x y : α) :
  c (c x ⊔ y) = c (x ⊔ y) :=
((c.le_closure_iff _ _).1 (sup_le (c.monotone le_sup_left) (le_sup_right.trans
  (c.le_closure _)))).antisymm (c.monotone (sup_le_sup_right (c.le_closure _) _))

lemma closure_sup_closure_right (x y : α) :
  c (x ⊔ c y) = c (x ⊔ y) :=
by rw [sup_comm, closure_sup_closure_left, sup_comm]

lemma closure_sup_closure (x y : α) :
  c (c x ⊔ c y) = c (x ⊔ y) :=
by rw [closure_sup_closure_left, closure_sup_closure_right]

end semilattice_sup

section complete_lattice
variables [complete_lattice α] (c : closure_operator α)

lemma closure_supr_closure {ι : Type u} (x : ι → α) :
  c (⨆ i, c (x i)) = c (⨆ i, x i) :=
le_antisymm ((c.le_closure_iff _ _).1 (supr_le (λ i, c.monotone
  (le_supr x i)))) (c.monotone (supr_le_supr (λ i, c.le_closure _)))

lemma closure_bsupr_closure (p : α → Prop) :
  c (⨆ x (H : p x), c x) = c (⨆ x (H : p x), x) :=
le_antisymm ((c.le_closure_iff _ _).1 (bsupr_le (λ x hx, c.monotone
  (le_bsupr_of_le x hx (le_refl x))))) (c.monotone (bsupr_le_bsupr (λ x hx, c.le_closure x)))

end complete_lattice
end closure_operator

/-! ### Lower adjoint -/

variables {α} {β : Type*}

/-- A lower adjoint of `u` on the preorder `α` is a function `l` such that `l` and `u` form a Galois
connection. It allows us to define closure operators whose output does not match the input. In
practice, `u` is often `coe : β → α`. -/
structure lower_adjoint [preorder α] [preorder β] (u : β → α) :=
(to_fun : α → β)
(gc' : galois_connection to_fun u)

namespace lower_adjoint

variable (α)

/-- The identity function as a lower adjoint to itself. -/
@[simps]
protected def id [preorder α] : lower_adjoint (id : α → α) :=
{ to_fun := λ x, x,
  gc' := galois_connection.id }

variable {α}

instance [preorder α] : inhabited (lower_adjoint (id : α → α)) := ⟨lower_adjoint.id α⟩

section preorder
variables [preorder α] [preorder β] {u : β → α} (l : lower_adjoint u)

instance : has_coe_to_fun (lower_adjoint u) (λ _, α → β) := { coe := to_fun }

/-- See Note [custom simps projection] -/
def simps.apply : α → β := l

lemma gc : galois_connection l u := l.gc'

@[ext] lemma ext :
  ∀ (l₁ l₂ : lower_adjoint u), (l₁ : α → β) = (l₂ : α → β) → l₁ = l₂
| ⟨l₁, _⟩ ⟨l₂, _⟩ h := by { congr, exact h }

@[mono] lemma monotone : monotone (u ∘ l) := l.gc.monotone_u.comp l.gc.monotone_l

/-- Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationarity. -/
lemma le_closure (x : α) : x ≤ u (l x) := l.gc.le_u_l _

end preorder

section partial_order
variables [partial_order α] [preorder β] {u : β → α} (l : lower_adjoint u)

/-- Every lower adjoint induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad. -/
@[simps]
def closure_operator :
  closure_operator α :=
{ to_fun := λ x, u (l x),
  monotone' := l.monotone,
  le_closure' := l.le_closure,
  idempotent' := λ x, show (u ∘ l ∘ u) (l x) = u (l x), by rw l.gc.u_l_u_eq_u }

lemma idempotent (x : α) : u (l (u (l x))) = u (l x) :=
l.closure_operator.idempotent _

lemma le_closure_iff (x y : α) : x ≤ u (l y) ↔ u (l x) ≤ u (l y) :=
l.closure_operator.le_closure_iff _ _

end partial_order

section preorder
variables [preorder α] [preorder β] {u : β → α} (l : lower_adjoint u)

/-- An element `x` is closed for `l : lower_adjoint u` if it is a fixed point: `u (l x) = x` -/
def closed : set α := λ x, u (l x) = x

lemma mem_closed_iff (x : α) : x ∈ l.closed ↔ u (l x) = x := iff.rfl

lemma closure_eq_self_of_mem_closed {x : α} (h : x ∈ l.closed) : u (l x) = x := h

end preorder

section partial_order
variables [partial_order α] [partial_order β] {u : β → α} (l : lower_adjoint u)

lemma mem_closed_iff_closure_le (x : α) : x ∈ l.closed ↔ u (l x) ≤ x :=
l.closure_operator.mem_closed_iff_closure_le _

@[simp] lemma closure_is_closed (x : α) : u (l x) ∈ l.closed := l.idempotent x

/-- The set of closed elements for `l` is the range of `u ∘ l`. -/
lemma closed_eq_range_close : l.closed = set.range (u ∘ l) :=
l.closure_operator.closed_eq_range_close

/-- Send an `x` to an element of the set of closed elements (by taking the closure). -/
def to_closed (x : α) : l.closed := ⟨u (l x), l.closure_is_closed x⟩

@[simp] lemma closure_le_closed_iff_le (x : α) {y : α} (hy : l.closed y) : u (l x) ≤ y ↔ x ≤ y :=
l.closure_operator.closure_le_closed_iff_le x hy

end partial_order

lemma closure_top [order_top α] [preorder β] {u : β → α} (l : lower_adjoint u) :
  u (l ⊤) = ⊤ :=
l.closure_operator.closure_top

lemma closure_inf_le [semilattice_inf α] [preorder β] {u : β → α} (l : lower_adjoint u) (x y : α) :
  u (l (x ⊓ y)) ≤ u (l x) ⊓ u (l y) :=
l.closure_operator.closure_inf_le x y

section semilattice_sup
variables [semilattice_sup α] [preorder β] {u : β → α} (l : lower_adjoint u)

lemma closure_sup_closure_le (x y : α) :
  u (l x) ⊔ u (l y) ≤ u (l (x ⊔ y)) :=
l.closure_operator.closure_sup_closure_le x y

lemma closure_sup_closure_left (x y : α) :
  u (l (u (l x) ⊔ y)) = u (l (x ⊔ y)) :=
l.closure_operator.closure_sup_closure_left x y

lemma closure_sup_closure_right (x y : α) :
  u (l (x ⊔ u (l y))) = u (l (x ⊔ y)) :=
l.closure_operator.closure_sup_closure_right x y

lemma closure_sup_closure (x y : α) :
  u (l (u (l x) ⊔ u (l y))) = u (l (x ⊔ y)) :=
l.closure_operator.closure_sup_closure x y

end semilattice_sup

section complete_lattice
variables [complete_lattice α] [preorder β] {u : β → α} (l : lower_adjoint u)

lemma closure_supr_closure {ι : Type u} (x : ι → α) :
  u (l (⨆ i, u (l (x i)))) = u (l (⨆ i, x i)) :=
l.closure_operator.closure_supr_closure x

lemma closure_bsupr_closure (p : α → Prop) :
  u (l (⨆ x (H : p x), u (l x))) = u (l (⨆ x (H : p x), x)) :=
l.closure_operator.closure_bsupr_closure p

end complete_lattice

/- Lemmas for `lower_adjoint (coe : α → set β)`, where `set_like α β` -/
section coe_to_set
variables [set_like α β] (l : lower_adjoint (coe : α → set β))

lemma subset_closure (s : set β) : s ⊆ l s :=
l.le_closure s

lemma not_mem_of_not_mem_closure {s : set β} {P : β} (hP : P ∉ l s) : P ∉ s :=
λ h, hP (subset_closure _ s h)

lemma le_iff_subset (s : set β) (S : α) : l s ≤ S ↔ s ⊆ S :=
l.gc s S

lemma mem_iff (s : set β) (x : β) : x ∈ l s ↔ ∀ S : α, s ⊆ S → x ∈ S :=
by { simp_rw [←set_like.mem_coe, ←set.singleton_subset_iff, ←l.le_iff_subset],
  exact ⟨λ h S, h.trans, λ h, h _ le_rfl⟩ }

lemma eq_of_le {s : set β} {S : α} (h₁ : s ⊆ S) (h₂ : S ≤ l s) : l s = S :=
((l.le_iff_subset _ _).2 h₁).antisymm h₂

lemma closure_union_closure_subset (x y : α) :
  (l x : set β) ∪ (l y) ⊆ l (x ∪ y) :=
l.closure_sup_closure_le x y

@[simp] lemma closure_union_closure_left (x y : α) :
  (l ((l x) ∪ y) : set β) = l (x ∪ y) :=
l.closure_sup_closure_left x y

@[simp] lemma closure_union_closure_right (x y : α) :
  l (x ∪ (l y)) = l (x ∪ y) :=
set_like.coe_injective (l.closure_sup_closure_right x y)

@[simp] lemma closure_union_closure (x y : α) :
  l ((l x) ∪ (l y)) = l (x ∪ y) :=
set_like.coe_injective (l.closure_operator.closure_sup_closure x y)

@[simp] lemma closure_Union_closure {ι : Type u} (x : ι → α) :
  l (⋃ i, l (x i)) = l (⋃ i, x i) :=
set_like.coe_injective (l.closure_supr_closure (coe ∘ x))

@[simp] lemma closure_bUnion_closure (p : set β → Prop) :
  l (⋃ x (H : p x), l x) = l (⋃ x (H : p x), x) :=
set_like.coe_injective (l.closure_bsupr_closure p)

end coe_to_set

end lower_adjoint

/-! ### Translations between `galois_connection`, `lower_adjoint`, `closure_operator` -/

variable {α}

/-- Every Galois connection induces a lower adjoint. -/
@[simps]
def galois_connection.lower_adjoint [preorder α] [preorder β] {l : α → β} {u : β → α}
  (gc : galois_connection l u) :
  lower_adjoint u :=
{ to_fun := l,
  gc' := gc }

/-- Every Galois connection induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad. -/
@[simps]
def galois_connection.closure_operator [partial_order α] [preorder β] {l : α → β} {u : β → α}
  (gc : galois_connection l u) :
  closure_operator α :=
gc.lower_adjoint.closure_operator

/-- The set of closed elements has a Galois insertion to the underlying type. -/
def closure_operator.gi [partial_order α] (c : closure_operator α) :
  galois_insertion c.to_closed coe :=
{ choice := λ x hx, ⟨x, hx.antisymm (c.le_closure x)⟩,
  gc := λ x y, (c.closure_le_closed_iff_le _ y.2),
  le_l_u := λ x, c.le_closure _,
  choice_eq := λ x hx, le_antisymm (c.le_closure x) hx }

/-- The Galois insertion associated to a closure operator can be used to reconstruct the closure
operator.
Note that the inverse in the opposite direction does not hold in general. -/
@[simp]
lemma closure_operator_gi_self [partial_order α] (c : closure_operator α) :
  c.gi.gc.closure_operator = c :=
by { ext x, refl }
