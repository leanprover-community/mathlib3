/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
import order.basic
import order.preorder_hom
import order.galois_connection
import tactic.monotonicity

/-!
# Closure operators on a partial order

We define (bundled) closure operators on a partial order as an monotone (increasing), extensive
(inflationary) and idempotent function.
We define closed elements for the operator as elements which are fixed by it.

Note that there is close connection to Galois connections and Galois insertions: every closure
operator induces a Galois insertion (from the set of closed elements to the underlying type), and
every Galois connection induces a closure operator (namely the composition). In particular,
a Galois insertion can be seen as a general case of a closure operator, where the inclusion is given
by coercion, see `closure_operator.gi`.

## References

* https://en.wikipedia.org/wiki/Closure_operator#Closure_operators_on_partially_ordered_sets

-/
universes u v

/-! ### Lower adjoint -/

/-
import order.closure
import group_theory.subgroup
import analysis.convex.basic


variables {α β : Type*} [preorder α] [preorder β] {l : α → β} {u : β → α} (l : lower_adjoint u)

@[simps] def subgroup.closure' {G : Type*} [group G] :
  lower_adjoint (coe : subgroup G → set G) :=
{ to_fun := λ k, Inf {K | k ⊆ K},
  gc' := λ k K,
    ⟨set.subset.trans $ λ x hx, subgroup.mem_Inf.2 $ λ K hK, hK hx, λ h, Inf_le h⟩ }

def convex_hull' {E : Type*} [add_comm_group E] [module ℝ E] :
  lower_adjoint (id : set E → set E) :=
{ to_fun := λ s, ⋂ (t : set E) (hst : s ⊆ t) (ht : convex t), t,
  gc' := λ s t,
  begin

  end }

lemma subset_closure' (G : Type*) [group G] (s : set G) :
  s ⊆ subgroup.closure' s :=
subgroup.closure'.le_closure _

-- Lemmas for `lower_adjoint (coe : α → set β)`, where `set_like α β`
section coe_to_set

namespace lower_adjoint

variables [set_like α β]
variables (closure : lower_adjoint (coe : α → set β))
variables {s : set β} {S : α}

lemma subset : s ⊆ (closure s : α) :=
closure.gc.le_u (le_refl _)

lemma le_iff : closure s ≤ S ↔ s ⊆ S :=
closure.gc _ _

lemma mem_iff {x : β} : x ∈ (closure s : α) ↔ ∀ S : α, s ⊆ S → x ∈ S :=
by { simp_rw [← set_like.mem_coe, ← set.singleton_subset_iff, ← closure.le_iff],
     exact ⟨λ h S, le_trans h, λ h, h _ (le_refl _)⟩ }

lemma eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
begin
  apply l.mem_closed_iff_closure_le.2,
end

end lower_adjoint

end coe_to_set-/

structure lower_adjoint {α β : Type*} [preorder α] [preorder β] (u : β → α) :=
(to_fun : α → β)
(gc' : galois_connection to_fun u)

namespace lower_adjoint

variables {α β : Type*} {u : β → α}

section preorder

variables [preorder α] [preorder β] (l : lower_adjoint u)

instance : has_coe_to_fun (lower_adjoint u) :=
{ F := λ _, α → β, coe := to_fun }

initialize_simps_projections lower_adjoint (to_fun → apply)

def gc : galois_connection l u := l.gc'

@[ext] lemma ext :
  ∀ (l₁ l₂ : lower_adjoint u), (l₁ : α → β) = (l₂ : α → β) → l₁ = l₂
| ⟨l₁, _⟩ ⟨l₂, _⟩ h := by { congr, exact h }

@[mono] lemma mono : monotone (u ∘ l) := l.gc.monotone_u.comp l.gc.monotone_l

@[mono] lemma monotone : monotone l := l.gc.monotone_l

/-- Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationarity. -/
lemma le_closure (x : α) : x ≤ u (l x) := l.gc.le_u_l _

end preorder

section partial_order

variables [partial_order α] [preorder β] (l : lower_adjoint u)

lemma closure_eq_of_le_closure {x : α}
  (h : u (l x) ≤ x) : u (l x) = x :=
h.antisymm (l.le_closure x)

@[simp] lemma idempotent (x : α) : u (l (u (l x))) = u (l x) :=
begin
  change u ((l ∘ u ∘ l) x) = u (l x),
  rw l.gc.l_u_l_eq_l,
end

lemma le_closure_iff (x y : α) : x ≤ u (l y) ↔ u (l x) ≤ u (l y) :=
⟨λ h, l.idempotent y ▸ l.mono h, λ h, (l.le_closure x).trans h⟩

end partial_order

@[simp] lemma closure_top [order_top α] [preorder β] (l : lower_adjoint u) :
  u (l ⊤) = ⊤ :=
le_top.antisymm (l.le_closure _)

lemma closure_inf_le [semilattice_inf α] [preorder β] (l : lower_adjoint u) (x y : α) :
  u (l (x ⊓ y)) ≤ u (l x) ⊓ u (l y) :=
l.mono.map_inf_le _ _

lemma closure_sup_closure_le [semilattice_sup α] [preorder β] (l : lower_adjoint u) (x y : α) :
  u (l x) ⊔ u (l y) ≤ u (l (x ⊔ y)) :=
l.mono.le_map_sup _ _

section preorder

variables [preorder α] [preorder β] (l : lower_adjoint u)

/-- An element `x` is closed for the closure operator `c` if it is a fixed point for it. -/
def closed : set α := λ x, u (l x) = x

lemma mem_closed_iff (x : α) : x ∈ l.closed ↔ u (l x) = x := iff.rfl

lemma closure_eq_self_of_mem_closed {x : α} (h : x ∈ l.closed) : u (l x) = x := h

end preorder

section partial_order

variables [partial_order α] [partial_order β] (l : lower_adjoint u)

lemma mem_closed_iff_closure_le (x : α) : x ∈ l.closed ↔ u (l x) ≤ x :=
⟨le_of_eq, λ h, h.antisymm (l.le_closure x)⟩

@[simp] lemma closure_is_closed (x : α) : u (l x) ∈ l.closed := l.idempotent x

/-- The set of closed elements for `c` is exactly its range. -/
lemma closed_eq_range_close : l.closed = set.range (u ∘ l) :=
set.ext $ λ x, ⟨λ h, ⟨x, h⟩, by { rintro ⟨y, rfl⟩, exact l.closure_is_closed y }⟩

/-- Send an `x` to an element of the set of closed elements (by taking the closure). -/
def to_closed (x : α) : l.closed := ⟨u (l x), l.closure_is_closed x⟩

@[simp] lemma closure_le_closed_iff_le (x : α) {y : α} (hy : l.closed y) : u (l x) ≤ y ↔ x ≤ y :=
by rw [←l.closure_eq_self_of_mem_closed hy, ←le_closure_iff]

end partial_order

@[simp] lemma closure_sup_closure_left [semilattice_sup α] [partial_order β]
  (l : lower_adjoint u)
  (x y : α) :
  u (l (u (l x) ⊔ y))  = u (l (x ⊔ y)) :=
le_antisymm ((l.le_closure_iff _ _).1 (sup_le (l.mono le_sup_left)
  (le_sup_right.trans (l.le_closure _)))) (l.mono (sup_le_sup_right (l.le_closure _) _))

@[simp] lemma closure_sup_closure_right [semilattice_sup α] [partial_order β] (l : lower_adjoint u)
  (x y : α) :
  u (l (x ⊔ u (l y))) = u (l (x ⊔ y)) :=
by rw [sup_comm, closure_sup_closure_left, sup_comm]

@[simp] lemma closure_sup_closure {α : Type u} [semilattice_sup α] (l : lower_adjoint u)
  (x y : α) :
  c (c x ⊔ c y) = c (x ⊔ y) :=
by rw [closure_sup_closure_left, closure_sup_closure_right]

@[simp] lemma closure_supr_closure {α : Type u} {ι : Type v} [complete_lattice α]
  (l : lower_adjoint u) (x : ι → α) :
  c (⨆ i, c (x i)) = c (⨆ i, x i) :=
le_antisymm ((le_closure_iff c _ _).1 (supr_le (λ i, c.monotone
  (le_supr _ _)))) (c.monotone (supr_le_supr (λ i, c.le_closure _)))

@[simp] lemma closure_bsupr_closure {α : Type u} [complete_lattice α] (l : lower_adjoint u)
  (p : α → Prop) :
  c (⨆ x (H : p x), c x) = c (⨆ x (H : p x), x) :=
le_antisymm ((le_closure_iff c _ _).1 (bsupr_le (λ x hx, c.monotone
  (le_bsupr_of_le x hx (le_refl x))))) (c.monotone (bsupr_le_bsupr (λ x hx, le_closure _ _)))

/-- The set of closed elements has a Galois insertion to the underlying type. -/
def gi : galois_insertion c.to_closed coe :=
{ choice := λ x hx, ⟨x, le_antisymm hx (c.le_closure x)⟩,
  gc := λ x y, (c.closure_le_closed_iff_le _ y.2),
  le_l_u := λ x, c.le_closure _,
  choice_eq := λ x hx, le_antisymm (c.le_closure x) hx }

end closure_operator

variables {α} (l : lower_adjoint u)

/--
Every Galois connection induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad.
-/
@[simps]
def galois_connection.closure_operator {β : Type u} [preorder β]
  {l : α → β} {u : β → α} (gc : galois_connection l u) :
  lower_adjoint u :=
{ to_fun := λ x, u (l x),
  monotone' := λ x y h, gc.monotone_u (gc.monotone_l h),
  le_closure' := gc.le_u_l,
  idempotent' := λ x, le_antisymm (gc.monotone_u (gc.l_u_le _)) (gc.le_u_l _) }

def lower_adjoint.closure_operator {β : Type u} [preorder β] {l : β → α} (la : lower_adjoint u) :
  lower_adjoint u :=
la.gc.closure_operator

/--
The Galois insertion associated to a closure operator can be used to reconstruct the closure
operator.

Note that the inverse in the opposite direction does not hold in general.
-/
@[simp]
lemma closure_operator_gi_self : c.gi.gc.closure_operator = c :=
by { ext x, refl }

end lower_adjoint

/-! ### Closure operator -/

variables (α : Type u) [partial_order α]

/--
A closure operator on the partial order `α` is a monotone function which is extensive (every `x`
is less than its closure) and idempotent.
-/
structure closure_operator extends α →ₘ α :=
(le_closure' : ∀ x, x ≤ to_fun x)
(idempotent' : ∀ x, to_fun (to_fun x) = to_fun x)

instance : has_coe_to_fun (closure_operator α) :=
{ F := _, coe := λ c, c.to_fun }

/-- See Note [custom simps projection] -/
def closure_operator.simps.apply (f : closure_operator α) : α → α := f

initialize_simps_projections closure_operator (to_preorder_hom_to_fun → apply, -to_preorder_hom)

namespace closure_operator

/-- The identity function as a closure operator. -/
@[simps]
def id : closure_operator α :=
{ to_fun := λ x, x,
  monotone' := λ _ _ h, h,
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
  idempotent' := λ x, le_antisymm (hf₃ x) (hf₁ (hf₂ x)) }

/-- Convenience constructor for a closure operator using the weaker minimality axiom:
`x ≤ f y → f x ≤ f y`, which is sometimes easier to prove in practice. -/
@[simps]
def mk₂ (f : α → α) (hf : ∀ x, x ≤ f x) (hmin : ∀ ⦃x y⦄, x ≤ f y → f x ≤ f y) :
  closure_operator α :=
{ to_fun := f,
  monotone' := λ x y hxy, hmin (le_trans hxy (hf y)),
  le_closure' := hf,
  idempotent' := λ x, le_antisymm (hmin (le_refl _)) (hf _) }

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
/--
Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationarity.
-/
lemma le_closure (x : α) : x ≤ c x := c.le_closure' x
@[simp] lemma idempotent (x : α) : c (c x) = c x := c.idempotent' x

lemma le_closure_iff (x y : α) : x ≤ c y ↔ c x ≤ c y :=
⟨λ h, c.idempotent y ▸ c.monotone h, λ h, le_trans (c.le_closure x) h⟩

@[simp] lemma closure_top {α : Type u} [order_top α] (c : closure_operator α) : c ⊤ = ⊤ :=
le_antisymm le_top (c.le_closure _)

lemma closure_inf_le {α : Type u} [semilattice_inf α] (c : closure_operator α) (x y : α) :
  c (x ⊓ y) ≤ c x ⊓ c y :=
c.monotone.map_inf_le _ _

lemma closure_sup_closure_le {α : Type u} [semilattice_sup α] (c : closure_operator α) (x y : α) :
  c x ⊔ c y ≤ c (x ⊔ y) :=
c.monotone.le_map_sup _ _

/-- An element `x` is closed for the closure operator `c` if it is a fixed point for it. -/
def closed : set α := λ x, c x = x

lemma mem_closed_iff (x : α) : x ∈ c.closed ↔ c x = x := iff.rfl
lemma mem_closed_iff_closure_le (x : α) : x ∈ c.closed ↔ c x ≤ x :=
⟨le_of_eq, λ h, le_antisymm h (c.le_closure x)⟩
lemma closure_eq_self_of_mem_closed {x : α} (h : x ∈ c.closed) : c x = x := h

@[simp] lemma closure_is_closed (x : α) : c x ∈ c.closed := c.idempotent x

/-- The set of closed elements for `c` is exactly its range. -/
lemma closed_eq_range_close : c.closed = set.range c :=
set.ext $ λ x, ⟨λ h, ⟨x, h⟩, by { rintro ⟨y, rfl⟩, apply c.idempotent }⟩

/-- Send an `x` to an element of the set of closed elements (by taking the closure). -/
def to_closed (x : α) : c.closed := ⟨c x, c.closure_is_closed x⟩

lemma top_mem_closed {α : Type u} [order_top α] (c : closure_operator α) : ⊤ ∈ c.closed :=
c.closure_top

@[simp] lemma closure_le_closed_iff_le (x : α) {y : α} (hy : c.closed y) : c x ≤ y ↔ x ≤ y :=
by rw [←c.closure_eq_self_of_mem_closed hy, ←le_closure_iff]

/-- A closure operator is equal to the closure operator obtained by feeding `c.closed` into the
`mk₃` constructor. -/
lemma eq_mk₃_closed (c : closure_operator α) :
  c = mk₃ c c.closed c.le_closure c.closure_is_closed
  (λ x y hxy hy, (c.closure_le_closed_iff_le x hy).2 hxy) :=
by { ext, refl }

/-- This lemma shows that the `p` fed into the `mk₃` constructor implies being closed. -/
lemma mem_mk₃_closed {f : α → α} {p : α → Prop} {hf : ∀ x, x ≤ f x} {hfp : ∀ x, p (f x)}
  {hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y} {x : α} (hx : p x) :
  x ∈ (mk₃ f p hf hfp hmin).closed :=
le_antisymm (hmin (le_refl _) hx) (hf _)

@[simp] lemma closure_sup_closure_left {α : Type u} [semilattice_sup α] (c : closure_operator α)
  (x y : α) :
  c (c x ⊔ y) = c (x ⊔ y) :=
le_antisymm ((le_closure_iff c _ _).1 (sup_le (c.monotone le_sup_left)
  (le_trans le_sup_right (le_closure _ _)))) (c.monotone (sup_le_sup_right (le_closure _ _) _))

@[simp] lemma closure_sup_closure_right {α : Type u} [semilattice_sup α] (c : closure_operator α)
  (x y : α) :
  c (x ⊔ c y) = c (x ⊔ y) :=
by rw [sup_comm, closure_sup_closure_left, sup_comm]

@[simp] lemma closure_sup_closure {α : Type u} [semilattice_sup α] (c : closure_operator α)
  (x y : α) :
  c (c x ⊔ c y) = c (x ⊔ y) :=
by rw [closure_sup_closure_left, closure_sup_closure_right]

@[simp] lemma closure_supr_closure {α : Type u} {ι : Type v} [complete_lattice α]
  (c : closure_operator α) (x : ι → α) :
  c (⨆ i, c (x i)) = c (⨆ i, x i) :=
le_antisymm ((le_closure_iff c _ _).1 (supr_le (λ i, c.monotone
  (le_supr _ _)))) (c.monotone (supr_le_supr (λ i, c.le_closure _)))

@[simp] lemma closure_bsupr_closure {α : Type u} [complete_lattice α] (c : closure_operator α)
  (p : α → Prop) :
  c (⨆ x (H : p x), c x) = c (⨆ x (H : p x), x) :=
le_antisymm ((le_closure_iff c _ _).1 (bsupr_le (λ x hx, c.monotone
  (le_bsupr_of_le x hx (le_refl x))))) (c.monotone (bsupr_le_bsupr (λ x hx, le_closure _ _)))

/-- The set of closed elements has a Galois insertion to the underlying type. -/
def gi : galois_insertion c.to_closed coe :=
{ choice := λ x hx, ⟨x, le_antisymm hx (c.le_closure x)⟩,
  gc := λ x y, (c.closure_le_closed_iff_le _ y.2),
  le_l_u := λ x, c.le_closure _,
  choice_eq := λ x hx, le_antisymm (c.le_closure x) hx }

end closure_operator

variables {α} (c : closure_operator α)

/--
Every Galois connection induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad.
-/
@[simps]
def galois_connection.closure_operator {β : Type u} [preorder β]
  {l : α → β} {u : β → α} (gc : galois_connection l u) :
  closure_operator α :=
{ to_fun := λ x, u (l x),
  monotone' := λ x y h, gc.monotone_u (gc.monotone_l h),
  le_closure' := gc.le_u_l,
  idempotent' := λ x, le_antisymm (gc.monotone_u (gc.l_u_le _)) (gc.le_u_l _) }

def lower_adjoint.closure_operator {β : Type u} [preorder β] {l : β → α} (la : lower_adjoint u) :
  closure_operator α :=
la.gc.closure_operator

/--
The Galois insertion associated to a closure operator can be used to reconstruct the closure
operator.

Note that the inverse in the opposite direction does not hold in general.
-/
@[simp]
lemma closure_operator_gi_self : c.gi.gc.closure_operator = c :=
by { ext x, refl }
