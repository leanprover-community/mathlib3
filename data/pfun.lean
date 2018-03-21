/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.set data.set.basic

universes u v w

/-- `roption α` is the type of "partial values" of type `α`. It
  is similar to `option α` except the domain condition can be an
  arbitrary proposition, not necessarily decidable. -/
structure roption (α : Type u) : Type u :=
(dom : Prop)
(get : dom → α)

namespace roption
variables {α : Type u} {β : Type v}

/-- Convert an `roption α` with a decidable domain to an option -/
def to_option (o : roption α) [decidable o.dom] : option α :=
if h : dom o then some (o.get h) else none

/-- `roption` extensionality -/
protected def ext : Π {o p : roption α}
  (H1 : o.dom ↔ p.dom)
  (H2 : ∀h1 h2, o.get h1 = p.get h2), o = p
| ⟨od, o⟩ ⟨pd, p⟩ H1 H2 := have t : od = pd, from propext H1,
  by cases t; rw [show o = p, from funext $ λp, H2 p p]

/-- The `none` value in `roption` has a `false` domain and an empty function. -/
protected def none : roption α := ⟨false, false.rec _⟩

/-- The `some a` value in `roption` has a `true` domain and the
  function returns `a`. -/
protected def some (a : α) : roption α := ⟨true, λ_, a⟩

instance none_decidable : decidable (@roption.none α).dom := decidable.false
instance some_decidable (a : α) : decidable (roption.some a).dom := decidable.true

/-- Convert an `option α` into an `roption α` -/
def of_option : option α → roption α
| none := roption.none
| (some a) := roption.some a

instance : has_coe (option α) (roption α) := ⟨of_option⟩

instance of_option_decidable : ∀ o : option α, decidable (of_option o).dom
| none := roption.none_decidable
| (some a) := roption.some_decidable a

theorem to_of_option (o : option α) : to_option (of_option o) = o :=
by cases o; refl

theorem of_to_option (o : roption α) [decidable o.dom] : of_option (to_option o) = o :=
begin
  unfold to_option,
  by_cases o.dom; {
    simp [h, dif_pos, dif_neg, of_option],
    apply roption.ext,
    simp [roption.some, roption.none, h],
    intros h1 h2,
    simp [roption.some, roption.none, h];
    contradiction }
end

/-- `a ∈ o` means that `o` is defined and equal to `a` -/
protected def mem (a : α) (o : roption α) : Prop := ∃ h, o.get h = a

instance : has_mem α (roption α) := ⟨roption.mem⟩

theorem dom_iff_mem : ∀ (o : roption α), o.dom ↔ ∃y, y ∈ o
| ⟨p, f⟩ := ⟨λh, ⟨f h, h, rfl⟩, λ⟨._, h, rfl⟩, h⟩

/-- `assert p f` is a bind-like operation which appends an additional condition
  `p` to the domain and uses `f` to produce the value. -/
def assert (p : Prop) (f : p → roption α) : roption α :=
⟨∃h : p, (f h).dom, λha, (f (let ⟨h, _⟩ := ha in h)).get (let ⟨_, h⟩ := ha in h)⟩

/-- The bind operation has value `g (f.get)`, and is defined when all the
  parts are defined. -/
protected def bind (f : roption α) (g : α → roption β) : roption β :=
assert (dom f) (λb, g (f.get b))

/-- The map operation for `roption` just maps the value and maintains the same domain. -/
protected def map (f : α → β) (o : roption α) : roption β :=
⟨o.dom, f ∘ o.get⟩

theorem bind_some_eq_map (f : α → β) (x) :
  roption.bind x (roption.some ∘ f) = roption.map f x :=
roption.ext ⟨λ⟨h, _⟩, h, λh, ⟨h, trivial⟩⟩ (λ_ _, rfl)

theorem some_bind (x : α) (f : α → roption β) :
  roption.bind (roption.some x) f = f x :=
roption.ext ⟨λ⟨_, h⟩, h, λh, ⟨trivial, h⟩⟩ (λ_ _, rfl)

theorem bind_assoc {γ} (f : roption α) (g : α → roption β) (k : β → roption γ) :
  roption.bind (roption.bind f g) k = roption.bind f (λ x, roption.bind (g x) k) :=
roption.ext (⟨λ⟨⟨h1, h2⟩, h3⟩, ⟨h1, h2, h3⟩, λ⟨h1, h2, h3⟩, ⟨⟨h1, h2⟩, h3⟩⟩) (λ_ _, rfl)

instance : monad roption :=
{ pure := @roption.some,
  map := @roption.map,
  bind := @roption.bind }

instance : is_lawful_monad roption :=
{ bind_pure_comp_eq_map := @bind_some_eq_map,
  id_map := λβ f, by cases f; refl,
  pure_bind := @some_bind,
  bind_assoc := @bind_assoc }

instance : monad_fail roption :=
{ fail := λ_ _, roption.none, ..roption.monad }

/- `restrict p o h` replaces the domain of `o` with `p`, and is well defined when
  `p` implies `o` is defined. -/
def restrict (p : Prop) : ∀ (o : roption α), (p → o.dom) → roption α
| ⟨d, f⟩ H := ⟨p, λh, f (H h)⟩

/-- `unwrap o` gets the value at `o`, ignoring the condition.
  (This function is unsound.) -/
meta def unwrap (o : roption α) : α := o.get undefined

theorem mem_unique : relator.left_unique ((∈) : α → roption α → Prop)
| ._ ⟨p, f⟩ ._ ⟨h1, rfl⟩ ⟨h2, rfl⟩ := rfl

theorem mem_some (a : α) : a ∈ roption.some a := ⟨trivial, rfl⟩

theorem mem_ret (a) : a ∈ (return a : roption α) := mem_some a

@[simp] theorem mem_ret_iff (a b) : b ∈ (return a : roption α) ↔ b = a :=
⟨λ⟨h, e⟩, e.symm, λ e, ⟨trivial, e.symm⟩⟩

theorem eq_ret_of_mem : ∀ {a : α} {o : roption α}, a ∈ o → o = return a
| ._ ⟨p, f⟩ ⟨h, rfl⟩ := begin
  apply roption.ext,
  exact iff_true_intro h,
  intros, refl
end

theorem mem_bind {f : roption α} {g : α → roption β} :
  ∀ {a b}, a ∈ f → b ∈ g a → b ∈ roption.bind f g
| ._ ._ ⟨h, rfl⟩ ⟨h2, rfl⟩ := ⟨⟨_, _⟩, rfl⟩

theorem exists_of_mem_bind {f : roption α} {g : α → roption β} :
  ∀ {b}, b ∈ roption.bind f g → ∃ a ∈ f, b ∈ g a
| ._ ⟨⟨h1, h2⟩, rfl⟩ := ⟨_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

theorem assert_defined {p : Prop} {f : p → roption α} :
  ∀ (h : p), (f h).dom → (roption.assert p f).dom := exists.intro

theorem bind_defined {f : roption α} {g : α → roption β} :
  ∀ (h : f.dom), (g (f.get h)).dom → (roption.bind f g).dom := assert_defined

end roption

/-- `pfun α β`, or `α →. β`, is the type of partial functions from
  `α` to `β`. It is defined as `α → roption β`. -/
def pfun (α : Type u) (β : Type v) : Type (max u v) := α → roption β

infixr ` →. `:25 := pfun

namespace pfun
variables {α : Type u} {β : Type v} {γ : Type w}

/-- The domain of a partial function -/
def dom (f : α →. β) : set α := λ a, (f a).dom

/-- Evaluate a partial function -/
def fn (f : α →. β) (x) (h : dom f x) : β := (f x).get h

/-- Evaluate a partial function to return an `option` -/
def eval_opt (f : α →. β) [D : decidable_pred (dom f)] (x : α) : option β :=
@roption.to_option _ _ (D x)

/-- Partial function extensionality -/
protected def ext {f g : α →. β}
  (H1 : ∀x, x ∈ dom f ↔ x ∈ dom g)
  (H2 : ∀x p q, f.fn x p = g.fn x q) : f = g :=
funext $ λx, roption.ext (H1 x) (H2 x)

/-- Turn a partial function into a function out of a subtype -/
def as_subtype (f : α →. β) (s : {x // f.dom x}) : β := f.fn s.1 s.2

/-- Turn a total function into a partial function -/
protected def lift (f : α → β) : α →. β := λ a, roption.some (f a)

instance : has_coe (α → β) (α →. β) := ⟨pfun.lift⟩

/-- The graph of a partial function is the set of pairs
  `(x, f x)` where `x` is in the domain of `f`. -/
def graph (f : α →. β) : set (α × β) := {p | p.2 ∈ f p.1}

/-- The range of a partial function is the set of values
  `f x` where `x` is in the domain of `f`. -/
def ran (f : α →. β) : set β := {b | ∃a, b ∈ f a}

/-- Restrict a partial function to a smaller domain. -/
def restrict (f : α →. β) {p : set α} (H : p ⊆ f.dom) : α →. β :=
λ x, roption.restrict (p x) (f x) (@H x)

theorem dom_iff_graph (f : α →. β) (x : α) : x ∈ f.dom ↔ ∃y, (x, y) ∈ f.graph :=
roption.dom_iff_mem _

theorem lift_graph {f : α → β} {a b} : (a, b) ∈ (f : α →. β).graph ↔ f a = b :=
show (∃ (h : true), f a = b) ↔ f a = b, by simp

/-- The monad `pure` function, the total constant `x` function -/
protected def pure (x : β) : α →. β := λ_, roption.some x

/-- The monad `bind` function, pointwise `roption.bind` -/
protected def bind (f : α →. β) (g : β → α →. γ) : α →. γ :=
λa, roption.bind (f a) (λb, g b a)

/-- The monad `map` function, pointwise `roption.map` -/
protected def map (f : β → γ) (g : α →. β) : α →. γ :=
λa, roption.map f (g a)

instance : monad (pfun.{u v} α) :=
{ pure := @pfun.pure _,
  bind := @pfun.bind _,
  map := @pfun.map _ }

instance : is_lawful_monad (pfun.{u v} α) :=
{ bind_pure_comp_eq_map := λβ γ f x, funext $ λ a, roption.bind_some_eq_map _ _,
  id_map := λβ f, by funext a; dsimp [functor.map, pfun.map]; cases f a; refl,
  pure_bind := λβ γ x f, funext $ λ a, roption.some_bind _ (f x),
  bind_assoc := λβ γ δ f g k,
    funext $ λ a, roption.bind_assoc (f a) (λ b, g b a) (λ b, k b a) }

theorem pure_defined (p : set α) (x : β) : p ⊆ (@pfun.pure α _ x).dom := set.subset_univ p

theorem bind_defined {α : Type u} {β γ : Type v} (p : set α) {f : α →. β} {g : β → α →. γ}
  (H1 : p ⊆ f.dom) (H2 : ∀x, p ⊆ (g x).dom) : p ⊆ (f >>= g).dom :=
λa ha, (⟨H1 ha, H2 _ ha⟩ : (f >>= g).dom a)

end pfun