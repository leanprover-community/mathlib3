/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon
-/
import data.part
import data.rel

/-!
# Partial functions

This file defines partial functions. Partial functions are like functions, except they can also be
"undefined" on some inputs. We define them as functions `α → part β`.

## Definitions

* `pfun α β`: Type of partial functions from `α` to `β`. Defined as `α → part β` and denoted
  `α →. β`.
* `pfun.dom`: Domain of a partial function. Set of values on which it is defined. Not to be confused
  with the domain of a function `α → β`, which is a type (`α` presently).
* `pfun.fn`: Evaluation of a partial function. Takes in an element and a proof it belongs to the
  partial function's `dom`.
* `pfun.as_subtype`: Returns a partial function as a function from its `dom`.
* `pfun.eval_opt`: Returns a partial function with a decidable `dom` as a function `a → option β`.
* `pfun.lift`: Turns a function into a partial function.
* `pfun.restrict`: Restriction of a partial function to a smaller `dom`.
* `pfun.res`: Turns a function into a partial function with a prescribed domain.
* `pfun.fix` : First return map of a partial function `f : α →. β ⊕ α`.
* `pfun.fix_induction`: A recursion principle for `pfun.fix`.

### Partial functions as relations

Partial functions can be considered as relations, so we specialize some `rel` definitions to `pfun`:
* `pfun.image`: Preimage of a set under a partial function.
* `pfun.ran`: Range of a partial function.
* `pfun.preimage`: Preimage of a set under a partial function.
* `pfun.core`: Core of a set under a partial function.
* `pfun.graph`: Graph of a partial function `a →. β`as a `set (α × β)`.
* `pfun.graph'`: Graph of a partial function `a →. β`as a `rel α β`.

### `pfun α` as a monad

Monad operations:
* `pfun.pure`: The monad `pure` function, the constant `x` function.
* `pfun.bind`: The monad `bind` function, pointwise `part.bind`
* `pfun.map`: The monad `map` function, pointwise `part.map`.
-/

/-- `pfun α β`, or `α →. β`, is the type of partial functions from
  `α` to `β`. It is defined as `α → part β`. -/
def pfun (α β : Type*) := α → part β

infixr ` →. `:25 := pfun

namespace pfun
variables {α β γ : Type*}

instance : inhabited (α →. β) := ⟨λ a, part.none⟩

/-- The domain of a partial function -/
def dom (f : α →. β) : set α := {a | (f a).dom}

theorem mem_dom (f : α →. β) (x : α) : x ∈ dom f ↔ ∃ y, y ∈ f x :=
by simp [dom, part.dom_iff_mem]

theorem dom_eq (f : α →. β) : dom f = {x | ∃ y, y ∈ f x} :=
set.ext (mem_dom f)

/-- Evaluate a partial function -/
def fn (f : α →. β) (x) (h : dom f x) : β := (f x).get h

/-- Evaluate a partial function to return an `option` -/
def eval_opt (f : α →. β) [D : decidable_pred (∈ dom f)] (x : α) : option β :=
@part.to_option _ _ (D x)

/-- Partial function extensionality -/
theorem ext' {f g : α →. β}
  (H1 : ∀ a, a ∈ dom f ↔ a ∈ dom g)
  (H2 : ∀ a p q, f.fn a p = g.fn a q) : f = g :=
funext $ λ a, part.ext' (H1 a) (H2 a)

theorem ext {f g : α →. β} (H : ∀ a b, b ∈ f a ↔ b ∈ g a) : f = g :=
funext $ λ a, part.ext (H a)

/-- Turns a partial function into a function out of its domain. -/
def as_subtype (f : α →. β) (s : f.dom) : β := f.fn s s.2

/-- The type of partial functions `α →. β` is equivalent to
the type of pairs `(p : α → Prop, f : subtype p → β)`. -/
def equiv_subtype : (α →. β) ≃ (Σ p : α → Prop, subtype p → β) :=
⟨λ f, ⟨λ a, (f a).dom, as_subtype f⟩,
 λ f x, ⟨f.1 x, λ h, f.2 ⟨x, h⟩⟩,
 λ f, funext $ λ a, part.eta _,
 λ ⟨p, f⟩, by dsimp; congr; funext a; cases a; refl⟩

theorem as_subtype_eq_of_mem {f : α →. β} {x : α} {y : β} (fxy : y ∈ f x) (domx : x ∈ f.dom) :
  f.as_subtype ⟨x, domx⟩ = y :=
part.mem_unique (part.get_mem _) fxy

/-- Turn a total function into a partial function. -/
protected def lift (f : α → β) : α →. β := λ a, part.some (f a)

instance : has_coe (α → β) (α →. β) := ⟨pfun.lift⟩

@[simp] theorem lift_eq_coe (f : α → β) : pfun.lift f = f := rfl

@[simp] theorem coe_val (f : α → β) (a : α) :
  (f : α →. β) a = part.some (f a) := rfl

/-- Graph of a partial function `f` as the set of pairs `(x, f x)` where `x` is in the domain of
`f`. -/
def graph (f : α →. β) : set (α × β) := {p | p.2 ∈ f p.1}

/-- Graph of a partial function as a relation. `x` and `y` are related iff `f x` is defined and
"equals" `y`. -/
def graph' (f : α →. β) : rel α β := λ x y, y ∈ f x

/-- The range of a partial function is the set of values
  `f x` where `x` is in the domain of `f`. -/
def ran (f : α →. β) : set β := {b | ∃ a, b ∈ f a}

/-- Restrict a partial function to a smaller domain. -/
def restrict (f : α →. β) {p : set α} (H : p ⊆ f.dom) : α →. β :=
λ x, (f x).restrict (x ∈ p) (@H x)

@[simp]
theorem mem_restrict {f : α →. β} {s : set α} (h : s ⊆ f.dom) (a : α) (b : β) :
  b ∈ f.restrict h a ↔ a ∈ s ∧ b ∈ f a :=
by simp [restrict]

/-- Turns a function into a partial function with a prescribed domain. -/
def res (f : α → β) (s : set α) : α →. β :=
(pfun.lift f).restrict s.subset_univ

theorem mem_res (f : α → β) (s : set α) (a : α) (b : β) :
  b ∈ res f s a ↔ (a ∈ s ∧ f a = b) :=
by simp [res, @eq_comm _ b]

theorem res_univ (f : α → β) : pfun.res f set.univ = f :=
rfl

theorem dom_iff_graph (f : α →. β) (x : α) : x ∈ f.dom ↔ ∃ y, (x, y) ∈ f.graph :=
part.dom_iff_mem

theorem lift_graph {f : α → β} {a b} : (a, b) ∈ (f : α →. β).graph ↔ f a = b :=
show (∃ (h : true), f a = b) ↔ f a = b, by simp

/-- The monad `pure` function, the total constant `x` function -/
protected def pure (x : β) : α →. β := λ _, part.some x

/-- The monad `bind` function, pointwise `part.bind` -/
def bind (f : α →. β) (g : β → α →. γ) : α →. γ :=
λ a, (f a).bind (λ b, g b a)

/-- The monad `map` function, pointwise `part.map` -/
def map (f : β → γ) (g : α →. β) : α →. γ :=
λ a, (g a).map f

instance : monad (pfun α) :=
{ pure := @pfun.pure _,
  bind := @pfun.bind _,
  map := @pfun.map _ }

instance : is_lawful_monad (pfun α) :=
{ bind_pure_comp_eq_map := λ β γ f x, funext $ λ a, part.bind_some_eq_map _ _,
  id_map := λ β f, by funext a; dsimp [functor.map, pfun.map]; cases f a; refl,
  pure_bind := λ β γ x f, funext $ λ a, part.bind_some.{u_1 u_2} _ (f x),
  bind_assoc := λ β γ δ f g k,
    funext $ λ a, (f a).bind_assoc (λ b, g b a) (λ b, k b a) }

theorem pure_defined (p : set α) (x : β) : p ⊆ (@pfun.pure α _ x).dom := p.subset_univ

theorem bind_defined {α β γ} (p : set α) {f : α →. β} {g : β → α →. γ}
  (H1 : p ⊆ f.dom) (H2 : ∀ x, p ⊆ (g x).dom) : p ⊆ (f >>= g).dom :=
λ a ha, (⟨H1 ha, H2 _ ha⟩ : (f >>= g).dom a)

/-- First return map. Transforms a partial function `f : α →. β ⊕ α` into the partial function
`α →. β` which sends `a : α` to the first value in `β` it hits by iterating `f`, if such a value
exists. By abusing notation to illustrate, either `f a` is in the `β` part of `β ⊕ α` (in which
case `f.fix a` returns `f a`), or it is undefined (in which case `f.fix a` is undefined as well), or
it is in the `α` part of `β ⊕ α` (in which case we repeat the procedure, so `f.fix a` will return
`f.fix (f a)`). -/
def fix (f : α →. β ⊕ α) : α →. β := λ a,
part.assert (acc (λ x y, sum.inr x ∈ f y) a) $ λ h,
@well_founded.fix_F _ (λ x y, sum.inr x ∈ f y) _
  (λ a IH, part.assert (f a).dom $ λ hf,
    by cases e : (f a).get hf with b a';
      [exact part.some b, exact IH _ ⟨hf, e⟩])
  a h

theorem dom_of_mem_fix {f : α →. β ⊕ α} {a : α} {b : β}
  (h : b ∈ f.fix a) : (f a).dom :=
let ⟨h₁, h₂⟩ := part.mem_assert_iff.1 h in
by rw well_founded.fix_F_eq at h₂; exact h₂.fst.fst

theorem mem_fix_iff {f : α →. β ⊕ α} {a : α} {b : β} :
  b ∈ f.fix a ↔ sum.inl b ∈ f a ∨ ∃ a', sum.inr a' ∈ f a ∧ b ∈ f.fix a' :=
⟨λ h, let ⟨h₁, h₂⟩ := part.mem_assert_iff.1 h in
  begin
    rw well_founded.fix_F_eq at h₂,
    simp at h₂,
    cases h₂ with h₂ h₃,
    cases e : (f a).get h₂ with b' a'; simp [e] at h₃,
    { subst b', refine or.inl ⟨h₂, e⟩ },
    { exact or.inr ⟨a', ⟨_, e⟩, part.mem_assert _ h₃⟩ }
  end,
λ h, begin
  simp [fix],
  rcases h with ⟨h₁, h₂⟩ | ⟨a', h, h₃⟩,
  { refine ⟨⟨_, λ y h', _⟩, _⟩,
    { injection part.mem_unique ⟨h₁, h₂⟩ h' },
    { rw well_founded.fix_F_eq, simp [h₁, h₂] } },
  { simp [fix] at h₃, cases h₃ with h₃ h₄,
    refine ⟨⟨_, λ y h', _⟩, _⟩,
    { injection part.mem_unique h h' with e,
      exact e ▸ h₃ },
    { cases h with h₁ h₂,
      rw well_founded.fix_F_eq, simp [h₁, h₂, h₄] } }
end⟩

/-- A recursion principle for `pfun.fix`. -/
@[elab_as_eliminator] def fix_induction
  {f : α →. β ⊕ α} {b : β} {C : α → Sort*} {a : α} (h : b ∈ f.fix a)
  (H : ∀ a, b ∈ f.fix a →
    (∀ a', b ∈ f.fix a' → sum.inr a' ∈ f a → C a') → C a) : C a :=
begin
  replace h := part.mem_assert_iff.1 h,
  have := h.snd, revert this,
  induction h.fst with a ha IH, intro h₂,
  refine H a (part.mem_assert_iff.2 ⟨⟨_, ha⟩, h₂⟩)
    (λ a' ha' fa', _),
  have := (part.mem_assert_iff.1 ha').snd,
  exact IH _ fa' ⟨ha _ fa', this⟩ this
end

end pfun

namespace pfun

variables {α β : Type*} (f : α →. β)

/-- Image of a set under a partial function. -/
def image (s : set α) : set β := f.graph'.image s

lemma image_def (s : set α) : f.image s = {y | ∃ x ∈ s, y ∈ f x} := rfl

lemma mem_image (y : β) (s : set α) : y ∈ f.image s ↔ ∃ x ∈ s, y ∈ f x :=
iff.rfl

lemma image_mono {s t : set α} (h : s ⊆ t) : f.image s ⊆ f.image t :=
rel.image_mono _ h

lemma image_inter (s t : set α) : f.image (s ∩ t) ⊆ f.image s ∩ f.image t :=
rel.image_inter _ s t

lemma image_union (s t : set α) : f.image (s ∪ t) = f.image s ∪ f.image t :=
rel.image_union _ s t

/-- Preimage of a set under a partial function. -/
def preimage (s : set β) : set α := rel.image (λ x y, x ∈ f y) s

lemma preimage_def (s : set β) : f.preimage s = {x | ∃ y ∈ s, y ∈ f x} := rfl

lemma mem_preimage (s : set β) (x : α) : x ∈ f.preimage s ↔ ∃ y ∈ s, y ∈ f x :=
iff.rfl

lemma preimage_subset_dom (s : set β) : f.preimage s ⊆ f.dom :=
λ x ⟨y, ys, fxy⟩, part.dom_iff_mem.mpr ⟨y, fxy⟩

lemma preimage_mono {s t : set β} (h : s ⊆ t) : f.preimage s ⊆ f.preimage t :=
rel.preimage_mono _ h

lemma preimage_inter (s t : set β) : f.preimage (s ∩ t) ⊆ f.preimage s ∩ f.preimage t :=
rel.preimage_inter _ s t

lemma preimage_union (s t : set β) : f.preimage (s ∪ t) = f.preimage s ∪ f.preimage t :=
rel.preimage_union _ s t

lemma preimage_univ : f.preimage set.univ = f.dom :=
by ext; simp [mem_preimage, mem_dom]

/-- Core of a set `s : set β` with respect to a partial function `f : α →. β`. Set of all `a : α`
such that `f a ∈ s`, if `f a` is defined. -/
def core (s : set β) : set α := f.graph'.core s

lemma core_def (s : set β) : f.core s = {x | ∀ y, y ∈ f x → y ∈ s} := rfl

lemma mem_core (x : α) (s : set β) : x ∈ f.core s ↔ (∀ y, y ∈ f x → y ∈ s) :=
iff.rfl

lemma compl_dom_subset_core (s : set β) : f.domᶜ ⊆ f.core s :=
λ x hx y fxy,
absurd ((mem_dom f x).mpr ⟨y, fxy⟩) hx

lemma core_mono {s t : set β} (h : s ⊆ t) : f.core s ⊆ f.core t :=
rel.core_mono _ h

lemma core_inter (s t : set β) : f.core (s ∩ t) = f.core s ∩ f.core t :=
rel.core_inter _ s t

lemma mem_core_res (f : α → β) (s : set α) (t : set β) (x : α) :
  x ∈ (res f s).core t ↔ x ∈ s → f x ∈ t :=
by simp [mem_core, mem_res]

section
open_locale classical

lemma core_res (f : α → β) (s : set α) (t : set β) : (res f s).core t = sᶜ ∪ f ⁻¹' t :=
by { ext, rw mem_core_res, by_cases h : x ∈ s; simp [h] }

end

lemma core_restrict (f : α → β) (s : set β) : (f : α →. β).core s = s.preimage f :=
by ext x; simp [core_def]

lemma preimage_subset_core (f : α →. β) (s : set β) : f.preimage s ⊆ f.core s :=
λ x ⟨y, ys, fxy⟩ y' fxy',
have y = y', from part.mem_unique fxy fxy',
this ▸ ys

lemma preimage_eq (f : α →. β) (s : set β) : f.preimage s = f.core s ∩ f.dom :=
set.eq_of_subset_of_subset
  (set.subset_inter (f.preimage_subset_core s) (f.preimage_subset_dom s))
  (λ x ⟨xcore, xdom⟩,
    let y := (f x).get xdom in
    have ys : y ∈ s, from xcore _ (part.get_mem _),
    show x ∈ f.preimage s, from  ⟨(f x).get xdom, ys, part.get_mem _⟩)

lemma core_eq (f : α →. β) (s : set β) : f.core s = f.preimage s ∪ f.domᶜ :=
by rw [preimage_eq, set.union_distrib_right, set.union_comm (dom f), set.compl_union_self,
        set.inter_univ, set.union_eq_self_of_subset_right (f.compl_dom_subset_core s)]

lemma preimage_as_subtype (f : α →. β) (s : set β) :
  f.as_subtype ⁻¹' s = subtype.val ⁻¹' f.preimage s :=
begin
  ext x,
  simp only [set.mem_preimage, set.mem_set_of_eq, pfun.as_subtype, pfun.mem_preimage],
  show f.fn (x.val) _ ∈ s ↔ ∃ y ∈ s, y ∈ f (x.val),
  exact iff.intro
    (λ h, ⟨_, h, part.get_mem _⟩)
    (λ ⟨y, ys, fxy⟩,
      have f.fn x.val x.property ∈ f x.val := part.get_mem _,
      part.mem_unique fxy this ▸ ys)
end

end pfun
