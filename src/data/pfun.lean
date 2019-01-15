/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.set.basic data.option.basic data.equiv.basic

/-- `roption α` is the type of "partial values" of type `α`. It
  is similar to `option α` except the domain condition can be an
  arbitrary proposition, not necessarily decidable. -/
structure {u} roption (α : Type u) : Type u :=
(dom : Prop)
(get : dom → α)

namespace roption
variables {α : Type*} {β : Type*} {γ : Type*}

/-- Convert an `roption α` with a decidable domain to an option -/
def to_option (o : roption α) [decidable o.dom] : option α :=
if h : dom o then some (o.get h) else none

/-- `roption` extensionality -/
def ext' : Π {o p : roption α}
  (H1 : o.dom ↔ p.dom)
  (H2 : ∀h₁ h₂, o.get h₁ = p.get h₂), o = p
| ⟨od, o⟩ ⟨pd, p⟩ H1 H2 := have t : od = pd, from propext H1,
  by cases t; rw [show o = p, from funext $ λp, H2 p p]

/-- `roption` eta expansion -/
@[simp] theorem eta : Π (o : roption α), (⟨o.dom, λ h, o.get h⟩ : roption α) = o
| ⟨h, f⟩ := rfl

/-- `a ∈ o` means that `o` is defined and equal to `a` -/
protected def mem (a : α) (o : roption α) : Prop := ∃ h, o.get h = a

instance : has_mem α (roption α) := ⟨roption.mem⟩

theorem dom_iff_mem : ∀ {o : roption α}, o.dom ↔ ∃y, y ∈ o
| ⟨p, f⟩ := ⟨λh, ⟨f h, h, rfl⟩, λ⟨_, h, rfl⟩, h⟩

theorem get_mem {o : roption α} (h) : get o h ∈ o := ⟨_, rfl⟩

/-- `roption` extensionality -/
def ext {o p : roption α} (H : ∀ a, a ∈ o ↔ a ∈ p) : o = p :=
ext' ⟨λ h, ((H _).1 ⟨h, rfl⟩).fst,
     λ h, ((H _).2 ⟨h, rfl⟩).fst⟩ $
λ a b, ((H _).2 ⟨_, rfl⟩).snd

/-- The `none` value in `roption` has a `false` domain and an empty function. -/
def none : roption α := ⟨false, false.rec _⟩

@[simp] theorem not_mem_none (a : α) : a ∉ @none α := λ h, h.fst

/-- The `some a` value in `roption` has a `true` domain and the
  function returns `a`. -/
def some (a : α) : roption α := ⟨true, λ_, a⟩

theorem mem_unique : relator.left_unique ((∈) : α → roption α → Prop)
| _ ⟨p, f⟩ _ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩ := rfl

theorem get_eq_of_mem {o : roption α} {a} (h : a ∈ o) (h') : get o h' = a :=
mem_unique ⟨_, rfl⟩ h

@[simp] theorem get_some {a : α} (ha : (some a).dom) : get (some a) ha = a := rfl

theorem mem_some (a : α) : a ∈ some a := ⟨trivial, rfl⟩

@[simp] theorem mem_some_iff {a b} : b ∈ (some a : roption α) ↔ b = a :=
⟨λ⟨h, e⟩, e.symm, λ e, ⟨trivial, e.symm⟩⟩

theorem eq_some_iff {a : α} {o : roption α} : o = some a ↔ a ∈ o :=
⟨λ e, e.symm ▸ mem_some _,
 λ ⟨h, e⟩, e ▸ ext' (iff_true_intro h) (λ _ _, rfl)⟩

theorem eq_none_iff {o : roption α} : o = none ↔ ∀ a, a ∉ o :=
⟨λ e, e.symm ▸ not_mem_none,
 λ h, ext (by simpa [not_mem_none])⟩

theorem eq_none_iff' {o : roption α} : o = none ↔ ¬ o.dom :=
⟨λ e, e.symm ▸ id, λ h, eq_none_iff.2 (λ a h', h h'.fst)⟩

@[simp] lemma some_inj {a b : α} : roption.some a = some b ↔ a = b :=
function.injective.eq_iff (λ a b h, congr_fun (eq_of_heq (roption.mk.inj h).2) trivial)

@[simp] lemma some_get {a : roption α} (ha : a.dom) :
  roption.some (roption.get a ha) = a :=
eq.symm (eq_some_iff.2 ⟨ha, rfl⟩)

lemma get_eq_iff_eq_some {a : roption α} {ha : a.dom} {b : α} :
  a.get ha = b ↔ a = some b :=
⟨λ h, by simp [h.symm], λ h, by simp [h]⟩

instance none_decidable : decidable (@none α).dom := decidable.false
instance some_decidable (a : α) : decidable (some a).dom := decidable.true

def get_or_else (a : roption α) [decidable a.dom] (d : α) :=
if ha : a.dom then a.get ha else d

@[simp] lemma get_or_else_none (d : α) : get_or_else none d = d :=
dif_neg id

@[simp] lemma get_or_else_some (a : α) (d : α) : get_or_else (some a) d = a :=
dif_pos trivial

@[simp] theorem mem_to_option {o : roption α} [decidable o.dom] {a : α} :
  a ∈ to_option o ↔ a ∈ o :=
begin
  unfold to_option,
  by_cases h : o.dom; simp [h],
  { exact ⟨λ h, ⟨_, h⟩, λ ⟨_, h⟩, h⟩ },
  { exact mt Exists.fst h }
end

/-- Convert an `option α` into an `roption α` -/
def of_option : option α → roption α
| option.none     := none
| (option.some a) := some a

@[simp] theorem mem_of_option {a : α} : ∀ {o : option α}, a ∈ of_option o ↔ a ∈ o
| option.none     := ⟨λ h, h.fst.elim, λ h, option.no_confusion h⟩
| (option.some b) := ⟨λ h, congr_arg option.some h.snd,
  λ h, ⟨trivial, option.some.inj h⟩⟩

@[simp] theorem of_option_dom {α} : ∀ (o : option α), (of_option o).dom ↔ o.is_some
| option.none     := by simp [of_option, none]
| (option.some a) := by simp [of_option]

theorem of_option_eq_get {α} (o : option α) : of_option o = ⟨_, @option.get _ o⟩ :=
roption.ext' (of_option_dom o) $ λ h₁ h₂, by cases o; [cases h₁, refl]

instance : has_coe (option α) (roption α) := ⟨of_option⟩

@[simp] theorem mem_coe {a : α} {o : option α} :
  a ∈ (o : roption α) ↔ a ∈ o := mem_of_option

@[simp] theorem coe_none : (@option.none α : roption α) = none := rfl
@[simp] theorem coe_some (a : α) : (option.some a : roption α) = some a := rfl

@[elab_as_eliminator] protected lemma roption.induction_on {P : roption α → Prop}
  (a : roption α) (hnone : P none) (hsome : ∀ a : α, P (some a)) : P a :=
(classical.em a.dom).elim
  (λ h, roption.some_get h ▸ hsome _)
  (λ h, (eq_none_iff'.2 h).symm ▸ hnone)

instance of_option_decidable : ∀ o : option α, decidable (of_option o).dom
| option.none     := roption.none_decidable
| (option.some a) := roption.some_decidable a

@[simp] theorem to_of_option (o : option α) : to_option (of_option o) = o :=
by cases o; refl

@[simp] theorem of_to_option (o : roption α) [decidable o.dom] : of_option (to_option o) = o :=
ext $ λ a, mem_of_option.trans mem_to_option

noncomputable def equiv_option : roption α ≃ option α :=
by haveI := classical.dec; exact
⟨λ o, to_option o, of_option, λ o, of_to_option o,
 λ o, eq.trans (by dsimp; congr) (to_of_option o)⟩

/-- `assert p f` is a bind-like operation which appends an additional condition
  `p` to the domain and uses `f` to produce the value. -/
def assert (p : Prop) (f : p → roption α) : roption α :=
⟨∃h : p, (f h).dom, λha, (f ha.fst).get ha.snd⟩

/-- The bind operation has value `g (f.get)`, and is defined when all the
  parts are defined. -/
protected def bind (f : roption α) (g : α → roption β) : roption β :=
assert (dom f) (λb, g (f.get b))

/-- The map operation for `roption` just maps the value and maintains the same domain. -/
def map (f : α → β) (o : roption α) : roption β :=
⟨o.dom, f ∘ o.get⟩

theorem mem_map (f : α → β) {o : roption α} :
  ∀ {a}, a ∈ o → f a ∈ map f o
| _ ⟨h, rfl⟩ := ⟨_, rfl⟩

@[simp] theorem mem_map_iff (f : α → β) {o : roption α} {b} :
  b ∈ map f o ↔ ∃ a ∈ o, f a = b :=
⟨match b with _, ⟨h, rfl⟩ := ⟨_, ⟨_, rfl⟩, rfl⟩ end,
 λ ⟨a, h₁, h₂⟩, h₂ ▸ mem_map f h₁⟩

@[simp] theorem map_none (f : α → β) :
  map f none = none := eq_none_iff.2 $ λ a, by simp

@[simp] theorem map_some (f : α → β) (a : α) : map f (some a) = some (f a) :=
eq_some_iff.2 $ mem_map f $ mem_some _

theorem mem_assert {p : Prop} {f : p → roption α}
  : ∀ {a} (h : p), a ∈ f h → a ∈ assert p f
| _ _ ⟨h, rfl⟩ := ⟨⟨_, _⟩, rfl⟩

@[simp] theorem mem_assert_iff {p : Prop} {f : p → roption α} {a} :
  a ∈ assert p f ↔ ∃ h : p, a ∈ f h :=
⟨match a with _, ⟨h, rfl⟩ := ⟨_, ⟨_, rfl⟩⟩ end,
 λ ⟨a, h⟩, mem_assert _ h⟩

theorem mem_bind {f : roption α} {g : α → roption β} :
  ∀ {a b}, a ∈ f → b ∈ g a → b ∈ f.bind g
| _ _ ⟨h, rfl⟩ ⟨h₂, rfl⟩ := ⟨⟨_, _⟩, rfl⟩

@[simp] theorem mem_bind_iff {f : roption α} {g : α → roption β} {b} :
  b ∈ f.bind g ↔ ∃ a ∈ f, b ∈ g a :=
⟨match b with _, ⟨⟨h₁, h₂⟩, rfl⟩ := ⟨_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩ end,
 λ ⟨a, h₁, h₂⟩, mem_bind h₁ h₂⟩

@[simp] theorem bind_none (f : α → roption β) :
  none.bind f = none := eq_none_iff.2 $ λ a, by simp

@[simp] theorem bind_some (a : α) (f : α → roption β) :
  (some a).bind f = f a := ext $ by simp

theorem bind_some_eq_map (f : α → β) (x : roption α) :
  x.bind (some ∘ f) = map f x :=
ext $ by simp [eq_comm]

theorem bind_assoc {γ} (f : roption α) (g : α → roption β) (k : β → roption γ) :
  (f.bind g).bind k = f.bind (λ x, (g x).bind k) :=
ext $ λ a, by simp; exact
 ⟨λ ⟨_, ⟨_, h₁, h₂⟩, h₃⟩, ⟨_, h₁, _, h₂, h₃⟩,
  λ ⟨_, h₁, _, h₂, h₃⟩, ⟨_, ⟨_, h₁, h₂⟩, h₃⟩⟩

@[simp] theorem bind_map {γ} (f : α → β) (x) (g : β → roption γ) :
  (map f x).bind g = x.bind (λ y, g (f y)) :=
by rw [← bind_some_eq_map, bind_assoc]; simp

@[simp] theorem map_bind {γ} (f : α → roption β) (x : roption α) (g : β → γ) :
  map g (x.bind f) = x.bind (λ y, map g (f y)) :=
by rw [← bind_some_eq_map, bind_assoc]; simp [bind_some_eq_map]

theorem map_map (g : β → γ) (f : α → β) (o : roption α) :
  map g (map f o) = map (g ∘ f) o :=
by rw [← bind_some_eq_map, bind_map, bind_some_eq_map]

instance : monad roption :=
{ pure := @some,
  map := @map,
  bind := @roption.bind }

instance : is_lawful_monad roption :=
{ bind_pure_comp_eq_map := @bind_some_eq_map,
  id_map := λ β f, by cases f; refl,
  pure_bind := @bind_some,
  bind_assoc := @bind_assoc }

theorem map_id' {f : α → α} (H : ∀ (x : α), f x = x) (o) : map f o = o :=
by rw [show f = id, from funext H]; exact id_map o

@[simp] theorem bind_some_right (x : roption α) : x.bind some = x :=
by rw [bind_some_eq_map]; simp [map_id']

@[simp] theorem ret_eq_some (a : α) : return a = some a := rfl

@[simp] theorem map_eq_map {α β} (f : α → β) (o : roption α) :
  f <$> o = map f o := rfl

@[simp] theorem bind_eq_bind {α β} (f : roption α) (g : α → roption β) :
  f >>= g = f.bind g := rfl

instance : monad_fail roption :=
{ fail := λ_ _, none, ..roption.monad }

/- `restrict p o h` replaces the domain of `o` with `p`, and is well defined when
  `p` implies `o` is defined. -/
def restrict (p : Prop) : ∀ (o : roption α), (p → o.dom) → roption α
| ⟨d, f⟩ H := ⟨p, λh, f (H h)⟩

/-- `unwrap o` gets the value at `o`, ignoring the condition.
  (This function is unsound.) -/
meta def unwrap (o : roption α) : α := o.get undefined

theorem assert_defined {p : Prop} {f : p → roption α} :
  ∀ (h : p), (f h).dom → (assert p f).dom := exists.intro

theorem bind_defined {f : roption α} {g : α → roption β} :
  ∀ (h : f.dom), (g (f.get h)).dom → (f.bind g).dom := assert_defined

@[simp] theorem bind_dom {f : roption α} {g : α → roption β} :
  (f.bind g).dom ↔ ∃ h : f.dom, (g (f.get h)).dom := iff.rfl

end roption

/-- `pfun α β`, or `α →. β`, is the type of partial functions from
  `α` to `β`. It is defined as `α → roption β`. -/
def pfun (α : Type*) (β : Type*) := α → roption β

infixr ` →. `:25 := pfun

namespace pfun
variables {α : Type*} {β : Type*} {γ : Type*}

/-- The domain of a partial function -/
def dom (f : α →. β) : set α := λ a, (f a).dom

/-- Evaluate a partial function -/
def fn (f : α →. β) (x) (h : dom f x) : β := (f x).get h

/-- Evaluate a partial function to return an `option` -/
def eval_opt (f : α →. β) [D : decidable_pred (dom f)] (x : α) : option β :=
@roption.to_option _ _ (D x)

/-- Partial function extensionality -/
def ext' {f g : α →. β}
  (H1 : ∀ a, a ∈ dom f ↔ a ∈ dom g)
  (H2 : ∀ a p q, f.fn a p = g.fn a q) : f = g :=
funext $ λ a, roption.ext' (H1 a) (H2 a)

def ext {f g : α →. β} (H : ∀ a b, b ∈ f a ↔ b ∈ g a) : f = g :=
funext $ λ a, roption.ext (H a)

/-- Turn a partial function into a function out of a subtype -/
def as_subtype (f : α →. β) (s : {x // f.dom x}) : β := f.fn s.1 s.2

def equiv_subtype : (α →. β) ≃ (Σ p : α → Prop, subtype p → β) :=
⟨λ f, ⟨f.dom, as_subtype f⟩,
 λ ⟨p, f⟩ x, ⟨p x, λ h, f ⟨x, h⟩⟩,
 λ f, funext $ λ a, roption.eta _,
 λ ⟨p, f⟩, by dsimp; congr; funext a; cases a; refl⟩

/-- Turn a total function into a partial function -/
protected def lift (f : α → β) : α →. β := λ a, roption.some (f a)

instance : has_coe (α → β) (α →. β) := ⟨pfun.lift⟩

@[simp] theorem lift_eq_coe (f : α → β) : pfun.lift f = f := rfl

@[simp] theorem coe_val (f : α → β) (a : α) :
  (f : α →. β) a = roption.some (f a) := rfl

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
roption.dom_iff_mem

theorem lift_graph {f : α → β} {a b} : (a, b) ∈ (f : α →. β).graph ↔ f a = b :=
show (∃ (h : true), f a = b) ↔ f a = b, by simp

/-- The monad `pure` function, the total constant `x` function -/
protected def pure (x : β) : α →. β := λ_, roption.some x

/-- The monad `bind` function, pointwise `roption.bind` -/
def bind (f : α →. β) (g : β → α →. γ) : α →. γ :=
λa, roption.bind (f a) (λb, g b a)

/-- The monad `map` function, pointwise `roption.map` -/
def map (f : β → γ) (g : α →. β) : α →. γ :=
λa, roption.map f (g a)

instance : monad (pfun α) :=
{ pure := @pfun.pure _,
  bind := @pfun.bind _,
  map := @pfun.map _ }

instance : is_lawful_monad (pfun α) :=
{ bind_pure_comp_eq_map := λ β γ f x, funext $ λ a, roption.bind_some_eq_map _ _,
  id_map := λ β f, by funext a; dsimp [functor.map, pfun.map]; cases f a; refl,
  pure_bind := λ β γ x f, funext $ λ a, roption.bind_some.{u_1 u_2} _ (f x),
  bind_assoc := λ β γ δ f g k,
    funext $ λ a, roption.bind_assoc (f a) (λ b, g b a) (λ b, k b a) }

theorem pure_defined (p : set α) (x : β) : p ⊆ (@pfun.pure α _ x).dom := set.subset_univ p

theorem bind_defined {α β γ} (p : set α) {f : α →. β} {g : β → α →. γ}
  (H1 : p ⊆ f.dom) (H2 : ∀x, p ⊆ (g x).dom) : p ⊆ (f >>= g).dom :=
λa ha, (⟨H1 ha, H2 _ ha⟩ : (f >>= g).dom a)

def fix (f : α →. β ⊕ α) : α →. β := λ a,
roption.assert (acc (λ x y, sum.inr x ∈ f y) a) $ λ h,
@well_founded.fix_F _ (λ x y, sum.inr x ∈ f y) _
  (λ a IH, roption.assert (f a).dom $ λ hf,
    by cases e : (f a).get hf with b a';
      [exact roption.some b, exact IH _ ⟨hf, e⟩])
  a h

theorem dom_of_mem_fix {f : α →. β ⊕ α} {a : α} {b : β}
  (h : b ∈ fix f a) : (f a).dom :=
let ⟨h₁, h₂⟩ := roption.mem_assert_iff.1 h in
by rw well_founded.fix_F_eq at h₂; exact h₂.fst.fst

theorem mem_fix_iff {f : α →. β ⊕ α} {a : α} {b : β} :
  b ∈ fix f a ↔ sum.inl b ∈ f a ∨ ∃ a', sum.inr a' ∈ f a ∧ b ∈ fix f a' :=
⟨λ h, let ⟨h₁, h₂⟩ := roption.mem_assert_iff.1 h in
  begin
    rw well_founded.fix_F_eq at h₂,
    simp at h₂,
    cases h₂ with h₂ h₃,
    cases e : (f a).get h₂ with b' a'; simp [e] at h₃,
    { subst b', refine or.inl ⟨h₂, e⟩ },
    { exact or.inr ⟨a', ⟨_, e⟩, roption.mem_assert _ h₃⟩ }
  end,
λ h, begin
  simp [fix],
  rcases h with ⟨h₁, h₂⟩ | ⟨a', h, h₃⟩,
  { refine ⟨⟨_, λ y h', _⟩, _⟩,
    { injection roption.mem_unique ⟨h₁, h₂⟩ h' },
    { rw well_founded.fix_F_eq, simp [h₁, h₂] } },
  { simp [fix] at h₃, cases h₃ with h₃ h₄,
    refine ⟨⟨_, λ y h', _⟩, _⟩,
    { injection roption.mem_unique h h' with e,
      exact e ▸ h₃ },
    { cases h with h₁ h₂,
      rw well_founded.fix_F_eq, simp [h₁, h₂, h₄] } }
end⟩

@[elab_as_eliminator] theorem fix_induction
  {f : α →. β ⊕ α} {b : β} {C : α → Sort*} {a : α} (h : b ∈ fix f a)
  (H : ∀ a, b ∈ fix f a →
    (∀ a', b ∈ fix f a' → sum.inr a' ∈ f a → C a') → C a) : C a :=
begin
  replace h := roption.mem_assert_iff.1 h,
  have := h.snd, revert this,
  induction h.fst with a ha IH, intro h₂,
  refine H a (roption.mem_assert_iff.2 ⟨⟨_, ha⟩, h₂⟩)
    (λ a' ha' fa', _),
  have := (roption.mem_assert_iff.1 ha').snd,
  exact IH _ fa' ⟨ha _ fa', this⟩ this
end

end pfun
