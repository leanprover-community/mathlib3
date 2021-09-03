/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon
-/
import data.equiv.basic

/-!
# Partial values of a type
-/

/-- `part α` is the type of "partial values" of type `α`. It
  is similar to `option α` except the domain condition can be an
  arbitrary proposition, not necessarily decidable. -/
structure {u} part (α : Type u) : Type u :=
(dom : Prop)
(get : dom → α)

namespace part
variables {α : Type*} {β : Type*} {γ : Type*}

/-- Convert a `part α` with a decidable domain to an option -/
def to_option (o : part α) [decidable o.dom] : option α :=
if h : dom o then some (o.get h) else none

/-- `part` extensionality -/
theorem ext' : ∀ {o p : part α}
  (H1 : o.dom ↔ p.dom)
  (H2 : ∀h₁ h₂, o.get h₁ = p.get h₂), o = p
| ⟨od, o⟩ ⟨pd, p⟩ H1 H2 := have t : od = pd, from propext H1,
  by cases t; rw [show o = p, from funext $ λp, H2 p p]

/-- `part` eta expansion -/
@[simp] theorem eta : Π (o : part α), (⟨o.dom, λ h, o.get h⟩ : part α) = o
| ⟨h, f⟩ := rfl

/-- `a ∈ o` means that `o` is defined and equal to `a` -/
protected def mem (a : α) (o : part α) : Prop := ∃ h, o.get h = a

instance : has_mem α (part α) := ⟨part.mem⟩

theorem mem_eq (a : α) (o : part α) : (a ∈ o) = (∃ h, o.get h = a) :=
rfl

theorem dom_iff_mem : ∀ {o : part α}, o.dom ↔ ∃y, y ∈ o
| ⟨p, f⟩ := ⟨λh, ⟨f h, h, rfl⟩, λ⟨_, h, rfl⟩, h⟩

theorem get_mem {o : part α} (h) : get o h ∈ o := ⟨_, rfl⟩

/-- `part` extensionality -/
@[ext]
theorem ext {o p : part α} (H : ∀ a, a ∈ o ↔ a ∈ p) : o = p :=
ext' ⟨λ h, ((H _).1 ⟨h, rfl⟩).fst,
     λ h, ((H _).2 ⟨h, rfl⟩).fst⟩ $
λ a b, ((H _).2 ⟨_, rfl⟩).snd

/-- The `none` value in `part` has a `false` domain and an empty function. -/
def none : part α := ⟨false, false.rec _⟩

instance : inhabited (part α) := ⟨none⟩

@[simp] theorem not_mem_none (a : α) : a ∉ @none α := λ h, h.fst

/-- The `some a` value in `part` has a `true` domain and the
  function returns `a`. -/
def some (a : α) : part α := ⟨true, λ_, a⟩

theorem mem_unique : ∀ {a b : α} {o : part α}, a ∈ o → b ∈ o → a = b
| _ _ ⟨p, f⟩ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩ := rfl

theorem mem.left_unique : relator.left_unique ((∈) : α → part α → Prop) :=
⟨λ a o b, mem_unique⟩

theorem get_eq_of_mem {o : part α} {a} (h : a ∈ o) (h') : get o h' = a :=
mem_unique ⟨_, rfl⟩ h

@[simp] theorem get_some {a : α} (ha : (some a).dom) : get (some a) ha = a := rfl

theorem mem_some (a : α) : a ∈ some a := ⟨trivial, rfl⟩

@[simp] theorem mem_some_iff {a b} : b ∈ (some a : part α) ↔ b = a :=
⟨λ⟨h, e⟩, e.symm, λ e, ⟨trivial, e.symm⟩⟩

theorem eq_some_iff {a : α} {o : part α} : o = some a ↔ a ∈ o :=
⟨λ e, e.symm ▸ mem_some _,
 λ ⟨h, e⟩, e ▸ ext' (iff_true_intro h) (λ _ _, rfl)⟩

theorem eq_none_iff {o : part α} : o = none ↔ ∀ a, a ∉ o :=
⟨λ e, e.symm ▸ not_mem_none,
 λ h, ext (by simpa [not_mem_none])⟩

theorem eq_none_iff' {o : part α} : o = none ↔ ¬ o.dom :=
⟨λ e, e.symm ▸ id, λ h, eq_none_iff.2 (λ a h', h h'.fst)⟩

lemma some_ne_none (x : α) : some x ≠ none :=
by { intro h, change none.dom, rw [← h], trivial }

lemma ne_none_iff {o : part α} : o ≠ none ↔ ∃x, o = some x :=
begin
  split,
  { rw [ne, eq_none_iff], intro h, push_neg at h, cases h with x hx, use x, rwa [eq_some_iff] },
  { rintro ⟨x, rfl⟩, apply some_ne_none }
end

lemma eq_none_or_eq_some (o : part α) : o = none ∨ ∃ x, o = some x :=
begin
  classical,
  by_cases h : o.dom,
  { rw dom_iff_mem at h, right,
    apply exists_imp_exists _ h,
    simp [eq_some_iff] },
  { rw eq_none_iff', exact or.inl h },
end

@[simp] lemma some_inj {a b : α} : part.some a = some b ↔ a = b :=
function.injective.eq_iff (λ a b h, congr_fun (eq_of_heq (part.mk.inj h).2) trivial)

@[simp] lemma some_get {a : part α} (ha : a.dom) :
  part.some (part.get a ha) = a :=
eq.symm (eq_some_iff.2 ⟨ha, rfl⟩)

lemma get_eq_iff_eq_some {a : part α} {ha : a.dom} {b : α} :
  a.get ha = b ↔ a = some b :=
⟨λ h, by simp [h.symm], λ h, by simp [h]⟩

lemma get_eq_get_of_eq (a : part α) (ha : a.dom) {b : part α} (h : a = b) :
  a.get ha = b.get (h ▸ ha) :=
by { congr, exact h }

instance none_decidable : decidable (@none α).dom := decidable.false
instance some_decidable (a : α) : decidable (some a).dom := decidable.true

/-- Retrieves the value of `a : part α` if it exists, and return the provided default value
otherwise. -/
def get_or_else (a : part α) [decidable a.dom] (d : α) :=
if ha : a.dom then a.get ha else d

@[simp] lemma get_or_else_none (d : α) : get_or_else none d = d :=
dif_neg id

@[simp] lemma get_or_else_some (a : α) (d : α) : get_or_else (some a) d = a :=
dif_pos trivial

@[simp] theorem mem_to_option {o : part α} [decidable o.dom] {a : α} :
  a ∈ to_option o ↔ a ∈ o :=
begin
  unfold to_option,
  by_cases h : o.dom; simp [h],
  { exact ⟨λ h, ⟨_, h⟩, λ ⟨_, h⟩, h⟩ },
  { exact mt Exists.fst h }
end

/-- Converts an `option α` into a `part α`. -/
def of_option : option α → part α
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
part.ext' (of_option_dom o) $ λ h₁ h₂, by cases o; [cases h₁, refl]

instance : has_coe (option α) (part α) := ⟨of_option⟩

@[simp] theorem mem_coe {a : α} {o : option α} :
  a ∈ (o : part α) ↔ a ∈ o := mem_of_option

@[simp] theorem coe_none : (@option.none α : part α) = none := rfl
@[simp] theorem coe_some (a : α) : (option.some a : part α) = some a := rfl

@[elab_as_eliminator] protected lemma induction_on {P : part α → Prop}
  (a : part α) (hnone : P none) (hsome : ∀ a : α, P (some a)) : P a :=
(classical.em a.dom).elim
  (λ h, part.some_get h ▸ hsome _)
  (λ h, (eq_none_iff'.2 h).symm ▸ hnone)

instance of_option_decidable : ∀ o : option α, decidable (of_option o).dom
| option.none     := part.none_decidable
| (option.some a) := part.some_decidable a

@[simp] theorem to_of_option (o : option α) : to_option (of_option o) = o :=
by cases o; refl

@[simp] theorem of_to_option (o : part α) [decidable o.dom] : of_option (to_option o) = o :=
ext $ λ a, mem_of_option.trans mem_to_option

/-- `part α` is (classically) equivalent to `option α`. -/
noncomputable def equiv_option : part α ≃ option α :=
by haveI := classical.dec; exact
⟨λ o, to_option o, of_option, λ o, of_to_option o,
 λ o, eq.trans (by dsimp; congr) (to_of_option o)⟩

/-- We give `part α` the order where everything is greater than `none`. -/
instance : order_bot (part α) :=
{ le := λ x y, ∀ i, i ∈ x → i ∈ y,
  le_refl := λ x y, id,
  le_trans := λ x y z f g i, g _ ∘ f _,
  le_antisymm := λ x y f g, part.ext $ λ z, ⟨f _, g _⟩,
  bot := none,
  bot_le := by { introv x, rintro ⟨⟨_⟩,_⟩, } }

instance : preorder (part α) :=
by apply_instance

lemma le_total_of_le_of_le {x y : part α} (z : part α) (hx : x ≤ z) (hy : y ≤ z) :
  x ≤ y ∨ y ≤ x :=
begin
  rcases part.eq_none_or_eq_some x with h | ⟨b, h₀⟩,
  { rw h, left, apply order_bot.bot_le _ },
  right, intros b' h₁,
  rw part.eq_some_iff at h₀,
  replace hx := hx _ h₀, replace hy := hy _ h₁,
  replace hx := part.mem_unique hx hy, subst hx,
  exact h₀
end

/-- `assert p f` is a bind-like operation which appends an additional condition
  `p` to the domain and uses `f` to produce the value. -/
def assert (p : Prop) (f : p → part α) : part α :=
⟨∃h : p, (f h).dom, λha, (f ha.fst).get ha.snd⟩

/-- The bind operation has value `g (f.get)`, and is defined when all the
  parts are defined. -/
protected def bind (f : part α) (g : α → part β) : part β :=
assert (dom f) (λb, g (f.get b))

/-- The map operation for `part` just maps the value and maintains the same domain. -/
def map (f : α → β) (o : part α) : part β :=
⟨o.dom, f ∘ o.get⟩

theorem mem_map (f : α → β) {o : part α} :
  ∀ {a}, a ∈ o → f a ∈ map f o
| _ ⟨h, rfl⟩ := ⟨_, rfl⟩

@[simp] theorem mem_map_iff (f : α → β) {o : part α} {b} :
  b ∈ map f o ↔ ∃ a ∈ o, f a = b :=
⟨match b with _, ⟨h, rfl⟩ := ⟨_, ⟨_, rfl⟩, rfl⟩ end,
 λ ⟨a, h₁, h₂⟩, h₂ ▸ mem_map f h₁⟩

@[simp] theorem map_none (f : α → β) :
  map f none = none := eq_none_iff.2 $ λ a, by simp

@[simp] theorem map_some (f : α → β) (a : α) : map f (some a) = some (f a) :=
eq_some_iff.2 $ mem_map f $ mem_some _

theorem mem_assert {p : Prop} {f : p → part α}
  : ∀ {a} (h : p), a ∈ f h → a ∈ assert p f
| _ x ⟨h, rfl⟩ := ⟨⟨x, h⟩, rfl⟩

@[simp] theorem mem_assert_iff {p : Prop} {f : p → part α} {a} :
  a ∈ assert p f ↔ ∃ h : p, a ∈ f h :=
⟨match a with _, ⟨h, rfl⟩ := ⟨_, ⟨_, rfl⟩⟩ end,
 λ ⟨a, h⟩, mem_assert _ h⟩

lemma assert_pos {p : Prop} {f : p → part α} (h : p) :
  assert p f = f h :=
begin
  dsimp [assert],
  cases h' : f h,
  simp only [h', h, true_and, iff_self, exists_prop_of_true, eq_iff_iff],
  apply function.hfunext,
  { simp only [h,h',exists_prop_of_true] },
  { cc }
end

lemma assert_neg {p : Prop} {f : p → part α} (h : ¬ p) :
  assert p f = none :=
begin
  dsimp [assert,none], congr,
  { simp only [h, not_false_iff, exists_prop_of_false] },
  { apply function.hfunext,
    { simp only [h, not_false_iff, exists_prop_of_false] },
    cc },
end

theorem mem_bind {f : part α} {g : α → part β} :
  ∀ {a b}, a ∈ f → b ∈ g a → b ∈ f.bind g
| _ _ ⟨h, rfl⟩ ⟨h₂, rfl⟩ := ⟨⟨h, h₂⟩, rfl⟩

@[simp] theorem mem_bind_iff {f : part α} {g : α → part β} {b} :
  b ∈ f.bind g ↔ ∃ a ∈ f, b ∈ g a :=
⟨match b with _, ⟨⟨h₁, h₂⟩, rfl⟩ := ⟨_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩ end,
 λ ⟨a, h₁, h₂⟩, mem_bind h₁ h₂⟩

@[simp] theorem bind_none (f : α → part β) :
  none.bind f = none := eq_none_iff.2 $ λ a, by simp

@[simp] theorem bind_some (a : α) (f : α → part β) :
  (some a).bind f = f a := ext $ by simp

theorem bind_some_eq_map (f : α → β) (x : part α) :
  x.bind (some ∘ f) = map f x :=
ext $ by simp [eq_comm]

theorem bind_assoc {γ} (f : part α) (g : α → part β) (k : β → part γ) :
  (f.bind g).bind k = f.bind (λ x, (g x).bind k) :=
ext $ λ a, by simp; exact
 ⟨λ ⟨_, ⟨_, h₁, h₂⟩, h₃⟩, ⟨_, h₁, _, h₂, h₃⟩,
  λ ⟨_, h₁, _, h₂, h₃⟩, ⟨_, ⟨_, h₁, h₂⟩, h₃⟩⟩

@[simp] theorem bind_map {γ} (f : α → β) (x) (g : β → part γ) :
  (map f x).bind g = x.bind (λ y, g (f y)) :=
by rw [← bind_some_eq_map, bind_assoc]; simp

@[simp] theorem map_bind {γ} (f : α → part β) (x : part α) (g : β → γ) :
  map g (x.bind f) = x.bind (λ y, map g (f y)) :=
by rw [← bind_some_eq_map, bind_assoc]; simp [bind_some_eq_map]

theorem map_map (g : β → γ) (f : α → β) (o : part α) :
  map g (map f o) = map (g ∘ f) o :=
by rw [← bind_some_eq_map, bind_map, bind_some_eq_map]

instance : monad part :=
{ pure := @some,
  map := @map,
  bind := @part.bind }

instance : is_lawful_monad part :=
{ bind_pure_comp_eq_map := @bind_some_eq_map,
  id_map := λ β f, by cases f; refl,
  pure_bind := @bind_some,
  bind_assoc := @bind_assoc }

theorem map_id' {f : α → α} (H : ∀ (x : α), f x = x) (o) : map f o = o :=
by rw [show f = id, from funext H]; exact id_map o

@[simp] theorem bind_some_right (x : part α) : x.bind some = x :=
by rw [bind_some_eq_map]; simp [map_id']

@[simp] theorem pure_eq_some (a : α) : pure a = some a := rfl
@[simp] theorem ret_eq_some (a : α) : return a = some a := rfl

@[simp] theorem map_eq_map {α β} (f : α → β) (o : part α) :
  f <$> o = map f o := rfl

@[simp] theorem bind_eq_bind {α β} (f : part α) (g : α → part β) :
  f >>= g = f.bind g := rfl

lemma bind_le {α} (x : part α) (f : α → part β) (y : part β) :
  x >>= f ≤ y ↔ (∀ a, a ∈ x → f a ≤ y) :=
begin
  split; intro h,
  { intros a h' b, replace h := h b,
    simp only [and_imp, exists_prop, bind_eq_bind, mem_bind_iff, exists_imp_distrib] at h,
    apply h _ h' },
  { intros b h',
    simp only [exists_prop, bind_eq_bind, mem_bind_iff] at h',
    rcases h' with ⟨a,h₀,h₁⟩, apply h _ h₀ _ h₁ },
end

instance : monad_fail part :=
{ fail := λ_ _, none, ..part.monad }

/-- `restrict p o h` replaces the domain of `o` with `p`, and is well defined when
  `p` implies `o` is defined. -/
def restrict (p : Prop) : ∀ (o : part α), (p → o.dom) → part α
| ⟨d, f⟩ H := ⟨p, λh, f (H h)⟩

@[simp]
theorem mem_restrict (p : Prop) (o : part α) (h : p → o.dom) (a : α) :
  a ∈ restrict p o h ↔ p ∧ a ∈ o :=
begin
  cases o, dsimp [restrict, mem_eq], split,
  { rintro ⟨h₀, h₁⟩, exact ⟨h₀, ⟨_, h₁⟩⟩ },
  rintro ⟨h₀, h₁, h₂⟩, exact ⟨h₀, h₂⟩
end

/-- `unwrap o` gets the value at `o`, ignoring the condition. This function is unsound. -/
meta def unwrap (o : part α) : α := o.get undefined

theorem assert_defined {p : Prop} {f : p → part α} :
  ∀ (h : p), (f h).dom → (assert p f).dom := exists.intro

theorem bind_defined {f : part α} {g : α → part β} :
  ∀ (h : f.dom), (g (f.get h)).dom → (f.bind g).dom := assert_defined

@[simp] theorem bind_dom {f : part α} {g : α → part β} :
  (f.bind g).dom ↔ ∃ h : f.dom, (g (f.get h)).dom := iff.rfl

end part
