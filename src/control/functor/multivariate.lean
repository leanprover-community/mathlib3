/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
import data.fin2
import logic.function.basic
import tactic.basic

/-!

Tuples of types, and their categorical structure.

Features:

`typevec n`   : n-tuples of types
`α ⟹ β`      : n-tuples of maps
`f ⊚ g`       : composition
`mvfunctor n` : the type class of multivariate functors
`f <$$> x`    : notation for map

Also, support functions for operating with n-tuples of types, such as:

`append1 α β`    : append type `β` to n-tuple `α` to obtain an (n+1)-tuple
`drop α`         : drops the last element of an (n+1)-tuple
`last α`         : returns the last element of an (n+1)-tuple
`append_fun f g` : appends a function g to an n-tuple of functions
`drop_fun f`     : drops the last function from an n+1-tuple
`last_fun f`     : returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.
-/

universes u v w


/--
n-tuples of sorts, as a category
-/
def ptypevec (n : ℕ) := fin2 n → Sort*

/-- like `ptypevec` but in `Type*` -/
def typevec (n : ℕ) := ptypevec.{u+1} n

instance {n} : inhabited (ptypevec.{u} n) := ⟨ λ _, punit ⟩
instance {n} : inhabited (typevec.{u} n) := ⟨ λ _, punit ⟩

namespace typevec

variable {n : ℕ}

/-- arrow in the category of `ptypevec` -/
def arrow (α β : ptypevec n) := Π i : fin2 n, α i → β i

infixl ` ⟹ `:40 := arrow

instance arrow.inhabited (α β : ptypevec n) [Π i, inhabited (β i)] : inhabited (α ⟹ β) :=
⟨ λ _ _, default _ ⟩

/-- identity of arrow composition -/
def id {α : typevec n} : α ⟹ α := λ i x, x

/-- arrow composition in the category of `typevec` -/
def comp {α β γ : typevec n} (g : β ⟹ γ) (f : α ⟹ β) : α ⟹ γ :=
λ i x, g i (f i x)

infixr ` ⊚ `:80 := typevec.comp   -- type as \oo

@[simp] theorem id_comp {α β : typevec n} (f : α ⟹ β) : id ⊚ f = f :=
rfl

@[simp] theorem comp_id {α β : typevec n} (f : α ⟹ β) : f ⊚ id = f :=
rfl

theorem comp_assoc {α β γ δ : typevec n} (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) :
  (h ⊚ g) ⊚ f = h ⊚ g ⊚ f := rfl

end typevec

/-- multivariate functors, i.e. functor between the category of type vectors
and the category of Type -/
class mvfunctor {n : ℕ} (F : typevec n → Type*) :=
(map : Π {α β : typevec n}, (α ⟹ β) → (F α → F β))

infixr ` <$$> `:100 := mvfunctor.map

namespace mvfunctor

variables {n : ℕ} {α β γ : typevec.{u} n} {F : typevec.{u} n → Type v} [mvfunctor F]

/-- predicate lifting over multivariate functors -/
def liftp {α : typevec n} (p : Π i, α i → Prop) (x : F α) : Prop :=
∃ u : F (λ i, subtype (p i)), (λ i, @subtype.val _ (p i)) <$$> u = x

/-- relational lifting over multivariate functors -/
def liftr {α : typevec n} (r : Π {i}, α i → α i → Prop) (x y : F α) : Prop :=
∃ u : F (λ i, {p : α i × α i // r p.fst p.snd}),
  (λ i (t : {p : α i × α i // r p.fst p.snd}), t.val.fst) <$$> u = x ∧
  (λ i (t : {p : α i × α i // r p.fst p.snd}), t.val.snd) <$$> u = y

/-- given `x : F α` and a projection `i` of type vector `α`, `supp x i` is the set
of `α.i` contained in `x` -/
def supp {α : typevec n} (x : F α) (i : fin2 n) : set (α i) :=
{ y : α i | ∀ {p}, liftp p x → p i y }

theorem of_mem_supp {α : typevec n} {x : F α} {p : Π ⦃i⦄, α i → Prop} (h : liftp p x) (i : fin2 n):
  ∀ y ∈ supp x i, p y :=
λ y hy, hy h

end mvfunctor

/-- laws for `mvfunctor` -/
class is_lawful_mvfunctor {n : ℕ} (F : typevec n → Type*) [mvfunctor F] : Prop :=
(id_map       : Π {α : typevec n} (x : F α), typevec.id <$$> x = x)
(comp_map     : Π {α β γ : typevec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α),
                    (h ⊚ g) <$$> x = h <$$> g <$$> x)

namespace mvfunctor

export is_lawful_mvfunctor (comp_map)
open is_lawful_mvfunctor

variables {n : ℕ} {α β γ : typevec.{u} n}
variables {F : typevec.{u} n → Type v} [mvfunctor F] [is_lawful_mvfunctor F]

@[simp]
lemma id_map (x : F α) :
  typevec.id <$$> x = x :=
id_map x

@[simp]
lemma id_map' (x : F α) :
  (λ i a, a) <$$> x = x :=
id_map x

lemma map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) :
  h <$$> g <$$> x = (h ⊚ g) <$$> x :=
eq.symm $ comp_map _ _ _

end mvfunctor

namespace eq

theorem mp_mpr {α β : Type*} (h : α = β) (x : β) :
  eq.mp h (eq.mpr h x) = x :=
by induction h; reflexivity

theorem mpr_mp {α β : Type*} (h : α = β) (x : α) :
  eq.mpr h (eq.mp h x) = x :=
by induction h; reflexivity

end eq

namespace typevec

variable {n : ℕ}

/--
Support for extending a typevec by one element.
-/
def append1 (α : typevec n) (β : Type*) : typevec (n+1)
| (fin2.fs i) := α i
| fin2.fz      := β

infixl ` ::: `:67 := append1

/-- retain only a `n-length` prefix of the argument -/
def drop (α : typevec (n+1)) : typevec n := λ i, α i.fs

/-- take the last value of a `(n+1)-length` vector -/
def last (α : typevec (n+1)) : Type* := α fin2.fz

instance last.inhabited (α : typevec (n+1)) [inhabited (α fin2.fz)] : inhabited (last α) :=
⟨ (default (α fin2.fz) : α fin2.fz) ⟩

theorem drop_append1 {α : typevec n} {β : Type*} {i : fin2 n} : drop (append1 α β) i = α i := rfl

theorem drop_append1' {α : typevec n} {β : Type*} : drop (append1 α β) = α :=
by ext; apply drop_append1

theorem last_append1 {α : typevec n} {β : Type*} : last (append1 α β) = β := rfl

@[simp]
theorem append1_drop_last (α : typevec (n+1)) : append1 (drop α) (last α) = α :=
funext $ λ i, by cases i; refl

/-- cases on `(n+1)-length` vectors -/
@[elab_as_eliminator] def append1_cases
  {C : typevec (n+1) → Sort u} (H : ∀ α β, C (append1 α β)) (γ) : C γ :=
by rw [← @append1_drop_last _ γ]; apply H

@[simp] theorem append1_cases_append1 {C : typevec (n+1) → Sort u}
  (H : ∀ α β, C (append1 α β)) (α β) :
  @append1_cases _ C H (append1 α β) = H α β := rfl

/-- append an arrow and a function for arbitrary source and target
type vectors -/
def split_fun {α α' : ptypevec (n+1)}
  (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α'
| (fin2.fs i) := f i
| fin2.fz      := g

/-- append an arrow and a function as well as their respective source
and target types / typevecs -/
def append_fun {α α' : ptypevec n} {β β' : Type*}
  (f : α ⟹ α') (g : β → β') : append1 α β ⟹ append1 α' β' := split_fun f g

infixl ` ::: ` := append_fun

/-- split off the prefix of an arrow -/
def drop_fun {α β : typevec (n+1)} (f : α ⟹ β) : drop α ⟹ drop β :=
λ i, f i.fs

/-- split off the last function of an arrow -/
def last_fun {α β : typevec (n+1)} (f : α ⟹ β) : last α → last β :=
f fin2.fz

/-- arrow in the category of `0-length` vectors -/
def nil_fun {α : typevec 0} {β : typevec 0} : α ⟹ β :=
λ i, fin2.elim0 i

theorem eq_of_drop_last_eq {α β : typevec (n+1)} {f g : α ⟹ β}
  (h₀ : ∀ j, drop_fun f j = drop_fun g j) (h₁ : last_fun f = last_fun g) : f = g :=
by ext1 (ieq | ⟨j, ieq⟩); apply_assumption

@[simp] theorem drop_fun_split_fun {α α' : typevec (n+1)}
  (f : drop α ⟹ drop α') (g : last α → last α') :
  drop_fun (split_fun f g) = f := rfl

/-- turn an equality into an arrow -/
def arrow.mp {α β : typevec n} (h : α = β) : α ⟹ β
| i := eq.mp (congr_fun h _)

/-- turn an equality into an arrow, with reverse direction -/
def arrow.mpr {α β : typevec n} (h : α = β) : β ⟹ α
| i := eq.mpr (congr_fun h _)

/-- decompose a vector into its prefix appended with its last element -/
def to_append1_drop_last {α : typevec (n+1)} : α ⟹ drop α ::: last α :=
arrow.mpr (append1_drop_last _)

@[simp] theorem last_fun_split_fun {α α' : typevec (n+1)}
  (f : drop α ⟹ drop α') (g : last α → last α') :
  last_fun (split_fun f g) = g := rfl

@[simp] theorem drop_fun_append_fun {α α' : typevec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
  drop_fun (f ::: g) = f := rfl

@[simp] theorem last_fun_append_fun {α α' : typevec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
  last_fun (f ::: g) = g := rfl

theorem split_drop_fun_last_fun {α α' : typevec (n+1)} (f : α ⟹ α') :
  split_fun (drop_fun f) (last_fun f) = f :=
eq_of_drop_last_eq (λ _, rfl) rfl

theorem split_fun_inj
  {α α' : typevec (n+1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
  (H : split_fun f g = split_fun f' g') : f = f' ∧ g = g' :=
by rw [← drop_fun_split_fun f g, H, ← last_fun_split_fun f g, H]; simp

theorem append_fun_inj {α α' : typevec n} {β β' : Type*} {f f' : α ⟹ α'} {g g' : β → β'} :
  f ::: g = f' ::: g' →  f = f' ∧ g = g' :=
split_fun_inj

theorem split_fun_comp {α₀ α₁ α₂ : typevec (n+1)}
    (f₀ : drop α₀ ⟹ drop α₁) (f₁ : drop α₁ ⟹ drop α₂)
    (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
  split_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) = split_fun f₁ g₁ ⊚ split_fun f₀ g₀ :=
eq_of_drop_last_eq (λ _, rfl) rfl

theorem append_fun_comp_split_fun
  {α γ : typevec n} {β δ : Type*} {ε : typevec (n + 1)}
    (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ)
    (g₀ : last ε → β) (g₁ : β → δ) :
  append_fun f₁ g₁ ⊚ split_fun f₀ g₀ = split_fun (f₁ ⊚ f₀) (g₁ ∘ g₀) :=
(split_fun_comp _ _ _ _).symm

lemma append_fun_comp {α₀ α₁ α₂ : typevec n} {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  f₁ ⊚ f₀ ::: g₁ ∘ g₀ = (f₁ ::: g₁) ⊚ (f₀ ::: g₀) :=
eq_of_drop_last_eq (λ _, rfl) rfl

lemma append_fun_comp' {α₀ α₁ α₂ : typevec n} {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = f₁ ⊚ f₀ ::: g₁ ∘ g₀ :=
eq_of_drop_last_eq (λ _, rfl) rfl

lemma nil_fun_comp {α₀ : typevec 0} (f₀ : α₀ ⟹ fin2.elim0) : nil_fun ⊚ f₀ = f₀ :=
funext $ λ x, fin2.elim0 x

theorem append_fun_comp_id {α : typevec n} {β₀ β₁ β₂ : Type*}
    (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
  @id _ α ::: g₁ ∘ g₀ = (id ::: g₁) ⊚ (id ::: g₀) :=
eq_of_drop_last_eq (λ _, rfl) rfl

@[simp]
theorem drop_fun_comp {α₀ α₁ α₂ : typevec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
  drop_fun (f₁ ⊚ f₀) = drop_fun f₁ ⊚ drop_fun f₀ := rfl

@[simp]
theorem last_fun_comp {α₀ α₁ α₂ : typevec (n+1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
  last_fun (f₁ ⊚ f₀) = last_fun f₁ ∘ last_fun f₀ := rfl

theorem append_fun_aux {α α' : typevec n} {β β' : Type*}
  (f : α ::: β ⟹ α' ::: β') : drop_fun f ::: last_fun f = f :=
eq_of_drop_last_eq (λ _, rfl) rfl

theorem append_fun_id_id {α : typevec n} {β : Type*} :
  @id n α ::: @_root_.id β = id :=
eq_of_drop_last_eq (λ _, rfl) rfl

instance subsingleton0 : subsingleton (typevec 0) :=
⟨ λ a b, funext $ λ a, fin2.elim0 a  ⟩

run_cmd do
  mk_simp_attr `typevec,
  tactic.add_doc_string `simp_attr.typevec
"simp set for the manipulation of typevec and arrow expressions"

local prefix `♯`:0 := cast (by try { simp }; congr' 1; try { simp })

/-- cases distinction for 0-length type vector -/
def typevec_cases_nil {β : typevec 0 → Sort*} (f : β fin2.elim0) :
  Π v, β v :=
λ v, ♯ f

/-- cases distinction for (n+1)-length type vector -/
def typevec_cases_cons (n : ℕ) {β : typevec (n+1) → Sort*} (f : Π t (v : typevec n), β (v ::: t)) :
  Π v, β v :=
λ v, ♯ f v.last v.drop

lemma typevec_cases_nil_append1 {β : typevec 0 → Sort*} (f : β fin2.elim0) :
  typevec_cases_nil f fin2.elim0 = f := rfl

lemma typevec_cases_cons_append1 (n : ℕ) {β : typevec (n+1) → Sort*}
      (f : Π t (v : typevec n), β (v ::: t))
      (v : typevec n) (α) :
  typevec_cases_cons n f (v ::: α) = f α v := rfl

open typevec

/-- cases distinction for an arrow in the category of 0-length type vectors -/
def typevec_cases_nil₃ {β : Π v v' : typevec 0, v ⟹ v' → Sort*} (f : β fin2.elim0 fin2.elim0 nil_fun) :
  Π v v' fs, β v v' fs :=
λ v v' fs,
begin
  refine cast _ f; congr' 1; ext; try { intros; casesm fin2 0 }, refl
end

/-- cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevec_cases_cons₃ (n : ℕ) {β : Π v v' : typevec (n+1), v ⟹ v' → Sort*}
  (F : Π t t' (f : t → t') (v v' : typevec n) (fs : v ⟹ v'), β (v ::: t) (v' ::: t') (fs ::: f)) :
  Π v v' fs, β v v' fs :=
begin
  intros v v',
  rw [←append1_drop_last v, ←append1_drop_last v'],
  intro fs,
  rw [←split_drop_fun_last_fun fs],
  apply F
end

/-- specialized cases distinction for an arrow in the category of 0-length type vectors -/
def typevec_cases_nil₂ {β : fin2.elim0 ⟹ fin2.elim0 → Sort*}
  (f : β nil_fun) :
  Π f, β f :=
begin
  intro g, have : g = nil_fun, ext ⟨ ⟩,
  rw this, exact f
end

/-- specialized cases distinction for an arrow in the category of (n+1)-length type vectors -/
def typevec_cases_cons₂ (n : ℕ) (t t' : Type*) (v v' : typevec (n)) {β : (v ::: t) ⟹ (v' ::: t') → Sort*}
  (F : Π (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) :
  Π fs, β fs :=
begin
  intro fs,
  rw [←split_drop_fun_last_fun fs],
  apply F
end

lemma typevec_cases_nil₂_append_fun {β : fin2.elim0 ⟹ fin2.elim0 → Sort*}
  (f : β nil_fun) :
  typevec_cases_nil₂ f nil_fun = f := rfl

lemma typevec_cases_cons₂_append_fun (n : ℕ) (t t' : Type*) (v v' : typevec (n)) {β : (v ::: t) ⟹ (v' ::: t') → Sort*}
  (F : Π (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) (f fs) :
  typevec_cases_cons₂ n t t' v v' F (fs ::: f) = F f fs := rfl


/- for lifting predicates and relations -/

/-- `pred_last α p x` predicates `p` of the last element of `x : α.append1 β`. -/
def pred_last (α : typevec n) {β : Type*} (p : β → Prop) : Π ⦃i⦄, (α.append1 β) i → Prop
| (fin2.fs i) := λ x, true
| fin2.fz      := p

/-- `rel_last α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r` and all the other elements are equal. -/
def rel_last (α : typevec n) {β γ : Type*} (r : β → γ → Prop) :
  Π ⦃i⦄, (α.append1 β) i → (α.append1 γ) i → Prop
| (fin2.fs i) := eq
| fin2.fz      := r

section liftp'
open nat

/-- `repeat n t` is a `n-length` type vector that contains `n` occurences of `t` -/
def repeat : Π (n : ℕ) (t : Sort*), typevec n
| 0 t := fin2.elim0
| (nat.succ i) t := append1 (repeat i t) t

/-- `prod α β` is the pointwise product of the components of `α` and `β` -/
def prod : Π {n} (α β : typevec.{u} n), typevec n
| 0 α β := fin2.elim0
| (succ n) α β := prod (drop α) (drop β) ::: (last α × last β)

infix ` ⊗ `:45 := prod

/-- `const x α` is an arrow that ignores its source and constructs a `typevec` that
contains nothing but `x` -/
protected def const {β} (x : β) : Π {n} (α : typevec n), α ⟹ repeat _ β
| (succ n) α (fin2.fs i) := const (drop α) _
| (succ n) α fin2.fz := λ _, x

open function (uncurry)

/-- vector of equality on a product of vectors -/
def repeat_eq : Π {n} (α : typevec n), α ⊗ α ⟹ repeat _ Prop
| 0 α := nil_fun
| (succ n) α := repeat_eq (drop α) ::: uncurry eq
-- | (succ n) α (fin2.fs i) := repeat_eq (drop α) _
-- | (succ n) α fin2.fz := λ x, x.1 = x.2

lemma const_append1 {β γ} (x : γ) {n} (α : typevec n) : typevec.const x (α ::: β) = append_fun (typevec.const x α) (λ _, x) :=
by ext i : 1; cases i; refl

lemma eq_nil_fun {α β : typevec 0} (f : α ⟹ β) : f = nil_fun :=
by ext x; cases x

lemma id_eq_nil_fun {α : typevec 0} : @id _ α = nil_fun :=
by ext x; cases x

lemma const_nil {β} (x : β) (α : typevec 0) : typevec.const x α = nil_fun :=
by ext i : 1; cases i; refl

@[typevec]
lemma repeat_eq_append1 {β} {n} (α : typevec n) : repeat_eq (α ::: β) = split_fun (repeat_eq α) (uncurry eq) :=
by induction n; refl

@[typevec]
lemma repeat_eq_nil (α : typevec 0) : repeat_eq α = nil_fun :=
by ext i : 1; cases i; refl

/-- predicate on a type vector to constrain only the last object -/
def pred_last' (α : typevec n) {β : Type*} (p : β → Prop) : α ::: β ⟹ repeat (n+1) Prop :=
split_fun (typevec.const true α) p

/-- predicate on the product of two type vectors to constrain only their last object -/
def rel_last' (α : typevec n) {β : Type*} (p : β → β → Prop) : (α ::: β ⊗ α ::: β) ⟹ repeat (n+1) Prop :=
split_fun (repeat_eq α) (uncurry p)

/-- given `F : typevec.{u} (n+1) → Type u`, `curry F : Type u → typevec.{u} → Type u`,
i.e. its first argument can be fed in separately from the rest of the vector of arguments -/
def curry (F : typevec.{u} (n+1) → Type*) (α : Type u) (β : typevec.{u} n) : Type* :=
F (β ::: α)

instance curry.inhabited (F : typevec.{u} (n+1) → Type*) (α : Type u) (β : typevec.{u} n)
  [I : inhabited (F $ β ::: α)]:
  inhabited (curry F α β) := I

/-- arrow to remove one element of a `repeat` vector -/
def drop_repeat (α : Type*) : Π {n}, drop (repeat (succ n) α) ⟹ repeat n α
| (succ n) (fin2.fs i) := drop_repeat i
| (succ n) fin2.fz := _root_.id

-- This definition bypasses the equation compiler to make sure we
-- recurse on the `fin2 n` argument and not the `ℕ` argument. This
-- matters because of how definitional equality is used with
-- `of_repeat`
/-- projection for a repeat vector -/
def of_repeat {α : Sort*} : Π {n i}, repeat n α i → α
| ._ fin2.fz := _root_.id
| ._ (fin2.fs i) := @of_repeat _ i

-- begin
--   induction i with n i IH,
--   { exact _root_.id }
--   { exact IH },
-- end

lemma const_iff_true {α : typevec n} {i x p} : of_repeat (typevec.const p α i x) ↔ p :=
by induction i; [refl, erw [typevec.const,@i_ih (drop α) x]]

variables  {F : typevec.{u} n → Type*} [mvfunctor F] {α β γ : typevec.{u} n}
variables (p : α ⟹ repeat n Prop) (r : α ⊗ α ⟹ repeat n Prop)

/-- left projection of a `prod` vector -/
def prod.fst : Π {n} {α β : typevec.{u} n}, α ⊗ β ⟹ α
| (succ n) α β (fin2.fs i) := @prod.fst _ (drop α) (drop β) i
| (succ n) α β fin2.fz := _root_.prod.fst

/-- right projection of a `prod` vector -/
def prod.snd : Π {n} {α β : typevec.{u} n}, α ⊗ β ⟹ β
| (succ n) α β (fin2.fs i) := @prod.snd _ (drop α) (drop β) i
| (succ n) α β fin2.fz := _root_.prod.snd

/-- introduce a product where both components are the same -/
def prod.diag : Π {n} {α : typevec.{u} n}, α ⟹ α ⊗ α
| (succ n) α (fin2.fs i) x := @prod.diag _ (drop α) _ x
| (succ n) α fin2.fz x := (x,x)

/-- constructor for `prod` -/
def prod.mk : Π {n} {α β : typevec.{u} n} (i : fin2 n), α i → β i → (α ⊗ β) i
| (succ n) α β (fin2.fs i) := prod.mk i
| (succ n) α β fin2.fz := _root_.prod.mk

/-- `prod` is functorial -/
def prod.map : Π {n} {α α' β β' : typevec.{u} n}, (α ⟹ β) → (α' ⟹ β') → α ⊗ α' ⟹ β ⊗ β'
| (succ n) α α' β β' x y (fin2.fs i) a := @prod.map _ (drop α) (drop α') (drop β) (drop β') (drop_fun x) (drop_fun y) _ a
| (succ n) α α' β β' x y fin2.fz a := (x _ a.1,y _ a.2)

infix ` ⊗ `:45 := prod.map

theorem fst_prod_mk {α α' β β' : typevec n} (f : α ⟹ β) (g : α' ⟹ β') :
  typevec.prod.fst ⊚ (f ⊗ g) = f ⊚ typevec.prod.fst :=
by ext i; induction i; [refl, apply i_ih]

theorem snd_prod_mk {α α' β β' : typevec n} (f : α ⟹ β) (g : α' ⟹ β') :
  typevec.prod.snd ⊚ (f ⊗ g) = g ⊚ typevec.prod.snd :=
by ext i; induction i; [refl, apply i_ih]

theorem fst_diag {α : typevec n} : typevec.prod.fst ⊚ (prod.diag : α ⟹ _) = id :=
by ext i; induction i; [refl, apply i_ih]

theorem snd_diag {α : typevec n} : typevec.prod.snd ⊚ (prod.diag : α ⟹ _) = id :=
by ext i; induction i; [refl, apply i_ih]

lemma repeat_eq_iff_eq {α : typevec n} {i x y} : of_repeat (repeat_eq α i (prod.mk _ x y)) ↔ x = y :=
by induction i; [refl, erw [repeat_eq,@i_ih (drop α) x y]]

-- -- This definition bypasses the equation compiler to make sure we
-- -- recurse on the `fin2 n` argument and not the `ℕ` argument. This
-- -- matters because of how definitional equality is used with
-- -- `subtype_`
-- def subtype_ {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop) : typevec n :=
-- λ i, begin
--   induction i with _ n i IH generalizing α p,
--   { exact _root_.subtype (λ x, p fin2.fz x) },
--   { exact @IH (drop α) (drop_fun p) },
-- end

/-- given a predicate vector `p` over vector `α`, `subtype_ p` is the type of vectors
that contain an `α` that satisfies `p` -/
def subtype_ : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), typevec n
| ._ α p fin2.fz := _root_.subtype (λ x, p fin2.fz x)
| ._ α p (fin2.fs i) := subtype_ (drop_fun p) i

-- def subtype_val : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), subtype_ p ⟹ α :=
-- by intros n α p i; induction i; [exact _root_.subtype.val, apply i_ih (drop_fun p)]

/-- projection on `subtype_` -/
def subtype_val : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), subtype_ p ⟹ α
| (succ n) α p (fin2.fs i) := @subtype_val n _ _ i
| (succ n) α p fin2.fz := _root_.subtype.val

/-- arrow that rearranges the type of `subtype_` to turn a subtype of vector into
a vector of subtypes -/
def to_subtype : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), (λ (i : fin2 n), { x // of_repeat $ p i x }) ⟹ subtype_ p
| (succ n) α p (fin2.fs i) x := to_subtype (drop_fun p) i x
| (succ n) α p fin2.fz x := x

/-- arrow that rearranges the type of `subtype_` to turn a vector of subtypes
into a subtype of vector -/
def of_subtype : Π {n} {α : typevec.{u} n} (p : α ⟹ repeat n Prop), subtype_ p ⟹ (λ (i : fin2 n), { x // of_repeat $ p i x })
| (succ n) α p (fin2.fs i) x := of_subtype _ i x
| (succ n) α p fin2.fz x := x


-- def to_subtype' : Π {n} {α : typevec.{u} n} (p : α ⊗ α ⟹ repeat n Prop), (λ (i : fin2 n), { x : α i × α i // of_repeat $ p i (prod.mk _ x.1 x.2) }) ⟹ subtype_ p :=
-- by {
--   intros n α p i x,
--   induction i,
--   { exact ⟨x.val,cast (by congr; simp [prod.mk]) x.property⟩ },
--   { exact i_ih (drop_fun p) x } }

-- @[simp]
-- lemma to_subtype'_eqn_1 {n} {α : typevec.{u} (succ n)} (p : α ⊗ α ⟹ repeat (succ n) Prop) (x) :
--   to_subtype' p fin2.fz x = ⟨x.val,cast (by congr; simp [prod.mk]) x.property⟩ := rfl

-- @[simp]
-- lemma to_subtype'_eqn_2 {n} {α : typevec.{u} (succ n)} (p : α ⊗ α ⟹ repeat (succ n) Prop) (i : fin2 n) (x) :
--   to_subtype' p (fin2.fs i) x = @to_subtype' n _ (drop_fun p) _ x := rfl

/-- similar to `to_subtype` adapted to relations (i.e. predicate on product) -/
def to_subtype' : Π {n} {α : typevec.{u} n} (p : α ⊗ α ⟹ repeat n Prop), (λ (i : fin2 n), { x : α i × α i // of_repeat $ p i (prod.mk _ x.1 x.2) }) ⟹ subtype_ p
| (succ n) α p (fin2.fs i) x := to_subtype' (drop_fun p) i x
| (succ n) α p fin2.fz x := ⟨x.val,cast (by congr; simp [prod.mk]) x.property⟩

-- def of_subtype' : Π {n} {α : typevec.{u} n} (p : α ⊗ α ⟹ repeat n Prop), subtype_ p ⟹ (λ (i : fin2 n), { x : α i × α i // of_repeat $ p i (prod.mk _ x.1 x.2) }) :=
-- by {
--   intros n α p i x,
--   induction i,
--   { exact ⟨x.val,cast (by congr; simp [prod.mk]) x.property⟩, },
--   { apply i_ih (drop_fun p) x }, }

-- @[simp]
-- lemma of_subtype'_eqn_1 {n} {α : typevec.{u} (succ n)} (p : α ⊗ α ⟹ repeat (succ n) Prop) (x) :
--   of_subtype' p fin2.fz x = ⟨x.val,cast (by congr; simp [prod.mk]) x.property⟩ := rfl

-- @[simp]
-- lemma of_subtype'_eqn_2 {n} {α : typevec.{u} (succ n)} (p : α ⊗ α ⟹ repeat (succ n) Prop) (i : fin2 n) (x) :
--   of_subtype' p (fin2.fs i) x = @of_subtype' n _ (drop_fun p) _ x := rfl

/-- similar to `of_subtype` adapted to relations (i.e. predicate on product) -/
def of_subtype' : Π {n} {α : typevec.{u} n} (p : α ⊗ α ⟹ repeat n Prop), subtype_ p ⟹ (λ (i : fin2 n), { x : α i × α i // of_repeat $ p i (prod.mk _ x.1 x.2) })
| ._ α p (fin2.fs i) x := of_subtype' _ i x
| ._ α p fin2.fz x := ⟨x.val,cast (by congr; simp [prod.mk]) x.property⟩

/-- similar to `diag` but the target vector is a `subtype_`
guaranteeing the equality of the components -/
def diag_sub  : Π {n} {α : typevec.{u} n}, α ⟹ subtype_ (repeat_eq α)
| (succ n) α (fin2.fs i) x := @diag_sub _ (drop α) _ x
| (succ n) α fin2.fz x := ⟨(x,x), rfl⟩

lemma subtype_val_nil {α : typevec.{u} 0} (ps : α ⟹ repeat 0 Prop) : typevec.subtype_val ps = nil_fun :=
funext $ by rintro ⟨ ⟩; refl

lemma diag_sub_val {n} {α : typevec.{u} n} :
  subtype_val (repeat_eq α) ⊚ diag_sub = prod.diag :=
by ext i; induction i; [refl, apply i_ih]

lemma prod_id : Π {n} {α β : typevec.{u} n}, (id ⊗ id) = (id : α ⊗ β ⟹ _) :=
begin
  intros, ext i a, induction i,
  { cases a, refl },
  { apply i_ih },
end

lemma append_prod_append_fun {n} {α α' β β' : typevec.{u} n}
  {φ φ' ψ ψ' : Type u}
  {f₀ : α ⟹ α'} {g₀ : β ⟹ β'}
  {f₁ : φ → φ'}  {g₁ : ψ → ψ'} :
  (f₀ ⊗ g₀) ::: _root_.prod.map f₁ g₁ = ((f₀ ::: f₁) ⊗ (g₀ ::: g₁)) :=
by ext i a; cases i; [cases a, skip]; refl

/-- adapt `mvfunctor.liftp` to accept predicates as arrows -/
def liftp' : F α → Prop :=
mvfunctor.liftp $ λ i x, of_repeat $ p i x

/-- adapt `mvfunctor.liftp` to accept relations as arrows -/
def liftr' : F α → F α → Prop :=
mvfunctor.liftr $ λ i x y, of_repeat $ r i $ prod.mk _ x y

/-- append an arrow whose target is `repeat n β` -/
def append_fun_to_repeat {α : ptypevec n} {β β' : Type*}
  (f : α ⟹ repeat n β') (g : β → β') : append1 α β ⟹ repeat n.succ β' := split_fun f g

variables [is_lawful_mvfunctor F] (F)

lemma exists_iff_exists_of_mono {p : F α → Prop} {q : F β → Prop} (f : α ⟹ β) (g : β ⟹ α)
  (h₀ : f ⊚ g = id)
  (h₁ : ∀ u : F α, p u ↔ q (f <$$> u)) :
  (∃ u : F α, p u) ↔ (∃ u : F β, q u) :=
begin
  split; rintro ⟨u,h₂⟩; [ use f <$$> u, use g <$$> u ],
  { apply (h₁ u).mp h₂ },
  { apply (h₁ _).mpr _,
    simp only [mvfunctor.map_map,h₀,is_lawful_mvfunctor.id_map,h₂] },
end
variables {F}


lemma liftp_def (x : F α) : liftp' p x ↔ ∃ u : F (subtype_ p), subtype_val p <$$> u = x :=
begin
  dsimp only [liftp', mvfunctor.liftp],
  apply exists_iff_exists_of_mono F (to_subtype p) (of_subtype p),
  { clear x _inst_2 _inst_1 F, dsimp only [comp],
    ext i x; induction i, { refl },
    -- Lean 3.11.0 problem
    rw [of_subtype,@to_subtype.equations._eqn_2 i_n _ p i_a,i_ih],
    refl, },
  { intro, rw [mvfunctor.map_map,(⊚)], congr',
    clear x u _inst_2 _inst_1 F, ext i ⟨ x,_ ⟩,
    induction i; dsimp only [to_subtype, subtype_val],
    { refl }, { apply i_ih }, }
end

lemma liftr_def (x y : F α) :
  liftr' r x y ↔
  ∃ u : F (subtype_ r), (prod.fst ⊚ subtype_val r) <$$> u = x ∧
                        (prod.snd ⊚ subtype_val r) <$$> u = y :=
begin
  dsimp only [liftr', mvfunctor.liftr],
  apply exists_iff_exists_of_mono F (to_subtype' r) (of_subtype' r),
  { clear x y _inst_2 _inst_1 F, dsimp only [comp],
    ext i x; induction i,
    { dsimp only [id], cases x, refl },
    -- Lean 3.11.0 problem
    { rw [of_subtype',@to_subtype'.equations._eqn_2 i_n _ r i_a, i_ih], refl } },
  { intro, rw [mvfunctor.map_map,(⊚),mvfunctor.map_map,(⊚)], congr';
    clear x y u _inst_2 _inst_1 F,
    { ext i ⟨ x,_ ⟩, induction i; dsimp only [subtype_val],
      { refl },
      apply i_ih, },
    { ext i ⟨x,_⟩,
      { induction i, { refl },
        { rw i_ih (drop_fun r), refl }, } } }
end

end liftp'

open nat

section liftp_last_pred_iff
variables  {F : typevec.{u} (n+1) → Type*} [mvfunctor F] [is_lawful_mvfunctor F]
           {α : typevec.{u} n}
variables (p : α ⟹ repeat n Prop)
          (r : α ⊗ α ⟹ repeat n Prop)

open mvfunctor

variables {β : Type u}
variables (pp : β → Prop)

private def f : Π (n α), (λ (i : fin2 (n + 1)), {p_1 // of_repeat (pred_last' α pp i p_1)}) ⟹
    λ (i : fin2 (n + 1)), {p_1 : (α ::: β) i // pred_last α pp p_1}
| _ α (fin2.fs i) x := ⟨ x.val, cast (by simp only [pred_last]; erw const_iff_true) x.property ⟩
| _ α fin2.fz x := ⟨ x.val, x.property ⟩

private def g : Π (n α), (λ (i : fin2 (n + 1)), {p_1 : (α ::: β) i // pred_last α pp p_1}) ⟹
    (λ (i : fin2 (n + 1)), {p_1 // of_repeat (pred_last' α pp i p_1)})
| _ α (fin2.fs i) x := ⟨ x.val, cast (by simp only [pred_last]; erw const_iff_true) x.property ⟩
| _ α fin2.fz x := ⟨ x.val, x.property ⟩

lemma liftp_last_pred_iff {β} (p : β → Prop) (x : F (α ::: β)) :
  liftp' (pred_last' _ p) x ↔ liftp (pred_last _ p) x :=
begin
  dsimp only [liftp,liftp'],
  apply exists_iff_exists_of_mono F (f _ n α) (g _ n α),
  { clear x _inst_2 _inst_1 F, ext i ⟨x,_⟩, cases i; refl },
  { intros, rw [mvfunctor.map_map,(⊚)],
    congr'; ext i ⟨x,_⟩; cases i; refl }
end

open function
variables (rr : β → β → Prop)

private def f : Π (n α), (λ (i : fin2 (n + 1)), {p_1 : _ × _ // of_repeat (rel_last' α rr i (prod.mk _ p_1.fst p_1.snd))}) ⟹
    λ (i : fin2 (n + 1)), {p_1 : (α ::: β) i × _ // rel_last α rr (p_1.fst) (p_1.snd)}
| _ α (fin2.fs i) x := ⟨ x.val, cast (by simp only [rel_last]; erw repeat_eq_iff_eq) x.property ⟩
| _ α fin2.fz x := ⟨ x.val, x.property ⟩

private def g : Π (n α), (λ (i : fin2 (n + 1)), {p_1 : (α ::: β) i × _ // rel_last α rr (p_1.fst) (p_1.snd)}) ⟹
    (λ (i : fin2 (n + 1)), {p_1 : _ × _ // of_repeat (rel_last' α rr i (prod.mk _ p_1.fst p_1.snd))})
| _ α (fin2.fs i) x := ⟨ x.val, cast (by simp only [rel_last]; erw repeat_eq_iff_eq) x.property ⟩
| _ α fin2.fz x := ⟨ x.val, x.property ⟩

lemma liftr_last_rel_iff  (x y : F (α ::: β)) :
  liftr' (rel_last' _ rr) x y ↔ liftr (rel_last _ rr) x y :=
begin
  dsimp only [liftr,liftr'],
  apply exists_iff_exists_of_mono F (f rr _ _) (g rr _ _),
  { clear x y _inst_2 _inst_1 F, ext i ⟨x,_⟩ : 2, cases i; refl, },
  { intros, rw [mvfunctor.map_map,mvfunctor.map_map,(⊚),(⊚)],
    congr'; ext i ⟨x,_⟩; cases i; refl }
end

end liftp_last_pred_iff

end typevec
