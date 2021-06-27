/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.W

/-!
# Polynomial functors

This file defines polynomial functors and the W-type construction as a
polynomial functor.  (For the M-type construction, see
pfunctor/M.lean.)
-/

universe u

/--
A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P.obj α`, which is defined as the sigma type `Σ x, P.B x → α`.

An element of `P.obj α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/

structure pfunctor :=
(A : Type u) (B : A → Type u)

namespace pfunctor

instance : inhabited pfunctor :=
⟨⟨default _, default _⟩⟩

variables (P : pfunctor) {α β : Type u}

/-- Applying `P` to an object of `Type` -/
def obj (α : Type*) := Σ x : P.A, P.B x → α

/-- Applying `P` to a morphism of `Type` -/
def map {α β : Type*} (f : α → β) : P.obj α → P.obj β :=
λ ⟨a, g⟩, ⟨a, f ∘ g⟩

instance obj.inhabited [inhabited P.A] [inhabited α] : inhabited (P.obj α) :=
⟨ ⟨ default _, λ _, default _ ⟩ ⟩
instance : functor P.obj := {map := @map P}

protected theorem map_eq {α β : Type*} (f : α → β) (a : P.A) (g : P.B a → α) :
  @functor.map P.obj _ _ _ f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
rfl

protected theorem id_map {α : Type*} : ∀ x : P.obj α, id <$> x = id x :=
λ ⟨a, b⟩, rfl

protected theorem comp_map {α β γ : Type*} (f : α → β) (g : β → γ) :
  ∀ x : P.obj α, (g ∘ f) <$> x = g <$> (f <$> x) :=
λ ⟨a, b⟩, rfl

instance : is_lawful_functor P.obj :=
{id_map := @pfunctor.id_map P, comp_map := @pfunctor.comp_map P}

/-- re-export existing definition of W-types and
adapt it to a packaged definition of polynomial functor -/
def W := _root_.W_type P.B

/- inhabitants of W types is awkward to encode as an instance
assumption because there needs to be a value `a : P.A`
such that `P.B a` is empty to yield a finite tree -/
attribute [nolint has_inhabited_instance] W
variables {P}

/-- root element  of a W tree -/
def W.head : W P → P.A
| ⟨a, f⟩ := a

/-- children of the root of a W tree -/
def W.children : Π x : W P, P.B (W.head x) → W P
| ⟨a, f⟩ := f

/-- destructor for W-types -/
def W.dest : W P → P.obj (W P)
| ⟨a, f⟩ := ⟨a, f⟩

/-- constructor for W-types -/
def W.mk : P.obj (W P) → W P
| ⟨a, f⟩ := ⟨a, f⟩

@[simp] theorem W.dest_mk (p : P.obj (W P)) : W.dest (W.mk p) = p :=
by cases p; reflexivity

@[simp] theorem W.mk_dest (p : W P) : W.mk (W.dest p) = p :=
by cases p; reflexivity

variables (P)

/-- `Idx` identifies a location inside the application of a pfunctor.
For `F : pfunctor`, `x : F.obj α` and `i : F.Idx`, `i` can designate
one part of `x` or is invalid, if `i.1 ≠ x.1` -/
def Idx := Σ x : P.A, P.B x

instance Idx.inhabited [inhabited P.A] [inhabited (P.B (default _))] : inhabited P.Idx :=
⟨ ⟨default _, default _⟩ ⟩

variables {P}

/-- `x.iget i` takes the component of `x` designated by `i` if any is or returns
a default value -/
def obj.iget [decidable_eq P.A] {α} [inhabited α] (x : P.obj α) (i : P.Idx) : α :=
if h : i.1 = x.1
  then x.2 (cast (congr_arg _ h) i.2)
  else default _

@[simp]
lemma fst_map {α β : Type u} (x : P.obj α) (f : α → β) :
  (f <$> x).1 = x.1 := by { cases x; refl }

@[simp]
lemma iget_map [decidable_eq P.A] {α β : Type u} [inhabited α] [inhabited β]
  (x : P.obj α) (f : α → β) (i : P.Idx)
  (h : i.1 = x.1) :
  (f <$> x).iget i = f (x.iget i) :=
by { simp only [obj.iget, fst_map, *, dif_pos, eq_self_iff_true],
     cases x, refl }

end pfunctor

/-
Composition of polynomial functors.
-/

namespace pfunctor

/-- functor composition for polynomial functors -/
def comp (P₂ P₁ : pfunctor.{u}) : pfunctor.{u} :=
⟨ Σ a₂ : P₂.1, P₂.2 a₂ → P₁.1,
  λ a₂a₁, Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u) ⟩

/-- constructor for composition -/
def comp.mk (P₂ P₁ : pfunctor.{u}) {α : Type} (x : P₂.obj (P₁.obj α)) : (comp P₂ P₁).obj α :=
⟨ ⟨ x.1, sigma.fst ∘ x.2 ⟩, λ a₂a₁, (x.2 a₂a₁.1).2 a₂a₁.2  ⟩

/-- destructor for composition -/
def comp.get (P₂ P₁ : pfunctor.{u}) {α : Type} (x : (comp P₂ P₁).obj α) : P₂.obj (P₁.obj α) :=
⟨ x.1.1, λ a₂, ⟨x.1.2 a₂, λ a₁, x.2 ⟨a₂,a₁⟩ ⟩ ⟩

end pfunctor

/-
Lifting predicates and relations.
-/

namespace pfunctor
variables {P : pfunctor.{u}}
open functor

theorem liftp_iff {α : Type u} (p : α → Prop) (x : P.obj α) :
  liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i, p (f i) :=
begin
  split,
  { rintros ⟨y, hy⟩, cases h : y with a f,
    refine ⟨a, λ i, (f i).val, _, λ i, (f i).property⟩,
    rw [←hy, h, pfunctor.map_eq] },
  rintros ⟨a, f, xeq, pf⟩,
  use ⟨a, λ i, ⟨f i, pf i⟩⟩,
  rw [xeq], reflexivity
end

theorem liftp_iff' {α : Type u} (p : α → Prop) (a : P.A) (f : P.B a → α) :
  @liftp.{u} P.obj _ α p ⟨a,f⟩ ↔ ∀ i, p (f i) :=
begin
  simp only [liftp_iff, sigma.mk.inj_iff]; split; intro,
  { casesm* [Exists _, _ ∧ _], subst_vars, assumption },
  repeat { constructor <|> assumption }
end

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : P.obj α) :
  liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) :=
begin
  split,
  { rintros ⟨u, xeq, yeq⟩, cases h : u with a f,
    use [a, λ i, (f i).val.fst, λ i, (f i).val.snd],
    split, { rw [←xeq, h], refl },
    split, { rw [←yeq, h], refl },
    intro i, exact (f i).property },
  rintros ⟨a, f₀, f₁, xeq, yeq, h⟩,
  use ⟨a, λ i, ⟨(f₀ i, f₁ i), h i⟩⟩,
  split,
  { rw [xeq], refl },
  rw [yeq], refl
end

open set

theorem supp_eq {α : Type u} (a : P.A) (f : P.B a → α) :
  @supp.{u} P.obj _ α  (⟨a,f⟩ : P.obj α) = f '' univ :=
begin
  ext, simp only [supp, image_univ, mem_range, mem_set_of_eq],
  split; intro h,
  { apply @h (λ x, ∃ (y : P.B a), f y = x),
    rw liftp_iff', intro, refine ⟨_,rfl⟩ },
  { simp only [liftp_iff'], cases h, subst x,
    tauto }
end

end pfunctor
