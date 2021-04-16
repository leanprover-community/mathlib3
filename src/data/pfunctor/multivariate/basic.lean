/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import control.functor.multivariate
import data.pfunctor.univariate
import data.sigma

/-!
# Multivariate polynomial functors.

Multivariate polynomial functors are used for defining M-types and W-types.
They map a type vector `α` to the type `Σ a : A, B a ⟹ α`, with `A : Type` and
`B : A → typevec n`. They interact well with Lean's inductive definitions because
they guarantee that occurrences of `α` are positive.
-/

universes u v
open_locale mvfunctor

/--
multivariate polynomial functors
-/
structure mvpfunctor (n : ℕ) :=
(A : Type.{u}) (B : A → typevec.{u} n)

namespace mvpfunctor
open mvfunctor (liftp liftr)

variables {n m : ℕ} (P : mvpfunctor.{u} n)

/-- Applying `P` to an object of `Type` -/
def obj (α : typevec.{u} n) : Type u := Σ a : P.A, P.B a ⟹ α

/-- Applying `P` to a morphism of `Type` -/
def map {α β : typevec n} (f : α ⟹ β) : P.obj α → P.obj β :=
λ ⟨a, g⟩, ⟨a, typevec.comp f g⟩

instance : inhabited (mvpfunctor n) :=
⟨ ⟨default _, λ _, default _⟩ ⟩

instance obj.inhabited {α : typevec n} [inhabited P.A] [Π i, inhabited (α i)] :
  inhabited (P.obj α) :=
⟨ ⟨default _, λ _ _, default _⟩ ⟩

instance : mvfunctor P.obj :=
⟨@mvpfunctor.map n P⟩

theorem map_eq {α β : typevec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α) :
  @mvfunctor.map _ P.obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩ :=
rfl

theorem id_map {α : typevec n} : ∀ x : P.obj α, typevec.id <$$> x = x
| ⟨a, g⟩ := rfl

theorem comp_map {α β γ : typevec n} (f : α ⟹ β) (g : β ⟹ γ) :
  ∀ x : P.obj α, (g ⊚ f) <$$> x = g <$$> (f <$$> x)
| ⟨a, h⟩ := rfl

instance : is_lawful_mvfunctor P.obj :=
{ id_map := @id_map _ P,
  comp_map := @comp_map _ P }

/-- Constant functor where the input object does not affect the output -/
def const (n : ℕ) (A : Type u) : mvpfunctor n :=
{ A := A, B := λ a i, pempty }

section const
variables (n) {A : Type u}  {α β : typevec.{u} n}

/-- Constructor for the constant functor -/
def const.mk (x : A) {α} : (const n A).obj α :=
⟨ x, λ i a, pempty.elim a ⟩

variables {n A}

/-- Destructor for the constant functor -/
def const.get (x : (const n A).obj α) : A :=
x.1

@[simp]
lemma const.get_map (f : α ⟹ β) (x : (const n A).obj α) :
  const.get (f <$$> x) = const.get x :=
by { cases x, refl }

@[simp]
lemma const.get_mk (x : A) : const.get (const.mk n x : (const n A).obj α) = x :=
by refl

@[simp]
lemma const.mk_get (x : (const n A).obj α) : const.mk n (const.get x) = x :=
by { cases x, dsimp [const.get,const.mk], congr' with _ ⟨ ⟩ }

end const

/-- Functor composition on polynomial functors -/
def comp (P : mvpfunctor.{u} n) (Q : fin2 n → mvpfunctor.{u} m) : mvpfunctor m :=
{ A := Σ a₂ : P.1, Π i, P.2 a₂ i → (Q i).1,
  B := λ a, λ i, Σ j (b : P.2 a.1 j), (Q j).2 (a.snd j b) i }

variables {P} {Q : fin2 n → mvpfunctor.{u} m} {α β : typevec.{u} m}

/-- Constructor for functor composition -/
def comp.mk (x : P.obj (λ i, (Q i).obj α)) : (comp P Q).obj α :=
⟨ ⟨ x.1, λ i a, (x.2 _ a).1  ⟩, λ i a, (x.snd a.fst (a.snd).fst).snd i (a.snd).snd ⟩

/-- Destructor for functor composition -/
def comp.get (x : (comp P Q).obj α) : P.obj (λ i, (Q i).obj α) :=
⟨ x.1.1, λ i a, ⟨x.fst.snd i a, λ (j : fin2 m) (b : (Q i).B _ j), x.snd j ⟨i, ⟨a, b⟩⟩⟩ ⟩

lemma comp.get_map (f : α ⟹ β) (x : (comp P Q).obj α) :
  comp.get (f <$$> x) = (λ i (x : (Q i).obj α), f <$$> x) <$$> comp.get x :=
by { cases x, refl }

@[simp]
lemma comp.get_mk (x : P.obj (λ i, (Q i).obj α)) : comp.get (comp.mk x) = x :=
begin
  cases x,
  simp! [comp.get,comp.mk],
end

@[simp]
lemma comp.mk_get (x : (comp P Q).obj α) : comp.mk (comp.get x) = x :=
begin
  cases x,
  dsimp [comp.get,comp.mk],
  ext : 2; intros, refl, refl,
  congr, ext1; intros; refl,
  ext : 2, congr, rcases x_1 with ⟨a,b,c⟩; refl
end

/-
lifting predicates and relations
-/

theorem liftp_iff {α : typevec n} (p : Π ⦃i⦄ , α i → Prop) (x : P.obj α) :
  liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i j, p (f i j) :=
begin
  split,
  { rintros ⟨y, hy⟩, cases h : y with a f,
    refine ⟨a, λ i j, (f i j).val, _, λ i j, (f i j).property⟩,
    rw [←hy, h, map_eq], refl },
  rintros ⟨a, f, xeq, pf⟩,
  use ⟨a, λ i j, ⟨f i j, pf i j⟩⟩,
  rw [xeq], reflexivity
end

theorem liftp_iff' {α : typevec n} (p : Π ⦃i⦄ , α i → Prop) (a : P.A) (f : P.B a ⟹ α) :
  @liftp.{u} _ P.obj _ α p ⟨a,f⟩ ↔ ∀ i x, p (f i x) :=
begin
  simp only [liftp_iff, sigma.mk.inj_iff]; split; intro,
  { casesm* [Exists _, _ ∧ _], subst_vars, assumption },
  repeat { constructor <|> assumption }
end

theorem liftr_iff {α : typevec n} (r : Π ⦃i⦄, α i → α i → Prop) (x y : P.obj α) :
  liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) :=
begin
  split,
  { rintros ⟨u, xeq, yeq⟩, cases h : u with a f,
    use [a, λ i j, (f i j).val.fst, λ i j, (f i j).val.snd],
    split, { rw [←xeq, h], refl },
    split, { rw [←yeq, h], refl },
    intros i j, exact (f i j).property },
  rintros ⟨a, f₀, f₁, xeq, yeq, h⟩,
  use ⟨a, λ i j, ⟨(f₀ i j, f₁ i j), h i j⟩⟩,
  dsimp, split,
  { rw [xeq], refl },
  rw [yeq], refl
end

open set mvfunctor

theorem supp_eq {α : typevec n} (a : P.A) (f : P.B a ⟹ α) (i) :
  @supp.{u} _ P.obj _ α  (⟨a,f⟩ : P.obj α) i = f i '' univ :=
begin
  ext, simp only [supp, image_univ, mem_range, mem_set_of_eq],
  split; intro h,
  { apply @h (λ i x, ∃ (y : P.B a i), f i y = x),
    rw liftp_iff', intros, refine ⟨_,rfl⟩ },
  { simp only [liftp_iff'], cases h, subst x,
    tauto }
end

end mvpfunctor

/-
Decomposing an n+1-ary pfunctor.
-/

namespace mvpfunctor
open typevec
variables {n : ℕ} (P : mvpfunctor.{u} (n+1))

/-- Split polynomial functor, get a n-ary functor
from a `n+1`-ary functor -/
def drop : mvpfunctor n :=
{ A := P.A, B := λ a, (P.B a).drop }

/-- Split polynomial functor, get a univariate functor
from a `n+1`-ary functor -/
def last : pfunctor :=
{ A := P.A, B := λ a, (P.B a).last }

/-- append arrows of a polynomial functor application -/
@[reducible] def append_contents {α : typevec n} {β : Type*}
    {a : P.A} (f' : P.drop.B a ⟹ α) (f : P.last.B a → β) :
  P.B a ⟹ α ::: β :=
split_fun f' f

end mvpfunctor
