/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import data.pfunctor.multivariate.basic

/-!
# The W construction as a multivariate polynomial functor.

W types are well-founded tree-like structures. They are defined
as the least fixpoint of a polynomial functor.

## Main definitions

 * `W_mk`     - constructor
 * `W_dest    - destructor
 * `W_rec`    - recursor: basis for defining functions by structural recursion on `P.W α`
 * `W_rec_eq` - defining equation for `W_rec`
 * `W_ind`    - induction principle for `P.W α`

## Implementation notes

Three views of M-types:

 * `Wp`: polynomial functor
 * `W`: data type inductively defined by a triple:
     shape of the root, data in the root and children of the root
 * `W`: least fixed point of a polynomial functor

Specifically, we define the polynomial functor `Wp` as:

 * A := a tree-like structure without information in the nodes
 * B := given the tree-like structure `t`, `B t` is a valid path
   (specified inductively by `W_path`) from the root of `t` to any given node.

As a result `Wp.obj α` is made of a dataless tree and a function from
its valid paths to values of `α`

## Reference

 * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

universes u v

namespace mvpfunctor
open typevec
open_locale mvfunctor

variables {n : ℕ} (P : mvpfunctor.{u} (n+1))

/-- A path from the root of a tree to one of its node -/
inductive W_path : P.last.W → fin2 n → Type u
| root (a : P.A) (f : P.last.B a → P.last.W) (i : fin2 n) (c : P.drop.B a i) :
    W_path ⟨a, f⟩ i
| child (a : P.A) (f : P.last.B a → P.last.W) (i : fin2 n) (j : P.last.B a) (c : W_path (f j) i) :
    W_path ⟨a, f⟩ i

instance W_path.inhabited (x : P.last.W) {i} [I : inhabited (P.drop.B x.head i)] :
  inhabited (W_path P x i) :=
⟨ match x, I with
  | ⟨a, f ⟩, I := W_path.root a f i (@default _ I)
  end ⟩

/-- Specialized destructor on `W_path` -/
def W_path_cases_on {α : typevec n} {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : Π j : P.last.B a, P.W_path (f j) ⟹ α) :
  P.W_path ⟨a, f⟩ ⟹ α :=
begin
  intros i x, cases x,
  case W_path.root : _ _ i c { exact g' i c },
  case W_path.child : _ _ i j c { exact g j i c}
end

/-- Specialized destructor on `W_path` -/
def W_path_dest_left {α : typevec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.W_path ⟨a, f⟩ ⟹ α) :
  P.drop.B a ⟹ α :=
λ i c, h i (W_path.root a f i c)

/-- Specialized destructor on `W_path` -/
def W_path_dest_right {α : typevec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.W_path ⟨a, f⟩ ⟹ α) :
  Π j : P.last.B a, P.W_path (f j) ⟹ α :=
λ j i c, h i (W_path.child a f i j c)

theorem W_path_dest_left_W_path_cases_on
    {α : typevec n} {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : Π j : P.last.B a, P.W_path (f j) ⟹ α) :
  P.W_path_dest_left (P.W_path_cases_on g' g) = g' := rfl

theorem W_path_dest_right_W_path_cases_on
    {α : typevec n} {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : Π j : P.last.B a, P.W_path (f j) ⟹ α) :
  P.W_path_dest_right (P.W_path_cases_on g' g) = g := rfl

theorem W_path_cases_on_eta {α : typevec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.W_path ⟨a, f⟩ ⟹ α) :
  P.W_path_cases_on (P.W_path_dest_left h) (P.W_path_dest_right h) = h :=
by ext i x; cases x; reflexivity

theorem comp_W_path_cases_on {α β : typevec n} (h : α ⟹ β) {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : Π j : P.last.B a, P.W_path (f j) ⟹ α) :
  h ⊚ P.W_path_cases_on g' g = P.W_path_cases_on (h ⊚ g') (λ i, h ⊚ g i) :=
by ext i x; cases x; reflexivity

/-- Polynomial functor for the W-type of `P`. `A` is a data-less well-founded
tree whereas, for a given `a : A`, `B a` is a valid path in tree `a` so
that `Wp.obj α` is made of a tree and a function from its valid paths to
the values it contains  -/
def Wp : mvpfunctor n :=
{ A := P.last.W, B := P.W_path }

/-- W-type of `P` -/
@[nolint has_inhabited_instance]
def W (α : typevec n) : Type* := P.Wp.obj α

instance mvfunctor_W : mvfunctor P.W := by delta mvpfunctor.W; apply_instance

/-!
First, describe operations on `W` as a polynomial functor.
-/

/-- Constructor for `Wp` -/
def Wp_mk {α : typevec n} (a : P.A) (f : P.last.B a → P.last.W) (f' : P.W_path ⟨a, f⟩ ⟹ α) :
  P.W α :=
⟨⟨a, f⟩, f'⟩

/-- Recursor for `Wp` -/
def Wp_rec {α : typevec n} {C : Type*}
  (g : Π (a : P.A) (f : P.last.B a → P.last.W),
    (P.W_path ⟨a, f⟩ ⟹ α) → (P.last.B a → C) → C) :
  Π (x : P.last.W) (f' : P.W_path x ⟹ α), C
| ⟨a, f⟩ f' := g a f f' (λ i, Wp_rec (f i) (P.W_path_dest_right f' i))

theorem Wp_rec_eq {α : typevec n} {C : Type*}
    (g : Π (a : P.A) (f : P.last.B a → P.last.W),
      (P.W_path ⟨a, f⟩ ⟹ α) → (P.last.B a → C) → C)
    (a : P.A) (f : P.last.B a → P.last.W) (f' : P.W_path ⟨a, f⟩ ⟹ α) :
  P.Wp_rec g ⟨a, f⟩ f' = g a f f' (λ i, P.Wp_rec g (f i) (P.W_path_dest_right f' i)) :=
rfl

-- Note: we could replace Prop by Type* and obtain a dependent recursor

theorem Wp_ind {α : typevec n} {C : Π x : P.last.W, P.W_path x ⟹ α → Prop}
  (ih : ∀ (a : P.A) (f : P.last.B a → P.last.W)
    (f' : P.W_path ⟨a, f⟩ ⟹ α),
      (∀ i : P.last.B a, C (f i) (P.W_path_dest_right f' i)) → C ⟨a, f⟩ f') :
  Π (x : P.last.W) (f' : P.W_path x ⟹ α), C x f'
| ⟨a, f⟩ f' := ih a f f' (λ i, Wp_ind _ _)

/-!
Now think of W as defined inductively by the data ⟨a, f', f⟩ where
- `a  : P.A` is the shape of the top node
- `f' : P.drop.B a ⟹ α` is the contents of the top node
- `f  : P.last.B a → P.last.W` are the subtrees
 -/

/-- Constructor for `W` -/
def W_mk {α : typevec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  P.W α :=
let g  : P.last.B a → P.last.W  := λ i, (f i).fst,
    g' : P.W_path ⟨a, g⟩ ⟹ α := P.W_path_cases_on f' (λ i, (f i).snd) in
⟨⟨a, g⟩, g'⟩

/-- Recursor for `W` -/
def W_rec {α : typevec n} {C : Type*}
    (g : Π a : P.A, ((P.drop).B a ⟹ α) → ((P.last).B a → P.W α) → ((P.last).B a → C) → C) :
  P.W α → C
| ⟨a, f'⟩ :=
  let g' (a : P.A) (f : P.last.B a → P.last.W) (h : P.W_path ⟨a, f⟩ ⟹ α)
        (h' : P.last.B a → C) : C :=
      g a (P.W_path_dest_left h) (λ i, ⟨f i, P.W_path_dest_right h i⟩) h' in
  P.Wp_rec g' a f'

/-- Defining equation for the recursor of `W` -/
theorem W_rec_eq {α : typevec n} {C : Type*}
    (g : Π a : P.A, ((P.drop).B a ⟹ α) → ((P.last).B a → P.W α) → ((P.last).B a → C) → C)
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  P.W_rec g (P.W_mk a f' f) = g a f' f (λ i, P.W_rec g (f i)) :=
begin
  rw [W_mk, W_rec], dsimp, rw [Wp_rec_eq],
  dsimp only [W_path_dest_left_W_path_cases_on, W_path_dest_right_W_path_cases_on],
  congr; ext1 i; cases (f i); refl
end

/-- Induction principle for `W` -/
theorem W_ind {α : typevec n} {C : P.W α → Prop}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α),
      (∀ i, C (f i)) → C (P.W_mk a f' f)) :
  ∀ x, C x :=
begin
  intro x, cases x with a f,
  apply @Wp_ind n P α (λ a f, C ⟨a, f⟩), dsimp,
  intros a f f' ih',
  dsimp [W_mk] at ih,
  let ih'' := ih a (P.W_path_dest_left f') (λ i, ⟨f i, P.W_path_dest_right f' i⟩),
  dsimp at ih'', rw W_path_cases_on_eta at ih'',
  apply ih'',
  apply ih'
end

theorem W_cases {α : typevec n} {C : P.W α → Prop}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α), C (P.W_mk a f' f)) :
  ∀ x, C x :=
P.W_ind (λ a f' f ih', ih a f' f)

/-- W-types are functorial -/
def W_map {α β : typevec n} (g : α ⟹ β) : P.W α → P.W β :=
λ x, g <$$> x

theorem W_mk_eq {α : typevec n} (a : P.A) (f : P.last.B a → P.last.W)
    (g' : P.drop.B a ⟹ α) (g : Π j : P.last.B a, P.W_path (f j) ⟹ α) :
  P.W_mk a g' (λ i, ⟨f i, g i⟩) =
    ⟨⟨a, f⟩, P.W_path_cases_on g' g⟩ := rfl

theorem W_map_W_mk {α β : typevec n} (g : α ⟹ β)
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  g <$$> P.W_mk a f' f = P.W_mk a (g ⊚ f') (λ i, g <$$> f i) :=
begin
  show _ = P.W_mk a (g ⊚ f') (mvfunctor.map g ∘ f),
  have : mvfunctor.map g ∘ f = λ i, ⟨(f i).fst, g ⊚ ((f i).snd)⟩,
  { ext i : 1, dsimp [function.comp], cases (f i), refl },
  rw this,
  have : f = λ i, ⟨(f i).fst, (f i).snd⟩,
  { ext1, cases (f x), refl },
  rw this, dsimp,
  rw [W_mk_eq, W_mk_eq],
  have h := mvpfunctor.map_eq P.Wp g,
  rw [h, comp_W_path_cases_on]
end

-- TODO: this technical theorem is used in one place in constructing the initial algebra.
-- Can it be avoided?

/-- Constructor of a value of `P.obj (α ::: β)` from components.
Useful to avoid complicated type annotation -/
@[reducible] def obj_append1 {α : typevec n} {β : Type*}
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → β) :
  P.obj (α ::: β) :=
⟨a, split_fun f' f⟩

theorem map_obj_append1 {α γ : typevec n} (g : α ⟹ γ)
  (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
append_fun g (P.W_map g) <$$> P.obj_append1 a f' f =
  P.obj_append1 a (g ⊚ f') (λ x, P.W_map g (f x)) :=
by rw [obj_append1, obj_append1, map_eq, append_fun, ← split_fun_comp]; refl

/-!
Yet another view of the W type: as a fixed point for a multivariate polynomial functor.
These are needed to use the W-construction to construct a fixed point of a qpf, since
the qpf axioms are expressed in terms of `map` on `P`.
-/

/-- Constructor for the W-type of `P` -/
def W_mk' {α : typevec n} : P.obj (α ::: P.W α) → P.W α
| ⟨a, f⟩ := P.W_mk a (drop_fun f) (last_fun f)

/-- Destructor for the W-type of `P` -/
def W_dest' {α : typevec.{u} n} : P.W α → P.obj (α.append1 (P.W α)) :=
P.W_rec (λ a f' f _, ⟨a, split_fun f' f⟩)

theorem W_dest'_W_mk {α : typevec n}
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  P.W_dest' (P.W_mk a f' f) = ⟨a, split_fun f' f⟩ :=
by rw [W_dest', W_rec_eq]

theorem W_dest'_W_mk' {α : typevec n} (x : P.obj (α.append1 (P.W α))) :
  P.W_dest' (P.W_mk' x) = x :=
by cases x with a f; rw [W_mk', W_dest'_W_mk, split_drop_fun_last_fun]

end mvpfunctor
