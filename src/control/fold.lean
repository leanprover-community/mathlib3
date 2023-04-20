/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Sean Leather
-/
import algebra.group.opposite
import algebra.free_monoid.basic
import control.traversable.instances
import control.traversable.lemmas
import category_theory.endomorphism
import category_theory.types
import category_theory.category.Kleisli
/-!

# List folds generalized to `traversable`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Informally, we can think of `foldl` as a special case of `traverse` where we do not care about the
reconstructed data structure and, in a state monad, we care about the final state.

The obvious way to define `foldl` would be to use the state monad but it
is nicer to reason about a more abstract interface with `fold_map` as a
primitive and `fold_map_hom` as a defining property.

```
def fold_map {α ω} [has_one ω] [has_mul ω] (f : α → ω) : t α → ω := ...

lemma fold_map_hom (α β)
  [monoid α] [monoid β] (f : α →* β)
  (g : γ → α) (x : t γ) :
  f (fold_map g x) = fold_map (f ∘ g) x :=
...
```

`fold_map` uses a monoid ω to accumulate a value for every element of
a data structure and `fold_map_hom` uses a monoid homomorphism to
substitute the monoid used by `fold_map`. The two are sufficient to
define `foldl`, `foldr` and `to_list`. `to_list` permits the
formulation of specifications in terms of operations on lists.

Each fold function can be defined using a specialized
monoid. `to_list` uses a free monoid represented as a list with
concatenation while `foldl` uses endofunctions together with function
composition.

The definition through monoids uses `traverse` together with the
applicative functor `const m` (where `m` is the monoid). As an
implementation, `const` guarantees that no resource is spent on
reconstructing the structure during traversal.

A special class could be defined for `foldable`, similarly to Haskell,
but the author cannot think of instances of `foldable` that are not also
`traversable`.
-/

universes u v

open ulift category_theory mul_opposite

namespace monoid
variables {m : Type u → Type u} [monad m]
variables {α β : Type u}
/--
For a list, foldl f x [y₀,y₁] reduces as follows:

```
calc  foldl f x [y₀,y₁]
    = foldl f (f x y₀) [y₁]      : rfl
... = foldl f (f (f x y₀) y₁) [] : rfl
... = f (f x y₀) y₁              : rfl
```
with
```
f : α → β → α
x : α
[y₀,y₁] : list β
```

We can view the above as a composition of functions:
```
... = f (f x y₀) y₁              : rfl
... = flip f y₁ (flip f y₀ x)    : rfl
... = (flip f y₁ ∘ flip f y₀) x  : rfl
```

We can use traverse and const to construct this composition:
```
calc   const.run (traverse (λ y, const.mk' (flip f y)) [y₀,y₁]) x
     = const.run ((::) <$> const.mk' (flip f y₀) <*> traverse (λ y, const.mk' (flip f y)) [y₁]) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> traverse (λ y, const.mk' (flip f y)) [] )) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> pure [] )) x
...  = const.run ( ((::) <$> const.mk' (flip f y₁) <*> pure []) ∘
         ((::) <$> const.mk' (flip f y₀)) ) x
...  = const.run ( const.mk' (flip f y₁) ∘ const.mk' (flip f y₀) ) x
...  = const.run ( flip f y₁ ∘ flip f y₀ ) x
...  = f (f x y₀) y₁
```

And this is how `const` turns a monoid into an applicative functor and
how the monoid of endofunctions define `foldl`.
-/
@[reducible] def foldl (α : Type u) : Type u := (End α)ᵐᵒᵖ
def foldl.mk (f : α → α) : foldl α := op f
def foldl.get (x : foldl α) : α → α := unop x
@[simps] def foldl.of_free_monoid (f : β → α → β) : free_monoid α →* monoid.foldl β :=
{ to_fun := λ xs, op $ flip (list.foldl f) xs.to_list,
  map_one' := rfl,
  map_mul' := by intros; simp only [free_monoid.to_list_mul, flip, unop_op,
    list.foldl_append, op_inj]; refl }

@[reducible] def foldr (α : Type u) : Type u := End α
def foldr.mk (f : α → α) : foldr α := f
def foldr.get (x : foldr α) : α → α := x
@[simps] def foldr.of_free_monoid (f : α → β → β) : free_monoid α →* monoid.foldr β :=
{ to_fun := λ xs, flip (list.foldr f) xs.to_list,
  map_one' := rfl,
  map_mul' := λ xs ys, funext $ λ z, list.foldr_append _ _ _ _ }

@[reducible] def mfoldl (m : Type u → Type u) [monad m] (α : Type u) : Type u :=
mul_opposite $ End $ Kleisli.mk m α
def mfoldl.mk (f : α → m α) : mfoldl m α := op f
def mfoldl.get (x : mfoldl m α) : α → m α := unop x
@[simps] def mfoldl.of_free_monoid [is_lawful_monad m] (f : β → α → m β) :
  free_monoid α →* monoid.mfoldl m β :=
{ to_fun := λ xs, op $ flip (list.mfoldl f) xs.to_list,
  map_one' := rfl,
  map_mul' := by intros; apply unop_injective; ext; apply list.mfoldl_append }

@[reducible] def mfoldr (m : Type u → Type u) [monad m] (α : Type u) : Type u :=
End $ Kleisli.mk m α
def mfoldr.mk (f : α → m α) : mfoldr m α := f
def mfoldr.get (x : mfoldr m α) : α → m α := x
@[simps] def mfoldr.of_free_monoid [is_lawful_monad m] (f : α → β → m β) :
  free_monoid α →* monoid.mfoldr m β :=
{ to_fun := λ xs, flip (list.mfoldr f) xs.to_list,
  map_one' := rfl,
  map_mul' := by intros; ext; apply list.mfoldr_append }

end monoid

namespace traversable
open monoid functor

section defs
variables {α β : Type u} {t : Type u → Type u} [traversable t]

def fold_map {α ω} [has_one ω] [has_mul ω] (f : α → ω) : t α → ω :=
traverse (const.mk' ∘ f)

def foldl (f : α → β → α) (x : α) (xs : t β) : α :=
(fold_map (foldl.mk ∘ flip f) xs).get x

def foldr (f : α → β → β) (x : β) (xs : t α) : β :=
(fold_map (foldr.mk ∘ f) xs).get x

/--
Conceptually, `to_list` collects all the elements of a collection
in a list. This idea is formalized by

  `lemma to_list_spec (x : t α) : to_list x = fold_map free_monoid.mk x`.

The definition of `to_list` is based on `foldl` and `list.cons` for
speed. It is faster than using `fold_map free_monoid.mk` because, by
using `foldl` and `list.cons`, each insertion is done in constant
time. As a consequence, `to_list` performs in linear.

On the other hand, `fold_map free_monoid.mk` creates a singleton list
around each element and concatenates all the resulting lists. In
`xs ++ ys`, concatenation takes a time proportional to `length xs`. Since
the order in which concatenation is evaluated is unspecified, nothing
prevents each element of the traversable to be appended at the end
`xs ++ [x]` which would yield a `O(n²)` run time. -/
def to_list : t α → list α :=
list.reverse ∘ foldl (flip list.cons) []

def length (xs : t α) : ℕ :=
down $ foldl (λ l _, up $ l.down + 1) (up 0) xs

variables {m : Type u → Type u} [monad m]

def mfoldl (f : α → β → m α) (x : α) (xs : t β) : m α :=
(fold_map (mfoldl.mk ∘ flip f) xs).get x

def mfoldr (f : α → β → m β) (x : β) (xs : t α) : m β :=
(fold_map (mfoldr.mk ∘ f) xs).get x

end defs

section applicative_transformation
variables {α β γ : Type u}

open function (hiding const)

def map_fold [monoid α] [monoid β] (f : α →* β) :
  applicative_transformation (const α) (const β) :=
{ app := λ x, f,
  preserves_seq'  := by { intros, simp only [f.map_mul, (<*>)], },
  preserves_pure' := by { intros, simp only [f.map_one, pure] } }

lemma free.map_eq_map (f : α → β) (xs : list α) :
  f <$> xs = (free_monoid.map f (free_monoid.of_list xs)).to_list := rfl

lemma foldl.unop_of_free_monoid  (f : β → α → β) (xs : free_monoid α) (a : β) :
  unop (foldl.of_free_monoid f xs) a = list.foldl f a xs.to_list := rfl

variables (m : Type u → Type u) [monad m] [is_lawful_monad m]

variables {t : Type u → Type u} [traversable t] [is_lawful_traversable t]
open is_lawful_traversable

lemma fold_map_hom [monoid α] [monoid β] (f : α →* β)
  (g : γ → α) (x : t γ) :
  f (fold_map g x) = fold_map (f ∘ g) x :=
calc  f (fold_map g x)
    = f (traverse (const.mk' ∘ g) x)                                     : rfl
... = (map_fold f).app _ (traverse (const.mk' ∘ g) x)   : rfl
... = traverse ((map_fold f).app _ ∘ (const.mk' ∘ g)) x :
        naturality (map_fold f) _ _
... = fold_map (f ∘ g) x : rfl

lemma fold_map_hom_free
  [monoid β] (f : free_monoid α →* β) (x : t α) :
  f (fold_map free_monoid.of x) = fold_map (f ∘ free_monoid.of) x :=
fold_map_hom f _ x

end applicative_transformation

section equalities
open is_lawful_traversable list (cons)
variables {α β γ : Type u}
variables {t : Type u → Type u} [traversable t] [is_lawful_traversable t]

@[simp]
lemma foldl.of_free_monoid_comp_of (f : α → β → α) :
  foldl.of_free_monoid f ∘ free_monoid.of = foldl.mk ∘ flip f := rfl

@[simp]
lemma foldr.of_free_monoid_comp_of (f : β → α → α) :
  foldr.of_free_monoid f ∘ free_monoid.of = foldr.mk ∘ f := rfl

@[simp]
lemma mfoldl.of_free_monoid_comp_of {m} [monad m] [is_lawful_monad m] (f : α → β → m α) :
  mfoldl.of_free_monoid f ∘ free_monoid.of = mfoldl.mk ∘ flip f :=
by { ext1 x, simp [(∘), mfoldl.of_free_monoid, mfoldl.mk, flip], refl }

@[simp]
lemma mfoldr.of_free_monoid_comp_of {m} [monad m] [is_lawful_monad m] (f : β → α → m α) :
  mfoldr.of_free_monoid f ∘ free_monoid.of = mfoldr.mk ∘ f :=
by { ext, simp [(∘), mfoldr.of_free_monoid, mfoldr.mk, flip] }

lemma to_list_spec (xs : t α) :
  to_list xs = free_monoid.to_list (fold_map free_monoid.of xs) :=
eq.symm $
calc  free_monoid.to_list (fold_map free_monoid.of xs)
    = free_monoid.to_list (fold_map free_monoid.of xs).reverse.reverse
                 : by simp only [list.reverse_reverse]
... = free_monoid.to_list (list.foldr cons [] (fold_map free_monoid.of xs).reverse).reverse
                 : by simp only [list.foldr_eta]
... = (unop (foldl.of_free_monoid (flip cons) (fold_map free_monoid.of xs)) []).reverse
                 : by simp [flip, list.foldr_reverse, foldl.of_free_monoid, unop_op]
... = to_list xs : begin
                     rw fold_map_hom_free (foldl.of_free_monoid (flip $ @cons α)),
                     { simp only [to_list, foldl, list.reverse_inj, foldl.get,
                         foldl.of_free_monoid_comp_of] },
                     { apply_instance }
                   end

lemma fold_map_map [monoid γ]  (f : α → β) (g : β → γ) (xs : t α) :
  fold_map g (f <$> xs) = fold_map (g ∘ f) xs :=
by simp only [fold_map,traverse_map]

lemma foldl_to_list (f : α → β → α) (xs : t β) (x : α) :
  foldl f x xs = list.foldl f x (to_list xs) :=
begin
  rw [← free_monoid.to_list_of_list (to_list xs), ← foldl.unop_of_free_monoid],
  simp only [foldl, to_list_spec, fold_map_hom_free,
    foldl.of_free_monoid_comp_of, foldl.get, free_monoid.of_list_to_list]
end

lemma foldr_to_list (f : α → β → β) (xs : t α) (x : β) :
  foldr f x xs = list.foldr f x (to_list xs) :=
begin
  change _ = foldr.of_free_monoid _ (free_monoid.of_list $ to_list xs) _,
  rw [to_list_spec, foldr, foldr.get, free_monoid.of_list_to_list, fold_map_hom_free,
    foldr.of_free_monoid_comp_of]
end

/-

-/

lemma to_list_map (f : α → β) (xs : t α) :
  to_list (f <$> xs) = f <$> to_list xs :=
by simp only [to_list_spec, free.map_eq_map, fold_map_hom, fold_map_map,
  free_monoid.of_list_to_list, free_monoid.map_of, (∘)]

@[simp] theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : t β) :
  foldl f a (g <$> l) = foldl (λ x y, f x (g y)) a l :=
by simp only [foldl, fold_map_map, (∘), flip]

@[simp] theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : t β) :
  foldr f a (g <$> l) = foldr (f ∘ g) a l :=
by simp only [foldr, fold_map_map, (∘), flip]

@[simp] theorem to_list_eq_self {xs : list α} : to_list xs = xs :=
begin
  simp only [to_list_spec, fold_map, traverse],
  induction xs,
  case list.nil { refl },
  case list.cons : _ _ ih { conv_rhs { rw [← ih] }, refl }
end

theorem length_to_list {xs : t α} : length xs = list.length (to_list xs) :=
begin
  unfold length,
  rw foldl_to_list,
  generalize : to_list xs = ys,
  let f := λ (n : ℕ) (a : α), n + 1,
  transitivity list.foldl f 0 ys,
  { generalize : 0 = n,
    induction ys with _ _ ih generalizing n,
    { simp only [list.foldl_nil] },
    { simp only [list.foldl, ih (n+1)] } },
  { induction ys with _ tl ih,
    { simp only [list.length, list.foldl_nil] },
    { simp only [list.foldl, list.length],
      rw [← ih],
      exact tl.foldl_hom (λx, x+1) f f 0 (λ n x, rfl) } }
end

variables {m : Type u → Type u} [monad m] [is_lawful_monad m]

lemma mfoldl_to_list {f : α → β → m α} {x : α} {xs : t β} :
  mfoldl f x xs = list.mfoldl f x (to_list xs) :=
calc mfoldl f x xs = unop (mfoldl.of_free_monoid f (free_monoid.of_list $ to_list xs)) x :
  by simp only [mfoldl, to_list_spec, fold_map_hom_free (mfoldl.of_free_monoid f),
    mfoldl.of_free_monoid_comp_of, mfoldl.get, free_monoid.of_list_to_list]
... = list.mfoldl f x (to_list xs) : by simp [mfoldl.of_free_monoid, unop_op, flip]

lemma mfoldr_to_list (f : α → β → m β) (x : β) (xs : t α) :
  mfoldr f x xs = list.mfoldr f x (to_list xs) :=
begin
  change _ = mfoldr.of_free_monoid f (free_monoid.of_list $ to_list xs) x,
  simp only [mfoldr, to_list_spec, fold_map_hom_free (mfoldr.of_free_monoid f),
    mfoldr.of_free_monoid_comp_of, mfoldr.get, free_monoid.of_list_to_list]
end

@[simp] theorem mfoldl_map (g : β → γ) (f : α → γ → m α) (a : α) (l : t β) :
  mfoldl f a (g <$> l) = mfoldl (λ x y, f x (g y)) a l :=
by simp only [mfoldl, fold_map_map, (∘), flip]

@[simp] theorem mfoldr_map (g : β → γ) (f : γ → α → m α) (a : α) (l : t β) :
  mfoldr f a (g <$> l) = mfoldr (f ∘ g) a l :=
by simp only [mfoldr, fold_map_map, (∘), flip]

end equalities

end traversable
