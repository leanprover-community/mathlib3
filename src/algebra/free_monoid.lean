/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yury Kudryashov
-/
import data.equiv.basic
import data.list.basic

/-!
# Free monoid over a given alphabet

## Main definitions

* `free_monoid α`: free monoid over alphabet `α`; defined as a synonym for `list α`
  with multiplication given by `(++)`.
* `free_monoid.of`: embedding `α → free_monoid α` sending each element `x` to `[x]`;
* `free_monoid.lift α M`: natural equivalence between `α → M` and `free_monoid α →* M`;
  for technical reasons `α` and `M` are explicit arguments;
* `free_monoid.map`: embedding of `α → β` into `free_monoid α →* free_monoid β` given by `list.map`.
-/

variables {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [monoid M] {N : Type*} [monoid N]

/-- Free monoid over a given alphabet. -/
@[to_additive free_add_monoid "Free nonabelian additive monoid over a given alphabet"]
def free_monoid (α) := list α

namespace free_monoid

@[to_additive]
instance {α} : monoid (free_monoid α) :=
{ one := [],
  mul := λ x y, (x ++ y : list α),
  mul_one := by intros; apply list.append_nil,
  one_mul := by intros; refl,
  mul_assoc := by intros; apply list.append_assoc }

@[to_additive]
instance {α} : inhabited (free_monoid α) := ⟨1⟩

@[to_additive]
lemma one_def {α} : (1 : free_monoid α) = [] := rfl

@[to_additive]
lemma mul_def {α} (xs ys : list α) : (xs * ys : free_monoid α) = (xs ++ ys : list α) :=
rfl

/-- Embeds an element of `α` into `free_monoid α` as a singleton list. -/
@[to_additive "Embeds an element of `α` into `free_add_monoid α` as a singleton list." ]
def of (x : α) : free_monoid α := [x]

@[to_additive]
lemma of_mul_eq_cons (x : α) (l : free_monoid α) : of x * l = x :: l := rfl

@[to_additive]
lemma hom_eq ⦃f g : free_monoid α →* M⦄ (h : ∀ x, f (of x) = g (of x)) :
  f = g :=
begin
  ext l,
  induction l with a l ihl,
  { exact f.map_one.trans g.map_one.symm },
  { rw [← of_mul_eq_cons, f.map_mul, h, ihl, ← g.map_mul] }
end

section
-- TODO[Lean 4] : make these arguments implicit
variables (α M)

/-- Equivalence between maps `α → M` and monoid homomorphisms `free_monoid α →* M`. -/
@[to_additive "Equivalence between maps `α → A` and additive monoid homomorphisms
`free_add_monoid α →+ A`."]
def lift : (α → M) ≃ (free_monoid α →* M) :=
{ to_fun := λ f, ⟨λ l, (l.map f).prod, rfl,
    λ l₁ l₂, by simp only [mul_def, list.map_append, list.prod_append]⟩,
  inv_fun := λ f x, f (of x),
  left_inv := λ f, funext $ λ x, one_mul (f x),
  right_inv := λ f, hom_eq $ λ x, one_mul (f (of x)) }
end

@[to_additive]
lemma lift_apply (f : α → M) (l : list α) : lift α M f l = (l.map f).prod := rfl

@[to_additive]
lemma lift_comp_of (f : α → M) : (lift α M f) ∘ of = f := (lift α M).symm_apply_apply f

@[simp, to_additive]
lemma lift_eval_of (f : α → M) (x : α) : lift α M f (of x) = f x :=
congr_fun (lift_comp_of f) x

@[simp, to_additive]
lemma lift_restrict (f : free_monoid α →* M) : lift α M (f ∘ of) = f :=
(lift α M).apply_symm_apply f

lemma comp_lift (g : M →* N) (f : α → M) : g.comp (lift α M f) = lift α N (g ∘ f) :=
hom_eq $ λ x, by simp

/-- The unique monoid homomorphism `free_monoid α →* free_monoid β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive monoid homomorphism `free_add_monoid α →+ free_add_monoid β`
that sends each `of x` to `of (f x)`."]
def map (f : α → β) : free_monoid α →* free_monoid β :=
{ to_fun := list.map f,
  map_one' := rfl,
  map_mul' := λ l₁ l₂, list.map_append _ _ _ }

@[simp, to_additive] lemma map_of (f : α → β) (x : α) : map f (of x) = of (f x) := rfl

@[to_additive]
lemma lift_of_comp_eq_map (f : α → β) :
  lift α (free_monoid β) (λ x, of (f x)) = map f :=
hom_eq $ λ x, rfl

@[to_additive]
lemma map_comp (g : β → γ) (f : α → β) : map (g ∘ f) = (map g).comp (map f) :=
hom_eq $ λ x, rfl

end free_monoid
