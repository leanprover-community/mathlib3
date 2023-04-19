/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yury Kudryashov
-/
import data.list.big_operators.basic

/-!
# Free monoid over a given alphabet

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `free_monoid α`: free monoid over alphabet `α`; defined as a synonym for `list α`
  with multiplication given by `(++)`.
* `free_monoid.of`: embedding `α → free_monoid α` sending each element `x` to `[x]`;
* `free_monoid.lift`: natural equivalence between `α → M` and `free_monoid α →* M`
* `free_monoid.map`: embedding of `α → β` into `free_monoid α →* free_monoid β` given by `list.map`.
-/

variables {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [monoid M] {N : Type*} [monoid N]

/-- Free monoid over a given alphabet. -/
@[to_additive "Free nonabelian additive monoid over a given alphabet"]
def free_monoid (α) := list α

namespace free_monoid

@[to_additive] instance [decidable_eq α] : decidable_eq (free_monoid α) := list.decidable_eq

/-- The identity equivalence between `free_monoid α` and `list α`. -/
@[to_additive "The identity equivalence between `free_add_monoid α` and `list α`."]
def to_list : free_monoid α ≃ list α := equiv.refl _

/-- The identity equivalence between `list α` and `free_monoid α`. -/
@[to_additive "The identity equivalence between `list α` and `free_add_monoid α`."]
def of_list : list α ≃ free_monoid α := equiv.refl _

@[simp, to_additive] lemma to_list_symm : (@to_list α).symm = of_list := rfl
@[simp, to_additive] lemma of_list_symm : (@of_list α).symm = to_list := rfl
@[simp, to_additive] lemma to_list_of_list (l : list α) : to_list (of_list l) = l := rfl
@[simp, to_additive] lemma of_list_to_list (xs : free_monoid α) : of_list (to_list xs) = xs := rfl
@[simp, to_additive] lemma to_list_comp_of_list : @to_list α ∘ of_list = id := rfl
@[simp, to_additive] lemma of_list_comp_to_list : @of_list α ∘ to_list = id := rfl

@[to_additive]
instance : cancel_monoid (free_monoid α) :=
{ one := of_list [],
  mul := λ x y, of_list (x.to_list ++ y.to_list),
  mul_one := list.append_nil,
  one_mul := list.nil_append,
  mul_assoc := list.append_assoc,
  mul_left_cancel := λ _ _ _, list.append_left_cancel,
  mul_right_cancel := λ _ _ _, list.append_right_cancel }

@[to_additive]
instance : inhabited (free_monoid α) := ⟨1⟩

@[simp, to_additive] lemma to_list_one : (1 : free_monoid α).to_list = [] := rfl
@[simp, to_additive] lemma of_list_nil : of_list ([] : list α) = 1 := rfl

@[simp, to_additive]
lemma to_list_mul (xs ys : free_monoid α) : (xs * ys).to_list = xs.to_list ++ ys.to_list := rfl

@[simp, to_additive]
lemma of_list_append (xs ys : list α) :
  of_list (xs ++ ys) = of_list xs * of_list ys :=
rfl

@[simp, to_additive]
lemma to_list_prod (xs : list (free_monoid α)) : to_list xs.prod = (xs.map to_list).join :=
by induction xs; simp [*, list.join]

@[simp, to_additive]
lemma of_list_join (xs : list (list α)) : of_list xs.join = (xs.map of_list).prod :=
to_list.injective $ by simp

/-- Embeds an element of `α` into `free_monoid α` as a singleton list. -/
@[to_additive "Embeds an element of `α` into `free_add_monoid α` as a singleton list." ]
def of (x : α) : free_monoid α := of_list [x]

@[simp, to_additive] lemma to_list_of (x : α) : to_list (of x) = [x] := rfl
@[to_additive] lemma of_list_singleton (x : α) : of_list [x] = of x := rfl

@[simp, to_additive] lemma of_list_cons (x : α) (xs : list α) :
  of_list (x :: xs) = of x * of_list xs :=
rfl

@[to_additive] lemma to_list_of_mul (x : α) (xs : free_monoid α) :
  to_list (of x * xs) = x :: xs.to_list :=
rfl

@[to_additive] lemma of_injective : function.injective (@of α) := list.singleton_injective

/-- Recursor for `free_monoid` using `1` and `free_monoid.of x * xs` instead of `[]` and
`x :: xs`. -/
@[elab_as_eliminator, to_additive
  "Recursor for `free_add_monoid` using `0` and `free_add_monoid.of x + xs` instead of `[]` and
  `x :: xs`."]
def rec_on {C : free_monoid α → Sort*} (xs : free_monoid α) (h0 : C 1)
  (ih : Π x xs, C xs → C (of x * xs)) : C xs := list.rec_on xs h0 ih

@[simp, to_additive] lemma rec_on_one {C : free_monoid α → Sort*} (h0 : C 1)
  (ih : Π x xs, C xs → C (of x * xs)) :
  @rec_on α C 1 h0 ih = h0 :=
rfl

@[simp, to_additive] lemma rec_on_of_mul {C : free_monoid α → Sort*} (x : α) (xs : free_monoid α)
  (h0 : C 1) (ih : Π x xs, C xs → C (of x * xs)) :
  @rec_on α C (of x * xs) h0 ih = ih x xs (rec_on xs h0 ih) :=
rfl

/-- A version of `list.cases_on` for `free_monoid` using `1` and `free_monoid.of x * xs` instead of
`[]` and `x :: xs`. -/
@[elab_as_eliminator, to_additive
  "A version of `list.cases_on` for `free_add_monoid` using `0` and `free_add_monoid.of x + xs`
  instead of `[]` and `x :: xs`."]
def cases_on {C : free_monoid α → Sort*} (xs : free_monoid α) (h0 : C 1)
  (ih : Π x xs, C (of x * xs)) : C xs := list.cases_on xs h0 ih

@[simp, to_additive] lemma cases_on_one {C : free_monoid α → Sort*} (h0 : C 1)
  (ih : Π x xs, C (of x * xs)) :
  @cases_on α C 1 h0 ih = h0 :=
rfl

@[simp, to_additive] lemma cases_on_of_mul {C : free_monoid α → Sort*} (x : α) (xs : free_monoid α)
  (h0 : C 1) (ih : Π x xs, C (of x * xs)) :
  @cases_on α C (of x * xs) h0 ih = ih x xs :=
rfl

@[ext, to_additive]
lemma hom_eq ⦃f g : free_monoid α →* M⦄ (h : ∀ x, f (of x) = g (of x)) :
  f = g :=
monoid_hom.ext $ λ l, rec_on l (f.map_one.trans g.map_one.symm) $
  λ x xs hxs, by simp only [h, hxs, monoid_hom.map_mul]

/-- A variant of `list.prod` that has `[x].prod = x` true definitionally.

The purpose is to make `free_monoid.lift_eval_of` true by `rfl`. -/
@[to_additive "A variant of `list.sum` that has `[x].sum = x` true definitionally.

The purpose is to make `free_add_monoid.lift_eval_of` true by `rfl`."]
def prod_aux {M} [monoid M] (l : list M) : M :=
l.rec_on 1 (λ x xs (_ : M), list.foldl (*) x xs)

@[to_additive]
lemma prod_aux_eq : ∀ l : list M, free_monoid.prod_aux l = l.prod
| [] := rfl
| (x :: xs) := congr_arg (λ x, list.foldl (*) x xs) (one_mul _).symm

/-- Equivalence between maps `α → M` and monoid homomorphisms `free_monoid α →* M`. -/
@[to_additive "Equivalence between maps `α → A` and additive monoid homomorphisms
`free_add_monoid α →+ A`."]
def lift : (α → M) ≃ (free_monoid α →* M) :=
{ to_fun := λ f, ⟨λ l, free_monoid.prod_aux (l.to_list.map f), rfl,
    λ l₁ l₂, by simp only [prod_aux_eq, to_list_mul, list.map_append, list.prod_append]⟩,
  inv_fun := λ f x, f (of x),
  left_inv := λ f, rfl,
  right_inv := λ f, hom_eq $ λ x, rfl }

@[simp, to_additive]
lemma lift_symm_apply (f : free_monoid α →* M) : lift.symm f = f ∘ of := rfl

@[to_additive]
lemma lift_apply (f : α → M) (l : free_monoid α) : lift f l = (l.to_list.map f).prod :=
prod_aux_eq _

@[to_additive] lemma lift_comp_of (f : α → M) : lift f ∘ of = f := rfl

@[simp, to_additive]
lemma lift_eval_of (f : α → M) (x : α) : lift f (of x) = f x := rfl

@[simp, to_additive]
lemma lift_restrict (f : free_monoid α →* M) : lift (f ∘ of) = f :=
lift.apply_symm_apply f

@[to_additive]
lemma comp_lift (g : M →* N) (f : α → M) : g.comp (lift f) = lift (g ∘ f) :=
by { ext, simp }

@[to_additive]
lemma hom_map_lift (g : M →* N) (f : α → M) (x : free_monoid α) : g (lift f x) = lift (g ∘ f) x :=
monoid_hom.ext_iff.1 (comp_lift g f) x

/-- Define a multiplicative action of `free_monoid α` on `β`. -/
@[to_additive "Define an additive action of `free_add_monoid α` on `β`."]
def mk_mul_action (f : α → β → β) : mul_action (free_monoid α) β :=
{ smul := λ l b, l.to_list.foldr f b,
  one_smul := λ x, rfl,
  mul_smul := λ xs ys b, list.foldr_append _ _ _ _ }

@[to_additive] lemma smul_def (f : α → β → β) (l : free_monoid α) (b : β) :
  (by haveI := mk_mul_action f; exact l • b = l.to_list.foldr f b) :=
rfl

@[to_additive] lemma of_list_smul (f : α → β → β) (l : list α) (b : β) :
  (by haveI := mk_mul_action f; exact (of_list l) • b = l.foldr f b) :=
rfl

@[simp, to_additive] lemma of_smul (f : α → β → β) (x : α) (y : β) :
  (by haveI := mk_mul_action f; exact of x • y) = f x y :=
rfl

/-- The unique monoid homomorphism `free_monoid α →* free_monoid β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive monoid homomorphism `free_add_monoid α →+ free_add_monoid β`
that sends each `of x` to `of (f x)`."]
def map (f : α → β) : free_monoid α →* free_monoid β :=
{ to_fun := λ l, of_list $ l.to_list.map f,
  map_one' := rfl,
  map_mul' := λ l₁ l₂, list.map_append _ _ _ }

@[simp, to_additive] lemma map_of (f : α → β) (x : α) : map f (of x) = of (f x) := rfl

@[to_additive] lemma to_list_map (f : α → β) (xs : free_monoid α) :
  (map f xs).to_list = xs.to_list.map f :=
rfl

@[to_additive] lemma of_list_map (f : α → β) (xs : list α) :
  of_list (xs.map f) = map f (of_list xs) :=
rfl

@[to_additive]
lemma lift_of_comp_eq_map (f : α → β) :
  lift (λ x, of (f x)) = map f :=
hom_eq $ λ x, rfl

@[to_additive]
lemma map_comp (g : β → γ) (f : α → β) : map (g ∘ f) = (map g).comp (map f) :=
hom_eq $ λ x, rfl

@[simp, to_additive] lemma map_id : map (@id α) = monoid_hom.id (free_monoid α) :=
hom_eq $ λ x, rfl

end free_monoid
