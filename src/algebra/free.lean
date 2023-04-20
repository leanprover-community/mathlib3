/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.hom.group
import algebra.hom.equiv.basic
import control.applicative
import control.traversable.basic
import logic.equiv.defs
import data.list.basic

/-!
# Free constructions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `free_magma α`: free magma (structure with binary operation without any axioms) over alphabet `α`,
  defined inductively, with traversable instance and decidable equality.
* `magma.assoc_quotient α`: quotient of a magma `α` by the associativity equivalence relation.
* `free_semigroup α`: free semigroup over alphabet `α`, defined as a structure with two fields
  `head : α` and `tail : list α` (i.e. nonempty lists), with traversable instance and decidable
  equality.
* `free_magma_assoc_quotient_equiv α`: isomorphism between `magma.assoc_quotient (free_magma α)` and
  `free_semigroup α`.
* `free_magma.lift`: the universal property of the free magma, expressing its adjointness.
-/

universes u v l

/-- Free magma over a given alphabet. -/
@[derive decidable_eq]
inductive free_magma (α : Type u) : Type u
| of : α → free_magma
| mul : free_magma → free_magma → free_magma

/-- Free nonabelian additive magma over a given alphabet. -/
@[derive decidable_eq]
inductive free_add_magma (α : Type u) : Type u
| of : α → free_add_magma
| add : free_add_magma → free_add_magma → free_add_magma

attribute [to_additive] free_magma

namespace free_magma

variables {α : Type u}

@[to_additive]
instance [inhabited α] : inhabited (free_magma α) := ⟨of default⟩

@[to_additive]
instance : has_mul (free_magma α) := ⟨free_magma.mul⟩

attribute [pattern] has_mul.mul

@[simp, to_additive]
theorem mul_eq (x y : free_magma α) : mul x y = x * y := rfl

/-- Recursor for `free_magma` using `x * y` instead of `free_magma.mul x y`. -/
@[elab_as_eliminator, to_additive
  "Recursor for `free_add_magma` using `x + y` instead of `free_add_magma.add x y`."]
def rec_on_mul {C : free_magma α → Sort l} (x)
  (ih1 : ∀ x, C (of x)) (ih2 : ∀ x y, C x → C y → C (x * y)) :
  C x :=
free_magma.rec_on x ih1 ih2

@[ext, to_additive]
lemma hom_ext {β : Type v} [has_mul β] {f g : free_magma α →ₙ* β} (h : f ∘ of = g ∘ of) : f = g :=
fun_like.ext _ _ $ λ x, rec_on_mul x (congr_fun h) $ by { intros, simp only [map_mul, *] }

end free_magma

/-- Lifts a function `α → β` to a magma homomorphism `free_magma α → β` given a magma `β`. -/
def free_magma.lift_aux {α : Type u} {β : Type v} [has_mul β] (f : α → β) : free_magma α → β
| (free_magma.of x) := f x
| (x * y)           := x.lift_aux * y.lift_aux

/-- Lifts a function `α → β` to an additive magma homomorphism `free_add_magma α → β` given
an additive magma `β`. -/
def free_add_magma.lift_aux {α : Type u} {β : Type v} [has_add β] (f : α → β) : free_add_magma α → β
| (free_add_magma.of x) := f x
| (x + y)               := x.lift_aux + y.lift_aux

attribute [to_additive free_add_magma.lift_aux] free_magma.lift_aux

namespace free_magma

section lift

variables {α : Type u} {β : Type v} [has_mul β] (f : α → β)

/-- The universal property of the free magma expressing its adjointness. -/
@[to_additive "The universal property of the free additive magma expressing its adjointness.",
  simps symm_apply]
def lift : (α → β) ≃ (free_magma α →ₙ* β) :=
{ to_fun    := λ f,
  { to_fun := lift_aux f,
    map_mul' := λ x y, rfl, },
  inv_fun   := λ F, F ∘ of,
  left_inv  := λ f, by { ext, refl },
  right_inv := λ F, by { ext, refl } }

@[simp, to_additive] lemma lift_of (x) : lift f (of x) = f x := rfl
@[simp, to_additive] lemma lift_comp_of : lift f ∘ of = f := rfl

@[simp, to_additive] lemma lift_comp_of' (f : free_magma α →ₙ* β) : lift (f ∘ of) = f :=
lift.apply_symm_apply f

end lift

section map

variables {α : Type u} {β : Type v} (f : α → β)

/-- The unique magma homomorphism `free_magma α →ₙ* free_magma β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive magma homomorphism `free_add_magma α → free_add_magma β` that
sends each `of x` to `of (f x)`."]
def map (f : α → β) : free_magma α →ₙ* free_magma β := lift (of ∘ f)

@[simp, to_additive] lemma map_of (x) : map f (of x) = of (f x) := rfl

end map

section category

variables {α β : Type u}

@[to_additive]
instance : monad free_magma :=
{ pure := λ _, of,
  bind := λ _ _ x f, lift f x }

/-- Recursor on `free_magma` using `pure` instead of `of`. -/
@[elab_as_eliminator, to_additive "Recursor on `free_add_magma` using `pure` instead of `of`."]
protected def rec_on_pure {C : free_magma α → Sort l} (x)
  (ih1 : ∀ x, C (pure x)) (ih2 : ∀ x y, C x → C y → C (x * y)) :
  C x :=
free_magma.rec_on_mul x ih1 ih2

@[simp, to_additive]
lemma map_pure (f : α → β) (x) : (f <$> pure x : free_magma β) = pure (f x) := rfl

@[simp, to_additive]
lemma map_mul' (f : α → β) (x y : free_magma α) : (f <$> (x * y)) = (f <$> x * f <$> y) := rfl

@[simp, to_additive]
lemma pure_bind (f : α → free_magma β) (x) : (pure x >>= f) = f x := rfl

@[simp, to_additive]
lemma mul_bind (f : α → free_magma β) (x y : free_magma α) :
  (x * y >>= f) = ((x >>= f) * (y >>= f)) := rfl

@[simp, to_additive]
lemma pure_seq {α β : Type u} {f : α → β} {x : free_magma α} : pure f <*> x = f <$> x := rfl

@[simp, to_additive]
lemma mul_seq {α β : Type u} {f g : free_magma (α → β)} {x : free_magma α} :
  (f * g) <*> x = (f <*> x) * (g <*> x) := rfl

@[to_additive]
instance : is_lawful_monad free_magma.{u} :=
{ pure_bind := λ _ _ _ _, rfl,
  bind_assoc := λ α β γ x f g, free_magma.rec_on_pure x (λ x, rfl)
    (λ x y ih1 ih2, by rw [mul_bind, mul_bind, mul_bind, ih1, ih2]),
  id_map := λ α x, free_magma.rec_on_pure x (λ _, rfl)
    (λ x y ih1 ih2, by rw [map_mul', ih1, ih2]) }

end category

end free_magma

/-- `free_magma` is traversable. -/
protected def free_magma.traverse {m : Type u → Type u} [applicative m] {α β : Type u}
  (F : α → m β) :
  free_magma α → m (free_magma β)
| (free_magma.of x) := free_magma.of <$> F x
| (x * y)           := (*) <$> x.traverse <*> y.traverse

/-- `free_add_magma` is traversable. -/
protected def free_add_magma.traverse {m : Type u → Type u} [applicative m] {α β : Type u}
  (F : α → m β) :
  free_add_magma α → m (free_add_magma β)
| (free_add_magma.of x) := free_add_magma.of <$> F x
| (x + y)               := (+) <$> x.traverse <*> y.traverse

attribute [to_additive free_add_magma.traverse] free_magma.traverse

namespace free_magma

variables {α : Type u}

section category

variables {β : Type u}

@[to_additive]
instance : traversable free_magma := ⟨@free_magma.traverse⟩

variables {m : Type u → Type u} [applicative m] (F : α → m β)

@[simp, to_additive]
lemma traverse_pure (x) : traverse F (pure x : free_magma α) = pure <$> F x := rfl

@[simp, to_additive]
lemma traverse_pure' : traverse F ∘ pure = λ x, (pure <$> F x : m (free_magma β)) := rfl

@[simp, to_additive]
lemma traverse_mul (x y : free_magma α) :
  traverse F (x * y) = (*) <$> traverse F x <*> traverse F y := rfl

@[simp, to_additive]
lemma traverse_mul' :
  function.comp (traverse F) ∘ @has_mul.mul (free_magma α) _ =
    λ x y, (*) <$> traverse F x <*> traverse F y := rfl

@[simp, to_additive]
lemma traverse_eq (x) : free_magma.traverse F x = traverse F x := rfl

@[simp, to_additive]
lemma mul_map_seq (x y : free_magma α) :
  ((*) <$> x <*> y : id (free_magma α)) = (x * y : free_magma α) := rfl

@[to_additive]
instance : is_lawful_traversable free_magma.{u} :=
{ id_traverse := λ α x, free_magma.rec_on_pure x (λ x, rfl)
    (λ x y ih1 ih2, by rw [traverse_mul, ih1, ih2, mul_map_seq]),
  comp_traverse := λ F G hf1 hg1 hf2 hg2 α β γ f g x, free_magma.rec_on_pure x
    (λ x, by resetI; simp only [traverse_pure, traverse_pure'] with functor_norm)
    (λ x y ih1 ih2, by resetI; rw [traverse_mul, ih1, ih2, traverse_mul];
      simp only [traverse_mul'] with functor_norm),
  naturality := λ F G hf1 hg1 hf2 hg2 η α β f x, free_magma.rec_on_pure x
    (λ x, by simp only [traverse_pure] with functor_norm)
    (λ x y ih1 ih2, by simp only [traverse_mul] with functor_norm; rw [ih1, ih2]),
  traverse_eq_map_id := λ α β f x, free_magma.rec_on_pure x (λ _, rfl)
    (λ x y ih1 ih2, by rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq]; refl),
  .. free_magma.is_lawful_monad }

end category

end free_magma

/-- Representation of an element of a free magma. -/
protected def free_magma.repr {α : Type u} [has_repr α] : free_magma α → string
| (free_magma.of x) := repr x
| (x * y)           := "( " ++ x.repr ++ " * " ++ y.repr ++ " )"

/-- Representation of an element of a free additive magma. -/
protected def free_add_magma.repr {α : Type u} [has_repr α] : free_add_magma α → string
| (free_add_magma.of x) := repr x
| (x + y)               := "( " ++ x.repr ++ " + " ++ y.repr ++ " )"

attribute [to_additive free_add_magma.repr] free_magma.repr

@[to_additive]
instance {α : Type u} [has_repr α] : has_repr (free_magma α) := ⟨free_magma.repr⟩

/-- Length of an element of a free magma. -/
@[simp] def free_magma.length {α : Type u} : free_magma α → ℕ
| (free_magma.of x) := 1
| (x * y)           := x.length + y.length

/-- Length of an element of a free additive magma. -/
@[simp] def free_add_magma.length {α : Type u} : free_add_magma α → ℕ
| (free_add_magma.of x) := 1
| (x + y)               := x.length + y.length

attribute [to_additive free_add_magma.length] free_magma.length

/-- Associativity relations for an additive magma. -/
inductive add_magma.assoc_rel (α : Type u) [has_add α] : α → α → Prop
| intro : ∀ x y z, add_magma.assoc_rel ((x + y) + z) (x + (y + z))
| left : ∀ w x y z, add_magma.assoc_rel (w + ((x + y) + z)) (w + (x + (y + z)))

/-- Associativity relations for a magma. -/
@[to_additive add_magma.assoc_rel "Associativity relations for an additive magma."]
inductive magma.assoc_rel (α : Type u) [has_mul α] : α → α → Prop
| intro : ∀ x y z, magma.assoc_rel ((x * y) * z) (x * (y * z))
| left : ∀ w x y z, magma.assoc_rel (w * ((x * y) * z)) (w * (x * (y * z)))

namespace magma

/-- Semigroup quotient of a magma. -/
@[to_additive add_magma.free_add_semigroup "Additive semigroup quotient of an additive magma."]
def assoc_quotient (α : Type u) [has_mul α] : Type u := quot $ assoc_rel α

namespace assoc_quotient

variables {α : Type u} [has_mul α]

@[to_additive]
lemma quot_mk_assoc (x y z : α) : quot.mk (assoc_rel α) (x * y * z) = quot.mk _ (x * (y * z)) :=
quot.sound (assoc_rel.intro _ _ _)

@[to_additive]
lemma quot_mk_assoc_left (x y z w : α) :
  quot.mk (assoc_rel α) (x * (y * z * w)) = quot.mk _ (x * (y * (z * w))) :=
quot.sound (assoc_rel.left _ _ _ _)

@[to_additive]
instance : semigroup (assoc_quotient α) :=
{ mul := λ x y,
    begin
      refine quot.lift_on₂ x y (λ x y, quot.mk _ (x * y)) _ _,
      { rintro a b₁ b₂ (⟨c, d, e⟩ | ⟨c, d, e, f⟩); simp only,
        { exact quot_mk_assoc_left _ _ _ _ },
        { rw [← quot_mk_assoc, quot_mk_assoc_left, quot_mk_assoc] } },
      { rintro a₁ a₂ b (⟨c, d, e⟩ | ⟨c, d, e, f⟩); simp only,
        { simp only [quot_mk_assoc, quot_mk_assoc_left] },
        { rw [quot_mk_assoc, quot_mk_assoc, quot_mk_assoc_left, quot_mk_assoc_left,
            quot_mk_assoc_left, ← quot_mk_assoc c d, ← quot_mk_assoc c d, quot_mk_assoc_left] } }
    end,
  mul_assoc := λ x y z, quot.induction_on₃ x y z $ λ p q r, quot_mk_assoc p q r }

/-- Embedding from magma to its free semigroup. -/
@[to_additive "Embedding from additive magma to its free additive semigroup."]
def of : α →ₙ* assoc_quotient α := ⟨quot.mk _, λ x y, rfl⟩

@[to_additive]
instance [inhabited α] : inhabited (assoc_quotient α) := ⟨of default⟩

@[elab_as_eliminator, to_additive]
protected lemma induction_on {C : assoc_quotient α → Prop} (x : assoc_quotient α)
  (ih : ∀ x, C (of x)) : C x :=
quot.induction_on x ih

section lift

variables {β : Type v} [semigroup β] (f : α →ₙ* β)

@[ext, to_additive]
lemma hom_ext {f g : assoc_quotient α →ₙ* β} (h : f.comp of = g.comp of) : f = g :=
fun_like.ext _ _ $ λ x, assoc_quotient.induction_on x $ fun_like.congr_fun h

/-- Lifts a magma homomorphism `α → β` to a semigroup homomorphism `magma.assoc_quotient α → β`
given a semigroup `β`. -/
@[to_additive "Lifts an additive magma homomorphism `α → β` to an additive semigroup homomorphism
`add_magma.assoc_quotient α → β` given an additive semigroup `β`.", simps symm_apply]
def lift : (α →ₙ* β) ≃ (assoc_quotient α →ₙ* β) :=
{ to_fun := λ f,
    { to_fun := λ x, quot.lift_on x f $
        by rintros a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩); simp only [map_mul, mul_assoc],
      map_mul' := λ x y, quot.induction_on₂ x y (map_mul f) },
  inv_fun := λ f, f.comp of,
  left_inv := λ f, fun_like.ext _ _ $ λ x, rfl,
  right_inv := λ f, hom_ext $ fun_like.ext _ _ $ λ x, rfl }

@[simp, to_additive] lemma lift_of (x : α) : lift f (of x) = f x := rfl

@[simp, to_additive] lemma lift_comp_of : (lift f).comp of = f := lift.symm_apply_apply f

@[simp, to_additive] lemma lift_comp_of' (f : assoc_quotient α →ₙ* β) :
  lift (f.comp of) = f :=
lift.apply_symm_apply f

end lift

variables {β : Type v} [has_mul β] (f : α →ₙ* β)

/-- From a magma homomorphism `α →ₙ* β` to a semigroup homomorphism
`magma.assoc_quotient α →ₙ* magma.assoc_quotient β`. -/
@[to_additive "From an additive magma homomorphism `α → β` to an additive semigroup homomorphism
`add_magma.assoc_quotient α → add_magma.assoc_quotient β`."]
def map : assoc_quotient α →ₙ* assoc_quotient β := lift (of.comp f)

@[simp, to_additive] lemma map_of (x) : map f (of x) = of (f x) := rfl

end assoc_quotient

end magma

/-- Free additive semigroup over a given alphabet. -/
@[ext] structure free_add_semigroup (α : Type u) := (head : α) (tail : list α)

/-- Free semigroup over a given alphabet. -/
@[ext, to_additive] structure free_semigroup (α : Type u) := (head : α) (tail : list α)

namespace free_semigroup

variables {α : Type u}

@[to_additive]
instance : semigroup (free_semigroup α) :=
{ mul := λ L1 L2, ⟨L1.1, L1.2 ++ L2.1 :: L2.2⟩,
  mul_assoc := λ L1 L2 L3, ext _ _ rfl $ list.append_assoc _ _ _ }

@[simp, to_additive] lemma head_mul (x y : free_semigroup α) : (x * y).1 = x.1 := rfl

@[simp, to_additive] lemma tail_mul (x y : free_semigroup α) : (x * y).2 = x.2 ++ (y.1 :: y.2) :=
rfl

@[simp, to_additive] lemma mk_mul_mk (x y : α) (L1 L2 : list α) :
  mk x L1 * mk y L2 = mk x (L1 ++ y :: L2) := rfl

/-- The embedding `α → free_semigroup α`. -/
@[to_additive "The embedding `α → free_add_semigroup α`.", simps]
def of (x : α) : free_semigroup α := ⟨x, []⟩

/-- Length of an element of free semigroup. -/
@[to_additive "Length of an element of free additive semigroup"]
def length (x : free_semigroup α) : ℕ := x.tail.length + 1

@[simp, to_additive] lemma length_mul (x y : free_semigroup α) :
  (x * y).length = x.length + y.length :=
by simp [length, ← add_assoc, add_right_comm]

@[simp, to_additive] lemma length_of (x : α) : (of x).length = 1 := rfl

@[to_additive] instance [inhabited α] : inhabited (free_semigroup α) := ⟨of default⟩

/-- Recursor for free semigroup using `of` and `*`. -/
@[elab_as_eliminator, to_additive "Recursor for free additive semigroup using `of` and `+`."]
protected def rec_on_mul {C : free_semigroup α → Sort l} (x)
  (ih1 : ∀ x, C (of x)) (ih2 : ∀ x y, C (of x) → C y → C (of x * y)) :
  C x :=
free_semigroup.rec_on x $ λ f s, list.rec_on s ih1 (λ hd tl ih f, ih2 f ⟨hd, tl⟩ (ih1 f) (ih hd)) f

@[ext, to_additive]
lemma hom_ext {β : Type v} [has_mul β] {f g : free_semigroup α →ₙ* β} (h : f ∘ of = g ∘ of) :
  f = g :=
fun_like.ext _ _ $ λ x, free_semigroup.rec_on_mul x (congr_fun h) $
  λ x y hx hy, by simp only [map_mul, *]

section lift

variables {β : Type v} [semigroup β] (f : α → β)

/-- Lifts a function `α → β` to a semigroup homomorphism `free_semigroup α → β` given
a semigroup `β`. -/
@[to_additive "Lifts a function `α → β` to an additive semigroup homomorphism
`free_add_semigroup α → β` given an additive semigroup `β`.", simps symm_apply]
def lift : (α → β) ≃ (free_semigroup α →ₙ* β) :=
{ to_fun := λ f,
    { to_fun := λ x, x.2.foldl (λ a b, a * f b) (f x.1),
      map_mul' := λ x y, by simp only [head_mul, tail_mul, ← list.foldl_map f, list.foldl_append,
        list.foldl_cons, list.foldl_assoc] },
  inv_fun := λ f, f ∘ of,
  left_inv := λ f, rfl,
  right_inv := λ f, hom_ext rfl }

@[simp, to_additive] lemma lift_of (x : α) : lift f (of x) = f x := rfl
@[simp, to_additive] lemma lift_comp_of : lift f ∘ of = f := rfl

@[simp, to_additive] lemma lift_comp_of' (f : free_semigroup α →ₙ* β) : lift (f ∘ of) = f :=
hom_ext rfl

@[to_additive] lemma lift_of_mul (x y) : lift f (of x * y) = f x * lift f y :=
by rw [map_mul, lift_of]

end lift

section map

variables {β : Type v} (f : α → β)

/-- The unique semigroup homomorphism that sends `of x` to `of (f x)`. -/
@[to_additive "The unique additive semigroup homomorphism that sends `of x` to `of (f x)`."]
def map : free_semigroup α →ₙ* free_semigroup β :=
lift $ of ∘ f

@[simp, to_additive] lemma map_of (x) : map f (of x) = of (f x) := rfl

@[simp, to_additive] lemma length_map (x) : (map f x).length = x.length :=
free_semigroup.rec_on_mul x (λ x, rfl) $ λ x y hx hy, by simp only [map_mul, length_mul, *]

end map

section category

variables {β : Type u}

@[to_additive]
instance : monad free_semigroup :=
{ pure := λ _, of,
  bind := λ _ _ x f, lift f x }

/-- Recursor that uses `pure` instead of `of`. -/
@[elab_as_eliminator, to_additive "Recursor that uses `pure` instead of `of`."]
def rec_on_pure {C : free_semigroup α → Sort l} (x)
  (ih1 : ∀ x, C (pure x)) (ih2 : ∀ x y, C (pure x) → C y → C (pure x * y)) :
  C x :=
free_semigroup.rec_on_mul x ih1 ih2

@[simp, to_additive]
lemma map_pure (f : α → β) (x) : (f <$> pure x : free_semigroup β) = pure (f x) := rfl

@[simp, to_additive]
lemma map_mul' (f : α → β) (x y : free_semigroup α) :
  (f <$> (x * y)) = (f <$> x * f <$> y) :=
map_mul (map f) _ _

@[simp, to_additive] lemma pure_bind (f : α → free_semigroup β) (x) :
  (pure x >>= f) = f x := rfl

@[simp, to_additive]
lemma mul_bind (f : α → free_semigroup β) (x y : free_semigroup α) :
  (x * y >>= f) = ((x >>= f) * (y >>= f)) :=
map_mul (lift f) _ _

@[simp, to_additive] lemma pure_seq {f : α → β} {x : free_semigroup α} :
  pure f <*> x = f <$> x := rfl

@[simp, to_additive]
lemma mul_seq {f g : free_semigroup (α → β)} {x : free_semigroup α} :
  (f * g) <*> x = (f <*> x) * (g <*> x) :=
mul_bind _ _ _

@[to_additive]
instance : is_lawful_monad free_semigroup.{u} :=
{ pure_bind := λ _ _ _ _, rfl,
  bind_assoc := λ α β γ x f g, rec_on_pure x (λ x, rfl)
    (λ x y ih1 ih2, by rw [mul_bind, mul_bind, mul_bind, ih1, ih2]),
  id_map := λ α x, rec_on_pure x (λ _, rfl) (λ x y ih1 ih2, by rw [map_mul', ih1, ih2]) }

/-- `free_semigroup` is traversable. -/
@[to_additive "`free_add_semigroup` is traversable."]
protected def traverse {m : Type u → Type u} [applicative m]
  {α β : Type u} (F : α → m β) (x : free_semigroup α) : m (free_semigroup β) :=
rec_on_pure x (λ x, pure <$> F x) (λ x y ihx ihy, (*) <$> ihx <*> ihy)

@[to_additive]
instance : traversable free_semigroup := ⟨@free_semigroup.traverse⟩

variables {m : Type u → Type u} [applicative m] (F : α → m β)

@[simp, to_additive]
lemma traverse_pure (x) :traverse F (pure x : free_semigroup α) = pure <$> F x := rfl
@[simp, to_additive]
lemma traverse_pure' : traverse F ∘ pure = λ x, (pure <$> F x : m (free_semigroup β)) := rfl

section
variables [is_lawful_applicative m]
@[simp, to_additive] lemma traverse_mul (x y : free_semigroup α) :
  traverse F (x * y) = (*) <$> traverse F x <*> traverse F y :=
let ⟨x, L1⟩ := x, ⟨y, L2⟩ := y in
list.rec_on L1 (λ x, rfl) (λ hd tl ih x,
  show (*) <$> pure <$> F x <*> traverse F ((mk hd tl) * (mk y L2)) =
  (*) <$> ((*) <$> pure <$> F x <*> traverse F (mk hd tl)) <*> traverse F (mk y L2),
  by rw ih; simp only [(∘), (mul_assoc _ _ _).symm] with functor_norm) x

@[simp, to_additive] lemma traverse_mul' :
  function.comp (traverse F) ∘ @has_mul.mul (free_semigroup α) _ =
    λ x y, (*) <$> traverse F x <*> traverse F y :=
funext $ λ x, funext $ λ y, traverse_mul F x y
end

@[simp, to_additive] lemma traverse_eq (x) : free_semigroup.traverse F x = traverse F x := rfl

@[simp, to_additive] lemma mul_map_seq (x y : free_semigroup α) :
  ((*) <$> x <*> y : id (free_semigroup α)) = (x * y : free_semigroup α) := rfl

@[to_additive]
instance : is_lawful_traversable free_semigroup.{u} :=
{ id_traverse := λ α x, free_semigroup.rec_on_mul x (λ x, rfl)
    (λ x y ih1 ih2, by rw [traverse_mul, ih1, ih2, mul_map_seq]),
  comp_traverse := λ F G hf1 hg1 hf2 hg2 α β γ f g x, rec_on_pure x
    (λ x, by resetI; simp only [traverse_pure, traverse_pure'] with functor_norm)
    (λ x y ih1 ih2, by resetI; rw [traverse_mul, ih1, ih2, traverse_mul];
      simp only [traverse_mul'] with functor_norm),
  naturality := λ F G hf1 hg1 hf2 hg2 η α β f x, rec_on_pure x
    (λ x, by simp only [traverse_pure] with functor_norm)
    (λ x y ih1 ih2, by resetI; simp only [traverse_mul] with functor_norm; rw [ih1, ih2]),
  traverse_eq_map_id := λ α β f x, free_semigroup.rec_on_mul x (λ _, rfl)
    (λ x y ih1 ih2, by rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq]; refl),
  .. free_semigroup.is_lawful_monad }

end category

@[to_additive]
instance [decidable_eq α] : decidable_eq (free_semigroup α) :=
λ x y, decidable_of_iff' _ (ext_iff _ _)

end free_semigroup

namespace free_magma

variables {α : Type u} {β : Type v}

/-- The canonical multiplicative morphism from `free_magma α` to `free_semigroup α`. -/
@[to_additive "The canonical additive morphism from `free_add_magma α` to `free_add_semigroup α`."]
def to_free_semigroup : free_magma α →ₙ* free_semigroup α := free_magma.lift free_semigroup.of

@[simp, to_additive] lemma to_free_semigroup_of (x : α) :
  to_free_semigroup (of x) = free_semigroup.of x :=
rfl

@[simp, to_additive] lemma to_free_semigroup_comp_of :
  @to_free_semigroup α ∘ of = free_semigroup.of :=
rfl

@[to_additive] lemma to_free_semigroup_comp_map (f : α → β) :
  to_free_semigroup.comp (map f) = (free_semigroup.map f).comp to_free_semigroup :=
by { ext1, refl }

@[to_additive] lemma to_free_semigroup_map (f : α → β) (x : free_magma α) :
  (map f x).to_free_semigroup = free_semigroup.map f x.to_free_semigroup :=
fun_like.congr_fun (to_free_semigroup_comp_map f) x

@[simp, to_additive] lemma length_to_free_semigroup (x : free_magma α) :
  x.to_free_semigroup.length = x.length :=
free_magma.rec_on_mul x (λ x, rfl) $ λ x y hx hy,
  by rw [map_mul, free_semigroup.length_mul, length, hx, hy]

end free_magma

/-- Isomorphism between `magma.assoc_quotient (free_magma α)` and `free_semigroup α`. -/
@[to_additive "Isomorphism between
`add_magma.assoc_quotient (free_add_magma α)` and `free_add_semigroup α`."]
def free_magma_assoc_quotient_equiv (α : Type u) :
  magma.assoc_quotient (free_magma α) ≃* free_semigroup α :=
(magma.assoc_quotient.lift free_magma.to_free_semigroup).to_mul_equiv
  (free_semigroup.lift (magma.assoc_quotient.of ∘ free_magma.of))
  (by { ext, refl }) (by { ext1, refl })
