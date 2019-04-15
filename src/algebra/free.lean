/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

1. Free magma of a type (traversable, decidable equality).
2. Free semigroup of a magma.
3. Free semigroup of a type (traversable, decidable equality).
4. Free monoid of a semigroup.

And finally, magma.free_semigroup (free_magma α) ≃ free_semigroup α.
-/

import data.equiv.basic

universes u v

inductive free_magma (α : Type u) : Type u
| of : α → free_magma
| mul : free_magma → free_magma → free_magma

namespace free_magma

variables {α : Type u}

instance : has_mul (free_magma α) := ⟨free_magma.mul⟩

@[elab_as_eliminator]
protected lemma induction_on {C : free_magma α → Prop} (x)
  (ih1 : ∀ x, C (of x)) (ih2 : ∀ x y, C x → C y → C (x * y)) :
  C x :=
free_magma.rec_on x ih1 ih2

section lift

variables {β : Type v} [has_mul β] (f : α → β)

def lift : free_magma α → β
| (of x) := f x
| (mul x y) := lift x * lift y

@[simp] lemma lift_of (x) : lift f (of x) = f x := rfl
@[simp] lemma lift_mul (x y) : lift f (x * y) = lift f x * lift f y := rfl

theorem lift_unique (f : free_magma α → β) (hf : ∀ x y, f (x * y) = f x * f y) :
  f = lift (f ∘ of) :=
funext $ λ x, free_magma.rec_on x (λ x, rfl) $ λ x y ih1 ih2,
(hf x y).trans $ congr (congr_arg _ ih1) ih2

end lift

section map

variables {β : Type v} (f : α → β)

def map : free_magma α → free_magma β :=
lift $ of ∘ f

@[simp] lemma map_of (x) : map f (of x) = of (f x) := rfl
@[simp] lemma map_mul (x y) : map f (x * y) = map f x * map f y := rfl

end map

section category

instance : monad free_magma :=
{ pure := λ _, of,
  bind := λ _ _ x f, lift f x }

@[elab_as_eliminator]
protected lemma induction_on' {C : free_magma α → Prop} (x)
  (ih1 : ∀ x, C (pure x)) (ih2 : ∀ x y, C x → C y → C (x * y)) :
  C x :=
free_magma.induction_on x ih1 ih2

variables {β : Type u}

@[simp] lemma map_pure (f : α → β) (x) : (f <$> pure x : free_magma β) = pure (f x) := rfl
@[simp] lemma map_mul' (f : α → β) (x y : free_magma α) : (f <$> (x * y)) = (f <$> x * f <$> y) := rfl

@[simp] lemma pure_bind (f : α → free_magma β) (x) : (pure x >>= f) = f x := rfl
@[simp] lemma mul_bind (f : α → free_magma β) (x y : free_magma α) : (x * y >>= f) = ((x >>= f) * (y >>= f)) := rfl

@[simp] lemma pure_seq {α β : Type u} {f : α → β} {x : free_magma α} : pure f <*> x = f <$> x := rfl
@[simp] lemma mul_seq {α β : Type u} {f g : free_magma (α → β)} {x : free_magma α} : (f * g) <*> x = (f <*> x) * (g <*> x) := rfl

instance : is_lawful_monad free_magma.{u} :=
{ pure_bind := λ _ _ _ _, rfl,
  bind_assoc := λ α β γ x f g, free_magma.induction_on' x (λ x, rfl)
    (λ x y ih1 ih2, by rw [mul_bind, mul_bind, mul_bind, ih1, ih2]),
  id_map := λ α x, free_magma.induction_on' x (λ _, rfl) (λ x y ih1 ih2, by rw [map_mul', ih1, ih2]) }

protected def traverse {m : Type u → Type u} [applicative m] {α β : Type u} (F : α → m β) : free_magma α → m (free_magma β)
| (of x) := of <$> F x
| (mul x y) := (*) <$> traverse x <*> traverse y

instance : traversable free_magma := ⟨@free_magma.traverse⟩

variables {m : Type u → Type u} [applicative m] (F : α → m β)

@[simp] lemma traverse_pure (x) : traverse F (pure x : free_magma α) = pure <$> F x := rfl
@[simp] lemma traverse_pure' : traverse F ∘ pure = λ x, (pure <$> F x : m (free_magma β)) := rfl
@[simp] lemma traverse_mul (x y : free_magma α) : traverse F (x * y) = (*) <$> traverse F x <*> traverse F y := rfl
@[simp] lemma traverse_mul' : function.comp (traverse F) ∘ @has_mul.mul (free_magma α) _ = λ x y, (*) <$> traverse F x <*> traverse F y := rfl
@[simp] lemma traverse_eq (x) : free_magma.traverse F x = traverse F x := rfl

@[simp] lemma mul_map_seq (x y : free_magma α) : ((*) <$> x <*> y : id (free_magma α)) = (x * y : free_magma α) := rfl

instance : is_lawful_traversable free_magma.{u} :=
{ id_traverse := λ α x, free_magma.induction_on x (λ x, rfl)
    (λ x y ih1 ih2, by rw [traverse_mul, ih1, ih2, mul_map_seq]),
  comp_traverse := λ F G hf1 hg1 hf2 hg2 α β γ f g x, free_magma.induction_on' x
    (λ x, by resetI; simp only [traverse_pure, traverse_pure'] with functor_norm)
    (λ x y ih1 ih2, by resetI; rw [traverse_mul, ih1, ih2, traverse_mul];
      simp only [traverse_mul'] with functor_norm),
  naturality := λ F G hf1 hg1 hf2 hg2 η α β f x, free_magma.induction_on' x
    (λ x, by simp only [traverse_pure] with functor_norm)
    (λ x y ih1 ih2, by simp only [traverse_mul] with functor_norm; rw [ih1, ih2]),
  traverse_eq_map_id := λ α β f x, free_magma.induction_on x (λ _, rfl)
    (λ x y ih1 ih2, by rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq]; refl) }

end category

instance [decidable_eq α] : decidable_eq (free_magma α)
| (of p)    (of x)    := decidable_of_iff (p = x) ⟨congr_arg of, of.inj⟩
| (of p)    (mul x y) := is_false $ λ H, free_magma.no_confusion H
| (mul p q) (of x)    := is_false $ λ H, free_magma.no_confusion H
| (mul p q) (mul x y) := @decidable_of_iff (mul p q = mul x y) (p = x ∧ q = y) ⟨λ ⟨hpx, hqy⟩, hpx ▸ hqy ▸ rfl, mul.inj⟩
    (@and.decidable _ _ (decidable_eq p x) (decidable_eq q y))

def repr' [has_repr α] : free_magma α → string
| (of x) := repr x
| (mul x y) := "( " ++ repr' x ++ " * " ++ repr' y ++ " )"

instance [has_repr α] : has_repr (free_magma α) := ⟨repr'⟩

def length : free_magma α → ℕ
| (of x)    := 1
| (mul x y) := length x + length y

end free_magma


namespace magma

inductive free_semigroup.r (α : Type u) [has_mul α] : α → α → Prop
| intro : ∀ x y z, free_semigroup.r ((x * y) * z) (x * (y * z))
| left : ∀ w x y z, free_semigroup.r (w * ((x * y) * z)) (w * (x * (y * z)))

def free_semigroup (α : Type u) [has_mul α] : Type u :=
quot $ free_semigroup.r α

namespace free_semigroup

variables {α : Type u} [has_mul α]

def of : α → free_semigroup α := quot.mk _

@[elab_as_eliminator]
protected lemma induction_on {C : free_semigroup α → Prop} (x : free_semigroup α)
  (ih : ∀ x, C (of x)) : C x :=
quot.induction_on x ih

theorem of_mul_assoc (x y z : α) : of ((x * y) * z) = of (x * (y * z)) := quot.sound $ r.intro x y z
theorem of_mul_assoc_left (w x y z : α) : of (w * ((x * y) * z)) = of (w * (x * (y * z))) := quot.sound $ r.left w x y z
theorem of_mul_assoc_right (w x y z : α) : of (((w * x) * y) * z) = of ((w * (x * y)) * z) :=
by rw [of_mul_assoc, of_mul_assoc, of_mul_assoc, of_mul_assoc_left]

instance : semigroup (free_semigroup α) :=
{ mul := λ x y, begin
    refine quot.lift_on x (λ p, quot.lift_on y (λ q, (quot.mk _ $ p * q : free_semigroup α)) _) _,
    { rintros a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩); change of _ = of _,
      { rw of_mul_assoc_left },
      { rw [← of_mul_assoc, of_mul_assoc_left, of_mul_assoc] } },
    { refine quot.induction_on y (λ q, _),
      rintros a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩); change of _ = of _,
      { rw of_mul_assoc_right },
      { rw [of_mul_assoc, of_mul_assoc, of_mul_assoc_left, of_mul_assoc_left, of_mul_assoc_left,
          ← of_mul_assoc c d, ← of_mul_assoc c d, of_mul_assoc_left] } }
  end,
  mul_assoc := λ x y z, quot.induction_on x $ λ p, quot.induction_on y $ λ q,
    quot.induction_on z $ λ r, of_mul_assoc p q r }

theorem of_mul (x y : α) : of (x * y) = of x * of y := rfl

section lift

variables {β : Type v} [semigroup β] (f : α → β)

def lift (hf : ∀ x y, f (x * y) = f x * f y) : free_semigroup α → β :=
quot.lift f $ by rintros a b (⟨c, d, e⟩ | ⟨c, d, e, f⟩); simp only [hf, mul_assoc]

@[simp] lemma lift_of {hf} (x : α) : lift f hf (of x) = f x := rfl

@[simp] lemma lift_mul {hf} (x y) : lift f hf (x * y) = lift f hf x * lift f hf y :=
quot.induction_on x $ λ p, quot.induction_on y $ λ q, hf p q

theorem lift_unique (f : free_semigroup α → β) (hf : ∀ x y, f (x * y) = f x * f y) :
  f = lift (f ∘ of) (λ p q, hf (of p) (of q)) :=
funext $ λ x, quot.induction_on x $ λ p, rfl

end lift

variables {β : Type v} [has_mul β] (f : α → β)

def map (hf : ∀ x y, f (x * y) = f x * f y) : free_semigroup α → free_semigroup β :=
lift (of ∘ f) (λ x y, congr_arg of $ hf x y)

@[simp] lemma map_of {hf} (x) : map f hf (of x) = of (f x) := rfl
@[simp] lemma map_mul {hf} (x y) : map f hf (x * y) = map f hf x * map f hf y :=
lift_mul _ _ _

end free_semigroup

end magma


def free_semigroup (α : Type u) : Type u :=
α × list α

namespace free_semigroup

variables {α : Type u}

instance : semigroup (free_semigroup α) :=
{ mul := λ L1 L2, (L1.1, L1.2 ++ L2.1 :: L2.2),
  mul_assoc := λ L1 L2 L3, prod.ext rfl $ list.append_assoc _ _ _ }

def of (x : α) : free_semigroup α :=
(x, [])

@[elab_as_eliminator]
protected lemma induction_on {C : free_semigroup α → Prop} (x)
  (ih1 : ∀ x, C (of x)) (ih2 : ∀ x y, C (of x) → C y → C (of x * y)) :
  C x :=
let ⟨x, L⟩ := x in list.rec_on L ih1 (λ hd tl ih x, ih2 x (hd, tl) (ih1 x) (ih hd)) x

section lift

variables {β : Type v} [semigroup β] (f : α → β)

def lift' : α → list α → β
| x [] := f x
| x (hd::tl) := f x * lift' hd tl

def lift (x : free_semigroup α) : β :=
lift' f x.1 x.2

@[simp] lemma lift_of (x : α) : lift f (of x) = f x := rfl
@[simp] lemma lift_of_mul (x y) : lift f (of x * y) = f x * lift f y := rfl

@[simp] lemma lift_mul (x y) : lift f (x * y) = lift f x * lift f y :=
free_semigroup.induction_on x (λ p, rfl)
  (λ p x ih1 ih2, by rw [mul_assoc, lift_of_mul, lift_of_mul, mul_assoc, ih2])

theorem lift_unique (f : free_semigroup α → β) (hf : ∀ x y, f (x * y) = f x * f y) :
  f = lift (f ∘ of) :=
funext $ λ ⟨x, L⟩, list.rec_on L (λ x, rfl) (λ hd tl ih x,
  (hf (of x) (hd, tl)).trans $ congr_arg _ $ ih _) x

end lift

section map

variables {β : Type v} (f : α → β)

def map : free_semigroup α → free_semigroup β :=
lift $ of ∘ f

@[simp] lemma map_of (x) : map f (of x) = of (f x) := rfl
@[simp] lemma map_mul (x y) : map f (x * y) = map f x * map f y :=
lift_mul _ _ _

end map

section category

instance : monad free_semigroup :=
{ pure := λ _, of,
  bind := λ _ _ x f, lift f x }

@[elab_as_eliminator]
protected lemma induction_on' {C : free_semigroup α → Prop} (x)
  (ih1 : ∀ x, C (pure x)) (ih2 : ∀ x y, C (pure x) → C y → C (pure x * y)) :
  C x :=
free_semigroup.induction_on x ih1 ih2

@[simp] lemma map_pure {α β : Type u} (f : α → β) (x) : (f <$> pure x : free_semigroup β) = pure (f x) := rfl
@[simp] lemma map_mul' {α β : Type u} (f : α → β) (x y : free_semigroup α) : (f <$> (x * y)) = (f <$> x * f <$> y) :=
map_mul _ _ _

@[simp] lemma pure_bind {α β : Type u} (f : α → free_semigroup β) (x) : (pure x >>= f) = f x := rfl
@[simp] lemma mul_bind {α β : Type u} (f : α → free_semigroup β) (x y : free_semigroup α) : (x * y >>= f) = ((x >>= f) * (y >>= f)) :=
lift_mul _ _ _

@[simp] lemma pure_seq {α β : Type u} {f : α → β} {x : free_semigroup α} : pure f <*> x = f <$> x := rfl
@[simp] lemma mul_seq {α β : Type u} {f g : free_semigroup (α → β)} {x : free_semigroup α} : (f * g) <*> x = (f <*> x) * (g <*> x) :=
mul_bind _ _ _

instance : is_lawful_monad free_semigroup.{u} :=
{ pure_bind := λ _ _ _ _, rfl,
  bind_assoc := λ α β γ x f g, free_semigroup.induction_on' x (λ x, rfl)
    (λ x y ih1 ih2, by rw [mul_bind, mul_bind, mul_bind, ih1, ih2]),
  id_map := λ α x, free_semigroup.induction_on' x (λ _, rfl) (λ x y ih1 ih2, by rw [map_mul', ih1, ih2]) }

def traverse' {m : Type u → Type u} [applicative m] {α β : Type u} (F : α → m β) : α → list α → m (free_semigroup β)
| x []       := pure <$> F x
| x (hd::tl) := (*) <$> (pure <$> F x) <*> traverse' hd tl

protected def traverse {m : Type u → Type u} [applicative m] {α β : Type u} (F : α → m β) (x : free_semigroup α) : m (free_semigroup β) :=
traverse' F x.1 x.2

instance : traversable free_semigroup := ⟨@free_semigroup.traverse⟩

variables {β : Type u} {m : Type u → Type u} [applicative m] (F : α → m β)

@[simp] lemma traverse_pure (x) : traverse F (pure x : free_semigroup α) = pure <$> F x := rfl
@[simp] lemma traverse_pure' : traverse F ∘ pure = λ x, (pure <$> F x : m (free_semigroup β)) := rfl

section
variables [is_lawful_applicative m]
@[simp] lemma traverse_mul (x y : free_semigroup α) : traverse F (x * y) = (*) <$> traverse F x <*> traverse F y :=
let ⟨x, L1⟩ := x, ⟨y, L2⟩ := y in
list.rec_on L1 (λ x, rfl) (λ hd tl ih x, show (*) <$> pure <$> F x <*> traverse F ((hd, tl) * (y, L2) : free_semigroup α) =
  (*) <$> ((*) <$> pure <$> F x <*> traverse F (hd, tl)) <*> traverse F (y, L2), by rw ih; simp only [(∘), (mul_assoc _ _ _).symm] with functor_norm) x

@[simp] lemma traverse_mul' : function.comp (traverse F) ∘ @has_mul.mul (free_semigroup α) _ = λ x y, (*) <$> traverse F x <*> traverse F y :=
funext $ λ x, funext $ λ y, traverse_mul F x y
end

@[simp] lemma traverse_eq (x) : free_semigroup.traverse F x = traverse F x := rfl

@[simp] lemma mul_map_seq (x y : free_semigroup α) : ((*) <$> x <*> y : id (free_semigroup α)) = (x * y : free_semigroup α) := rfl

instance : is_lawful_traversable free_semigroup.{u} :=
{ id_traverse := λ α x, free_semigroup.induction_on x (λ x, rfl)
    (λ x y ih1 ih2, by rw [traverse_mul, ih1, ih2, mul_map_seq]),
  comp_traverse := λ F G hf1 hg1 hf2 hg2 α β γ f g x, free_semigroup.induction_on' x
    (λ x, by resetI; simp only [traverse_pure, traverse_pure'] with functor_norm)
    (λ x y ih1 ih2, by resetI; rw [traverse_mul, ih1, ih2, traverse_mul];
      simp only [traverse_mul'] with functor_norm),
  naturality := λ F G hf1 hg1 hf2 hg2 η α β f x, free_semigroup.induction_on' x
    (λ x, by simp only [traverse_pure] with functor_norm)
    (λ x y ih1 ih2, by resetI; simp only [traverse_mul] with functor_norm; rw [ih1, ih2]),
  traverse_eq_map_id := λ α β f x, free_semigroup.induction_on x (λ _, rfl)
    (λ x y ih1 ih2, by rw [traverse_mul, ih1, ih2, map_mul', mul_map_seq]; refl) }

end category

instance [decidable_eq α] : decidable_eq (free_semigroup α) := prod.decidable_eq

end free_semigroup


namespace semigroup

def free_monoid : Type u → Type u := option

namespace free_monoid

attribute [reducible] free_monoid
instance (α : Type u) [semigroup α] : monoid (free_monoid α) :=
{ mul := option.lift_or_get (*),
  mul_assoc := is_associative.assoc _,
  one := failure,
  one_mul := is_left_id.left_id _,
  mul_one := is_right_id.right_id _ }
attribute [semireducible] free_monoid

def of {α : Type u} : α → free_monoid α := some

variables {α : Type u} [semigroup α]

@[elab_as_eliminator]
protected lemma induction_on {C : free_monoid α → Prop} (x : free_monoid α)
  (h1 : C 1) (hof : ∀ x, C (of x)) : C x :=
option.rec_on x h1 hof

@[simp] lemma of_mul (x y : α) : of (x * y) = of x * of y := rfl

section lift

variables {β : Type v} [monoid β] (f : α → β)

def lift (x : free_monoid α) : β :=
option.rec_on x 1 f

@[simp] lemma lift_of (x) : lift f (of x) = f x := rfl

@[simp] lemma lift_one : lift f 1 = 1 := rfl

@[simp] lemma lift_mul (hf : ∀ x y, f (x * y) = f x * f y) (x y) :
  lift f (x * y) = lift f x * lift f y :=
free_monoid.induction_on x (by rw [one_mul, lift_one, one_mul]) $ λ x,
free_monoid.induction_on y (by rw [mul_one, lift_one, mul_one]) $ λ y,
hf x y

theorem lift_unique (f : free_monoid α → β) (hf : f 1 = 1) :
  f = lift (f ∘ of) :=
funext $ λ x, free_monoid.induction_on x hf $ λ x, rfl

end lift

variables {β : Type v} [semigroup β] (f : α → β)

def map : free_monoid α → free_monoid β :=
lift $ of ∘ f

@[simp] lemma map_of (x) : map f (of x) = of (f x) := rfl
@[simp] lemma map_mul (hf : ∀ x y, f (x * y) = f x * f y) (x y) : map f (x * y) = map f x * map f y :=
lift_mul _ (λ x y, congr_arg of $ hf x y) _ _

end free_monoid

end semigroup


def free_semigroup_free_magma (α : Type u) : magma.free_semigroup (free_magma α) ≃ free_semigroup α :=
{ to_fun := magma.free_semigroup.lift (free_magma.lift free_semigroup.of) (free_magma.lift_mul _),
  inv_fun := free_semigroup.lift (magma.free_semigroup.of ∘ free_magma.of),
  left_inv := λ x, magma.free_semigroup.induction_on x $ λ p, by rw magma.free_semigroup.lift_of;
    exact free_magma.induction_on p
      (λ x, by rw [free_magma.lift_of, free_semigroup.lift_of])
      (λ x y ihx ihy, by rw [free_magma.lift_mul, free_semigroup.lift_mul, ihx, ihy, magma.free_semigroup.of_mul]),
  right_inv := λ x, free_semigroup.induction_on x
    (λ x, by rw [free_semigroup.lift_of, magma.free_semigroup.lift_of, free_magma.lift_of])
    (λ x y ihx ihy, by rw [free_semigroup.lift_mul, magma.free_semigroup.lift_mul, ihx, ihy]) }

@[simp] lemma free_semigroup_free_magma_mul {α : Type u} (x y) :
  free_semigroup_free_magma α (x * y) = free_semigroup_free_magma α x * free_semigroup_free_magma α y :=
magma.free_semigroup.lift_mul _ _ _
