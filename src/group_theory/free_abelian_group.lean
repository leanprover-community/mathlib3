/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.group.pi
import group_theory.free_group
import group_theory.abelianization
import algebra.module.basic -- we use the ℤ-module structure on an add_comm_group in punit_equiv

/-!
# Free abelian groups

The free abelian group on a type `α`, defined as the abelianisation of
the free group on `α`.

The free abelian group on `α` can be abstractly defined as the left adjoint of the
forgetful functor from abelian groups to types. Alternatively, one could define
it as the functions `α → ℤ` which send all but finitely many `(a : α)` to `0`,
under pointwise addition. In this file, it is defined as the abelianisation
of the free group on `α`. All the constructions and theorems required to show
the adjointness of the construction and the forgetful functor are proved in this
file, but the category-theoretic adjunction statement is in
`algebra.category.Group.adjunctions` .

## Main definitions

Here we use the following variables: `(α β : Type*) (A : Type*) [add_comm_group A]`

* `free_abelian_group α` : the free abelian group on a type `α`. As an abelian
group it is `α →₀ ℤ`, the functions from `α` to `ℤ` such that all but finitely
many elements get mapped to zero, however this is not how it is implemented.

* `lift f : free_abelian_group α →+ A` : the group homomorphism induced
  by the map `f : α → A`.

* `map (f : α → β) : free_abelian_group α →+ free_abelian_group β` : functoriality
    of `free_abelian_group`

* `instance [monoid α] : semigroup (free_abelian_group α)`

* `instance [comm_monoid α] : comm_ring (free_abelian_group α)`

It has been suggested that we would be better off refactoring this file
and using `finsupp` instead.

## Implementation issues

The definition is `def free_abelian_group : Type u :=
additive $ abelianization $ free_group α`

Chris Hughes has suggested that this all be rewritten in terms of `finsupp`.
Johan Commelin has written all the API relating the definition to `finsupp`
in the lean-liquid repo.

The lemmas `map_pure`, `map_of`, `map_zero`, `map_add`, `map_neg` and `map_sub`
are proved about the `functor.map` `<$>` construction, and need `α` and `β` to
be in the same universe. But
`free_abelian_group.map (f : α → β)` is defined to be the `add_group`
homomorphism `free_abelian_group α →+ free_abelian_group β` (with `α` and `β` now
allowed to be in different universes), so `(map f).map_add`
etc can be used to prove that `free_abelian_group.map` preserves addition. The
functions `map_id`, `map_id_apply`, `map_comp`, `map_comp_apply` and `map_of_apply`
are about `free_abelian_group.map`.

-/


universes u v

variables (α : Type u)

/-- The free abelian group on a type. -/
def free_abelian_group : Type u :=
additive $ abelianization $ free_group α

instance : add_comm_group (free_abelian_group α) :=
@additive.add_comm_group _ $ abelianization.comm_group _

instance : inhabited (free_abelian_group α) := ⟨0⟩

variable {α}

namespace free_abelian_group

/-- The canonical map from α to `free_abelian_group α` -/
def of (x : α) : free_abelian_group α :=
abelianization.of $ free_group.of x

/-- The map `free_abelian_group α →+ A` induced by a map of types `α → A`. -/
def lift {β : Type v} [add_comm_group β] : (α → β) ≃ (free_abelian_group α →+ β) :=
(@free_group.lift _ (multiplicative β) _).trans $
  (@abelianization.lift _ _ (multiplicative β) _).trans monoid_hom.to_additive

namespace lift
variables {β : Type v} [add_comm_group β] (f : α → β)
open free_abelian_group

@[simp] protected lemma of (x : α) : lift f (of x) = f x :=
begin
  convert @abelianization.lift.of (free_group α) _ (multiplicative β) _ _ _,
  convert free_group.lift.of.symm
end

protected theorem unique (g : free_abelian_group α →+ β)
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = lift f x :=
add_monoid_hom.congr_fun ((lift.symm_apply_eq).mp (funext hg : g ∘ of = f)) _

/-- See note [partially-applied ext lemmas]. -/
@[ext]
protected theorem ext (g h : free_abelian_group α →+ β)
  (H : ∀ x, g (of x) = h (of x)) :
  g = h :=
lift.symm.injective $ funext H

lemma map_hom {α β γ} [add_comm_group β] [add_comm_group γ]
  (a : free_abelian_group α) (f : α → β) (g : β →+ γ) :
  g (lift f a) = lift (g ∘ f) a :=
begin
  suffices : (g.comp (lift f)) a = lift (g ∘ f) a,
    exact this,
  apply @lift.unique,
  assume a,
  show g ((lift f) (of a)) = g (f a),
  simp only [(∘), lift.of],
end

end lift

section
open_locale classical

lemma of_injective : function.injective (of : α → free_abelian_group α) :=
λ x y hoxy, classical.by_contradiction $ assume hxy : x ≠ y,
  let f : free_abelian_group α →+ ℤ := lift (λ z, if x = z then (1 : ℤ) else 0) in
  have hfx1 : f (of x) = 1, from (lift.of _ _).trans $ if_pos rfl,
  have hfy1 : f (of y) = 1, from hoxy ▸ hfx1,
  have hfy0 : f (of y) = 0, from (lift.of _ _).trans $ if_neg hxy,
  one_ne_zero $ hfy1.symm.trans hfy0

end

local attribute [instance] quotient_group.left_rel

@[elab_as_eliminator]
protected theorem induction_on
  {C : free_abelian_group α → Prop}
  (z : free_abelian_group α)
  (C0 : C 0)
  (C1 : ∀ x, C $ of x)
  (Cn : ∀ x, C (of x) → C (-of x))
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
quotient.induction_on' z $ λ x, quot.induction_on x $ λ L,
list.rec_on L C0 $ λ ⟨x, b⟩ tl ih,
bool.rec_on b (Cp _ _ (Cn _ (C1 x)) ih) (Cp _ _ (C1 x) ih)

theorem lift.add' {α β} [add_comm_group β] (a : free_abelian_group α) (f g : α → β) :
  lift (f + g) a = lift f a + lift g a :=
begin
  refine free_abelian_group.induction_on a _ _ _ _,
  { simp only [(lift _).map_zero, zero_add] },
  { assume x,
    simp only [lift.of, pi.add_apply] },
  { assume x h,
    simp only [map_neg, lift.of, pi.add_apply, neg_add] },
  { assume x y hx hy,
    simp only [(lift _).map_add, hx, hy, add_add_add_comm] }
end

/-- If `g : free_abelian_group X` and `A` is an abelian group then `lift_add_group_hom g`
is the additive group homomorphism sending a function `X → A` to the term of type `A`
corresponding to the evaluation of the induced map `free_abelian_group X → A` at `g`. -/
@[simps]
def lift_add_group_hom {α} (β) [add_comm_group β] (a : free_abelian_group α) : (α → β) →+ β :=
add_monoid_hom.mk' (λ f, lift f a) (lift.add' a)

lemma lift_neg' {β} [add_comm_group β] (f : α → β) : lift (-f) = -lift f :=
add_monoid_hom.ext $ λ _, (lift_add_group_hom _ _ : (α → β) →+ β).map_neg _

section monad

variables {β : Type u}

instance : monad free_abelian_group.{u} :=
{ pure := λ α, of,
  bind := λ α β x f, lift f x }

@[elab_as_eliminator]
protected theorem induction_on'
  {C : free_abelian_group α → Prop}
  (z : free_abelian_group α)
  (C0 : C 0)
  (C1 : ∀ x, C $ pure x)
  (Cn : ∀ x, C (pure x) → C (-pure x))
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
free_abelian_group.induction_on z C0 C1 Cn Cp

@[simp] lemma map_pure (f : α → β) (x : α) : f <$> (pure x : free_abelian_group α) = pure (f x) :=
rfl

@[simp] protected lemma map_zero (f : α → β) : f <$> (0 : free_abelian_group α) = 0 :=
(lift (of ∘ f)).map_zero

@[simp] protected lemma map_add (f : α → β) (x y : free_abelian_group α) :
  f <$> (x + y) = f <$> x + f <$> y :=
(lift _).map_add _ _

@[simp] protected lemma map_neg (f : α → β) (x : free_abelian_group α) : f <$> (-x) = -(f <$> x) :=
map_neg (lift $ of ∘ f) _

@[simp] protected lemma map_sub (f : α → β) (x y : free_abelian_group α) :
  f <$> (x - y) = f <$> x - f <$> y :=
map_sub (lift $ of ∘ f) _ _

@[simp] lemma map_of (f : α → β) (y : α) : f <$> of y = of (f y) := rfl

@[simp] lemma pure_bind (f : α → free_abelian_group β) (x) : pure x >>= f = f x :=
lift.of _ _

@[simp] lemma zero_bind (f : α → free_abelian_group β) : 0 >>= f = 0 :=
(lift f).map_zero

@[simp] lemma add_bind (f : α → free_abelian_group β) (x y : free_abelian_group α) :
  x + y >>= f = (x >>= f) + (y >>= f) :=
(lift _).map_add _ _

@[simp] lemma neg_bind (f : α → free_abelian_group β) (x : free_abelian_group α) :
  -x >>= f = -(x >>= f) :=
map_neg (lift f) _

@[simp] lemma sub_bind (f : α → free_abelian_group β) (x y : free_abelian_group α) :
  x - y >>= f = (x >>= f) - (y >>= f) :=
map_sub (lift f) _ _

@[simp] lemma pure_seq (f : α → β) (x : free_abelian_group α) : pure f <*> x = f <$> x :=
pure_bind _ _

@[simp] lemma zero_seq (x : free_abelian_group α) : (0 : free_abelian_group (α → β)) <*> x = 0 :=
zero_bind _

@[simp] lemma add_seq (f g : free_abelian_group (α → β)) (x : free_abelian_group α) :
  f + g <*> x = (f <*> x) + (g <*> x) :=
add_bind _ _ _

@[simp] lemma neg_seq (f : free_abelian_group (α → β)) (x : free_abelian_group α) :
  -f <*> x = -(f <*> x) :=
neg_bind _ _

@[simp] lemma sub_seq (f g : free_abelian_group (α → β)) (x : free_abelian_group α) :
  f - g <*> x = (f <*> x) - (g <*> x) :=
sub_bind _ _ _

/-- If `f : free_abelian_group (α → β)`, then `f <*>` is an additive morphism
`free_abelian_group α →+ free_abelian_group β`. -/
def seq_add_group_hom (f : free_abelian_group (α → β)) :
  free_abelian_group α →+ free_abelian_group β :=
add_monoid_hom.mk' ((<*>) f)
  (λ x y, show lift (<$> (x+y)) _ = _,
    by { simp only [free_abelian_group.map_add], exact lift.add' f _ _, })

@[simp] lemma seq_zero (f : free_abelian_group (α → β)) : f <*> 0 = 0 :=
(seq_add_group_hom f).map_zero

@[simp] lemma seq_add (f : free_abelian_group (α → β)) (x y : free_abelian_group α) :
  f <*> (x + y) = (f <*> x) + (f <*> y) :=
(seq_add_group_hom f).map_add x y

@[simp] lemma seq_neg (f : free_abelian_group (α → β)) (x : free_abelian_group α) :
  f <*> (-x) = -(f <*> x) :=
(seq_add_group_hom f).map_neg x

@[simp] lemma seq_sub (f : free_abelian_group (α → β)) (x y : free_abelian_group α) :
  f <*> (x - y) = (f <*> x) - (f <*> y) :=
(seq_add_group_hom f).map_sub x y

instance : is_lawful_monad free_abelian_group.{u} :=
{ id_map := λ α x, free_abelian_group.induction_on' x (free_abelian_group.map_zero id)
    (map_pure id) (λ x ih, by rw [free_abelian_group.map_neg, ih])
      (λ x y ihx ihy, by rw [free_abelian_group.map_add, ihx, ihy]),
  pure_bind := λ α β x f, pure_bind f x,
  bind_assoc := λ α β γ x f g, free_abelian_group.induction_on' x
    (by iterate 3 { rw zero_bind }) (λ x, by iterate 2 { rw pure_bind })
    (λ x ih, by iterate 3 { rw neg_bind }; rw ih)
    (λ x y ihx ihy, by iterate 3 { rw add_bind }; rw [ihx, ihy]) }

instance : is_comm_applicative free_abelian_group.{u} :=
{ commutative_prod := λ α β x y, free_abelian_group.induction_on' x
    (by rw [free_abelian_group.map_zero, zero_seq, seq_zero])
    (λ p, by rw [map_pure, pure_seq]; exact free_abelian_group.induction_on' y
      (by rw [free_abelian_group.map_zero, free_abelian_group.map_zero, zero_seq])
      (λ q, by rw [map_pure, map_pure, pure_seq, map_pure])
      (λ q ih, by rw [free_abelian_group.map_neg, free_abelian_group.map_neg, neg_seq, ih])
      (λ y₁ y₂ ih1 ih2,
        by rw [free_abelian_group.map_add, free_abelian_group.map_add, add_seq, ih1, ih2]))
    (λ p ih, by rw [free_abelian_group.map_neg, neg_seq, seq_neg, ih])
    (λ x₁ x₂ ih1 ih2, by rw [free_abelian_group.map_add, add_seq, seq_add, ih1, ih2]) }


end monad

universe w

variables {β : Type v} {γ : Type w}

/-- The additive group homomorphism `free_abelian_group α →+ free_abelian_group β` induced from a
  map `α → β` -/
def map (f : α → β) : free_abelian_group α →+ free_abelian_group β :=
lift (of ∘ f)

lemma lift_comp {α} {β} {γ} [add_comm_group γ]
  (f : α → β) (g : β → γ) (x : free_abelian_group α) :
  lift (g ∘ f) x = lift g (map f x) :=
begin
  apply free_abelian_group.induction_on x,
  { exact add_monoid_hom.map_zero _ },
  { intro y, refl },
  { intros x h, simp only [h, add_monoid_hom.map_neg] },
  { intros x y h₁ h₂, simp only [h₁, h₂, add_monoid_hom.map_add] }
end

lemma map_id : map id = add_monoid_hom.id (free_abelian_group α) :=
eq.symm $ lift.ext _ _ $ λ x, lift.unique of (add_monoid_hom.id _) $
  λ y, add_monoid_hom.id_apply _ _

lemma map_id_apply (x : free_abelian_group α) : map id x = x := by {rw map_id, refl }

lemma map_comp {f : α → β} {g : β → γ} : map (g ∘ f) = (map g).comp (map f) :=
eq.symm $ lift.ext _ _ $ λ x, eq.symm $ lift_comp _ _ _

lemma map_comp_apply {f : α → β} {g : β → γ} (x : free_abelian_group α) :
  map (g ∘ f) x = (map g) ((map f) x) := by { rw map_comp, refl }

-- version of map_of which uses `map`
@[simp] lemma map_of_apply {f : α → β} (a : α) : map f (of a) = of (f a) := rfl

variable (α)

section has_mul
variables [has_mul α]

instance : has_mul (free_abelian_group α) := ⟨λ x, lift $ λ x₂, lift (λ x₁, of $ x₁ * x₂) x⟩

variable {α}

lemma mul_def (x y : free_abelian_group α) : x * y = lift (λ x₂, lift (λ x₁, of (x₁ * x₂)) x) y :=
rfl

@[simp] lemma of_mul_of (x y : α) : of x * of y = of (x * y) := rfl
lemma of_mul (x y : α) : of (x * y) = of x * of y := rfl

instance : distrib (free_abelian_group α) :=
{ add := (+),
  left_distrib := λ x y z, (lift _).map_add _ _,
  right_distrib := λ x y z, by simp only [(*), map_add, ←pi.add_def, lift.add'],
  ..free_abelian_group.has_mul _ }

instance : non_unital_non_assoc_ring (free_abelian_group α) :=
{ zero_mul := λ a, by { have h : 0 * a + 0 * a = 0 * a, by simp [←add_mul], simpa using h },
  mul_zero := λ a, rfl,
  ..free_abelian_group.distrib, ..free_abelian_group.add_comm_group _ }

end has_mul

instance [has_one α] : has_one (free_abelian_group α) := ⟨of 1⟩

instance [semigroup α] : non_unital_ring (free_abelian_group α) :=
{ mul := (*),
  mul_assoc := λ x y z, begin
    refine free_abelian_group.induction_on z (by simp) (λ L3, _) (λ L3 ih, _) (λ z₁ z₂ ih₁ ih₂, _),
    { refine free_abelian_group.induction_on y (by simp) (λ L2, _) (λ L2 ih, _)
        (λ y₁ y₂ ih₁ ih₂, _),
      { refine free_abelian_group.induction_on x (by simp) (λ L1, _) (λ L1 ih, _)
          (λ x₁ x₂ ih₁ ih₂, _),
        { rw [of_mul_of, of_mul_of, of_mul_of, of_mul_of, mul_assoc] },
        { rw [neg_mul, neg_mul, neg_mul, ih] },
        { rw [add_mul, add_mul, add_mul, ih₁, ih₂] } },
      { rw [neg_mul, mul_neg, mul_neg, neg_mul, ih] },
      { rw [add_mul, mul_add, mul_add, add_mul, ih₁, ih₂] } },
    { rw [mul_neg, mul_neg, mul_neg, ih] },
    { rw [mul_add, mul_add, mul_add, ih₁, ih₂] }
  end,
  .. free_abelian_group.non_unital_non_assoc_ring }

section monoid

variables {R : Type*} [monoid α] [ring R]

instance : ring (free_abelian_group α) :=
{ mul := (*),
  mul_one := λ x, begin
    unfold has_mul.mul semigroup.mul has_one.one,
    rw lift.of,
    refine free_abelian_group.induction_on x rfl (λ L, _) (λ L ih, _) (λ x1 x2 ih1 ih2, _),
    { erw [lift.of], congr' 1, exact mul_one L },
    { rw [map_neg, ih] },
    { rw [map_add, ih1, ih2] }
  end,
  one_mul := λ x, begin
    unfold has_mul.mul semigroup.mul has_one.one,
    refine free_abelian_group.induction_on x rfl _ _ _,
    { intros L, rw [lift.of, lift.of], congr' 1, exact one_mul L },
    { intros L ih, rw [map_neg, ih] },
    { intros x1 x2 ih1 ih2, rw [map_add, ih1, ih2] }
  end,
  .. free_abelian_group.non_unital_ring _, ..free_abelian_group.has_one _ }

variable {α}

/-- `free_abelian_group.of` is a `monoid_hom` when `α` is a `monoid`. -/
def of_mul_hom : α →* free_abelian_group α :=
{ to_fun := of,
  map_one' := rfl,
  map_mul' := of_mul }

@[simp] lemma of_mul_hom_coe : (of_mul_hom : α → free_abelian_group α) = of := rfl

/-- If `f` preserves multiplication, then so does `lift f`. -/
def lift_monoid : (α →* R) ≃ (free_abelian_group α →+* R) :=
{ to_fun := λ f,
  { to_fun := lift f,
    map_one' := (lift.of f _).trans f.map_one,
    map_mul' := λ x y,
    begin
      refine free_abelian_group.induction_on y (mul_zero _).symm (λ L2, _) (λ L2 ih, _) _,
      { refine free_abelian_group.induction_on x (zero_mul _).symm (λ L1, _) (λ L1 ih, _) _,
        { simp_rw [of_mul_of, lift.of],
          exact f.map_mul _ _ },
        { simp_rw [neg_mul, map_neg, neg_mul],
          exact congr_arg has_neg.neg ih },
        { intros x1 x2 ih1 ih2,
          simp only [add_mul, map_add, ih1, ih2] } },
      { rw [mul_neg, map_neg, map_neg, mul_neg, ih] },
      { intros y1 y2 ih1 ih2,
        rw [mul_add, map_add, map_add, mul_add, ih1, ih2] },
    end,
    .. lift f },
  inv_fun := λ F, monoid_hom.comp ↑F of_mul_hom,
  left_inv := λ f, monoid_hom.ext $ lift.of _,
  right_inv := λ F, ring_hom.coe_add_monoid_hom_injective $
    lift.apply_symm_apply (↑F : free_abelian_group α →+ R) }

@[simp] lemma lift_monoid_coe_add_monoid_hom (f : α →* R) : ↑(lift_monoid f) = lift f := rfl

@[simp] lemma lift_monoid_coe (f : α →* R) : ⇑(lift_monoid f) = lift f := rfl

@[simp] lemma lift_monoid_symm_coe (f : free_abelian_group α →+* R) :
  ⇑(lift_monoid.symm f) = lift.symm ↑f := rfl

lemma one_def : (1 : free_abelian_group α) = of 1 := rfl
lemma of_one : (of 1 : free_abelian_group α) = 1 := rfl

end monoid

instance [comm_monoid α] : comm_ring (free_abelian_group α) :=
{ mul_comm := λ x y, begin
    refine free_abelian_group.induction_on x (zero_mul y) _ _ _,
    { intros s, refine free_abelian_group.induction_on y (zero_mul _).symm _ _ _,
      { intros t, unfold has_mul.mul semigroup.mul ring.mul,
        iterate 4 { rw lift.of }, congr' 1, exact mul_comm _ _ },
      { intros t ih, rw [mul_neg, ih, neg_mul_eq_neg_mul] },
      { intros y1 y2 ih1 ih2, rw [mul_add, add_mul, ih1, ih2] } },
    { intros s ih, rw [neg_mul, ih, neg_mul_eq_mul_neg] },
    { intros x1 x2 ih1 ih2, rw [add_mul, mul_add, ih1, ih2] }
  end,
  .. free_abelian_group.ring α }

instance pempty_unique : unique (free_abelian_group pempty) :=
{ default := 0,
  uniq := λ x, free_abelian_group.induction_on x rfl
    (λ x, pempty.elim x)
    (λ x, pempty.elim x)
    (by { rintros - - rfl rfl, simp }) }

/-- The free abelian group on a type with one term is isomorphic to `ℤ`. -/
def punit_equiv (T : Type*) [unique T] : free_abelian_group T ≃+ ℤ :=
{ to_fun := free_abelian_group.lift (λ _, (1 : ℤ)),
  inv_fun := λ n, n • of (inhabited.default),
  left_inv := λ z, free_abelian_group.induction_on z
    (by simp only [zero_smul, add_monoid_hom.map_zero])
    (unique.forall_iff.2 $ by simp only [one_smul, lift.of])
    (unique.forall_iff.2 $ by simp)
    (λ x y hx hy, by { simp only [add_monoid_hom.map_add, add_smul] at *, rw [hx, hy]}),
  right_inv := λ n,
  begin
    rw [add_monoid_hom.map_zsmul, lift.of],
    exact zsmul_int_one n
  end,
  map_add' := add_monoid_hom.map_add _ }

/-- Isomorphic types have isomorphic free abelian groups. -/
def equiv_of_equiv {α β : Type*} (f : α ≃ β) : free_abelian_group α ≃+ free_abelian_group β :=
{ to_fun := map f,
  inv_fun := map f.symm,
  left_inv := begin
    intros x,
    rw [← map_comp_apply, equiv.symm_comp_self, map_id],
    refl,
  end,
  right_inv := begin
    intros x,
    rw [← map_comp_apply, equiv.self_comp_symm, map_id],
    refl,
  end,
  map_add' := add_monoid_hom.map_add _ }

end free_abelian_group
