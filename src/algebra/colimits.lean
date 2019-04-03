import category_theory.instances.monoids
import category_theory.limits.limits

universes u v

lemma subtype.ext' {α : Sort u} {p : α → Prop} {a b : {x // p x}} (h : a.val = b.val) : a = b :=
subtype.ext.2 h

open category_theory
open category_theory.instances
open category_theory.limits

/-
We build colimits of monoids.

We do so knowing nothing about monoids.
In particular, I want to claim that this file could be produced by a python script
that just looks at the output of `#print monoid`:

  -- structure monoid : Type u → Type u
  -- fields:
  -- monoid.mul : Π {α : Type u} [c : monoid α], α → α → α
  -- monoid.mul_assoc : ∀ {α : Type u} [c : monoid α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
  -- monoid.one : Π (α : Type u) [c : monoid α], α
  -- monoid.one_mul : ∀ {α : Type u} [c : monoid α] (a : α), 1 * a = a
  -- monoid.mul_one : ∀ {α : Type u} [c : monoid α] (a : α), a * 1 = a

and if we'd fed it the output of `#print comm_ring`, this file would instead build
colimits of commutative rings.

A slightly bolder claim is that we could do this with tactics, as well.
-/

namespace monoid.colimits

variables {J : Type v} [small_category J] (F : J ⥤ Mon.{v})

inductive prequotient
-- There's always `of`
| of : Π (j : J) (x : (F.obj j).α), prequotient
-- Then one generator for each operation
| one {} : prequotient
| mul : prequotient → prequotient → prequotient

open prequotient

inductive relation : prequotient F → prequotient F → Prop
-- There's always a `map` relation
| map : Π (j j' : J) (f : j ⟶ j') (x : (F.obj j).α), relation (of j' ((F.map f) x)) (of j x)
-- Then one relation per operation, describing the interaction with `of`
| mul : Π (j) (x y : (F.obj j).α), relation (of j (x * y)) (mul (of j x) (of j y))
| one : Π (j), relation (of j 1) one
-- Then one relation per argument of each operation
| mul_1 : Π (x x' y) (r : relation x x'), relation (mul x y) (mul x' y)
| mul_2 : Π (x y y') (r : relation y y'), relation (mul x y) (mul x y')
-- And one relation per axiom
| mul_assoc : Π (x y z), relation (mul (mul x y) z) (mul x (mul y z))
| one_mul : Π (x), relation (mul one x) x
| mul_one : Π (x), relation (mul x one) x

def colimit_type : Type v := quot (relation F)

instance : monoid (colimit_type F) :=
{ mul :=
  begin
    fapply @quot.lift _ _ ((colimit_type F) → (colimit_type F)),
    { intro x,
      fapply @quot.lift,
      { intro y,
        exact quot.mk _ (mul x y) },
      { intros y y' r,
        apply quot.sound,
        exact relation.mul_2 _ _ _ r } },
    { intros x x' r,
      funext y,
      induction y,
      dsimp,
      apply quot.sound,
      { exact relation.mul_1 _ _ _ r },
      { refl } },
  end,
  one :=
  begin
    exact quot.mk _ one
  end,
  mul_assoc := λ x y z,
  begin
    induction x,
    induction y,
    induction z,
    dsimp,
    apply quot.sound,
    apply relation.mul_assoc,
    refl,
    refl,
    refl,
  end,
  one_mul := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.one_mul,
    refl,
  end,
  mul_one := λ x,
  begin
    induction x,
    dsimp,
    apply quot.sound,
    apply relation.mul_one,
    refl,
  end }

@[simp] lemma quot_one : quot.mk (relation F) one = (1 : colimit_type F) := rfl
@[simp] lemma quot_mul (x y) : quot.mk (relation F) (mul x y) = ((quot.mk _ x) * (quot.mk _ y) : colimit_type F) := rfl

def colimit : Mon := ⟨colimit_type F, by apply_instance⟩

def cocone_fun (j : J) (x : (F.obj j).α) : colimit_type F :=
quot.mk _ (of j x)

instance cocone_is_hom (j : J) : is_monoid_hom (cocone_fun F j) :=
{ map_one :=
  begin
    apply quot.sound,
    apply relation.one,
  end,
  map_mul := λ x y,
  begin
    apply quot.sound,
    apply relation.mul,
  end }

def cocone_morphism (j : J) : F.obj j ⟶ colimit F :=
{ val := cocone_fun F j,
  property := by apply_instance }

section
local attribute [extensionality] subtype.ext'
@[simp] lemma cocone_naturality (j j' : J) (f : j ⟶ j') :
  F.map f ≫ (cocone_morphism F j') = cocone_morphism F j :=
begin
  ext,
  dsimp,
  apply quot.sound,
  apply relation.map,
end
end

def colimit_cocone : cocone F :=
{ X := colimit F,
  ι :=
  { app := cocone_morphism F, } }.

@[simp] def desc_fun_lift (s : cocone F) : prequotient F → s.X
| (of j x)  := (s.ι.app j) x
| one       := 1
| (mul x y) := desc_fun_lift x * desc_fun_lift y

def desc_fun (s : cocone F) : colimit_type F → s.X :=
begin
  fapply quot.lift,
  { exact desc_fun_lift F s },
  { intros x y r,
    induction r; dsimp,
    -- map
    { rw cocone.naturality_bundled, },
    -- mul
    { rw is_monoid_hom.map_mul ⇑((s.ι).app r_j) },
    -- one
    { erw is_monoid_hom.map_one ⇑((s.ι).app r), refl },
    -- mul_1
    { rw r_ih, },
    -- mul_2
    { rw r_ih, },
    -- mul_assoc
    { rw mul_assoc, },
    -- one_mul
    { rw one_mul, },
    -- mul_one
    { rw mul_one, } }
end

instance desc_fun_is_morphism (s : cocone F) : is_monoid_hom (desc_fun F s) :=
{ map_one := rfl,
  map_mul := λ x y,
  begin
    induction x, induction y,
    refl,
    refl,
    refl,
  end, }

@[simp] def desc_morphism (s : cocone F) : colimit F ⟶ s.X :=
{ val := desc_fun F s,
  property := by apply_instance }

local attribute [extensionality] subtype.ext'
def colimit_is_colimit : is_colimit (colimit_cocone F) :=
{ desc := λ s, desc_morphism F s,
  uniq' := λ s m w,
  begin
    ext, -- TODO write a better ext, for morphisms in concrete categories, that uses the coercion rather than .val
    induction x,
    induction x,
    { dsimp,
      have w' := congr_fun (congr_arg subtype.val (w x_j)) x_x,
      dsimp at w',
      erw w',
      refl },
    { simp,
      erw is_monoid_hom.map_one m.val,
      erw is_monoid_hom.map_one (desc_fun F s),
      refl },
    { simp,
      erw is_monoid_hom.map_mul m.val,
      erw is_monoid_hom.map_mul (desc_fun F s),
      rw [x_ih_a, x_ih_a_1],
      refl },
    refl
  end }

end monoid.colimits
