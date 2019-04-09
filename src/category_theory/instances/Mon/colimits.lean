import category_theory.instances.monoids
import category_theory.limits.limits

universes v

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

namespace category_theory.instances.Mon.colimits

variables {J : Type v} [small_category J] (F : J ⥤ Mon.{v})

inductive prequotient
-- There's always `of`
| of : Π (j : J) (x : (F.obj j).α), prequotient
-- Then one generator for each operation
| one {} : prequotient
| mul : prequotient → prequotient → prequotient

open prequotient

inductive relation : prequotient F → prequotient F → Prop
-- Make it an equivalence relation:
| refl : Π (x), relation x x
| symm : Π (x y) (h : relation x y), relation y x
| trans : Π (x y z) (h : relation x y) (k : relation y z), relation x z
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

def colimit_setoid : setoid (prequotient F) :=
{ r := relation F, iseqv := ⟨relation.refl, relation.symm, relation.trans⟩ }
attribute [instance] colimit_setoid

def colimit_type : Type v := quotient (colimit_setoid F)

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

@[simp] lemma quot_one : quot.mk setoid.r one = (1 : colimit_type F) := rfl
@[simp] lemma quot_mul (x y) : quot.mk setoid.r (mul x y) = ((quot.mk setoid.r x) * (quot.mk setoid.r y) : colimit_type F) := rfl

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

@[simp] lemma cocone_naturality {j j' : J} (f : j ⟶ j') :
  F.map f ≫ (cocone_morphism F j') = cocone_morphism F j :=
begin
  ext,
  apply quot.sound,
  apply relation.map,
end

@[simp] lemma cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j):
  (F.map f ≫ (cocone_morphism F j')) x = (cocone_morphism F j) x :=
by rw cocone_naturality

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
    induction r; try { dsimp },
    -- refl
    { refl },
    -- symm
    { exact r_ih.symm },
    -- trans
    { exact eq.trans r_ih_h r_ih_k },
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

def colimit_is_colimit : is_colimit (colimit_cocone F) :=
{ desc := λ s, desc_morphism F s,
  uniq' := λ s m w,
  begin
    ext,
    induction x,
    induction x,
    { have w' := congr_fun (congr_arg (λ f : F.obj x_j ⟶ s.X, (f : F.obj x_j → s.X)) (w x_j)) x_x,
      erw w',
      refl, },
    { simp only [desc_morphism, quot_one],
      erw is_monoid_hom.map_one ⇑m,
      refl, },
    { simp only [desc_morphism, quot_mul],
      erw is_monoid_hom.map_mul ⇑m,
      rw [x_ih_a, x_ih_a_1],
      refl, },
    refl
  end }.

-- FIXME why is this infer_instance needed!?
instance has_colimits_Mon : @has_colimits Mon.{v} infer_instance :=
{ has_colimits_of_shape := λ J 𝒥,
  { has_colimit := λ F, by resetI; exact
    { cocone := colimit_cocone F,
      is_colimit := colimit_is_colimit F } } }

end category_theory.instances.Mon.colimits
