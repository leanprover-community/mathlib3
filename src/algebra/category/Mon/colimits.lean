/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Mon.basic
import category_theory.limits.has_limits
import category_theory.limits.concrete_category
import category_theory.limits.types
import category_theory.limits.preserves.filtered

/-!
# The category of monoids has all colimits.

We do this construction knowing nothing about monoids.
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

universes v

open category_theory
open category_theory.limits

namespace Mon.colimits
/-!
We build the colimit of a diagram in `Mon` by constructing the
free monoid on the disjoint union of all the monoids in the diagram,
then taking the quotient by the monoid laws within each monoid,
and the identifications given by the morphisms in the diagram.
-/

variables {J : Type v} [small_category J] (F : J ⥤ Mon.{v})

/--
An inductive type representing all monoid expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive prequotient
-- There's always `of`
| of : Π (j : J) (x : F.obj j), prequotient
-- Then one generator for each operation
| one : prequotient
| mul : prequotient → prequotient → prequotient

instance : inhabited (prequotient F) := ⟨prequotient.one⟩

open prequotient

/--
The relation on `prequotient` saying when two expressions are equal
because of the monoid laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive relation : prequotient F → prequotient F → Prop
-- Make it an equivalence relation:
| refl : Π (x), relation x x
| symm : Π (x y) (h : relation x y), relation y x
| trans : Π (x y z) (h : relation x y) (k : relation y z), relation x z
-- There's always a `map` relation
| map : Π (j j' : J) (f : j ⟶ j') (x : F.obj j), relation (of j' ((F.map f) x)) (of j x)
-- Then one relation per operation, describing the interaction with `of`
| mul : Π (j) (x y : F.obj j), relation (of j (x * y)) (mul (of j x) (of j y))
| one : Π (j), relation (of j 1) one
-- Then one relation per argument of each operation
| mul_1 : Π (x x' y) (r : relation x x'), relation (mul x y) (mul x' y)
| mul_2 : Π (x y y') (r : relation y y'), relation (mul x y) (mul x y')
-- And one relation per axiom
| mul_assoc : Π (x y z), relation (mul (mul x y) z) (mul x (mul y z))
| one_mul : Π (x), relation (mul one x) x
| mul_one : Π (x), relation (mul x one) x

/--
The setoid corresponding to monoid expressions modulo monoid relations and identifications.
-/
def colimit_setoid : setoid (prequotient F) :=
{ r := relation F, iseqv := ⟨relation.refl, relation.symm, relation.trans⟩ }
attribute [instance] colimit_setoid

/--
The underlying type of the colimit of a diagram in `Mon`.
-/
@[derive inhabited]
def colimit_type : Type v := quotient (colimit_setoid F)

instance monoid_colimit_type : monoid (colimit_type F) :=
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
@[simp] lemma quot_mul (x y) : quot.mk setoid.r (mul x y) =
  ((quot.mk setoid.r x) * (quot.mk setoid.r y) : colimit_type F) := rfl

/-- The bundled monoid giving the colimit of a diagram. -/
def colimit : Mon := ⟨colimit_type F, by apply_instance⟩

/-- The function from a given monoid in the diagram to the colimit monoid. -/
def cocone_fun (j : J) (x : F.obj j) : colimit_type F :=
quot.mk _ (of j x)

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
def cocone_morphism (j : J) : F.obj j ⟶ colimit F :=
{ to_fun := cocone_fun F j,
  map_one' := quot.sound (relation.one _),
  map_mul' := λ x y, quot.sound (relation.mul _ _ _) }

@[simp] lemma cocone_naturality {j j' : J} (f : j ⟶ j') :
  F.map f ≫ (cocone_morphism F j') = cocone_morphism F j :=
begin
  ext,
  apply quot.sound,
  apply relation.map,
end

@[simp] lemma cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j):
  (cocone_morphism F j') (F.map f x) = (cocone_morphism F j) x :=
by { rw ←cocone_naturality F f, refl }

/-- The cocone over the proposed colimit monoid. -/
def colimit_cocone : cocone F :=
{ X := colimit F,
  ι :=
  { app := cocone_morphism F, } }.

/-- The function from the free monoid on the diagram to the cone point of any other cocone. -/
@[simp] def desc_fun_lift (s : cocone F) : prequotient F → s.X
| (of j x)  := (s.ι.app j) x
| one       := 1
| (mul x y) := desc_fun_lift x * desc_fun_lift y

/-- The function from the colimit monoid to the cone point of any other cocone. -/
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
    { simp, },
    -- mul
    { simp, },
    -- one
    { simp, },
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

/-- The monoid homomorphism from the colimit monoid to the cone point of any other cocone. -/
def desc_morphism (s : cocone F) : colimit F ⟶ s.X :=
{ to_fun := desc_fun F s,
  map_one' := rfl,
  map_mul' := λ x y, by { induction x; induction y; refl }, }

/-- Evidence that the proposed colimit is the colimit. -/
def colimit_cocone_is_colimit : is_colimit (colimit_cocone F) :=
{ desc := λ s, desc_morphism F s,
  uniq' := λ s m w,
  begin
    ext,
    induction x,
    induction x,
    { have w' := congr_fun (congr_arg (λ f : F.obj x_j ⟶ s.X, (f : F.obj x_j → s.X)) (w x_j)) x_x,
      erw w',
      refl, },
    { simp *, },
    { simp *, },
    refl
  end }.

instance has_colimits_Mon : has_colimits Mon :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk
    { cocone := colimit_cocone F,
      is_colimit := colimit_cocone_is_colimit F } } }

instance monoid_comp_forget (j : J) : monoid ((F ⋙ forget Mon).obj j) :=
by { change monoid (F.obj j), apply_instance, }

@[simps]
def one_nat_trans : (F ⋙ forget Mon) ⋙ types.star ⟶ F ⋙ forget Mon :=
{ app := λ j p, 1, }

@[simps]
def mul_nat_trans : (F ⋙ forget Mon) ⋙ types.diagonal ⟶ F ⋙ forget Mon :=
{ app := λ j p, p.1 * p.2, }

@[simps]
def mul_one_nat_trans : (F ⋙ forget Mon) ⟶ (F ⋙ forget Mon) ⋙ types.Prop :=
{ app := λ j p, ⟨p * 1 = p⟩, }

@[simps]
def mul_assoc_nat_trans : (F ⋙ forget Mon) ⋙ types.triple_diagonal ⟶ (F ⋙ forget Mon) ⋙ types.Prop :=
{ app := λ j p, ⟨(p.1 * p.2.1) * p.2.2 = p.1 * (p.2.1 * p.2.2)⟩,
  naturality' := λ j j' f,
  begin
    ext ⟨x,y,z⟩,
    dsimp,
    split,
    { intro h, simp only [mul_assoc], },
    { intro h, simp only [←(F.map f).map_mul, h], },
  end }

noncomputable
def one_colimit [is_filtered J] (F : J ⥤ Mon) :
  punit.{v+1} ⟶ limits.colimit (F ⋙ forget Mon) :=
(preserves_colimit_iso' (F ⋙ forget Mon) types.star).hom ≫ colim.map (one_nat_trans F)

noncomputable
def mul_colimit [is_filtered J] (F : J ⥤ Mon) :
  types.diagonal.obj (limits.colimit (F ⋙ forget Mon)) ⟶ limits.colimit (F ⋙ forget Mon) :=
(preserves_colimit_iso' (F ⋙ forget Mon) types.diagonal).hom ≫ colim.map (mul_nat_trans F)

noncomputable
def mul_assoc_colimit [is_filtered J] (F : J ⥤ Mon) :
  types.triple_diagonal.obj (limits.colimit (F ⋙ forget Mon)) ⟶ ulift Prop :=
(preserves_colimit_iso' (F ⋙ forget Mon) types.triple_diagonal).hom ≫
  colim.map (mul_assoc_nat_trans F) ≫
  (preserves_colimit_iso' (F ⋙ forget Mon) types.Prop).inv

lemma desc_comp_star (F : J ⥤ Type v) (s) (x) :
  ∃ j : J, colimit.desc (F ⋙ types.star) s x = s.ι.app j punit.star :=
begin
  obtain ⟨j, ⟨⟩, rfl⟩ := types.jointly_surjective _ (colimit.is_colimit _) x,
  exact ⟨j, rfl⟩,
end

lemma desc_comp_star' [is_filtered J] (F : J ⥤ Type v) (s) (x) (j) :
  colimit.desc (F ⋙ types.star) s x = s.ι.app j punit.star :=
begin
  obtain ⟨j', e⟩ := desc_comp_star F s x,
  rw e, clear e,
  rw [←s.w (is_filtered.left_to_sup j j'), ←s.w (is_filtered.right_to_sup j j')],
  simp,
end

@[simp]
lemma desc_comp_star'' [is_filtered J] (F : J ⥤ Type v) (s) (x) :
  colimit.desc (F ⋙ types.star) s x = s.ι.app (is_filtered.nonempty.some) punit.star :=
desc_comp_star' F s x _

lemma inv_desc_comp_diagonal (F : J ⥤ Type v) (s : cocone F)
  [is_iso (colimit.desc (F ⋙ types.diagonal) (types.diagonal.map_cocone s))]
  {j₁ j₂ : J} (x₁ : F.obj j₁) (x₂ : F.obj j₂)
  {j : J} (i₁ : j₁ ⟶ j) (i₂ : j₂ ⟶ j) :
  inv (colimit.desc (F ⋙ types.diagonal) (types.diagonal.map_cocone s))
    (s.ι.app j₁ x₁, s.ι.app j₂ x₂) = colimit.ι (F ⋙ types.diagonal) j (F.map i₁ x₁, F.map i₂ x₂) :=
begin
  sorry,
end

lemma inv_desc_comp_diagonal' (F : J ⥤ Type v) (s : cocone F)
  [is_iso (colimit.desc (F ⋙ types.diagonal) (types.diagonal.map_cocone s))]
  {j : J} (x₁ : F.obj j) (x₂ : F.obj j) :
  inv (colimit.desc (F ⋙ types.diagonal) (types.diagonal.map_cocone s))
    (s.ι.app j x₁, s.ι.app j x₂) = colimit.ι (F ⋙ types.diagonal) j (x₁, x₂) :=
by simpa using inv_desc_comp_diagonal F s x₁ x₂ (𝟙 _) (𝟙 _)

lemma inv_desc_comp_diagonal'' [is_filtered J] (F : J ⥤ Type v) (s : cocone F)
  [is_iso (colimit.desc (F ⋙ types.diagonal) (types.diagonal.map_cocone s))]
  {j₁ j₂ : J} (x₁ : F.obj j₁) (x₂ : F.obj j₂)  :
  inv (colimit.desc (F ⋙ types.diagonal) (types.diagonal.map_cocone s))
    (s.ι.app j₁ x₁, s.ι.app j₂ x₂) =
    colimit.ι (F ⋙ types.diagonal) (is_filtered.sup j₁ j₂)
      (F.map (is_filtered.left_to_sup j₁ j₂) x₁, F.map (is_filtered.right_to_sup j₁ j₂) x₂) :=
inv_desc_comp_diagonal F s x₁ x₂ _ _

@[simp]
lemma inv_desc_comp_diagonal''' [is_filtered J] (F : J ⥤ Type v)
  [is_iso (colimit.desc (F ⋙ types.diagonal) (types.diagonal.map_cocone (colimit.cocone F)))]
  {j₁ j₂ : J} (x₁ : F.obj j₁) (x₂ : F.obj j₂)  :
  inv (colimit.desc (F ⋙ types.diagonal) (types.diagonal.map_cocone (colimit.cocone F)))
    (colimit.ι F j₁ x₁, colimit.ι F j₂ x₂) =
    colimit.ι (F ⋙ types.diagonal) (is_filtered.sup j₁ j₂)
      (F.map (is_filtered.left_to_sup j₁ j₂) x₁, F.map (is_filtered.right_to_sup j₁ j₂) x₂) :=
inv_desc_comp_diagonal'' F (colimit.cocone F) _ _

noncomputable
instance [is_filtered J] : monoid (limits.colimit (F ⋙ forget Mon)) :=
{ one := one_colimit F punit.star,
  mul := λ x y, mul_colimit F (x, y),
  one_mul := λ x,
  begin
    obtain ⟨j, x, rfl⟩ := types.jointly_surjective' _ x,
    dsimp [(*), mul_colimit, one_colimit],
    dunfold preserves_colimit_iso',
    dsimp [preserves_colimit_iso, is_colimit.cocone_point_unique_up_to_iso],
    dsimp [colim, colim_map, is_colimit.map],
    simp,
  end,
  mul_one := sorry,
  mul_assoc := λ x y z,
  begin
    obtain ⟨jx, x, rfl⟩ := types.jointly_surjective' _ x,
    obtain ⟨jy, y, rfl⟩ := types.jointly_surjective' _ y,
    obtain ⟨jz, z, rfl⟩ := types.jointly_surjective' _ z,
    dsimp [(*), mul_colimit, one_colimit],
    dunfold preserves_colimit_iso',
    dsimp [preserves_colimit_iso, is_colimit.cocone_point_unique_up_to_iso],
    dsimp [colim, colim_map, is_colimit.map],
    simp [monoid_hom.map_mul],
    rw [mul_assoc],

    sorry,
  end, }

end Mon.colimits
