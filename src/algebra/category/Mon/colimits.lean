/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Mon.basic
import category_theory.limits.has_limits
import category_theory.limits.concrete_category
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
    { simp *, },
    { simp *, },
    refl
  end }.

instance has_colimits_Mon : has_colimits Mon :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk
    { cocone := colimit_cocone F,
      is_colimit := colimit_is_colimit F } } }

end Mon.colimits

namespace Mon.filtered_colimits

open category_theory.is_filtered (renaming max → max')

section

parameters {J : Type v} [small_category J] (F : J ⥤ Mon.{v})

local infixl `~` := types.filtered_colimit.rel (F ⋙ forget Mon)

abbreviation M : Type v := types.quot (F ⋙ forget Mon)
abbreviation M.mk : (Σ j, F.obj j) → M := quot.mk (types.quot.rel (F ⋙ forget Mon))

noncomputable theory
open_locale classical

variables [is_filtered J]

instance monoid_obj (j) : monoid ((F ⋙ forget Mon).obj j) :=
by { change monoid (F.obj j), apply_instance }

def colimit_one : M := M.mk ⟨is_filtered.nonempty.some, 1⟩

lemma colimit_one_eq' (j : J) : colimit_one = M.mk ⟨j, 1⟩ :=
begin
  apply quot.eqv_gen_sound,
  apply types.filtered_colimit.eqv_gen_quot_rel_of_rel,
  refine ⟨is_filtered.max _ _, is_filtered.left_to_max _ _, is_filtered.right_to_max _ _, _⟩,
  simp,
end

def colimit_mul_aux (x y : Σ j, F.obj j) : M :=
M.mk ⟨is_filtered.max x.1 y.1,
  F.map (is_filtered.left_to_max x.1 y.1) x.2 * F.map (is_filtered.right_to_max x.1 y.1) y.2⟩

lemma colimit_mul_aux_eq_of_rel_left {x x' y : Σ j, F.obj j} (hxx' : x ~ x') :
  colimit_mul_aux x y = colimit_mul_aux x' y :=
begin
  cases x with j₁ x, cases y with j₂ y, cases x' with j₃ x',
  obtain ⟨l, f, g, hfg⟩ := hxx',
  simp at hfg,
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ := crown (left_to_max j₁ j₂) (right_to_max j₁ j₂)
    (right_to_max j₃ j₂) (left_to_max j₃ j₂) f g,
  apply quot.eqv_gen_sound,
  apply types.filtered_colimit.eqv_gen_quot_rel_of_rel,
  use [s, α, γ],
  dsimp,
  simp_rw [monoid_hom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp, comp_apply, hfg]
end

lemma colimit_mul_aux_eq_of_rel_right {x y y' : Σ j, F.obj j} (hyy' : y ~ y') :
  colimit_mul_aux x y = colimit_mul_aux x y' :=
begin
  cases y with j₁ y, cases x with j₂ x, cases y' with j₃ y',
  obtain ⟨l, f, g, hfg⟩ := hyy',
  simp at hfg,
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ := crown (right_to_max j₂ j₁) (left_to_max j₂ j₁)
    (left_to_max j₂ j₃) (right_to_max j₂ j₃) f g,
  apply quot.eqv_gen_sound,
  apply types.filtered_colimit.eqv_gen_quot_rel_of_rel,
  use [s, α, γ],
  dsimp,
  simp_rw [monoid_hom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp, comp_apply, hfg]
end

def colimit_mul (x y : M) : M :=
begin
  refine quot.lift₂ (colimit_mul_aux F) _ _ x y,
  { intros x y y' h,
    apply colimit_mul_aux_eq_of_rel_right,
    apply types.filtered_colimit.rel_of_quot_rel,
    exact h },
  { intros x x' y h,
    apply colimit_mul_aux_eq_of_rel_left,
    apply types.filtered_colimit.rel_of_quot_rel,
    exact h },
end

lemma colimit_mul_eq' (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
  colimit_mul (quot.mk _ x) (quot.mk _ y) = quot.mk _ ⟨k, F.map f x.2 * F.map g y.2⟩ :=
begin
  cases x with j₁ x, cases y with j₂ y,
  obtain ⟨s, α, β, h₁, h₂⟩ := bowtie (left_to_max j₁ j₂) f (right_to_max j₁ j₂) g,
  apply quot.eqv_gen_sound,
  apply types.filtered_colimit.eqv_gen_quot_rel_of_rel,
  use [s, α, β],
  dsimp,
  simp_rw [monoid_hom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂],
end

lemma colimit_one_mul (x : M) : colimit_mul colimit_one x = x :=
begin
  apply quot.induction_on x, clear x, intro x,
  cases x with j x,
  rw [colimit_one_eq' F j, colimit_mul_eq' F ⟨j, 1⟩ ⟨j, x⟩ j (𝟙 j) (𝟙 j),
    monoid_hom.map_one, one_mul, F.map_id, id_apply],
end

lemma colimit_mul_one (x : types.quot (F ⋙ forget Mon)) :
  colimit_mul x colimit_one = x :=
begin
  apply quot.induction_on x, clear x, intro x,
  cases x with j x,
  rw [colimit_one_eq' F j, colimit_mul_eq' F ⟨j, x⟩ ⟨j, 1⟩ j (𝟙 j) (𝟙 j),
    monoid_hom.map_one, mul_one, F.map_id, id_apply],
end

lemma colimit_mul_assoc (x y z : M) :
  colimit_mul (colimit_mul x y) z = colimit_mul x (colimit_mul y z) :=
begin
  apply quot.induction_on₃ x y z, clear x y z, intros x y z,
  cases x with j₁ x, cases y with j₂ y, cases z with j₃ z,
  rw [colimit_mul_eq' F ⟨j₁, x⟩ ⟨j₂, y⟩ _ (first_to_max₃ j₁ j₂ j₃) (second_to_max₃ j₁ j₂ j₃),
    colimit_mul_eq' F ⟨max₃ j₁ j₂ j₃, _⟩ ⟨j₃, z⟩ _ (𝟙 _) (third_to_max₃ j₁ j₂ j₃),
    colimit_mul_eq' F ⟨j₂, y⟩ ⟨j₃, z⟩ _ (second_to_max₃ j₁ j₂ j₃) (third_to_max₃ j₁ j₂ j₃),
    colimit_mul_eq' F ⟨j₁, x⟩ ⟨max₃ j₁ j₂ j₃, _⟩ _ (first_to_max₃ j₁ j₂ j₃) (𝟙 _)],
  simp only [F.map_id, id_apply, mul_assoc],
end

instance colimit_monoid : monoid M :=
{ one := colimit_one,
  mul := colimit_mul,
  one_mul := colimit_one_mul,
  mul_one := colimit_mul_one,
  mul_assoc := colimit_mul_assoc }

lemma colimit_one_eq (j : J) : (1 : M) = M.mk ⟨j, 1⟩ :=
colimit_one_eq' j

lemma colimit_mul_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
  M.mk x * M.mk y = M.mk ⟨k, F.map f x.2 * F.map g y.2⟩ :=
colimit_mul_eq' x y k f g

/-- The bundled monoid giving the colimit of a diagram. -/
def colimit : Mon := ⟨M, by apply_instance⟩

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
def cocone_morphism (j : J) : F.obj j ⟶ colimit :=
{ to_fun := (types.colimit_cocone (F ⋙ forget Mon)).ι.app j,
  map_one' := (colimit_one_eq j).symm,
  map_mul' := λ x y, begin
    convert (colimit_mul_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 j) (𝟙 j)).symm,
    rw [F.map_id, id_apply, id_apply], refl,
  end }

@[simp] lemma cocone_naturality {j j' : J} (f : j ⟶ j') :
  F.map f ≫ (cocone_morphism j') = cocone_morphism j :=
monoid_hom.coe_inj ((types.colimit_cocone (F ⋙ forget Mon)).ι.naturality f)

/-- The cocone over the proposed colimit monoid. -/
def colimit_cocone : cocone F :=
{ X := colimit,
  ι := { app := cocone_morphism } }.

def colimit_desc (t : cocone F) : colimit ⟶ t.X :=
{ to_fun := (types.colimit_cocone_is_colimit (F ⋙ forget Mon)).desc ((forget Mon).map_cocone t),
  map_one' := begin
    rw colimit_one_eq F is_filtered.nonempty.some,
    exact monoid_hom.map_one _,
  end,
  map_mul' := λ x y, begin
    apply quot.induction_on₂ x y, clear x y, intros x y,
    cases x with i x, cases y with j y,
    rw colimit_mul_eq F ⟨i, x⟩ ⟨j, y⟩ (max' i j) (left_to_max i j) (right_to_max i j),
    dsimp [types.colimit_cocone_is_colimit],
    rw [monoid_hom.map_mul, t.w_apply, t.w_apply],
  end }

def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := colimit_desc,
  fac' := λ t j, monoid_hom.coe_inj
    ((types.colimit_cocone_is_colimit (F ⋙ forget Mon)).fac ((forget Mon).map_cocone t) j),
  uniq' := λ t m h, begin
    apply monoid_hom.coe_inj,
    refine (types.colimit_cocone_is_colimit (F ⋙ forget Mon)).uniq ((forget Mon).map_cocone t) m _,
    intro j,
    ext x,
    exact monoid_hom.congr_fun (h j) x,
  end }

instance forget_preserves_filtered_colimits : preserves_filtered_colimits (forget Mon) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F) (types.colimit_cocone_is_colimit (F ⋙ forget Mon)) } }

end

end Mon.filtered_colimits
