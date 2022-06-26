/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import algebra.category.Mon.basic
import category_theory.limits.concrete_category
import category_theory.limits.preserves.filtered

/-!
# The forgetful functor from (commutative) (additive) monoids preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ Mon`.
We then construct a monoid structure on the colimit of `F ⋙ forget Mon` (in `Type`), thereby
showing that the forgetful functor `forget Mon` preserves filtered colimits. Similarly for `AddMon`,
`CommMon` and `AddCommMon`.

-/

universes v u

noncomputable theory
open_locale classical

open category_theory
open category_theory.limits
open category_theory.is_filtered (renaming max → max') -- avoid name collision with `_root_.max`.

namespace Mon.filtered_colimits

section

-- We use parameters here, mainly so we can have the abbreviations `M` and `M.mk` below, without
-- passing around `F` all the time.
parameters {J : Type v} [small_category J] (F : J ⥤ Mon.{max v u})

/--
The colimit of `F ⋙ forget Mon` in the category of types.
In the following, we will construct a monoid structure on `M`.
-/
@[to_additive "The colimit of `F ⋙ forget AddMon` in the category of types.
In the following, we will construct an additive monoid structure on `M`."]
abbreviation M : Type (max v u) := types.quot (F ⋙ forget Mon)

/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive "The canonical projection into the colimit, as a quotient type."]
abbreviation M.mk : (Σ j, F.obj j) → M := quot.mk (types.quot.rel (F ⋙ forget Mon))

@[to_additive]
lemma M.mk_eq (x y : Σ j, F.obj j)
  (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
  M.mk x = M.mk y :=
quot.eqv_gen_sound (types.filtered_colimit.eqv_gen_quot_rel_of_rel (F ⋙ forget Mon) x y h)

variables [is_filtered J]

/--
As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to define the
"one" in the colimit as the equivalence class of `⟨j₀, 1 : F.obj j₀⟩`.
-/
@[to_additive "As `J` is nonempty, we can pick an arbitrary object `j₀ : J`. We use this object to
define the \"zero\" in the colimit as the equivalence class of `⟨j₀, 0 : F.obj j₀⟩`."]
instance colimit_has_one : has_one M :=
{ one := M.mk ⟨is_filtered.nonempty.some, 1⟩ }

/--
The definition of the "one" in the colimit is independent of the chosen object of `J`.
In particular, this lemma allows us to "unfold" the definition of `colimit_one` at a custom chosen
object `j`.
-/
@[to_additive "The definition of the \"zero\" in the colimit is independent of the chosen object
of `J`. In particular, this lemma allows us to \"unfold\" the definition of `colimit_zero` at a
custom chosen object `j`."]
lemma colimit_one_eq (j : J) : (1 : M) = M.mk ⟨j, 1⟩ :=
begin
  apply M.mk_eq,
  refine ⟨max' _ j, left_to_max _ j, right_to_max _ j, _⟩,
  simp,
end

/--
The "unlifted" version of multiplication in the colimit. To multiply two dependent pairs
`⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂` (given by `is_filtered.max`)
and multiply them there.
-/
@[to_additive "The \"unlifted\" version of addition in the colimit. To add two dependent pairs
`⟨j₁, x⟩` and `⟨j₂, y⟩`, we pass to a common successor of `j₁` and `j₂` (given by `is_filtered.max`)
and add them there."]
def colimit_mul_aux (x y : Σ j, F.obj j) : M :=
M.mk ⟨max' x.1 y.1, F.map (left_to_max x.1 y.1) x.2 * F.map (right_to_max x.1 y.1) y.2⟩

/-- Multiplication in the colimit is well-defined in the left argument. -/
@[to_additive "Addition in the colimit is well-defined in the left argument."]
lemma colimit_mul_aux_eq_of_rel_left {x x' y : Σ j, F.obj j}
  (hxx' : types.filtered_colimit.rel (F ⋙ forget Mon) x x') :
  colimit_mul_aux x y = colimit_mul_aux x' y :=
begin
  cases x with j₁ x, cases y with j₂ y, cases x' with j₃ x',
  obtain ⟨l, f, g, hfg⟩ := hxx',
  simp at hfg,
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ := tulip (left_to_max j₁ j₂) (right_to_max j₁ j₂)
    (right_to_max j₃ j₂) (left_to_max j₃ j₂) f g,
  apply M.mk_eq,
  use [s, α, γ],
  dsimp,
  simp_rw [monoid_hom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp, comp_apply, hfg]
end

/-- Multiplication in the colimit is well-defined in the right argument. -/
@[to_additive "Addition in the colimit is well-defined in the right argument."]
lemma colimit_mul_aux_eq_of_rel_right {x y y' : Σ j, F.obj j}
  (hyy' : types.filtered_colimit.rel (F ⋙ forget Mon) y y') :
  colimit_mul_aux x y = colimit_mul_aux x y' :=
begin
  cases y with j₁ y, cases x with j₂ x, cases y' with j₃ y',
  obtain ⟨l, f, g, hfg⟩ := hyy',
  simp at hfg,
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ := tulip (right_to_max j₂ j₁) (left_to_max j₂ j₁)
    (left_to_max j₂ j₃) (right_to_max j₂ j₃) f g,
  apply M.mk_eq,
  use [s, α, γ],
  dsimp,
  simp_rw [monoid_hom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp, comp_apply, hfg]
end

/-- Multiplication in the colimit. See also `colimit_mul_aux`. -/
@[to_additive "Addition in the colimit. See also `colimit_add_aux`."]
instance colimit_has_mul : has_mul M :=
{ mul := λ x y, begin
    refine quot.lift₂ (colimit_mul_aux F) _ _ x y,
  { intros x y y' h,
    apply colimit_mul_aux_eq_of_rel_right,
    apply types.filtered_colimit.rel_of_quot_rel,
    exact h },
  { intros x x' y h,
    apply colimit_mul_aux_eq_of_rel_left,
    apply types.filtered_colimit.rel_of_quot_rel,
    exact h },
  end }

/--
Multiplication in the colimit is independent of the chosen "maximum" in the filtered category.
In particular, this lemma allows us to "unfold" the definition of the multiplication of `x` and `y`,
using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`.
-/
@[to_additive "Addition in the colimit is independent of the chosen \"maximum\" in the filtered
category. In particular, this lemma allows us to \"unfold\" the definition of the addition of `x`
and `y`, using a custom object `k` and morphisms `f : x.1 ⟶ k` and `g : y.1 ⟶ k`."]
lemma colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
  (M.mk x) * (M.mk y) = M.mk ⟨k, F.map f x.2 * F.map g y.2⟩ :=
begin
  cases x with j₁ x, cases y with j₂ y,
  obtain ⟨s, α, β, h₁, h₂⟩ := bowtie (left_to_max j₁ j₂) f (right_to_max j₁ j₂) g,
  apply M.mk_eq,
  use [s, α, β],
  dsimp,
  simp_rw [monoid_hom.map_mul, ← comp_apply, ← F.map_comp, h₁, h₂],
end

@[to_additive]
instance colimit_monoid : monoid M :=
{ one_mul := λ x, begin
    apply quot.induction_on x, clear x, intro x, cases x with j x,
    rw [colimit_one_eq F j, colimit_mul_mk_eq F ⟨j, 1⟩ ⟨j, x⟩ j (𝟙 j) (𝟙 j),
      monoid_hom.map_one, one_mul, F.map_id, id_apply],
  end,
  mul_one := λ x, begin
    apply quot.induction_on x, clear x, intro x, cases x with j x,
    rw [colimit_one_eq F j, colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, 1⟩ j (𝟙 j) (𝟙 j),
      monoid_hom.map_one, mul_one, F.map_id, id_apply],
  end,
  mul_assoc := λ x y z, begin
    apply quot.induction_on₃ x y z, clear x y z, intros x y z,
    cases x with j₁ x, cases y with j₂ y, cases z with j₃ z,
    rw [colimit_mul_mk_eq F ⟨j₁, x⟩ ⟨j₂, y⟩ _ (first_to_max₃ j₁ j₂ j₃) (second_to_max₃ j₁ j₂ j₃),
      colimit_mul_mk_eq F ⟨max₃ j₁ j₂ j₃, _⟩ ⟨j₃, z⟩ _ (𝟙 _) (third_to_max₃ j₁ j₂ j₃),
      colimit_mul_mk_eq F ⟨j₂, y⟩ ⟨j₃, z⟩ _ (second_to_max₃ j₁ j₂ j₃) (third_to_max₃ j₁ j₂ j₃),
      colimit_mul_mk_eq F ⟨j₁, x⟩ ⟨max₃ j₁ j₂ j₃, _⟩ _ (first_to_max₃ j₁ j₂ j₃) (𝟙 _)],
    simp only [F.map_id, id_apply, mul_assoc],
  end,
  ..colimit_has_one,
  ..colimit_has_mul }

/-- The bundled monoid giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive monoid giving the filtered colimit of a diagram."]
def colimit : Mon := Mon.of M

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
@[to_additive "The additive monoid homomorphism from a given additive monoid in the diagram to the
colimit additive monoid."]
def cocone_morphism (j : J) : F.obj j ⟶ colimit :=
{ to_fun := (types.colimit_cocone (F ⋙ forget Mon)).ι.app j,
  map_one' := (colimit_one_eq j).symm,
  map_mul' := λ x y, begin
    convert (colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 j) (𝟙 j)).symm,
    rw [F.map_id, id_apply, id_apply], refl,
  end }

@[simp, to_additive]
lemma cocone_naturality {j j' : J} (f : j ⟶ j') :
  F.map f ≫ (cocone_morphism j') = cocone_morphism j :=
monoid_hom.coe_inj ((types.colimit_cocone (F ⋙ forget Mon)).ι.naturality f)

/-- The cocone over the proposed colimit monoid. -/
@[to_additive "The cocone over the proposed colimit additive monoid."]
def colimit_cocone : cocone F :=
{ X := colimit,
  ι := { app := cocone_morphism } }.

/--
Given a cocone `t` of `F`, the induced monoid homomorphism from the colimit to the cocone point.
As a function, this is simply given by the induced map of the corresponding cocone in `Type`.
The only thing left to see is that it is a monoid homomorphism.
-/
@[to_additive "Given a cocone `t` of `F`, the induced additive monoid homomorphism from the colimit
to the cocone point. As a function, this is simply given by the induced map of the corresponding
cocone in `Type`. The only thing left to see is that it is an additive monoid homomorphism."]
def colimit_desc (t : cocone F) : colimit ⟶ t.X :=
{ to_fun := (types.colimit_cocone_is_colimit (F ⋙ forget Mon)).desc ((forget Mon).map_cocone t),
  map_one' := begin
    rw colimit_one_eq F is_filtered.nonempty.some,
    exact monoid_hom.map_one _,
  end,
  map_mul' := λ x y, begin
    apply quot.induction_on₂ x y, clear x y, intros x y,
    cases x with i x, cases y with j y,
    rw colimit_mul_mk_eq F ⟨i, x⟩ ⟨j, y⟩ (max' i j) (left_to_max i j) (right_to_max i j),
    dsimp [types.colimit_cocone_is_colimit],
    rw [monoid_hom.map_mul, t.w_apply, t.w_apply],
  end }

/-- The proposed colimit cocone is a colimit in `Mon`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddMon`."]
def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := colimit_desc,
  fac' := λ t j, monoid_hom.coe_inj
    ((types.colimit_cocone_is_colimit (F ⋙ forget Mon)).fac ((forget Mon).map_cocone t) j),
  uniq' := λ t m h, monoid_hom.coe_inj $
    (types.colimit_cocone_is_colimit (F ⋙ forget Mon)).uniq ((forget Mon).map_cocone t) m
      (λ j, funext $ λ x, monoid_hom.congr_fun (h j) x) }

@[to_additive]
instance forget_preserves_filtered_colimits : preserves_filtered_colimits (forget Mon.{u}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit.{u u} F) (types.colimit_cocone_is_colimit (F ⋙ forget Mon.{u})) } }

end

end Mon.filtered_colimits


namespace CommMon.filtered_colimits

open Mon.filtered_colimits (colimit_mul_mk_eq)

section

-- We use parameters here, mainly so we can have the abbreviation `M` below, without
-- passing around `F` all the time.
parameters {J : Type v} [small_category J] [is_filtered J] (F : J ⥤ CommMon.{max v u})

/--
The colimit of `F ⋙ forget₂ CommMon Mon` in the category `Mon`.
In the following, we will show that this has the structure of a _commutative_ monoid.
-/
@[to_additive "The colimit of `F ⋙ forget₂ AddCommMon AddMon` in the category `AddMon`. In the
following, we will show that this has the structure of a _commutative_ additive monoid."]
abbreviation M : Mon := Mon.filtered_colimits.colimit (F ⋙ forget₂ CommMon Mon.{max v u})

@[to_additive]
instance colimit_comm_monoid : comm_monoid M :=
{ mul_comm := λ x y, begin
    apply quot.induction_on₂ x y, clear x y, intros x y,
    let k := max' x.1 y.1,
    let f := left_to_max x.1 y.1,
    let g := right_to_max x.1 y.1,
    rw [colimit_mul_mk_eq _ x y k f g, colimit_mul_mk_eq _ y x k g f],
    dsimp,
    rw mul_comm,
 end
  ..M.monoid }

/-- The bundled commutative monoid giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive commutative monoid giving the filtered colimit of a diagram."]
def colimit : CommMon := CommMon.of M

/-- The cocone over the proposed colimit commutative monoid. -/
@[to_additive "The cocone over the proposed colimit additive commutative monoid."]
def colimit_cocone : cocone F :=
{ X := colimit,
  ι := { ..(Mon.filtered_colimits.colimit_cocone (F ⋙ forget₂ CommMon Mon.{max v u})).ι } }

/-- The proposed colimit cocone is a colimit in `CommMon`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddCommMon`."]
def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := λ t, Mon.filtered_colimits.colimit_desc (F ⋙ forget₂ CommMon Mon.{max v u})
    ((forget₂ CommMon Mon.{max v u}).map_cocone t),
  fac' := λ t j, monoid_hom.coe_inj $
    (types.colimit_cocone_is_colimit (F ⋙ forget CommMon)).fac ((forget CommMon).map_cocone t) j,
  uniq' := λ t m h, monoid_hom.coe_inj $
    (types.colimit_cocone_is_colimit (F ⋙ forget CommMon)).uniq ((forget CommMon).map_cocone t) m
    ((λ j, funext $ λ x, monoid_hom.congr_fun (h j) x)) }

@[to_additive forget₂_AddMon_preserves_filtered_colimits]
instance forget₂_Mon_preserves_filtered_colimits :
  preserves_filtered_colimits (forget₂ CommMon Mon.{u}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit.{u u} F)
      (Mon.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ CommMon Mon.{u})) } }

@[to_additive]
instance forget_preserves_filtered_colimits :
  preserves_filtered_colimits (forget CommMon.{u}) :=
limits.comp_preserves_filtered_colimits (forget₂ CommMon Mon) (forget Mon)

end

end CommMon.filtered_colimits
