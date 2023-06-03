/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.group.ext
import category_theory.limits.shapes.biproducts
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.preserves.shapes.biproducts
import category_theory.limits.preserves.shapes.products
import category_theory.preadditive.basic
import tactic.abel

/-!
# Basic facts about biproducts in preadditive categories.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In (or between) preadditive categories,

* Any biproduct satisfies the equality
  `total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`,
  or, in the binary case, `total : fst ≫ inl + snd ≫ inr = 𝟙 X`.

* Any (binary) `product` or (binary) `coproduct` is a (binary) `biproduct`.

* In any category (with zero morphisms), if `biprod.map f g` is an isomorphism,
  then both `f` and `g` are isomorphisms.

* If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
  so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
  via Gaussian elimination.

* As a corollary of the previous two facts,
  if we have an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  we can construct an isomorphism `X₂ ≅ Y₂`.

* If `f : W ⊞ X ⟶ Y ⊞ Z` is an isomorphism, either `𝟙 W = 0`,
  or at least one of the component maps `W ⟶ Y` and `W ⟶ Z` is nonzero.

* If `f : ⨁ S ⟶ ⨁ T` is an isomorphism,
  then every column (corresponding to a nonzero summand in the domain)
  has some nonzero matrix entry.

* A functor preserves a biproduct if and only if it preserves
  the corresponding product if and only if it preserves the corresponding coproduct.
-/

open category_theory
open category_theory.preadditive
open category_theory.limits
open category_theory.functor
open category_theory.preadditive

open_locale classical
open_locale big_operators

universes v v' u u'

noncomputable theory

namespace category_theory

variables {C : Type u} [category.{v} C] [preadditive C]

namespace limits

variables {J : Type} [fintype J]

/--
In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
def is_bilimit_of_total {f : J → C} (b : bicone f) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X) :
  b.is_bilimit :=
{ is_limit :=
  { lift := λ s, ∑ (j : J), s.π.app ⟨j⟩ ≫ b.ι j,
    uniq' := λ s m h,
    begin
      erw [←category.comp_id m, ←total, comp_sum],
      apply finset.sum_congr rfl,
      intros j m,
      erw [reassoc_of (h ⟨j⟩)],
    end,
    fac' := λ s j,
    begin
      cases j,
      simp only [sum_comp, category.assoc, bicone.to_cone_π_app, b.ι_π, comp_dite],
      -- See note [dsimp, simp].
      dsimp, simp,
    end },
  is_colimit :=
  { desc := λ s, ∑ (j : J), b.π j ≫ s.ι.app ⟨j⟩,
    uniq' := λ s m h,
    begin
      erw [←category.id_comp m, ←total, sum_comp],
            apply finset.sum_congr rfl,
      intros j m,
      erw [category.assoc, h ⟨j⟩],
    end,
    fac' := λ s j,
    begin
      cases j,
      simp only [comp_sum, ←category.assoc, bicone.to_cocone_ι_app, b.ι_π, dite_comp],
      dsimp, simp,
    end } }

lemma is_bilimit.total {f : J → C} {b : bicone f} (i : b.is_bilimit) :
  ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X :=
i.is_limit.hom_ext (λ j, by { cases j, simp [sum_comp, b.ι_π, comp_dite] })

/--
In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
lemma has_biproduct_of_total {f : J → C} (b : bicone f) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X) :
  has_biproduct f :=
has_biproduct.mk
{ bicone := b,
  is_bilimit := is_bilimit_of_total b total }

/-- In a preadditive category, any finite bicone which is a limit cone is in fact a bilimit
    bicone. -/
def is_bilimit_of_is_limit {f : J → C} (t : bicone f) (ht : is_limit t.to_cone) : t.is_bilimit :=
is_bilimit_of_total _ $ ht.hom_ext $
  λ j, by { cases j, simp [sum_comp, t.ι_π, dite_comp, comp_dite] }

/-- We can turn any limit cone over a pair into a bilimit bicone. -/
def bicone_is_bilimit_of_limit_cone_of_is_limit {f : J → C} {t : cone (discrete.functor f)}
  (ht : is_limit t) : (bicone.of_limit_cone ht).is_bilimit :=
is_bilimit_of_is_limit _ $
  is_limit.of_iso_limit ht $ cones.ext (iso.refl _) (by { rintro ⟨j⟩, tidy })

/-- In a preadditive category, if the product over `f : J → C` exists,
    then the biproduct over `f` exists. -/
lemma has_biproduct.of_has_product {J : Type} [finite J] (f : J → C) [has_product f] :
  has_biproduct f :=
by casesI nonempty_fintype J; exact
has_biproduct.mk
{ bicone := _,
  is_bilimit := bicone_is_bilimit_of_limit_cone_of_is_limit (limit.is_limit _) }

/-- In a preadditive category, any finite bicone which is a colimit cocone is in fact a bilimit
    bicone. -/
def is_bilimit_of_is_colimit {f : J → C} (t : bicone f) (ht : is_colimit t.to_cocone) :
  t.is_bilimit :=
is_bilimit_of_total _ $ ht.hom_ext $ λ j, begin
  cases j,
  simp_rw [bicone.to_cocone_ι_app, comp_sum, ← category.assoc, t.ι_π, dite_comp],
  tidy
end

/-- We can turn any limit cone over a pair into a bilimit bicone. -/
def bicone_is_bilimit_of_colimit_cocone_of_is_colimit {f : J → C} {t : cocone (discrete.functor f)}
  (ht : is_colimit t) : (bicone.of_colimit_cocone ht).is_bilimit :=
is_bilimit_of_is_colimit _ $
  is_colimit.of_iso_colimit ht $ cocones.ext (iso.refl _) (by { rintro ⟨j⟩, tidy })

/-- In a preadditive category, if the coproduct over `f : J → C` exists,
    then the biproduct over `f` exists. -/
lemma has_biproduct.of_has_coproduct {J : Type} [finite J] (f : J → C) [has_coproduct f] :
  has_biproduct f :=
by casesI nonempty_fintype J; exact
has_biproduct.mk
{ bicone := _,
  is_bilimit := bicone_is_bilimit_of_colimit_cocone_of_is_colimit (colimit.is_colimit _) }

/-- A preadditive category with finite products has finite biproducts. -/
lemma has_finite_biproducts.of_has_finite_products [has_finite_products C] :
  has_finite_biproducts C :=
⟨λ n, { has_biproduct := λ F, has_biproduct.of_has_product _ }⟩

/-- A preadditive category with finite coproducts has finite biproducts. -/
lemma has_finite_biproducts.of_has_finite_coproducts [has_finite_coproducts C] :
  has_finite_biproducts C :=
⟨λ n, { has_biproduct := λ F, has_biproduct.of_has_coproduct _ }⟩

section
variables {f : J → C} [has_biproduct f]

/--
In any preadditive category, any biproduct satsifies
`∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
-/
@[simp] lemma biproduct.total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) :=
is_bilimit.total (biproduct.is_bilimit _)

lemma biproduct.lift_eq {T : C} {g : Π j, T ⟶ f j} :
  biproduct.lift g = ∑ j, g j ≫ biproduct.ι f j :=
begin
  ext j,
  simp only [sum_comp, biproduct.ι_π, comp_dite, biproduct.lift_π, category.assoc, comp_zero,
    finset.sum_dite_eq', finset.mem_univ, eq_to_hom_refl, category.comp_id, if_true],
end

lemma biproduct.desc_eq {T : C} {g : Π j, f j ⟶ T} :
  biproduct.desc g = ∑ j, biproduct.π f j ≫ g j :=
begin
  ext j,
  simp [comp_sum, biproduct.ι_π_assoc, dite_comp],
end

@[simp, reassoc] lemma biproduct.lift_desc {T U : C} {g : Π j, T ⟶ f j} {h : Π j, f j ⟶ U} :
  biproduct.lift g ≫ biproduct.desc h = ∑ j : J, g j ≫ h j :=
by simp [biproduct.lift_eq, biproduct.desc_eq, comp_sum, sum_comp, biproduct.ι_π_assoc,
  comp_dite, dite_comp]

lemma biproduct.map_eq [has_finite_biproducts C] {f g : J → C} {h : Π j, f j ⟶ g j} :
  biproduct.map h = ∑ j : J, biproduct.π f j ≫ h j ≫ biproduct.ι g j :=
begin
  ext,
  simp [biproduct.ι_π, biproduct.ι_π_assoc, comp_sum, sum_comp, comp_dite, dite_comp],
end

@[simp, reassoc]
lemma biproduct.matrix_desc
  {K : Type} [fintype K] [has_finite_biproducts C]
  {f : J → C} {g : K → C} (m : Π j k, f j ⟶ g k) {P} (x : Π k, g k ⟶ P) :
  biproduct.matrix m ≫ biproduct.desc x = biproduct.desc (λ j, ∑ k, m j k ≫ x k) :=
by { ext, simp, }

@[simp, reassoc]
lemma biproduct.lift_matrix
  {K : Type} [fintype K] [has_finite_biproducts C]
  {f : J → C} {g : K → C} {P} (x : Π j, P ⟶ f j) (m : Π j k, f j ⟶ g k)  :
  biproduct.lift x ≫ biproduct.matrix m = biproduct.lift (λ k, ∑ j, x j ≫ m j k) :=
by { ext, simp, }

@[reassoc]
lemma biproduct.matrix_map
  {K : Type} [fintype K] [has_finite_biproducts C]
  {f : J → C} {g : K → C} {h : K → C} (m : Π j k, f j ⟶ g k) (n : Π k, g k ⟶ h k) :
  biproduct.matrix m ≫ biproduct.map n = biproduct.matrix (λ j k, m j k ≫ n k) :=
by { ext, simp, }

@[reassoc]
lemma biproduct.map_matrix
  {K : Type} [fintype K] [has_finite_biproducts C]
  {f : J → C} {g : J → C} {h : K → C} (m : Π k, f k ⟶ g k) (n : Π j k, g j ⟶ h k) :
  biproduct.map m ≫ biproduct.matrix n = biproduct.matrix (λ j k, m j ≫ n j k) :=
by { ext, simp, }

end

/-- Reindex a categorical biproduct via an equivalence of the index types. -/
@[simps]
def biproduct.reindex {β γ : Type} [fintype β] [decidable_eq β] [decidable_eq γ]
  (ε : β ≃ γ) (f : γ → C) [has_biproduct f] [has_biproduct (f ∘ ε)] : (⨁ (f ∘ ε)) ≅ (⨁ f) :=
{ hom := biproduct.desc (λ b, biproduct.ι f (ε b)),
  inv := biproduct.lift (λ b, biproduct.π f (ε b)),
  hom_inv_id' := by { ext b b', by_cases h : b = b', { subst h, simp, }, { simp [h], }, },
  inv_hom_id' := begin
    ext g g',
    by_cases h : g = g';
    simp [preadditive.sum_comp, preadditive.comp_sum, biproduct.ι_π, biproduct.ι_π_assoc, comp_dite,
      equiv.apply_eq_iff_eq_symm_apply, finset.sum_dite_eq' finset.univ (ε.symm g') _, h],
  end, }

/--
In a preadditive category, we can construct a binary biproduct for `X Y : C` from
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
def is_binary_bilimit_of_total {X Y : C} (b : binary_bicone X Y)
  (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X) : b.is_bilimit :=
{ is_limit :=
  { lift := λ s, binary_fan.fst s ≫ b.inl +
      binary_fan.snd s ≫ b.inr,
    uniq' := λ s m h, by erw [←category.comp_id m, ←total,
      comp_add, reassoc_of (h ⟨walking_pair.left⟩), reassoc_of (h ⟨walking_pair.right⟩)],
    fac' := λ s j, by rcases j with ⟨⟨⟩⟩; simp, },
  is_colimit :=
  { desc := λ s, b.fst ≫ binary_cofan.inl s +
      b.snd ≫ binary_cofan.inr s,
    uniq' := λ s m h, by erw [←category.id_comp m, ←total,
      add_comp, category.assoc, category.assoc, h ⟨walking_pair.left⟩, h ⟨walking_pair.right⟩],
    fac' := λ s j, by rcases j with ⟨⟨⟩⟩; simp, } }

lemma is_bilimit.binary_total {X Y : C} {b : binary_bicone X Y} (i : b.is_bilimit) :
  b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X :=
i.is_limit.hom_ext (λ j, by { rcases j with ⟨⟨⟩⟩; simp, })

/--
In a preadditive category, we can construct a binary biproduct for `X Y : C` from
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
lemma has_binary_biproduct_of_total {X Y : C} (b : binary_bicone X Y)
  (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X) : has_binary_biproduct X Y :=
has_binary_biproduct.mk
{ bicone := b,
  is_bilimit := is_binary_bilimit_of_total b total }

/-- We can turn any limit cone over a pair into a bicone. -/
@[simps]
def binary_bicone.of_limit_cone {X Y : C} {t : cone (pair X Y)} (ht : is_limit t) :
  binary_bicone X Y :=
{ X := t.X,
  fst := t.π.app ⟨walking_pair.left⟩,
  snd := t.π.app ⟨walking_pair.right⟩,
  inl := ht.lift (binary_fan.mk (𝟙 X) 0),
  inr := ht.lift (binary_fan.mk 0 (𝟙 Y)) }

lemma inl_of_is_limit {X Y : C} {t : binary_bicone X Y} (ht : is_limit t.to_cone) :
  t.inl = ht.lift (binary_fan.mk (𝟙 X) 0) :=
by apply ht.uniq (binary_fan.mk (𝟙 X) 0); rintro ⟨⟨⟩⟩; dsimp; simp

lemma inr_of_is_limit {X Y : C} {t : binary_bicone X Y} (ht : is_limit t.to_cone) :
  t.inr = ht.lift (binary_fan.mk 0 (𝟙 Y)) :=
by apply ht.uniq (binary_fan.mk 0 (𝟙 Y)); rintro ⟨⟨⟩⟩; dsimp; simp

/-- In a preadditive category, any binary bicone which is a limit cone is in fact a bilimit
    bicone. -/
def is_binary_bilimit_of_is_limit {X Y : C} (t : binary_bicone X Y) (ht : is_limit t.to_cone) :
  t.is_bilimit :=
is_binary_bilimit_of_total _ (by refine binary_fan.is_limit.hom_ext ht _ _; simp)

/-- We can turn any limit cone over a pair into a bilimit bicone. -/
def binary_bicone_is_bilimit_of_limit_cone_of_is_limit {X Y : C} {t : cone (pair X Y)}
  (ht : is_limit t) : (binary_bicone.of_limit_cone ht).is_bilimit :=
is_binary_bilimit_of_total _ $ binary_fan.is_limit.hom_ext ht (by simp) (by simp)

/-- In a preadditive category, if the product of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
lemma has_binary_biproduct.of_has_binary_product (X Y : C) [has_binary_product X Y] :
  has_binary_biproduct X Y :=
has_binary_biproduct.mk
{ bicone := _,
  is_bilimit := binary_bicone_is_bilimit_of_limit_cone_of_is_limit (limit.is_limit _) }

/-- In a preadditive category, if all binary products exist, then all binary biproducts exist. -/
lemma has_binary_biproducts.of_has_binary_products [has_binary_products C] :
  has_binary_biproducts C :=
{ has_binary_biproduct := λ X Y, has_binary_biproduct.of_has_binary_product X Y, }

/-- We can turn any colimit cocone over a pair into a bicone. -/
@[simps]
def binary_bicone.of_colimit_cocone {X Y : C} {t : cocone (pair X Y)} (ht : is_colimit t) :
  binary_bicone X Y :=
{ X := t.X,
  fst := ht.desc (binary_cofan.mk (𝟙 X) 0),
  snd := ht.desc (binary_cofan.mk 0 (𝟙 Y)),
  inl := t.ι.app ⟨walking_pair.left⟩,
  inr := t.ι.app ⟨walking_pair.right⟩ }

lemma fst_of_is_colimit {X Y : C} {t : binary_bicone X Y} (ht : is_colimit t.to_cocone) :
  t.fst = ht.desc (binary_cofan.mk (𝟙 X) 0) :=
begin
  apply ht.uniq (binary_cofan.mk (𝟙 X) 0),
  rintro ⟨⟨⟩⟩; dsimp; simp
end

lemma snd_of_is_colimit {X Y : C} {t : binary_bicone X Y} (ht : is_colimit t.to_cocone) :
  t.snd = ht.desc (binary_cofan.mk 0 (𝟙 Y)) :=
begin
  apply ht.uniq (binary_cofan.mk 0 (𝟙 Y)),
  rintro ⟨⟨⟩⟩; dsimp; simp
end

/-- In a preadditive category, any binary bicone which is a colimit cocone is in fact a
    bilimit bicone. -/
def is_binary_bilimit_of_is_colimit {X Y : C} (t : binary_bicone X Y)
  (ht : is_colimit t.to_cocone) : t.is_bilimit :=
is_binary_bilimit_of_total _
begin
  refine binary_cofan.is_colimit.hom_ext ht _ _; simp,
  { rw [category.comp_id t.inl] },
  { rw [category.comp_id t.inr] }
end

/-- We can turn any colimit cocone over a pair into a bilimit bicone. -/
def binary_bicone_is_bilimit_of_colimit_cocone_of_is_colimit {X Y : C} {t : cocone (pair X Y)}
  (ht : is_colimit t) : (binary_bicone.of_colimit_cocone ht).is_bilimit :=
is_binary_bilimit_of_is_colimit (binary_bicone.of_colimit_cocone ht) $
  is_colimit.of_iso_colimit ht $ cocones.ext (iso.refl _) $ λ j, by { rcases j with ⟨⟨⟩⟩, tidy }

/-- In a preadditive category, if the coproduct of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
lemma has_binary_biproduct.of_has_binary_coproduct (X Y : C) [has_binary_coproduct X Y] :
  has_binary_biproduct X Y :=
has_binary_biproduct.mk
{ bicone := _,
  is_bilimit := binary_bicone_is_bilimit_of_colimit_cocone_of_is_colimit (colimit.is_colimit _) }

/-- In a preadditive category, if all binary coproducts exist, then all binary biproducts exist. -/
lemma has_binary_biproducts.of_has_binary_coproducts [has_binary_coproducts C] :
  has_binary_biproducts C :=
{ has_binary_biproduct := λ X Y, has_binary_biproduct.of_has_binary_coproduct X Y, }

section
variables {X Y : C} [has_binary_biproduct X Y]

/--
In any preadditive category, any binary biproduct satsifies
`biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y)`.
-/
@[simp] lemma biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) :=
begin
  ext; simp [add_comp],
end

lemma biprod.lift_eq {T : C} {f : T ⟶ X} {g : T ⟶ Y} :
  biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr :=
begin
  ext; simp [add_comp],
end

lemma biprod.desc_eq {T : C} {f : X ⟶ T} {g : Y ⟶ T} :
  biprod.desc f g = biprod.fst ≫ f + biprod.snd ≫ g :=
begin
  ext; simp [add_comp],
end

@[simp, reassoc] lemma biprod.lift_desc {T U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U} :
  biprod.lift f g ≫ biprod.desc h i = f ≫ h + g ≫ i :=
by simp [biprod.lift_eq, biprod.desc_eq]

lemma biprod.map_eq [has_binary_biproducts C] {W X Y Z : C} {f : W ⟶ Y} {g : X ⟶ Z} :
  biprod.map f g = biprod.fst ≫ f ≫ biprod.inl + biprod.snd ≫ g ≫ biprod.inr :=
by apply biprod.hom_ext; apply biprod.hom_ext'; simp

/--
Every split mono `f` with a cokernel induces a binary bicone with `f` as its `inl` and
the cokernel map as its `snd`.
We will show in `is_bilimit_binary_bicone_of_split_mono_of_cokernel` that this binary bicone is in
fact already a biproduct. -/
@[simps]
def binary_bicone_of_is_split_mono_of_cokernel {X Y : C} {f : X ⟶ Y} [is_split_mono f]
  {c : cokernel_cofork f} (i : is_colimit c) : binary_bicone X c.X :=
{ X := Y,
  fst := retraction f,
  snd := c.π,
  inl := f,
  inr :=
    let c' : cokernel_cofork (𝟙 Y - (𝟙 Y - retraction f ≫ f)) :=
      cokernel_cofork.of_π (cofork.π c) (by simp) in
    let i' : is_colimit c' := is_cokernel_epi_comp i (retraction f) (by simp) in
    let i'' := is_colimit_cofork_of_cokernel_cofork i' in
    (split_epi_of_idempotent_of_is_colimit_cofork C (by simp) i'').section_,
  inl_fst' := by simp,
  inl_snd' := by simp,
  inr_fst' :=
  begin
    dsimp only,
    rw [split_epi_of_idempotent_of_is_colimit_cofork_section_,
      is_colimit_cofork_of_cokernel_cofork_desc, is_cokernel_epi_comp_desc],
    dsimp only [cokernel_cofork_of_cofork_of_π],
    letI := epi_of_is_colimit_cofork i,
    apply zero_of_epi_comp c.π,
    simp only [sub_comp, comp_sub, category.comp_id, category.assoc, is_split_mono.id, sub_self,
      cofork.is_colimit.π_desc_assoc, cokernel_cofork.π_of_π, is_split_mono.id_assoc],
    apply sub_eq_zero_of_eq,
    apply category.id_comp
  end,
  inr_snd' := by apply split_epi.id }

/-- The bicone constructed in `binary_bicone_of_split_mono_of_cokernel` is a bilimit.
This is a version of the splitting lemma that holds in all preadditive categories. -/
def is_bilimit_binary_bicone_of_is_split_mono_of_cokernel {X Y : C} {f : X ⟶ Y} [is_split_mono f]
  {c : cokernel_cofork f} (i : is_colimit c) :
  (binary_bicone_of_is_split_mono_of_cokernel i).is_bilimit :=
is_binary_bilimit_of_total _
begin
  simp only [binary_bicone_of_is_split_mono_of_cokernel_fst,
    binary_bicone_of_is_split_mono_of_cokernel_inr, binary_bicone_of_is_split_mono_of_cokernel_snd,
    split_epi_of_idempotent_of_is_colimit_cofork_section_],
  dsimp only [binary_bicone_of_is_split_mono_of_cokernel_X],
  rw [is_colimit_cofork_of_cokernel_cofork_desc, is_cokernel_epi_comp_desc],
  simp only [binary_bicone_of_is_split_mono_of_cokernel_inl, cofork.is_colimit.π_desc,
    cokernel_cofork_of_cofork_π, cofork.π_of_π, add_sub_cancel'_right]
end

/-- If `b` is a binary bicone such that `b.inl` is a kernel of `b.snd`, then `b` is a bilimit
    bicone. -/
def binary_bicone.is_bilimit_of_kernel_inl {X Y : C} (b : binary_bicone X Y)
  (hb : is_limit b.snd_kernel_fork) : b.is_bilimit :=
is_binary_bilimit_of_is_limit _ $ binary_fan.is_limit.mk _
  (λ T f g, f ≫ b.inl + g ≫ b.inr) (λ T f g, by simp) (λ T f g, by simp) $ λ T f g m h₁ h₂,
  begin
    have h₁' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by simpa using sub_eq_zero.2 h₁,
    have h₂' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.snd = 0 := by simpa using sub_eq_zero.2 h₂,
    obtain ⟨q : T ⟶ X, hq : q ≫ b.inl = m - (f ≫ b.inl + g ≫ b.inr)⟩ :=
      kernel_fork.is_limit.lift' hb _ h₂',
    rw [←sub_eq_zero, ←hq, ←category.comp_id q, ←b.inl_fst, ←category.assoc, hq, h₁', zero_comp]
  end

/-- If `b` is a binary bicone such that `b.inr` is a kernel of `b.fst`, then `b` is a bilimit
    bicone. -/
def binary_bicone.is_bilimit_of_kernel_inr {X Y : C} (b : binary_bicone X Y)
  (hb : is_limit b.fst_kernel_fork) : b.is_bilimit :=
is_binary_bilimit_of_is_limit _ $ binary_fan.is_limit.mk _
  (λ T f g, f ≫ b.inl + g ≫ b.inr) (λ t f g, by simp) (λ t f g, by simp) $ λ T f g m h₁ h₂,
  begin
    have h₁' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.fst = 0 := by simpa using sub_eq_zero.2 h₁,
    have h₂' : (m - (f ≫ b.inl + g ≫ b.inr)) ≫ b.snd = 0 := by simpa using sub_eq_zero.2 h₂,
    obtain ⟨q : T ⟶ Y, hq : q ≫ b.inr = m - (f ≫ b.inl + g ≫ b.inr)⟩ :=
      kernel_fork.is_limit.lift' hb _ h₁',
    rw [←sub_eq_zero, ←hq, ←category.comp_id q, ←b.inr_snd, ←category.assoc, hq, h₂', zero_comp]
  end

/-- If `b` is a binary bicone such that `b.fst` is a cokernel of `b.inr`, then `b` is a bilimit
    bicone. -/
def binary_bicone.is_bilimit_of_cokernel_fst {X Y : C} (b : binary_bicone X Y)
  (hb : is_colimit b.inr_cokernel_cofork) : b.is_bilimit :=
is_binary_bilimit_of_is_colimit _ $ binary_cofan.is_colimit.mk _
  (λ T f g, b.fst ≫ f + b.snd ≫ g) (λ T f g, by simp) (λ T f g, by simp) $ λ T f g m h₁ h₂,
  begin
    have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₁,
    have h₂' : b.inr ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₂,
    obtain ⟨q : X ⟶ T, hq : b.fst ≫ q = m - (b.fst ≫ f + b.snd ≫ g)⟩ :=
      cokernel_cofork.is_colimit.desc' hb _ h₂',
    rw [←sub_eq_zero, ←hq, ←category.id_comp q, ←b.inl_fst, category.assoc, hq, h₁', comp_zero]
  end

/-- If `b` is a binary bicone such that `b.snd` is a cokernel of `b.inl`, then `b` is a bilimit
    bicone. -/
def binary_bicone.is_bilimit_of_cokernel_snd {X Y : C} (b : binary_bicone X Y)
  (hb : is_colimit b.inl_cokernel_cofork) : b.is_bilimit :=
is_binary_bilimit_of_is_colimit _ $ binary_cofan.is_colimit.mk _
  (λ T f g, b.fst ≫ f + b.snd ≫ g) (λ T f g, by simp) (λ T f g, by simp) $ λ T f g m h₁ h₂,
  begin
    have h₁' : b.inl ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₁,
    have h₂' : b.inr ≫ (m - (b.fst ≫ f + b.snd ≫ g)) = 0 := by simpa using sub_eq_zero.2 h₂,
    obtain ⟨q : Y ⟶ T, hq : b.snd ≫ q = m - (b.fst ≫ f + b.snd ≫ g)⟩ :=
      cokernel_cofork.is_colimit.desc' hb _ h₁',
    rw [←sub_eq_zero, ←hq, ←category.id_comp q, ←b.inr_snd, category.assoc, hq, h₂', comp_zero]
  end

/--
Every split epi `f` with a kernel induces a binary bicone with `f` as its `snd` and
the kernel map as its `inl`.
We will show in `binary_bicone_of_is_split_mono_of_cokernel` that this binary bicone is in fact
already a biproduct. -/
@[simps]
def binary_bicone_of_is_split_epi_of_kernel {X Y : C} {f : X ⟶ Y} [is_split_epi f]
  {c : kernel_fork f} (i : is_limit c) : binary_bicone c.X Y :=
{ X := X,
  fst :=
    let c' : kernel_fork (𝟙 X - (𝟙 X - f ≫ section_ f)) :=
      kernel_fork.of_ι (fork.ι c) (by simp) in
    let i' : is_limit c' := is_kernel_comp_mono i (section_ f) (by simp) in
    let i'' := is_limit_fork_of_kernel_fork i' in
    (split_mono_of_idempotent_of_is_limit_fork C (by simp) i'').retraction,
  snd := f,
  inl := c.ι,
  inr := section_ f,
  inl_fst' := by apply split_mono.id,
  inl_snd' := by simp,
  inr_fst' :=
  begin
    dsimp only,
    rw [split_mono_of_idempotent_of_is_limit_fork_retraction,
      is_limit_fork_of_kernel_fork_lift, is_kernel_comp_mono_lift],
    dsimp only [kernel_fork_of_fork_ι],
    letI := mono_of_is_limit_fork i,
    apply zero_of_comp_mono c.ι,
    simp only [comp_sub, category.comp_id, category.assoc, sub_self, fork.is_limit.lift_ι,
      fork.ι_of_ι, is_split_epi.id_assoc]
  end,
  inr_snd' := by simp }

/-- The bicone constructed in `binary_bicone_of_is_split_epi_of_kernel` is a bilimit.
This is a version of the splitting lemma that holds in all preadditive categories. -/
def is_bilimit_binary_bicone_of_is_split_epi_of_kernel {X Y : C} {f : X ⟶ Y} [is_split_epi f]
  {c : kernel_fork f} (i : is_limit c) :
  (binary_bicone_of_is_split_epi_of_kernel i).is_bilimit :=
binary_bicone.is_bilimit_of_kernel_inl _ $ i.of_iso_limit $ fork.ext (iso.refl _) (by simp)

end

section
variables {X Y : C} (f g : X ⟶ Y)

/-- The existence of binary biproducts implies that there is at most one preadditive structure. -/
lemma biprod.add_eq_lift_id_desc [has_binary_biproduct X X] :
  f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g :=
by simp

/-- The existence of binary biproducts implies that there is at most one preadditive structure. -/
lemma biprod.add_eq_lift_desc_id [has_binary_biproduct Y Y] :
  f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y) :=
by simp

end

end limits

open category_theory.limits

section
local attribute [ext] preadditive

/-- The existence of binary biproducts implies that there is at most one preadditive structure. -/
instance subsingleton_preadditive_of_has_binary_biproducts {C : Type u} [category.{v} C]
  [has_zero_morphisms C] [has_binary_biproducts C] : subsingleton (preadditive C) :=
subsingleton.intro $ λ a b,
begin
  ext X Y f g,
  have h₁ := @biprod.add_eq_lift_id_desc _ _ a _ _ f g
    (by convert (infer_instance : has_binary_biproduct X X)),
  have h₂ := @biprod.add_eq_lift_id_desc _ _ b _ _ f g
    (by convert (infer_instance : has_binary_biproduct X X)),
  refine h₁.trans (eq.trans _ h₂.symm),
  congr' 2;
  exact subsingleton.elim _ _
end
end

section
variables  [has_binary_biproducts.{v} C]

variables {X₁ X₂ Y₁ Y₂ : C}
variables (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)

/--
The "matrix" morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` with specified components.
-/
def biprod.of_components : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂ :=
biprod.fst ≫ f₁₁ ≫ biprod.inl +
biprod.fst ≫ f₁₂ ≫ biprod.inr +
biprod.snd ≫ f₂₁ ≫ biprod.inl +
biprod.snd ≫ f₂₂ ≫ biprod.inr

@[simp]
lemma biprod.inl_of_components :
  biprod.inl ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ =
    f₁₁ ≫ biprod.inl + f₁₂ ≫ biprod.inr :=
by simp [biprod.of_components]

@[simp]
lemma biprod.inr_of_components :
  biprod.inr ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ =
    f₂₁ ≫ biprod.inl + f₂₂ ≫ biprod.inr :=
by simp [biprod.of_components]

@[simp]
lemma biprod.of_components_fst :
  biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.fst =
    biprod.fst ≫ f₁₁ + biprod.snd ≫ f₂₁ :=
by simp [biprod.of_components]

@[simp]
lemma biprod.of_components_snd :
  biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.snd =
    biprod.fst ≫ f₁₂ + biprod.snd ≫ f₂₂ :=
by simp [biprod.of_components]

@[simp]
lemma biprod.of_components_eq (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) :
  biprod.of_components (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd)
    (biprod.inr ≫ f ≫ biprod.fst) (biprod.inr ≫ f ≫ biprod.snd) = f :=
begin
  ext;
  simp only [category.comp_id, biprod.inr_fst, biprod.inr_snd, biprod.inl_snd, add_zero, zero_add,
    biprod.inl_of_components, biprod.inr_of_components, eq_self_iff_true, category.assoc, comp_zero,
    biprod.inl_fst, preadditive.add_comp],
end

@[simp]
lemma biprod.of_components_comp {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
  (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂)
  (g₁₁ : Y₁ ⟶ Z₁) (g₁₂ : Y₁ ⟶ Z₂) (g₂₁ : Y₂ ⟶ Z₁) (g₂₂ : Y₂ ⟶ Z₂) :
  biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.of_components g₁₁ g₁₂ g₂₁ g₂₂ =
    biprod.of_components
      (f₁₁ ≫ g₁₁ + f₁₂ ≫ g₂₁) (f₁₁ ≫ g₁₂ + f₁₂ ≫ g₂₂)
      (f₂₁ ≫ g₁₁ + f₂₂ ≫ g₂₁) (f₂₁ ≫ g₁₂ + f₂₂ ≫ g₂₂) :=
begin
  dsimp [biprod.of_components],
  apply biprod.hom_ext; apply biprod.hom_ext';
  simp only [add_comp, comp_add, add_comp_assoc, add_zero, zero_add,
    biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
    biprod.inl_fst_assoc, biprod.inl_snd_assoc, biprod.inr_fst_assoc, biprod.inr_snd_assoc,
    comp_zero, zero_comp,
    category.comp_id, category.assoc],
end

/--
The unipotent upper triangular matrix
```
(1 r)
(0 1)
```
as an isomorphism.
-/
@[simps]
def biprod.unipotent_upper {X₁ X₂ : C} (r : X₁ ⟶ X₂) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ :=
{ hom := biprod.of_components (𝟙 _) r 0 (𝟙 _),
  inv := biprod.of_components (𝟙 _) (-r) 0 (𝟙 _), }

/--
The unipotent lower triangular matrix
```
(1 0)
(r 1)
```
as an isomorphism.
-/
@[simps]
def biprod.unipotent_lower {X₁ X₂ : C} (r : X₂ ⟶ X₁) : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂ :=
{ hom := biprod.of_components (𝟙 _) 0 r (𝟙 _),
  inv := biprod.of_components (𝟙 _) 0 (-r) (𝟙 _), }

/--
If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
via Gaussian elimination.

(This is the version of `biprod.gaussian` written in terms of components.)
-/
def biprod.gaussian' [is_iso f₁₁] :
  Σ' (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) (g₂₂ : X₂ ⟶ Y₂),
    L.hom ≫ (biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂) ≫ R.hom = biprod.map f₁₁ g₂₂ :=
⟨biprod.unipotent_lower (-(f₂₁ ≫ inv f₁₁)),
 biprod.unipotent_upper (-(inv f₁₁ ≫ f₁₂)),
 f₂₂ - f₂₁ ≫ (inv f₁₁) ≫ f₁₂,
 by ext; simp; abel⟩

/--
If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
via Gaussian elimination.
-/
def biprod.gaussian (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) [is_iso (biprod.inl ≫ f ≫ biprod.fst)] :
  Σ' (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) (g₂₂ : X₂ ⟶ Y₂),
    L.hom ≫ f ≫ R.hom = biprod.map (biprod.inl ≫ f ≫ biprod.fst) g₂₂ :=
begin
  let := biprod.gaussian'
    (biprod.inl ≫ f ≫ biprod.fst) (biprod.inl ≫ f ≫ biprod.snd)
    (biprod.inr ≫ f ≫ biprod.fst) (biprod.inr ≫ f ≫ biprod.snd),
  simpa [biprod.of_components_eq],
end

/--
If `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` via a two-by-two matrix whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def biprod.iso_elim' [is_iso f₁₁] [is_iso (biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂)] : X₂ ≅ Y₂ :=
begin
  obtain ⟨L, R, g, w⟩ := biprod.gaussian' f₁₁ f₁₂ f₂₁ f₂₂,
  letI : is_iso (biprod.map f₁₁ g) := by { rw ←w, apply_instance, },
  letI : is_iso g := (is_iso_right_of_is_iso_biprod_map f₁₁ g),
  exact as_iso g,
end

/--
If `f` is an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def biprod.iso_elim (f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂) [is_iso (biprod.inl ≫ f.hom ≫ biprod.fst)] : X₂ ≅ Y₂ :=
begin
  letI : is_iso (biprod.of_components
       (biprod.inl ≫ f.hom ≫ biprod.fst)
       (biprod.inl ≫ f.hom ≫ biprod.snd)
       (biprod.inr ≫ f.hom ≫ biprod.fst)
       (biprod.inr ≫ f.hom ≫ biprod.snd)) :=
  by { simp only [biprod.of_components_eq], apply_instance, },
  exact biprod.iso_elim'
    (biprod.inl ≫ f.hom ≫ biprod.fst)
    (biprod.inl ≫ f.hom ≫ biprod.snd)
    (biprod.inr ≫ f.hom ≫ biprod.fst)
    (biprod.inr ≫ f.hom ≫ biprod.snd)
end

lemma biprod.column_nonzero_of_iso {W X Y Z : C}
  (f : W ⊞ X ⟶ Y ⊞ Z) [is_iso f] :
  𝟙 W = 0 ∨ biprod.inl ≫ f ≫ biprod.fst ≠ 0 ∨ biprod.inl ≫ f ≫ biprod.snd ≠ 0 :=
begin
  by_contra' h,
  rcases h with ⟨nz, a₁, a₂⟩,
  set x := biprod.inl ≫ f ≫ inv f ≫ biprod.fst,
  have h₁ : x = 𝟙 W, by simp [x],
  have h₀ : x = 0,
  { dsimp [x],
    rw [←category.id_comp (inv f), category.assoc, ←biprod.total],
    conv_lhs { slice 2 3, rw [comp_add], },
    simp only [category.assoc],
    rw [comp_add_assoc, add_comp],
    conv_lhs { congr, skip, slice 1 3, rw a₂, },
    simp only [zero_comp, add_zero],
    conv_lhs { slice 1 3, rw a₁, },
    simp only [zero_comp], },
  exact nz (h₁.symm.trans h₀),
end

end

lemma biproduct.column_nonzero_of_iso'
  {σ τ : Type} [finite τ]
  {S : σ → C} [has_biproduct S] {T : τ → C} [has_biproduct T]
  (s : σ) (f : ⨁ S ⟶ ⨁ T) [is_iso f] :
  (∀ t : τ, biproduct.ι S s ≫ f ≫ biproduct.π T t = 0) → 𝟙 (S s) = 0 :=
begin
  casesI nonempty_fintype τ,
  intro z,
  set x := biproduct.ι S s ≫ f ≫ inv f ≫ biproduct.π S s,
  have h₁ : x = 𝟙 (S s), by simp [x],
  have h₀ : x = 0,
  { dsimp [x],
    rw [←category.id_comp (inv f), category.assoc, ←biproduct.total],
    simp only [comp_sum_assoc],
    conv_lhs { congr, apply_congr, skip, simp only [reassoc_of z], },
    simp, },
  exact h₁.symm.trans h₀,
end

/--
If `f : ⨁ S ⟶ ⨁ T` is an isomorphism, and `s` is a non-trivial summand of the source,
then there is some `t` in the target so that the `s, t` matrix entry of `f` is nonzero.
-/
def biproduct.column_nonzero_of_iso
  {σ τ : Type} [fintype τ]
  {S : σ → C} [has_biproduct S] {T : τ → C} [has_biproduct T]
  (s : σ) (nz : 𝟙 (S s) ≠ 0)
  (f : ⨁ S ⟶ ⨁ T) [is_iso f] :
  trunc (Σ' t : τ, biproduct.ι S s ≫ f ≫ biproduct.π T t ≠ 0) :=
begin
  classical,
  apply trunc_sigma_of_exists,
  have t := biproduct.column_nonzero_of_iso'.{v} s f,
  by_contradiction h,
  simp only [not_exists_not] at h,
  exact nz (t h)
end

section preadditive
variables {D : Type.{u'}} [category.{v'} D] [preadditive.{v'} D]
variables (F : C ⥤ D) [preserves_zero_morphisms F]

namespace limits

section fintype
variables {J : Type} [fintype J]

local attribute [tidy] tactic.discrete_cases

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
    preserves finite products. -/
def preserves_product_of_preserves_biproduct {f : J → C} [preserves_biproduct f F] :
  preserves_limit (discrete.functor f) F :=
{ preserves := λ c hc, is_limit.of_iso_limit
  ((is_limit.postcompose_inv_equiv (discrete.comp_nat_iso_discrete _ _) _).symm
    (is_bilimit_of_preserves F (bicone_is_bilimit_of_limit_cone_of_is_limit hc)).is_limit) $
  cones.ext (iso.refl _) (by tidy) }

section
local attribute [instance] preserves_product_of_preserves_biproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
    preserves finite products. -/
def preserves_products_of_shape_of_preserves_biproducts_of_shape
  [preserves_biproducts_of_shape J F] : preserves_limits_of_shape (discrete J) F :=
{ preserves_limit := λ f, preserves_limit_of_iso_diagram _ discrete.nat_iso_functor.symm }

end

/-- A functor between preadditive categories that preserves (zero morphisms and) finite products
    preserves finite biproducts. -/
def preserves_biproduct_of_preserves_product {f : J → C} [preserves_limit (discrete.functor f) F] :
  preserves_biproduct f F :=
{ preserves := λ b hb, is_bilimit_of_is_limit _ $
    is_limit.of_iso_limit ((is_limit.postcompose_hom_equiv (discrete.comp_nat_iso_discrete _ _)
      (F.map_cone b.to_cone)).symm (is_limit_of_preserves F hb.is_limit)) $
      cones.ext (iso.refl _) (by tidy) }

/-- If the (product-like) biproduct comparison for `F` and `f` is a monomorphism, then `F`
    preserves the biproduct of `f`. For the converse, see `map_biproduct`. -/
def preserves_biproduct_of_mono_biproduct_comparison {f : J → C} [has_biproduct f]
  [has_biproduct (F.obj ∘ f)] [mono (biproduct_comparison F f)] : preserves_biproduct f F :=
begin
  have : pi_comparison F f = (F.map_iso (biproduct.iso_product f)).inv ≫
    biproduct_comparison F f ≫ (biproduct.iso_product _).hom,
  { ext, convert pi_comparison_comp_π F f j.as; simp [← functor.map_comp] },
  haveI : is_iso (biproduct_comparison F f) := is_iso_of_mono_of_is_split_epi _,
  haveI : is_iso (pi_comparison F f) := by { rw this, apply_instance },
  haveI := preserves_product.of_iso_comparison F f,
  apply preserves_biproduct_of_preserves_product
end

/-- If the (coproduct-like) biproduct comparison for `F` and `f` is an epimorphism, then `F`
    preserves the biproduct of `F` and `f`. For the converse, see `map_biproduct`. -/
def preserves_biproduct_of_epi_biproduct_comparison' {f : J → C} [has_biproduct f]
  [has_biproduct (F.obj ∘ f)] [epi (biproduct_comparison' F f)] : preserves_biproduct f F :=
begin
  haveI : epi ((split_epi_biproduct_comparison F f).section_) := by simpa,
  haveI : is_iso (biproduct_comparison F f) := is_iso.of_epi_section'
    (split_epi_biproduct_comparison F f),
  apply preserves_biproduct_of_mono_biproduct_comparison
end

/-- A functor between preadditive categories that preserves (zero morphisms and) finite products
    preserves finite biproducts. -/
def preserves_biproducts_of_shape_of_preserves_products_of_shape
  [preserves_limits_of_shape (discrete J) F] : preserves_biproducts_of_shape J F :=
{ preserves := λ f, preserves_biproduct_of_preserves_product F }

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
    preserves finite coproducts. -/
def preserves_coproduct_of_preserves_biproduct {f : J → C} [preserves_biproduct f F] :
  preserves_colimit (discrete.functor f) F :=
{ preserves := λ c hc, is_colimit.of_iso_colimit
    ((is_colimit.precompose_hom_equiv (discrete.comp_nat_iso_discrete _ _) _).symm
      (is_bilimit_of_preserves F
        (bicone_is_bilimit_of_colimit_cocone_of_is_colimit hc)).is_colimit) $
    cocones.ext (iso.refl _) (by tidy) }

section
local attribute [instance] preserves_coproduct_of_preserves_biproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) finite biproducts
    preserves finite coproducts. -/
def preserves_coproducts_of_shape_of_preserves_biproducts_of_shape
  [preserves_biproducts_of_shape J F] : preserves_colimits_of_shape (discrete J) F :=
{ preserves_colimit := λ f, preserves_colimit_of_iso_diagram _ discrete.nat_iso_functor.symm }

end

/-- A functor between preadditive categories that preserves (zero morphisms and) finite coproducts
    preserves finite biproducts. -/
def preserves_biproduct_of_preserves_coproduct {f : J → C}
  [preserves_colimit (discrete.functor f) F] : preserves_biproduct f F :=
{ preserves := λ b hb, is_bilimit_of_is_colimit _ $
    is_colimit.of_iso_colimit ((is_colimit.precompose_inv_equiv (discrete.comp_nat_iso_discrete _ _)
      (F.map_cocone b.to_cocone)).symm (is_colimit_of_preserves F hb.is_colimit)) $
      cocones.ext (iso.refl _) (by tidy) }

/-- A functor between preadditive categories that preserves (zero morphisms and) finite coproducts
    preserves finite biproducts. -/
def preserves_biproducts_of_shape_of_preserves_coproducts_of_shape
  [preserves_colimits_of_shape (discrete J) F] : preserves_biproducts_of_shape J F :=
{ preserves := λ f, preserves_biproduct_of_preserves_coproduct F }

end fintype

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
    preserves binary products. -/
def preserves_binary_product_of_preserves_binary_biproduct {X Y : C}
  [preserves_binary_biproduct X Y F] : preserves_limit (pair X Y) F :=
{ preserves := λ c hc, is_limit.of_iso_limit
    ((is_limit.postcompose_inv_equiv (by exact diagram_iso_pair _) _).symm
      (is_binary_bilimit_of_preserves F
        (binary_bicone_is_bilimit_of_limit_cone_of_is_limit hc)).is_limit) $
    cones.ext (iso.refl _) (λ j, by { rcases j with ⟨⟨⟩⟩, tidy }) }

section
local attribute [instance] preserves_binary_product_of_preserves_binary_biproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
    preserves binary products. -/
def preserves_binary_products_of_preserves_binary_biproducts
  [preserves_binary_biproducts F] : preserves_limits_of_shape (discrete walking_pair) F :=
{ preserves_limit := λ K, preserves_limit_of_iso_diagram _ (diagram_iso_pair _).symm }

end

/-- A functor between preadditive categories that preserves (zero morphisms and) binary products
    preserves binary biproducts. -/
def preserves_binary_biproduct_of_preserves_binary_product {X Y : C}
  [preserves_limit (pair X Y) F] : preserves_binary_biproduct X Y F :=
{ preserves := λ b hb, is_binary_bilimit_of_is_limit _ $
    is_limit.of_iso_limit ((is_limit.postcompose_hom_equiv (by exact diagram_iso_pair _)
      (F.map_cone b.to_cone)).symm (is_limit_of_preserves F hb.is_limit)) $
        cones.ext (iso.refl _) (λ j, by { rcases j with ⟨⟨⟩⟩, tidy }) }

/-- If the (product-like) biproduct comparison for `F`, `X` and `Y` is a monomorphism, then
    `F` preserves the biproduct of `X` and `Y`. For the converse, see `map_biprod`. -/
def preserves_binary_biproduct_of_mono_biprod_comparison {X Y : C} [has_binary_biproduct X Y]
  [has_binary_biproduct (F.obj X) (F.obj Y)] [mono (biprod_comparison F X Y)] :
  preserves_binary_biproduct X Y F :=
begin
  have : prod_comparison F X Y = (F.map_iso (biprod.iso_prod X Y)).inv ≫
    biprod_comparison F X Y ≫ (biprod.iso_prod _ _).hom := by { ext; simp [← functor.map_comp] },
  haveI : is_iso (biprod_comparison F X Y) := is_iso_of_mono_of_is_split_epi _,
  haveI : is_iso (prod_comparison F X Y) := by { rw this, apply_instance },
  haveI := preserves_limit_pair.of_iso_prod_comparison F X Y,
  apply preserves_binary_biproduct_of_preserves_binary_product
end

/-- If the (coproduct-like) biproduct comparison for `F`, `X` and `Y` is an epimorphism, then
    `F` preserves the biproduct of `X` and `Y`. For the converse, see `map_biprod`. -/
def preserves_binary_biproduct_of_epi_biprod_comparison' {X Y : C} [has_binary_biproduct X Y]
  [has_binary_biproduct (F.obj X) (F.obj Y)] [epi (biprod_comparison' F X Y)] :
  preserves_binary_biproduct X Y F :=
begin
  haveI : epi ((split_epi_biprod_comparison F X Y).section_) := by simpa,
  haveI : is_iso (biprod_comparison F X Y) := is_iso.of_epi_section'
    (split_epi_biprod_comparison F X Y),
  apply preserves_binary_biproduct_of_mono_biprod_comparison
end

/-- A functor between preadditive categories that preserves (zero morphisms and) binary products
    preserves binary biproducts. -/
def preserves_binary_biproducts_of_preserves_binary_products
  [preserves_limits_of_shape (discrete walking_pair) F] : preserves_binary_biproducts F :=
{ preserves := λ X Y, preserves_binary_biproduct_of_preserves_binary_product F }

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
    preserves binary coproducts. -/
def preserves_binary_coproduct_of_preserves_binary_biproduct {X Y : C}
  [preserves_binary_biproduct X Y F] : preserves_colimit (pair X Y) F :=
{ preserves := λ c hc, is_colimit.of_iso_colimit
    ((is_colimit.precompose_hom_equiv (by exact diagram_iso_pair _) _).symm
      (is_binary_bilimit_of_preserves F
        (binary_bicone_is_bilimit_of_colimit_cocone_of_is_colimit hc)).is_colimit) $
      cocones.ext (iso.refl _) (λ j, by { rcases j with ⟨⟨⟩⟩, tidy }) }

section
local attribute [instance] preserves_binary_coproduct_of_preserves_binary_biproduct

/-- A functor between preadditive categories that preserves (zero morphisms and) binary biproducts
    preserves binary coproducts. -/
def preserves_binary_coproducts_of_preserves_binary_biproducts
  [preserves_binary_biproducts F] : preserves_colimits_of_shape (discrete walking_pair) F :=
{ preserves_colimit := λ K, preserves_colimit_of_iso_diagram _ (diagram_iso_pair _).symm }

end

/-- A functor between preadditive categories that preserves (zero morphisms and) binary coproducts
    preserves binary biproducts. -/
def preserves_binary_biproduct_of_preserves_binary_coproduct {X Y : C}
  [preserves_colimit (pair X Y) F] : preserves_binary_biproduct X Y F :=
{ preserves := λ b hb, is_binary_bilimit_of_is_colimit _ $
    is_colimit.of_iso_colimit ((is_colimit.precompose_inv_equiv (by exact diagram_iso_pair _)
      (F.map_cocone b.to_cocone)).symm (is_colimit_of_preserves F hb.is_colimit)) $
        cocones.ext (iso.refl _) (λ j, by { rcases j with ⟨⟨⟩⟩, tidy }) }

/-- A functor between preadditive categories that preserves (zero morphisms and) binary coproducts
    preserves binary biproducts. -/
def preserves_binary_biproducts_of_preserves_binary_coproducts
  [preserves_colimits_of_shape (discrete walking_pair) F] : preserves_binary_biproducts F :=
{ preserves := λ X Y, preserves_binary_biproduct_of_preserves_binary_coproduct F }

end limits

end preadditive

end category_theory
