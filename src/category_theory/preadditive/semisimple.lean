

import category_theory.preadditive.biproducts
import category_theory.preadditive.schur
import category_theory.subobject.limits
import category_theory.noetherian

/-!
# Semisimple objects

We prove the fundamental result about semisimple objects
in a preadditive category with biproducts and kernels,
namely that the following conditions on `X` are equivalent:
* `X` is a direct sum of simple objects
* every subobject of `X` is complemented.

These then give the definition of a semisimple object.

The proof proceeds through the following sequence of observations:
* `simple_subobject_of_semisimple_iso_summand`:
  if a simple object includes into a direct sum of simples,
  one of the components of the inclusion map must be an isomorphism
* `simple_subobject_of_semisimple`
  if a simple object includes into a direct sum of simples,
  then after composing with isomorphisms on either side
  we can realise this inclusion as the inclusion of one of the summands.
-/

open category_theory
open category_theory.limits

universes v u

-- #14146
lemma ite_dite_distrib_left {P Q : Prop} [decidable P] [decidable Q] {α : Type*} (a : α) (b : Q → α) (c : ¬Q → α) :
  (if P then (if h : Q then b h else c h) else a) = if h : Q then (if P then b h else a) else (if P then c h else a) :=
by split_ifs; refl

lemma ite_dite_distrib_right {P Q : Prop} [decidable P] [decidable Q] {α : Type*} (a : α) (b : Q → α) (c : ¬Q → α) :
  (if P then a else (if h : Q then b h else c h)) = if h : Q then (if P then a else b h) else (if P then a else c h) :=
by split_ifs; refl

noncomputable theory
open_locale classical big_operators

variables {C : Type u} [category.{v} C] [preadditive C]
variables [has_binary_biproducts C] [has_kernels C]

variables {ι : Type v} [decidable_eq ι] [fintype ι]

-- PR'd as #14143
@[simp] lemma comp_ite {P : Prop} [decidable P]
  {X Y Z : C} (f : X ⟶ Y) (g g' : (Y ⟶ Z)) :
  (f ≫ if P then g else g') = (if P then f ≫ g else f ≫ g') :=
by { split_ifs; refl }

@[simp] lemma ite_comp {P : Prop} [decidable P]
  {X Y Z : C} (f f' : (X ⟶ Y))  (g : Y ⟶ Z) :
  (if P then f else f') ≫ g = (if P then f ≫ g else f' ≫ g) :=
by { split_ifs; refl }

/--
Given a simple subobject of a direct sum of simple objects,
one of the components of the inclusion map must be an isomorphism, by Schur's lemma.
-/
lemma simple_subobject_of_semisimple_iso_summand (f : ι → C) [has_biproduct f] [∀ i, simple (f i)]
  (V : subobject (⨁ f)) [simple (V : C)] :
  ∃ (i : ι), is_iso (V.arrow ≫ biproduct.π _ i) :=
begin
  by_cases h : ∀ i, V.arrow ≫ biproduct.π _ i = 0,
  { have z : V.arrow = 0, { ext, simp [h], },
    have t : 𝟙 (V : C) = 0, { apply (cancel_mono V.arrow).1, simp [z], },
    exact false.elim (id_nonzero (V : C) t), },
  { simp only [not_forall] at h,
    obtain ⟨i, w⟩ := h,
    exact ⟨i, is_iso_of_hom_simple w⟩, }
end

/-- An auxiliary definition for `simple_subobject_of_semisimple`. -/
def simple_subobject_of_semisimple_iso_hom (f : ι → C) [has_finite_biproducts C] [∀ i, simple (f i)]
  (V : subobject (⨁ f)) [simple (V : C)] (i : ι) [is_iso (V.arrow ≫ biproduct.π _ i)] :
  ⨁ f ⟶ ⨁ f :=
∑ (k : ι), if k = i then 0 else
  biproduct.π _ i ≫ inv (V.arrow ≫ biproduct.π _ i) ≫ V.arrow ≫ biproduct.π f k ≫ biproduct.ι f k

@[simp, reassoc] lemma simple_subobject_of_semisimple_iso_hom_π
  (f : ι → C) [has_finite_biproducts C] [∀ i, simple (f i)]
  (V : subobject (⨁ f)) [simple (V : C)] (i : ι) [is_iso (V.arrow ≫ biproduct.π _ i)] (j) :
  simple_subobject_of_semisimple_iso_hom f V i ≫ biproduct.π f j =
    if j = i then 0 else
      biproduct.π _ i ≫ inv (V.arrow ≫ biproduct.π _ i) ≫ V.arrow ≫ biproduct.π f j :=
begin
  simp_rw [simple_subobject_of_semisimple_iso_hom, preadditive.sum_comp, ite_comp, category.assoc,
    zero_comp, biproduct.ι_π, comp_dite, comp_zero, ite_dite_distrib_right, if_t_t,
    finset.sum_dite_eq', finset.mem_univ, if_true, eq_to_hom_refl, category.comp_id],
end

attribute [irreducible] simple_subobject_of_semisimple_iso_hom

/-- An auxiliary definition for `simple_subobject_of_semisimple`. -/
def simple_subobject_of_semisimple_iso (f : ι → C) [has_finite_biproducts C] [∀ i, simple (f i)]
  (V : subobject (⨁ f)) [simple (V : C)] (i : ι) [is_iso (V.arrow ≫ biproduct.π _ i)] :
    ⨁ f ≅ ⨁ f :=
{ hom := 𝟙 _ - simple_subobject_of_semisimple_iso_hom f V i,
  inv := 𝟙 _ + simple_subobject_of_semisimple_iso_hom f V i,
  hom_inv_id' := begin
    apply biproduct.hom_ext,
    intro j,
    simp only [preadditive.sub_comp, preadditive.comp_sub, preadditive.add_comp,
      preadditive.comp_add, category.id_comp, category.comp_id, category.assoc],
    simp only [simple_subobject_of_semisimple_iso_hom_π],
    split_ifs; simp,
  end,
  inv_hom_id' := begin
    apply biproduct.hom_ext,
    intro j,
    simp only [preadditive.sub_comp, preadditive.comp_sub, preadditive.add_comp,
      preadditive.comp_add, category.id_comp, category.comp_id, category.assoc],
    simp only [simple_subobject_of_semisimple_iso_hom_π],
    split_ifs; simp,
  end, }

/--
Any simple subobject of a direct sum of simple objects is, up to isomorphism,
one of the summands.
-/
lemma simple_subobject_of_semisimple (f : ι → C) [has_finite_biproducts C] [∀ i, simple (f i)]
  (V : subobject (⨁ f)) [simple (V : C)] :
  ∃ (i : ι) [is_iso (V.arrow ≫ biproduct.π _ i)] (k : Aut (⨁ f)),
    V.arrow ≫ k.hom = V.arrow ≫ biproduct.π _ i ≫ biproduct.ι f i :=
begin
  obtain ⟨i, _⟩ := simple_subobject_of_semisimple_iso_summand f V,
  resetI,
  refine ⟨i, infer_instance, simple_subobject_of_semisimple_iso f V i, _⟩,
  ext,
  simp only [simple_subobject_of_semisimple_iso, simple_subobject_of_semisimple_iso_hom_π,
    as_iso_hom, category.comp_id, category.assoc,
    comp_ite, comp_zero, preadditive.comp_sub, preadditive.sub_comp],
  split_ifs with w w,
  { unfreezingI { subst w, }, simp, },
  { simp only [←category.assoc, is_iso.hom_inv_id],
    simp [biproduct.ι_π_ne f (ne.symm w)], },
end

-- /--
-- If we have `V` inside `W`, and an inclusion of `W` into `V ⊞ Z`,
-- so that `V` is taken identically to `V`,
-- then `V` is complemented in `W`.
-- -/
-- def complement {W V Z : C} (i : V ⟶ W) [mono i] (j : W ⟶ V ⊞ Z) [mono j]
--   (w : i ≫ j = biprod.inl) :
--   W ≅ V ⊞ kernel (j ≫ biprod.fst) :=
-- { hom := j ≫ biprod.fst ≫ biprod.inl +
--     kernel.lift _ (𝟙 W - j ≫ biprod.fst ≫ i) (by simp [reassoc_of w]) ≫ biprod.inr,
--   inv := biprod.fst ≫ i + biprod.snd ≫ kernel.ι _,
--   hom_inv_id' := by tidy,
--   inv_hom_id' := begin
--     ext, -- Check each entry of the 2x2 matrix separately.
--     { simp [reassoc_of w], },
--     { simp [reassoc_of w], },
--     { simp, },
--     { simp only [category.assoc, category.id_comp, category.comp_id,
--         preadditive.add_comp, preadditive.comp_add, preadditive.comp_sub, zero_comp, comp_zero,
--         biprod.inr_fst_assoc, biprod.inl_snd, biprod.inr_snd, biprod.inr_snd_assoc,
--         zero_add, kernel.lift_ι],
--       simp only [sub_eq_self],
--       slice_lhs 1 3 { simp only [kernel.condition], },
--       simp only [zero_comp], }
--   end, }.

@[simp, reassoc]
lemma foo {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso (f ≫ g)] :
  f ≫ g ≫ inv (f ≫ g) = 𝟙 X :=
by { rw [←category.assoc, is_iso.hom_inv_id], }

@[simp]
lemma kernel_subobject_comp_arrow_comp
  {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) [has_kernel (f ≫ g)] (k : Y ⟶ Z) :
  (kernel_subobject (f ≫ g)).arrow ≫ f ≫ g ≫ k = 0 :=
begin
  slice_lhs 1 3 { rw kernel_subobject_arrow_comp, },
  rw zero_comp,
end

-- def complement' {X Y : C} {V W : subobject (X ⊞ Y)} (h : V ≤ W) [is_iso (V.arrow ≫ biprod.fst)] :
--   (W : C) ≅ V ⊞ kernel_subobject (W.arrow ≫ biprod.fst) :=
-- { hom := W.arrow ≫ biprod.fst ≫ inv (V.arrow ≫ biprod.fst) ≫ biprod.inl +
--     factor_thru_kernel_subobject (W.arrow ≫ biprod.fst)
--       (𝟙 W - W.arrow ≫ biprod.fst ≫ inv (V.arrow ≫ biprod.fst) ≫ (subobject.of_le _ _ h))
--       (by simp) ≫
--     biprod.inr,
--   inv := biprod.fst ≫ (subobject.of_le _ _ h) + biprod.snd ≫ (kernel_subobject _).arrow,
--   hom_inv_id' := by simp,
--   inv_hom_id' := begin
--     ext; -- Check each entry of the 2x2 matrix separately.
--     simp,
--   end, }.

lemma complement_hom_inv_id (f : ι → C) [has_finite_biproducts C]
  {V W : subobject (⨁ f)} (h : V ≤ W) (i : ι) [is_iso (V.arrow ≫ biproduct.π f i)] (w) :
  (W.arrow ≫ biproduct.π f i ≫ inv (V.arrow ≫ biproduct.π f i) ≫ biprod.inl +
    factor_thru_kernel_subobject (W.arrow ≫ biproduct.π f i)
      (𝟙 W - W.arrow ≫ biproduct.π f i ≫ inv (V.arrow ≫ biproduct.π f i) ≫ V.of_le W h) w ≫
      biprod.inr) ≫
    (biprod.fst ≫ V.of_le W h +
      biprod.snd ≫ (kernel_subobject (W.arrow ≫ biproduct.π f i)).arrow) =
  𝟙 W :=
by simp

lemma complement_inv_hom_id (f : ι → C) [has_finite_biproducts C]
  {V W : subobject (⨁ f)} (h : V ≤ W) (i : ι) [is_iso (V.arrow ≫ biproduct.π f i)] (w) :
  (biprod.fst ≫ V.of_le W h +
      biprod.snd ≫ (kernel_subobject (W.arrow ≫ biproduct.π f i)).arrow) ≫
  (W.arrow ≫ biproduct.π f i ≫ inv (V.arrow ≫ biproduct.π f i) ≫ biprod.inl +
    factor_thru_kernel_subobject (W.arrow ≫ biproduct.π f i)
      (𝟙 W - W.arrow ≫ biproduct.π f i ≫ inv (V.arrow ≫ biproduct.π f i) ≫ V.of_le W h) w ≫
      biprod.inr) =
  𝟙 (V ⊞ kernel_subobject (W.arrow ≫ biproduct.π f i)) :=
-- This works `by ext; simp`, but is sadly too slow.
begin
  ext, -- Check each entry of the 2x2 matrix separately.
  { simp only [category.assoc, category.comp_id, is_iso.hom_inv_id_assoc,
      preadditive.comp_add, preadditive.add_comp_assoc, biprod.inl_fst, biprod.inr_fst,
      comp_zero, add_zero, subobject.of_le_arrow, kernel_subobject_arrow_comp], },
  { simp only [category.assoc, category.comp_id, foo_assoc,
      preadditive.add_comp, preadditive.comp_sub, biprod.inl_snd_assoc, biprod.inr_snd,
      comp_zero, zero_comp, zero_add, sub_self,
      factor_thru_kernel_subobject_comp_arrow, subobject.of_le_arrow_assoc], },
  { simp only [category.assoc, category.comp_id,
      preadditive.comp_add, preadditive.add_comp_assoc, preadditive.add_comp,
      biprod.inr_fst_assoc, biprod.inr_snd_assoc, biprod.inr_fst,
      comp_zero, zero_comp, zero_add, add_zero,
      kernel_subobject_comp_arrow_comp], },
  { simp only [category.assoc, category.id_comp,
      preadditive.comp_add, preadditive.add_comp, preadditive.comp_sub,
      biprod.inr_fst_assoc, biprod.inr_snd_assoc,
      zero_comp, zero_add, sub_zero,
      factor_thru_kernel_subobject_comp_arrow, kernel_subobject_comp_arrow_comp], },
end

def complement'' (f : ι → C) [has_finite_biproducts C]
  {V W : subobject (⨁ f)} (h : V ≤ W) (i : ι) [is_iso (V.arrow ≫ biproduct.π f i)] :
  (W : C) ≅ V ⊞ kernel_subobject (W.arrow ≫ biproduct.π f i) :=
{ hom := W.arrow ≫ biproduct.π f i ≫ inv (V.arrow ≫ biproduct.π f i) ≫ biprod.inl +
    factor_thru_kernel_subobject (W.arrow ≫ biproduct.π f i)
      (𝟙 W - W.arrow ≫ biproduct.π f i ≫ inv (V.arrow ≫ biproduct.π f i) ≫ (subobject.of_le _ _ h))
      (by simp) ≫
    biprod.inr,
  inv := biprod.fst ≫ (subobject.of_le _ _ h) + biprod.snd ≫ (kernel_subobject _).arrow,
  hom_inv_id' := complement_hom_inv_id f h i _,
  inv_hom_id' := complement_inv_hom_id f h i _, }.

/--
A subobject `W` of a direct sum of simple objects `⨁ f`
which itself contains a simple subobject
can be written as `W ≅ f i ⊞ W'` for some `i`,
so that the inclusion takes `f i` to the corresponding summand,
and `W'` is a subobject of the other summands.

(In `subobject_of_semisimple` we further assume that the category is noetherian,
and replace the hypothesis that `W` contains a simple subobject with
the hypothesis `W ≠ ⊥`.)
-/
lemma subobject_of_semisimple' (f : ι → C) [has_finite_biproducts C] [∀ i, simple (f i)]
  (W : subobject (⨁ f)) (w : ∃ V, V ≤ W ∧ simple (V : C)) :
  ∃ (i : ι) (W' : subobject (⨁ (λ j : ({i}ᶜ : set ι), f j))) (j : (W : C) ≅ f i ⊞ W'),
    W.arrow = j.hom ≫ (biprod.fst ≫ biproduct.ι _ i +
      biprod.snd ≫ W'.arrow ≫ biproduct.from_subtype _ _) :=
begin
  obtain ⟨V, h, _⟩ := w, resetI,
  obtain ⟨i, j, k, w⟩ := simple_subobject_of_semisimple f V,
  resetI,
  use i,
  refine ⟨kernel_subobject (biproduct.from_subtype _ _ ≫ k.hom ≫ biproduct.π _ i), _, _⟩,
  refine complement'' f h i ≪≫ _,
  -- fsplit,
  -- apply biprod.lift,
  -- exact W.arrow ≫ biproduct.π _ _,
  -- apply factor_thru_kernel_subobject _ (W.arrow ≫ biproduct.to_subtype _ _),

  -- sorry
end

/--
A nonzero subobject `W` of a direct sum of simple objects `⨁ f` can be written as
`W ≅ f i ⊞ W'` for some `i`, so that the inclusion takes `f i` to the corresponding summand,
and `W'` is a subobject of the other summands.
-/
lemma subobject_of_semisimple [noetherian C] (f : ι → C) [has_finite_biproducts C] [∀ i, simple (f i)]
  (W : subobject (⨁ f)) (w : W ≠ ⊥) :
  ∃ (i : ι) (W' : subobject (⨁ (λ j : ({i}ᶜ : set ι), f j))) (j : (W : C) ≅ f i ⊞ W'),
    W.arrow = j.hom ≫ (biprod.fst ≫ biproduct.ι _ i +
      biprod.snd ≫ W'.arrow ≫ biproduct.from_subtype _ _) :=
subobject_of_semisimple' f W sorry

def biproduct.π_le (f : ι → C) {p q : set ι} (h : p ⊆ q) [has_finite_biproducts C] :
  (⨁ (λ i : q, f i)) ⟶ (⨁ (λ i : p, f i)) :=
biproduct.lift (λ i, biproduct.π _ (⟨i.1, h i.2⟩ : q))

@[simp, reassoc] lemma biproduct.π_le_π (f : ι → C) {p q : set ι} (h : p ⊆ q) [has_finite_biproducts C] (j : p) :
  biproduct.π_le f h ≫ biproduct.π (λ i : p, f i) j = biproduct.π (λ i : q, f i) ⟨j.1, h j.2⟩ :=
by { simp [biproduct.π_le], }

def biproduct.ι_le (f : ι → C) {p q : set ι} (h : p ⊆ q) [has_finite_biproducts C] :
  (⨁ (λ i : p, f i)) ⟶ (⨁ (λ i : q, f i)) :=
biproduct.desc (λ i, biproduct.ι (λ (i : q), f i) (⟨i.1, h i.2⟩ : q))

@[simp, reassoc] lemma biproduct.ι_ι_le (f : ι → C) {p q : set ι} (h : p ⊆ q) [has_finite_biproducts C] (j : p) :
  biproduct.ι (λ i : p, f i) j ≫ biproduct.ι_le f h = biproduct.ι (λ i : q, f i) ⟨j.1, h j.2⟩ :=
by { simp [biproduct.ι_le], }

@[reassoc]
lemma biproduct.ι_π_le (f : ι → C) {p q : set ι} (h : p ⊆ q) [has_finite_biproducts C] (j : q) :
  biproduct.ι (λ i : q, f i) j ≫ biproduct.π_le f h =
    if h : j.1 ∈ p then biproduct.ι (λ i : p, f i) ⟨j.1, h⟩ else 0 :=
begin
  rcases j with ⟨j, jm⟩,
  ext ⟨k, km⟩,
  simp only [biproduct.π_le, biproduct.ι_π, subtype.mk_eq_mk, category.assoc, biproduct.lift_π],
  by_cases t : j = k,
  { subst t, dsimp, simp [km], dsimp, simp, },
  { simp only [dif_neg t], dsimp,
    split_ifs,
    { rw [biproduct.ι_π_ne], simpa using t, },
    { simp, }, },
end

@[reassoc]
lemma biproduct.ι_le_π (f : ι → C) {p q : set ι} (h : p ⊆ q) [has_finite_biproducts C] (j : q) :
  biproduct.ι_le f h ≫ biproduct.π (λ i : q, f i) j =
    if h : j.1 ∈ p then biproduct.π (λ i : p, f i) ⟨j.1, h⟩ else 0 :=
begin
  rcases j with ⟨j, jm⟩,
  ext ⟨k, km⟩,
  simp only [biproduct.ι_le, biproduct.ι_π, comp_dite, subtype.mk_eq_mk, biproduct.ι_desc_assoc,
    comp_zero],
  by_cases t : k = j,
  { subst t, dsimp, simp [km], },
  { simp only [dif_neg t], dsimp, simp, }
end

@[simps]
def biproduct.select (p : set ι) (i : ι) (h : i ∉ p) (f : ι → C) [has_finite_biproducts C] :
  ⨁ (λ j : insert i p, f j) ≅ f i ⊞ (⨁ (λ j : p, f j)) :=
{ hom := biprod.lift
    (biproduct.π _ (⟨i, set.mem_insert i p⟩ : insert i p))
    (biproduct.π_le _ (set.subset_insert i p)),
  inv := biprod.desc
    (biproduct.ι (λ (j : (insert i p)), f j) (⟨i, set.mem_insert i p⟩ : insert i p))
    (biproduct.ι_le _ (set.subset_insert i p)),
  hom_inv_id' := begin
    simp only [biprod.lift_desc],
    ext ⟨j, rfl|jm⟩ ⟨k, rfl|km⟩,
    { dsimp,
      simp only [preadditive.comp_add, preadditive.add_comp, category.assoc, category.comp_id,
        biproduct.ι_π_self],
      erw [biproduct.ι_π_self, biproduct.ι_π_self_assoc, biproduct.ι_le_π, dif_neg h],
      dsimp, simp, },
    { dsimp,
      simp only [preadditive.comp_add, preadditive.add_comp, category.assoc, category.comp_id],
      erw [biproduct.ι_π_self_assoc, biproduct.ι_π_le_assoc, dif_neg h],
      simp, refl, },
    { dsimp,
      simp only [preadditive.comp_add, category.comp_id],
      rw [biproduct.ι_π_ne_assoc, biproduct.ι_π_le_assoc, dif_pos jm, biproduct.ι_ι_le, zero_comp,
        zero_add],
      { refl, },
      { simpa using ne_of_mem_of_not_mem jm h, }, },
  end,
  inv_hom_id' := begin
    ext,
    { simp only [biprod.inl_desc_assoc, category.assoc, biprod.lift_fst, biproduct.ι_π_self,
        category.comp_id, biprod.inl_fst],
      refl, },
    { simp only [biprod.inl_desc_assoc, category.assoc, biprod.lift_snd, biproduct.π_le_π,
        category.comp_id, biprod.inl_snd, zero_comp],
      rw [biproduct.ι_π_ne],
      simpa using ne.symm (ne_of_mem_of_not_mem j.2 h), },
    { simp only [biprod.inr_desc_assoc, category.assoc, biprod.lift_fst,
        biproduct.ι_ι_le_assoc, category.comp_id, biprod.inr_fst, comp_zero],
      rw [biproduct.ι_π_ne],
      simpa using ne_of_mem_of_not_mem j.2 h, },
    { simp only [biprod.inr_desc_assoc, category.assoc, biprod.lift_snd,
         biproduct.ι_ι_le_assoc, biproduct.π_le_π, category.comp_id, biprod.inr_snd],
      rw [biproduct.ι_π, biproduct.ι_π],
      cases j, cases j_1,
      simp, refl, },
  end, }

@[simps]
def biproduct.reindex {β γ : Type v} [fintype β] [fintype γ] (ε : β ≃ γ) (f : γ → C) [has_biproduct f] [has_biproduct (f ∘ ε)] :
  (⨁ (f ∘ ε)) ≅ (⨁ f) :=
{ hom := biproduct.desc (λ b, biproduct.ι f (ε b)),
  inv := biproduct.lift (λ b, biproduct.π f (ε b)),
  hom_inv_id' := by { ext b b', by_cases h : b = b', { subst h, simp, }, { simp [h], }, },
  inv_hom_id' := begin
    ext g g',
    by_cases h : g = g';
    simp [preadditive.sum_comp, preadditive.comp_sum, biproduct.ι_π, biproduct.ι_π_assoc, comp_dite,
      equiv.apply_eq_iff_eq_symm_apply, finset.sum_dite_eq' finset.univ (ε.symm g') _, h],
  end, }.

@[simp] lemma zero_eq_iso_comp_iff {X Y Z : C} (i : X ≅ Y) (f : Y ⟶ Z) : (0 : X ⟶ Z) = i.hom ≫ f ↔ f = 0 := sorry

open_locale classical

def biproduct_is_zero_of_is_empty [is_empty ι] (f : ι → C) [has_biproduct f] : is_zero (⨁ f) := sorry


def subobject_is_zero_of_is_zero {X : C} (h : is_zero X) (Y : subobject X) : is_zero (Y : C) := sorry

def subobject.bot_is_zero [has_finite_biproducts C] (X : C) : is_zero ((⊥ : subobject X) : C) := sorry


/--
Up to isomorphism, any subobject of a direct sum of simple objects is just a subset of the summands.
-/
lemma subobject_of_semisimple'' [noetherian C] (f : ι → C) [has_finite_biproducts C] [∀ i, simple (f i)]
  (W : subobject (⨁ f)) :
  ∃ (p : set ι) (j : (W : C) ≅ ⨁ (λ i : p, f i)), W.arrow = j.hom ≫ biproduct.from_subtype _ _ :=
begin
  -- We prove this by induction on `n`, the cardinality of `ι`.
  set n := fintype.card ι with h,
  clear_value n,
  unfreezingI { induction n with n ih generalizing ι, },
  { -- The base case of the induction, when `ι` is empty
    haveI : is_empty ι := fintype.card_eq_zero_iff.mp h.symm,
    have zS : is_zero (⨁ f) := biproduct_is_zero_of_is_empty f,
    have zW : is_zero (W : C) := subobject_is_zero_of_is_zero zS _,
    exact ⟨∅, ⟨is_zero.iso zW (biproduct_is_zero_of_is_empty _), zW.eq_of_src _ _⟩⟩, },
  -- First we deal easily with the possibility that `W` is trivial.
  by_cases w : W = ⊥,
  { subst w,
    have zW := subobject.bot_is_zero (⨁ f),
    exact ⟨∅, ⟨is_zero.iso zW (biproduct_is_zero_of_is_empty _), zW.eq_of_src _ _⟩⟩, },
  -- Otherwise, we see that `W` must be isomorphic to one of the summands,
  -- plus some subobject `W'` of the other summands.
  obtain ⟨i, W', j₁, z⟩ := subobject_of_semisimple f W w, clear w,
  -- We then apply the inductive hypothesis to the other summand.
  obtain ⟨p', j₂, r'⟩ := ih (λ j : ({i}ᶜ : set ι), f j) W' (by simp only
    [←h, fintype.card_compl_set, tsub_zero, nat.succ_sub_succ_eq_sub, set.card_singleton]),
  clear ih h,
  -- We now have all the ingredients.
  -- We preparing the set of summands `p`, and the isomorphism `j`.
  let r : ({i}ᶜ : set ι) ↪ ι := function.embedding.subtype _,
  let ε : p' ≃ r '' p' := equiv.set.image r.1 p' r.2,
  have m : i ∉ r '' p',
  { rintro ⟨⟨h, v⟩, ⟨q, t⟩⟩,
    simp only [r, function.embedding.coe_fn_mk, subtype.coe_mk] at t,
    simpa only [set.mem_singleton, not_true, t, set.mem_compl_eq] using v, },
  refine ⟨insert i (r '' p'),
    j₁.trans ((biprod.map_iso (iso.refl _)
      (j₂.trans (biproduct.reindex ε (λ j : r '' p', f j)))).trans (biproduct.select _ _ m _).symm),
    _⟩,
  -- Finally, we need to calculate that `W.arrow = j.hom ≫ biproduct.from_subtype _ _`.
  ext j,
  simp only [z, r', set.mem_compl_eq, set.mem_singleton_iff, set.mem_insert_iff, set.mem_image,
    function.embedding.coe_subtype, set_coe.exists, subtype.coe_mk, exists_and_distrib_right,
    exists_eq_right, category.assoc, preadditive.comp_add, preadditive.add_comp,
    biproduct.from_subtype_π, dite_not, iso.trans_hom, biprod.map_iso_hom, iso.refl_hom,
    iso.symm_hom, biproduct.select_inv],
  by_cases t : j = i,
  { subst t,
    simp only [eq_self_iff_true, not_true, exists_false_left, or_false, biproduct.ι_π_self,
      category.comp_id, dif_pos, comp_zero, add_zero, iso.cancel_iso_hom_left],
    ext,
    { simp only [biprod.inl_fst, biprod.inl_map_assoc, biprod.inl_desc_assoc, category.id_comp],
      symmetry, exact (biproduct.ι_π_self _ _), },
    { simp only [biprod.inr_fst, biprod.inr_map_assoc, biprod.inr_desc_assoc, category.assoc,
        zero_eq_iso_comp_iff, preadditive.is_iso.comp_left_eq_zero],
      ext k,
      simp only [biproduct.ι_ι_le_assoc, comp_zero],
      refine biproduct.ι_π_ne _ _,
      simpa only [subtype.mk_eq_mk, ne.def, subtype.val_eq_coe]
        using ne_of_mem_of_not_mem k.2 m, }, },
  { simp only [t, not_false_iff, exists_true_left, false_or, dif_neg],
    simp only [biproduct.ι_π_ne _ (ne.symm t), comp_zero, zero_add, iso.cancel_iso_hom_left],
    ext,
    { simp only [biprod.inl_snd_assoc, zero_comp, biprod.inl_map_assoc, biprod.inl_desc_assoc,
        category.id_comp],
      split_ifs,
      { erw [biproduct.ι_π, dif_neg], simpa using (ne.symm t), },
      { simp only [comp_zero], },},
    { simp only [biprod.inr_snd_assoc, biprod.inr_map_assoc, biprod.inr_desc_assoc,
        category.assoc, iso.cancel_iso_hom_left, biproduct.reindex_hom],
      split_ifs with h h,
      { erw [biproduct.from_subtype_π, biproduct.ι_le_π, dif_pos h],
        simp only [h, t, set.mem_compl_eq, set.mem_singleton_iff, not_false_iff, set.mem_image,
          function.embedding.coe_subtype, set_coe.exists, subtype.coe_mk,
          exists_and_distrib_right, exists_eq_right, exists_true_left, dif_pos],
        ext ⟨⟨k, kh₁⟩, kh₂⟩,
        simp only [biproduct.ι_π, function.embedding.coe_subtype, subtype.coe_mk,
          subtype.mk_eq_mk, function.embedding.to_fun_eq_coe, equiv.set.image_apply,
          biproduct.ι_desc_assoc],
        refl, },
      { simp only [comp_zero],
        erw [biproduct.from_subtype_π, dif_neg h], }, }, },
end



#print is_complemented

variables [has_initial C] [initial_mono_class C] [has_pullbacks C] [has_images C]
variables

lemma foo' (n : ℕ) {ι : Type v} [decidable_eq ι] [fintype ι] (h : fintype.card ι = n)
  (f : ι → C) [∀ i, simple (f i)] [has_biproduct f] : is_complemented (subobject (⨁ (λ i, f i))) :=
begin
  unfreezingI { induction n with n ih generalizing ι, },
  { sorry, },
  split,
  intro W,
  by_cases h : W = ⊥,
  { subst h, exact ⟨⊤, is_compl_bot_top⟩, },
end

lemma foo {ι : Type v} [decidable_eq ι] [fintype ι] (f : ι → C) [∀ i, simple (f i)] [has_biproduct f] :
  is_complemented (subobject (⨁ (λ i, f i))) :=
foo' (fintype.card ι) rfl f
