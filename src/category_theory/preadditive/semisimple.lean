

import category_theory.preadditive.biproducts
import category_theory.preadditive.schur
import category_theory.subobject.lattice
import category_theory.noetherian

open category_theory
open category_theory.limits

universes v u

noncomputable theory
open_locale classical big_operators

variables {C : Type u} [category.{v} C] [preadditive C]
variables [has_binary_biproducts C] [has_kernels C]

-- def W' {W V V' : C} (i : W ⟶ V ⊞ V') [mono i] (j : V ⟶ W) [mono j] (w : j ≫ i = biprod.inl) :
--   C :=
-- kernel (i ≫ biprod.fst)

variables {ι : Type v} [decidable_eq ι] [fintype ι]

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

def aux (f : ι → C) [has_finite_biproducts C] [∀ i, simple (f i)]
  (V : subobject (⨁ f)) [simple (V : C)] (i : ι) [is_iso (V.arrow ≫ biproduct.π _ i)] : ⨁ f ⟶ ⨁ f :=
∑ (k : ι), if k = i then 0 else biproduct.π _ i ≫ inv (V.arrow ≫ biproduct.π _ i) ≫ V.arrow ≫ biproduct.π f k ≫ biproduct.ι f k

@[simp] lemma aux_π (f : ι → C) [has_finite_biproducts C] [∀ i, simple (f i)]
  (V : subobject (⨁ f)) [simple (V : C)] (i : ι) [is_iso (V.arrow ≫ biproduct.π _ i)] (j) :
  aux f V i ≫ biproduct.π f j = if j = i then 0 else biproduct.π _ i ≫ inv (V.arrow ≫ biproduct.π _ i) ≫ V.arrow ≫ biproduct.π f j := sorry

def aux₃ (f : ι → C) [has_finite_biproducts C] [∀ i, simple (f i)]
  (V : subobject (⨁ f)) [simple (V : C)] (i : ι) [is_iso (V.arrow ≫ biproduct.π _ i)] : ⨁ f ≅ ⨁ f :=
{ hom := 𝟙 _ - aux f V i,
  inv := 𝟙 _ + aux f V i,
  hom_inv_id' := begin
    apply biproduct.hom_ext,
    intro j,
    simp only [preadditive.sub_comp, preadditive.add_comp],
  end,
  hom_inv_id' := sorry, }

/--
Any simple subobject of a direct sum of simple objects is, up to isomorphism,
one of the summands.
-/
lemma simple_subobject_of_semisimple (f : ι → C) [has_finite_biproducts C] [∀ i, simple (f i)]
  (V : subobject (⨁ f)) [simple (V : C)] :
  ∃ (i : ι) (j : (V : C) ≅ f i) (k : Aut (⨁ f)), V.arrow ≫ k.hom = j.hom ≫ biproduct.ι f i :=
begin
  obtain ⟨i, _⟩ := simple_subobject_of_semisimple_iso_summand f V,
  resetI,
  refine ⟨i, as_iso (V.arrow ≫ biproduct.π _ i), _, _⟩,
  { split,

    sorry,
    sorry,
   },
  { sorry, },
end

/--
A subobject `W` of a direct sum of simple objects `⨁ f`
which itself contains a simple subobject can be written as
`W ≅ f i ⊞ W'` for some `i`, so that the inclusion takes `f i` to the corresponding summand,
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
  use i,
  sorry
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

def biproduct.π_le {p q : set ι} [decidable_pred (∈p)] [decidable_pred (∈q)] (h : p ⊆ q) (f : ι → C) [has_finite_biproducts C] :
  (⨁ (λ i : q, f i)) ⟶ (⨁ (λ i : p, f i)) :=
biproduct.lift (λ i, biproduct.π _ (⟨i.1, h i.2⟩ : q))

def biproduct.ι_le {p q : set ι} [decidable_pred (∈p)] [decidable_pred (∈q)] (h : p ⊆ q) (f : ι → C) [has_finite_biproducts C] :
  (⨁ (λ i : p, f i)) ⟶ (⨁ (λ i : q, f i)) :=
biproduct.desc (λ i, biproduct.ι (λ (i : q), f i) (⟨i.1, h i.2⟩ : q))

instance fsdf {ι : Type*} [decidable_eq ι] (p : set ι) [decidable_pred (∈p)] (i : ι) : decidable_pred (∈(insert i p)) := sorry

@[simps]
def biproduct.select (p : set ι) [decidable_pred (∈p)] (i : ι) (h : i ∉ p) (f : ι → C) [has_finite_biproducts C] :
  ⨁ (λ j : insert i p, f j) ≅ f i ⊞ (⨁ (λ j : p, f j)) :=
{ hom := begin
    apply biprod.lift,
    exact biproduct.π _ (⟨i, set.mem_insert i p⟩ : insert i p),
    apply biproduct.π_le,
    exact set.subset_insert i p,
end,
 inv := begin
   apply biprod.desc,
    exact biproduct.ι (λ (j : (insert i p)), f j) (⟨i, set.mem_insert i p⟩ : insert i p),
    apply biproduct.ι_le,
    exact set.subset_insert i p,
 end,
 hom_inv_id' := sorry,
 inv_hom_id' := sorry, }

def biproduct.reindex {β γ : Type v} [fintype β] [decidable_eq β] [fintype γ] [decidable_eq γ] (ε : β ≃ γ) (f : γ → C) [has_biproduct f] [has_biproduct (f ∘ ε)] :
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


/--
Up to isomorphism, any subobject of a direct sum of simple objects is just a subset of the summands.
-/
lemma subobject_of_semisimple'' [noetherian C] (f : ι → C) [has_finite_biproducts C] [∀ i, simple (f i)]
  (W : subobject (⨁ f)) :
  ∃ (p : set ι) (j : (W : C) ≅ ⨁ (λ i : p, f i)), W.arrow = j.hom ≫ biproduct.from_subtype _ _ :=
begin
  set n := fintype.card ι with h,
  clear_value n,
  unfreezingI { induction n with n ih generalizing ι, },
  { sorry, },
  by_cases w : W = ⊥,
  { sorry, },
  obtain ⟨i, W', j₁, z⟩ := subobject_of_semisimple f W w, clear w,
  obtain ⟨p', j₂, r'⟩ := ih (λ j : ({i}ᶜ : set ι), f j) W' sorry, clear ih h,
  let r : ({i}ᶜ : set ι) ↪ ι := ⟨λ x, x.1, by tidy⟩,
  let ε : p' ≃ r '' p' := equiv.set.image r.1 p' r.2,
  let j₃ : (⨁ λ (j : p'), (λ (j : ({i}ᶜ : set ι)), f j) j) ≅ (⨁ λ j : r '' p', f j) := biproduct.reindex ε (λ j : r '' p', f j),
  have m : i ∉ r '' p' := sorry,
  use insert i (r '' p'),
  refine ⟨_, _⟩,
  refine j₁.trans _,
  refine (biprod.map_iso (iso.refl _) (j₂.trans j₃)).trans _,
  refine (biproduct.select _ _ m _).symm,
  ext j,
  by_cases t : i = j,
  sorry { subst t, simp [z], ext, simp, symmetry, exact (biproduct.ι_π_self _ _),
    simp [biproduct.ι_le], ext, simp, sorry, },
  sorry { simp [z, t, r'], rw dif_neg, rw dif_neg, simp, ext, simp, simp, ext, simp, sorry, sorry, sorry, }
end

/--
If we have `V` inside `W`, and an inclusion of `W` into `V ⊞ Z`,
so that `V` is taken identically to `V`,
then `V` is complemented in `W`.
-/
def complement {W V Z : C} (i : V ⟶ W) [mono i] (j : W ⟶ V ⊞ Z) [mono j]
  (w : i ≫ j = biprod.inl) :
  W ≅ V ⊞ kernel (j ≫ biprod.fst) :=
sorry
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
