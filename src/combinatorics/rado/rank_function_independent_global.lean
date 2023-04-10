/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/

import combinatorics.rado.finset_section
import combinatorics.rado.rank_function_independent
import category_theory.cofiltered_system

/-!
# Extension from locally independent to globally independent sections

We use a compactness argument (essentially, that a product of discrete finite spaces
is compact) to show that an independent section exists if there are independent sections
on all finite subsets. See `rank_fn.independent.section`.

We also prove that an independent section `f` on `s` can be extended to `insert i s`
when the union of `f '' s` and `F i` has rank larger than `#s`; see
`rank_fn.independent_on.extends`.
-/

namespace rank_fn

open finset opposite

universes u v

variables {ι : Type u} {α : Type v} [decidable_eq α]

-- We take inspiration from `combinatorics.hall.basic`.

/-- The type of independent sections on a finite subset `s` of `ι` -/
def independent_sections_on (r : rank_fn α) (F : ι → finset α) (s : finset ι) : Type (max u v) :=
{f : s → α // is_section (s.restrict F) f ∧ independent r f}

variables {r : rank_fn α} {F : ι → finset α}

instance [inhabited α] : inhabited (independent_sections_on r F ∅) :=
{ default := ⟨λ _, default,
              by simp only [is_section, is_empty.forall_iff],
              λ s, independent_on_def.mpr
                      (by simp only [(eq_iff_true_of_subsingleton s ∅).mpr trivial, card_empty,
                                     image_empty, empty])⟩ }

/- It would be more convenient to use `{f : ι → α // is_section_on F f s ∧ independent_on r f s}`
   (as that would avoid fiddling with subtypes), but then the type would not always be finite,
   which is a crucial input for the compactness statement. -/

/- Everything below except for `rank_fn.independent.section` could be marked as `private`,
   since it is only used in its proof and unlikely to be useful outside of it. -/

/-- If we restrict an independent section on `s` to a subset `s'`, then the restriction
is also an independent section. -/
lemma independent_sections_on.restrict_prop {s' s : finset ι} (h : s' ⊆ s)
  (f : independent_sections_on r F s) :
  is_section (s'.restrict F) (λ i : s', f.val ⟨i, h i.property⟩) ∧
    independent r (λ i : s', f.val ⟨i, h i.property⟩) :=
begin
  classical,
  obtain ⟨hf₁, hf₂⟩ := f.property,
  refine ⟨λ i, (by simpa only using hf₁ ⟨i.val, h i.property⟩), λ t, _⟩,
  letI : has_coe s' s := { coe := λ i, ⟨i.val, h i.property⟩ },
  have hci : function.injective (coe : s' → s),
  { refine λ i j hij, subtype.ext_val _,
    replace hij := subtype.ext_iff_val.mp hij,
    exact hij, },
  specialize hf₂ (t.image (coe : s' → s)),
  rw independent_on_def at hf₂ ⊢,
  rw [subtype.val_eq_coe, card_image_of_injective _ hci] at hf₂,
  refine hf₂.trans_eq (congr_arg _ _),
  ext,
  simp_rw [mem_image],
  refine ⟨λ H, _, λ H, _⟩,
  { obtain ⟨i, ⟨j, hj₁, rfl⟩, hi₂⟩ := H,
    exact ⟨j, hj₁, hi₂⟩, },
  { obtain ⟨i, hi₁, hi₂⟩ := H,
    refine ⟨i, ⟨i, hi₁, rfl⟩, hi₂⟩, }
end

/-- The map restricting an independent section on `s` to an independent section on
a subset `s' ⊆ s`. -/
def independent_sections_on.restrict {s' s : finset ι} (h : s' ⊆ s)
  (f : independent_sections_on r F s) : independent_sections_on r F s' :=
⟨λ i, f.val ⟨i, h i.property⟩, independent_sections_on.restrict_prop h f⟩

lemma independent_sections_on.apply_mem {s : finset ι} (f : independent_sections_on r F s)
  (i : s) : f.val i ∈ F i :=
by simpa only [set.restrict_apply] using f.property.1 i

variables (r F)

/-- There are only finitely many (independent) sections on any finite subset. -/
instance independent_sections_on.finite (s : finset ι) : finite (independent_sections_on r F s) :=
begin
  rw independent_sections_on,
  let g : independent_sections_on r F s → (s → s.bUnion F) :=
    λ f i, ⟨f.val i, mem_bUnion.mpr ⟨i.val, i.property, f.apply_mem _⟩⟩,
  refine finite.of_injective g _,
  intros f f' h,
  simp only [g, function.funext_iff, subtype.val_eq_coe] at h,
  ext a,
  exact h a,
end

/-- The "Rado functor" on the opposite category of finite subsets of `ι`. It sends a subset `s`
to the type of indpendent sections (with respect to the rank function `r` and the family `F` of
finite subsets of `α`) on `s`, with the natural restriction maps. -/
def rado_functor : (finset ι)ᵒᵖ ⥤ Type (max u v) :=
{ obj := λ s, independent_sections_on r F s.unop,
  map := λ s t g f, independent_sections_on.restrict (category_theory.le_of_hom g.unop) f,
  -- spelling out a proof of `map_id'` seems to speed things up here
  map_id' := λ s, begin
    ext,
    simp only [independent_sections_on.restrict, subtype.val_eq_coe, subtype.coe_eta,
               category_theory.types_id_apply],
  end }

lemma le {ι} : ∀ {s t : finset ι}, s ⊆ t → s ≤ t := λ _ _ h, h

lemma rado_functor.map_apply {s t : finset ι} (hst : s ⊆ t) (f : (rado_functor r F).obj (op t)) :
  (rado_functor r F).map (category_theory.hom_of_le (le hst)).op f = f.restrict hst := rfl

/-- If the set of independent sections on each finite subset `s` of `ι` is nonempty,
then there is a global independent section on all of `ι`. -/
lemma independent.section (hnonempty : ∀ s : finset ι, nonempty (independent_sections_on r F s)) :
  ∃ f : ι → α, is_section F f ∧ independent r f :=
begin
  classical,
  haveI : ∀ (s : (finset ι)ᵒᵖ), nonempty ((rado_functor r F).obj s) := λ s, hnonempty s.unop,
  haveI : ∀ (s : (finset ι)ᵒᵖ), finite ((rado_functor r F).obj s) :=
    λ s, by {rw rado_functor, apply_instance},
  -- apply the compactness result from Category Theory
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system (rado_functor r F),
  -- extract the desired function from the section of the functor
  let f : ι → α := λ i, (u (op ({i} : finset ι))).val
                          ⟨i, by simp only [unop_op, mem_singleton]⟩,
  have H₁ : ∀ s : finset ι, (unop $ op s).restrict F = s.restrict F := λ s, rfl,
  have H₂ : ∀ s : finset ι, (u $ op s).val = s.restrict f,
  { intro s,
    ext i,
    simp only [subtype.val_eq_coe, restrict, f],
    have his : ({i} : finset ι) ⊆ s,
    { simpa only [singleton_subset_iff, unop_op s] using i.property, },
    rw [← hu (category_theory.hom_of_le (le his)).op, rado_functor.map_apply r F his],
    simp only [independent_sections_on.restrict, subtype.val_eq_coe, subtype.coe_mk, mk_coe], },
  refine ⟨f, λ i, _, λ s, _⟩,
  { have H := (u $ op {i}).property.1,
    simp_rw [H₁, H₂] at H,
    exact H ⟨i, mem_singleton_self i⟩, },
  { have H := (u $ op s).property.2,
    simp_rw [H₁, H₂] at H,
    exact independent_on_iff_independent_restrict.mpr H, }
end

variables {r F}

/-- If `f` is an independent section of `F` on `s`, `i ∉ s`, and `#s < r ((f '' s) ∪ F i)`,
then `f` extends to an independent section `g` on `insert i s`. -/
lemma independent_on.extends [decidable_eq ι] {f : ι → α} {s : finset ι} {i : ι} (hi : i ∉ s)
  (h₁ : is_section_on F f s) (h₂ : independent_on r f s) (hr : s.card < r (s.image f ∪ F i)) :
  ∃ g : ι → α, is_section_on F g (insert i s) ∧ s.eq_on f g ∧ independent_on r g (insert i s) :=
begin
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ F i, s.card + 1 ≤ r (insert a (s.image f)),
  { by_contra' H,
    have H' : ∀ a ∈ F i, r (insert a (s.image f)) = r (s.image f) :=
    λ a ha, le_antisymm ((nat.lt_add_one_iff.mp (H a ha)).trans h₂) (r.mono $ subset_insert _ _),
    exact nat.lt_irrefl _ (((hr.trans_eq (r.stationary' H')).trans_le (r.le_card _)).trans_le
            card_image_le), },
  -- We obtain the desired function by replacing the value of `f` at `i` by `a`.
  refine ⟨function.update f i a, λ j hj, _, λ j hj, (function.update_noteq (λ hf, _) _ _).symm, _⟩,
  { rcases eq_or_ne j i with rfl | hj',
    { rwa function.update_same, },
    { rw [function.update_noteq hj'],
      exact h₁ j ((mem_insert.mp hj).resolve_left hj'), } },
  { exact hi (hf ▸ hj), },
  { rw [independent_on_def, card_insert_eq_card_add_one hi],
    convert ha₂,
    rw [image_update f $ mem_insert_self _ _, ← insert_sdiff_singleton_self' hi, insert_eq,
        union_comm], }
end

end rank_fn
