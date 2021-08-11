/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import topology.separation
import topology.opens

/-!
# The Alexandroff Compactification
We construct the Alexandroff compactification of an arbitrary topological space `X` and prove
some properties inherited from `X`.

## Main defintion
* `alexandroff`: the Alexandroff compactification
* `of`: the inclusion map defined by `option.some`. This map requires the argument
        `topological_space X`
* `infty`: the extra point

## Main results
* The topological structure of `alexandroff X`
* The connectedness of `alexandroff X` for a noncompact, preconnected `X`
* `alexandroff X` is `T₁` for a T₁ space `X`
* `alexandroff X` is Hausdorff if `X` is locally compact and Hausdorff
-/

noncomputable theory
open set
open_locale classical topological_space

section basic

/-- The Alexandroff extension of an arbitrary topological space `X` -/
@[nolint unused_arguments]
def alexandroff (X : Type*) [topological_space X] := option X

variables {X : Type*} [topological_space X]

/-- The embedding of `X` to its Alexandroff extension -/
def of : X → alexandroff X := some

/-- The range of the embedding -/
def range_of (X : Type*) [topological_space X] : set (alexandroff X) := range (@of X _)

lemma of_apply {x : X} : of x = some x := rfl

lemma of_injective : function.injective (@of X _) :=
option.some_injective X

/-- The point at infinity -/
def infty : alexandroff X := none
localized "notation `∞` := infty" in alexandroff

namespace alexandroff

instance : has_coe_t X (alexandroff X) := ⟨of⟩

instance : inhabited (alexandroff X) := ⟨∞⟩

@[norm_cast]
lemma coe_eq_coe {x y : X} : (x : alexandroff X) = y ↔ x = y :=
of_injective.eq_iff

@[simp] lemma coe_ne_infty (x : X) : (x : alexandroff X) ≠ ∞  .
@[simp] lemma infty_ne_coe (x : X) : ∞ ≠ (x : alexandroff X) .
@[simp] lemma of_eq_coe {x : X} : (of x : alexandroff X) = x := rfl

/-- Recursor for `alexandroff` using the preferred forms `∞` and `↑x`. -/
@[elab_as_eliminator]
def rec_infty_coe (C : alexandroff X → Sort*) (h₁ : C infty) (h₂ : Π (x : X), C x) :
  Π (z : alexandroff X), C z :=
option.rec h₁ h₂

lemma ne_infty_iff_exists {x : alexandroff X} :
  x ≠ ∞ ↔ ∃ (y : X), x = y :=
by { induction x using alexandroff.rec_infty_coe; simp }

@[simp] lemma coe_mem_range_of (x : X) : (x : alexandroff X) ∈ (range_of X) :=
by simp [range_of]

lemma union_infty_eq_univ : (range_of X ∪ {∞}) = univ :=
begin
  refine le_antisymm (subset_univ _) (λ x hx, _),
  induction x using alexandroff.rec_infty_coe; simp
end

@[simp] lemma infty_not_mem_range_of : ∞ ∉ range_of X :=
by simp [range_of]

@[simp] lemma not_mem_range_of_iff (x : alexandroff X) :
  x ∉ range_of X ↔ x = ∞ :=
by { induction x using alexandroff.rec_infty_coe; simp [infty_not_mem_range_of] }

attribute [nolint simp_nf] not_mem_range_of_iff

lemma infty_not_mem_image_of {s : set X} : ∞ ∉ of '' s :=
not_mem_subset (image_subset_range _ _) infty_not_mem_range_of

lemma inter_infty_eq_empty : (range_of X) ∩ {∞} = ∅ :=
by { ext x, induction x using alexandroff.rec_infty_coe; simp }

lemma of_preimage_infty : (of⁻¹' {∞} : set X) = ∅ :=
by { ext, simp }

end alexandroff

end basic

open alexandroff
open_locale alexandroff

section topology

variables {X : Type*} [topological_space X]

instance : topological_space (alexandroff X) :=
{ is_open := λ s, (∞ ∈ s → is_compact (of⁻¹' s)ᶜ) ∧ is_open (of⁻¹' s),
  is_open_univ := by simp,
  is_open_inter :=
  λ s t ⟨hms, hs⟩ ⟨hmt, ht⟩, begin
    refine ⟨_, hs.inter ht⟩,
    rintros ⟨hms', hmt'⟩,
    simpa [compl_inter] using (hms hms').union (hmt hmt')
  end,
  is_open_sUnion :=
  λ S ht, begin
    suffices : is_open (of⁻¹' ⋃₀S),
    { refine ⟨_, this⟩,
      intro h,
      obtain ⟨(a : set (alexandroff X)), ha, ha'⟩ := mem_sUnion.mp h,
      replace ht := (ht a ha).1 ha',
      refine compact_of_is_closed_subset ht this.is_closed_compl _,
      rw [compl_subset_compl, preimage_subset_iff],
      intros y hy,
      refine ⟨a, ha, hy⟩ },
     rw is_open_iff_forall_mem_open,
     simp only [and_imp, exists_prop, mem_Union, preimage_sUnion, mem_preimage, of_eq_coe,
                exists_imp_distrib],
     intros y s hs hy,
     refine ⟨of ⁻¹' s, subset_subset_Union _ (subset_subset_Union hs (subset.refl _)), _,
        mem_preimage.mpr hy⟩,
     exact (ht s hs).2
  end }

variables {s : set (alexandroff X)} {s' : set X}

lemma is_open_alexandroff_iff_aux :
  is_open s ↔ (∞ ∈ s → is_compact (of⁻¹' s)ᶜ) ∧ is_open (of⁻¹' s) :=
iff.rfl

lemma is_open_iff_of_mem' (h : ∞ ∈ s) :
  is_open s ↔ is_compact (of⁻¹' s)ᶜ ∧ is_open (of⁻¹' s) :=
by simp [is_open_alexandroff_iff_aux, h]

lemma is_open_iff_of_mem (h : ∞ ∈ s) :
  is_open s ↔ is_compact (of⁻¹' s)ᶜ ∧ is_closed (of⁻¹' s)ᶜ :=
by simp [is_open_alexandroff_iff_aux, h, is_closed_compl_iff]

lemma is_open_iff_of_not_mem (h : ∞ ∉ s) :
  is_open s ↔ is_open (of⁻¹' s) :=
by simp [is_open_alexandroff_iff_aux, h]

lemma is_open_of_is_open (h : is_open s) : is_open (of⁻¹' s) := h.2

end topology

section topological_prop

variables {X : Type*} [topological_space X]

@[continuity] lemma continuous_of : continuous (@of X _) :=
continuous_def.mpr (λ s hs, is_open_of_is_open hs)

/-- An open set in `alexandroff X` constructed from a closed compact set in `X` -/
def opens_of_compl {s : set X} (h : is_compact s ∧ is_closed s) :
  topological_space.opens (alexandroff X) :=
⟨(of '' s)ᶜ, by { rw [is_open_iff_of_mem ((mem_compl_iff _ _).mpr infty_not_mem_image_of),
  preimage_compl, compl_compl, of_injective.preimage_image _], exact h }⟩

lemma infty_mem_opens_of_compl {s : set X} (h : is_compact s ∧ is_closed s) :
  ∞ ∈ (opens_of_compl h) :=
by { simp only [opens_of_compl, topological_space.opens.coe_mk],
     exact mem_compl infty_not_mem_image_of }

lemma is_open_map_of : is_open_map (@of X _) :=
λ s hs, begin
  rw [← preimage_image_eq s of_injective] at hs,
  rwa is_open_iff_of_not_mem infty_not_mem_image_of
end

lemma is_open_range_of : is_open (@range_of X _) :=
is_open_map_of.is_open_range

instance : compact_space (alexandroff X) :=
{ compact_univ :=
  begin
    refine is_compact_of_finite_subcover (λ ι Z h H, _),
    simp only [univ_subset_iff] at H ⊢,
    rcases Union_eq_univ_iff.mp H ∞ with ⟨K, hK⟩,
    have minor₁ : is_compact (of⁻¹' Z K)ᶜ,
    { specialize h K, rw is_open_iff_of_mem hK at h, exact h.1 },
    let p : ι → set X := λ i, of⁻¹' Z i,
    have minor₂ : ∀ i, is_open (p i) := λ i, is_open_of_is_open (h i),
    have minor₃ : (of⁻¹' Z K)ᶜ ⊆ ⋃ i, p i :=
      by simp only [p, ← preimage_Union, H, preimage_univ, subset_univ],
    rcases is_compact_iff_finite_subcover.mp minor₁ p minor₂ minor₃ with ⟨ι', H'⟩,
    refine ⟨insert K ι', _⟩,
    rw ← preimage_compl at H',
    simp only [Union_eq_univ_iff],
    intros x,
    by_cases hx : x ∈ Z K,
    { exact ⟨K, mem_Union.mpr ⟨finset.mem_insert_self _ _, hx⟩⟩ },
    { have triv₁ : x ≠ ∞ := (ne_of_mem_of_not_mem hK hx).symm,
      rcases ne_infty_iff_exists.mp triv₁ with ⟨y, hy⟩,
      have triv₂ : (y : alexandroff X) ∈ {x} := mem_singleton_of_eq hy.symm,
      rw [← mem_compl_iff, ← singleton_subset_iff] at hx,
      have : of⁻¹' {x} ⊆ of⁻¹' (Z K)ᶜ := λ y hy, hx hy,
      have key : y ∈ ⋃ (i : ι) (H : i ∈ ι'), p i := this.trans H' (mem_preimage.mpr triv₂),
      rcases mem_bUnion_iff'.mp key with ⟨i, hi, hyi⟩,
      refine ⟨i, mem_Union.mpr ⟨finset.subset_insert _ ι' hi, _⟩⟩,
      simpa [hy] using hyi }
  end }

lemma dense_range_of (h : ¬ is_compact (univ : set X)) : dense (@range_of X _) :=
begin
  refine dense_iff_inter_open.mpr (λ s hs Hs, _),
  by_cases H : ∞ ∈ s,
  { rw is_open_iff_of_mem H at hs,
    have minor₁ : s ≠ {∞},
    { rintro rfl,
      rw [of_preimage_infty, compl_empty] at hs,
      exact h hs.1 },
    have minor₂ : of⁻¹' s ≠ ∅,
    { by_contra w,
      rw [not_not, eq_empty_iff_forall_not_mem] at w,
      simp only [mem_preimage] at w,
      have : ∀ z ∈ s, z = ∞ := λ z hz,
        by_contra (λ w', let ⟨x, hx⟩ := ne_infty_iff_exists.mp w' in
          by rw hx at hz; exact (w x) hz),
      exact minor₁ (eq_singleton_iff_unique_mem.mpr ⟨H, this⟩) },
    rcases ne_empty_iff_nonempty.mp minor₂ with ⟨x, hx⟩,
    exact ⟨of x, hx, x, rfl⟩ },
  { rcases Hs with ⟨z, hz⟩,
    rcases ne_infty_iff_exists.mp (ne_of_mem_of_not_mem hz H) with ⟨x, hx⟩,
    rw hx at hz,
    exact ⟨of x, hz, x, rfl⟩ }
end

lemma connected_space_alexandroff [preconnected_space X] (h : ¬ is_compact (univ : set X)) :
  connected_space (alexandroff X) :=
{ is_preconnected_univ :=
  begin
    rw ← dense_iff_closure_eq.mp (dense_range_of h),
    convert is_preconnected.closure
      (is_preconnected_univ.image of continuous_of.continuous_on),
    rw image_univ,
    refl,
    apply_instance
  end,
  to_nonempty := ⟨∞⟩ }

instance [t1_space X] : t1_space (alexandroff X) :=
{ t1 :=
  λ z, begin
    induction z using alexandroff.rec_infty_coe,
    { rw [← is_open_compl_iff, compl_eq_univ_diff, ← union_infty_eq_univ,
          union_diff_cancel_right (subset.antisymm_iff.mp inter_infty_eq_empty).1],
      exact is_open_range_of },
    { have : ∞ ∈ ({z}ᶜ : set (alexandroff X)) :=
        mem_compl (λ w, (infty_ne_coe z) (mem_singleton_iff.mp w)),
      rw [← is_open_compl_iff, is_open_iff_of_mem this],
      rw [preimage_compl, compl_compl, ← of_eq_coe,
          ← image_singleton, of_injective.preimage_image _],
      exact ⟨is_compact_singleton, is_closed_singleton⟩ }
  end }

instance [locally_compact_space X] [t2_space X] : t2_space (alexandroff X) :=
{ t2 :=
  λ x y hxy, begin
    have key : ∀ (z : alexandroff X), z ≠ ∞ →
      ∃ (u v : set (alexandroff X)), is_open u ∧ is_open v ∧ ∞ ∈ u ∧ z ∈ v ∧ u ∩ v = ∅ :=
    λ z h, begin
      rcases ne_infty_iff_exists.mp h with ⟨y', hy'⟩,
      rcases exists_open_with_compact_closure y' with ⟨u, hu, huy', Hu⟩,
      have minor₁ : _ ∧ is_closed (closure u) := ⟨Hu, is_closed_closure⟩,
      refine ⟨opens_of_compl minor₁, of '' u, _⟩,
      refine ⟨(opens_of_compl minor₁).2, is_open_map_of _ hu,
        infty_mem_opens_of_compl minor₁, ⟨y', huy', hy'.symm⟩, _⟩,
      simp only [opens_of_compl, topological_space.opens.coe_mk],
      have minor₂ : (of '' closure u)ᶜ ∩ of '' u ⊆ (of '' u)ᶜ ∩ of '' u,
      { apply inter_subset_inter_left,
        simp only [compl_subset_compl, image_subset _ (subset_closure)] },
      rw compl_inter_self at minor₂,
      exact eq_empty_of_subset_empty minor₂
    end,
    induction x using alexandroff.rec_infty_coe; induction y using alexandroff.rec_infty_coe,
    { simpa using hxy },
    { simpa using key y hxy.symm },
    { rcases key x hxy with ⟨u, v, hu, hv, hxu, hyv, huv⟩,
      exact ⟨v, u, hv, hu, hyv, hxu, (inter_comm u v) ▸ huv⟩ },
    { have hxy' : x ≠ y := λ w, hxy (coe_eq_coe.mpr w),
      rcases t2_separation hxy' with ⟨u, v, hu, hv, hxu, hyv, huv⟩,
      refine ⟨of '' u, of '' v, is_open_map_of _ hu, is_open_map_of _ hv,
        ⟨x, hxu, rfl⟩, ⟨y, hyv, rfl⟩, _⟩,
      simp only [image_inter of_injective, huv, image_empty], }
  end }

end topological_prop
