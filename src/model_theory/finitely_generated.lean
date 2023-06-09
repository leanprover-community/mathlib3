/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.substructures

/-!
# Finitely Generated First-Order Structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file defines what it means for a first-order (sub)structure to be finitely or countably
generated, similarly to other finitely-generated objects in the algebra library.

## Main Definitions
* `first_order.language.substructure.fg` indicates that a substructure is finitely generated.
* `first_order.language.Structure.fg` indicates that a structure is finitely generated.
* `first_order.language.substructure.cg` indicates that a substructure is countably generated.
* `first_order.language.Structure.cg` indicates that a structure is countably generated.


## TODO
Develop a more unified definition of finite generation using the theory of closure operators, or use
this definition of finite generation to define the others.

-/

open_locale first_order
open set

namespace first_order
namespace language
open Structure

variables {L : language} {M : Type*} [L.Structure M]

namespace substructure

/-- A substructure of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
def fg (N : L.substructure M) : Prop := ∃ S : finset M, closure L ↑S = N

theorem fg_def {N : L.substructure M} :
  N.fg ↔ ∃ S : set M, S.finite ∧ closure L S = N :=
⟨λ ⟨t, h⟩, ⟨_, finset.finite_to_set t, h⟩, begin
  rintro ⟨t', h, rfl⟩,
  rcases finite.exists_finset_coe h with ⟨t, rfl⟩,
  exact ⟨t, rfl⟩
end⟩

lemma fg_iff_exists_fin_generating_family {N : L.substructure M} :
  N.fg ↔ ∃ (n : ℕ) (s : fin n → M), closure L (range s) = N :=
begin
  rw fg_def,
  split,
  { rintros ⟨S, Sfin, hS⟩,
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding,
    exact ⟨n, f, hS⟩, },
  { rintros ⟨n, s, hs⟩,
    refine ⟨range s, finite_range s, hs⟩ },
end

theorem fg_bot : (⊥ : L.substructure M).fg :=
⟨∅, by rw [finset.coe_empty, closure_empty]⟩

theorem fg_closure {s : set M} (hs : s.finite) : fg (closure L s) :=
⟨hs.to_finset, by rw [hs.coe_to_finset]⟩

theorem fg_closure_singleton (x : M) : fg (closure L ({x} : set M)) :=
fg_closure (finite_singleton x)

theorem fg.sup {N₁ N₂ : L.substructure M}
  (hN₁ : N₁.fg) (hN₂ : N₂.fg) : (N₁ ⊔ N₂).fg :=
let ⟨t₁, ht₁⟩ := fg_def.1 hN₁, ⟨t₂, ht₂⟩ := fg_def.1 hN₂ in
fg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩

theorem fg.map {N : Type*} [L.Structure N] (f : M →[L] N) {s : L.substructure M} (hs : s.fg) :
  (s.map f).fg :=
let ⟨t, ht⟩ := fg_def.1 hs in fg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩

theorem fg.of_map_embedding {N : Type*} [L.Structure N] (f : M ↪[L] N) {s : L.substructure M}
  (hs : (s.map f.to_hom).fg) : s.fg :=
begin
  rcases hs with ⟨t, h⟩,
  rw fg_def,
  refine ⟨f ⁻¹' t, t.finite_to_set.preimage (f.injective.inj_on _), _⟩,
  have hf : function.injective f.to_hom := f.injective,
  refine map_injective_of_injective hf _,
  rw [← h, map_closure, embedding.coe_to_hom, image_preimage_eq_of_subset],
  intros x hx,
  have h' := subset_closure hx,
  rw h at h',
  exact hom.map_le_range h'
end

/-- A substructure of `M` is countably generated if it is the closure of a countable subset of `M`.
-/
def cg (N : L.substructure M) : Prop := ∃ S : set M, S.countable ∧ closure L S = N

theorem cg_def {N : L.substructure M} :
  N.cg ↔ ∃ S : set M, S.countable ∧ closure L S = N := iff.refl _

theorem fg.cg {N : L.substructure M} (h : N.fg) : N.cg :=
begin
  obtain ⟨s, hf, rfl⟩ := fg_def.1 h,
  refine ⟨s, hf.countable, rfl⟩,
end

lemma cg_iff_empty_or_exists_nat_generating_family {N : L.substructure M} :
  N.cg ↔ (↑N = (∅ : set M)) ∨ ∃ (s : ℕ → M), closure L (range s) = N :=
begin
  rw cg_def,
  split,
  { rintros ⟨S, Scount, hS⟩,
    cases eq_empty_or_nonempty ↑N with h h,
    { exact or.intro_left _ h },
    obtain ⟨f, h'⟩ := (Scount.union (set.countable_singleton h.some)).exists_eq_range
      (singleton_nonempty h.some).inr,
    refine or.intro_right _ ⟨f, _⟩,
    rw [← h', closure_union, hS, sup_eq_left, closure_le],
    exact singleton_subset_iff.2 h.some_mem },
  { intro h,
    cases h with h h,
    { refine ⟨∅, countable_empty, closure_eq_of_le (empty_subset _) _⟩,
      rw [← set_like.coe_subset_coe, h],
      exact empty_subset _ },
    { obtain ⟨f, rfl⟩ := h,
      exact ⟨range f, countable_range _, rfl⟩ } },
end

theorem cg_bot : (⊥ : L.substructure M).cg := fg_bot.cg

theorem cg_closure {s : set M} (hs : s.countable) : cg (closure L s) :=
⟨s, hs, rfl⟩

theorem cg_closure_singleton (x : M) : cg (closure L ({x} : set M)) := (fg_closure_singleton x).cg

theorem cg.sup {N₁ N₂ : L.substructure M}
  (hN₁ : N₁.cg) (hN₂ : N₂.cg) : (N₁ ⊔ N₂).cg :=
let ⟨t₁, ht₁⟩ := cg_def.1 hN₁, ⟨t₂, ht₂⟩ := cg_def.1 hN₂ in
cg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩

theorem cg.map {N : Type*} [L.Structure N] (f : M →[L] N) {s : L.substructure M} (hs : s.cg) :
  (s.map f).cg :=
let ⟨t, ht⟩ := cg_def.1 hs in cg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩

theorem cg.of_map_embedding {N : Type*} [L.Structure N] (f : M ↪[L] N) {s : L.substructure M}
  (hs : (s.map f.to_hom).cg) : s.cg :=
begin
  rcases hs with ⟨t, h1, h2⟩,
  rw cg_def,
  refine ⟨f ⁻¹' t, h1.preimage f.injective, _⟩,
  have hf : function.injective f.to_hom := f.injective,
  refine map_injective_of_injective hf _,
  rw [← h2, map_closure, embedding.coe_to_hom, image_preimage_eq_of_subset],
  intros x hx,
  have h' := subset_closure hx,
  rw h2 at h',
  exact hom.map_le_range h'
end

theorem cg_iff_countable [countable (Σl, L.functions l)] {s : L.substructure M} :
  s.cg ↔ countable s :=
begin
  refine ⟨_, λ h, ⟨s, h.to_set, s.closure_eq⟩⟩,
  rintro ⟨s, h, rfl⟩,
  exact h.substructure_closure L
end

end substructure

open substructure

namespace Structure

variables (L) (M)

/-- A structure is finitely generated if it is the closure of a finite subset. -/
class fg : Prop := (out : (⊤ : L.substructure M).fg)

/-- A structure is countably generated if it is the closure of a countable subset. -/
class cg : Prop := (out : (⊤ : L.substructure M).cg)

variables {L M}

lemma fg_def : fg L M ↔ (⊤ : L.substructure M).fg := ⟨λ h, h.1, λ h, ⟨h⟩⟩

/-- An equivalent expression of `Structure.fg` in terms of `set.finite` instead of `finset`. -/
lemma fg_iff : fg L M ↔ ∃ S : set M, S.finite ∧ closure L S = (⊤ : L.substructure M) :=
by rw [fg_def, substructure.fg_def]

lemma fg.range {N : Type*} [L.Structure N] (h : fg L M) (f : M →[L] N) :
  f.range.fg :=
begin
  rw [hom.range_eq_map],
  exact (fg_def.1 h).map f,
end

lemma fg.map_of_surjective {N : Type*} [L.Structure N] (h : fg L M) (f : M →[L] N)
  (hs : function.surjective f) :
  fg L N :=
begin
  rw ← hom.range_eq_top at hs,
  rw [fg_def, ← hs],
  exact h.range f,
end

lemma cg_def : cg L M ↔ (⊤ : L.substructure M).cg := ⟨λ h, h.1, λ h, ⟨h⟩⟩

/-- An equivalent expression of `Structure.cg`. -/
lemma cg_iff : cg L M ↔ ∃ S : set M, S.countable ∧ closure L S = (⊤ : L.substructure M) :=
by rw [cg_def, substructure.cg_def]

lemma cg.range {N : Type*} [L.Structure N] (h : cg L M) (f : M →[L] N) :
  f.range.cg :=
begin
  rw [hom.range_eq_map],
  exact (cg_def.1 h).map f,
end

lemma cg.map_of_surjective {N : Type*} [L.Structure N] (h : cg L M) (f : M →[L] N)
  (hs : function.surjective f) :
  cg L N :=
begin
  rw ← hom.range_eq_top at hs,
  rw [cg_def, ← hs],
  exact h.range f,
end

lemma cg_iff_countable [countable (Σl, L.functions l)] : cg L M ↔ countable M :=
by rw [cg_def, cg_iff_countable, top_equiv.to_equiv.countable_iff]

lemma fg.cg (h : fg L M) : cg L M :=
cg_def.2 (fg_def.1 h).cg

@[priority 100] instance cg_of_fg [h : fg L M] : cg L M := h.cg

end Structure

lemma equiv.fg_iff {N : Type*} [L.Structure N] (f : M ≃[L] N) :
  Structure.fg L M ↔ Structure.fg L N :=
⟨λ h, h.map_of_surjective f.to_hom f.to_equiv.surjective,
  λ h, h.map_of_surjective f.symm.to_hom f.to_equiv.symm.surjective⟩

lemma substructure.fg_iff_Structure_fg (S : L.substructure M) :
  S.fg ↔ Structure.fg L S :=
begin
  rw Structure.fg_def,
  refine ⟨λ h, fg.of_map_embedding S.subtype _, λ h, _⟩,
  { rw [← hom.range_eq_map, range_subtype],
    exact h },
  { have h := h.map S.subtype.to_hom,
    rw [← hom.range_eq_map, range_subtype] at h,
    exact h }
end

lemma equiv.cg_iff {N : Type*} [L.Structure N] (f : M ≃[L] N) :
  Structure.cg L M ↔ Structure.cg L N :=
⟨λ h, h.map_of_surjective f.to_hom f.to_equiv.surjective,
  λ h, h.map_of_surjective f.symm.to_hom f.to_equiv.symm.surjective⟩

lemma substructure.cg_iff_Structure_cg (S : L.substructure M) :
  S.cg ↔ Structure.cg L S :=
begin
  rw Structure.cg_def,
  refine ⟨λ h, cg.of_map_embedding S.subtype _, λ h, _⟩,
  { rw [← hom.range_eq_map, range_subtype],
    exact h },
  { have h := h.map S.subtype.to_hom,
    rw [← hom.range_eq_map, range_subtype] at h,
    exact h }
end

end language
end first_order
