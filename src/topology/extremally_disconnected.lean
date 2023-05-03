/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import topology.stone_cech

/-!
# Extremally disconnected spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An extremally disconnected topological space is a space in which the closure of every open set is
open. Such spaces are also called Stonean spaces. They are the projective objects in the category of
compact Hausdorff spaces.

## Main declarations

* `extremally_disconnected`: Predicate for a space to be extremally disconnected.
* `compact_t2.projective`: ¨Predicate for a topological space to be a projective object in the
  category of compact Hausdorff spaces.
* `compact_t2.projective.extremally_disconnected`: Compact Hausdorff spaces that are
  projective are extremally disconnected.

# TODO

Prove the converse to `compact_t2.projective.extremally_disconnected`, namely that a compact,
Hausdorff, extremally disconnected space is a projective object in the category of compact Hausdorff
spaces.

## References

[Gleason, *Projective topological spaces*][gleason1958]
-/

noncomputable theory

open set
open_locale classical

universes u v w
variables (X : Type u) [topological_space X]

open function

/-- An extremally disconnected topological space is a space
in which the closure of every open set is open. -/
class extremally_disconnected : Prop :=
(open_closure : ∀ U : set X, is_open U → is_open (closure U))

section

include X

/--  The assertion `compact_t2.projective` states that given continuous maps
`f : X → Z` and `g : Y → Z` with `g` surjective between `t_2`, compact topological spaces,
there exists a continuous lift `h : X → Y`, such that `f = g ∘ h`. -/
def compact_t2.projective : Prop :=
Π {Y Z : Type u} [topological_space Y] [topological_space Z],
  by exactI Π [compact_space Y] [t2_space Y] [compact_space Z] [t2_space Z],
  Π {f : X → Z} {g : Y → Z} (hf : continuous f) (hg : continuous g) (g_sur : surjective g),
  ∃ h : X → Y, continuous h ∧ g ∘ h = f

end

variable {X}

lemma stone_cech.projective [discrete_topology X] : compact_t2.projective (stone_cech X) :=
begin
  introsI Y Z _tsY _tsZ _csY _t2Y _csZ _csZ f g hf hg g_sur,
  let s : Z → Y := λ z, classical.some $ g_sur z,
  have hs : g ∘ s = id := funext (λ z, classical.some_spec (g_sur z)),
  let t := s ∘ f ∘ stone_cech_unit,
  have ht : continuous t := continuous_of_discrete_topology,
  let h : stone_cech X → Y := stone_cech_extend ht,
  have hh : continuous h := continuous_stone_cech_extend ht,
  refine ⟨h, hh, dense_range_stone_cech_unit.equalizer (hg.comp hh) hf _⟩,
  rw [comp.assoc, stone_cech_extend_extends ht, ← comp.assoc, hs, comp.left_id],
end

protected lemma compact_t2.projective.extremally_disconnected [compact_space X] [t2_space X]
  (h : compact_t2.projective X) :
  extremally_disconnected X :=
begin
  refine { open_closure := λ U hU, _ },
  let Z₁ : set (X × bool) := Uᶜ ×ˢ {tt},
  let Z₂ : set (X × bool) := closure U ×ˢ {ff},
  let Z : set (X × bool) := Z₁ ∪ Z₂,
  have hZ₁₂ : disjoint Z₁ Z₂ := disjoint_left.2 (λ x hx₁ hx₂, by cases hx₁.2.symm.trans hx₂.2),
  have hZ₁ : is_closed Z₁ := hU.is_closed_compl.prod  (t1_space.t1 _),
  have hZ₂ : is_closed Z₂ := is_closed_closure.prod (t1_space.t1 ff),
  have hZ : is_closed Z := hZ₁.union  hZ₂,
  let f : Z → X := prod.fst ∘ subtype.val,
  have f_cont : continuous f := continuous_fst.comp continuous_subtype_val,
  have f_sur : surjective f,
  { intro x,
    by_cases hx : x ∈ U,
    { exact ⟨⟨(x, ff), or.inr ⟨subset_closure hx, set.mem_singleton _⟩⟩, rfl⟩  },
    { exact ⟨⟨(x, tt), or.inl ⟨hx, set.mem_singleton _⟩⟩, rfl⟩ } },
  haveI : compact_space Z := is_compact_iff_compact_space.mp hZ.is_compact,
  obtain ⟨g, hg, g_sec⟩ := h continuous_id f_cont f_sur,
  let φ := coe ∘ g,
  have hφ : continuous φ := continuous_subtype_val.comp hg,
  have hφ₁ : ∀ x, (φ x).1 = x := congr_fun g_sec,
  suffices : closure U = φ ⁻¹' Z₂,
  { rw [this, set.preimage_comp, ←is_closed_compl_iff, ←preimage_compl,
      ←preimage_subtype_coe_eq_compl subset.rfl],
    { exact hZ₁.preimage hφ },
    { rw [hZ₁₂.inter_eq, inter_empty] } },
  refine (closure_minimal _ $ hZ₂.preimage hφ).antisymm (λ x hx, _),
  { rintro x hx,
    have : φ x ∈ (Z₁ ∪ Z₂) := (g x).2,
    simpa [hx, hφ₁] using this },
  { rw ←hφ₁ x,
    exact hx.1 }
end
