/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.AffineScheme
import topology.spectral.hom

/-!
# Quasi-compact morphisms

A morphism of schemes is quasi-compact if the preimages of quasi-compact open sets are
quasi-compact.

It suffices to check that preimages of affine open sets are compact
(`quasi_compact_iff_forall_affine`).

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism is `quasi-compact` if the underlying map of topological spaces is, i.e. if the preimages
of quasi-compact open sets are quasi-compact.
-/
@[mk_iff]
class quasi_compact (f : X ⟶ Y) : Prop :=
(is_compact_preimage : ∀ U : set Y.carrier, is_open U → is_compact U → is_compact (f.1.base ⁻¹' U))

lemma quasi_compact_iff_spectral : quasi_compact f ↔ is_spectral_map f.1.base :=
⟨λ ⟨h⟩, ⟨by continuity, h⟩, λ h, ⟨h.2⟩⟩

@[priority 900]
instance quasi_compact_of_is_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] : quasi_compact f :=
begin
  constructor,
  intros U hU hU',
  convert hU'.image (inv f.1.base).continuous_to_fun using 1,
  rw set.image_eq_preimage_of_inverse,
  delta function.left_inverse,
  exacts [is_iso.inv_hom_id_apply f.1.base, is_iso.hom_inv_id_apply f.1.base]
end

instance quasi_compact_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [quasi_compact f] [quasi_compact g] : quasi_compact (f ≫ g) :=
begin
  constructor,
  intros U hU hU',
  rw [Scheme.comp_val_base, coe_comp, set.preimage_comp],
  apply quasi_compact.is_compact_preimage,
  { exact continuous.is_open_preimage (by continuity) _ hU },
  apply quasi_compact.is_compact_preimage; assumption
end

lemma is_compact_open_iff_eq_finset_affine_union {X : Scheme} (U : set X.carrier) :
  is_compact U ∧ is_open U ↔
    ∃ (s : set X.affine_opens), s.finite ∧ U = ⋃ (i : X.affine_opens) (h : i ∈ s), i :=
begin
  apply opens.is_compact_open_iff_eq_finite_Union_of_is_basis
    (coe : X.affine_opens → opens X.carrier),
  { rw subtype.range_coe, exact is_basis_affine_open X },
  { intro i, exact i.2.is_compact }
end

lemma is_compact_open_iff_eq_basic_open_union {X : Scheme} [is_affine X] (U : set X.carrier) :
  is_compact U ∧ is_open U ↔
    ∃ (s : set (X.presheaf.obj (op ⊤))), s.finite ∧
      U = ⋃ (i : X.presheaf.obj (op ⊤)) (h : i ∈ s), X.basic_open i :=
begin
  apply opens.is_compact_open_iff_eq_finite_Union_of_is_basis,
  { exact is_basis_basic_open X },
  { intro i, exact ((top_is_affine_open _).basic_open_is_affine _).is_compact }
end

lemma quasi_compact_iff_forall_affine : quasi_compact f ↔
  ∀ U : opens Y.carrier, is_affine_open U → is_compact (f.1.base ⁻¹' (U : set Y.carrier)) :=
begin
  rw quasi_compact_iff,
  refine ⟨λ H U hU, H U U.prop hU.is_compact, _⟩,
  intros H U hU hU',
  obtain ⟨S, hS, rfl⟩ := (is_compact_open_iff_eq_finset_affine_union U).mp ⟨hU', hU⟩,
  simp only [set.preimage_Union, subtype.val_eq_coe],
  exact hS.compact_bUnion (λ i _, H i i.prop)
end

@[elab_as_eliminator]
lemma compact_open_induction_on {P : opens X.carrier → Prop} (S : opens X.carrier)
  (hS : is_compact S.1)
  (h₁ : P ⊥)
  (h₂ : ∀ (S : opens X.carrier) (hS : is_compact S.1) (U : X.affine_opens), P S → P (S ⊔ U)) :
    P S :=
begin
  classical,
  obtain ⟨s, hs, hs'⟩ := (is_compact_open_iff_eq_finset_affine_union S.1).mp ⟨hS, S.2⟩,
  replace hs' : S = supr (λ i : s, (i : opens X.carrier)) := by { ext1, simpa using hs' },
  subst hs',
  apply hs.induction_on,
  { convert h₁, rw supr_eq_bot, rintro ⟨_, h⟩, exact h.elim },
  { intros x s h₃ hs h₄,
    have : is_compact (⨆ i : s, (i : opens X.carrier)).1,
    { refine ((is_compact_open_iff_eq_finset_affine_union _).mpr _).1, exact ⟨s, hs, by simp⟩ },
    convert h₂ _ this x h₄,
    simp only [coe_coe],
    rw [supr_subtype, sup_comm],
    conv_rhs { rw supr_subtype },
    exact supr_insert }
end

end algebraic_geometry
