/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.nilpotent
import algebra.lie.normalizer

/-!
# Engel's theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains a proof of Engel's theorem providing necessary and sufficient conditions for Lie
algebras and Lie modules to be nilpotent.

The key result `lie_module.is_nilpotent_iff_forall` says that if `M` is a Lie module of a
Noetherian Lie algebra `L`, then `M` is nilpotent iff the image of `L → End(M)` consists of
nilpotent elements. In the special case that we have the adjoint representation `M = L`, this says
that a Lie algebra is nilpotent iff `ad x : End(L)` is nilpotent for all `x : L`.

Engel's theorem is true for any coefficients (i.e., it is really a theorem about Lie rings) and so
we work with coefficients in any commutative ring `R` throughout.

On the other hand, Engel's theorem is not true for infinite-dimensional Lie algebras and so a
finite-dimensionality assumption is required. We prove the theorem subject to the the assumption
that the Lie algebra is Noetherian as an `R`-module, though actually we only need the slightly
weaker property that the relation `>` is well-founded on the complete lattice of Lie subalgebras.

## Remarks about the proof

Engel's theorem is usually proved in the special case that the coefficients are a field, and uses
an inductive argument on the dimension of the Lie algebra. One begins by choosing either a maximal
proper Lie subalgebra (in some proofs) or a maximal nilpotent Lie subalgebra (in other proofs, at
the cost of obtaining a weaker end result).

Since we work with general coefficients, we cannot induct on dimension and an alternate approach
must be taken. The key ingredient is the concept of nilpotency, not just for Lie algebras, but for
Lie modules. Using this concept, we define an _Engelian Lie algebra_ `lie_algebra.is_engelian` to
be one for which a Lie module is nilpotent whenever the action consists of nilpotent endomorphisms.
The argument then proceeds by selecting a maximal Engelian Lie subalgebra and showing that it cannot
be proper.

The first part of the traditional statement of Engel's theorem consists of the statement that if `M`
is a non-trivial `R`-module and `L ⊆ End(M)` is a finite-dimensional Lie subalgebra of nilpotent
elements, then there exists a non-zero element `m : M` that is annihilated by every element of `L`.
This follows trivially from the result established here `lie_module.is_nilpotent_iff_forall`, that
`M` is a nilpotent Lie module over `L`, since the last non-zero term in the lower central series
will consist of such elements `m` (see: `lie_module.nontrivial_max_triv_of_is_nilpotent`). It seems
that this result has not previously been established at this level of generality.

The second part of the traditional statement of Engel's theorem concerns nilpotency of the Lie
algebra and a proof of this for general coefficients appeared in the literature as long ago
[as 1937](zorn1937). This also follows trivially from `lie_module.is_nilpotent_iff_forall` simply by
taking `M = L`.

It is pleasing that the two parts of the traditional statements of Engel's theorem are thus unified
into a single statement about nilpotency of Lie modules. This is not usually emphasised.

## Main definitions

  * `lie_algebra.is_engelian`
  * `lie_algebra.is_engelian_of_is_noetherian`
  * `lie_module.is_nilpotent_iff_forall`
  * `lie_algebra.is_nilpotent_iff_forall`

-/

universes u₁ u₂ u₃ u₄

variables {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L₂] [lie_algebra R L₂]
variables [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]

include R L

namespace lie_submodule

open lie_module

variables {I : lie_ideal R L} {x : L} (hxI : (R ∙ x) ⊔ I = ⊤)

include hxI

lemma exists_smul_add_of_span_sup_eq_top (y : L) : ∃ (t : R) (z ∈ I), y = t • x + z :=
begin
  have hy : y ∈ (⊤ : submodule R L) := submodule.mem_top,
  simp only [← hxI, submodule.mem_sup, submodule.mem_span_singleton] at hy,
  obtain ⟨-, ⟨t, rfl⟩, z, hz, rfl⟩ := hy,
  exact ⟨t, z, hz, rfl⟩,
end

lemma lie_top_eq_of_span_sup_eq_top (N : lie_submodule R L M) :
  (↑⁅(⊤ : lie_ideal R L), N⁆ : submodule R M) =
  (N : submodule R M).map (to_endomorphism R L M x) ⊔ (↑⁅I, N⁆ : submodule R M) :=
begin
  simp only [lie_ideal_oper_eq_linear_span', submodule.sup_span, mem_top, exists_prop,
    exists_true_left, submodule.map_coe, to_endomorphism_apply_apply],
  refine le_antisymm (submodule.span_le.mpr _) (submodule.span_mono (λ z hz, _)),
  { rintros z ⟨y, n, hn : n ∈ N, rfl⟩,
    obtain ⟨t, z, hz, rfl⟩ := exists_smul_add_of_span_sup_eq_top hxI y,
    simp only [set_like.mem_coe, submodule.span_union, submodule.mem_sup],
    exact ⟨t • ⁅x, n⁆, submodule.subset_span ⟨t • n, N.smul_mem' t hn, lie_smul t x n⟩,
      ⁅z, n⁆, submodule.subset_span ⟨z, hz, n, hn, rfl⟩, by simp⟩, },
  { rcases hz with ⟨m, hm, rfl⟩ | ⟨y, hy, m, hm, rfl⟩,
    exacts [⟨x, m, hm, rfl⟩, ⟨y, m, hm, rfl⟩], },
end

lemma lcs_le_lcs_of_is_nilpotent_span_sup_eq_top {n i j : ℕ} (hxn : (to_endomorphism R L M x)^n = 0)
  (hIM : lower_central_series R L M i ≤ I.lcs M j) :
  lower_central_series R L M (i + n) ≤ I.lcs M (j + 1) :=
begin
  suffices : ∀ l, ((⊤ : lie_ideal R L).lcs M (i + l) : submodule R M) ≤
    (I.lcs M j : submodule R M).map
    ((to_endomorphism R L M x)^l) ⊔ (I.lcs M (j + 1) : submodule R M),
  { simpa only [bot_sup_eq, lie_ideal.incl_coe, submodule.map_zero, hxn] using this n, },
  intros l,
  induction l with l ih,
  { simp only [add_zero, lie_ideal.lcs_succ, pow_zero, linear_map.one_eq_id, submodule.map_id],
    exact le_sup_of_le_left hIM, },
  { simp only [lie_ideal.lcs_succ, i.add_succ l, lie_top_eq_of_span_sup_eq_top hxI, sup_le_iff],
    refine ⟨(submodule.map_mono ih).trans _, le_sup_of_le_right _⟩,
    { rw [submodule.map_sup, ← submodule.map_comp, ← linear_map.mul_eq_comp, ← pow_succ,
        ← I.lcs_succ],
      exact sup_le_sup_left coe_map_to_endomorphism_le _, },
    { refine le_trans (mono_lie_right _ _ I _) (mono_lie_right _ _ I hIM),
      exact antitone_lower_central_series R L M le_self_add, }, },
end

lemma is_nilpotent_of_is_nilpotent_span_sup_eq_top
  (hnp : is_nilpotent $ to_endomorphism R L M x) (hIM : is_nilpotent R I M) :
  is_nilpotent R L M :=
begin
  obtain ⟨n, hn⟩ := hnp,
  unfreezingI { obtain ⟨k, hk⟩ := hIM, },
  have hk' : I.lcs M k = ⊥,
  { simp only [← coe_to_submodule_eq_iff, I.coe_lcs_eq, hk, bot_coe_submodule], },
  suffices : ∀ l, lower_central_series R L M (l * n) ≤ I.lcs M l,
  { use k * n,
    simpa [hk'] using this k, },
  intros l,
  induction l with l ih,
  { simp, },
  { exact (l.succ_mul n).symm ▸ lcs_le_lcs_of_is_nilpotent_span_sup_eq_top hxI hn ih, },
end

end lie_submodule

section lie_algebra

open lie_module (hiding is_nilpotent)

variables (R L)

/-- A Lie algebra `L` is said to be Engelian if a sufficient condition for any `L`-Lie module `M` to
be nilpotent is that the image of the map `L → End(M)` consists of nilpotent elements.

Engel's theorem `lie_algebra.is_engelian_of_is_noetherian` states that any Noetherian Lie algebra is
Engelian. -/
def lie_algebra.is_engelian : Prop :=
  ∀ (M : Type u₄) [add_comm_group M], by exactI ∀ [module R M] [lie_ring_module L M], by exactI ∀
    [lie_module R L M], by exactI ∀ (h : ∀ (x : L), is_nilpotent (to_endomorphism R L M x)),
    lie_module.is_nilpotent R L M

variables {R L}

lemma lie_algebra.is_engelian_of_subsingleton [subsingleton L] : lie_algebra.is_engelian R L :=
begin
  intros M _i1 _i2 _i3 _i4 h,
  use 1,
  suffices : (⊤ : lie_ideal R L) = ⊥, { simp [this], },
  haveI := (lie_submodule.subsingleton_iff R L L).mpr infer_instance,
  apply subsingleton.elim,
end

lemma function.surjective.is_engelian
  {f : L →ₗ⁅R⁆ L₂} (hf : function.surjective f) (h : lie_algebra.is_engelian.{u₁ u₂ u₄} R L) :
  lie_algebra.is_engelian.{u₁ u₃ u₄} R L₂ :=
begin
  introsI M _i1 _i2 _i3 _i4 h',
  letI : lie_ring_module L M := lie_ring_module.comp_lie_hom M f,
  letI : lie_module R L M := comp_lie_hom M f,
  have hnp : ∀ x, is_nilpotent (to_endomorphism R L M x) := λ x, h' (f x),
  have surj_id : function.surjective (linear_map.id : M →ₗ[R] M) := function.surjective_id,
  haveI : lie_module.is_nilpotent R L M := h M hnp,
  apply hf.lie_module_is_nilpotent surj_id,
  simp,
end

lemma lie_equiv.is_engelian_iff (e : L ≃ₗ⁅R⁆ L₂) :
  lie_algebra.is_engelian.{u₁ u₂ u₄} R L ↔ lie_algebra.is_engelian.{u₁ u₃ u₄} R L₂ :=
⟨e.surjective.is_engelian, e.symm.surjective.is_engelian⟩

lemma lie_algebra.exists_engelian_lie_subalgebra_of_lt_normalizer
  {K : lie_subalgebra R L} (hK₁ : lie_algebra.is_engelian.{u₁ u₂ u₄} R K) (hK₂ : K < K.normalizer) :
  ∃ (K' : lie_subalgebra R L) (hK' : lie_algebra.is_engelian.{u₁ u₂ u₄} R K'), K < K' :=
begin
  obtain ⟨x, hx₁, hx₂⟩ := set_like.exists_of_lt hK₂,
  let K' : lie_subalgebra R L :=
  { lie_mem' := λ y z, lie_subalgebra.lie_mem_sup_of_mem_normalizer hx₁,
    .. (R ∙ x) ⊔ (K : submodule R L) },
  have hxK' : x ∈ K' := submodule.mem_sup_left (submodule.subset_span (set.mem_singleton _)),
  have hKK' : K ≤ K' := (lie_subalgebra.coe_submodule_le_coe_submodule K K').mp le_sup_right,
  have hK' : K' ≤ K.normalizer,
  { rw ← lie_subalgebra.coe_submodule_le_coe_submodule,
    exact sup_le ((submodule.span_singleton_le_iff_mem _ _).mpr hx₁) hK₂.le, },
  refine ⟨K', _, lt_iff_le_and_ne.mpr ⟨hKK', λ contra, hx₂ (contra.symm ▸ hxK')⟩⟩,
  introsI M _i1 _i2 _i3 _i4 h,
  obtain ⟨I, hI₁ : (I : lie_subalgebra R K') = lie_subalgebra.of_le hKK'⟩ :=
    lie_subalgebra.exists_nested_lie_ideal_of_le_normalizer hKK' hK',
  have hI₂ : (R ∙ (⟨x, hxK'⟩ : K')) ⊔ I = ⊤,
  { rw [← lie_ideal.coe_to_lie_subalgebra_to_submodule R K' I, hI₁],
    apply submodule.map_injective_of_injective (K' : submodule R L).injective_subtype,
    simpa, },
  have e : K ≃ₗ⁅R⁆ I := (lie_subalgebra.equiv_of_le hKK').trans
    (lie_equiv.of_eq _ _ ((lie_subalgebra.coe_set_eq _ _).mpr hI₁.symm)),
  have hI₃ : lie_algebra.is_engelian R I := e.is_engelian_iff.mp hK₁,
  exact lie_submodule.is_nilpotent_of_is_nilpotent_span_sup_eq_top hI₂ (h _) (hI₃ _ (λ x, h x)),
end

local attribute [instance] lie_subalgebra.subsingleton_bot

variables [is_noetherian R L]

/-- *Engel's theorem*.

Note that this implies all traditional forms of Engel's theorem via
`lie_module.nontrivial_max_triv_of_is_nilpotent`, `lie_module.is_nilpotent_iff_forall`,
`lie_algebra.is_nilpotent_iff_forall`. -/
lemma lie_algebra.is_engelian_of_is_noetherian : lie_algebra.is_engelian R L :=
begin
  introsI M _i1 _i2 _i3 _i4 h,
  rw ← is_nilpotent_range_to_endomorphism_iff,
  let L' := (to_endomorphism R L M).range,
  replace h : ∀ (y : L'), is_nilpotent (y : module.End R M),
  { rintros ⟨-, ⟨y, rfl⟩⟩,
    simp [h], },
  change lie_module.is_nilpotent R L' M,
  let s := { K : lie_subalgebra R L' | lie_algebra.is_engelian R K },
  have hs : s.nonempty := ⟨⊥, lie_algebra.is_engelian_of_subsingleton⟩,
  suffices : ⊤ ∈ s,
  { rw ← is_nilpotent_of_top_iff,
    apply this M,
    simp [lie_subalgebra.to_endomorphism_eq, h], },
  have : ∀ (K ∈ s), K ≠ ⊤ → ∃ (K' ∈ s), K < K',
  { rintros K (hK₁ : lie_algebra.is_engelian R K) hK₂,
    apply lie_algebra.exists_engelian_lie_subalgebra_of_lt_normalizer hK₁,
    apply lt_of_le_of_ne K.le_normalizer,
    rw [ne.def, eq_comm, K.normalizer_eq_self_iff, ← ne.def,
      ← lie_submodule.nontrivial_iff_ne_bot R K],
    haveI : nontrivial (L' ⧸ K.to_lie_submodule),
    { replace hK₂ : K.to_lie_submodule ≠ ⊤ :=
        by rwa [ne.def, ← lie_submodule.coe_to_submodule_eq_iff, K.coe_to_lie_submodule,
          lie_submodule.top_coe_submodule, ← lie_subalgebra.top_coe_submodule,
          K.coe_to_submodule_eq_iff],
      exact submodule.quotient.nontrivial_of_lt_top _ hK₂.lt_top, },
    haveI : lie_module.is_nilpotent R K (L' ⧸ K.to_lie_submodule),
    { refine hK₁ _ (λ x, _),
      have hx := lie_algebra.is_nilpotent_ad_of_is_nilpotent (h x),
      exact module.End.is_nilpotent.mapq _ hx, },
    exact nontrivial_max_triv_of_is_nilpotent R K (L' ⧸ K.to_lie_submodule), },
  haveI _i5 : is_noetherian R L' :=
    is_noetherian_of_surjective L _ (linear_map.range_range_restrict (to_endomorphism R L M)),
  obtain ⟨K, hK₁, hK₂⟩ := (lie_subalgebra.well_founded_of_noetherian R L').has_min s hs,
  have hK₃ : K = ⊤,
  { by_contra contra,
    obtain ⟨K', hK'₁, hK'₂⟩ := this K hK₁ contra,
    exact hK₂ K' hK'₁ hK'₂, },
  exact hK₃ ▸ hK₁,
end

/-- Engel's theorem. -/
lemma lie_module.is_nilpotent_iff_forall :
  lie_module.is_nilpotent R L M ↔ ∀ x, is_nilpotent $ to_endomorphism R L M x :=
⟨begin
  introsI h,
  obtain ⟨k, hk⟩ := nilpotent_endo_of_nilpotent_module R L M,
  exact λ x, ⟨k, hk x⟩,
end,
λ h, lie_algebra.is_engelian_of_is_noetherian M h⟩

/-- Engel's theorem. -/
lemma lie_algebra.is_nilpotent_iff_forall :
  lie_algebra.is_nilpotent R L ↔ ∀ x, is_nilpotent $ lie_algebra.ad R L x :=
lie_module.is_nilpotent_iff_forall

end lie_algebra
