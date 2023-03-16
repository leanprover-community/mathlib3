/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.solvable
import algebra.lie.quotient
import algebra.lie.normalizer
import linear_algebra.eigenspace
import ring_theory.nilpotent

/-!
# Nilpotent Lie algebras

Like groups, Lie algebras admit a natural concept of nilpotency. More generally, any Lie module
carries a natural concept of nilpotency. We define these here via the lower central series.

## Main definitions

  * `lie_module.lower_central_series`
  * `lie_module.is_nilpotent`

## Tags

lie algebra, lower central series, nilpotent
-/

universes u v w w₁ w₂

section nilpotent_modules

variables {R : Type u} {L : Type v} {M : Type w}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]
variables (k : ℕ) (N : lie_submodule R L M)

namespace lie_submodule

/-- A generalisation of the lower central series. The zeroth term is a specified Lie submodule of
a Lie module. In the case when we specify the top ideal `⊤` of the Lie algebra, regarded as a Lie
module over itself, we get the usual lower central series of a Lie algebra.

It can be more convenient to work with this generalisation when considering the lower central series
of a Lie submodule, regarded as a Lie module in its own right, since it provides a type-theoretic
expression of the fact that the terms of the Lie submodule's lower central series are also Lie
submodules of the enclosing Lie module.

See also `lie_module.lower_central_series_eq_lcs_comap` and
`lie_module.lower_central_series_map_eq_lcs` below, as well as `lie_submodule.ucs`. -/
def lcs : lie_submodule R L M → lie_submodule R L M := (λ N, ⁅(⊤ : lie_ideal R L), N⁆)^[k]

@[simp] lemma lcs_zero (N : lie_submodule R L M) : N.lcs 0 = N := rfl

@[simp] lemma lcs_succ : N.lcs (k + 1) = ⁅(⊤ : lie_ideal R L), N.lcs k⁆ :=
function.iterate_succ_apply' (λ N', ⁅⊤, N'⁆) k N

end lie_submodule

namespace lie_module

variables (R L M)

/-- The lower central series of Lie submodules of a Lie module. -/
def lower_central_series : lie_submodule R L M := (⊤ : lie_submodule R L M).lcs k

@[simp] lemma lower_central_series_zero : lower_central_series R L M 0 = ⊤ := rfl

@[simp] lemma lower_central_series_succ :
  lower_central_series R L M (k + 1) = ⁅(⊤ : lie_ideal R L), lower_central_series R L M k⁆ :=
(⊤ : lie_submodule R L M).lcs_succ k

end lie_module

namespace lie_submodule

open lie_module

variables {R L M}

lemma lcs_le_self : N.lcs k ≤ N :=
begin
  induction k with k ih,
  { simp, },
  { simp only [lcs_succ],
    exact (lie_submodule.mono_lie_right _ _ ⊤ ih).trans (N.lie_le_right ⊤), },
end

lemma lower_central_series_eq_lcs_comap :
  lower_central_series R L N k = (N.lcs k).comap N.incl :=
begin
  induction k with k ih,
  { simp, },
  { simp only [lcs_succ, lower_central_series_succ] at ⊢ ih,
    have : N.lcs k ≤ N.incl.range,
    { rw N.range_incl,
      apply lcs_le_self, },
    rw [ih, lie_submodule.comap_bracket_eq _ _ N.incl N.ker_incl this], },
end

lemma lower_central_series_map_eq_lcs :
  (lower_central_series R L N k).map N.incl = N.lcs k :=
begin
  rw [lower_central_series_eq_lcs_comap, lie_submodule.map_comap_incl, inf_eq_right],
  apply lcs_le_self,
end

end lie_submodule

namespace lie_module

variables (R L M)

lemma antitone_lower_central_series : antitone $ lower_central_series R L M :=
begin
  intros l k,
  induction k with k ih generalizing l;
  intros h,
  { exact (le_zero_iff.mp h).symm ▸ le_rfl, },
  { rcases nat.of_le_succ h with hk | hk,
    { rw lower_central_series_succ,
      exact (lie_submodule.mono_lie_right _ _ ⊤ (ih hk)).trans (lie_submodule.lie_le_right _ _), },
    { exact hk.symm ▸ le_rfl, }, },
end

lemma trivial_iff_lower_central_eq_bot : is_trivial L M ↔ lower_central_series R L M 1 = ⊥ :=
begin
  split; intros h,
  { erw [eq_bot_iff, lie_submodule.lie_span_le], rintros m ⟨x, n, hn⟩, rw [← hn, h.trivial], simp,},
  { rw lie_submodule.eq_bot_iff at h, apply is_trivial.mk, intros x m, apply h,
    apply lie_submodule.subset_lie_span, use [x, m], refl, },
end

lemma iterate_to_endomorphism_mem_lower_central_series (x : L) (m : M) (k : ℕ) :
  (to_endomorphism R L M x)^[k] m ∈ lower_central_series R L M k :=
begin
  induction k with k ih,
  { simp only [function.iterate_zero], },
  { simp only [lower_central_series_succ, function.comp_app, function.iterate_succ',
      to_endomorphism_apply_apply],
    exact lie_submodule.lie_mem_lie _ _ (lie_submodule.mem_top x) ih, },
end

variables {R L M}

lemma map_lower_central_series_le
  {M₂ : Type w₁} [add_comm_group M₂] [module R M₂] [lie_ring_module L M₂] [lie_module R L M₂]
  (k : ℕ) (f : M →ₗ⁅R,L⁆ M₂) :
  lie_submodule.map f (lower_central_series R L M k) ≤ lower_central_series R L M₂ k :=
begin
  induction k with k ih,
  { simp only [lie_module.lower_central_series_zero, le_top], },
  { simp only [lie_module.lower_central_series_succ, lie_submodule.map_bracket_eq],
    exact lie_submodule.mono_lie_right _ _ ⊤ ih, },
end

variables (R L M)
open lie_algebra

lemma derived_series_le_lower_central_series (k : ℕ) :
  derived_series R L k ≤ lower_central_series R L L k :=
begin
  induction k with k h,
  { rw [derived_series_def, derived_series_of_ideal_zero, lower_central_series_zero],
    exact le_rfl, },
  { have h' : derived_series R L k ≤ ⊤, { simp only [le_top], },
    rw [derived_series_def, derived_series_of_ideal_succ, lower_central_series_succ],
    exact lie_submodule.mono_lie _ _ _ _ h' h, },
end

/-- A Lie module is nilpotent if its lower central series reaches 0 (in a finite number of
steps). -/
class is_nilpotent : Prop :=
(nilpotent : ∃ k, lower_central_series R L M k = ⊥)

/-- See also `lie_module.is_nilpotent_iff_exists_ucs_eq_top`. -/
lemma is_nilpotent_iff :
  is_nilpotent R L M ↔ ∃ k, lower_central_series R L M k = ⊥ :=
⟨λ h, h.nilpotent, λ h, ⟨h⟩⟩

variables {R L M}

lemma _root_.lie_submodule.is_nilpotent_iff_exists_lcs_eq_bot (N : lie_submodule R L M) :
  lie_module.is_nilpotent R L N ↔ ∃ k, N.lcs k = ⊥ :=
begin
  rw is_nilpotent_iff,
  refine exists_congr (λ k, _),
  rw [N.lower_central_series_eq_lcs_comap k, lie_submodule.comap_incl_eq_bot,
    inf_eq_right.mpr (N.lcs_le_self k)],
end

variables (R L M)

@[priority 100]
instance trivial_is_nilpotent [is_trivial L M] : is_nilpotent R L M :=
⟨by { use 1, change ⁅⊤, ⊤⁆ = ⊥, simp, }⟩

lemma nilpotent_endo_of_nilpotent_module [hM : is_nilpotent R L M] :
  ∃ (k : ℕ), ∀ (x : L), (to_endomorphism R L M x)^k = 0 :=
begin
  unfreezingI { obtain ⟨k, hM⟩ := hM, },
  use k,
  intros x, ext m,
  rw [linear_map.pow_apply, linear_map.zero_apply, ← @lie_submodule.mem_bot R L M, ← hM],
  exact iterate_to_endomorphism_mem_lower_central_series R L M x m k,
end

/-- For a nilpotent Lie module, the weight space of the 0 weight is the whole module.

This result will be used downstream to show that weight spaces are Lie submodules, at which time
it will be possible to state it in the language of weight spaces. -/
lemma infi_max_gen_zero_eigenspace_eq_top_of_nilpotent [is_nilpotent R L M] :
  (⨅ (x : L), (to_endomorphism R L M x).maximal_generalized_eigenspace 0) = ⊤ :=
begin
  ext m,
  simp only [module.End.mem_maximal_generalized_eigenspace, submodule.mem_top, sub_zero, iff_true,
    zero_smul, submodule.mem_infi],
  intros x,
  obtain ⟨k, hk⟩ := nilpotent_endo_of_nilpotent_module R L M,
  use k, rw hk,
  exact linear_map.zero_apply m,
end

/-- If the quotient of a Lie module `M` by a Lie submodule on which the Lie algebra acts trivially
is nilpotent then `M` is nilpotent.

This is essentially the Lie module equivalent of the fact that a central
extension of nilpotent Lie algebras is nilpotent. See `lie_algebra.nilpotent_of_nilpotent_quotient`
below for the corresponding result for Lie algebras. -/
lemma nilpotent_of_nilpotent_quotient {N : lie_submodule R L M}
  (h₁ : N ≤ max_triv_submodule R L M) (h₂ : is_nilpotent R L (M ⧸ N)) : is_nilpotent R L M :=
begin
  unfreezingI { obtain ⟨k, hk⟩ := h₂, },
  use k+1,
  simp only [lower_central_series_succ],
  suffices : lower_central_series R L M k ≤ N,
  { replace this := lie_submodule.mono_lie_right _ _ ⊤ (le_trans this h₁),
    rwa [ideal_oper_max_triv_submodule_eq_bot, le_bot_iff] at this, },
  rw [← lie_submodule.quotient.map_mk'_eq_bot_le, ← le_bot_iff, ← hk],
  exact map_lower_central_series_le k (lie_submodule.quotient.mk' N),
end

/-- Given a nilpotent Lie module `M` with lower central series `M = C₀ ≥ C₁ ≥ ⋯ ≥ Cₖ = ⊥`, this is
the natural number `k` (the number of inclusions).

For a non-nilpotent module, we use the junk value 0. -/
noncomputable def nilpotency_length : ℕ :=
Inf { k | lower_central_series R L M k = ⊥ }

lemma nilpotency_length_eq_zero_iff [is_nilpotent R L M] :
  nilpotency_length R L M = 0 ↔ subsingleton M :=
begin
  let s := { k | lower_central_series R L M k = ⊥ },
  have hs : s.nonempty,
  { unfreezingI { obtain ⟨k, hk⟩ := (by apply_instance : is_nilpotent R L M), },
    exact ⟨k, hk⟩, },
  change Inf s = 0 ↔ _,
  rw [← lie_submodule.subsingleton_iff R L M, ← subsingleton_iff_bot_eq_top,
      ← lower_central_series_zero, @eq_comm (lie_submodule R L M)],
  refine ⟨λ h, h ▸ nat.Inf_mem hs, λ h, _⟩,
  rw nat.Inf_eq_zero,
  exact or.inl h,
end

lemma nilpotency_length_eq_succ_iff (k : ℕ) :
  nilpotency_length R L M = k + 1 ↔
  lower_central_series R L M (k + 1) = ⊥ ∧ lower_central_series R L M k ≠ ⊥ :=
begin
  let s := { k | lower_central_series R L M k = ⊥ },
  change Inf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s,
  have hs : ∀ k₁ k₂, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s,
  { rintros k₁ k₂ h₁₂ (h₁ : lower_central_series R L M k₁ = ⊥),
    exact eq_bot_iff.mpr (h₁ ▸ antitone_lower_central_series R L M h₁₂), },
  exact nat.Inf_upward_closed_eq_succ_iff hs k,
end

/-- Given a non-trivial nilpotent Lie module `M` with lower central series
`M = C₀ ≥ C₁ ≥ ⋯ ≥ Cₖ = ⊥`, this is the `k-1`th term in the lower central series (the last
non-trivial term).

For a trivial or non-nilpotent module, this is the bottom submodule, `⊥`. -/
noncomputable def lower_central_series_last : lie_submodule R L M :=
match nilpotency_length R L M with
| 0     := ⊥
| k + 1 := lower_central_series R L M k
end

lemma lower_central_series_last_le_max_triv :
  lower_central_series_last R L M ≤ max_triv_submodule R L M :=
begin
  rw lower_central_series_last,
  cases h : nilpotency_length R L M with k,
  { exact bot_le, },
  { rw le_max_triv_iff_bracket_eq_bot,
    rw [nilpotency_length_eq_succ_iff, lower_central_series_succ] at h,
    exact h.1, },
end

lemma nontrivial_lower_central_series_last [nontrivial M] [is_nilpotent R L M] :
  nontrivial (lower_central_series_last R L M) :=
begin
  rw [lie_submodule.nontrivial_iff_ne_bot, lower_central_series_last],
  cases h : nilpotency_length R L M,
  { rw [nilpotency_length_eq_zero_iff, ← not_nontrivial_iff_subsingleton] at h,
    contradiction, },
  { rw nilpotency_length_eq_succ_iff at h,
    exact h.2, },
end

lemma nontrivial_max_triv_of_is_nilpotent [nontrivial M] [is_nilpotent R L M] :
  nontrivial (max_triv_submodule R L M) :=
set.nontrivial_mono
  (lower_central_series_last_le_max_triv R L M)
  (nontrivial_lower_central_series_last R L M)

@[simp] lemma coe_lcs_range_to_endomorphism_eq (k : ℕ) :
  (lower_central_series R (to_endomorphism R L M).range M k : submodule R M) =
  lower_central_series R L M k :=
begin
  induction k with k ih,
  { simp, },
  { simp only [lower_central_series_succ, lie_submodule.lie_ideal_oper_eq_linear_span',
      ← (lower_central_series R (to_endomorphism R L M).range M k).mem_coe_submodule, ih],
    congr,
    ext m,
    split,
    { rintros ⟨⟨-, ⟨y, rfl⟩⟩, -, n, hn, rfl⟩,
      exact ⟨y, lie_submodule.mem_top _, n, hn, rfl⟩, },
    { rintros ⟨x, hx, n, hn, rfl⟩,
      exact ⟨⟨to_endomorphism R L M x, lie_hom.mem_range_self _ x⟩, lie_submodule.mem_top _,
        n, hn, rfl⟩, }, },
end

@[simp] lemma is_nilpotent_range_to_endomorphism_iff :
  is_nilpotent R (to_endomorphism R L M).range M ↔ is_nilpotent R L M :=
begin
  split;
  rintros ⟨k, hk⟩;
  use k;
  rw ← lie_submodule.coe_to_submodule_eq_iff at ⊢ hk;
  simpa using hk,
end

end lie_module

namespace lie_submodule

variables {N₁ N₂ : lie_submodule R L M}

/-- The upper (aka ascending) central series.

See also `lie_submodule.lcs`. -/
def ucs (k : ℕ) : lie_submodule R L M → lie_submodule R L M :=
normalizer^[k]

@[simp] lemma ucs_zero : N.ucs 0 = N := rfl

@[simp] lemma ucs_succ (k : ℕ) :
  N.ucs (k + 1) = (N.ucs k).normalizer :=
function.iterate_succ_apply' normalizer k N

lemma ucs_add (k l : ℕ) :
  N.ucs (k + l) = (N.ucs l).ucs k :=
function.iterate_add_apply normalizer k l N

@[mono] lemma ucs_mono (k : ℕ) (h : N₁ ≤ N₂) :
  N₁.ucs k ≤ N₂.ucs k :=
begin
  induction k with k ih, { simpa, },
  simp only [ucs_succ],
  mono,
end

lemma ucs_eq_self_of_normalizer_eq_self (h : N₁.normalizer = N₁) (k : ℕ) :
  N₁.ucs k = N₁ :=
by { induction k with k ih, { simp, }, { rwa [ucs_succ, ih], }, }

/-- If a Lie module `M` contains a self-normalizing Lie submodule `N`, then all terms of the upper
central series of `M` are contained in `N`.

An important instance of this situation arises from a Cartan subalgebra `H ⊆ L` with the roles of
`L`, `M`, `N` played by `H`, `L`, `H`, respectively. -/
lemma ucs_le_of_normalizer_eq_self (h : N₁.normalizer = N₁) (k : ℕ) :
  (⊥ : lie_submodule R L M).ucs k ≤ N₁ :=
by { rw ← ucs_eq_self_of_normalizer_eq_self h k, mono, simp, }

lemma lcs_add_le_iff (l k : ℕ) :
  N₁.lcs (l + k) ≤ N₂ ↔ N₁.lcs l ≤ N₂.ucs k :=
begin
  revert l,
  induction k with k ih, { simp, },
  intros l,
  rw [(by abel : l + (k + 1) = l + 1 + k), ih, ucs_succ, lcs_succ, top_lie_le_iff_le_normalizer],
end

lemma lcs_le_iff (k : ℕ) :
  N₁.lcs k ≤ N₂ ↔ N₁ ≤ N₂.ucs k :=
by { convert lcs_add_le_iff 0 k, rw zero_add, }

lemma gc_lcs_ucs (k : ℕ):
  galois_connection (λ (N : lie_submodule R L M), N.lcs k) (λ (N : lie_submodule R L M), N.ucs k) :=
λ N₁ N₂, lcs_le_iff k

lemma ucs_eq_top_iff (k : ℕ) : N.ucs k = ⊤ ↔ lie_module.lower_central_series R L M k ≤ N :=
by { rw [eq_top_iff, ← lcs_le_iff], refl, }

lemma _root_.lie_module.is_nilpotent_iff_exists_ucs_eq_top :
  lie_module.is_nilpotent R L M ↔ ∃ k, (⊥ : lie_submodule R L M).ucs k = ⊤ :=
by { rw lie_module.is_nilpotent_iff, exact exists_congr (λ k, by simp [ucs_eq_top_iff]), }

lemma ucs_comap_incl (k : ℕ) :
  ((⊥ : lie_submodule R L M).ucs k).comap N.incl = (⊥ : lie_submodule R L N).ucs k :=
by { induction k with k ih, { exact N.ker_incl, }, { simp [← ih], }, }

lemma is_nilpotent_iff_exists_self_le_ucs :
  lie_module.is_nilpotent R L N ↔ ∃ k, N ≤ (⊥ : lie_submodule R L M).ucs k :=
by simp_rw [lie_module.is_nilpotent_iff_exists_ucs_eq_top, ← ucs_comap_incl, comap_incl_eq_top]

end lie_submodule

section morphisms

open lie_module function

variables {L₂ M₂ : Type*} [lie_ring L₂] [lie_algebra R L₂]
variables [add_comm_group M₂] [module R M₂] [lie_ring_module L₂ M₂] [lie_module R L₂ M₂]
variables {f : L →ₗ⁅R⁆ L₂} {g : M →ₗ[R] M₂}
variables (hf : surjective f) (hg : surjective g) (hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆)

include hf hg hfg

lemma function.surjective.lie_module_lcs_map_eq (k : ℕ) :
  (lower_central_series R L M k : submodule R M).map g = lower_central_series R L₂ M₂ k :=
begin
  induction k with k ih,
  { simp [linear_map.range_eq_top, hg], },
  { suffices : g '' {m | ∃ (x : L) n, n ∈ lower_central_series R L M k ∧ ⁅x, n⁆ = m} =
               {m | ∃ (x : L₂) n, n ∈ lower_central_series R L M k ∧ ⁅x, g n⁆ = m},
    { simp only [← lie_submodule.mem_coe_submodule] at this,
      simp [← lie_submodule.mem_coe_submodule, ← ih, lie_submodule.lie_ideal_oper_eq_linear_span',
        submodule.map_span, -submodule.span_image, this], },
    ext m₂,
    split,
    { rintros ⟨m, ⟨x, n, hn, rfl⟩, rfl⟩,
      exact ⟨f x, n, hn, hfg x n⟩, },
    { rintros ⟨x, n, hn, rfl⟩,
      obtain ⟨y, rfl⟩ := hf x,
      exact ⟨⁅y, n⁆, ⟨y, n, hn, rfl⟩, (hfg y n).symm⟩, }, },
end

lemma function.surjective.lie_module_is_nilpotent [is_nilpotent R L M] : is_nilpotent R L₂ M₂ :=
begin
  obtain ⟨k, hk⟩ := id (by apply_instance : is_nilpotent R L M),
  use k,
  rw ← lie_submodule.coe_to_submodule_eq_iff at ⊢ hk,
  simp [← hf.lie_module_lcs_map_eq hg hfg k, hk],
end

omit hf hg hfg

lemma equiv.lie_module_is_nilpotent_iff (f : L ≃ₗ⁅R⁆ L₂) (g : M ≃ₗ[R] M₂)
  (hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆) :
  is_nilpotent R L M ↔ is_nilpotent R L₂ M₂ :=
begin
  split;
  introsI h,
  { have hg : surjective (g : M →ₗ[R] M₂) := g.surjective,
    exact f.surjective.lie_module_is_nilpotent hg hfg, },
  { have hg : surjective (g.symm : M₂ →ₗ[R] M) := g.symm.surjective,
    refine f.symm.surjective.lie_module_is_nilpotent hg (λ x m, _),
    rw [linear_equiv.coe_coe, lie_equiv.coe_to_lie_hom, ← g.symm_apply_apply ⁅f.symm x, g.symm m⁆,
      ← hfg, f.apply_symm_apply, g.apply_symm_apply], },
end

@[simp] lemma lie_module.is_nilpotent_of_top_iff :
  is_nilpotent R (⊤ : lie_subalgebra R L) M ↔ is_nilpotent R L M :=
equiv.lie_module_is_nilpotent_iff lie_subalgebra.top_equiv (1 : M ≃ₗ[R] M) (λ x m, rfl)

end morphisms

end nilpotent_modules

@[priority 100]
instance lie_algebra.is_solvable_of_is_nilpotent (R : Type u) (L : Type v)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [hL : lie_module.is_nilpotent R L L] :
  lie_algebra.is_solvable R L :=
begin
  obtain ⟨k, h⟩ : ∃ k, lie_module.lower_central_series R L L k = ⊥ := hL.nilpotent,
  use k, rw ← le_bot_iff at h ⊢,
  exact le_trans (lie_module.derived_series_le_lower_central_series R L k) h,
end

section nilpotent_algebras

variables (R : Type u) (L : Type v) (L' : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']

/-- We say a Lie algebra is nilpotent when it is nilpotent as a Lie module over itself via the
adjoint representation. -/
abbreviation lie_algebra.is_nilpotent (R : Type u) (L : Type v)
  [comm_ring R] [lie_ring L] [lie_algebra R L] : Prop :=
lie_module.is_nilpotent R L L

open lie_algebra

lemma lie_algebra.nilpotent_ad_of_nilpotent_algebra [is_nilpotent R L] :
  ∃ (k : ℕ), ∀ (x : L), (ad R L x)^k = 0 :=
lie_module.nilpotent_endo_of_nilpotent_module R L L

/-- See also `lie_algebra.zero_root_space_eq_top_of_nilpotent`. -/
lemma lie_algebra.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent [is_nilpotent R L] :
  (⨅ (x : L), (ad R L x).maximal_generalized_eigenspace 0) = ⊤ :=
lie_module.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent R L L

-- TODO Generalise the below to Lie modules if / when we define morphisms, equivs of Lie modules
-- covering a Lie algebra morphism of (possibly different) Lie algebras.

variables {R L L'}

open lie_module (lower_central_series)

/-- Given an ideal `I` of a Lie algebra `L`, the lower central series of `L ⧸ I` is the same
whether we regard `L ⧸ I` as an `L` module or an `L ⧸ I` module.

TODO: This result obviously generalises but the generalisation requires the missing definition of
morphisms between Lie modules over different Lie algebras. -/
lemma coe_lower_central_series_ideal_quot_eq {I : lie_ideal R L} (k : ℕ) :
  (lower_central_series R L (L ⧸ I) k : submodule R (L ⧸ I)) =
  lower_central_series R (L ⧸ I) (L ⧸ I) k :=
begin
  induction k with k ih,
  { simp only [lie_submodule.top_coe_submodule, lie_module.lower_central_series_zero], },
  { simp only [lie_module.lower_central_series_succ, lie_submodule.lie_ideal_oper_eq_linear_span],
    congr,
    ext x,
    split,
    { rintros ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩,
      erw [← lie_submodule.mem_coe_submodule, ih, lie_submodule.mem_coe_submodule] at hz,
      exact ⟨⟨lie_submodule.quotient.mk y, lie_submodule.mem_top _⟩, ⟨z, hz⟩, rfl⟩, },
    { rintros ⟨⟨⟨y⟩, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩,
      erw [← lie_submodule.mem_coe_submodule, ← ih, lie_submodule.mem_coe_submodule] at hz,
      exact ⟨⟨y, lie_submodule.mem_top _⟩, ⟨z, hz⟩, rfl⟩, }, },
end

/-- Note that the below inequality can be strict. For example the ideal of strictly-upper-triangular
2x2 matrices inside the Lie algebra of upper-triangular 2x2 matrices with `k = 1`. -/
lemma lie_module.coe_lower_central_series_ideal_le {I : lie_ideal R L} (k : ℕ) :
  (lower_central_series R I I k : submodule R I) ≤ lower_central_series R L I k :=
begin
  induction k with k ih,
  { simp, },
  { simp only [lie_module.lower_central_series_succ, lie_submodule.lie_ideal_oper_eq_linear_span],
    apply submodule.span_mono,
    rintros x ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩,
    exact ⟨⟨y.val, lie_submodule.mem_top _⟩, ⟨z, ih hz⟩, rfl⟩, },
end

/-- A central extension of nilpotent Lie algebras is nilpotent. -/
lemma lie_algebra.nilpotent_of_nilpotent_quotient {I : lie_ideal R L}
  (h₁ : I ≤ center R L) (h₂ : is_nilpotent R (L ⧸ I)) : is_nilpotent R L :=
begin
  suffices : lie_module.is_nilpotent R L (L ⧸ I),
  { exact lie_module.nilpotent_of_nilpotent_quotient R L L h₁ this, },
  unfreezingI { obtain ⟨k, hk⟩ := h₂, },
  use k,
  simp [← lie_submodule.coe_to_submodule_eq_iff, coe_lower_central_series_ideal_quot_eq, hk],
end

lemma lie_algebra.non_trivial_center_of_is_nilpotent [nontrivial L] [is_nilpotent R L] :
  nontrivial $ center R L :=
lie_module.nontrivial_max_triv_of_is_nilpotent R L L

lemma lie_ideal.map_lower_central_series_le (k : ℕ) {f : L →ₗ⁅R⁆ L'} :
  lie_ideal.map f (lower_central_series R L L k) ≤ lower_central_series R L' L' k :=
begin
  induction k with k ih,
  { simp only [lie_module.lower_central_series_zero, le_top], },
  { simp only [lie_module.lower_central_series_succ],
    exact le_trans (lie_ideal.map_bracket_le f) (lie_submodule.mono_lie _ _ _ _ le_top ih), },
end

lemma lie_ideal.lower_central_series_map_eq (k : ℕ) {f : L →ₗ⁅R⁆ L'}
  (h : function.surjective f) :
  lie_ideal.map f (lower_central_series R L L k) = lower_central_series R L' L' k :=
begin
  have h' : (⊤ : lie_ideal R L).map f = ⊤,
  { rw ←f.ideal_range_eq_map,
    exact f.ideal_range_eq_top_of_surjective h, },
  induction k with k ih,
  { simp only [lie_module.lower_central_series_zero], exact h', },
  { simp only [lie_module.lower_central_series_succ, lie_ideal.map_bracket_eq f h, ih, h'], },
end

lemma function.injective.lie_algebra_is_nilpotent [h₁ : is_nilpotent R L'] {f : L →ₗ⁅R⁆ L'}
  (h₂ : function.injective f) : is_nilpotent R L :=
{ nilpotent :=
  begin
    obtain ⟨k, hk⟩ := id h₁,
    use k,
    apply lie_ideal.bot_of_map_eq_bot h₂, rw [eq_bot_iff, ← hk],
    apply lie_ideal.map_lower_central_series_le,
  end, }

lemma function.surjective.lie_algebra_is_nilpotent [h₁ : is_nilpotent R L] {f : L →ₗ⁅R⁆ L'}
  (h₂ : function.surjective f) : is_nilpotent R L' :=
{ nilpotent :=
  begin
    obtain ⟨k, hk⟩ := id h₁,
    use k,
    rw [← lie_ideal.lower_central_series_map_eq k h₂, hk],
    simp only [lie_ideal.map_eq_bot_iff, bot_le],
  end, }

lemma lie_equiv.nilpotent_iff_equiv_nilpotent (e : L ≃ₗ⁅R⁆ L') :
  is_nilpotent R L ↔ is_nilpotent R L' :=
begin
  split; introsI h,
  { exact e.symm.injective.lie_algebra_is_nilpotent, },
  { exact e.injective.lie_algebra_is_nilpotent, },
end

lemma lie_hom.is_nilpotent_range [is_nilpotent R L] (f : L →ₗ⁅R⁆ L') :
  is_nilpotent R f.range :=
f.surjective_range_restrict.lie_algebra_is_nilpotent

/-- Note that this result is not quite a special case of
`lie_module.is_nilpotent_range_to_endomorphism_iff` which concerns nilpotency of the
`(ad R L).range`-module `L`, whereas this result concerns nilpotency of the `(ad R L).range`-module
`(ad R L).range`. -/
@[simp] lemma lie_algebra.is_nilpotent_range_ad_iff :
  is_nilpotent R (ad R L).range ↔ is_nilpotent R L :=
begin
  refine ⟨λ h, _, _⟩,
  { have : (ad R L).ker = center R L, { simp, },
    exact lie_algebra.nilpotent_of_nilpotent_quotient (le_of_eq this)
      ((ad R L).quot_ker_equiv_range.nilpotent_iff_equiv_nilpotent.mpr h), },
  { introsI h,
    exact (ad R L).is_nilpotent_range, },
end

instance [h : lie_algebra.is_nilpotent R L] : lie_algebra.is_nilpotent R (⊤ : lie_subalgebra R L) :=
lie_subalgebra.top_equiv.nilpotent_iff_equiv_nilpotent.mpr h

end nilpotent_algebras

namespace lie_ideal

open lie_module

variables {R L : Type*} [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L)
variables (M : Type*) [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]
variables (k : ℕ)

/-- Given a Lie module `M` over a Lie algebra `L` together with an ideal `I` of `L`, this is the
lower central series of `M` as an `I`-module. The advantage of using this definition instead of
`lie_module.lower_central_series R I M` is that its terms are Lie submodules of `M` as an
`L`-module, rather than just as an `I`-module.

See also `lie_ideal.coe_lcs_eq`. -/
def lcs : lie_submodule R L M := (λ N, ⁅I, N⁆)^[k] ⊤

@[simp] lemma lcs_zero : I.lcs M 0 = ⊤ := rfl

@[simp] lemma lcs_succ : I.lcs M (k + 1) = ⁅I, I.lcs M k⁆ :=
function.iterate_succ_apply' (λ N, ⁅I, N⁆) k ⊤

lemma lcs_top : (⊤ : lie_ideal R L).lcs M k = lower_central_series R L M k := rfl

lemma coe_lcs_eq : (I.lcs M k : submodule R M) = lower_central_series R I M k :=
begin
  induction k with k ih,
  { simp, },
  { simp_rw [lower_central_series_succ, lcs_succ, lie_submodule.lie_ideal_oper_eq_linear_span',
      ← (I.lcs M k).mem_coe_submodule, ih, lie_submodule.mem_coe_submodule,
      lie_submodule.mem_top, exists_true_left, (I : lie_subalgebra R L).coe_bracket_of_module],
    congr,
    ext m,
    split,
    { rintros ⟨x, hx, m, hm, rfl⟩,
      exact ⟨⟨x, hx⟩, m, hm, rfl⟩, },
    { rintros ⟨⟨x, hx⟩, m, hm, rfl⟩,
      exact ⟨x, hx, m, hm, rfl⟩, }, },
end

end lie_ideal

section of_associative

variables (R : Type u) {A : Type v} [comm_ring R] [ring A] [algebra R A]

lemma lie_algebra.ad_nilpotent_of_nilpotent {a : A} (h : is_nilpotent a) :
  is_nilpotent (lie_algebra.ad R A a) :=
begin
  rw lie_algebra.ad_eq_lmul_left_sub_lmul_right,
  have hl : is_nilpotent (linear_map.mul_left R a),
  { rwa linear_map.is_nilpotent_mul_left_iff, },
  have hr : is_nilpotent (linear_map.mul_right R a),
  { rwa linear_map.is_nilpotent_mul_right_iff, },
  have := @linear_map.commute_mul_left_right R A _ _ _ _ _ a a,
  exact this.is_nilpotent_sub hl hr,
end

variables {R}

lemma lie_subalgebra.is_nilpotent_ad_of_is_nilpotent_ad {L : Type v} [lie_ring L] [lie_algebra R L]
  (K : lie_subalgebra R L) {x : K} (h : is_nilpotent (lie_algebra.ad R L ↑x)) :
  is_nilpotent (lie_algebra.ad R K x) :=
begin
  obtain ⟨n, hn⟩ := h,
  use n,
  exact linear_map.submodule_pow_eq_zero_of_pow_eq_zero (K.ad_comp_incl_eq x) hn,
end

lemma lie_algebra.is_nilpotent_ad_of_is_nilpotent {L : lie_subalgebra R A} {x : L}
  (h : is_nilpotent (x : A)) : is_nilpotent (lie_algebra.ad R L x) :=
L.is_nilpotent_ad_of_is_nilpotent_ad $ lie_algebra.ad_nilpotent_of_nilpotent R h

end of_associative
