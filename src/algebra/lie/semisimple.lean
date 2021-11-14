/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.solvable

/-!
# Semisimple Lie algebras

The famous Cartan-Dynkin-Killing classification of semisimple Lie algebras renders them one of the
most important classes of Lie algebras. In this file we define simple and semisimple Lie algebras
and prove some basic related results.

## Main definitions

  * `lie_module.is_irreducible`
  * `lie_algebra.is_simple`
  * `lie_algebra.is_semisimple`
  * `lie_algebra.is_semisimple_iff_no_solvable_ideals`
  * `lie_algebra.is_semisimple_iff_no_abelian_ideals`
  * `lie_algebra.abelian_radical_iff_solvable_is_abelian`

## Tags

lie algebra, radical, simple, semisimple
-/

universes u v w w₁ w₂

/-- A Lie module is irreducible if it is zero or its only non-trivial Lie submodule is itself. -/
class lie_module.is_irreducible (R : Type u) (L : Type v) (M : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
  [lie_ring_module L M] [lie_module R L M] : Prop :=
(irreducible : ∀ (N : lie_submodule R L M), N ≠ ⊥ → N = ⊤)

namespace lie_algebra

variables (R : Type u) (L : Type v)
variables [comm_ring R] [lie_ring L] [lie_algebra R L]

/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
class is_simple extends lie_module.is_irreducible R L L : Prop :=
(non_abelian : ¬is_lie_abelian L)

/-- A semisimple Lie algebra is one with trivial radical.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients. We are following [Seligman, page 15](seligman1967) and using the label
for the weakest of the various properties which are all equivalent over a field of characteristic
zero. -/
class is_semisimple : Prop :=
(semisimple : radical R L = ⊥)

lemma is_semisimple_iff_no_solvable_ideals :
  is_semisimple R L ↔ ∀ (I : lie_ideal R L), is_solvable R I → I = ⊥ :=
⟨λ h, Sup_eq_bot.mp h.semisimple, λ h, ⟨Sup_eq_bot.mpr h⟩⟩

lemma is_semisimple_iff_no_abelian_ideals :
  is_semisimple R L ↔ ∀ (I : lie_ideal R L), is_lie_abelian I → I = ⊥ :=
begin
  rw is_semisimple_iff_no_solvable_ideals,
  split; intros h₁ I h₂,
  { haveI : is_lie_abelian I := h₂, apply h₁, exact lie_algebra.of_abelian_is_solvable R I, },
  { haveI : is_solvable R I := h₂, rw ← abelian_of_solvable_ideal_eq_bot_iff, apply h₁,
    exact abelian_derived_abelian_of_ideal I, },
end

@[simp] lemma center_eq_bot_of_semisimple [h : is_semisimple R L] : center R L = ⊥ :=
by { rw is_semisimple_iff_no_abelian_ideals at h, apply h, apply_instance, }

/-- A simple Lie algebra is semisimple. -/
@[priority 100]
instance is_semisimple_of_is_simple [h : is_simple R L] : is_semisimple R L :=
begin
  rw is_semisimple_iff_no_abelian_ideals,
  intros I hI,
  tactic.unfreeze_local_instances, obtain ⟨⟨h₁⟩, h₂⟩ := h,
  by_contradiction contra,
  rw [h₁ I contra, lie_abelian_iff_equiv_lie_abelian lie_ideal.top_equiv_self] at hI,
  exact h₂ hI,
end

/-- A semisimple Abelian Lie algebra is trivial. -/
lemma subsingleton_of_semisimple_lie_abelian [is_semisimple R L] [h : is_lie_abelian L] :
  subsingleton L :=
begin
  rw [is_lie_abelian_iff_center_eq_top R L, center_eq_bot_of_semisimple] at h,
  exact (lie_submodule.subsingleton_iff R L L).mp (subsingleton_of_bot_eq_top h),
end

lemma abelian_radical_of_semisimple [is_semisimple R L] : is_lie_abelian (radical R L) :=
by { rw is_semisimple.semisimple, exact is_lie_abelian_bot R L, }

/-- The two properties shown to be equivalent here are possible definitions for a Lie algebra
to be reductive.

Note that there is absolutely [no agreement](https://mathoverflow.net/questions/284713/) on what
the label 'reductive' should mean when the coefficients are not a field of characteristic zero. -/
lemma abelian_radical_iff_solvable_is_abelian [is_noetherian R L] :
  is_lie_abelian (radical R L) ↔ ∀ (I : lie_ideal R L), is_solvable R I → is_lie_abelian I :=
begin
  split,
  { rintros h₁ I h₂,
    rw lie_ideal.solvable_iff_le_radical at h₂,
    exact (lie_ideal.hom_of_le_injective h₂).is_lie_abelian h₁, },
  { intros h, apply h, apply_instance, },
end

lemma ad_ker_eq_bot_of_semisimple [is_semisimple R L] : (ad R L).ker = ⊥ :=
by simp

end lie_algebra
