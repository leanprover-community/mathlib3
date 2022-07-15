/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import ring_theory.noetherian
import ring_theory.rees_algebra
import ring_theory.finiteness

/-!

# `I`-filtrations of modules

This file contains the definitions and basic results around (stable) `I`-filtrations of modules.

-/


universes u v

variables {R M : Type u} [comm_ring R] [add_comm_group M] [module R M] (I : ideal R)

open polynomial
open_locale polynomial big_operators

/-- An `I`-filtration on the module `M` is a sequence of decreasing submodules `N i` such that
`I • N ≤ I (i + 1)`. Note that we do not require the filtration to start from `⊤`. -/
@[ext]
structure ideal.filtration (M : Type u) [add_comm_group M] [module R M] :=
(N : ℕ → submodule R M)
(mono : ∀ i, N (i + 1) ≤ N i)
(smul_le : ∀ i, I • N i ≤ N (i + 1))

variables (F F' : I.filtration M) {I}

namespace ideal.filtration

lemma pow_smul_le (i j : ℕ) : I ^ i • F.N j ≤ F.N (i + j) :=
begin
  induction i,
  { simp },
  { rw [pow_succ, mul_smul, nat.succ_eq_add_one, add_assoc, add_comm 1, ← add_assoc],
    exact (submodule.smul_mono_right i_ih).trans (F.smul_le _) }
end

lemma pow_smul_le_pow_smul (i j k : ℕ) : I ^ (i + k) • F.N j ≤ I ^ k • F.N (i + j) :=
by { rw [add_comm, pow_add, mul_smul], exact submodule.smul_mono_right (F.pow_smul_le i j) }

protected
lemma antitone : antitone F.N :=
antitone_nat_of_succ_le F.mono

/-- The trivial `I`-filtration of `N`. -/
@[simps]
def _root_.ideal.trivial_filtration (I : ideal R) (N : submodule R M) : I.filtration M :=
{ N := λ i, N,
  mono := λ i, le_of_eq rfl,
  smul_le := λ i, submodule.smul_le_right }

/-- The `sup` of two `I.filtration`s is an `I.filtration`. -/
instance : has_sup (I.filtration M) :=
⟨λ F F', ⟨F.N ⊔ F'.N, λ i, sup_le_sup (F.mono i) (F'.mono i),
    λ i, (le_of_eq (submodule.smul_sup _ _ _)).trans $ sup_le_sup (F.smul_le i) (F'.smul_le i)⟩⟩

/-- The `Sup` of a family of `I.filtration`s is an `I.filtration`. -/
instance : has_Sup (I.filtration M) := ⟨λ S,
{ N := Sup (ideal.filtration.N '' S),
  mono := λ i, begin
    apply Sup_le_Sup_of_forall_exists_le _,
    rintros _ ⟨⟨_, F, hF, rfl⟩, rfl⟩,
    exact ⟨_, ⟨⟨_, F, hF, rfl⟩, rfl⟩, F.mono i⟩,
  end,
  smul_le := λ i, begin
    rw [Sup_eq_supr', supr_apply, submodule.smul_supr, supr_apply],
    apply supr_mono _,
    rintro ⟨_, F, hF, rfl⟩,
    exact F.smul_le i,
  end }⟩

/-- The `inf` of two `I.filtration`s is an `I.filtration`. -/
instance : has_inf (I.filtration M) :=
⟨λ F F', ⟨F.N ⊓ F'.N, λ i, inf_le_inf (F.mono i) (F'.mono i),
    λ i, (submodule.smul_inf_le _ _ _).trans $ inf_le_inf (F.smul_le i) (F'.smul_le i)⟩⟩

/-- The `Inf` of a family of `I.filtration`s is an `I.filtration`. -/
instance : has_Inf (I.filtration M) := ⟨λ S,
{ N := Inf (ideal.filtration.N '' S),
  mono := λ i, begin
    apply Inf_le_Inf_of_forall_exists_le _,
    rintros _ ⟨⟨_, F, hF, rfl⟩, rfl⟩,
    exact ⟨_, ⟨⟨_, F, hF, rfl⟩, rfl⟩, F.mono i⟩,
  end,
  smul_le := λ i, begin
    rw [Inf_eq_infi', infi_apply, infi_apply],
    refine submodule.smul_infi_le.trans _,
    apply infi_mono _,
    rintro ⟨_, F, hF, rfl⟩,
    exact F.smul_le i,
  end }⟩

instance : has_top (I.filtration M) := ⟨I.trivial_filtration ⊤⟩
instance : has_bot (I.filtration M) := ⟨I.trivial_filtration ⊥⟩

@[simp] lemma sup_N : (F ⊔ F').N = F.N ⊔ F'.N := rfl
@[simp] lemma Sup_N (S : set (I.filtration M)) : (Sup S).N = Sup (ideal.filtration.N '' S) := rfl
@[simp] lemma inf_N : (F ⊓ F').N = F.N ⊓ F'.N := rfl
@[simp] lemma Inf_N (S : set (I.filtration M)) : (Inf S).N = Inf (ideal.filtration.N '' S) := rfl
@[simp] lemma top_N : (⊤ : I.filtration M).N = ⊤ := rfl
@[simp] lemma bot_N : (⊥ : I.filtration M).N = ⊥ := rfl

@[simp] lemma supr_N {ι : Sort*} (f : ι → I.filtration M) : (supr f).N = ⨆ i, (f i).N :=
congr_arg Sup (set.range_comp _ _).symm

@[simp] lemma infi_N {ι : Sort*} (f : ι → I.filtration M) : (infi f).N = ⨅ i, (f i).N :=
congr_arg Inf (set.range_comp _ _).symm

instance : complete_lattice (I.filtration M) :=
function.injective.complete_lattice ideal.filtration.N ideal.filtration.ext
  sup_N inf_N (λ _, Sup_image) (λ _, Inf_image) top_N bot_N

instance : inhabited (I.filtration M) := ⟨⊥⟩

/-- An `I` filtration is stable if `I • F.N n = F.N (n+1)` for large enough `n`. -/
def stable : Prop :=
∃ n₀, ∀ n ≥ n₀, I • F.N n = F.N (n + 1)

/-- The trivial stable `I`-filtration of `N`. -/
@[simps]
def _root_.ideal.stable_filtration (I : ideal R) (N : submodule R M) :
  I.filtration M :=
{ N := λ i, I ^ i • N,
  mono := λ i, by { rw [add_comm, pow_add, mul_smul], exact submodule.smul_le_right },
  smul_le := λ i, by { rw [add_comm, pow_add, mul_smul, pow_one], exact le_refl _ } }

lemma _root_.ideal.stable_filtration_stable (I : ideal R) (N : submodule R M) :
  (I.stable_filtration N).stable :=
by { use 0, intros n _, dsimp, rw [add_comm, pow_add, mul_smul, pow_one] }

variables {F F'} (h : F.stable)

include h

lemma stable.exists_pow_smul_eq :
  ∃ n₀, ∀ k, F.N (n₀ + k) = I ^ k • F.N n₀ :=
begin
  obtain ⟨n₀, hn⟩ := h,
  use n₀,
  intro k,
  induction k,
  { simp },
  { rw [nat.succ_eq_add_one, ← add_assoc, ← hn, k_ih, add_comm, pow_add, mul_smul, pow_one],
    linarith }
end

lemma stable.exists_pow_smul_eq_of_ge :
  ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀ :=
begin
  obtain ⟨n₀, hn₀⟩ := h.exists_pow_smul_eq,
  use n₀,
  intros n hn,
  convert hn₀ (n - n₀),
  rw [add_comm, tsub_add_cancel_of_le hn],
end

omit h

lemma stable_iff_exists_pow_smul_eq_of_ge :
  F.stable ↔ ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀ :=
begin
  refine ⟨stable.exists_pow_smul_eq_of_ge, λ h, ⟨h.some, λ n hn, _⟩⟩,
  rw [h.some_spec n hn, h.some_spec (n+1) (by linarith), smul_smul, ← pow_succ,
    tsub_add_eq_add_tsub hn],
end

lemma stable.exists_forall_le (h : F.stable) (e : F.N 0 ≤ F'.N 0) :
  ∃ n₀, ∀ n, F.N (n + n₀) ≤ F'.N n :=
begin
  obtain ⟨n₀, hF⟩ := h,
  use n₀,
  intro n,
  induction n with n hn,
  { refine (F.antitone _).trans e, simp },
  { rw [nat.succ_eq_one_add, add_assoc, add_comm, add_comm 1 n, ← hF],
    exact (submodule.smul_mono_right hn).trans (F'.smul_le _),
    simp },
end

lemma stable.bounded_difference (h : F.stable) (h' : F'.stable) (e : F.N 0 = F'.N 0) :
  ∃ n₀, ∀ n, F.N (n + n₀) ≤ F'.N n ∧ F'.N (n + n₀) ≤ F.N n :=
begin
  obtain ⟨n₁, h₁⟩ := h.exists_forall_le (le_of_eq e),
  obtain ⟨n₂, h₂⟩ := h'.exists_forall_le (le_of_eq e.symm),
  use max n₁ n₂,
  intro n,
  refine ⟨(F.antitone _).trans (h₁ n), (F'.antitone _).trans (h₂ n)⟩; simp
end

end ideal.filtration
