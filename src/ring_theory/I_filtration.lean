/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import algebra.direct_sum.ring
import algebra.direct_sum.module
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
structure I_filtration (M : Type u) [add_comm_group M] [module R M] :=
(N : ℕ → submodule R M)
(mono : ∀ i, N (i + 1) ≤ N i)
(smul_le : ∀ i, I • N i ≤ N (i + 1))

variables (F : I_filtration I M) {I}

lemma I_filtration.pow_smul_le (i j : ℕ) : I ^ i • F.N j ≤ F.N (i + j) :=
begin
  induction i,
  { simp },
  { rw [pow_succ, mul_smul, nat.succ_eq_add_one, add_assoc, add_comm 1, ← add_assoc],
    exact (submodule.smul_mono_right i_ih).trans (F.smul_le _) }
end

lemma I_filtration.pow_smul_le_pow_smul (i j k : ℕ) : I ^ (i + k) • F.N j ≤ I ^ k • F.N (i + j) :=
by { rw [add_comm, pow_add, mul_smul], exact submodule.smul_mono_right (F.pow_smul_le i j) }

lemma I_filtration.antitone (F : I_filtration I M) : antitone F.N :=
begin
  intros i j e,
  refine nat.le_induction _ _ _ e,
  { exact le_refl _ },
  { intros n _ e', exact (F.mono _).trans e' }
end

/-- The trivial `I`-filtration of `N`. -/
def trivial_I_filtration (I : ideal R) (N : submodule R M) :
  I_filtration I M :=
{ N := λ i, N,
  mono := λ i, le_of_eq rfl,
  smul_le := λ i, submodule.smul_le_right }

/-- The `Sup` of a family of `I_filtration`s is an `I_filtration`. -/
@[simps]
def I_filtration.Sup (S : set (I_filtration I M)) : I_filtration I M :=
{ N := Sup (I_filtration.N '' S),
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
  end }

/-- The `Inf` of a family of `I_filtration`s is an `I_filtration`. -/
@[simps]
def I_filtration.Inf (S : set (I_filtration I M)) : I_filtration I M :=
{ N := Inf (I_filtration.N '' S),
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
  end }

instance : partial_order (I_filtration I M) := partial_order.lift I_filtration.N I_filtration.ext

instance : complete_lattice (I_filtration I M) :=
{ sup := λ F F', ⟨F.N ⊔ F'.N, λ i, sup_le_sup (F.mono i) (F'.mono i),
    λ i, (le_of_eq (submodule.smul_sup _ _ _)).trans $ sup_le_sup (F.smul_le i) (F'.smul_le i)⟩,
  le_sup_left := λ a b i, le_sup_left,
  le_sup_right := λ a b i, le_sup_right,
  sup_le := λ a b c i j x, sup_le (i x) (j x),
  inf := λ F F', ⟨F.N ⊓ F'.N, λ i, inf_le_inf (F.mono i) (F'.mono i),
    λ i, (submodule.smul_inf_le _ _ _).trans $ inf_le_inf (F.smul_le i) (F'.smul_le i)⟩,
  inf_le_left := λ a b i, inf_le_left,
  inf_le_right := λ a b i, inf_le_right,
  le_inf := λ a b c i j x, le_inf (i x) (j x),
  Sup := I_filtration.Sup,
  le_Sup := λ s F hF i, le_Sup ⟨⟨_, F, hF, rfl⟩, rfl⟩,
  Sup_le := λ s F hF i, Sup_le (by { rintros _ ⟨⟨_, F', hF', rfl⟩, rfl⟩, exact hF F' hF' i }),
  Inf := I_filtration.Inf,
  Inf_le := λ s F hF i, Inf_le ⟨⟨_, F, hF, rfl⟩, rfl⟩,
  le_Inf := λ s F hF i, le_Inf (by { rintros _ ⟨⟨_, F', hF', rfl⟩, rfl⟩, exact hF F' hF' i }),
  top := trivial_I_filtration I ⊤,
  bot := trivial_I_filtration I ⊥,
  le_top := λ x i, le_top,
  bot_le := λ x i, bot_le,
  ..(show partial_order (I_filtration I M), by apply_instance) }

instance : inhabited (I_filtration I M) := ⟨⊥⟩

/-- An `I` filtration is stable if `I • F.N n = F.N (n+1)` for large enough `n`. -/
def I_filtration.stable : Prop :=
∃ n₀, ∀ n ≥ n₀, I • F.N n = F.N (n + 1)

/-- The trivial stable `I`-filtration of `N`. -/
@[simps]
def stable_I_filtration (I : ideal R) (N : submodule R M) :
  I_filtration I M :=
{ N := λ i, I ^ i • N,
  mono := λ i, by { rw [add_comm, pow_add, mul_smul], exact submodule.smul_le_right },
  smul_le := λ i, by { rw [add_comm, pow_add, mul_smul, pow_one], exact le_refl _ } }

lemma stable_I_filtration.stable (I : ideal R) (N : submodule R M) :
  (stable_I_filtration I N).stable :=
by { use 0, intros n _, dsimp, rw [add_comm, pow_add, mul_smul, pow_one] }

lemma I_filtration.stable.exists_pow_smul_eq {F : I_filtration I M} (h : F.stable) :
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

lemma I_filtration.stable.exists_pow_smul_eq_of_ge {F : I_filtration I M} (h : F.stable) :
  ∃ n₀, ∀ n ≥ n₀, F.N n = I ^ (n - n₀) • F.N n₀ :=
begin
  obtain ⟨n₀, hn₀⟩ := h.exists_pow_smul_eq,
  use n₀,
  intros n hn,
  convert hn₀ (n - n₀),
  rw [add_comm, tsub_add_cancel_of_le hn],
end

lemma I_filtration.stable.exists_forall_le {F F' : I_filtration I M}
  (h : F.stable) (e : F.N 0 = F'.N 0) :
  ∃ n₀, ∀ n, F.N (n + n₀) ≤ F'.N n :=
begin
  obtain ⟨n₀, hF⟩ := h,
  use n₀,
  intro n,
  induction n with n hn,
  { rw ← e, apply F.antitone, simp },
  { rw [nat.succ_eq_one_add, add_assoc, add_comm, add_comm 1 n, ← hF],
    exact (submodule.smul_mono_right hn).trans (F'.smul_le _),
    simp },
end

lemma I_filtration.stable.bounded_difference {F F' : I_filtration I M}
  (h : F.stable) (h' : F'.stable) (e : F.N 0 = F'.N 0) :
  ∃ n₀, ∀ n, F.N (n + n₀) ≤ F'.N n ∧ F'.N (n + n₀) ≤ F.N n :=
begin
  obtain ⟨n₁, h₁⟩ := h.exists_forall_le e,
  obtain ⟨n₂, h₂⟩ := h'.exists_forall_le e.symm,
  use max n₁ n₂,
  intro n,
  refine ⟨(F.antitone _).trans (h₁ n), (F'.antitone _).trans (h₂ n)⟩; simp
end
