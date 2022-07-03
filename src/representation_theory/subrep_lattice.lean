/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.subrep

variables {k k' G V : Type*}

section add_comm_monoid

variables
  [comm_semiring k] [comm_semiring k'] [monoid G]
  [add_comm_monoid V] [module k V] [module k' V]
  [has_smul k' k] [is_scalar_tower k' k V]
  {ρ : representation k G V} {p q : subrep ρ}

namespace subrep

/-- The set `{0}` is the bottom element of the lattice of subreps. -/
instance : has_bot (subrep ρ) :=
⟨{ carrier := {0}, smulG_mem' := by simp { contextual := tt }, .. (⊥ : submodule k V)}⟩

instance inhabited' : inhabited (subrep ρ) := ⟨⊥⟩

@[simp] lemma bot_coe : ((⊥ : subrep ρ) : set V) = {0} := rfl
@[simp] lemma bot_to_submodule : (⊥ : subrep ρ).to_submodule = ⊥ := rfl

-- restrict_scalars_bot

@[simp] lemma mem_bot {x : V} : x ∈ (⊥ : subrep ρ) ↔ x = 0 := set.mem_singleton_iff

-- restrict_scalars_eq_bot_iff

instance unique_bot : unique (⊥ : subrep ρ) :=
⟨infer_instance, λ x, subtype.ext x.mem⟩

instance : order_bot (subrep ρ) :=
{ bot := ⊥,
  bot_le := λ p x, by simp [zero_mem] {contextual := tt} }

protected lemma eq_bot_iff (p : subrep ρ) : p = ⊥ ↔ ∀ x ∈ p, x = (0 : V) :=
⟨ λ h, h.symm ▸ λ x hx, hx,
  λ h, eq_bot_iff.mpr (λ x hx, h x hx) ⟩

@[ext] protected lemma bot_ext (x y : (⊥ : subrep ρ)) : x = y :=
begin
  rcases x with ⟨x, xm⟩, rcases y with ⟨y, ym⟩, congr,
  rw (subrep.eq_bot_iff _).mp rfl x xm,
  rw (subrep.eq_bot_iff _).mp rfl y ym
end

protected lemma ne_bot_iff (p : subrep ρ) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : V) :=
by { haveI := classical.prop_decidable, simp_rw [ne.def, p.eq_bot_iff, not_forall] }

lemma nonzero_mem_of_bot_lt {p : subrep ρ} (bot_lt : ⊥ < p) : ∃ a : p, a ≠ 0 :=
let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp bot_lt.ne' in ⟨⟨b, hb₁⟩, hb₂ ∘ (congr_arg coe)⟩

lemma exists_mem_ne_zero_of_ne_bot {p : subrep ρ} (h : p ≠ ⊥) : ∃ b : V, b ∈ p ∧ b ≠ 0 :=
let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp h in ⟨b, hb₁, hb₂⟩




end subrep



end add_comm_monoid
