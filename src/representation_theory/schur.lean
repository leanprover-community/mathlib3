/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.subrep_hom
import field_theory.is_alg_closed.basic
import linear_algebra.eigenspace

variables {k G V V₂ : Type*} [comm_ring k] [monoid G] [add_comm_group V] [module k V]
  [add_comm_group V₂] [module k V₂]

/-- A representation is irreducible if its only subreps are the singleton (zero representation)
or the whole representation (allowed to be zero also). -/
def is_irreducible (ρ : representation k G V) : Prop := ∀ (p : subrep ρ), p = ⊥ ∨ p = ⊤

lemma rep_equiv.is_irreducible {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (h : is_irreducible ρ) (e : ρ ≃ᵣ ρ₂) :
  is_irreducible ρ₂ :=
begin
  intro,
  have := h (subrep.comap (e : ρ →ᵣ ρ₂) p),
  cases this with hb ht,
  { apply or.intro_left,
    have := congr_arg (subrep.map (e : ρ →ᵣ ρ₂)) hb,
    have hp : p ≤ (e : ρ →ᵣ ρ₂).range, simp,
    rw [_root_.subrep.map_comap_eq_self hp, subrep.map_bot] at this,
    exact this },
  { apply or.intro_right,
    have := congr_arg (subrep.map (e : ρ →ᵣ ρ₂)) ht,
    have hp : p ≤ (e : ρ →ᵣ ρ₂).range, simp,
    rw [_root_.subrep.map_comap_eq_self hp, subrep.map_top, rep_hom.range_eq_top.mpr] at this,
    exact this,
    apply rep_equiv.surjective }
end

namespace representation

/-- A rep_hom from an irreducible representation to another representation is either 0 or
injective. -/
lemma schur_injective {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (f : ρ →ᵣ ρ₂) (h : is_irreducible ρ) : f = 0 ∨ function.injective f :=
begin
  have := h f.ker,
  cases this with hk hk,
  { apply or.intro_right,
    exact rep_hom.ker_eq_bot.mp hk },
  { apply or.intro_left,
    exact rep_hom.ker_eq_top.mp hk }
end

/-- A rep_hom from a representation to an irreducible representation is either 0 or
surjective. -/
lemma schur_surjective {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (f : ρ →ᵣ ρ₂) (h : is_irreducible ρ₂) : f = 0 ∨ function.surjective f :=
begin
  have := h f.range,
  cases this with hr hr,
  { apply or.intro_left,
    exact rep_hom.range_eq_bot.mp hr },
  { apply or.intro_right,
    exact rep_hom.range_eq_top.mp hr }
end

/-- Schur's lemma: A rep_hom between irreducible representations is either 0 or bijective. -/
theorem schur {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (f : ρ →ᵣ ρ₂) (h₁ : is_irreducible ρ) (h₂ : is_irreducible ρ₂) : f = 0 ∨ function.bijective f :=
begin
  have := and.intro (schur_injective f h₁) (schur_surjective f h₂),
  rw [←or_and_distrib_left, ←function.bijective] at this,
  exact this
end

/-- Produce a rep_equiv using Schur's lemma -/
noncomputable def schur_equiv {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (f : ρ →ᵣ ρ₂) (h₁ : is_irreducible ρ) (h₂ : is_irreducible ρ₂) (h₃ : f ≠ 0) : ρ ≃ᵣ ρ₂ :=
begin
  apply rep_equiv.of_bijective f,
  { have h_inj := schur_injective f h₁,
    cases h_inj,
    exact absurd h_inj h₃,
    exact h_inj },
  { have h_sur := schur_surjective f h₂,
    cases h_sur,
    exact absurd h_sur h₃,
    exact h_sur }
end

/-- For a finite-dimensional representation over an algebraically closed field, every
representation endomorphism is a scalar multiple of the identity. -/
theorem schur_smul_one {k G V : Type*} [field k] [is_alg_closed k] [monoid G] [add_comm_group V]
  [module k V] [finite_dimensional k V] {ρ : representation k G V}
  (f : ρ →ᵣ ρ) (h : is_irreducible ρ) : ∃ c : k, f = c • 1 :=
begin
  by_cases ht : ∃ (x y : V), x ≠ y,
  -- case V is nontrivial
  { rcases ht with ⟨x, y, ht⟩,
    haveI := nontrivial_of_ne x y ht, -- synth instance of nontrivial V
    obtain ⟨c, hc⟩ := module.End.exists_eigenvalue f.to_linear_map, -- get eigenvalue
    refine ⟨c, _⟩,
    rw ←sub_eq_zero,
    apply or_iff_not_imp_right.mp (schur_injective _ h), -- use schur to show f - c • 1 = 0
    apply not_imp_not.mpr rep_hom.ker_eq_bot.mpr, -- show f - c • 1 is not injective
    apply not_imp_not.mpr subrep.to_submodule_eq.mpr, -- work on the level of submodules
    exact hc },
  -- case V is trivial, show f = 0
  { push_neg at ht,
    refine ⟨0, _⟩,
    ext,
    rw [zero_smul, rep_hom.zero_apply],
    exact ht (f x) 0 }
end

set_option trace.simplify.rewrite true
/-- The space of rep_hom between two equivalent non-zero irreducible representations
is one-dimensional. -/
lemma lin_hom_irreducible_rank_eq_one {k G V V₂ : Type*} [field k] [is_alg_closed k] [monoid G]
  [add_comm_group V] [module k V] [finite_dimensional k V] [nontrivial V]
  [add_comm_group V₂] [module k V₂]
  {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (h : is_irreducible ρ) (e : ρ ≃ᵣ ρ₂) :
  finite_dimensional.finrank k (ρ →ᵣ ρ₂) = 1 :=
begin
  apply finrank_eq_one_iff'.mpr,
  refine ⟨e, _⟩,
  split,
  { apply not_imp_not.mpr rep_hom.congr_fun,
    push_neg,
    obtain ⟨x, hx⟩ := exists_ne (0 : V),
    refine ⟨x, _⟩,
    rw [rep_equiv.coe_coe, rep_hom.zero_apply, ne.def, rep_equiv.map_eq_zero_iff],
    exact hx },
  { intro f,
    have sch := schur f h (rep_equiv.is_irreducible h e),
    cases sch,
    { refine ⟨0, _⟩,
      rw [sch, zero_smul] },
    { set f' := rep_equiv.of_bijective f sch.1 sch.2 with hf,
      obtain ⟨c, hc⟩ := schur_smul_one ((f'.trans e.symm) : ρ →ᵣ ρ) h₁,
      refine ⟨c, _⟩,
      rw [←rep_equiv.comp_coe, ←rep_equiv.to_rep_hom_eq_coe,
      rep_equiv.to_rep_hom_symm_comp_eq, rep_equiv.to_rep_hom_eq_coe, rep_hom.comp_smul,
      rep_hom.one_eq_id, rep_hom.comp_id] at hc,
      rw [←hc, hf],
      ext,
      refl } }
end

/-- The space of rep_hom between two inequivalent irreducible representations is trivial. -/
lemma lin_hom_irreducible_rank {k G V V₂ : Type*} [field k] [is_alg_closed k] [monoid G]
  [add_comm_group V] [module k V] [finite_dimensional k V]
  [add_comm_group V₂] [module k V₂] [finite_dimensional k V₂]
  {ρ : representation k G V} {ρ₂ : representation k G V₂}
  (h₁ : is_irreducible ρ) (h₂ : is_irreducible ρ₂) (h₃ : is_empty (ρ ≃ᵣ ρ₂)) :
  finite_dimensional.finrank k (ρ →ᵣ ρ₂) = 0 :=
begin
  apply finrank_eq_zero_of_dim_eq_zero,
  apply dim_zero_iff.mpr,
  show nontrivial k,
  apply_instance,
  show no_zero_smul_divisors k (ρ →ᵣ ρ₂),
  apply_instance,
  split,
  have : ∀ f : ρ →ᵣ ρ₂, f = 0,
  { intro,
    apply or_iff_not_imp_right.mp (schur f h₁ h₂),
    intro hf,
    have e := rep_equiv.of_bijective f hf.1 hf.2,
    exact is_empty_iff.mp h₃ e },
  intros f g,
  rw [this f, this g]
end

end representation
