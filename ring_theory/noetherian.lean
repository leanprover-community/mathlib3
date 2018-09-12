/-
Copyright (c) 2018 Mario Carneiro and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro and Kevin Buzzard
-/

import order.order_iso
import data.fintype data.polynomial
import tactic.tidy
import linear_algebra.submodule
import ring_theory.ideals

local attribute [instance] classical.dec
open set lattice

def is_fg {α β} [ring α] [module α β]
  (s : set β) [is_submodule s] : Prop :=
∃ t : finset β, _root_.span ↑t = s

namespace submodule
universes u v
variables {α : Type u} {β : Type v} [ring α] [module α β]

def fg (s : submodule α β) : Prop := is_fg (s : set β)

theorem fg_def {s : submodule α β} :
  s.fg ↔ ∃ t : set β, finite t ∧ span t = s :=
⟨λ ⟨t, h⟩, ⟨_, finset.finite_to_set t, ext h⟩, begin
  rintro ⟨t', h, rfl⟩,
  rcases finite.exists_finset_coe h with ⟨t, rfl⟩,
  exact ⟨t, rfl⟩
end⟩

end submodule

def is_noetherian (α β) [ring α] [module α β] : Prop :=
∀ (s : submodule α β), s.fg

theorem is_noetherian_iff_well_founded
  {α β} [ring α] [module α β] :
  is_noetherian α β ↔ well_founded ((>) : submodule α β → submodule α β → Prop) :=
⟨λ h, begin
  apply order_embedding.well_founded_iff_no_descending_seq.2,
  swap, { apply is_strict_order.swap },
  rintro ⟨⟨N, hN⟩⟩,
  let M := ⨆ n, N n,
  rcases submodule.fg_def.1 (h M) with ⟨t, h₁, h₂⟩,
  have hN' : ∀ {a b}, a ≤ b → N a ≤ N b :=
    λ a b, (le_iff_le_of_strict_mono N (λ _ _, hN.1)).2,
  have : t ⊆ ⋃ i, (N i : set β),
  { rw [← submodule.Union_set_of_directed _ N _],
    { show t ⊆ M, rw ← h₂,
      apply subset_span },
    { apply_instance },
    { exact λ i j, ⟨max i j,
        hN' (le_max_left _ _),
        hN' (le_max_right _ _)⟩ } },
  simp [subset_def] at this,
  have : ∀ x : t, (∃ (i : ℕ), x.1 ∈ N i), {simpa},
  rcases classical.axiom_of_choice this with ⟨f, hf⟩,
  dsimp at f hf,
  cases h₁ with h₁,
  let A := finset.sup (@finset.univ t h₁) f,
  have : M ≤ N A,
  { rw ← h₂, apply submodule.span_subset_iff.2,
    exact λ x h, hN' (finset.le_sup (@finset.mem_univ t h₁ _))
      (hf ⟨x, h⟩) },
  exact not_le_of_lt (hN.1 (nat.lt_succ_self A))
    (le_trans (le_supr _ _) this)
 end,
 λ h N, begin
  suffices : ∀ M ≤ N, ∃ s, finite s ∧ M ⊔ submodule.span s = N,
  { rcases this ⊥ bot_le with ⟨s, hs, e⟩,
    exact submodule.fg_def.2 ⟨s, hs, by simpa using e⟩ },
  refine λ M, h.induction M _, intros M IH MN,
  by_cases h : ∀ x, x ∈ N → x ∈ M,
  { cases le_antisymm MN h, exact ⟨∅, by simp⟩ },
  { simp [not_forall] at h,
    rcases h with ⟨x, h, h₂⟩,
    have : ¬M ⊔ submodule.span {x} ≤ M,
    { intro hn, apply h₂,
      simpa using submodule.span_subset_iff.1 (le_trans le_sup_right hn) },
    rcases IH (M ⊔ submodule.span {x})
      ⟨@le_sup_left _ _ M _, this⟩
      (sup_le MN (submodule.span_subset_iff.2 (by simpa))) with ⟨s, hs, hs₂⟩,
    refine ⟨insert x s, finite_insert _ hs, _⟩,
    rw [← hs₂, sup_assoc, ← submodule.span_union], simp }
 end⟩

def is_noetherian_ring (α) [ring α] : Prop := is_noetherian α α

theorem ring.is_noetherian_of_fintype (R M) [ring R] [module R M] [fintype M] : is_noetherian R M :=
begin
  intro N,
  existsi (to_finset N : finset M),
  suffices : span (N : set M) = N,
    simpa,
  exact span_eq_of_is_submodule N.to_is_submodule,
end

noncomputable instance fintype.of_subsingleton_ring {α} [ring α] [h : subsingleton α] : fintype α :=
{ elems := {0},
  complete := λ x, begin
    suffices: x = 0, by simpa,
    exact subsingleton.elim x 0,
  end
}

theorem ring.is_noetherian_of_zero_eq_one {R} [ring R] (h01 : (0 : R) = 1) : is_noetherian_ring R :=
by haveI := semiring.subsingleton_of_zero_eq_one h01; exact ring.is_noetherian_of_fintype R R

theorem is_noetherian_of_submodule_of_noetherian (R M) [ring R] [module R M] (N : set M) [is_submodule N]
  (h : is_noetherian R M) : is_noetherian R N :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  convert order_embedding.well_founded (order_embedding.rsymm (submodule.lt_order_embedding R M N)) h,end

theorem is_noetherian_of_quotient_of_noetherian (R) [ring R] (M) [module R M] (N : set M) [is_submodule N]
  (h : is_noetherian R M) : is_noetherian R (quotient_module.quotient M N) :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  convert order_embedding.well_founded (order_embedding.rsymm (quotient_module.lt_order_embedding R M N)) h,end
