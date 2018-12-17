/-
Copyright (c) 2018 Mario Carneiro and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/

import order.order_iso
import data.fintype data.polynomial
import linear_algebra.lc
import tactic.tidy
import ring_theory.multiplicity
import ring_theory.ideals

open set lattice

namespace submodule
variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β]

def fg (s : submodule α β) : Prop := ∃ t : finset β, submodule.span ↑t = s

theorem fg_def {s : submodule α β} :
  s.fg ↔ ∃ t : set β, finite t ∧ span t = s :=
⟨λ ⟨t, h⟩, ⟨_, finset.finite_to_set t, h⟩, begin
  rintro ⟨t', h, rfl⟩,
  rcases finite.exists_finset_coe h with ⟨t, rfl⟩,
  exact ⟨t, rfl⟩
end⟩

end submodule

def is_noetherian (α β) [ring α] [add_comm_group β] [module α β] : Prop :=
∀ (s : submodule α β), s.fg

theorem is_noetherian_iff_well_founded
  (α β) [ring α] [add_comm_group β] [module α β] :
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
  { rw [← submodule.Union_coe_of_directed _ N _],
    { show t ⊆ M, rw ← h₂,
      apply submodule.subset_span },
    { apply_instance },
    { exact λ i j, ⟨max i j,
        hN' (le_max_left _ _),
        hN' (le_max_right _ _)⟩ } },
  simp [subset_def] at this,
  choose f hf using show ∀ x : t, ∃ (i : ℕ), x.1 ∈ N i, { simpa },
  cases h₁ with h₁,
  let A := finset.sup (@finset.univ t h₁) f,
  have : M ≤ N A,
  { rw ← h₂, apply submodule.span_le.2,
    exact λ x h, hN' (finset.le_sup (@finset.mem_univ t h₁ _))
      (hf ⟨x, h⟩) },
  exact not_le_of_lt (hN.1 (nat.lt_succ_self A))
    (le_trans (le_supr _ _) this)
  end,
  begin
    assume h N,
    suffices : ∀ M ≤ N, ∃ s, finite s ∧ M ⊔ submodule.span s = N,
    { rcases this ⊥ bot_le with ⟨s, hs, e⟩,
      exact submodule.fg_def.2 ⟨s, hs, by simpa using e⟩ },
    refine λ M, h.induction M _, intros M IH MN,
    letI := classical.dec,
    by_cases h : ∀ x, x ∈ N → x ∈ M,
    { cases le_antisymm MN h, exact ⟨∅, by simp⟩ },
    { simp [not_forall] at h,
      rcases h with ⟨x, h, h₂⟩,
      have : ¬M ⊔ submodule.span {x} ≤ M,
      { intro hn, apply h₂,
        have := le_trans le_sup_right hn,
        exact submodule.span_le.1 this (mem_singleton x) },
      rcases IH (M ⊔ submodule.span {x})
        ⟨@le_sup_left _ _ M _, this⟩
        (sup_le MN (submodule.span_le.2 (by simpa))) with ⟨s, hs, hs₂⟩,
      refine ⟨insert x s, finite_insert _ hs, _⟩,
      rw [← hs₂, sup_assoc, ← submodule.span_union], simp }
  end⟩

def is_noetherian_ring (α) [ring α] : Prop := is_noetherian α α

theorem ring.is_noetherian_of_fintype (R M) [ring R] [add_comm_group M] [module R M] [fintype M] : is_noetherian R M :=
by letI := classical.dec; exact
assume s, ⟨to_finset s, by rw [finset.coe_to_finset', submodule.span_eq]⟩

theorem ring.is_noetherian_of_zero_eq_one {R} [ring R] (h01 : (0 : R) = 1) : is_noetherian_ring R :=
by haveI := subsingleton_of_zero_eq_one R h01;
   haveI := fintype.of_subsingleton (0:R);
   exact ring.is_noetherian_of_fintype R R

theorem is_noetherian_of_submodule_of_noetherian (R M) [ring R] [add_comm_group M] [module R M] (N : submodule R M)
  (h : is_noetherian R M) : is_noetherian R N :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  convert order_embedding.well_founded (order_embedding.rsymm (submodule.map_subtype.lt_order_embedding N)) h
end

theorem is_noetherian_of_quotient_of_noetherian (R) [ring R] (M) [add_comm_group M] [module R M] (N : submodule R M)
  (h : is_noetherian R M) : is_noetherian R N.quotient :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  convert order_embedding.well_founded (order_embedding.rsymm (submodule.comap_mkq.lt_order_embedding N)) h
end

namespace is_neotherian_ring

variables {α : Type*} [integral_domain α] (hα : is_noetherian_ring α)
--variables [decidable_rel ((∣) : α → α → Prop)]
open associates multiplicity nat

local attribute [elab_as_eliminator] well_founded.fix
local attribute [instance, priority 0] classical.prop_decidable

lemma well_founded_dvd_not_unit : well_founded (λ a b : α, a ≠ 0 ∧ ∃ x, ¬is_unit x ∧ a * x = b) :=
well_founded.intro (@well_founded.fix α
  (λ a : α, acc (λ a b : α, a ≠ 0 ∧ ∃ x, ¬ is_unit x ∧ a * x = b) a) _
  (inv_image.wf (λ x, ideal.span {x}) ((is_noetherian_iff_well_founded α α).1 hα))
  (λ b ih, acc.intro _ (λ a ⟨hb0, x, hxu, hx⟩, ih _
    (lt_of_le_of_ne
      (λ y hy, ideal.mem_span_singleton.2 $
        dvd.trans (show a ∣ b, by simp [hx.symm])
          (ideal.mem_span_singleton.1 hy))
      (λ hab : ideal.span {b} = ideal.span {a},
        absurd (show a ∈ (ideal.span {a} : ideal α),
          by simp [ideal.mem_span_singleton])
        (hab ▸ mt ideal.mem_span_singleton.1
          (λ hab, hxu $ is_unit_iff_dvd_one.2 $
            (mul_dvd_mul_iff_left hb0).1 $
              by simpa [hx] using hab)))))))

lemma multiplicity_finite_of_is_not_unit {a b : α} (hb0 : b ≠ 0) (ha : ¬is_unit a) : finite a b :=
@well_founded.fix α
  (λ b : α, b ≠ 0 → finite a b) _ (well_founded_dvd_not_unit hα)
  (λ b ih hb0,
    if hab : a ∣ b
    then let ⟨x, hx⟩ := hab in
      if hxu : is_unit x
      then ⟨1, λ h, ha (is_unit_of_dvd_unit
        ((mul_dvd_mul_iff_left (show a ≠ 0, from (λ ha0, by simp * at *))).1 $
          by simpa [_root_.pow_add, hx] using h) hxu)⟩
      else
        have hx0 : x ≠ 0, from λ hx0, by simp * at *,
        have ha0 : a ≠ 0, from λ ha0, by simp * at *,
        hx.symm ▸ let ⟨n, hn⟩ := ih x ⟨hx0, a, ha, by rw [hx, mul_comm]⟩ hx0 in
        ⟨n + 1, by rw [_root_.pow_succ, mul_dvd_mul_iff_left ha0]; exact hn⟩
    else ⟨0, by simpa using hab⟩)
  b hb0

lemma finite_of_prime {p a : α} (hp : prime p) (ha0 : a ≠ 0) : finite p a :=
multiplicity_finite_of_is_not_unit hα ha0 hp.2.1

lemma exists_irreducible_factor {a : α} (ha : ¬ is_unit a) (ha0 : a ≠ 0) :
  ∃ i, irreducible i ∧ i ∣ a :=
(irreducible_or_factor a ha).elim (λ hai, ⟨a, hai, dvd_refl _⟩)
  (well_founded.fix
    (well_founded_dvd_not_unit hα)
    (λ a ih ha ha0 ⟨x, y, hx, hy, hxy⟩,
      have hx0 : x ≠ 0, from λ hx0, ha0 (by rw [← hxy, hx0, zero_mul]),
      (irreducible_or_factor x hx).elim
        (λ hxi, ⟨x, hxi, hxy ▸ by simp⟩)
        (λ hxf, let ⟨i, hi⟩ := ih x ⟨hx0, y, hy, hxy⟩ hx hx0 hxf in
          ⟨i, hi.1, dvd.trans hi.2 (hxy ▸ by simp)⟩)) a ha ha0)

end is_neotherian_ring