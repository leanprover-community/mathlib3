/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

Definition of splitting fields, and definition of homomorphism into any field that splits
-/
import data.polynomial
import ring_theory.principal_ideal_domain

universes u v w

variables {α : Type u} {β : Type v} {γ : Type w}

namespace polynomial

noncomputable theory
open_locale classical big_operators
variables [field α] [field β] [field γ]
open polynomial

section splits

variables (i : α →+* β)

/-- a polynomial `splits` iff it is zero or all of its irreducible factors have `degree` 1 -/
def splits (f : polynomial α) : Prop :=
f = 0 ∨ ∀ {g : polynomial β}, irreducible g → g ∣ f.map i → degree g = 1

@[simp] lemma splits_zero : splits i (0 : polynomial α) := or.inl rfl

@[simp] lemma splits_C (a : α) : splits i (C a) :=
if ha : a = 0 then ha.symm ▸ (@C_0 α _).symm ▸ splits_zero i
else
have hia : i a ≠ 0, from mt ((is_add_group_hom.injective_iff i).1
  i.injective _) ha,
or.inr $ λ g hg ⟨p, hp⟩, absurd hg.1 (classical.not_not.2 (is_unit_iff_degree_eq_zero.2 $
  by have := congr_arg degree hp;
    simp [degree_C hia, @eq_comm (with_bot ℕ) 0,
      nat.with_bot.add_eq_zero_iff] at this; clear _fun_match; tautology))

lemma splits_of_degree_eq_one {f : polynomial α} (hf : degree f = 1) : splits i f :=
or.inr $ λ g hg ⟨p, hp⟩,
  by have := congr_arg degree hp;
  simp [nat.with_bot.add_eq_one_iff, hf, @eq_comm (with_bot ℕ) 1,
    mt is_unit_iff_degree_eq_zero.2 hg.1] at this;
  clear _fun_match; tauto

lemma splits_of_degree_le_one {f : polynomial α} (hf : degree f ≤ 1) : splits i f :=
begin
  cases h : degree f with n,
  { rw [degree_eq_bot.1 h]; exact splits_zero i },
  { cases n with n,
    { rw [eq_C_of_degree_le_zero (trans_rel_right (≤) h (le_refl _))];
      exact splits_C _ _ },
    { have hn : n = 0,
      { rw h at hf,
        cases n, { refl }, { exact absurd hf dec_trivial } },
      exact splits_of_degree_eq_one _ (by rw [h, hn]; refl) } }
end

lemma splits_mul {f g : polynomial α} (hf : splits i f) (hg : splits i g) : splits i (f * g) :=
if h : f * g = 0 then by simp [h]
else or.inr $ λ p hp hpf, ((principal_ideal_ring.irreducible_iff_prime.1 hp).2.2 _ _
    (show p ∣ map i f * map i g, by convert hpf; rw polynomial.map_mul)).elim
  (hf.resolve_left (λ hf, by simpa [hf] using h) hp)
  (hg.resolve_left (λ hg, by simpa [hg] using h) hp)

lemma splits_of_splits_mul {f g : polynomial α} (hfg : f * g ≠ 0) (h : splits i (f * g)) :
  splits i f ∧ splits i g :=
⟨or.inr $ λ g hgi hg, or.resolve_left h hfg hgi (by rw map_mul; exact dvd.trans hg (dvd_mul_right _ _)),
 or.inr $ λ g hgi hg, or.resolve_left h hfg hgi (by rw map_mul; exact dvd.trans hg (dvd_mul_left _ _))⟩

lemma splits_map_iff (j : β →+* γ) {f : polynomial α} :
  splits j (f.map i) ↔ splits (j.comp i) f :=
by simp [splits, polynomial.map_map]

theorem splits_one : splits i 1 :=
splits_C i 1

theorem splits_X_sub_C {x : α} : (X - C x).splits i :=
splits_of_degree_eq_one _ $ degree_X_sub_C x

theorem splits_id_iff_splits {f : polynomial α} :
  (f.map i).splits (ring_hom.id β) ↔ f.splits i :=
by rw [splits_map_iff, ring_hom.id_comp]

theorem splits_mul_iff {f g : polynomial α} (hf : f ≠ 0) (hg : g ≠ 0) :
  (f * g).splits i ↔ f.splits i ∧ g.splits i :=
⟨splits_of_splits_mul i (mul_ne_zero hf hg), λ ⟨hfs, hgs⟩, splits_mul i hfs hgs⟩

theorem splits_prod {ι : Type w} {s : ι → polynomial α} {t : finset ι} :
  (∀ j ∈ t, (s j).splits i) → (∏ x in t, s x).splits i :=
begin
  refine finset.induction_on t (λ _, splits_one i) (λ a t hat ih ht, _),
  rw finset.forall_mem_insert at ht, rw finset.prod_insert hat,
  exact splits_mul i ht.1 (ih ht.2)
end

theorem splits_prod_iff {ι : Type w} {s : ι → polynomial α} {t : finset ι} :
  (∀ j ∈ t, s j ≠ 0) → ((∏ x in t, s x).splits i ↔ ∀ j ∈ t, (s j).splits i) :=
begin
  refine finset.induction_on t (λ _, ⟨λ _ _ h, h.elim, λ _, splits_one i⟩) (λ a t hat ih ht, _),
  rw finset.forall_mem_insert at ht ⊢,
  rw [finset.prod_insert hat, splits_mul_iff i ht.1 (finset.prod_ne_zero_iff.2 ht.2), ih ht.2]
end

lemma exists_root_of_splits {f : polynomial α} (hs : splits i f) (hf0 : degree f ≠ 0) :
  ∃ x, eval₂ i x f = 0 :=
if hf0 : f = 0 then ⟨37, by simp [hf0]⟩
else
  let ⟨g, hg⟩ := is_noetherian_ring.exists_irreducible_factor
    (show ¬ is_unit (f.map i), from mt is_unit_iff_degree_eq_zero.1 (by rwa degree_map))
    (by rw [ne.def, map_eq_zero]; exact hf0) in
  let ⟨x, hx⟩ := exists_root_of_degree_eq_one (hs.resolve_left hf0 hg.1 hg.2) in
  let ⟨i, hi⟩ := hg.2 in
  ⟨x, by rw [← eval_map, hi, eval_mul, show _ = _, from hx, zero_mul]⟩

lemma exists_multiset_of_splits {f : polynomial α} : splits i f →
  ∃ (s : multiset β), f.map i = C (i f.leading_coeff) *
  (s.map (λ a : β, (X : polynomial β) - C a)).prod :=
suffices splits (ring_hom.id _) (f.map i) → ∃ s : multiset β, f.map i =
  (C (f.map i).leading_coeff) * (s.map (λ a : β, (X : polynomial β) - C a)).prod,
by rwa [splits_map_iff, leading_coeff_map i] at this,
is_noetherian_ring.irreducible_induction_on (f.map i)
  (λ _, ⟨{37}, by simp [i.map_zero]⟩)
  (λ u hu _, ⟨0,
    by conv_lhs { rw eq_C_of_degree_eq_zero (is_unit_iff_degree_eq_zero.1 hu) };
      simp [leading_coeff, nat_degree_eq_of_degree_eq_some (is_unit_iff_degree_eq_zero.1 hu)]⟩)
  (λ f p hf0 hp ih hfs,
    have hpf0 : p * f ≠ 0, from mul_ne_zero hp.ne_zero hf0,
    let ⟨s, hs⟩ := ih (splits_of_splits_mul _ hpf0 hfs).2 in
    ⟨-(p * norm_unit p).coeff 0 :: s,
      have hp1 : degree p = 1, from hfs.resolve_left hpf0 hp (by simp),
      begin
        rw [multiset.map_cons, multiset.prod_cons, leading_coeff_mul, C_mul, mul_assoc,
          mul_left_comm (C f.leading_coeff), ← hs, ← mul_assoc, mul_left_inj' hf0],
        conv_lhs {rw eq_X_add_C_of_degree_eq_one hp1},
        simp only [mul_add, coe_norm_unit hp.ne_zero, mul_comm p, coeff_neg,
          C_neg, sub_eq_add_neg, neg_neg, coeff_C_mul, (mul_assoc _ _ _).symm, C_mul.symm,
          mul_inv_cancel (show p.leading_coeff ≠ 0, from mt leading_coeff_eq_zero.1
            hp.ne_zero), one_mul],
      end⟩)

section UFD

local attribute [instance, priority 10] principal_ideal_ring.to_unique_factorization_domain
local infix ` ~ᵤ ` : 50 := associated

open unique_factorization_domain associates

lemma splits_of_exists_multiset {f : polynomial α} {s : multiset β}
  (hs : f.map i = C (i f.leading_coeff) * (s.map (λ a : β, (X : polynomial β) - C a)).prod) :
  splits i f :=
if hf0 : f = 0 then or.inl hf0
else
  or.inr $ λ p hp hdp,
    have ht : multiset.rel associated
      (factors (f.map i)) (s.map (λ a : β, (X : polynomial β) - C a)) :=
    unique
      (λ p hp, irreducible_factors (mt (map_eq_zero i).1 hf0) _ hp)
      (λ p' m, begin
          obtain ⟨a,m,rfl⟩ := multiset.mem_map.1 m,
          exact irreducible_of_degree_eq_one (degree_X_sub_C _),
        end)
      (associated.symm $ calc _ ~ᵤ f.map i :
        ⟨(units.map' C : units β →* units (polynomial β)) (units.mk0 (f.map i).leading_coeff
            (mt leading_coeff_eq_zero.1 (mt (map_eq_zero i).1 hf0))),
          by conv_rhs {rw [hs, ← leading_coeff_map i, mul_comm]}; refl⟩
        ... ~ᵤ _ : associated.symm (unique_factorization_domain.factors_prod (by simpa using hf0))),
  let ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd (by simpa) hp hdp in
  let ⟨q', hq', hqq'⟩ := multiset.exists_mem_of_rel_of_mem ht hq in
  let ⟨a, ha⟩ := multiset.mem_map.1 hq' in
  by rw [← degree_X_sub_C a, ha.2];
    exact degree_eq_degree_of_associated (hpq.trans hqq')

lemma splits_of_splits_id {f : polynomial α} : splits (ring_hom.id _) f → splits i f :=
unique_factorization_domain.induction_on_prime f (λ _, splits_zero _)
  (λ _ hu _, splits_of_degree_le_one _
    ((is_unit_iff_degree_eq_zero.1 hu).symm ▸ dec_trivial))
  (λ a p ha0 hp ih hfi, splits_mul _
    (splits_of_degree_eq_one _
      ((splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).1.resolve_left
        hp.1 (irreducible_of_prime hp) (by rw map_id)))
    (ih (splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).2))

end UFD

lemma splits_iff_exists_multiset {f : polynomial α} : splits i f ↔
  ∃ (s : multiset β), f.map i = C (i f.leading_coeff) *
  (s.map (λ a : β, (X : polynomial β) - C a)).prod :=
⟨exists_multiset_of_splits i, λ ⟨s, hs⟩, splits_of_exists_multiset i hs⟩

lemma splits_comp_of_splits (j : β →+* γ) {f : polynomial α}
  (h : splits i f) : splits (j.comp i) f :=
begin
  change i with ((ring_hom.id _).comp i) at h,
  rw [← splits_map_iff],
  rw [← splits_map_iff i] at h,
  exact splits_of_splits_id _ h
end

end splits

end polynomial
