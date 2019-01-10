/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes, Morenikeji Neri
-/

import algebra.euclidean_domain
import ring_theory.ideals ring_theory.noetherian ring_theory.unique_factorization_domain

variables {α : Type*}

open set function ideal
local attribute [instance] classical.prop_decidable

class ideal.is_principal [comm_ring α] (S : ideal α) : Prop :=
(principal : ∃ a, S = span {a})

class principal_ideal_domain (α : Type*) extends integral_domain α :=
(principal : ∀ (S : ideal α), S.is_principal)
attribute [instance] principal_ideal_domain.principal
namespace ideal.is_principal
variable [comm_ring α]

noncomputable def generator (S : ideal α) [S.is_principal] : α :=
classical.some (principal S)

lemma span_singleton_generator (S : ideal α) [S.is_principal] : span {generator S} = S :=
eq.symm (classical.some_spec (principal S))

@[simp] lemma generator_mem (S : ideal α) [S.is_principal] : generator S ∈ S :=
by conv {to_rhs, rw ← span_singleton_generator S}; exact subset_span (mem_singleton _)

lemma mem_iff_generator_dvd (S : ideal α) [S.is_principal] {x : α} : x ∈ S ↔ generator S ∣ x :=
by rw [← mem_span_singleton, span_singleton_generator]

lemma eq_bot_iff_generator_eq_zero (S : ideal α) [S.is_principal] :
  S = ⊥ ↔ generator S = 0 :=
by rw [← span_singleton_eq_bot, span_singleton_generator]

end ideal.is_principal

namespace is_prime
open ideal.is_principal ideal

lemma to_maximal_ideal [principal_ideal_domain α] {S : ideal α}
  [hpi : is_prime S] (hS : S ≠ ⊥) : is_maximal S :=
is_maximal_iff.2 ⟨(ne_top_iff_one S).1 hpi.1, begin
  assume T x hST hxS hxT,
  haveI := principal_ideal_domain.principal S,
  haveI := principal_ideal_domain.principal T,
  cases (mem_iff_generator_dvd _).1 (hST $ generator_mem S) with z hz,
  cases hpi.2 (show generator T * z ∈ S, from hz ▸ generator_mem S),
  { have hTS : T ≤ S, rwa [← span_singleton_generator T, span_le, singleton_subset_iff],
    exact (hxS $ hTS hxT).elim },
  cases (mem_iff_generator_dvd _).1 h with y hy,
  have : generator S ≠ 0 := mt (eq_bot_iff_generator_eq_zero _).2 hS,
  rw [← mul_one (generator S), hy, mul_left_comm, domain.mul_left_inj this] at hz,
  exact hz.symm ▸ ideal.mul_mem_right _ (generator_mem T)
end⟩

end is_prime

section
open euclidean_domain
variable [euclidean_domain α]

lemma mod_mem_iff {S : ideal α} {x y : α} (hy : y ∈ S) : x % y ∈ S ↔ x ∈ S :=
⟨λ hxy, div_add_mod x y ▸ ideal.add_mem S (mul_mem_right S hy) hxy,
  λ hx, (mod_eq_sub_mul_div x y).symm ▸ ideal.sub_mem S hx (ideal.mul_mem_right S hy)⟩

instance euclidean_domain.to_principal_ideal_domain : principal_ideal_domain α :=
{ principal := λ S, by exactI
    ⟨if h : {x : α | x ∈ S ∧ x ≠ 0} = ∅
    then ⟨0, submodule.ext $ λ a, by rw [← submodule.bot_coe, span_eq, submodule.mem_bot]; exact
      ⟨λ haS, by_contradiction $ λ ha0, eq_empty_iff_forall_not_mem.1 h a ⟨haS, ha0⟩,
      λ h₁, h₁.symm ▸ S.zero_mem⟩⟩
    else
    have wf : well_founded euclidean_domain.r := euclidean_domain.r_well_founded α,
    have hmin : well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h ∈ S ∧
        well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h ≠ 0,
      from well_founded.min_mem wf {x : α | x ∈ S ∧ x ≠ 0} h,
    ⟨well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h,
      submodule.ext $ λ x,
      ⟨λ hx, div_add_mod x (well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h) ▸
        (mem_span_singleton.2 $ dvd_add (dvd_mul_right _ _) $
        have (x % (well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h) ∉ {x : α | x ∈ S ∧ x ≠ 0}),
          from λ h₁, well_founded.not_lt_min wf _ h h₁ (mod_lt x hmin.2),
        have x % well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h = 0, by finish [(mod_mem_iff hmin.1).2 hx],
        by simp *),
      λ hx, let ⟨y, hy⟩ := mem_span_singleton.1 hx in hy.symm ▸ ideal.mul_mem_right _ hmin.1⟩⟩⟩ }

end


namespace principal_ideal_domain
variables [principal_ideal_domain α]

lemma is_noetherian_ring : is_noetherian_ring α :=
assume s : ideal α,
begin
  cases (principal s).principal with a hs,
  refine ⟨finset.singleton a, submodule.ext' _⟩, rw hs, refl
end

section
local attribute [instance] classical.prop_decidable
open submodule

lemma factors_decreasing (b₁ b₂ : α) (h₁ : b₁ ≠ 0) (h₂ : ¬ is_unit b₂) :
  submodule.span ({b₁ * b₂} : set α) < submodule.span {b₁} :=
lt_of_le_not_le (ideal.span_le.2 $ singleton_subset_iff.2 $
  ideal.mem_span_singleton.2 ⟨b₂, rfl⟩) $ λ h,
h₂ $ is_unit_of_dvd_one _ $ (mul_dvd_mul_iff_left h₁).1 $
by rwa [mul_one, ← ideal.span_singleton_le_span_singleton]

end

lemma is_maximal_of_irreducible {p : α} (hp : irreducible p) :
  is_maximal (span ({p} : set α)) :=
⟨mt span_singleton_eq_top.1 hp.1, λ I hI, begin
  rcases principal I with ⟨a, rfl⟩,
  rw span_singleton_eq_top,
  unfreezeI,
  rcases span_singleton_le_span_singleton.1 (le_of_lt hI) with ⟨b, rfl⟩,
  refine (of_irreducible_mul hp).resolve_right (mt (λ hb, _) (not_le_of_lt hI)),
  rw [span_singleton_le_span_singleton, mul_dvd_of_is_unit_right hb]
end⟩

lemma irreducible_iff_prime {p : α} : irreducible p ↔ prime p :=
⟨λ hp, (span_singleton_prime $ nonzero_of_irreducible hp).1 $
    (is_maximal_of_irreducible hp).is_prime,
  irreducible_of_prime⟩

lemma associates_irreducible_iff_prime : ∀{p : associates α}, irreducible p ↔ p.prime :=
associates.forall_associated.2 $ assume a,
by rw [associates.irreducible_mk_iff, associates.prime_mk, irreducible_iff_prime]

section
local attribute [instance] classical.prop_decidable

noncomputable def factors (a : α) : multiset α :=
if h : a = 0 then ∅ else classical.some
  (is_noetherian_ring.exists_factors is_noetherian_ring a h)

lemma factors_spec (a : α) (h : a ≠ 0) :
  (∀b∈factors a, irreducible b) ∧ associated a (factors a).prod :=
begin
  unfold factors, rw [dif_neg h],
  exact classical.some_spec
    (is_noetherian_ring.exists_factors is_noetherian_ring a h)
end

/-- The unique factorization domain structure given by the principal ideal domain.

This is not added as type class instance, since the `factors` might be computed in a different way.
E.g. factors could return normalized values.
-/
noncomputable def to_unique_factorization_domain : unique_factorization_domain α :=
{ factors := factors,
  factors_prod := assume a ha, associated.symm (factors_spec a ha).2,
  prime_factors := assume a ha, by simpa [irreducible_iff_prime] using (factors_spec a ha).1 }

end

end principal_ideal_domain
