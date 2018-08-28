/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import algebra.euclidean_domain ring_theory.ideals
universes u v
variables {α : Type u} {β : Type v} [comm_ring α] {a b : α}

open set function is_ideal
local attribute [instance] classical.prop_decidable

class is_principal_ideal (S : set α) : Prop :=
(principal : ∃ a : α, S = {x | a ∣ x})

class principal_ideal_domain (α : Type u) extends integral_domain α :=
(principal : ∀ (S : set α) [is_ideal S], is_principal_ideal S)

namespace is_principal_ideal

noncomputable def generator (S : set α) [is_principal_ideal S] : α :=
classical.some (principal S)

lemma generator_generates (S : set α) [is_principal_ideal S] : {x | generator S ∣ x} = S :=
eq.symm (classical.some_spec (principal S))

@[simp] lemma generator_mem (S : set α) [is_principal_ideal S] : generator S ∈ S :=
by conv {to_rhs, rw ← generator_generates S}; exact dvd_refl _

lemma mem_iff_generator_dvd (S : set α) [is_principal_ideal S] {x : α} : x ∈ S ↔ generator S ∣ x :=
by conv {to_lhs, rw ← generator_generates S}; refl

lemma eq_trivial_iff_generator_eq_zero (S : set α) [is_principal_ideal S] :
  S = trivial α ↔ generator S = 0 :=
⟨λ h, by rw [← mem_trivial, ← h]; exact generator_mem S,
  λ h, set.ext $ λ x, by rw [mem_iff_generator_dvd S, h, zero_dvd_iff, mem_trivial]⟩

instance to_is_ideal (S : set α) [is_principal_ideal S] : is_ideal S :=
{ to_is_submodule :=
  { zero_ := by rw ← generator_generates S; simp,
    add_ := λ x y h, by rw ← generator_generates S at *; exact (dvd_add_iff_right h).1,
    smul := λ c x h, by rw ← generator_generates S at h ⊢; exact dvd_mul_of_dvd_right h _ } }

end is_principal_ideal

open euclidean_domain is_principal_ideal is_ideal

lemma mod_mem_iff {α : Type u} [euclidean_domain α] {S : set α} [is_ideal S] {x y : α}
  (hy : y ∈ S) : x % y ∈ S ↔ x ∈ S :=
⟨λ hxy, div_add_mod x y ▸ is_ideal.add (is_ideal.mul_right hy) hxy,
  λ hx, (mod_eq_sub_mul_div x y).symm ▸ is_ideal.sub hx (is_ideal.mul_right hy)⟩

instance euclidean_domain.to_principal_ideal_domain {α : Type u} [euclidean_domain α] :
  principal_ideal_domain α :=
{ principal := λ S h, by exactI
    ⟨if h : {x : α | x ∈ S ∧ x ≠ 0} = ∅
    then ⟨0, set.ext $ λ a, ⟨by finish [set.ext_iff],
            λ h₁, (show a = 0, by simpa using h₁).symm ▸ is_ideal.zero S⟩⟩
    else
    have wf : well_founded euclidean_domain.r := euclidean_domain.r_well_founded α,
    have hmin : well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h ∈ S ∧
        well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h ≠ 0,
      from well_founded.min_mem wf {x : α | x ∈ S ∧ x ≠ 0} h,
    ⟨well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h,
      set.ext $ λ x,
      ⟨λ hx, div_add_mod x (well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h) ▸
        dvd_add (dvd_mul_right _ _)
        (have (x % (well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h) ∉ {x : α | x ∈ S ∧ x ≠ 0}),
          from λ h₁, well_founded.not_lt_min wf _ h h₁ (mod_lt x hmin.2),
        have x % well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h = 0, by finish [(mod_mem_iff hmin.1).2 hx],
        by simp *),
      λ hx, let ⟨y, hy⟩ := hx in hy.symm ▸ is_ideal.mul_right hmin.1⟩⟩⟩ }

lemma is_prime_ideal.to_maximal_ideal {α : Type*} [principal_ideal_domain α] {S : set α}
  [hpi : is_prime_ideal S] (hS : S ≠ trivial α) : is_maximal_ideal S :=
is_maximal_ideal.mk _ (is_proper_ideal_iff_one_not_mem.1 (by apply_instance))
begin
  assume x T i hST hxS hxT,
  haveI := principal_ideal_domain.principal S,
  haveI := principal_ideal_domain.principal T,
  cases (mem_iff_generator_dvd _).1 (hST ((mem_iff_generator_dvd _).2 (dvd_refl _))) with z hz,
  cases is_prime_ideal.mem_or_mem_of_mul_mem (show generator T * z ∈ S,
    by rw [mem_iff_generator_dvd S, ← hz]),
  { have hST' : S = T := set.subset.antisymm hST
      (λ y hyT, (mem_iff_generator_dvd _).2
        (dvd.trans ((mem_iff_generator_dvd _).1 h) ((mem_iff_generator_dvd _).1 hyT))),
    cc },
  { cases (mem_iff_generator_dvd _).1 h with y hy,
    rw [← mul_one (generator S), hy, mul_left_comm,
      domain.mul_left_inj (mt (eq_trivial_iff_generator_eq_zero S).2 hS)] at hz,
    exact hz.symm ▸ is_ideal.mul_right (generator_mem T) }
end