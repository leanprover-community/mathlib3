/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes, Morenikeji Neri
-/

import algebra.euclidean_domain
import ring_theory.ideals ring_theory.noetherian ring_theory.unique_factorization_domain

variables {α : Type*}

open set function is_ideal
local attribute [instance] classical.prop_decidable

class is_principal_ideal [comm_ring α] (S : set α) : Prop :=
(principal : ∃ a : α, S = {x | a ∣ x})

class principal_ideal_domain (α : Type*) extends integral_domain α :=
(principal : ∀ (S : set α) [is_ideal S], is_principal_ideal S)

namespace is_principal_ideal
variable [comm_ring α]

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

namespace is_prime_ideal
open is_principal_ideal is_ideal

lemma to_maximal_ideal [principal_ideal_domain α] {S : set α}
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

end is_prime_ideal

section
open euclidean_domain
variable [euclidean_domain α]

lemma mod_mem_iff {S : set α} [is_ideal S] {x y : α} (hy : y ∈ S) : x % y ∈ S ↔ x ∈ S :=
⟨λ hxy, div_add_mod x y ▸ is_ideal.add (is_ideal.mul_right hy) hxy,
  λ hx, (mod_eq_sub_mul_div x y).symm ▸ is_ideal.sub hx (is_ideal.mul_right hy)⟩

instance euclidean_domain.to_principal_ideal_domain : principal_ideal_domain α :=
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

end


namespace principal_ideal_domain
variables [principal_ideal_domain α]

lemma is_noetherian_ring : is_noetherian_ring α :=
assume ⟨s, hs⟩,
begin
  letI := classical.dec_eq α,
  have : is_ideal s := {.. hs},
  rcases (principal s).principal with ⟨a, rfl⟩,
  refine ⟨{a}, show span (↑({a} : finset α)) = {x : α | a ∣ x}, from _⟩,
  simp [span_singleton, set.range, has_dvd.dvd, eq_comm, mul_comm]
end

section
local attribute [instance] classical.prop_decidable
open submodule

lemma factors_decreasing (b₁ b₂ : α) (h₁ : b₁ ≠ 0) (h₂ : ¬ is_unit b₂) :
  submodule.span {b₁} > submodule.span ({b₁ * b₂} : set α) :=
lt_of_le_not_le (span_singleton_subset.2 $ mem_span_singleton.2 $ ⟨b₂, by simp [mul_comm]⟩) $
assume (h : submodule.span {b₁} ⊆ submodule.span ({b₁ * b₂} : set α)),
have ∃ (c : α), b₁ * (b₂ * c) = b₁ * 1,
{ simpa [span_singleton_subset, mem_span_singleton, mul_left_comm, mul_comm, mul_assoc, eq_comm] using h },
let ⟨c, eq⟩ := this in
have b₂ * c = 1, from eq_of_mul_eq_mul_left h₁ eq,
h₂ ⟨units.mk_of_mul_eq_one _ _ this, rfl⟩

lemma exists_factors (a : α) : a ≠ 0 → ∃f:multiset α, (∀b∈f, irreducible b) ∧ associated a f.prod :=
have well_founded (inv_image (>) (λb, submodule.span ({b} : set α))), from
  inv_image.wf _ $ is_noetherian_iff_well_founded.1 $ is_noetherian_ring,
this.induction a
begin
  assume a ih ha,
  by_cases h_unit : is_unit a,
  { exact match a, h_unit with _, ⟨u, rfl⟩ := ⟨∅, by simp, u⁻¹, by simp⟩ end },
  by_cases h_irreducible : irreducible a,
  { exact ⟨{a}, by simp [h_irreducible]⟩ },

  have : ∃b₁ b₂, a = b₁ * b₂ ∧ ¬ is_unit b₁ ∧ ¬ is_unit b₂,
  { simp [irreducible, not_or_distrib, not_forall] at h_irreducible; from h_irreducible h_unit },
  rcases this with ⟨b₁, b₂, eq, h₁, h₂⟩,

  have hb₁ : b₁ ≠ 0, { assume eq, simp * at * },
  have : submodule.span {b₁} > submodule.span ({a} : set α),
    by rw [eq]; from factors_decreasing b₁ b₂ hb₁ h₂,
  rcases ih b₁ this hb₁ with ⟨f₁, hf₁, ha₁⟩,

  have hb₂ : b₂ ≠ 0, { assume eq, simp * at * },
  have : submodule.span {b₂} > submodule.span ({a} : set α),
    by rw [eq, mul_comm]; from factors_decreasing b₂ b₁ hb₂ h₁,
  rcases ih b₂ this hb₂ with ⟨f₂, hf₂, ha₂⟩,

  refine ⟨f₁ + f₂, _⟩,
  simpa [or_imp_distrib, forall_and_distrib, eq, associated_mul_mul ha₁ ha₂] using and.intro hf₁ hf₂
end

end

lemma is_maximal_ideal_of_irreducible {p : α} (hp : irreducible p) :
  is_maximal_ideal {a | p ∣ a} :=
begin
  letI h : is_ideal {a | p ∣ a} := @is_principal_ideal.to_is_ideal _ _ _ ⟨⟨p, rfl⟩⟩,
  refine is_maximal_ideal.mk _ (assume ⟨q, hq⟩, hp.1 ⟨units.mk_of_mul_eq_one _ q hq.symm, rfl⟩) _,
  assume x T i hT hxp hx,
  rcases (principal T).principal with ⟨q, rfl⟩,
  rcases hT (dvd_refl p) with ⟨c, rfl⟩,
  rcases hp.2 _ _ rfl with ⟨q, rfl⟩ | ⟨c, rfl⟩,
  { exact units.coe_dvd _ _ },
  { simp at hxp hx, exact (hxp hx).elim }
end

lemma prime_of_irreducible {p : α} (hp : irreducible p) : prime p :=
have is_prime_ideal {a | p ∣ a}, from
  @is_maximal_ideal.is_prime_ideal α _ _ (is_maximal_ideal_of_irreducible hp),
⟨assume h, not_irreducible_zero (show irreducible (0:α), from h ▸ hp), hp.1, this.mem_or_mem_of_mul_mem⟩

lemma associates_prime_of_irreducible : ∀{p : associates α}, irreducible p → p.prime :=
associates.forall_associated.2 $ assume a,
begin
  rw [associates.irreducible_mk_iff, associates.prime_mk],
  exact prime_of_irreducible
end

lemma eq_of_prod_eq_associates {s : multiset (associates α)} :
  ∀{t:multiset (associates α)}, (∀a∈s, irreducible a) → (∀a∈t, irreducible a) → s.prod = t.prod →
  s = t :=
begin
  letI := classical.dec_eq (associates α),
  refine s.induction_on _ _,
  { assume t _ ht eq,
    have : ∀a∈t, (a:associates α) = 1, from associates.prod_eq_one_iff.1 eq.symm,
    have : ∀a∈t, irreducible (1 : associates α), from assume a ha, this a ha ▸ ht a ha,
    exact (multiset.eq_zero_of_forall_not_mem $ assume a ha, not_irreducible_one $ this a ha).symm },
  { assume a s ih t hs ht h,
    have ha : a.prime, from associates_prime_of_irreducible (hs a $ multiset.mem_cons_self a s),
    rcases associates.exists_mem_multiset_le_of_prime ha ⟨s.prod, by simpa using h⟩
      with ⟨x, hx, hxa⟩,
    have : x.prime, from associates_prime_of_irreducible (ht x hx),
    have : a = x := (associates.one_or_eq_of_le_of_prime _ _ this hxa).resolve_left ha.2.1,
    subst this,
    have : s.prod = (t.erase a).prod,
    { rw ← multiset.cons_erase hx at h,
      simp at h,
      exact associates.eq_of_mul_eq_mul_left a _ _ ha.1 h },
    have : s = t.erase a, from ih
      (assume x hxs, hs x $ multiset.mem_cons_of_mem hxs)
      (assume x hxt, ht x $ classical.by_cases
        (assume h : x = a, h.symm ▸ hx)
        (assume ne, (multiset.mem_erase_of_ne ne).1 hxt))
      this,
    rw [this, multiset.cons_erase hx] }
end

lemma associated_of_associated_prod_prod {s t : multiset α}
  (hs : ∀a∈s, irreducible a) (ht : ∀a∈t, irreducible a) (h : associated s.prod t.prod) :
  multiset.rel associated s t :=
begin
  refine (associates.rel_associated_iff_map_eq_map.2 $ eq_of_prod_eq_associates _ _ _),
  { assume a ha,
    rcases multiset.mem_map.1 ha with ⟨x, hx, rfl⟩,
    simpa [associates.irreducible_mk_iff] using hs x hx },
  { assume a ha,
    rcases multiset.mem_map.1 ha with ⟨x, hx, rfl⟩,
    simpa [associates.irreducible_mk_iff] using ht x hx },
  rwa [associates.prod_mk, associates.prod_mk, associates.mk_eq_mk_iff_associated]
end

section
local attribute [instance] classical.prop_decidable

noncomputable def factors (a : α) : multiset α :=
if h : a = 0 then ∅ else classical.some (exists_factors a h)

lemma factors_spec (a : α) (h : a ≠ 0) :
  (∀b∈factors a, irreducible b) ∧ associated a (factors a).prod :=
begin
  unfold factors, rw [dif_neg h],
  exact classical.some_spec (exists_factors a h)
end

/-- The unique factorization domain structure given by the principal ideal domain.

This is not added as type class instance, since the `factors` might be computed in a different way.
E.g. factors could return normalized values.
-/
noncomputable def to_unique_factorization_domain : unique_factorization_domain α :=
{ factors := factors,
  factors_prod := assume a ha, associated.symm (factors_spec a ha).2,
  irreducible_factors := assume a ha, (factors_spec a ha).1,
  unique := assume s t, associated_of_associated_prod_prod }

end

end principal_ideal_domain
