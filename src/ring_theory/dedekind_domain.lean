/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import ring_theory.discrete_valuation_ring
import ring_theory.fractional_ideal
import ring_theory.ideal.over

/-!
# Dedekind domains

This file defines the notion of a Dedekind domain (or Dedekind ring),
giving three equivalent definitions (TODO: and shows that they are equivalent).

## Main definitions

 - `is_dedekind_domain` defines a Dedekind domain as a commutative ring that is not a field,
   Noetherian, integrally closed in its field of fractions and has Krull dimension exactly one.
   `is_dedekind_domain_iff` shows that this does not depend on the choice of field of fractions.
 - `is_dedekind_domain_dvr` alternatively defines a Dedekind domain as an integral domain that is not a field,
   Noetherian, and the localization at every nonzero prime ideal is a discrete valuation ring.
 - `is_dedekind_domain_inv` alternatively defines a Dedekind domain as an integral domain that is not a field,
   and every nonzero fractional ideal is invertible.
 - `is_dedekind_domain_inv_iff` shows that this does note depend on the choice of field of fractions.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags

dedekind domain, dedekind ring
-/

variables (R A K : Type*) [comm_ring R] [integral_domain A] [field K]

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def ring.dimension_le_one : Prop :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

open ideal ring

namespace ring

lemma dimension_le_one.principal_ideal_ring
  [is_principal_ideal_ring A] : dimension_le_one A :=
λ p nonzero prime, by { haveI := prime, exact is_prime.to_maximal_ideal nonzero }

lemma dimension_le_one.integral_closure [nontrivial R] [algebra R A]
  (h : dimension_le_one R) : dimension_le_one (integral_closure R A) :=
begin
  intros p ne_bot prime,
  haveI := prime,
  refine integral_closure.is_maximal_of_is_maximal_comap p
    (h _ (integral_closure.comap_ne_bot ne_bot) _),
  apply is_prime.comap
end
end ring

/--
A Dedekind domain is an integral domain that is Noetherian, integrally closed, and
has Krull dimension exactly one (`not_is_field` and `dimension_le_one`).

The integral closure condition is independent of the choice of field of fractions:
use `is_dedekind_domain_iff` to prove `is_dedekind_domain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
class is_dedekind_domain : Prop :=
(not_is_field : ¬ is_field A)
(is_noetherian_ring : is_noetherian_ring A)
(dimension_le_one : dimension_le_one A)
(is_integrally_closed : integral_closure A (fraction_ring A) = ⊥)

/-- An integral domain is a Dedekind domain iff and only if it is not a field, is Noetherian, has dimension ≤ 1,
and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
lemma is_dedekind_domain_iff (f : fraction_map A K) :
  is_dedekind_domain A ↔
    (¬ is_field A) ∧ is_noetherian_ring A ∧ dimension_le_one A ∧
    integral_closure A f.codomain = ⊥ :=
⟨λ ⟨hf, hr, hd, hi⟩, ⟨hf, hr, hd,
  by rw [←integral_closure_map_alg_equiv (fraction_ring.alg_equiv_of_quotient f),
         hi, algebra.map_bot]⟩,
 λ ⟨hf, hr, hd, hi⟩, ⟨hf, hr, hd,
  by rw [←integral_closure_map_alg_equiv (fraction_ring.alg_equiv_of_quotient f).symm,
         hi, algebra.map_bot]⟩⟩

/--
A Dedekind domain is an integral domain that is not a field, is Noetherian, and the localization at
every nonzero prime is a discrete valuation ring.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_dvr : Prop :=
(not_is_field : ¬ is_field A)
(is_noetherian_ring : is_noetherian_ring A)
(is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : ideal A), P.is_prime →
  discrete_valuation_ring (localization.at_prime P))

/--
A Dedekind domain is an integral domain that is not a field such that every fractional ideal has an inverse.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_inv : Prop :=
(not_is_field : ¬ is_field A)
(mul_inv_cancel : ∀ I ≠ (⊥ : fractional_ideal (fraction_ring.of A)), I * I⁻¹ = 1)

section

open ring.fractional_ideal

lemma is_dedekind_domain_inv_iff (f : fraction_map A K) :
  is_dedekind_domain_inv A ↔
    (¬ is_field A) ∧ (∀ I ≠ (⊥ : fractional_ideal f), I * I⁻¹ = 1) :=
begin
  split; rintros ⟨hf, hi⟩; use hf; intros I hI,
  { have := hi (map (fraction_ring.alg_equiv_of_quotient f).symm.to_alg_hom I) (map_ne_zero _ hI),
    erw [← map_inv, ← fractional_ideal.map_mul] at this,
    convert congr_arg (map (fraction_ring.alg_equiv_of_quotient f).to_alg_hom) this;
      simp only [alg_equiv.to_alg_hom_eq_coe, map_symm_map, map_one] },
  { have := hi (map (fraction_ring.alg_equiv_of_quotient f).to_alg_hom I) (map_ne_zero _ hI),
    erw [← map_inv, ← fractional_ideal.map_mul] at this,
    convert congr_arg (map (fraction_ring.alg_equiv_of_quotient f).symm.to_alg_hom) this;
      simp only [alg_equiv.to_alg_hom_eq_coe, map_map_symm, map_one] }
end



/-
Time to break stuff

-/


/-
Might want to pull out some lemmas about the set of ideals that don't contain prime products
-/
lemma ideal_contains_prime_product [is_dedekind_domain A] (I : ideal A) (gt_zero : ⊥ < I) : ∃(pset : multiset $ ideal A), ∅ < pset ∧ pset.prod ≤ I ∧ (∀(P ∈ pset), ideal.is_prime P ∧ ⊥ < P) :=
begin
  classical,
  letI : is_noetherian A A, exact is_dedekind_domain.is_noetherian_ring,
  by_contra hyp,
  push_neg at hyp,
  let S := {J : ideal A | ∀(qset : multiset $ ideal A), ∅ < qset → qset.prod ≤ J → (∃ (P : ideal A), P ∈ qset ∧ (P.is_prime → ¬⊥ < P))},
  have key : S.nonempty,
  {use I, exact hyp },
  rcases set_has_maximal_iff_noetherian.2 _ S key with ⟨M, Mkey, maximal⟩,
  rw set.mem_set_of_eq at Mkey,
  by_cases ne_top : M = ⊤,
  { --basically krull's theorem
    have not_field : ¬ is_field A := by exact is_dedekind_domain.not_is_field,
    rcases ring.not_is_field_iff_exists_prime.1 not_field with ⟨P, ne0, hp⟩,
    have netop := hp.1,
    have bot_lt := bot_lt_iff_ne_bot.mpr ne0,
    rw ne_top at *,
    let qs := ({P} : multiset $ ideal A),
    have h2 : ∅ < qs, exact (∅ : multiset $ ideal A).lt_cons_self P,
    have h3 : qs.prod ≤ ⊤, have blah : qs.prod = P, exact multiset.prod_singleton P, rw blah, exact submodule.comap_subtype_eq_top.mp rfl,
    rcases Mkey qs h2 h3 with ⟨Q, qeq, qkey⟩,
    have blah : Q = P, exact multiset.mem_singleton.1 qeq,
    rw [blah,ne_top] at *,
    apply qkey, assumption', },
  by_cases ne_bot : M = ⊥,
  { have h1 := maximal I, --have that if the maximum of a set of ideals is ⊥, then it only contains ⊥, contra since I < ⊥ and I ∈ A
    have h2 : I ∈ S, simpa,
    rw ne_bot at h1,
    have h4 : ⊥ ≤ I,
    {cases gt_zero, exact gt_zero_left,},
    cases gt_zero,
    have := h1 h2 h4,
    rw this at *, tauto, },
  by_cases non_prime : ideal.is_prime M,
  { have h1 : ({M} : multiset $ ideal A).prod ≤  M,
    suffices h2 : ({M} : multiset $ ideal A).prod = M, rw h2, exact le_refl M,
    exact multiset.prod_singleton M,
    have h3 : ∅ < ({M} : multiset $ ideal A), exact (∅ : multiset $ ideal A).lt_cons_self M,
    rcases Mkey {M} h3 h1 with ⟨P, hp, hp2⟩,
    have := multiset.mem_singleton.1 hp,
    subst this,
    exact hp2 non_prime (bot_lt_iff_ne_bot.mpr ne_bot) },
  unfold ideal.is_prime at non_prime,
  push_neg at non_prime,
  rcases non_prime ne_top with ⟨r, s, hr, hs, hrs⟩,
  clear' non_prime ne_top,
  set rm := M + ideal.span{r} with hrm,
  set sm := M + ideal.span{s} with hrs,
  have h1 : M < rm ∧ M < sm,
  { split; apply submodule.lt_add_iff_not_mem.2; assumption },
  cases h1 with rgt sgt,
  have main : rm*sm ≤ M,
  { simp only [hrm, hrs, left_distrib, right_distrib],
    repeat {rw ideal.add_eq_sup},
    simp only [ideal.mul_le_left, ideal.mul_le_right, sup_le_iff, true_and],
    have := ideal.span_singleton_mul_span_singleton r s,
    rw this, rw ideal.span_le, exact set.singleton_subset_iff.mpr hr },
  have key1 : rm ∉ S,
  { intro rma,
    cases rgt,
    have h1 := maximal rm rma rgt_left,
    have : rm ≠ M, {exfalso, apply rgt_right, rw h1, simp only [set.le_eq_subset] },
    exact this h1, },
  have key2 : sm ∉ S,
  { intro sma,
    cases sgt,
    have h1 := maximal sm sma sgt_left,
    have : sm ≠ M, {exfalso, apply sgt_right, rw h1, simp only [set.le_eq_subset]},
    exact this h1, },
  rw set.mem_set_of_eq at key1, rw set.mem_set_of_eq at key2,
  push_neg at key1, push_neg at key2,
  rcases key1 with ⟨qs1, qpos1, qle1, qprime1⟩,
  rcases key2 with ⟨qs2, qpos2, qle2, qprime2⟩,
  set qs := qs1 + qs2,
  have h1 : ∅ < qs, exact add_pos qpos1 qpos2,
  have h2 : qs.prod ≤ M, simp only [multiset.prod_add], have h' := submodule.mul_le_mul qle1 qle2, exact le_trans h' main,
  rcases Mkey qs h1 h2 with ⟨P, hp, Pkey⟩,
  have h3 : P.is_prime ∧ ⊥ < P, cases multiset.mem_add.mp hp, exact qprime1 P h, exact qprime2 P h,
  cases h3 with h3 h4,
  exact Pkey h3 h4,
  assumption,
end

namespace ring

lemma local1 (S : submonoid R) (f : localization_map S $ localization S) : ∀(I : ideal R), I ≤ comap f.to_ring_hom (map f.to_ring_hom I) :=
begin
  apply le_comap_map,
end

lemma local2 (S : submonoid R) (f : localization_map S $ localization S) (I' : ideal $ localization S) (I : ideal R) (hI' : I'.comap f.to_ring_hom = I) : I' = I.map f.to_ring_hom :=
begin
  rw ← hI',
  symmetry,
  apply localization_map.map_comap f,
end
/-
--https://math.stackexchange.com/questions/110735/why-is-the-localization-of-a-commutative-noetherian-ring-still-noetherian
Sketch for noetherianness : gt in local → gt in original
then well_founded gt in local if well_founded gt in original

-/

--abstract to modules(?)
--better name
-- Every local ideal is of the form S⁻¹I for some ideal I of R.
lemma local_ideal_char (S : submonoid R) (f : localization_map S $ localization S) : ∀(I : ideal f.codomain), ∃(I' : ideal R), ideal.map f.to_ring_hom I' = I :=
  λ (I : ideal f.codomain), Exists.intro (I.comap f.to_ring_hom) (f.map_comap I)

--pull out more lemmas(?)
--better name
lemma local_rel_emb (S : submonoid R) (f : localization_map S $ localization S) : (gt : ideal f.codomain → ideal f.codomain → Prop) ↪r (gt : ideal R → ideal R → Prop) :=
begin
  refine {to_embedding := _, map_rel_iff' := _},
  refine {to_fun := comap f.to_map, inj' := f.order_embedding.inj'},
  dsimp at *,
  intros,
  split,
  {
    intro hab,
    rcases submodule.exists_of_lt hab with ⟨x, hxa, hxb⟩,
    rw [gt_iff_lt, submodule.lt_iff_le_and_exists],
    split,
    exact ideal.comap_mono hab.1,
    rcases f.surj' x with ⟨z,hz⟩,
    use z.1,
    split,
    sorry, --hz z.2 is a unit, x is in a.comap f
    sorry, --hz z.2 is a unit, x is not in b.comap f,
  },
  { simp only [gt_iff_lt],
    intro hab,
    rw submodule.lt_iff_le_and_exists at *,
    rcases hab with ⟨hab, x, hxa, hxb⟩,
    split, rwa [f.order_embedding.map_rel_iff'],
    use f.to_fun x,
    split,
    { have h1 : f.to_fun x ∈ (a.comap f.to_ring_hom).map f.to_ring_hom := by tidy, --avoid tidy
      simpa only [f.map_comap], },
    contrapose! hxb,
    have h1 : f.to_map⁻¹' ({f.to_map x} : _) ≤ b.comap f.to_ring_hom,
    { suffices : ({f.to_map x} : set f.codomain) ≤ b,
    exact set.monotone_preimage this,
    simpa only [set.singleton_subset_iff, set.le_eq_subset],},
    have h2 : x ∈ f.to_map⁻¹' ({f.to_map x} : _) := rfl,
    exact h1 h2,
  }
end

--better name
lemma noetherian_local [is_noetherian_ring R] (S : submonoid R) (f : localization_map S $ localization S) : is_noetherian_ring f.codomain :=
begin
  unfold is_noetherian_ring,
  have a : is_noetherian R R, assumption,
  rw [is_noetherian_iff_well_founded, rel_embedding.well_founded_iff_no_descending_seq] at *,
  contrapose! a,
  cases a,
  --have hh := h.to_embedding.inj',
  --have ha := a.to_embedding.inj',
  --have h1 : (h ∘ a : (gt : ℕ → ℕ → Prop) ↪r (gt : submodule R R → submodule R R → Prop)),
  split,
  exact rel_embedding.trans a (local_rel_emb R S f),
  --use h ∘ a,
  --exact function.injective.comp hh ha,
  --transport infinite chain of ideals of localization along order morphisms to
  --get infinite chain of ideals of original
end


end ring































end
