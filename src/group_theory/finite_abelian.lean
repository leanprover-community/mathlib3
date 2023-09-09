/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import algebra.module.pid
import data.zmod.quotient

/-!
# Structure of finite(ly generated) abelian groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* `add_comm_group.equiv_free_prod_direct_sum_zmod` : Any finitely generated abelian group is the
  product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some prime powers
  `p i ^ e i`.
* `add_comm_group.equiv_direct_sum_zmod_of_fintype` : Any finite abelian group is a direct sum of
  some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.

-/

open_locale direct_sum

universe u

namespace module

variables (M : Type u)

lemma finite_of_fg_torsion [add_comm_group M] [module ℤ M] [module.finite ℤ M]
  (hM : module.is_torsion ℤ M) : _root_.finite M :=
begin
  rcases module.equiv_direct_sum_of_is_torsion hM with ⟨ι, _, p, h, e, ⟨l⟩⟩,
  haveI : ∀ i : ι, ne_zero (p i ^ e i).nat_abs :=
  λ i, ⟨int.nat_abs_ne_zero_of_ne_zero $ pow_ne_zero (e i) (h i).ne_zero⟩,
  haveI : ∀ i : ι, _root_.finite $ ℤ ⧸ submodule.span ℤ {p i ^ e i} :=
  λ i, finite.of_equiv _ (p i ^ e i).quotient_span_equiv_zmod.symm.to_equiv,
  haveI : _root_.finite ⨁ i, ℤ ⧸ (submodule.span ℤ {p i ^ e i} : submodule ℤ ℤ) :=
  finite.of_equiv _ dfinsupp.equiv_fun_on_fintype.symm,
  exact finite.of_equiv _ l.symm.to_equiv
end

end module

variables (G : Type u)

namespace add_comm_group

variable [add_comm_group G]

/-- **Structure theorem of finitely generated abelian groups** : Any finitely generated abelian
group is the product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some
prime powers `p i ^ e i`. -/
theorem equiv_free_prod_direct_sum_zmod [hG : add_group.fg G] :
  ∃ (n : ℕ) (ι : Type) [fintype ι] (p : ι → ℕ) [∀ i, nat.prime $ p i] (e : ι → ℕ),
  nonempty $ G ≃+ (fin n →₀ ℤ) × ⨁ (i : ι), zmod (p i ^ e i) :=
begin
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ :=
    @module.equiv_free_prod_direct_sum _ _ _ _ _ _ _ (module.finite.iff_add_group_fg.mpr hG),
  refine ⟨n, ι, fι, λ i, (p i).nat_abs, λ i, _, e, ⟨_⟩⟩,
  { rw [← int.prime_iff_nat_abs_prime, ← gcd_monoid.irreducible_iff_prime], exact hp i },
  exact f.to_add_equiv.trans ((add_equiv.refl _).prod_congr $ dfinsupp.map_range.add_equiv $
    λ i, ((int.quotient_span_equiv_zmod _).trans $
      zmod.ring_equiv_congr $ (p i).nat_abs_pow _).to_add_equiv)
end

/-- **Structure theorem of finite abelian groups** : Any finite abelian group is a direct sum of
some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`. -/
theorem equiv_direct_sum_zmod_of_fintype [finite G] :
  ∃ (ι : Type) [fintype ι] (p : ι → ℕ) [∀ i, nat.prime $ p i] (e : ι → ℕ),
  nonempty $ G ≃+ ⨁ (i : ι), zmod (p i ^ e i) :=
begin
  casesI nonempty_fintype G,
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := equiv_free_prod_direct_sum_zmod G,
  cases n,
  { exact ⟨ι, fι, p, hp, e, ⟨f.trans add_equiv.unique_prod⟩⟩ },
  { haveI := @fintype.prod_left _ _ _ (fintype.of_equiv G f.to_equiv) _,
    exact (fintype.of_surjective (λ f : fin n.succ →₀ ℤ, f 0) $
      λ a, ⟨finsupp.single 0 a, finsupp.single_eq_same⟩).false.elim }
end

lemma finite_of_fg_torsion [hG' : add_group.fg G] (hG : add_monoid.is_torsion G) : finite G :=
@module.finite_of_fg_torsion _ _ _ (module.finite.iff_add_group_fg.mpr hG') $
  add_monoid.is_torsion_iff_is_torsion_int.mp hG

end add_comm_group

namespace comm_group

lemma finite_of_fg_torsion [comm_group G] [group.fg G] (hG : monoid.is_torsion G) : finite G :=
@finite.of_equiv _ _ (add_comm_group.finite_of_fg_torsion (additive G) hG) multiplicative.of_add

end comm_group
