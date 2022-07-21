/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import algebra.module.pid
import data.zmod.quotient

/-!
# Structure of finite(ly generated) abelian groups

* `add_comm_group.equiv_free_prod_direct_sum_zmod` : Any finitely generated abelian group is the
  product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some prime powers
  `p i ^ e i`.
* `add_comm_group.equiv_direct_sum_zmod_of_fintype` : Any finite abelian group is a direct sum of
  some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.

-/

open_locale direct_sum

namespace module

open_locale classical

/-- A finitely generated torsion `ℤ`-module is finite. -/
noncomputable def fintype_of_fg_torsion (G : Type*) [add_comm_group G] [module ℤ G]
  [module.finite ℤ G] (hit : module.is_torsion ℤ G) : fintype G :=
let hG := (module.equiv_direct_sum_of_is_torsion hit).some_spec in
@fintype.of_equiv _ _
  (@fintype.of_equiv _ _
    (@pi.fintype _ _ _ hG.some $ λ i,
      @fintype.of_equiv _ _
        (@zmod.fintype _
          ⟨int.nat_abs_pos_of_ne_zero $ pow_ne_zero (hG.some_spec.some_spec.some_spec.some i) $
            irreducible.ne_zero $ hG.some_spec.some_spec.some i⟩)
        (int.quotient_span_equiv_zmod _).symm.to_equiv)
    (@dfinsupp.equiv_fun_on_fintype _ _ _ hG.some).symm)
  hG.some_spec.some_spec.some_spec.some_spec.some.symm.to_equiv

end module

namespace add_comm_group

/-- **Structure theorem of finitely generated abelian groups** : Any finitely generated abelian
group is the product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some
prime powers `p i ^ e i`.-/
theorem equiv_free_prod_direct_sum_zmod (G : Type*) [add_comm_group G] [hG : add_group.fg G] :
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
some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.-/
theorem equiv_direct_sum_zmod_of_fintype (G : Type*) [add_comm_group G] [fintype G] :
  ∃ (ι : Type) [fintype ι] (p : ι → ℕ) [∀ i, nat.prime $ p i] (e : ι → ℕ),
  nonempty $ G ≃+ ⨁ (i : ι), zmod (p i ^ e i) :=
begin
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := equiv_free_prod_direct_sum_zmod G,
  cases n,
  { exact ⟨ι, fι, p, hp, e, ⟨f.trans add_equiv.unique_prod⟩⟩ },
  { haveI := @fintype.prod_left _ _ _ (fintype.of_equiv G f.to_equiv) _,
    exact (fintype.of_surjective (λ f : fin n.succ →₀ ℤ, f 0) $
      λ a, ⟨finsupp.single 0 a, finsupp.single_eq_same⟩).false.elim }
end

/-- A finitely generated torsion abelian additive group is finite. -/
noncomputable def fintype_of_fg_torsion (G : Type*) [add_comm_group G] [hfg : add_group.fg G]
  (hit : add_monoid.is_torsion G) : fintype G :=
@module.fintype_of_fg_torsion _ _ _
  (module.finite.iff_add_group_fg.mpr $ add_group.fg_iff_add_monoid.fg.mpr $
    add_group.fg_iff_add_monoid.fg.mp hfg) $
  add_monoid.is_torsion_iff_is_torsion_int.mp hit

end add_comm_group

namespace comm_group

/-- A finitely generated torsion abelian multiplicative group is finite. -/
noncomputable def fintype_of_fg_torsion (G : Type*) [comm_group G] [group.fg G]
  (hG : monoid.is_torsion G) : fintype G :=
@fintype.of_equiv _ _ (add_comm_group.fintype_of_fg_torsion (additive G) hG) multiplicative.of_add

end comm_group
