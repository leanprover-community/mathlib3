import ring_theory.principal_ideal_domain
import algebra.direct_sum.module
import ring_theory.finiteness
import algebra.module.torsion

universes u v
--variables [Π p : Prop, decidable p]
open_locale classical

section coprime
end coprime

section pid
open_locale direct_sum
open_locale big_operators
open submodule
open dfinsupp

variables {R : Type u} [comm_ring R] [is_domain R] [is_principal_ideal_ring R]
  {M : Type v} [add_comm_group M] [module R M]

noncomputable instance i : gcd_monoid R := unique_factorization_monoid.to_gcd_monoid _

/-lemma torsion_independent' {ι : Type*} [fintype ι] (p : ι → R)
  (hp : ∀ i, is_coprime (p i) (∏ j in {i}ᶜ, (p j))) :
  complete_lattice.independent (λ i, torsion R M (p i)) := λ i,
begin
  dsimp, rw [disjoint_iff, eq_bot_iff], intros x hx,
  rw submodule.mem_inf at hx, obtain ⟨hxi, hxj⟩ := hx,
  have hxi : p i • x = 0 := hxi,
  rw mem_supr_iff_exists_dfinsupp' at hxj, cases hxj with f hf,
  obtain ⟨b, c, h1⟩ := hp i,
  rw [mem_bot, ← one_smul _ x, ← h1, add_smul],
  convert (zero_add (0:M)),
  { rw [mul_smul, hxi, smul_zero] },
  { rw [← hf, smul_sum, sum_eq_zero],
    intro j, by_cases hj : j = i,
    { convert smul_zero _,
      rw ← mem_bot _, convert coe_mem (f j),
      symmetry, rw supr_eq_bot, intro hj',
      exfalso, exact hj' hj },
    { have hj : j ∈ ({i} : finset ι)ᶜ,
      { rw finset.mem_compl, intro hj', apply hj, rw ← finset.mem_singleton, exact hj' },
      rw [finset.prod_eq_prod_diff_singleton_mul hj, ← mul_assoc, mul_smul],
      have : (⨆ (H : ¬j = i), torsion R M (p j)) ≤ torsion R M (p j) := supr_const_le,
      have : (f j : M) ∈ torsion R M (p j) := this (coe_mem _),
      have : p j • (f j : M) = 0 := this,
      rw [this, smul_zero] } }
end

lemma torsion_independent {ι : Type*} [fintype ι] (p : ι → R) (hp : pairwise (is_coprime on p)) :
  complete_lattice.independent (λ i, torsion R M (p i)) := sorry -- timeout ??
--torsion_independent' p (pairwise_coprime_iff_coprime_prod.mp hp)-/

lemma coprime_of_irreducible_pow {ι : Type*} [fintype ι] (p : ι → R)
  (irred : ∀ i, irreducible (p i)) (assoc : ∀ i j, associated (p i) (p j) → i = j)
  (e : ι → ℕ) : pairwise (is_coprime on λ i, p i ^ e i) :=
λ i j h, ((irred i).coprime_iff_not_dvd.mpr
  (λ h', h (assoc _ _ ((irred i).associated_of_dvd (irred j) h')))).pow_left.pow_right


theorem prime_power_torsion_generators [module.finite R M] (hM : torsion' R M = ⊤) :
  ∃ (ι : Type u) [fintype ι] (p : ι → R) [∀ i, irreducible (p i)] (e : ι → ℕ),
  direct_sum.submodule_is_internal (λ i, torsion R M ((p i) ^ e i)) :=
begin
  cases (module.finite_def.mp (by apply_instance) : (⊤ : submodule R M).fg) with S h,
  have all_torsion := λ x, begin have hx : x ∈ ⊤ := mem_top, rw ← hM at hx, exact hx end,
  let P : multiset (associates R) :=
    S.val.bind (λ s, multiset.map associates.mk $
      principal_ideal_ring.factors ↑(classical.some (all_torsion s))),
  let ι : Type u := P.to_finset,
  haveI : fintype ι := fintype.of_finset P.to_finset (λ x, iff.rfl),
  let p : ι → R := λ i, classical.some $ associates.mk_surjective i,
  have hp : ∀ i, associates.mk (p i) = i := λ i, classical.some_spec $ associates.mk_surjective ↑i,
  have irred : ∀ i, irreducible (p i) := λ i, begin
    have hi := i.prop, rw [multiset.mem_to_finset, multiset.mem_bind] at hi,
    obtain ⟨s, hs, hi⟩ := hi, rw multiset.mem_map at hi, obtain ⟨q, hq, hi⟩ := hi,
    rw [← associates.irreducible_mk, hp i, ← hi, associates.irreducible_mk],
    apply (principal_ideal_ring.factors_spec _ _).left _ hq,
    exact non_zero_divisors.coe_ne_zero _
  end,
  refine ⟨ι, by apply_instance, p, irred, λ i, P.count i, _⟩,
  have coprime : pairwise (is_coprime on λ i, p i ^ P.count i) :=
    coprime_of_irreducible_pow _ irred (λ i j assoc, subtype.coe_injective
      (by { rw [← hp, ← hp, associates.mk_eq_mk_iff_associated], exact assoc })) _,
  apply torsion_is_internal coprime,
  rw [eq_top_iff, ← h, span_le], intros s hs, rw set_like.mem_coe,
  refine torsion_le_torsion_of_dvd ↑_ _ _ (classical.some_spec (all_torsion s)), sorry
end

end pid

/-  have fg : (torsion' R M).fg :=
    is_noetherian_def.mp (is_noetherian_of_fg_of_noetherian' (module.finite_def.mp _)) _,
  { cases fg with S h,
    classical,
    let P := S.val.bind (λ s, factors $ begin
      by_cases hs : s ∈ torsion' R M,
      { exact classical.some hs },
      { exact 0 } --irrelevant value
    end),
    use P.to_finset,
    split, split,
    { intro p,
      cases p with p hp,
      rw [mem_to_finset, mem_bind] at hp,
      cases hp with s hp, cases hp with hs hp,
      apply (factors_spec _ _).left _ hp,
      split_ifs with h1,
      { exact (classical.some_spec h1).right },
      { exfalso, apply h1,
        rw ← h, exact submodule.subset_span hs } },
    { use λ p, count (p:R) P,
      sorry },
    { apply_instance } },
  apply_instance -/
