/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import algebra.direct_sum.module
import linear_algebra.isomorphisms
import group_theory.torsion
import ring_theory.coprime.ideal
import ring_theory.finiteness

/-!
# Torsion submodules

## Main definitions

* `torsion_of R M x` : the torsion ideal of `x`, containing all `a` such that `a • x = 0`.
* `submodule.torsion_by R M a` : the `a`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0`.
* `submodule.torsion_by_set R M s` : the submodule containing all elements `x` of `M` such that
  `a • x = 0` for all `a` in `s`.
* `submodule.torsion' R M S` : the `S`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0` for some `a` in `S`.
* `submodule.torsion R M` : the torsion submoule, containing all elements `x` of `M` such that
  `a • x = 0` for some non-zero-divisor `a` in `R`.
* `module.is_torsion_by R M a` : the property that defines a `a`-torsion module. Similarly,
  `is_torsion_by_set`, `is_torsion'` and `is_torsion`.
* `module.is_torsion_by_set.module` : Creates a `R ⧸ I`-module from a `R`-module that
  `is_torsion_by_set R _ I`.

## Main statements

* `quot_torsion_of_equiv_span_singleton` : isomorphism between the span of an element of `M` and
  the quotient by its torsion ideal.
* `torsion' R M S` and `torsion R M` are submodules.
* `torsion_by_set_eq_torsion_by_span` : torsion by a set is torsion by the ideal generated by it.
* `submodule.torsion_by_is_torsion_by` : the `a`-torsion submodule is a `a`-torsion module.
  Similar lemmas for `torsion'` and `torsion`.
* `submodule.torsion_by_is_internal` : a `∏ i, p i`-torsion module is the internal direct sum of its
  `p i`-torsion submodules when the `p i` are pairwise coprime. A more general version with coprime
  ideals is `submodule.torsion_by_set_is_internal`.
* `submodule.no_zero_smul_divisors_iff_torsion_bot` : a module over a domain has
  `no_zero_smul_divisors` (that is, there is no non-zero `a`, `x` such that `a • x = 0`)
  iff its torsion submodule is trivial.
* `submodule.quotient_torsion.torsion_eq_bot` : quotienting by the torsion submodule makes the
  torsion submodule of the new module trivial. If `R` is a domain, we can derive an instance
  `submodule.quotient_torsion.no_zero_smul_divisors : no_zero_smul_divisors R (M ⧸ torsion R M)`.

## Notation

* The notions are defined for a `comm_semiring R` and a `module R M`. Some additional hypotheses on
  `R` and `M` are required by some lemmas.
* The letters `a`, `b`, ... are used for scalars (in `R`), while `x`, `y`, ... are used for vectors
  (in `M`).

## Tags

Torsion, submodule, module, quotient
-/

namespace ideal

section torsion_of

variables (R M : Type*) [semiring R] [add_comm_monoid M] [module R M]

/--The torsion ideal of `x`, containing all `a` such that `a • x = 0`.-/
@[simps] def torsion_of (x : M) : ideal R := (linear_map.to_span_singleton R M x).ker

@[simp] lemma torsion_of_zero : torsion_of R M (0 : M) = ⊤ := by simp [torsion_of]

variables {R M}

@[simp] lemma mem_torsion_of_iff (x : M) (a : R) : a ∈ torsion_of R M x ↔ a • x = 0 := iff.rfl

variables (R)

@[simp] lemma torsion_of_eq_top_iff (m : M) : torsion_of R M m = ⊤ ↔ m = 0 :=
begin
  refine ⟨λ h, _, λ h, by simp [h]⟩,
  rw [← one_smul R m, ← mem_torsion_of_iff m (1 : R), h],
  exact submodule.mem_top,
end

@[simp] lemma torsion_of_eq_bot_iff_of_no_zero_smul_divisors
  [nontrivial R] [no_zero_smul_divisors R M] (m : M) :
  torsion_of R M m = ⊥ ↔ m ≠ 0 :=
begin
  refine ⟨λ h contra, _, λ h, (submodule.eq_bot_iff _).mpr $ λ r hr, _⟩,
  { rw [contra, torsion_of_zero] at h,
    exact bot_ne_top.symm h, },
  { rw [mem_torsion_of_iff, smul_eq_zero] at hr,
    tauto, },
end

/-- See also `complete_lattice.independent.linear_independent` which provides the same conclusion
but requires the stronger hypothesis `no_zero_smul_divisors R M`. -/
lemma complete_lattice.independent.linear_independent' {ι R M : Type*} {v : ι → M}
  [ring R] [add_comm_group M] [module R M]
  (hv : complete_lattice.independent $ λ i, (R ∙ v i))
  (h_ne_zero : ∀ i, ideal.torsion_of R M (v i) = ⊥) :
  linear_independent R v :=
begin
  refine linear_independent_iff_not_smul_mem_span.mpr (λ i r hi, _),
  replace hv := complete_lattice.independent_def.mp hv i,
  simp only [supr_subtype', ← submodule.span_range_eq_supr, disjoint_iff] at hv,
  have : r • v i ∈ ⊥,
  { rw [← hv, submodule.mem_inf],
    refine ⟨submodule.mem_span_singleton.mpr ⟨r, rfl⟩, _⟩,
    convert hi,
    ext,
    simp, },
  rw [← submodule.mem_bot R, ← h_ne_zero i],
  simpa using this,
end

end torsion_of

section
variables (R M : Type*) [ring R] [add_comm_group M] [module R M]
/--The span of `x` in `M` is isomorphic to `R` quotiented by the torsion ideal of `x`.-/
noncomputable def quot_torsion_of_equiv_span_singleton (x : M) :
  (R ⧸ torsion_of R M x) ≃ₗ[R] (R ∙ x) :=
(linear_map.to_span_singleton R M x).quot_ker_equiv_range.trans $
linear_equiv.of_eq _ _ (linear_map.span_singleton_eq_range R M x).symm

variables {R M}
@[simp] lemma quot_torsion_of_equiv_span_singleton_apply_mk (x : M) (a : R) :
  quot_torsion_of_equiv_span_singleton R M x (submodule.quotient.mk a) =
    a • ⟨x, submodule.mem_span_singleton_self x⟩ := rfl
end
end ideal

open_locale non_zero_divisors

section defs

variables (R M : Type*) [comm_semiring R] [add_comm_monoid M] [module R M]

namespace submodule

/-- The `a`-torsion submodule for `a` in `R`, containing all elements `x` of `M` such that
  `a • x = 0`. -/
@[simps] def torsion_by (a : R) : submodule R M := (distrib_mul_action.to_linear_map _ _ a).ker

/-- The submodule containing all elements `x` of `M` such that `a • x = 0` for all `a` in `s`. -/
@[simps] def torsion_by_set (s : set R) : submodule R M := Inf (torsion_by R M '' s)

/-- The `S`-torsion submodule, containing all elements `x` of `M` such that `a • x = 0` for some
`a` in `S`. -/
@[simps] def torsion' (S : Type*)
  [comm_monoid S] [distrib_mul_action S M] [smul_comm_class S R M] :
  submodule R M :=
{ carrier := { x | ∃ a : S, a • x = 0 },
  zero_mem' := ⟨1, smul_zero _⟩,
  add_mem' := λ x y ⟨a, hx⟩ ⟨b, hy⟩,
    ⟨b * a,
      by rw [smul_add, mul_smul, mul_comm, mul_smul, hx, hy, smul_zero, smul_zero, add_zero]⟩,
  smul_mem' := λ a x ⟨b, h⟩, ⟨b, by rw [smul_comm, h, smul_zero]⟩ }

/-- The torsion submodule, containing all elements `x` of `M` such that  `a • x = 0` for some
  non-zero-divisor `a` in `R`. -/
@[reducible] def torsion := torsion' R M R⁰

end submodule

namespace module

/-- A `a`-torsion module is a module where every element is `a`-torsion. -/
@[reducible] def is_torsion_by (a : R) := ∀ ⦃x : M⦄, a • x = 0

/-- A module where every element is `a`-torsion for all `a` in `s`. -/
@[reducible] def is_torsion_by_set (s : set R) := ∀ ⦃x : M⦄ ⦃a : s⦄, (a : R) • x = 0

/-- A `S`-torsion module is a module where every element is `a`-torsion for some `a` in `S`. -/
@[reducible] def is_torsion' (S : Type*) [has_smul S M] := ∀ ⦃x : M⦄, ∃ a : S, a • x = 0

/-- A torsion module is a module where every element is `a`-torsion for some non-zero-divisor `a`.
-/
@[reducible] def is_torsion := ∀ ⦃x : M⦄, ∃ a : R⁰, a • x = 0

end module

end defs

variables {R M : Type*}

section
variables [comm_semiring R] [add_comm_monoid M] [module R M] (s : set R) (a : R)

namespace submodule

@[simp] lemma smul_torsion_by (x : torsion_by R M a) : a • x = 0 := subtype.ext x.prop
@[simp] lemma smul_coe_torsion_by (x : torsion_by R M a) : a • (x : M) = 0 := x.prop
@[simp] lemma mem_torsion_by_iff (x : M) : x ∈ torsion_by R M a ↔ a • x = 0 := iff.rfl

@[simp] lemma mem_torsion_by_set_iff (x : M) :
  x ∈ torsion_by_set R M s ↔ ∀ a : s, (a : R) • x = 0 :=
begin
  refine ⟨λ h ⟨a, ha⟩, mem_Inf.mp h _ (set.mem_image_of_mem _ ha), λ h, mem_Inf.mpr _⟩,
  rintro _ ⟨a, ha, rfl⟩, exact h ⟨a, ha⟩
end

@[simp] lemma torsion_by_singleton_eq : torsion_by_set R M {a} = torsion_by R M a :=
begin
  ext x,
  simp only [mem_torsion_by_set_iff, set_coe.forall, subtype.coe_mk, set.mem_singleton_iff,
    forall_eq, mem_torsion_by_iff]
end

lemma torsion_by_set_le_torsion_by_set_of_subset {s t : set R} (st : s ⊆ t) :
  torsion_by_set R M t ≤ torsion_by_set R M s :=
Inf_le_Inf $ λ _ ⟨a, ha, h⟩, ⟨a, st ha, h⟩

/-- Torsion by a set is torsion by the ideal generated by it. -/
lemma torsion_by_set_eq_torsion_by_span :
  torsion_by_set R M s = torsion_by_set R M (ideal.span s) :=
begin
  refine le_antisymm (λ x hx, _) (torsion_by_set_le_torsion_by_set_of_subset subset_span),
  rw mem_torsion_by_set_iff at hx ⊢,
  suffices : ideal.span s ≤ ideal.torsion_of R M x,
  { rintro ⟨a, ha⟩, exact this ha },
  rw ideal.span_le, exact λ a ha, hx ⟨a, ha⟩
end

lemma torsion_by_span_singleton_eq : torsion_by_set R M (R ∙ a) = torsion_by R M a :=
((torsion_by_set_eq_torsion_by_span _).symm.trans $ torsion_by_singleton_eq _)

lemma torsion_by_le_torsion_by_of_dvd (a b : R) (dvd : a ∣ b) :
  torsion_by R M a ≤ torsion_by R M b :=
begin
  rw [← torsion_by_span_singleton_eq, ← torsion_by_singleton_eq],
  apply torsion_by_set_le_torsion_by_set_of_subset,
  rintro c (rfl : c = b), exact ideal.mem_span_singleton.mpr dvd
end

@[simp] lemma torsion_by_one : torsion_by R M 1 = ⊥ :=
eq_bot_iff.mpr (λ _ h, by { rw [mem_torsion_by_iff, one_smul] at h, exact h })
@[simp] lemma torsion_by_univ : torsion_by_set R M set.univ = ⊥ :=
by { rw [eq_bot_iff, ← torsion_by_one, ← torsion_by_singleton_eq],
  exact torsion_by_set_le_torsion_by_set_of_subset (λ _ _, trivial) }

end submodule
open submodule
namespace module

@[simp] lemma is_torsion_by_singleton_iff : is_torsion_by_set R M {a} ↔ is_torsion_by R M a :=
begin
  refine ⟨λ h x, @h _ ⟨_, set.mem_singleton _⟩, λ h x, _⟩,
  rintro ⟨b, rfl : b = a⟩, exact @h _
end

lemma is_torsion_by_set_iff_torsion_by_set_eq_top :
  is_torsion_by_set R M s ↔ submodule.torsion_by_set R M s = ⊤ :=
⟨λ h, eq_top_iff.mpr (λ _ _, (mem_torsion_by_set_iff _ _).mpr $ @h _),
  λ h x, by { rw [← mem_torsion_by_set_iff, h], trivial }⟩

/-- A `a`-torsion module is a module whose `a`-torsion submodule is the full space. -/
lemma is_torsion_by_iff_torsion_by_eq_top : is_torsion_by R M a ↔ torsion_by R M a = ⊤ :=
by rw [← torsion_by_singleton_eq, ← is_torsion_by_singleton_iff,
  is_torsion_by_set_iff_torsion_by_set_eq_top]

lemma is_torsion_by_set_iff_is_torsion_by_span :
  is_torsion_by_set R M s ↔ is_torsion_by_set R M (ideal.span s) :=
by rw [is_torsion_by_set_iff_torsion_by_set_eq_top, is_torsion_by_set_iff_torsion_by_set_eq_top,
  torsion_by_set_eq_torsion_by_span]

lemma is_torsion_by_span_singleton_iff : is_torsion_by_set R M (R ∙ a) ↔ is_torsion_by R M a :=
((is_torsion_by_set_iff_is_torsion_by_span _).symm.trans $ is_torsion_by_singleton_iff _)

end module
namespace submodule
open module

lemma torsion_by_set_is_torsion_by_set : is_torsion_by_set R (torsion_by_set R M s) s :=
λ ⟨x, hx⟩ a, subtype.ext $ (mem_torsion_by_set_iff _ _).mp hx a

/-- The `a`-torsion submodule is a `a`-torsion module. -/
lemma torsion_by_is_torsion_by : is_torsion_by R (torsion_by R M a) a := λ _, smul_torsion_by _ _

@[simp] lemma torsion_by_torsion_by_eq_top : torsion_by R (torsion_by R M a) a = ⊤ :=
(is_torsion_by_iff_torsion_by_eq_top a).mp $ torsion_by_is_torsion_by a
@[simp] lemma torsion_by_set_torsion_by_set_eq_top :
  torsion_by_set R (torsion_by_set R M s) s = ⊤ :=
(is_torsion_by_set_iff_torsion_by_set_eq_top s).mp $ torsion_by_set_is_torsion_by_set s

variables (R M)
lemma torsion_gc : @galois_connection (submodule R M) (ideal R)ᵒᵈ _ _
  annihilator (λ I, torsion_by_set R M $ I.of_dual) :=
λ A I, ⟨λ h x hx, (mem_torsion_by_set_iff _ _).mpr $ λ ⟨a, ha⟩, mem_annihilator.mp (h ha) x hx,
  λ h a ha, mem_annihilator.mpr $ λ x hx, (mem_torsion_by_set_iff _ _).mp (h hx) ⟨a, ha⟩⟩

variables {R M}
section coprime
open_locale big_operators
variables {ι : Type*} {p : ι → ideal R} {S : finset ι}
variables (hp : (S : set ι).pairwise $ λ i j, p i ⊔ p j = ⊤)
include hp

lemma supr_torsion_by_ideal_eq_torsion_by_infi :
  (⨆ i ∈ S, torsion_by_set R M $ p i) = torsion_by_set R M ↑(⨅ i ∈ S, p i) :=
begin
  cases S.eq_empty_or_nonempty with h h,
  { rw h, convert supr_emptyset, convert torsion_by_univ, convert top_coe, exact infi_emptyset },
  apply le_antisymm,
  { apply supr_le _, intro i, apply supr_le _, intro is,
    apply torsion_by_set_le_torsion_by_set_of_subset,
    exact (infi_le (λ i, ⨅ (H : i ∈ S), p i) i).trans (infi_le _ is), },
  { intros x hx,
    rw mem_supr_finset_iff_exists_sum,
    obtain ⟨μ, hμ⟩ := (mem_supr_finset_iff_exists_sum _ _).mp
      ((ideal.eq_top_iff_one _).mp $ (ideal.supr_infi_eq_top_iff_pairwise h _).mpr hp),
    refine ⟨λ i, ⟨(μ i : R) • x, _⟩, _⟩,
    { rw mem_torsion_by_set_iff at hx ⊢,
      rintro ⟨a, ha⟩, rw smul_smul,
      suffices : a * μ i ∈ ⨅ i ∈ S, p i, from hx ⟨_, this⟩,
      rw mem_infi, intro j, rw mem_infi, intro hj,
      by_cases ij : j = i,
      { rw ij, exact ideal.mul_mem_right _ _ ha },
      { have := coe_mem (μ i), simp only [mem_infi] at this,
        exact ideal.mul_mem_left _ _ (this j hj ij) } },
    { simp_rw coe_mk, rw [← finset.sum_smul, hμ, one_smul] } }
end

lemma sup_indep_torsion_by_ideal : S.sup_indep (λ i, torsion_by_set R M $ p i) :=
λ T hT i hi hiT, begin
  rw [disjoint_iff, finset.sup_eq_supr,
    supr_torsion_by_ideal_eq_torsion_by_infi $ λ i hi j hj ij, hp (hT hi) (hT hj) ij],
  have := @galois_connection.u_inf _ _ (order_dual.to_dual _) (order_dual.to_dual _) _ _ _ _
    (torsion_gc R M), dsimp at this ⊢,
  rw [← this, ideal.sup_infi_eq_top, top_coe, torsion_by_univ],
  intros j hj, apply hp hi (hT hj), rintro rfl, exact hiT hj
end

omit hp
variables {q : ι → R} (hq : (S : set ι).pairwise $ is_coprime on q)
include hq

lemma supr_torsion_by_eq_torsion_by_prod :
  (⨆ i ∈ S, torsion_by R M $ q i) = torsion_by R M (∏ i in S, q i) :=
begin
  rw [← torsion_by_span_singleton_eq, ideal.submodule_span_eq,
    ← ideal.finset_inf_span_singleton _ _ hq, finset.inf_eq_infi,
    ← supr_torsion_by_ideal_eq_torsion_by_infi],
  { congr, ext : 1, congr, ext : 1, exact (torsion_by_span_singleton_eq _).symm },
  { exact λ i hi j hj ij, (ideal.sup_eq_top_iff_is_coprime _ _).mpr (hq hi hj ij), }
end

lemma sup_indep_torsion_by : S.sup_indep (λ i, torsion_by R M $ q i) :=
begin
  convert sup_indep_torsion_by_ideal
    (λ i hi j hj ij, (ideal.sup_eq_top_iff_is_coprime (q i) _).mpr $ hq hi hj ij),
  ext : 1, exact (torsion_by_span_singleton_eq _).symm,
end

end coprime
end submodule
end

section needs_group
variables [comm_ring R] [add_comm_group M] [module R M]

namespace submodule
open_locale big_operators
variables {ι : Type*} [decidable_eq ι] {S : finset ι}

/--If the `p i` are pairwise coprime, a `⨅ i, p i`-torsion module is the internal direct sum of
its `p i`-torsion submodules.-/
lemma torsion_by_set_is_internal {p : ι → ideal R}
  (hp : (S : set ι).pairwise $ λ i j, p i ⊔ p j = ⊤)
  (hM : module.is_torsion_by_set R M (⨅ i ∈ S, p i : ideal R)) :
  direct_sum.is_internal (λ i : S, torsion_by_set R M $ p i) :=
direct_sum.is_internal_submodule_of_independent_of_supr_eq_top
  (complete_lattice.independent_iff_sup_indep.mpr $ sup_indep_torsion_by_ideal hp)
  ((supr_subtype'' ↑S $ λ i, torsion_by_set R M $ p i).trans $
    (supr_torsion_by_ideal_eq_torsion_by_infi hp).trans $
    (module.is_torsion_by_set_iff_torsion_by_set_eq_top _).mp hM)

/--If the `q i` are pairwise coprime, a `∏ i, q i`-torsion module is the internal direct sum of
its `q i`-torsion submodules.-/
lemma torsion_by_is_internal {q : ι → R} (hq : (S : set ι).pairwise $ is_coprime on q)
  (hM : module.is_torsion_by R M $ ∏ i in S, q i) :
  direct_sum.is_internal (λ i : S, torsion_by R M $ q i) :=
begin
  rw [← module.is_torsion_by_span_singleton_iff, ideal.submodule_span_eq,
    ← ideal.finset_inf_span_singleton _ _ hq, finset.inf_eq_infi] at hM,
  convert torsion_by_set_is_internal
    (λ i hi j hj ij, (ideal.sup_eq_top_iff_is_coprime (q i) _).mpr $ hq hi hj ij) hM,
  ext : 1, exact (torsion_by_span_singleton_eq _).symm,
end

end submodule

namespace module
variables {I : ideal R} (hM : is_torsion_by_set R M I)
include hM

/-- can't be an instance because hM can't be inferred -/
def is_torsion_by_set.has_smul : has_smul (R ⧸ I) M :=
{ smul := λ b x, quotient.lift_on' b (• x) $ λ b₁ b₂ h, begin
    show b₁ • x = b₂ • x,
    have : (-b₁ + b₂) • x = 0 := @hM x ⟨_, quotient_add_group.left_rel_apply.mp h⟩,
    rw [add_smul, neg_smul, neg_add_eq_zero] at this,
    exact this
  end }

@[simp] lemma is_torsion_by_set.mk_smul (b : R) (x : M) :
  by haveI := hM.has_smul; exact ideal.quotient.mk I b • x = b • x := rfl

/-- A `(R ⧸ I)`-module is a `R`-module which `is_torsion_by_set R M I`. -/
def is_torsion_by_set.module : module (R ⧸ I) M :=
@function.surjective.module_left _ _ _ _ _ _ _ hM.has_smul
  _ ideal.quotient.mk_surjective (is_torsion_by_set.mk_smul hM)

instance is_torsion_by_set.smul_assoc_class {S : Type*} [has_smul S R] [has_smul S M]
  [smul_assoc_class S R M] [smul_assoc_class S R R] :
  @@smul_assoc_class S (R ⧸ I) M _ (is_torsion_by_set.module hM).to_has_smul _ :=
{ smul_assoc := λ b d x, quotient.induction_on' d $ λ c, (smul_assoc b c x : _) }

omit hM

instance : module (R ⧸ I) (M ⧸ I • (⊤ : submodule R M)) :=
is_torsion_by_set.module (λ x r, begin
  induction x using quotient.induction_on,
  refine (submodule.quotient.mk_eq_zero _).mpr (submodule.smul_mem_smul r.prop _),
  trivial,
end)

end module

namespace submodule

instance (I : ideal R) : module (R ⧸ I) (torsion_by_set R M I) :=
module.is_torsion_by_set.module $ torsion_by_set_is_torsion_by_set I

@[simp] lemma torsion_by_set.mk_smul (I : ideal R) (b : R) (x : torsion_by_set R M I) :
  ideal.quotient.mk I b • x = b • x := rfl

instance (I : ideal R) {S : Type*} [has_smul S R] [has_smul S M]
  [smul_assoc_class S R M] [smul_assoc_class S R R] :
  smul_assoc_class S (R ⧸ I) (torsion_by_set R M I) :=
infer_instance

/-- The `a`-torsion submodule as a `(R ⧸ R∙a)`-module. -/
instance (a : R) : module (R ⧸ R ∙ a) (torsion_by R M a) :=
module.is_torsion_by_set.module $
  (module.is_torsion_by_span_singleton_iff a).mpr $ torsion_by_is_torsion_by a

@[simp] lemma torsion_by.mk_smul (a b : R) (x : torsion_by R M a) :
  ideal.quotient.mk (R ∙ a) b • x = b • x := rfl

instance (a : R) {S : Type*} [has_smul S R] [has_smul S M]
  [smul_assoc_class S R M] [smul_assoc_class S R R] :
  smul_assoc_class S (R ⧸ R ∙ a) (torsion_by R M a) :=
infer_instance

end submodule
end needs_group

namespace submodule
section torsion'
open module

variables [comm_semiring R] [add_comm_monoid M] [module R M]
variables (S : Type*) [comm_monoid S] [distrib_mul_action S M] [smul_comm_class S R M]

@[simp] lemma mem_torsion'_iff (x : M) : x ∈ torsion' R M S ↔ ∃ a : S, a • x = 0 := iff.rfl
@[simp] lemma mem_torsion_iff (x : M) : x ∈ torsion R M ↔ ∃ a : R⁰, a • x = 0 := iff.rfl

@[simps] instance : has_smul S (torsion' R M S) :=
⟨λ s x, ⟨s • x, by { obtain ⟨x, a, h⟩ := x, use a, dsimp, rw [smul_comm, h, smul_zero] }⟩⟩
instance : distrib_mul_action S (torsion' R M S) := subtype.coe_injective.distrib_mul_action
  ((torsion' R M S).subtype).to_add_monoid_hom (λ (c : S) x, rfl)
instance : smul_comm_class S R (torsion' R M S) := ⟨λ s a x, subtype.ext $ smul_comm _ _ _⟩

/-- A `S`-torsion module is a module whose `S`-torsion submodule is the full space. -/
lemma is_torsion'_iff_torsion'_eq_top : is_torsion' M S ↔ torsion' R M S = ⊤ :=
⟨λ h, eq_top_iff.mpr (λ _ _, @h _), λ h x, by { rw [← @mem_torsion'_iff R, h], trivial }⟩

/-- The `S`-torsion submodule is a `S`-torsion module. -/
lemma torsion'_is_torsion' : is_torsion' (torsion' R M S) S := λ ⟨x, ⟨a, h⟩⟩, ⟨a, subtype.ext h⟩

@[simp] lemma torsion'_torsion'_eq_top : torsion' R (torsion' R M S) S = ⊤ :=
(is_torsion'_iff_torsion'_eq_top S).mp $ torsion'_is_torsion' S

/-- The torsion submodule of the torsion submodule (viewed as a module) is the full
torsion module. -/
@[simp] lemma torsion_torsion_eq_top : torsion R (torsion R M) = ⊤ := torsion'_torsion'_eq_top R⁰

/-- The torsion submodule is always a torsion module. -/
lemma torsion_is_torsion : module.is_torsion R (torsion R M) := torsion'_is_torsion' R⁰
end torsion'

section torsion
variables [comm_semiring R] [add_comm_monoid M] [module R M]
open_locale big_operators

lemma is_torsion_by_ideal_of_finite_of_is_torsion [module.finite R M] (hM : module.is_torsion R M) :
  ∃ I : ideal R, (I : set R) ∩ R⁰ ≠ ∅ ∧ module.is_torsion_by_set R M I :=
begin
  cases (module.finite_def.mp infer_instance : (⊤ : submodule R M).fg) with S h,
  refine ⟨∏ x in S, ideal.torsion_of R M x, _, _⟩,
  { rw set.ne_empty_iff_nonempty,
    refine ⟨_, _, (∏ x in S, (@hM x).some : R⁰).2⟩,
    rw [subtype.val_eq_coe, submonoid.coe_finset_prod],
    apply ideal.prod_mem_prod,
    exact λ x _, (@hM x).some_spec },
  { rw [module.is_torsion_by_set_iff_torsion_by_set_eq_top, eq_top_iff, ← h, span_le],
    intros x hx, apply torsion_by_set_le_torsion_by_set_of_subset,
    { apply ideal.le_of_dvd, exact finset.dvd_prod_of_mem _ hx },
    { rw mem_torsion_by_set_iff, rintro ⟨a, ha⟩, exact ha } }
end

variables [no_zero_divisors R] [nontrivial R]

lemma coe_torsion_eq_annihilator_ne_bot :
  (torsion R M : set M) = { x : M | (R ∙ x).annihilator ≠ ⊥ } :=
begin
  ext x, simp_rw [submodule.ne_bot_iff, mem_annihilator, mem_span_singleton],
  exact ⟨λ ⟨a, hax⟩, ⟨a, λ _ ⟨b, hb⟩, by rw [← hb, smul_comm, ← submonoid.smul_def, hax, smul_zero],
    non_zero_divisors.coe_ne_zero _⟩,
    λ ⟨a, hax, ha⟩, ⟨⟨_, mem_non_zero_divisors_of_ne_zero ha⟩, hax x ⟨1, one_smul _ _⟩⟩⟩
end

/-- A module over a domain has `no_zero_smul_divisors` iff its torsion submodule is trivial. -/
lemma no_zero_smul_divisors_iff_torsion_eq_bot :
  no_zero_smul_divisors R M ↔ torsion R M = ⊥ :=
begin
  split; intro h,
  { haveI : no_zero_smul_divisors R M := h,
    rw eq_bot_iff, rintro x ⟨a, hax⟩,
    change (a : R) • x = 0 at hax,
    cases eq_zero_or_eq_zero_of_smul_eq_zero hax with h0 h0,
    { exfalso, exact non_zero_divisors.coe_ne_zero a h0 }, { exact h0 } },
  { exact { eq_zero_or_eq_zero_of_smul_eq_zero := λ a x hax, begin
      by_cases ha : a = 0,
      { left, exact ha },
      { right, rw [← mem_bot _, ← h],
        exact ⟨⟨a, mem_non_zero_divisors_of_ne_zero ha⟩, hax⟩ }
    end } }
end
end torsion

namespace quotient_torsion

variables [comm_ring R] [add_comm_group M] [module R M]

/-- Quotienting by the torsion submodule gives a torsion-free module. -/
@[simp] lemma torsion_eq_bot : torsion R (M ⧸ torsion R M) = ⊥ :=
eq_bot_iff.mpr $ λ z, quotient.induction_on' z $ λ x ⟨a, hax⟩,
begin
  rw [quotient.mk'_eq_mk, ← quotient.mk_smul, quotient.mk_eq_zero] at hax,
  rw [mem_bot, quotient.mk'_eq_mk, quotient.mk_eq_zero],
  cases hax with b h,
  exact ⟨b * a, (mul_smul _ _ _).trans h⟩
end

instance no_zero_smul_divisors [is_domain R] : no_zero_smul_divisors R (M ⧸ torsion R M) :=
no_zero_smul_divisors_iff_torsion_eq_bot.mpr torsion_eq_bot

end quotient_torsion

section p_torsion
open module
section
variables [monoid R] [add_comm_monoid M] [distrib_mul_action R M]

lemma is_torsion'_powers_iff (p : R) :
  is_torsion' M (submonoid.powers p) ↔ ∀ x : M, ∃ n : ℕ, p ^ n • x = 0 :=
⟨λ h x, let ⟨⟨a, ⟨n, rfl⟩⟩, hx⟩ := @h x in ⟨n, hx⟩,
λ h x, let ⟨n, hn⟩ := h x in ⟨⟨_, ⟨n, rfl⟩⟩, hn⟩⟩

/--In a `p ^ ∞`-torsion module (that is, a module where all elements are cancelled by scalar
multiplication by some power of `p`), the smallest `n` such that `p ^ n • x = 0`.-/
def p_order {p : R} (hM : is_torsion' M $ submonoid.powers p) (x : M)
  [Π n : ℕ, decidable (p ^ n • x = 0)] :=
nat.find $ (is_torsion'_powers_iff p).mp hM x
@[simp] lemma pow_p_order_smul {p : R} (hM : is_torsion' M $ submonoid.powers p) (x : M)
  [Π n : ℕ, decidable (p ^ n • x = 0)] : p ^ p_order hM x • x = 0 :=
nat.find_spec $ (is_torsion'_powers_iff p).mp hM x

end
variables [comm_semiring R] [add_comm_monoid M] [module R M] [Π x : M, decidable (x = 0)]

lemma exists_is_torsion_by {p : R} (hM : is_torsion' M $ submonoid.powers p)
  (d : ℕ) (hd : d ≠ 0) (s : fin d → M) (hs : span R (set.range s) = ⊤) :
  ∃ j : fin d, module.is_torsion_by R M (p ^ p_order hM (s j)) :=
begin
  let oj := list.argmax (λ i, p_order hM $ s i) (list.fin_range d),
  have hoj : oj.is_some := (option.ne_none_iff_is_some.mp $
    λ eq_none, hd $ list.fin_range_eq_nil.mp $ list.argmax_eq_none.mp eq_none),
  use option.get hoj,
  rw [is_torsion_by_iff_torsion_by_eq_top, eq_top_iff, ← hs, submodule.span_le,
    set.range_subset_iff], intro i, change _ • _ = _,
  have : p_order hM (s i) ≤ p_order hM (s $ option.get hoj) :=
    list.le_of_mem_argmax (list.mem_fin_range i) (option.get_mem hoj),
  rw [← nat.sub_add_cancel this, pow_add, mul_smul, pow_p_order_smul, smul_zero]
end

end p_torsion
end submodule

namespace ideal.quotient

open submodule

lemma torsion_by_eq_span_singleton {R : Type*} [comm_ring R] (a b : R) (ha : a ∈ R⁰) :
  torsion_by R (R ⧸ R ∙ a * b) a = R ∙ (mk _ b) :=
begin
  ext x, rw [mem_torsion_by_iff, mem_span_singleton],
  obtain ⟨x, rfl⟩ := mk_surjective x, split; intro h,
  { rw [← mk_eq_mk, ← quotient.mk_smul, quotient.mk_eq_zero, mem_span_singleton] at h,
    obtain ⟨c, h⟩ := h, rw [smul_eq_mul, smul_eq_mul, mul_comm, mul_assoc,
      mul_cancel_left_mem_non_zero_divisor ha, mul_comm] at h,
    use c, rw [← h, ← mk_eq_mk, ← quotient.mk_smul, smul_eq_mul, mk_eq_mk] },
  { obtain ⟨c, h⟩ := h,
    rw [← h, smul_comm, ← mk_eq_mk, ← quotient.mk_smul,
      (quotient.mk_eq_zero _).mpr $ mem_span_singleton_self _, smul_zero] }
end
end ideal.quotient

namespace add_monoid

theorem is_torsion_iff_is_torsion_nat [add_comm_monoid M] :
  add_monoid.is_torsion M ↔ module.is_torsion ℕ M :=
begin
  refine ⟨λ h x, _, λ h x, _⟩,
  { obtain ⟨n, h0, hn⟩ := (is_of_fin_add_order_iff_nsmul_eq_zero x).mp (h x),
    exact ⟨⟨n, mem_non_zero_divisors_of_ne_zero $ ne_of_gt h0⟩, hn⟩ },
  { rw is_of_fin_add_order_iff_nsmul_eq_zero,
    obtain ⟨n, hn⟩ := @h x,
    refine ⟨n, nat.pos_of_ne_zero (non_zero_divisors.coe_ne_zero _), hn⟩ }
end

theorem is_torsion_iff_is_torsion_int [add_comm_group M] :
  add_monoid.is_torsion M ↔ module.is_torsion ℤ M :=
begin
  refine ⟨λ h x, _, λ h x, _⟩,
  { obtain ⟨n, h0, hn⟩ := (is_of_fin_add_order_iff_nsmul_eq_zero x).mp (h x),
    exact ⟨⟨n, mem_non_zero_divisors_of_ne_zero $ ne_of_gt $ int.coe_nat_pos.mpr h0⟩,
      (coe_nat_zsmul _ _).trans hn⟩ },
  { rw is_of_fin_add_order_iff_nsmul_eq_zero,
    obtain ⟨n, hn⟩ := @h x,
    exact exists_nsmul_eq_zero_of_zsmul_eq_zero (non_zero_divisors.coe_ne_zero n) hn }
end

end add_monoid
