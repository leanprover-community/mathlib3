/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.polynomial.expand
import linear_algebra.finite_dimensional
import linear_algebra.matrix.charpoly.linear_map
import ring_theory.adjoin.fg
import ring_theory.finite_type
import ring_theory.polynomial.scale_roots
import ring_theory.polynomial.tower
import ring_theory.tensor_product

/-!
# Integral closure of a subring.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If A is an R-algebra then `a : A` is integral over R if it is a root of a monic polynomial
with coefficients in R. Enough theory is developed to prove that integral elements
form a sub-R-algebra of A.

## Main definitions

Let `R` be a `comm_ring` and let `A` be an R-algebra.

* `ring_hom.is_integral_elem (f : R →+* A) (x : A)` : `x` is integral with respect to the map `f`,

* `is_integral (x : A)`  : `x` is integral over `R`, i.e., is a root of a monic polynomial with
                           coefficients in `R`.
* `integral_closure R A` : the integral closure of `R` in `A`, regarded as a sub-`R`-algebra of `A`.
-/

open_locale classical
open_locale big_operators polynomial
open polynomial submodule

section ring
variables {R S A : Type*}
variables [comm_ring R] [ring A] [ring S] (f : R →+* S)

/-- An element `x` of `A` is said to be integral over `R` with respect to `f`
if it is a root of a monic polynomial `p : R[X]` evaluated under `f` -/
def ring_hom.is_integral_elem (f : R →+* A) (x : A) :=
∃ p : R[X], monic p ∧ eval₂ f x p = 0

/-- A ring homomorphism `f : R →+* A` is said to be integral
if every element `A` is integral with respect to the map `f` -/
def ring_hom.is_integral (f : R →+* A) :=
∀ x : A, f.is_integral_elem x

variables [algebra R A] (R)

/-- An element `x` of an algebra `A` over a commutative ring `R` is said to be *integral*,
if it is a root of some monic polynomial `p : R[X]`.
Equivalently, the element is integral over `R` with respect to the induced `algebra_map` -/
def is_integral (x : A) : Prop :=
(algebra_map R A).is_integral_elem x

variable (A)

/-- An algebra is integral if every element of the extension is integral over the base ring -/
protected def algebra.is_integral : Prop :=
(algebra_map R A).is_integral

variables {R A}

lemma ring_hom.is_integral_map {x : R} : f.is_integral_elem (f x) :=
⟨X - C x, monic_X_sub_C _, by simp⟩

theorem is_integral_algebra_map {x : R} : is_integral R (algebra_map R A x) :=
(algebra_map R A).is_integral_map

theorem is_integral_of_noetherian (H : is_noetherian R A) (x : A) :
  is_integral R x :=
begin
  let leval : (R[X] →ₗ[R] A) := (aeval x).to_linear_map,
  let D : ℕ → submodule R A := λ n, (degree_le R n).map leval,
  let M := well_founded.min (is_noetherian_iff_well_founded.1 H)
    (set.range D) ⟨_, ⟨0, rfl⟩⟩,
  have HM : M ∈ set.range D := well_founded.min_mem _ _ _,
  cases HM with N HN,
  have HM : ¬M < D (N+1) := well_founded.not_lt_min
    (is_noetherian_iff_well_founded.1 H) (set.range D) _ ⟨N+1, rfl⟩,
  rw ← HN at HM,
  have HN2 : D (N+1) ≤ D N := classical.by_contradiction (λ H, HM
    (lt_of_le_not_le (map_mono (degree_le_mono
      (with_bot.coe_le_coe.2 (nat.le_succ N)))) H)),
  have HN3 : leval (X^(N+1)) ∈ D N,
  { exact HN2 (mem_map_of_mem (mem_degree_le.2 (degree_X_pow_le _))) },
  rcases HN3 with ⟨p, hdp, hpe⟩,
  refine ⟨X^(N+1) - p, monic_X_pow_sub (mem_degree_le.1 hdp), _⟩,
  show leval (X ^ (N + 1) - p) = 0,
  rw [linear_map.map_sub, hpe, sub_self]
end

theorem is_integral_of_submodule_noetherian (S : subalgebra R A)
  (H : is_noetherian R S.to_submodule) (x : A) (hx : x ∈ S) :
  is_integral R x :=
begin
  suffices : is_integral R (show S, from ⟨x, hx⟩),
  { rcases this with ⟨p, hpm, hpx⟩,
    replace hpx := congr_arg S.val hpx,
    refine ⟨p, hpm, eq.trans _ hpx⟩,
    simp only [aeval_def, eval₂, sum_def],
    rw S.val.map_sum,
    refine finset.sum_congr rfl (λ n hn, _),
    rw [S.val.map_mul, S.val.map_pow, S.val.commutes, S.val_apply, subtype.coe_mk], },
  refine is_integral_of_noetherian H ⟨x, hx⟩
end

end ring

section
variables {R A B S : Type*}
variables [comm_ring R] [comm_ring A] [comm_ring B] [comm_ring S]
variables [algebra R A] [algebra R B] (f : R →+* S)

lemma map_is_integral {B C F : Type*} [ring B] [ring C] [algebra R B] [algebra A B]
  [algebra R C] [is_scalar_tower R A B] [algebra A C] [is_scalar_tower R A C] {b : B}
  [alg_hom_class F A B C] (f : F) (hb : is_integral R b) : is_integral R (f b) :=
begin
  obtain ⟨P, hP⟩ := hb,
  refine ⟨P, hP.1, _⟩,
  rw [← aeval_def, show (aeval (f b)) P = (aeval (f b)) (P.map (algebra_map R A)), by simp,
    aeval_alg_hom_apply, aeval_map_algebra_map, aeval_def, hP.2, _root_.map_zero]
end

lemma is_integral_map_of_comp_eq_of_is_integral {R S T U : Type*} [comm_ring R] [comm_ring S]
  [comm_ring T] [comm_ring U] [algebra R S] [algebra T U] (φ : R →+* T) (ψ : S →+* U)
  (h : (algebra_map T U).comp φ = ψ.comp (algebra_map R S)) {a : S} (ha : is_integral R a) :
  is_integral T (ψ a) :=
begin
  rw [is_integral, ring_hom.is_integral_elem] at ⊢ ha,
  obtain ⟨p, hp⟩ := ha,
  refine ⟨p.map φ, hp.left.map _, _⟩,
  rw [← eval_map, map_map, h, ← map_map, eval_map, eval₂_at_apply,
    eval_map, hp.right, ring_hom.map_zero],
end

theorem is_integral_alg_hom_iff {A B : Type*} [ring A] [ring B] [algebra R A] [algebra R B]
  (f : A →ₐ[R] B) (hf : function.injective f) {x : A} : is_integral R (f x) ↔ is_integral R x :=
begin
  refine ⟨_, map_is_integral f⟩,
  rintros ⟨p, hp, hx⟩,
  use [p, hp],
  rwa [← f.comp_algebra_map, ← alg_hom.coe_to_ring_hom, ← polynomial.hom_eval₂,
    alg_hom.coe_to_ring_hom, map_eq_zero_iff f hf] at hx
end

@[simp]
theorem is_integral_alg_equiv {A B : Type*} [ring A] [ring B] [algebra R A] [algebra R B]
  (f : A ≃ₐ[R] B) {x : A} : is_integral R (f x) ↔ is_integral R x :=
⟨λ h, by simpa using map_is_integral f.symm.to_alg_hom h, map_is_integral f.to_alg_hom⟩

theorem is_integral_of_is_scalar_tower [algebra A B] [is_scalar_tower R A B]
  {x : B} (hx : is_integral R x) : is_integral A x :=
let ⟨p, hp, hpx⟩ := hx in
⟨p.map $ algebra_map R A, hp.map _,
  by rw [← aeval_def, aeval_map_algebra_map, aeval_def, hpx]⟩

lemma map_is_integral_int {B C F : Type*} [ring B] [ring C] {b : B}
  [ring_hom_class F B C] (f : F) (hb : is_integral ℤ b) :
  is_integral ℤ (f b) :=
map_is_integral (f : B →+* C).to_int_alg_hom hb

theorem is_integral_of_subring {x : A} (T : subring R)
  (hx : is_integral T x) : is_integral R x :=
is_integral_of_is_scalar_tower hx

lemma is_integral.algebra_map [algebra A B] [is_scalar_tower R A B]
  {x : A} (h : is_integral R x) :
  is_integral R (algebra_map A B x) :=
begin
  rcases h with ⟨f, hf, hx⟩,
  use [f, hf],
  rw [is_scalar_tower.algebra_map_eq R A B, ← hom_eval₂, hx, ring_hom.map_zero]
end

lemma is_integral_algebra_map_iff [algebra A B] [is_scalar_tower R A B]
  {x : A} (hAB : function.injective (algebra_map A B)) :
  is_integral R (algebra_map A B x) ↔ is_integral R x :=
is_integral_alg_hom_iff (is_scalar_tower.to_alg_hom R A B) hAB

theorem is_integral_iff_is_integral_closure_finite {r : A} :
  is_integral R r ↔ ∃ s : set R, s.finite ∧ is_integral (subring.closure s) r :=
begin
  split; intro hr,
  { rcases hr with ⟨p, hmp, hpr⟩,
    refine ⟨_, finset.finite_to_set _, p.restriction, monic_restriction.2 hmp, _⟩,
    rw [← aeval_def, ← aeval_map_algebra_map R r p.restriction,
      map_restriction, aeval_def, hpr], },
  rcases hr with ⟨s, hs, hsr⟩,
  exact is_integral_of_subring _ hsr
end

theorem fg_adjoin_singleton_of_integral (x : A) (hx : is_integral R x) :
  (algebra.adjoin R ({x} : set A)).to_submodule.fg :=
begin
  rcases hx with ⟨f, hfm, hfx⟩,
  existsi finset.image ((^) x) (finset.range (nat_degree f + 1)),
  apply le_antisymm,
  { rw span_le, intros s hs, rw finset.mem_coe at hs,
    rcases finset.mem_image.1 hs with ⟨k, hk, rfl⟩, clear hk,
    exact (algebra.adjoin R {x}).pow_mem (algebra.subset_adjoin (set.mem_singleton _)) k },
  intros r hr, change r ∈ algebra.adjoin R ({x} : set A) at hr,
  rw algebra.adjoin_singleton_eq_range_aeval at hr,
  rcases (aeval x).mem_range.mp hr with ⟨p, rfl⟩,
  rw ← mod_by_monic_add_div p hfm,
  rw ← aeval_def at hfx,
  rw [alg_hom.map_add, alg_hom.map_mul, hfx, zero_mul, add_zero],
  have : degree (p %ₘ f) ≤ degree f := degree_mod_by_monic_le p hfm,
  generalize_hyp : p %ₘ f = q at this ⊢,
  rw [← sum_C_mul_X_pow_eq q, aeval_def, eval₂_sum, sum_def],
  refine sum_mem (λ k hkq, _),
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← algebra.smul_def],
  refine smul_mem _ _ (subset_span _),
  rw finset.mem_coe, refine finset.mem_image.2 ⟨_, _, rfl⟩,
  rw [finset.mem_range, nat.lt_succ_iff], refine le_of_not_lt (λ hk, _),
  rw [degree_le_iff_coeff_zero] at this,
  rw [mem_support_iff] at hkq, apply hkq, apply this,
  exact lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 hk)
end

theorem fg_adjoin_of_finite {s : set A} (hfs : s.finite)
  (his : ∀ x ∈ s, is_integral R x) : (algebra.adjoin R s).to_submodule.fg :=
set.finite.induction_on hfs (λ _, ⟨{1}, submodule.ext $ λ x,
  by { erw [algebra.adjoin_empty, finset.coe_singleton, ← one_eq_span, one_eq_range,
            linear_map.mem_range, algebra.mem_bot], refl }⟩)
(λ a s has hs ih his, by rw [← set.union_singleton, algebra.adjoin_union_coe_submodule]; exact
  fg.mul (ih $ λ i hi, his i $ set.mem_insert_of_mem a hi)
    (fg_adjoin_singleton_of_integral _ $ his a $ set.mem_insert a s)) his

lemma is_noetherian_adjoin_finset [is_noetherian_ring R] (s : finset A)
  (hs : ∀ x ∈ s, is_integral R x) :
  is_noetherian R (algebra.adjoin R (↑s : set A)) :=
is_noetherian_of_fg_of_noetherian _ (fg_adjoin_of_finite s.finite_to_set hs)

/-- If `S` is a sub-`R`-algebra of `A` and `S` is finitely-generated as an `R`-module,
  then all elements of `S` are integral over `R`. -/
theorem is_integral_of_mem_of_fg (S : subalgebra R A)
  (HS : S.to_submodule.fg) (x : A) (hx : x ∈ S) : is_integral R x :=
begin
  -- say `x ∈ S`. We want to prove that `x` is integral over `R`.
  -- Say `S` is generated as an `R`-module by the set `y`.
  cases HS with y hy,
  -- We can write `x` as `∑ rᵢ yᵢ` for `yᵢ ∈ Y`.
  obtain ⟨lx, hlx1, hlx2⟩ :
    ∃ (l : A →₀ R) (H : l ∈ finsupp.supported R R ↑y), (finsupp.total A A R id) l = x,
  { rwa [←(@finsupp.mem_span_image_iff_total A A R _ _ _ id ↑y x), set.image_id ↑y, hy] },
  -- Note that `y ⊆ S`.
  have hyS : ∀ {p}, p ∈ y → p ∈ S := λ p hp, show p ∈ S.to_submodule,
    by { rw ← hy, exact subset_span hp },
  -- Now `S` is a subalgebra so the product of two elements of `y` is also in `S`.
  have : ∀ (jk : (↑(y ×ˢ y) : set (A × A))), jk.1.1 * jk.1.2 ∈ S.to_submodule :=
    λ jk, S.mul_mem (hyS (finset.mem_product.1 jk.2).1) (hyS (finset.mem_product.1 jk.2).2),
  rw [← hy, ← set.image_id ↑y] at this, simp only [finsupp.mem_span_image_iff_total] at this,
  -- Say `yᵢyⱼ = ∑rᵢⱼₖ yₖ`
  choose ly hly1 hly2,
  -- Now let `S₀` be the subring of `R` generated by the `rᵢ` and the `rᵢⱼₖ`.
  let S₀ : subring R :=
    subring.closure ↑(lx.frange ∪ finset.bUnion finset.univ (finsupp.frange ∘ ly)),
  -- It suffices to prove that `x` is integral over `S₀`.
  refine is_integral_of_subring S₀ _,
  letI : comm_ring S₀ := subring_class.to_comm_ring S₀,
  letI : algebra S₀ A := algebra.of_subring S₀,
  -- Claim: the `S₀`-module span (in `A`) of the set `y ∪ {1}` is closed under
  -- multiplication (indeed, this is the motivation for the definition of `S₀`).
  have :
    span S₀ (insert 1 ↑y : set A) * span S₀ (insert 1 ↑y : set A) ≤ span S₀ (insert 1 ↑y : set A),
  { rw span_mul_span, refine span_le.2 (λ z hz, _),
    rcases set.mem_mul.1 hz with ⟨p, q, rfl | hp, hq, rfl⟩,
    { rw one_mul, exact subset_span hq },
    rcases hq with rfl | hq,
    { rw mul_one, exact subset_span (or.inr hp) },
    erw ← hly2 ⟨(p, q), finset.mem_product.2 ⟨hp, hq⟩⟩,
    rw [finsupp.total_apply, finsupp.sum],
    refine (span S₀ (insert 1 ↑y : set A)).sum_mem (λ t ht, _),
    have : ly ⟨(p, q), finset.mem_product.2 ⟨hp, hq⟩⟩ t ∈ S₀ :=
    subring.subset_closure (finset.mem_union_right _ $ finset.mem_bUnion.2
      ⟨⟨(p, q), finset.mem_product.2 ⟨hp, hq⟩⟩, finset.mem_univ _,
        finsupp.mem_frange.2 ⟨finsupp.mem_support_iff.1 ht, _, rfl⟩⟩),
    change (⟨_, this⟩ : S₀) • t ∈ _, exact smul_mem _ _ (subset_span $ or.inr $ hly1 _ ht) },
  -- Hence this span is a subring. Call this subring `S₁`.
  let S₁ : subring A :=
  { carrier := span S₀ (insert 1 ↑y : set A),
    one_mem' := subset_span $ or.inl rfl,
    mul_mem' := λ p q hp hq, this $ mul_mem_mul hp hq,
    zero_mem' := (span S₀ (insert 1 ↑y : set A)).zero_mem,
    add_mem' := λ _ _, (span S₀ (insert 1 ↑y : set A)).add_mem,
    neg_mem' := λ _, (span S₀ (insert 1 ↑y : set A)).neg_mem },
  have : S₁ = subalgebra.to_subring (algebra.adjoin S₀ (↑y : set A)),
  { ext z,
    suffices : z ∈ span ↥S₀ (insert 1 ↑y : set A) ↔
      z ∈ (algebra.adjoin ↥S₀ (y : set A)).to_submodule,
    { simpa },
    split; intro hz,
    { exact (span_le.2
        (set.insert_subset.2 ⟨(algebra.adjoin S₀ ↑y).one_mem, algebra.subset_adjoin⟩)) hz },
    { rw [subalgebra.mem_to_submodule, algebra.mem_adjoin_iff] at hz,
      suffices : subring.closure (set.range ⇑(algebra_map ↥S₀ A) ∪ ↑y) ≤ S₁,
      { exact this hz },
      refine subring.closure_le.2 (set.union_subset _ (λ t ht, subset_span $ or.inr ht)),
      rw set.range_subset_iff,
      intro y,
      rw algebra.algebra_map_eq_smul_one,
      exact smul_mem _ y (subset_span (or.inl rfl)) } },
  have foo : ∀ z, z ∈ S₁ ↔ z ∈ algebra.adjoin ↥S₀ (y : set A),
    simp [this],
  haveI : is_noetherian_ring ↥S₀ := is_noetherian_subring_closure _ (finset.finite_to_set _),
  refine is_integral_of_submodule_noetherian (algebra.adjoin S₀ ↑y)
    (is_noetherian_of_fg_of_noetherian _ ⟨insert 1 y,
      by { rw [finset.coe_insert], ext z, simp [S₁], convert foo z}⟩) _ _,
  rw [← hlx2, finsupp.total_apply, finsupp.sum], refine subalgebra.sum_mem _ (λ r hr, _),
  have : lx r ∈ S₀ :=
    subring.subset_closure (finset.mem_union_left _ (finset.mem_image_of_mem _ hr)),
  change (⟨_, this⟩ : S₀) • r ∈ _,
  rw finsupp.mem_supported at hlx1,
  exact subalgebra.smul_mem _ (algebra.subset_adjoin $ hlx1 hr) _
end

lemma module.End.is_integral {M : Type*} [add_comm_group M] [module R M] [module.finite R M] :
  algebra.is_integral R (module.End R M) :=
linear_map.exists_monic_and_aeval_eq_zero R

/-- Suppose `A` is an `R`-algebra, `M` is an `A`-module such that `a • m ≠ 0` for all non-zero `a`
and `m`. If `x : A` fixes a nontrivial f.g. `R`-submodule `N` of `M`, then `x` is `R`-integral. -/
lemma is_integral_of_smul_mem_submodule {M : Type*} [add_comm_group M] [module R M]
  [module A M] [is_scalar_tower R A M] [no_zero_smul_divisors A M]
  (N : submodule R M) (hN : N ≠ ⊥) (hN' : N.fg) (x : A)
    (hx : ∀ n ∈ N, x • n ∈ N) : is_integral R x :=
begin
  let A' : subalgebra R A :=
  { carrier := { x | ∀ n ∈ N, x • n ∈ N },
    mul_mem' := λ a b ha hb n hn, smul_smul a b n ▸ ha _ (hb _ hn),
    one_mem' := λ n hn, (one_smul A n).symm ▸ hn,
    add_mem' := λ a b ha hb n hn, (add_smul a b n).symm ▸ N.add_mem (ha _ hn) (hb _ hn),
    zero_mem' := λ n hn, (zero_smul A n).symm ▸ N.zero_mem,
    algebra_map_mem' := λ r n hn, (algebra_map_smul A r n).symm ▸ N.smul_mem r hn },
  let f : A' →ₐ[R] module.End R N := alg_hom.of_linear_map
    { to_fun := λ x, (distrib_mul_action.to_linear_map R M x).restrict x.prop,
      map_add' := λ x y, linear_map.ext $ λ n, subtype.ext $ add_smul x y n,
      map_smul' := λ r s, linear_map.ext $ λ n, subtype.ext $ smul_assoc r s n }
      (linear_map.ext $ λ n, subtype.ext $ one_smul _ _)
      (λ x y, linear_map.ext $ λ n, subtype.ext $ mul_smul x y n),
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ N, a ≠ (0 : M),
  { by_contra h', push_neg at h', apply hN, rwa eq_bot_iff },
  have : function.injective f,
  { show function.injective f.to_linear_map,
    rw [← linear_map.ker_eq_bot, eq_bot_iff],
    intros s hs,
    have : s.1 • a = 0 := congr_arg subtype.val (linear_map.congr_fun hs ⟨a, ha₁⟩),
    exact subtype.ext ((eq_zero_or_eq_zero_of_smul_eq_zero this).resolve_right ha₂) },
  show is_integral R (A'.val ⟨x, hx⟩),
  rw [is_integral_alg_hom_iff A'.val subtype.val_injective,
    ← is_integral_alg_hom_iff f this],
  haveI : module.finite R N := by rwa [module.finite_def, submodule.fg_top],
  apply module.End.is_integral,
end

variables {f}

lemma ring_hom.finite.to_is_integral (h : f.finite) : f.is_integral :=
by { letI := f.to_algebra, exact λ x, is_integral_of_mem_of_fg ⊤ h.1 _ trivial }

alias ring_hom.finite.to_is_integral ← ring_hom.is_integral.of_finite

lemma ring_hom.is_integral.to_finite (h : f.is_integral) (h' : f.finite_type) : f.finite :=
begin
  letI := f.to_algebra,
  unfreezingI { obtain ⟨s, hs⟩ := h' },
  constructor,
  change (⊤ : subalgebra R S).to_submodule.fg,
  rw ← hs,
  exact fg_adjoin_of_finite (set.to_finite _) (λ x _, h x)
end

alias ring_hom.is_integral.to_finite ← ring_hom.finite.of_is_integral_of_finite_type

/-- finite = integral + finite type -/
lemma ring_hom.finite_iff_is_integral_and_finite_type :
  f.finite ↔ f.is_integral ∧ f.finite_type :=
⟨λ h, ⟨h.to_is_integral, h.to_finite_type⟩, λ ⟨h, h'⟩, h.to_finite h'⟩

lemma algebra.is_integral.finite (h : algebra.is_integral R A) [h' : algebra.finite_type R A] :
  module.finite R A :=
begin
  have := h.to_finite
    (by { delta ring_hom.finite_type, convert h', ext, exact (algebra.smul_def _ _).symm }),
  delta ring_hom.finite at this, convert this, ext, exact algebra.smul_def _ _,
end

lemma algebra.is_integral.of_finite [h : module.finite R A] : algebra.is_integral R A :=
begin
  apply ring_hom.finite.to_is_integral,
  delta ring_hom.finite, convert h, ext, exact (algebra.smul_def _ _).symm,
end

/-- finite = integral + finite type -/
lemma algebra.finite_iff_is_integral_and_finite_type :
  module.finite R A ↔ algebra.is_integral R A ∧ algebra.finite_type R A :=
⟨λ h, by exactI ⟨algebra.is_integral.of_finite, infer_instance⟩, λ ⟨h, h'⟩, by exactI h.finite⟩

variables (f)

lemma ring_hom.is_integral_of_mem_closure {x y z : S}
  (hx : f.is_integral_elem x) (hy : f.is_integral_elem y)
  (hz : z ∈ subring.closure ({x, y} : set S)) :
  f.is_integral_elem z :=
begin
  letI : algebra R S := f.to_algebra,
  have := (fg_adjoin_singleton_of_integral x hx).mul (fg_adjoin_singleton_of_integral y hy),
  rw [← algebra.adjoin_union_coe_submodule, set.singleton_union] at this,
  exact is_integral_of_mem_of_fg (algebra.adjoin R {x, y}) this z
    (algebra.mem_adjoin_iff.2 $ subring.closure_mono (set.subset_union_right _ _) hz),
end

theorem is_integral_of_mem_closure {x y z : A}
  (hx : is_integral R x) (hy : is_integral R y)
  (hz : z ∈ subring.closure ({x, y} : set A)) :
  is_integral R z :=
(algebra_map R A).is_integral_of_mem_closure hx hy hz

lemma ring_hom.is_integral_zero : f.is_integral_elem 0 :=
f.map_zero ▸ f.is_integral_map

theorem is_integral_zero : is_integral R (0:A) :=
(algebra_map R A).is_integral_zero

lemma ring_hom.is_integral_one : f.is_integral_elem 1 :=
f.map_one ▸ f.is_integral_map

theorem is_integral_one : is_integral R (1:A) :=
(algebra_map R A).is_integral_one

lemma ring_hom.is_integral_add {x y : S}
  (hx : f.is_integral_elem x) (hy : f.is_integral_elem y) :
  f.is_integral_elem (x + y) :=
f.is_integral_of_mem_closure hx hy $ subring.add_mem _
  (subring.subset_closure (or.inl rfl)) (subring.subset_closure (or.inr rfl))

theorem is_integral_add {x y : A}
  (hx : is_integral R x) (hy : is_integral R y) :
  is_integral R (x + y) :=
(algebra_map R A).is_integral_add hx hy

lemma ring_hom.is_integral_neg {x : S}
  (hx : f.is_integral_elem x) : f.is_integral_elem (-x) :=
f.is_integral_of_mem_closure hx hx (subring.neg_mem _ (subring.subset_closure (or.inl rfl)))

theorem is_integral_neg {x : A}
  (hx : is_integral R x) : is_integral R (-x) :=
(algebra_map R A).is_integral_neg hx

lemma ring_hom.is_integral_sub {x y : S}
  (hx : f.is_integral_elem x) (hy : f.is_integral_elem y) : f.is_integral_elem (x - y) :=
by simpa only [sub_eq_add_neg] using f.is_integral_add hx (f.is_integral_neg hy)

theorem is_integral_sub {x y : A}
  (hx : is_integral R x) (hy : is_integral R y) : is_integral R (x - y) :=
(algebra_map R A).is_integral_sub hx hy

lemma ring_hom.is_integral_mul {x y : S}
  (hx : f.is_integral_elem x) (hy : f.is_integral_elem y) : f.is_integral_elem (x * y) :=
f.is_integral_of_mem_closure hx hy (subring.mul_mem _
  (subring.subset_closure (or.inl rfl)) (subring.subset_closure (or.inr rfl)))

theorem is_integral_mul {x y : A}
  (hx : is_integral R x) (hy : is_integral R y) : is_integral R (x * y) :=
(algebra_map R A).is_integral_mul hx hy

lemma is_integral_smul [algebra S A] [algebra R S] [is_scalar_tower R S A] {x : A} (r : R)
  (hx : is_integral S x) : is_integral S (r • x) :=
begin
  rw [algebra.smul_def, is_scalar_tower.algebra_map_apply R S A],
  exact is_integral_mul is_integral_algebra_map hx,
end

lemma is_integral_of_pow {x : A} {n : ℕ} (hn : 0 < n) (hx : is_integral R $ x ^ n) :
  is_integral R x :=
begin
  rcases hx with ⟨p, ⟨hmonic, heval⟩⟩,
  exact ⟨expand R n p, monic.expand hn hmonic,
         by rwa [eval₂_eq_eval_map, map_expand, expand_eval, ← eval₂_eq_eval_map]⟩
end

variables (R A)

/-- The integral closure of R in an R-algebra A. -/
def integral_closure : subalgebra R A :=
{ carrier := { r | is_integral R r },
  zero_mem' := is_integral_zero,
  one_mem' := is_integral_one,
  add_mem' := λ _ _, is_integral_add,
  mul_mem' := λ _ _, is_integral_mul,
  algebra_map_mem' := λ x, is_integral_algebra_map }

theorem mem_integral_closure_iff_mem_fg {r : A} :
  r ∈ integral_closure R A ↔ ∃ M : subalgebra R A, M.to_submodule.fg ∧ r ∈ M :=
⟨λ hr, ⟨algebra.adjoin R {r}, fg_adjoin_singleton_of_integral _ hr, algebra.subset_adjoin rfl⟩,
λ ⟨M, Hf, hrM⟩, is_integral_of_mem_of_fg M Hf _ hrM⟩

variables {R} {A}

lemma adjoin_le_integral_closure {x : A} (hx : is_integral R x) :
  algebra.adjoin R {x} ≤ integral_closure R A :=
begin
  rw [algebra.adjoin_le_iff],
  simp only [set_like.mem_coe, set.singleton_subset_iff],
  exact hx
end

lemma le_integral_closure_iff_is_integral {S : subalgebra R A} :
  S ≤ integral_closure R A ↔ algebra.is_integral R S :=
set_like.forall.symm.trans (forall_congr (λ x, show is_integral R (algebra_map S A x)
  ↔ is_integral R x, from is_integral_algebra_map_iff subtype.coe_injective))

lemma is_integral_sup {S T : subalgebra R A} :
  algebra.is_integral R ↥(S ⊔ T) ↔ algebra.is_integral R S ∧ algebra.is_integral R T :=
by simp only [←le_integral_closure_iff_is_integral, sup_le_iff]

/-- Mapping an integral closure along an `alg_equiv` gives the integral closure. -/
lemma integral_closure_map_alg_equiv (f : A ≃ₐ[R] B) :
  (integral_closure R A).map (f : A →ₐ[R] B) = integral_closure R B :=
begin
  ext y,
  rw subalgebra.mem_map,
  split,
  { rintros ⟨x, hx, rfl⟩,
    exact map_is_integral f hx },
  { intro hy,
    use [f.symm y, map_is_integral (f.symm : B →ₐ[R] A) hy],
    simp }
end

lemma integral_closure.is_integral (x : integral_closure R A) : is_integral R x :=
let ⟨p, hpm, hpx⟩ := x.2 in ⟨p, hpm, subtype.eq $
by rwa [← aeval_def, subtype.val_eq_coe, ← subalgebra.val_apply, aeval_alg_hom_apply] at hpx⟩

lemma ring_hom.is_integral_of_is_integral_mul_unit (x y : S) (r : R) (hr : f r * y = 1)
  (hx : f.is_integral_elem (x * y)) : f.is_integral_elem x :=
begin
  obtain ⟨p, ⟨p_monic, hp⟩⟩ := hx,
  refine ⟨scale_roots p r, ⟨(monic_scale_roots_iff r).2 p_monic, _⟩⟩,
  convert scale_roots_eval₂_eq_zero f hp,
  rw [mul_comm x y, ← mul_assoc, hr, one_mul],
end

theorem is_integral_of_is_integral_mul_unit {x y : A} {r : R} (hr : algebra_map R A r * y = 1)
  (hx : is_integral R (x * y)) : is_integral R x :=
(algebra_map R A).is_integral_of_is_integral_mul_unit x y r hr hx

/-- Generalization of `is_integral_of_mem_closure` bootstrapped up from that lemma -/
lemma is_integral_of_mem_closure' (G : set A) (hG : ∀ x ∈ G, is_integral R x) :
  ∀ x ∈ (subring.closure G), is_integral R x :=
λ x hx, subring.closure_induction hx hG is_integral_zero is_integral_one
  (λ _ _, is_integral_add) (λ _, is_integral_neg) (λ _ _, is_integral_mul)

lemma is_integral_of_mem_closure'' {S : Type*} [comm_ring S] {f : R →+* S} (G : set S)
  (hG : ∀ x ∈ G, f.is_integral_elem x) : ∀ x ∈ (subring.closure G), f.is_integral_elem x :=
λ x hx, @is_integral_of_mem_closure' R S _ _ f.to_algebra G hG x hx

lemma is_integral.pow {x : A} (h : is_integral R x) (n : ℕ) : is_integral R (x ^ n) :=
(integral_closure R A).pow_mem h n

lemma is_integral.nsmul {x : A} (h : is_integral R x) (n : ℕ) : is_integral R (n • x) :=
(integral_closure R A).nsmul_mem h n

lemma is_integral.zsmul {x : A} (h : is_integral R x) (n : ℤ) : is_integral R (n • x) :=
(integral_closure R A).zsmul_mem h n

lemma is_integral.multiset_prod {s : multiset A} (h : ∀ x ∈ s, is_integral R x) :
  is_integral R s.prod :=
(integral_closure R A).multiset_prod_mem h

lemma is_integral.multiset_sum {s : multiset A} (h : ∀ x ∈ s, is_integral R x) :
  is_integral R s.sum :=
(integral_closure R A).multiset_sum_mem h

lemma is_integral.prod {α : Type*} {s : finset α} (f : α → A) (h : ∀ x ∈ s, is_integral R (f x)) :
  is_integral R (∏ x in s, f x) :=
(integral_closure R A).prod_mem h

lemma is_integral.sum {α : Type*} {s : finset α} (f : α → A) (h : ∀ x ∈ s, is_integral R (f x)) :
  is_integral R (∑ x in s, f x) :=
(integral_closure R A).sum_mem h

lemma is_integral.det {n : Type*} [fintype n] [decidable_eq n] {M : matrix n n A}
  (h : ∀ i j, is_integral R (M i j)) :
  is_integral R M.det :=
begin
  rw [matrix.det_apply],
  exact is_integral.sum _ (λ σ hσ, is_integral.zsmul (is_integral.prod _ (λ i hi, h _ _)) _)
end

@[simp] lemma is_integral.pow_iff {x : A} {n : ℕ} (hn : 0 < n) :
  is_integral R (x ^ n) ↔ is_integral R x :=
⟨is_integral_of_pow hn, λ hx, is_integral.pow hx n⟩

open_locale tensor_product

lemma is_integral.tmul (x : A) {y : B} (h : is_integral R y) : is_integral A (x ⊗ₜ[R] y) :=
begin
  obtain ⟨p, hp, hp'⟩ := h,
  refine ⟨(p.map (algebra_map R A)).scale_roots x, _, _⟩,
  { rw polynomial.monic_scale_roots_iff, exact hp.map _ },
  convert @polynomial.scale_roots_eval₂_mul (A ⊗[R] B) A _ _ _
    algebra.tensor_product.include_left.to_ring_hom (1 ⊗ₜ y) x using 2,
  { simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom, mul_one, one_mul,
      algebra.tensor_product.include_left_apply, algebra.tensor_product.tmul_mul_tmul] },
  convert (mul_zero _).symm,
  rw [polynomial.eval₂_map, algebra.tensor_product.include_left_comp_algebra_map,
    ← polynomial.eval₂_map],
  convert polynomial.eval₂_at_apply algebra.tensor_product.include_right.to_ring_hom y,
  rw [polynomial.eval_map, hp', _root_.map_zero],
end

section

variables (p : R[X]) (x : S)

/--  The monic polynomial whose roots are `p.leading_coeff * x` for roots `x` of `p`. -/
noncomputable
def normalize_scale_roots (p : R[X]) : R[X] :=
∑ i in p.support, monomial i
  (if i = p.nat_degree then 1 else p.coeff i * p.leading_coeff ^ (p.nat_degree - 1 - i))

lemma normalize_scale_roots_coeff_mul_leading_coeff_pow (i : ℕ) (hp : 1 ≤ nat_degree p) :
  (normalize_scale_roots p).coeff i * p.leading_coeff ^ i =
    p.coeff i * p.leading_coeff ^ (p.nat_degree - 1) :=
begin
  simp only [normalize_scale_roots, finset_sum_coeff, coeff_monomial, finset.sum_ite_eq', one_mul,
    zero_mul, mem_support_iff, ite_mul, ne.def, ite_not],
  split_ifs with h₁ h₂,
  { simp [h₁], },
  { rw [h₂, leading_coeff, ← pow_succ, tsub_add_cancel_of_le hp], },
  { rw [mul_assoc, ← pow_add, tsub_add_cancel_of_le],
    apply nat.le_pred_of_lt,
    rw lt_iff_le_and_ne,
    exact ⟨le_nat_degree_of_ne_zero h₁, h₂⟩, },
end

lemma leading_coeff_smul_normalize_scale_roots (p : R[X]) :
  p.leading_coeff • normalize_scale_roots p = scale_roots p p.leading_coeff :=
begin
  ext,
  simp only [coeff_scale_roots, normalize_scale_roots, coeff_monomial, coeff_smul, finset.smul_sum,
    ne.def, finset.sum_ite_eq', finset_sum_coeff, smul_ite, smul_zero, mem_support_iff],
  split_ifs with h₁ h₂,
  { simp [*] },
  { simp [*] },
  { rw [algebra.id.smul_eq_mul, mul_comm, mul_assoc, ← pow_succ', tsub_right_comm,
      tsub_add_cancel_of_le],
    rw nat.succ_le_iff,
    exact tsub_pos_of_lt (lt_of_le_of_ne (le_nat_degree_of_ne_zero h₁) h₂) },
end

lemma normalize_scale_roots_support :
  (normalize_scale_roots p).support ≤ p.support :=
begin
  intro x,
  contrapose,
  simp only [not_mem_support_iff, normalize_scale_roots, finset_sum_coeff, coeff_monomial,
    finset.sum_ite_eq', mem_support_iff, ne.def, not_not, ite_eq_right_iff],
  intros h₁ h₂,
  exact (h₂ h₁).rec _,
end

lemma normalize_scale_roots_degree :
  (normalize_scale_roots p).degree = p.degree :=
begin
  apply le_antisymm,
  { exact finset.sup_mono (normalize_scale_roots_support p) },
  { rw [← degree_scale_roots, ← leading_coeff_smul_normalize_scale_roots],
    exact degree_smul_le _ _ }
end

lemma normalize_scale_roots_eval₂_leading_coeff_mul (h : 1 ≤ p.nat_degree) (f : R →+* S) (x : S) :
  (normalize_scale_roots p).eval₂ f (f p.leading_coeff * x) =
    f p.leading_coeff ^ (p.nat_degree - 1) * (p.eval₂ f x) :=
begin
  rw [eval₂_eq_sum_range, eval₂_eq_sum_range, finset.mul_sum],
  apply finset.sum_congr,
  { rw nat_degree_eq_of_degree_eq (normalize_scale_roots_degree p) },
  intros n hn,
  rw [mul_pow, ← mul_assoc, ← f.map_pow, ← f.map_mul,
    normalize_scale_roots_coeff_mul_leading_coeff_pow _ _ h, f.map_mul, f.map_pow],
  ring,
end

lemma normalize_scale_roots_monic (h : p ≠ 0) : (normalize_scale_roots p).monic :=
begin
  delta monic leading_coeff,
  rw nat_degree_eq_of_degree_eq (normalize_scale_roots_degree p),
  suffices : p = 0 → (0 : R) = 1,
  { simpa [normalize_scale_roots, coeff_monomial] },
  exact λ h', (h h').rec _,
end

/-- Given a `p : R[X]` and a `x : S` such that `p.eval₂ f x = 0`,
`f p.leading_coeff * x` is integral. -/
lemma ring_hom.is_integral_elem_leading_coeff_mul (h : p.eval₂ f x = 0) :
  f.is_integral_elem (f p.leading_coeff * x) :=
begin
  by_cases h' : 1 ≤ p.nat_degree,
  { use normalize_scale_roots p,
    have : p ≠ 0 := λ h'', by { rw [h'', nat_degree_zero] at h', exact nat.not_succ_le_zero 0 h' },
    use normalize_scale_roots_monic p this,
    rw [normalize_scale_roots_eval₂_leading_coeff_mul p h' f x, h, mul_zero] },
  { by_cases hp : p.map f = 0,
    { apply_fun (λ q, coeff q p.nat_degree) at hp,
      rw [coeff_map, coeff_zero, coeff_nat_degree] at hp,
      rw [hp, zero_mul],
      exact f.is_integral_zero },
    { rw [nat.one_le_iff_ne_zero, not_not] at h',
      rw [eq_C_of_nat_degree_eq_zero h', eval₂_C] at h,
      suffices : p.map f = 0,
      { exact (hp this).rec _ },
      rw [eq_C_of_nat_degree_eq_zero h', map_C, h, C_eq_zero] } }
end

/-- Given a `p : R[X]` and a root `x : S`,
then `p.leading_coeff • x : S` is integral over `R`. -/
lemma is_integral_leading_coeff_smul [algebra R S] (h : aeval x p = 0) :
  is_integral R (p.leading_coeff • x) :=
begin
  rw aeval_def at h,
  rw algebra.smul_def,
  exact (algebra_map R S).is_integral_elem_leading_coeff_mul p x h,
end

end

end

section is_integral_closure

/-- `is_integral_closure A R B` is the characteristic predicate stating `A` is
the integral closure of `R` in `B`,
i.e. that an element of `B` is integral over `R` iff it is an element of (the image of) `A`.
-/
class is_integral_closure (A R B : Type*) [comm_ring R] [comm_semiring A] [comm_ring B]
  [algebra R B] [algebra A B] : Prop :=
(algebra_map_injective [] : function.injective (algebra_map A B))
(is_integral_iff : ∀ {x : B}, is_integral R x ↔ ∃ y, algebra_map A B y = x)

instance integral_closure.is_integral_closure (R A : Type*) [comm_ring R] [comm_ring A]
  [algebra R A] : is_integral_closure (integral_closure R A) R A :=
⟨subtype.coe_injective, λ x, ⟨λ h, ⟨⟨x, h⟩, rfl⟩, by { rintro ⟨⟨_, h⟩, rfl⟩, exact h }⟩⟩

namespace is_integral_closure

variables {R A B : Type*} [comm_ring R] [comm_ring A] [comm_ring B]
variables [algebra R B] [algebra A B] [is_integral_closure A R B]

variables (R) {A} (B)
protected theorem is_integral [algebra R A] [is_scalar_tower R A B] (x : A) : is_integral R x :=
(is_integral_algebra_map_iff (algebra_map_injective A R B)).mp $
show is_integral R (algebra_map A B x), from is_integral_iff.mpr ⟨x, rfl⟩

theorem is_integral_algebra [algebra R A] [is_scalar_tower R A B] :
  algebra.is_integral R A :=
λ x, is_integral_closure.is_integral R B x

theorem no_zero_smul_divisors [algebra R A] [is_scalar_tower R A B] [no_zero_smul_divisors R B] :
  no_zero_smul_divisors R A :=
begin
  refine function.injective.no_zero_smul_divisors
      _ (is_integral_closure.algebra_map_injective A R B) (map_zero _) (λ _ _, _),
  simp only [algebra.algebra_map_eq_smul_one, is_scalar_tower.smul_assoc],
 end

variables {R} (A) {B}

/-- If `x : B` is integral over `R`, then it is an element of the integral closure of `R` in `B`. -/
noncomputable def mk' (x : B) (hx : is_integral R x) : A :=
classical.some (is_integral_iff.mp hx)

@[simp] lemma algebra_map_mk' (x : B) (hx : is_integral R x) :
  algebra_map A B (mk' A x hx) = x :=
classical.some_spec (is_integral_iff.mp hx)

@[simp] lemma mk'_one (h : is_integral R (1 : B) := is_integral_one) :
  mk' A 1 h = 1 :=
algebra_map_injective A R B $ by rw [algebra_map_mk', ring_hom.map_one]

@[simp] lemma mk'_zero (h : is_integral R (0 : B) := is_integral_zero) :
  mk' A 0 h = 0 :=
algebra_map_injective A R B $ by rw [algebra_map_mk', ring_hom.map_zero]

@[simp] lemma mk'_add (x y : B) (hx : is_integral R x) (hy : is_integral R y) :
  mk' A (x + y) (is_integral_add hx hy) = mk' A x hx + mk' A y hy :=
algebra_map_injective A R B $ by simp only [algebra_map_mk', ring_hom.map_add]

@[simp] lemma mk'_mul (x y : B) (hx : is_integral R x) (hy : is_integral R y) :
  mk' A (x * y) (is_integral_mul hx hy) = mk' A x hx * mk' A y hy :=
algebra_map_injective A R B $ by simp only [algebra_map_mk', ring_hom.map_mul]

@[simp] lemma mk'_algebra_map [algebra R A] [is_scalar_tower R A B] (x : R)
  (h : is_integral R (algebra_map R B x) := is_integral_algebra_map) :
  is_integral_closure.mk' A (algebra_map R B x) h = algebra_map R A x :=
algebra_map_injective A R B $ by rw [algebra_map_mk', ← is_scalar_tower.algebra_map_apply]

section lift

variables {R} (A B) {S : Type*} [comm_ring S] [algebra R S] [algebra S B] [is_scalar_tower R S B]
variables [algebra R A] [is_scalar_tower R A B] (h : algebra.is_integral R S)

/-- If `B / S / R` is a tower of ring extensions where `S` is integral over `R`,
then `S` maps (uniquely) into an integral closure `B / A / R`. -/
noncomputable def lift : S →ₐ[R] A :=
{ to_fun := λ x, mk' A (algebra_map S B x) (is_integral.algebra_map (h x)),
  map_one' := by simp only [ring_hom.map_one, mk'_one],
  map_zero' := by simp only [ring_hom.map_zero, mk'_zero],
  map_add' := λ x y, by simp_rw [← mk'_add, ring_hom.map_add],
  map_mul' := λ x y, by simp_rw [← mk'_mul, ring_hom.map_mul],
  commutes' := λ x, by simp_rw [← is_scalar_tower.algebra_map_apply, mk'_algebra_map] }

@[simp] lemma algebra_map_lift (x : S) : algebra_map A B (lift A B h x) = algebra_map S B x :=
algebra_map_mk' _ _ _

end lift

section equiv

variables (R A B) (A' : Type*) [comm_ring A'] [algebra A' B] [is_integral_closure A' R B]
variables [algebra R A] [algebra R A'] [is_scalar_tower R A B] [is_scalar_tower R A' B]

/-- Integral closures are all isomorphic to each other. -/
noncomputable def equiv : A ≃ₐ[R] A' :=
alg_equiv.of_alg_hom (lift _ B (is_integral_algebra R B)) (lift _ B (is_integral_algebra R B))
  (by { ext x, apply algebra_map_injective A' R B, simp })
  (by { ext x, apply algebra_map_injective A R B, simp })

@[simp] lemma algebra_map_equiv (x : A) : algebra_map A' B (equiv R A B A' x) = algebra_map A B x :=
algebra_map_lift _ _ _ _

end equiv

end is_integral_closure

end is_integral_closure

section algebra
open algebra
variables {R A B S T : Type*}
variables [comm_ring R] [comm_ring A] [comm_ring B] [comm_ring S] [comm_ring T]
variables [algebra A B] [algebra R B] (f : R →+* S) (g : S →+* T)

lemma is_integral_trans_aux (x : B) {p : A[X]} (pmonic : monic p) (hp : aeval x p = 0) :
  is_integral (adjoin R (↑(p.map $ algebra_map A B).frange : set B)) x :=
begin
  generalize hS : (↑(p.map $ algebra_map A B).frange : set B) = S,
  have coeffs_mem : ∀ i, (p.map $ algebra_map A B).coeff i ∈ adjoin R S,
  { intro i, by_cases hi : (p.map $ algebra_map A B).coeff i = 0,
    { rw hi, exact subalgebra.zero_mem _ },
    rw ← hS,
    exact subset_adjoin (coeff_mem_frange _ _ hi) },
  obtain ⟨q, hq⟩ : ∃ q : (adjoin R S)[X], q.map (algebra_map (adjoin R S) B) =
      (p.map $ algebra_map A B),
  { rw ← set.mem_range, exact (polynomial.mem_map_range _).2 (λ i, ⟨⟨_, coeffs_mem i⟩, rfl⟩) },
  use q,
  split,
  { suffices h : (q.map (algebra_map (adjoin R S) B)).monic,
    { refine monic_of_injective _ h,
      exact subtype.val_injective },
    { rw hq, exact pmonic.map _ } },
  { convert hp using 1,
    replace hq := congr_arg (eval x) hq,
    convert hq using 1; symmetry; apply eval_map },
end

variables [algebra R A] [is_scalar_tower R A B]

/-- If A is an R-algebra all of whose elements are integral over R,
and x is an element of an A-algebra that is integral over A, then x is integral over R.-/
lemma is_integral_trans (A_int : algebra.is_integral R A) (x : B) (hx : is_integral A x) :
  is_integral R x :=
begin
  rcases hx with ⟨p, pmonic, hp⟩,
  let S : set B := ↑(p.map $ algebra_map A B).frange,
  refine is_integral_of_mem_of_fg (adjoin R (S ∪ {x})) _ _ (subset_adjoin $ or.inr rfl),
  refine fg_trans (fg_adjoin_of_finite (finset.finite_to_set _) (λ x hx, _)) _,
  { rw [finset.mem_coe, frange, finset.mem_image] at hx,
    rcases hx with ⟨i, _, rfl⟩,
    rw coeff_map,
    exact map_is_integral (is_scalar_tower.to_alg_hom R A B) (A_int _) },
  { apply fg_adjoin_singleton_of_integral,
    exact is_integral_trans_aux _ pmonic hp }
end

/-- If A is an R-algebra all of whose elements are integral over R,
and B is an A-algebra all of whose elements are integral over A,
then all elements of B are integral over R.-/
lemma algebra.is_integral_trans (hA : algebra.is_integral R A) (hB : algebra.is_integral A B) :
  algebra.is_integral R B :=
λ x, is_integral_trans hA x (hB x)

lemma ring_hom.is_integral_trans (hf : f.is_integral) (hg : g.is_integral) :
  (g.comp f).is_integral :=
@algebra.is_integral_trans R S T _ _ _ g.to_algebra (g.comp f).to_algebra f.to_algebra
  (@is_scalar_tower.of_algebra_map_eq R S T _ _ _ f.to_algebra g.to_algebra (g.comp f).to_algebra
  (ring_hom.comp_apply g f)) hf hg

lemma ring_hom.is_integral_of_surjective (hf : function.surjective f) : f.is_integral :=
λ x, (hf x).rec_on (λ y hy, (hy ▸ f.is_integral_map : f.is_integral_elem x))

lemma is_integral_of_surjective (h : function.surjective (algebra_map R A)) :
  algebra.is_integral R A := (algebra_map R A).is_integral_of_surjective h

/-- If `R → A → B` is an algebra tower with `A → B` injective,
then if the entire tower is an integral extension so is `R → A` -/
lemma is_integral_tower_bot_of_is_integral (H : function.injective (algebra_map A B))
  {x : A} (h : is_integral R (algebra_map A B x)) : is_integral R x :=
begin
  rcases h with ⟨p, ⟨hp, hp'⟩⟩,
  refine ⟨p, ⟨hp, _⟩⟩,
  rw [is_scalar_tower.algebra_map_eq R A B, ← eval₂_map,
      eval₂_hom, ← ring_hom.map_zero (algebra_map A B)] at hp',
  rw [eval₂_eq_eval_map],
  exact H hp',
end

lemma ring_hom.is_integral_tower_bot_of_is_integral (hg : function.injective g)
  (hfg : (g.comp f).is_integral) : f.is_integral :=
λ x,
  @is_integral_tower_bot_of_is_integral R S T _ _ _ g.to_algebra (g.comp f).to_algebra f.to_algebra
  (@is_scalar_tower.of_algebra_map_eq R S T _ _ _ f.to_algebra g.to_algebra (g.comp f).to_algebra
  (ring_hom.comp_apply g f))  hg x (hfg (g x))

lemma is_integral_tower_bot_of_is_integral_field {R A B : Type*} [comm_ring R] [field A]
  [comm_ring B] [nontrivial B] [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B]
  {x : A} (h : is_integral R (algebra_map A B x)) : is_integral R x :=
is_integral_tower_bot_of_is_integral (algebra_map A B).injective h

lemma ring_hom.is_integral_elem_of_is_integral_elem_comp {x : T}
  (h : (g.comp f).is_integral_elem x) : g.is_integral_elem x :=
let ⟨p, ⟨hp, hp'⟩⟩ := h in ⟨p.map f, hp.map f, by rwa ← eval₂_map at hp'⟩

lemma ring_hom.is_integral_tower_top_of_is_integral (h : (g.comp f).is_integral) : g.is_integral :=
λ x, ring_hom.is_integral_elem_of_is_integral_elem_comp f g (h x)

/-- If `R → A → B` is an algebra tower,
then if the entire tower is an integral extension so is `A → B`. -/
lemma is_integral_tower_top_of_is_integral {x : B} (h : is_integral R x) : is_integral A x :=
begin
  rcases h with ⟨p, ⟨hp, hp'⟩⟩,
  refine ⟨p.map (algebra_map R A), ⟨hp.map (algebra_map R A), _⟩⟩,
  rw [is_scalar_tower.algebra_map_eq R A B, ← eval₂_map] at hp',
  exact hp',
end

lemma ring_hom.is_integral_quotient_of_is_integral {I : ideal S} (hf : f.is_integral) :
  (ideal.quotient_map I f le_rfl).is_integral :=
begin
  rintros ⟨x⟩,
  obtain ⟨p, ⟨p_monic, hpx⟩⟩ := hf x,
  refine ⟨p.map (ideal.quotient.mk _), ⟨p_monic.map _, _⟩⟩,
  simpa only [hom_eval₂, eval₂_map] using congr_arg (ideal.quotient.mk I) hpx
end

lemma is_integral_quotient_of_is_integral {I : ideal A} (hRA : algebra.is_integral R A) :
  algebra.is_integral (R ⧸ I.comap (algebra_map R A)) (A ⧸ I) :=
(algebra_map R A).is_integral_quotient_of_is_integral hRA

lemma is_integral_quotient_map_iff {I : ideal S} :
  (ideal.quotient_map I f le_rfl).is_integral ↔
    ((ideal.quotient.mk I).comp f : R →+* S ⧸ I).is_integral :=
begin
  let g := ideal.quotient.mk (I.comap f),
  have := ideal.quotient_map_comp_mk le_rfl,
  refine ⟨λ h, _, λ h, ring_hom.is_integral_tower_top_of_is_integral g _ (this ▸ h)⟩,
  refine this ▸ ring_hom.is_integral_trans g (ideal.quotient_map I f le_rfl) _ h,
  exact ring_hom.is_integral_of_surjective g ideal.quotient.mk_surjective,
end

/-- If the integral extension `R → S` is injective, and `S` is a field, then `R` is also a field. -/
lemma is_field_of_is_integral_of_is_field
  {R S : Type*} [comm_ring R] [nontrivial R] [comm_ring S] [is_domain S]
  [algebra R S] (H : algebra.is_integral R S) (hRS : function.injective (algebra_map R S))
  (hS : is_field S) : is_field R :=
begin
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, λ a ha, _⟩,
  -- Let `a_inv` be the inverse of `algebra_map R S a`,
  -- then we need to show that `a_inv` is of the form `algebra_map R S b`.
  obtain ⟨a_inv, ha_inv⟩ := hS.mul_inv_cancel (λ h, ha (hRS (trans h (ring_hom.map_zero _).symm))),

  -- Let `p : R[X]` be monic with root `a_inv`,
  -- and `q` be `p` with coefficients reversed (so `q(a) = q'(a) * a + 1`).
  -- We claim that `q(a) = 0`, so `-q'(a)` is the inverse of `a`.
  obtain ⟨p, p_monic, hp⟩ := H a_inv,
  use -∑ (i : ℕ) in finset.range p.nat_degree, (p.coeff i) * a ^ (p.nat_degree - i - 1),

  -- `q(a) = 0`, because multiplying everything with `a_inv^n` gives `p(a_inv) = 0`.
  -- TODO: this could be a lemma for `polynomial.reverse`.
  have hq : ∑ (i : ℕ) in finset.range (p.nat_degree + 1), (p.coeff i) * a ^ (p.nat_degree - i) = 0,
  { apply (injective_iff_map_eq_zero (algebra_map R S)).mp hRS,
    have a_inv_ne_zero : a_inv ≠ 0 := right_ne_zero_of_mul (mt ha_inv.symm.trans one_ne_zero),
    refine (mul_eq_zero.mp _).resolve_right (pow_ne_zero p.nat_degree a_inv_ne_zero),
    rw [eval₂_eq_sum_range] at hp,
    rw [ring_hom.map_sum, finset.sum_mul],
    refine (finset.sum_congr rfl (λ i hi, _)).trans hp,
    rw [ring_hom.map_mul, mul_assoc],
    congr,
    have : a_inv ^ p.nat_degree = a_inv ^ (p.nat_degree - i) * a_inv ^ i,
    { rw [← pow_add a_inv, tsub_add_cancel_of_le (nat.le_of_lt_succ (finset.mem_range.mp hi))] },
    rw [ring_hom.map_pow, this, ← mul_assoc, ← mul_pow, ha_inv, one_pow, one_mul] },

  -- Since `q(a) = 0` and `q(a) = q'(a) * a + 1`, we have `a * -q'(a) = 1`.
  -- TODO: we could use a lemma for `polynomial.div_X` here.
  rw [finset.sum_range_succ_comm, p_monic.coeff_nat_degree, one_mul, tsub_self, pow_zero,
      add_eq_zero_iff_eq_neg, eq_comm] at hq,
  rw [mul_comm, neg_mul, finset.sum_mul],
  convert hq using 2,
  refine finset.sum_congr rfl (λ i hi, _),
  have : 1 ≤ p.nat_degree - i := le_tsub_of_add_le_left (finset.mem_range.mp hi),
  rw [mul_assoc, ← pow_succ', tsub_add_cancel_of_le this]
end

lemma is_field_of_is_integral_of_is_field'
  {R S : Type*} [comm_ring R] [comm_ring S] [is_domain S] [algebra R S]
  (H : algebra.is_integral R S) (hR : is_field R) :
  is_field S :=
begin
  letI := hR.to_field,
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, λ x hx, _⟩,
  let A := algebra.adjoin R ({x} : set S),
  haveI : is_noetherian R A :=
  is_noetherian_of_fg_of_noetherian A.to_submodule (fg_adjoin_singleton_of_integral x (H x)),
  haveI : module.finite R A := module.is_noetherian.finite R A,
  obtain ⟨y, hy⟩ := linear_map.surjective_of_injective (@linear_map.mul_left_injective R A _ _ _ _
    ⟨x, subset_adjoin (set.mem_singleton x)⟩ (λ h, hx (subtype.ext_iff.mp h))) 1,
  exact ⟨y, subtype.ext_iff.mp hy⟩,
end

lemma algebra.is_integral.is_field_iff_is_field
  {R S : Type*} [comm_ring R] [nontrivial R] [comm_ring S] [is_domain S] [algebra R S]
  (H : algebra.is_integral R S) (hRS : function.injective (algebra_map R S)) :
  is_field R ↔ is_field S :=
⟨is_field_of_is_integral_of_is_field' H, is_field_of_is_integral_of_is_field H hRS⟩

end algebra

theorem integral_closure_idem {R : Type*} {A : Type*} [comm_ring R] [comm_ring A] [algebra R A] :
  integral_closure (integral_closure R A : set A) A = ⊥ :=
eq_bot_iff.2 $ λ x hx, algebra.mem_bot.2
⟨⟨x, @is_integral_trans _ _ _ _ _ _ _ _ (integral_closure R A).algebra
     _ integral_closure.is_integral x hx⟩, rfl⟩

section is_domain
variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain S] [algebra R S]

instance : is_domain (integral_closure R S) :=
infer_instance

theorem roots_mem_integral_closure {f : R[X]} (hf : f.monic) {a : S}
  (ha : a ∈ (f.map $ algebra_map R S).roots) : a ∈ integral_closure R S :=
⟨f, hf, (eval₂_eq_eval_map _).trans $ (mem_roots $ (hf.map _).ne_zero).1 ha⟩

end is_domain
