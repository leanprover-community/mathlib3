/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Integral closure of a subring.
-/

import ring_theory.adjoin linear_algebra.finsupp ring_theory.adjoin_root
import tactic.interactive

universes u v

open_locale classical
open polynomial submodule

section
variables (R : Type u) {A : Type v}
variables [comm_ring R] [comm_ring A]
variables [algebra R A]

def is_integral (x : A) : Prop :=
∃ p : polynomial R, monic p ∧ aeval R A x p = 0

variables {R}
theorem is_integral_algebra_map {x : R} : is_integral R (algebra_map A x) :=
⟨X - C x, monic_X_sub_C _,
by rw [alg_hom.map_sub, aeval_def, aeval_def, eval₂_X, eval₂_C, sub_self]⟩

theorem is_integral_of_subring {x : A} (T : set R) [is_subring T]
  (hx : is_integral T (algebra.comap.to_comap T R A x)) : is_integral R (x : A) :=
let ⟨p, hpm, hpx⟩ := hx in
⟨⟨p.support, λ n, (p.to_fun n).1,
  λ n, finsupp.mem_support_iff.trans (not_iff_not_of_iff
    ⟨λ H, have _ := congr_arg subtype.val H, this,
    λ H, subtype.eq H⟩)⟩,
have _ := congr_arg subtype.val hpm, this, hpx⟩

theorem is_integral_iff_is_integral_closure_finite {r : A} :
  is_integral R r ↔ ∃ s : set R, s.finite ∧
    is_integral (ring.closure s) (algebra.comap.to_comap (ring.closure s) R A r) :=
begin
  split; intro hr,
  { rcases hr with ⟨p, hmp, hpr⟩,
    exact ⟨_, set.finite_mem_finset _, p.restriction, subtype.eq hmp, hpr⟩ },
  rcases hr with ⟨s, hs, hsr⟩,
  exact is_integral_of_subring _ hsr
end

theorem fg_adjoin_singleton_of_integral (x : A) (hx : is_integral R x) :
  (algebra.adjoin R ({x} : set A) : submodule R A).fg :=
begin
  rcases hx with ⟨f, hfm, hfx⟩,
  existsi finset.image ((^) x) (finset.range (nat_degree f + 1)),
  apply le_antisymm,
  { rw span_le, intros s hs, rw finset.mem_coe at hs,
    rcases finset.mem_image.1 hs with ⟨k, hk, rfl⟩, clear hk,
    exact is_submonoid.pow_mem (algebra.subset_adjoin (set.mem_singleton _)) },
  intros r hr, change r ∈ algebra.adjoin R ({x} : set A) at hr,
  rw algebra.adjoin_singleton_eq_range at hr, rcases hr with ⟨p, rfl⟩,
  rw ← mod_by_monic_add_div p hfm,
  rw [alg_hom.map_add, alg_hom.map_mul, hfx, zero_mul, add_zero],
  have : degree (p %ₘ f) ≤ degree f := degree_mod_by_monic_le p hfm,
  generalize_hyp : p %ₘ f = q at this ⊢,
  rw [← sum_C_mul_X_eq q, aeval_def, eval₂_sum, finsupp.sum, mem_coe],
  refine sum_mem _ (λ k hkq, _),
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← algebra.smul_def],
  refine smul_mem _ _ (subset_span _),
  rw finset.mem_coe, refine finset.mem_image.2 ⟨_, _, rfl⟩,
  rw [finset.mem_range, nat.lt_succ_iff], refine le_of_not_lt (λ hk, _),
  rw [degree_le_iff_coeff_zero] at this,
  rw [finsupp.mem_support_iff] at hkq, apply hkq, apply this,
  exact lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 hk)
end

theorem fg_adjoin_of_finite {s : set A} (hfs : s.finite)
  (his : ∀ x ∈ s, is_integral R x) : (algebra.adjoin R s : submodule R A).fg :=
set.finite.induction_on hfs (λ _, ⟨finset.singleton 1, le_antisymm
  (span_le.2 $ set.singleton_subset_iff.2 $ is_submonoid.one_mem _)
  (show ring.closure _ ⊆ _, by rw set.union_empty; exact
    set.subset.trans (ring.closure_subset (set.subset.refl _))
    (λ y ⟨x, hx⟩, hx ▸ mul_one (algebra_map A x) ▸ algebra.smul_def x (1:A) ▸ (mem_coe _).2
      (submodule.smul_mem _ x $ subset_span $ or.inl rfl)))⟩)
(λ a s has hs ih his, by rw [← set.union_singleton, algebra.adjoin_union_coe_submodule]; exact
  fg_mul _ _ (ih $ λ i hi, his i $ set.mem_insert_of_mem a hi)
    (fg_adjoin_singleton_of_integral _ $ his a $ set.mem_insert a s)) his

theorem is_integral_of_noetherian' (H : is_noetherian R A) (x : A) :
  is_integral R x :=
begin
  let leval : @linear_map R (polynomial R) A _ _ _ _ _ := (aeval R A x).to_linear_map,
  let D : ℕ → submodule R A := λ n, (degree_le R n).map leval,
  let M := well_founded.min (is_noetherian_iff_well_founded.1 H)
    (set.range D) (set.ne_empty_of_mem ⟨0, rfl⟩),
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

theorem is_integral_of_noetherian (S : subalgebra R A)
  (H : is_noetherian R (S : submodule R A)) (x : A) (hx : x ∈ S) :
  is_integral R x :=
begin
  letI : algebra R S := S.algebra,
  letI : comm_ring S := S.comm_ring R A,
  suffices : is_integral R (⟨x, hx⟩ : S),
  { rcases this with ⟨p, hpm, hpx⟩,
    replace hpx := congr_arg subtype.val hpx,
    refine ⟨p, hpm, eq.trans _ hpx⟩,
    simp only [aeval_def, eval₂, finsupp.sum],
    rw ← finset.sum_hom subtype.val,
    { refine finset.sum_congr rfl (λ n hn, _),
      change _ = _ * _,
      rw is_semiring_hom.map_pow subtype.val, refl,
      split; intros; refl },
    refine { map_add := _, map_zero := _ }; intros; refl },
  refine is_integral_of_noetherian' H ⟨x, hx⟩
end

set_option class.instance_max_depth 100
theorem is_integral_of_mem_of_fg (S : subalgebra R A)
  (HS : (S : submodule R A).fg) (x : A) (hx : x ∈ S) : is_integral R x :=
begin
  cases HS with y hy,
  obtain ⟨lx, hlx1, hlx2⟩ :
    ∃ (l : A →₀ R) (H : l ∈ finsupp.supported R R ↑y), (finsupp.total A A R id) l = x,
  { rwa [←(@finsupp.mem_span_iff_total A A R _ _ _ id ↑y x), set.image_id ↑y, hy] },
  have : ∀ (jk : (↑(y.product y) : set (A × A))), jk.1.1 * jk.1.2 ∈ (span R ↑y : submodule R A),
  { intros jk,
    let j : ↥(↑y : set A) := ⟨jk.1.1, (finset.mem_product.1 jk.2).1⟩,
    let k : ↥(↑y : set A) := ⟨jk.1.2, (finset.mem_product.1 jk.2).2⟩,
    have hj : j.1 ∈ (span R ↑y : submodule R A) := subset_span j.2,
    have hk : k.1 ∈ (span R ↑y : submodule R A) := subset_span k.2,
    revert hj hk, rw hy, exact @is_submonoid.mul_mem A _ S _ j.1 k.1 },
  rw ← set.image_id ↑y at this,
  simp only [finsupp.mem_span_iff_total] at this,
  choose ly hly1 hly2,
  let S₀' : finset R := lx.frange ∪ finset.bind finset.univ (finsupp.frange ∘ ly),
  let S₀ : set R := ring.closure ↑S₀',
  refine is_integral_of_subring (ring.closure ↑S₀') _,
  letI : algebra S₀ (algebra.comap S₀ R A) := algebra.comap.algebra _ _ _,
  letI hmod : module S₀ (algebra.comap S₀ R A) := algebra.to_module,
  have : (span S₀ (insert 1 (↑y:set A) : set (algebra.comap S₀ R A)) : submodule S₀ (algebra.comap S₀ R A)) =
      (algebra.adjoin S₀ ((↑y : set A) : set (algebra.comap S₀ R A)) : subalgebra S₀ (algebra.comap S₀ R A)),
  { apply le_antisymm,
    { rw [span_le, set.insert_subset, mem_coe], split,
      change _ ∈ ring.closure _, exact is_submonoid.one_mem _, exact algebra.subset_adjoin },
    rw [algebra.adjoin_eq_span, span_le], intros r hr, refine monoid.in_closure.rec_on hr _ _ _,
    { intros r hr, exact subset_span (set.mem_insert_of_mem _ hr) },
    { exact subset_span (set.mem_insert _ _) },
    intros r1 r2 hr1 hr2 ih1 ih2,
    rw ← set.image_id (insert _ ↑y) at ih1 ih2,
    simp only [mem_coe, finsupp.mem_span_iff_total] at ih1 ih2,
    have ih1' := ih1, have ih2' := ih2,
    rcases ih1' with ⟨l1, hl1, rfl⟩, rcases ih2' with ⟨l2, hl2, rfl⟩,
    simp only [finsupp.total_apply, finsupp.sum_mul, finsupp.mul_sum, mem_coe],
    rw [finsupp.sum], refine sum_mem _ _, intros r2 hr2,
    rw [finsupp.sum], refine sum_mem _ _, intros r1 hr1,
    rw [algebra.mul_smul_comm, algebra.smul_mul_assoc],
    letI : module ↥S₀ A := hmod, refine smul_mem _ _ (smul_mem _ _ _),
    rcases hl1 hr1 with rfl | hr1,
    { change 1 * r2 ∈ _, rw one_mul r2, exact subset_span (hl2 hr2) },
    rcases hl2 hr2 with rfl | hr2,
    { change r1 * 1 ∈ _, rw mul_one, exact subset_span (set.mem_insert_of_mem _ hr1) },
    let jk : ↥(↑(finset.product y y) : set (A × A)) := ⟨(r1, r2), finset.mem_product.2 ⟨hr1, hr2⟩⟩,
    specialize hly2 jk, change _ = r1 * r2 at hly2, rw [id, id, ← hly2, finsupp.total_apply],
    rw [finsupp.sum], refine sum_mem _ _, intros z hz,
    have : ly jk z ∈ S₀,
    { apply ring.subset_closure,
      apply finset.mem_union_right, apply finset.mem_bind.2,
      exact ⟨jk, finset.mem_univ _, by convert finset.mem_image_of_mem _ hz⟩ },
    change @has_scalar.smul S₀ (algebra.comap S₀ R A) hmod.to_has_scalar ⟨ly jk z, this⟩ z ∈ _,
    exact smul_mem _ _ (subset_span (set.mem_insert_of_mem _ (hly1 _ hz))) },
  haveI : is_noetherian_ring ↥S₀ :=
  by { convert is_noetherian_ring_closure _ (finset.finite_to_set _), apply_instance },
  apply is_integral_of_noetherian
    (algebra.adjoin S₀ ((↑y : set A) : set (algebra.comap S₀ R A)) : subalgebra S₀ (algebra.comap S₀ R A))
    (is_noetherian_of_fg_of_noetherian _ ⟨insert 1 y, by rw finset.coe_insert; convert this⟩),
  show x ∈ ((algebra.adjoin S₀ ((↑y : set A) : set (algebra.comap S₀ R A)) :
      subalgebra S₀ (algebra.comap S₀ R A)) : submodule S₀ (algebra.comap S₀ R A)),
  rw [← hlx2, finsupp.total_apply, finsupp.sum], refine sum_mem _ _, intros r hr,
  rw ← this,
  have : lx r ∈ ring.closure ↑S₀' :=
    ring.subset_closure (finset.mem_union_left _ (by convert finset.mem_image_of_mem _ hr)),
  change @has_scalar.smul S₀ (algebra.comap S₀ R A) hmod.to_has_scalar ⟨lx r, this⟩ r ∈ _,
  rw finsupp.mem_supported at hlx1,
  exact smul_mem _ _ (subset_span (set.mem_insert_of_mem _ (hlx1 hr))),
end

theorem is_integral_of_mem_closure {x y z : A}
  (hx : is_integral R x) (hy : is_integral R y)
  (hz : z ∈ ring.closure ({x, y} : set A)) :
  is_integral R z :=
begin
  have := fg_mul _ _ (fg_adjoin_singleton_of_integral x hx) (fg_adjoin_singleton_of_integral y hy),
  rw [← algebra.adjoin_union_coe_submodule, set.union_singleton, insert] at this,
  exact is_integral_of_mem_of_fg (algebra.adjoin R {x, y}) this z
    (ring.closure_mono (set.subset_union_right _ _) hz)
end

theorem is_integral_zero : is_integral R (0:A) :=
algebra.map_zero R A ▸ is_integral_algebra_map

theorem is_integral_one : is_integral R (1:A) :=
algebra.map_one R A ▸ is_integral_algebra_map

theorem is_integral_add {x y : A}
  (hx : is_integral R x) (hy : is_integral R y) :
  is_integral R (x + y) :=
is_integral_of_mem_closure hx hy (is_add_submonoid.add_mem
  (ring.subset_closure (or.inr (or.inl rfl))) (ring.subset_closure (or.inl rfl)))

theorem is_integral_neg {x : A}
  (hx : is_integral R x) : is_integral R (-x) :=
is_integral_of_mem_closure hx hx (is_add_subgroup.neg_mem
  (ring.subset_closure (or.inl rfl)))

theorem is_integral_sub {x y : A}
  (hx : is_integral R x) (hy : is_integral R y) : is_integral R (x - y) :=
is_integral_add hx (is_integral_neg hy)

theorem is_integral_mul {x y : A}
  (hx : is_integral R x) (hy : is_integral R y) :
  is_integral R (x * y) :=
is_integral_of_mem_closure hx hy (is_submonoid.mul_mem
  (ring.subset_closure (or.inr (or.inl rfl))) (ring.subset_closure (or.inl rfl)))

variables (R A)
def integral_closure : subalgebra R A :=
{ carrier := { r | is_integral R r },
  subring :=
  { zero_mem := is_integral_zero,
    one_mem := is_integral_one,
    add_mem := λ _ _, is_integral_add,
    neg_mem := λ _, is_integral_neg,
    mul_mem := λ _ _, is_integral_mul },
  range_le := λ y ⟨x, hx⟩, hx ▸ is_integral_algebra_map }

theorem mem_integral_closure_iff_mem_fg {r : A} :
  r ∈ integral_closure R A ↔ ∃ M : subalgebra R A, (M : submodule R A).fg ∧ r ∈ M :=
⟨λ hr, ⟨algebra.adjoin R {r}, fg_adjoin_singleton_of_integral _ hr, algebra.subset_adjoin (or.inl rfl)⟩,
λ ⟨M, Hf, hrM⟩, is_integral_of_mem_of_fg M Hf _ hrM⟩

theorem integral_closure_idem : integral_closure (integral_closure R A : set A) A = ⊥ :=
begin
  rw lattice.eq_bot_iff, intros r hr,
  rcases is_integral_iff_is_integral_closure_finite.1 hr with ⟨s, hfs, hr⟩,
  apply algebra.mem_bot.2, refine ⟨⟨_, _⟩, rfl⟩,
  refine (mem_integral_closure_iff_mem_fg _ _).2 ⟨algebra.adjoin _ (subtype.val '' s ∪ {r}),
    algebra.fg_trans
      (fg_adjoin_of_finite (set.finite_image _ hfs)
        (λ y ⟨x, hx, hxy⟩, hxy ▸ x.2))
      _,
    algebra.subset_adjoin (or.inr (or.inl rfl))⟩,
  refine fg_adjoin_singleton_of_integral _ _,
  rcases hr with ⟨p, hmp, hpx⟩,
  refine ⟨to_subring (of_subring _ (of_subring _ p)) _ _, _, hpx⟩,
  { intros x hx, rcases finsupp.mem_frange.1 hx with ⟨h1, n, rfl⟩,
    change (coeff p n).1.1 ∈ ring.closure _,
    rcases ring.exists_list_of_mem_closure (coeff p n).2 with ⟨L, HL1, HL2⟩, rw ← HL2,
    clear HL2 hfs h1 hx n hmp hpx hr r p,
    induction L with hd tl ih, { exact is_add_submonoid.zero_mem _ },
    rw list.forall_mem_cons at HL1,
    rw [list.map_cons, list.sum_cons],
    refine is_add_submonoid.add_mem _ (ih HL1.2),
    cases HL1 with HL HL', clear HL' ih tl,
    induction hd with hd tl ih, { exact is_submonoid.one_mem _ },
    rw list.forall_mem_cons at HL,
    rw list.prod_cons,
    refine is_submonoid.mul_mem _ (ih HL.2),
    rcases HL.1 with hs | rfl,
    { exact algebra.subset_adjoin (set.mem_image_of_mem _ hs) },
    exact is_add_subgroup.neg_mem (is_submonoid.one_mem _) },
  replace hmp := congr_arg subtype.val hmp,
  replace hmp := congr_arg subtype.val hmp,
  exact subtype.eq hmp
end

end

section algebra
open algebra
variables {R : Type*} {A : Type*} {B : Type*}
variables [comm_ring R] [comm_ring A] [comm_ring B]
variables [algebra R A] [algebra A B]

set_option class.instance_max_depth 50

lemma is_integral_trans_aux (x : B) {p : polynomial A} (pmonic : monic p) (hp : aeval A B x p = 0)
  (S : set (comap R A B))
  (hS : S = (↑((finset.range (p.nat_degree + 1)).image
    (λ i, to_comap R A B (p.coeff i))) : set (comap R A B))) :
  is_integral (adjoin R S) (comap.to_comap R A B x) :=
begin
  have coeffs_mem : ∀ i, coeff (map (to_comap R A B) p) i ∈ adjoin R S,
  { intro i,
    by_cases hi : i ∈ finset.range (p.nat_degree + 1),
    { apply algebra.subset_adjoin, subst S,
      rw [finset.mem_coe, finset.mem_image, coeff_map],
      exact ⟨i, hi, rfl⟩ },
    { rw [finset.mem_range, not_lt] at hi,
      rw [coeff_map, coeff_eq_zero_of_nat_degree_lt hi, alg_hom.map_zero],
      exact submodule.zero_mem (adjoin R S : submodule R (comap R A B)) } },
  obtain ⟨q, hq⟩ : ∃ q : polynomial (adjoin R S), q.map (algebra_map (comap R A B)) =
      (p.map $ to_comap R A B),
  { rw [← set.mem_range], dsimp only,
    apply (polynomial.mem_map_range _).2,
    { intros i, specialize coeffs_mem i, rw ← subalgebra.mem_coe at coeffs_mem,
      convert coeffs_mem, exact subtype.val_range },
    { apply is_ring_hom.is_semiring_hom } },
  use q,
  split,
  { suffices h : (q.map (algebra_map (comap R A B))).monic,
    { refine @monic_of_injective _ _ _ _ _
        (by exact is_ring_hom.is_semiring_hom _) _ _ h,
      exact subtype.val_injective },
    { rw hq, exact monic_map _ pmonic } },
  { convert hp using 1,
    replace hq := congr_arg (eval (comap.to_comap R A B x)) hq,
    convert hq using 1; symmetry, swap,
    exact eval_map _ _,
    refine @eval_map _ _ _ _ _ _ (by exact is_ring_hom.is_semiring_hom _) _ },
end

/-- If A is an R-algebra all of whose elements are integral over R,
and x is an element of an A-algebra that is integral over A, then x is integral over R.-/
lemma is_integral_trans (A_int : ∀ x : A, is_integral R x) (x : B) (hx : is_integral A x) :
  is_integral R (comap.to_comap R A B x) :=
begin
  rcases hx with ⟨p, pmonic, hp⟩,
  let S : set (comap R A B) :=
    (↑((finset.range (p.nat_degree + 1)).image
      (λ i, to_comap R A B (p.coeff i))) : set (comap R A B)),
  refine is_integral_of_mem_of_fg (adjoin R (S ∪ {comap.to_comap R A B x})) _ _ _,
  swap, { apply subset_adjoin, simp },
  apply fg_trans,
  { apply fg_adjoin_of_finite, { apply finset.finite_to_set },
    intros x hx,
    rw [finset.mem_coe, finset.mem_image] at hx,
    rcases hx with ⟨i, hi, rfl⟩,
    rcases A_int (p.coeff i) with ⟨q, hq, hqx⟩,
    use [q, hq],
    replace hqx := congr_arg (to_comap R A B : A → (comap R A B)) hqx,
    rw alg_hom.map_zero at hqx,
    convert hqx using 1,
    symmetry, exact polynomial.hom_eval₂ _ _ _ _ },
  { apply fg_adjoin_singleton_of_integral,
    exact is_integral_trans_aux _ pmonic hp _ rfl }
end

/-- If A is an R-algebra all of whose elements are integral over R,
and B is an A-algebra all of whose elements are integral over A,
then all elements of B are integral over R.-/
lemma algebra.is_integral_trans (A_int : ∀ x : A, is_integral R x)(B_int : ∀ x:B, is_integral A x) :
  ∀ x:(comap R A B), is_integral R x :=
λ x, is_integral_trans A_int x (B_int x)

lemma is_integral_of_is_integral_to_comap {x : A} (h : is_integral R (to_comap R A B x)) :
  is_integral R x :=
begin
  rcases h with ⟨p, hm, h0⟩,
  existsi [p, hm],
  change eval₂ (algebra_map (comap R A B)) (to_comap R A B x) p = 0 at h0,
  rw [to_comap_apply] at h0,
  change eval₂ (algebra_map (comap R A B)) _ p = 0 at h0,
  change eval₂ (algebra_map A) x p = 0,
  sorry
end

end algebra



/-- The `generic polynomial` over a commutative ring `R` of degree `n` is the monic polynomial
`(X - X₁) * ... * (X - Xₙ)` where `X₁,...,Xₙ` are variables. -/
noncomputable def generic_polynomial (R : Type u) [comm_ring R] (n : ℕ) :
  polynomial (mv_polynomial (fin n) R) :=
finset.univ.prod (λ i : fin n, (X : polynomial (mv_polynomial (fin n) R)) - C (mv_polynomial.X i))

def symmetric_relations {R : Type u} [comm_ring R] (n : ℕ) (p : polynomial R) :
  set (mv_polynomial (fin n) R) :=
set.image (coeff (p.map mv_polynomial.C - generic_polynomial R n) ∘ @fin.val n) set.univ

def splitting_ring {R : Type u} [comm_ring R] {p : polynomial R} (hp : monic p) : Type* :=
ideal.quotient $ ideal.span $ symmetric_relations (nat_degree p) p

variables {R : Type u} [comm_ring R]
variables {p : polynomial R} (hp : monic p)

namespace splitting_ring

noncomputable instance : comm_ring (splitting_ring hp) := ideal.quotient.comm_ring _

noncomputable instance : algebra R (splitting_ring hp) :=
algebra.of_ring_hom (ideal.quotient.mk _ ∘ mv_polynomial.C) (is_ring_hom.comp _ _)

lemma splits : ∃ s : finset (splitting_ring hp),
  p.map (algebra_map $ splitting_ring hp) = s.prod (λ x, X - C x) :=
⟨finset.univ.image $ ideal.quotient.mk _ ∘ mv_polynomial.X,
begin
  ext n,
  apply eq_of_sub_eq_zero,
  rw [finset.prod_image, ←coeff_sub],
  conv_lhs { congr, congr, skip, congr, skip, funext,
    rw [←map_C (ideal.quotient.mk _), ←map_X (ideal.quotient.mk _), ←map_sub], },
  --{ intros x _ y _, sorry } --map is injective
end⟩

end splitting_ring

/-structure splitting_ring' {R : Type u} [comm_ring R] {p : polynomial R} (hp : monic p) :=
(A : Type*) [ring : comm_ring A] [algebra : algebra R A]
(s : multiset A)
(splits : p.map (algebra_map A) = (s.map (λ x, X - C x)).prod)-/

/-structure splitting_ring {R : Type u} [comm_ring R] (p : polynomial R) :=
(S : Type*) [ring : comm_ring S] [algebra : algebra R S]
(s : finset S)
(splits : p.map (algebra_map S) = C (algebra_map S $ p.leading_coeff) *
  (s.prod (λ x, (X - C x) ^ root_multiplicity x (p.map $ algebra_map S))))

variables {R : Type u} [comm_ring R] (p : polynomial R)

instance splitting_ring.comm_ring (T : splitting_ring p) : comm_ring T.S := T.ring
instance splitting_ring.algebra' (T : splitting_ring p) : algebra R T.S := T.algebra

instance adjoin_root.algebra (f : polynomial R) : algebra R (adjoin_root f) := sorry

noncomputable def div_by_root (x : R) : polynomial R :=
p /ₘ (X - C x) ^ p.root_multiplicity x

lemma div_by_root_mul (x : R) : (div_by_root p x) * (X - C x) ^ p.root_multiplicity x = p := sorry

lemma div_by_root_map (x : R) {S : Type v} [comm_ring S] (i : R → S) :
  div_by_root (p.map i) (i x) = (div_by_root p x).map i := sorry

lemma leading_coeff_div_by_root (x : R) : leading_coeff (div_by_root p x) = leading_coeff p := sorry

lemma div_by_root_root_multiplicity {x y : R} (h : x ≠ y) :
  (div_by_root p x).root_multiplicity y = p.root_multiplicity y := sorry

lemma div_by_root_root_multiplicity_map {x : R} {S : Type v} [comm_ring S] (i : R → S) {y : S} (h : i x ≠ y) :
  ((div_by_root p x).map i).root_multiplicity y = (p.map i).root_multiplicity y := sorry

lemma comm_ring.leading_coeff_map {S : Type v} [comm_ring S] (i : R → S) [is_semiring_hom i] :
leading_coeff (p.map i) = i (leading_coeff p) := sorry

lemma root_multiplicity_map (x : R) {S : Type v} [comm_ring S] (i : R → S) [is_semiring_hom i] :
p.root_multiplicity x = (p.map i).root_multiplicity (i x) := sorry


variables (T : splitting_ring (div_by_root (p.map (algebra_map $ adjoin_root p)) adjoin_root.root))

noncomputable instance algebra_aux : algebra R T.S :=
algebra.of_ring_hom (algebra_map _ ∘ algebra_map (adjoin_root p)) (is_ring_hom.comp _ _)

--#check (algebra_map T.S : adjoin_root p → T.S)
#check (adjoin_root.root : adjoin_root p)
#check insert _ T.s

--#check insert ((algebra_map T.S : adjoin_root p → T.S) adjoin_root.root) T.s

--hint
instance splitting_ring.algebra'2 (T : splitting_ring p) : algebra R T.S := T.algebra

lemma splitting_ring.exists_aux : p.map (algebra_map T.S) = C (algebra_map T.S $ p.leading_coeff) *
    finset.prod (insert ((algebra_map T.S : adjoin_root p → T.S) adjoin_root.root) T.s)
      (λ (x : T.S), (X - C x) ^ root_multiplicity x (p.map $ algebra_map T.S)) :=
begin
  let x : adjoin_root p := adjoin_root.root,
  have h : algebra_map (T.S) x ∉ T.s, from sorry,
  conv_lhs { rw [←div_by_root_mul (p.map $ algebra_map T.S) (algebra_map T.S x)] },
  rw [finset.prod_insert h, mul_comm, ←mul_assoc, mul_comm (C _), mul_assoc],
  congr,
  change div_by_root (map (λ (x : R), algebra_map (T.S) (algebra_map (adjoin_root p) x)) p) _ = _,
  rw [←polynomial.map_map (algebra_map $ adjoin_root p), div_by_root_map, T.splits],
  rw [leading_coeff_div_by_root, comm_ring.leading_coeff_map],
  --rw [←div_by_root_map],
  conv_lhs { congr, skip, congr, skip, funext, rw [div_by_root_root_multiplicity_map _ _ sorry] },
  sorry,
  apply_instance
end

def splitting_ring.exists : Π {R : Type u} [hc : comm_ring R]
  (p : by exactI polynomial R), @splitting_ring R hc p
| R hc p :=
let x : by exactI adjoin_root p := by exactI adjoin_root.root in
let T := by exactI splitting_ring.exists (div_by_root (p.map $ algebra_map _) x) in
by exactI splitting_ring.mk T.S (insert (algebra_map T.S x) T.s) (splitting_ring.exists_aux _ _)
using_well_founded { _ }
--begin
  --letI := hc,
  --let x : adjoin_root p := adjoin_root.root,
  --let T := splitting_ring.exists (div_by_root (p.map $ algebra_map _) x),
  --letI : algebra R T.S := algebra.of_ring_hom (algebra_map _ ∘ algebra_map (adjoin_root p)) (is_ring_hom.comp _ _),
  --have h : algebra_map (T.S) x ∉ T.s, from sorry,
  --exact splitting_ring.mk T.S (insert (algebra_map T.S x) T.s) (splitting_ring.exists_aux _ _),
  /-conv_lhs { rw [←div_by_root_mul (p.map $ algebra_map T.S) (algebra_map T.S x)] },
  rw [finset.prod_insert h, mul_comm, ←mul_assoc, mul_comm (C _), mul_assoc],
  congr,
  change div_by_root (map (λ (x : R), algebra_map (T.S) (algebra_map S x)) p) _ = _,
  rw [←polynomial.map_map (algebra_map S), div_by_root_map, T.splits],
  rw [leading_coeff_div_by_root, comm_ring.leading_coeff_map],
  --rw [←div_by_root_map],
  conv_lhs { congr, skip, congr, skip, funext, rw [div_by_root_root_multiplicity_map _ _ sorry] },
-/
--end


-/
--using_well_founded {  }

/-variables (R : Type u) {A : Type v}
variables [comm_ring R] [comm_ring A]
variables [algebra R A]
set_option class.instance_max_depth 100

lemma degree_lt_wf' : well_founded (λp q : (Σ R : (Σ α, comm_semiring α), @polynomial R.1 R.2),
  @degree p.1.1 p.1.2 p.2 < @degree q.1.1 q.1.2 q.2) := sorry

instance (f : polynomial R): algebra R (adjoin_root f) := sorry

lemma monic_C_iff {a : R} : monic (C a) ↔ a = 1 := sorry

structure splitting_ring_aux {R : Type u} [comm_ring R] (p : polynomial R) (n : ℕ) :=
(S : Type*) [ring : comm_ring S] [algebra : algebra R S]
(s : multiset S)
(card : s.card = n)
(dvd : (s.map (λ x, X - C x)).prod ∣ p.map (algebra_map S))

#check Σ' (G : Type u) [hc : comm_ring G], polynomial G
#check Σ (G : Type u) (hc : comm_ring G), polynomial G
#check @nat_degree

structure aux :=
(R : Type u) [hc : comm_ring R]
(p : polynomial R)
(nonzero : p ≠ 0)

instance test (x : aux): comm_ring x.R := x.hc

lemma aux_lt_wf : well_founded (λ x y : aux, degree x.p < degree y.p) :=
inv_image.wf (λ x, degree x.p) (with_bot.well_founded_lt nat.lt_wf)

--instance aux_wf : has_well_founded aux := ⟨_, aux_lt_wf⟩

def splitting_ring (a : aux) : Type* :=
well_founded.recursion aux_lt_wf a (
begin
  intros x ih,
  let S := adjoin_root (x.p),
  let q := ((x.p).map (algebra_map S : x.R → S)) /ₘ
    (X - C adjoin_root.root) ^ ((x.p).map (algebra_map S : x.R → S)).root_multiplicity adjoin_root.root,
  have : q ≠ 0, from sorry,
  refine ih ⟨S, q, this⟩ _,
  { refine lt_of_lt_of_le (degree_div_by_monic_lt _ _ _ _) (le_of_eq _),
    apply monic_pow, exact monic_X_sub_C _,
    sorry,
    sorry,
    refine degree_map_eq_of_leading_coeff_ne_zero _ _, sorry }
end)

def splitting_ring_aux.exists_aux (R : Type*) [comm_ring R] {p : polynomial R} :
  ∀ n : ℕ, splitting_ring_aux p n
| 0 := sorry
| (n+1) := by {
  let A := splitting_ring_aux.exists_aux n;
  let S := A.S,
  letI := A.ring,
  letI := A.algebra,
  let pS := p.map (algebra_map S),
  let q := pS /ₘ (A.s.map (λ x, X - C x)).prod,
  let T := adjoin_root q,
  letI : algebra R T := sorry,
  let pT := p.map (algebra_map T),
  let x := adjoin_root.root,
  let s' := (multiset.repeat x $ pT.root_multiplicity x) ∪ (A.s.map (algebra_map T)),
  refine splitting_ring_aux.mk T s' _ _,
  /-{ rw [multiset.card_cons, multiset.card_map, A.card] },
  { rw [multiset.map_cons, multiset.prod_cons],
    have : p.map (algebra_map T) =
      (X - C x) ^ pT.root_multiplicity x * (pT /ₘ (X - C x) ^ pT.root_multiplicity x),
      sorry,
    rw [this],
    refine mul_dvd_mul _ _, sorry, sorry

   }-/
}


noncomputable def splitting_ring'.exists_aux2 (R : Type*) [comm_ring R] :
  ∀ (n : ℕ) {p : polynomial R}, monic p → p.degree = n → splitting_ring' p
| 0 p hm h := by { rw [with_bot.coe_zero] at h,
  have h1 : p = 1, { rw [eq_C_of_degree_eq_zero h] at ⊢ hm, rw [monic_C_iff] at hm, rw [hm, C_1] },
  rw [h1],
  refine splitting_ring'.mk R 0 _,
  rw [map_one, multiset.map_zero, multiset.prod_zero] }
| (n+1) p hm h := by {
  let S := adjoin_root p,
  let pS := p.map (algebra_map S),
  have : monic pS, from monic_map _ hm,
  have : pS.eval adjoin_root.root = 0, from sorry,
  let q := pS /ₘ ((X - C adjoin_root.root) ^ pS.root_multiplicity adjoin_root.root),
  have hmq : monic q, from sorry,
  have hq : degree q = nat_degree q, from sorry,--degree_eq_nat_degree (ne_zero_of_monic hqm), --S is nonzero
  have hl : degree q < degree p, from sorry,
  let T := splitting_ring'.exists_aux2 (nat_degree q),
}


--well_founded.recursion degree_lt_wf' begin  end --(sigma.mk (sigma.mk R _) p)
--  sorry
  /-(λ x h, begin
    let S := adjoin_root x,
    let xS := x.map (algebra_map S),
    have : xS.eval adjoin_root.root = 0, from sorry,

   end)-/

def splitting_ring'.exists (p : polynomial R) : splitting_ring' p :=
well_founded.recursion polynomial.degree_lt_wf p
  (λ x h, begin
    let S := adjoin_root x,
    let xS := x.map (algebra_map S),
    have : xS.eval adjoin_root.root = 0, from sorry,

   end)

def splitting_ring {p : polynomial R} (hp : monic p) : Type := sorry

variables {p : polynomial A} (hp : monic p)

instance splitting_ring.is_comm_ring : comm_ring (splitting_ring hp) := sorry

instance splitting_ring.algebra : algebra A (splitting_ring hp) := sorry

def splitting_ring.splitting_set : multiset (splitting_ring hp) := sorry

/-- A polynomial splits over its splitting ring. -/
lemma splitting_ring.splits :
 p.map (algebra_map $ splitting_ring hp) = ((splitting_ring.splitting_set hp).map (λ a, X - C a)).prod :=
sorry


--TODO: move
lemma multiset.prod_zero_of_zero_mem {α : Type*} [comm_ring α] {s : multiset α} (h : (0:α) ∈ s) :
  s.prod = 0 := sorry

--TODO: move
lemma multiset.map_prod {α β : Type*} [comm_monoid α] [comm_monoid β] (s : multiset α) (f : α → β)
  [is_monoid_hom f] : (s.map f).prod = f s.prod := sorry

lemma splitting_ring.aeval {x : splitting_ring hp} (hx : x ∈ splitting_ring.splitting_set hp) :
  (aeval A (splitting_ring hp) x).to_fun p = 0 :=
calc p.eval₂ (algebra_map $ splitting_ring hp) x
    = (p.map $ algebra_map $ splitting_ring hp).eval x : eq.symm $ eval₂_map _ _ _
... = ((splitting_ring.splitting_set hp).map (λ a, X - C a)).prod.eval x : by rw [splitting_ring.splits]
... = ((splitting_ring.splitting_set hp).map (λ a, eval x (X - C a))).prod : sorry --eval_prod
... = 0 : multiset.prod_zero_of_zero_mem begin rw [multiset.mem_map],
  refine ⟨x, hx, _⟩, rw [eval_sub, eval_X, eval_C, sub_self] end

lemma mem_coeff_prod_X_sub_C {s : multiset A} {M : subalgebra R A} :
  (∀ x ∈ s, x ∈ M) → ∀ n, coeff (s.map (λ x, X - C x)).prod n ∈ M :=
multiset.induction_on s
  (λ _ _, by { rw [multiset.map_zero, multiset.prod_zero, coeff_one],
    split_ifs, exact M.subring.one_mem, exact M.subring.zero_mem })
  (λ x s hs h n, by {
    rw [multiset.map_cons, multiset.prod_cons, coeff_mul],
    change _ ∈ (M : submodule R A),
    refine submodule.sum_mem _ _,
    intros c _,
    change _ ∈ M.carrier,
    apply M.subring.mul_mem,
    { rw [coeff_sub, coeff_X, coeff_C], apply is_add_subgroup.sub_mem,
      all_goals { split_ifs }, exact M.subring.one_mem, exact M.subring.zero_mem,
      refine h _ (multiset.mem_cons_self _ _), exact M.subring.zero_mem },
    { exact hs (λ x hx, h _ $ multiset.mem_cons_of_mem hx) _ } })

--TODO: move
lemma mem_adjoin_of_mem {s : set A} {x : A} (h : x ∈ s) : x ∈ algebra.adjoin R s := sorry

lemma is_integral_coeff_of_is_integral_coeff_mul_right {p q : polynomial A} (hp : monic p) (hq : monic q)
  (h : ∀ n, is_integral R (coeff (p * q) n)) (n : ℕ) : is_integral R (p.coeff n) :=
begin
  let A' := algebra.comap R A (splitting_ring hp),
  haveI : algebra A A' := splitting_ring.algebra hp,
  let s := splitting_ring.splitting_set hp, -- s is the multiset of roots of p in A'
  let R':= integral_closure R A',
  let pqR' : polynomial R' := ((p * q).map $ algebra.to_comap R A (splitting_ring hp)).to_subring R' _,
  have hR' : ∀ x ∈ s, is_integral R (algebra.comap.to_comap R A _ x),
  { intros x hx,
    have h : x ∈ integral_closure (R' : set A') A',
    { refine ⟨pqR', _, _⟩,
      { rw [monic_to_subring], exact monic_map _ (monic_mul hp hq) },
      { exact calc eval₂ id x ((p * q).map (algebra_map A'))
          = eval₂ (algebra_map A') x p * _ :
          by { rw [map_mul (algebra_map A'), eval₂_mul, eval₂_map (algebra_map A')], refl,
            all_goals { apply_instance } }
      ... = (aeval A (splitting_ring hp) x).to_fun p * _ : rfl
      ... = 0 : by rw [splitting_ring.aeval hp hx, zero_mul] } },
    rw [integral_closure_idem] at h, sorry },
  let M : subalgebra R A' := algebra.adjoin R s.to_finset.to_set,
  have hM : M ≤ R', from algebra.adjoin_le (λ x hx, hR' x (multiset.mem_to_finset.mp hx)),
  have : algebra_map (splitting_ring hp) (coeff p n) ∈ M,
  { rw [←coeff_map (algebra_map _), splitting_ring.splits hp],
    --rw [←subalgebra.mem_coe, show ↑M = ↑M.to_submodule, from sorry],
    refine mem_coeff_prod_X_sub_C R (λ x hx, mem_adjoin_of_mem R _) n,
    exact multiset.mem_to_finset.mpr hx,
    apply_instance },
  exact is_integral_of_is_integral_to_comap (hM this),
  sorry
end

lemma is_integral_coeff_of_is_integral_coeff_mul_left {p q : polynomial A} (hp : monic p) (hq : monic q)
  (h : ∀ n, is_integral R (coeff (q * p) n)) (n : ℕ) : is_integral R (p.coeff n) :=
is_integral_coeff_of_is_integral_coeff_mul_right R hp hq (mul_comm q p ▸ h) n

/-
lemma of_is_integrally_closed (integrally_closed : integral_closure R A = ⊥) {f g : polynomial A}
 (hf : monic f) (hg : monic g) (hr : ∀ n, coeff (f * g) n ∈ set.range (algebra_map A : R → A)) :
 ∀ n, coeff f n ∈ set.range (algebra_map A : R → A) ∧ coeff g n ∈ set.range (algebra_map A : R → A) :=
begin
  intro n,
  let hr := hr n,
  rw [set.mem_range] at ⊢ hr, rw [set.mem_range],
  cases hr with x hx,
  have : ∀ n, is_integral R (coeff (f * g) n),
  { intro n,
    have := hr n,
    rw [set.mem_range] at this,
    cases this with x hx,
    rw [←hx],
    exact is_integral_algebra_map },
  have h : ∀ n, is_integral R (f.coeff n) ∧ is_integral R (g.coeff n), from
    is_integral_coeff_of_is_integral_coeff_mul R A hf hg this,
  exact ⟨⟨h n, begin  end⟩, sorry⟩

end
-/-/
