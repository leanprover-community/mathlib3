/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ring_theory.algebra_tower

/-!
# Integral closure of a subring.
-/
universes u v w

open_locale classical
open polynomial submodule

section
variables (R : Type u) {A : Type v} {B : Type w}
variables [comm_ring R] [comm_ring A] [comm_ring B]
variables [algebra R A] [algebra R B]

/-- An element `x` of an algebra `A` over a commutative ring `R` is said to be *integral*,
if it is a root of some monic polynomial `p : polynomial R`. -/
def is_integral (x : A) : Prop :=
∃ p : polynomial R, monic p ∧ aeval x p = 0

variables {R}
theorem is_integral_algebra_map {x : R} : is_integral R (algebra_map R A x) :=
⟨X - C x, monic_X_sub_C _,
by rw [alg_hom.map_sub, aeval_def, aeval_def, eval₂_X, eval₂_C, sub_self]⟩

theorem is_integral_alg_hom (f : A →ₐ[R] B) {x : A} (hx : is_integral R x) : is_integral R (f x) :=
let ⟨p, hp, hpx⟩ := hx in ⟨p, hp, by rw [aeval_alg_hom_apply, hpx, f.map_zero]⟩

theorem is_integral_of_subring {x : A} (T : set R) [is_subring T]
  (hx : is_integral T x) : is_integral R x :=
let ⟨p, hpm, hpx⟩ := hx in
⟨⟨p.support, λ n, (p.to_fun n).1,
  λ n, finsupp.mem_support_iff.trans (not_iff_not_of_iff
    ⟨λ H, have _ := congr_arg subtype.val H, this,
    λ H, subtype.eq H⟩)⟩,
have _ := congr_arg subtype.val hpm, this, hpx⟩

theorem is_integral_iff_is_integral_closure_finite {r : A} :
  is_integral R r ↔ ∃ s : set R, s.finite ∧ is_integral (ring.closure s) r :=
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
  rw algebra.adjoin_singleton_eq_range at hr,
  rcases hr with ⟨p, rfl⟩,
  rw ← mod_by_monic_add_div p hfm,
  rw [alg_hom.map_add, alg_hom.map_mul, hfx, zero_mul, add_zero],
  have : degree (p %ₘ f) ≤ degree f := degree_mod_by_monic_le p hfm,
  generalize_hyp : p %ₘ f = q at this ⊢,
  rw [← sum_C_mul_X_eq q, aeval_def, eval₂_sum, finsupp.sum],
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
set.finite.induction_on hfs (λ _, ⟨{1}, submodule.ext $ λ x,
  by { erw [algebra.adjoin_empty, finset.coe_singleton, ← one_eq_span, one_eq_map_top,
      map_top, linear_map.mem_range, algebra.mem_bot], refl }⟩)
(λ a s has hs ih his, by rw [← set.union_singleton, algebra.adjoin_union_coe_submodule]; exact
  fg_mul _ _ (ih $ λ i hi, his i $ set.mem_insert_of_mem a hi)
    (fg_adjoin_singleton_of_integral _ $ his a $ set.mem_insert a s)) his

theorem is_integral_of_noetherian' (H : is_noetherian R A) (x : A) :
  is_integral R x :=
begin
  let leval : @linear_map R (polynomial R) A _ _ _ _ _ := (aeval x).to_linear_map,
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
    rw ← p.support.sum_hom subtype.val,
    { refine finset.sum_congr rfl (λ n hn, _),
      change _ = _ * _,
      rw is_semiring_hom.map_pow coe, refl,
      split; intros; refl },
    refine { map_add := _, map_zero := _ }; intros; refl },
  refine is_integral_of_noetherian' H ⟨x, hx⟩
end

theorem is_integral_of_mem_of_fg (S : subalgebra R A)
  (HS : (S : submodule R A).fg) (x : A) (hx : x ∈ S) : is_integral R x :=
begin
  cases HS with y hy,
  obtain ⟨lx, hlx1, hlx2⟩ :
    ∃ (l : A →₀ R) (H : l ∈ finsupp.supported R R ↑y), (finsupp.total A A R id) l = x,
  { rwa [←(@finsupp.mem_span_iff_total A A R _ _ _ id ↑y x), set.image_id ↑y, hy] },
  have hyS : ∀ {p}, p ∈ y → p ∈ S := λ p hp, show p ∈ (S : submodule R A),
    by { rw ← hy, exact subset_span hp },
  have : ∀ (jk : (↑(y.product y) : set (A × A))), jk.1.1 * jk.1.2 ∈ (S : submodule R A) :=
    λ jk, S.mul_mem (hyS (finset.mem_product.1 jk.2).1) (hyS (finset.mem_product.1 jk.2).2),
  rw [← hy, ← set.image_id ↑y] at this, simp only [finsupp.mem_span_iff_total] at this,
  choose ly hly1 hly2,
  let S₀ : set R := ring.closure ↑(lx.frange ∪ finset.bind finset.univ (finsupp.frange ∘ ly)),
  refine is_integral_of_subring S₀ _,
  have : span S₀ (insert 1 ↑y : set A) * span S₀ (insert 1 ↑y : set A) ≤ span S₀ (insert 1 ↑y : set A),
  { rw span_mul_span, refine span_le.2 (λ z hz, _),
    rcases set.mem_mul.1 hz with ⟨p, q, rfl | hp, hq, rfl⟩,
    { rw one_mul, exact subset_span hq },
    rcases hq with rfl | hq,
    { rw mul_one, exact subset_span (or.inr hp) },
    erw ← hly2 ⟨(p, q), finset.mem_product.2 ⟨hp, hq⟩⟩,
    rw [finsupp.total_apply, finsupp.sum],
    refine (span S₀ (insert 1 ↑y : set A)).sum_mem (λ t ht, _),
    have : ly ⟨(p, q), finset.mem_product.2 ⟨hp, hq⟩⟩ t ∈ S₀ :=
    ring.subset_closure (finset.mem_union_right _ $ finset.mem_bind.2
      ⟨⟨(p, q), finset.mem_product.2 ⟨hp, hq⟩⟩, finset.mem_univ _,
        finsupp.mem_frange.2 ⟨finsupp.mem_support_iff.1 ht, _, rfl⟩⟩),
    change (⟨_, this⟩ : S₀) • t ∈ _, exact smul_mem _ _ (subset_span $ or.inr $ hly1 _ ht) },
  haveI : is_subring (span S₀ (insert 1 ↑y : set A) : set A) :=
  { one_mem := subset_span $ or.inl rfl,
    mul_mem := λ p q hp hq, this $ mul_mem_mul hp hq,
    zero_mem := (span S₀ (insert 1 ↑y : set A)).zero_mem,
    add_mem := λ _ _, (span S₀ (insert 1 ↑y : set A)).add_mem,
    neg_mem := λ _, (span S₀ (insert 1 ↑y : set A)).neg_mem },
  have : span S₀ (insert 1 ↑y : set A) = algebra.adjoin S₀ (↑y : set A),
  { refine le_antisymm (span_le.2 $ set.insert_subset.2
        ⟨(algebra.adjoin S₀ ↑y).one_mem, algebra.subset_adjoin⟩) (λ z hz, _),
    rw [subalgebra.mem_to_submodule, algebra.mem_adjoin_iff] at hz, rw ← submodule.mem_coe,
    refine ring.closure_subset (set.union_subset (set.range_subset_iff.2 $ λ t, _)
      (λ t ht, subset_span $ or.inr ht)) hz,
    rw algebra.algebra_map_eq_smul_one,
    exact smul_mem (span S₀ (insert 1 ↑y : set A)) _ (subset_span $ or.inl rfl) },
  haveI : is_noetherian_ring ↥S₀ := is_noetherian_ring_closure _ (finset.finite_to_set _),
  refine is_integral_of_noetherian (algebra.adjoin S₀ ↑y)
    (is_noetherian_of_fg_of_noetherian _ ⟨insert 1 y, by rw [finset.coe_insert, this]⟩) _ _,
  rw [← hlx2, finsupp.total_apply, finsupp.sum], refine subalgebra.sum_mem _ (λ r hr, _),
  have : lx r ∈ S₀ := ring.subset_closure (finset.mem_union_left _ (finset.mem_image_of_mem _ hr)),
  change (⟨_, this⟩ : S₀) • r ∈ _,
  rw finsupp.mem_supported at hlx1,
  exact subalgebra.smul_mem _ (algebra.subset_adjoin $ hlx1 hr) _
end

theorem is_integral_of_mem_closure {x y z : A}
  (hx : is_integral R x) (hy : is_integral R y)
  (hz : z ∈ ring.closure ({x, y} : set A)) :
  is_integral R z :=
begin
  have := fg_mul _ _ (fg_adjoin_singleton_of_integral x hx) (fg_adjoin_singleton_of_integral y hy),
  rw [← algebra.adjoin_union_coe_submodule, set.singleton_union] at this,
  exact is_integral_of_mem_of_fg (algebra.adjoin R {x, y}) this z
    (algebra.mem_adjoin_iff.2  $ ring.closure_mono (set.subset_union_right _ _) hz)
end

theorem is_integral_zero : is_integral R (0:A) :=
(algebra_map R A).map_zero ▸ is_integral_algebra_map

theorem is_integral_one : is_integral R (1:A) :=
(algebra_map R A).map_one ▸ is_integral_algebra_map

theorem is_integral_add {x y : A}
  (hx : is_integral R x) (hy : is_integral R y) :
  is_integral R (x + y) :=
is_integral_of_mem_closure hx hy (is_add_submonoid.add_mem
  (ring.subset_closure (or.inl rfl)) (ring.subset_closure (or.inr rfl)))

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
  (ring.subset_closure (or.inl rfl)) (ring.subset_closure (or.inr rfl)))

variables (R A)
def integral_closure : subalgebra R A :=
{ carrier :=
  { carrier := { r | is_integral R r },
    zero_mem' := is_integral_zero,
    one_mem' := is_integral_one,
    add_mem' := λ _ _, is_integral_add,
    mul_mem' := λ _ _, is_integral_mul },
  algebra_map_mem' := λ x, is_integral_algebra_map }

theorem mem_integral_closure_iff_mem_fg {r : A} :
  r ∈ integral_closure R A ↔ ∃ M : subalgebra R A, (M : submodule R A).fg ∧ r ∈ M :=
⟨λ hr, ⟨algebra.adjoin R {r}, fg_adjoin_singleton_of_integral _ hr, algebra.subset_adjoin rfl⟩,
λ ⟨M, Hf, hrM⟩, is_integral_of_mem_of_fg M Hf _ hrM⟩

variables {R} {A}

lemma integral_closure.is_integral (x : integral_closure R A) : is_integral R x :=
exists_imp_exists
  (λ p, and.imp_right (λ hp, show aeval x p = 0,
    from subtype.ext (trans (p.hom_eval₂ _ (integral_closure R A).val.to_ring_hom x) hp)))
  x.2

theorem integral_closure_idem : integral_closure (integral_closure R A : set A) A = ⊥ :=
begin
  rw eq_bot_iff, intros r hr,
  rcases is_integral_iff_is_integral_closure_finite.1 hr with ⟨s, hfs, hr⟩,
  apply algebra.mem_bot.2, refine ⟨⟨_, _⟩, rfl⟩,
  refine (mem_integral_closure_iff_mem_fg _ _).2 ⟨algebra.adjoin _ (subtype.val '' s ∪ {r}),
    algebra.fg_trans (fg_adjoin_of_finite (hfs.image _) (λ y ⟨x, hx, hxy⟩, hxy ▸ x.2)) _,
    algebra.subset_adjoin (or.inr rfl)⟩,
  refine fg_adjoin_singleton_of_integral _ _,
  rcases hr with ⟨p, hmp, hpx⟩,
  refine ⟨to_subring (of_subring _ (of_subring _ p)) _ _, _, hpx⟩,
  { intros x hx, rcases finsupp.mem_frange.1 hx with ⟨h1, n, rfl⟩,
    change (coeff p n).1.1 ∈ algebra.adjoin R (_ : set A),
    rcases ring.exists_list_of_mem_closure (coeff p n).2 with ⟨L, HL1, HL2⟩, rw ← HL2,
    clear HL2 hfs h1 hx n hmp hpx hr r p,
    induction L with hd tl ih, { exact subalgebra.zero_mem _ },
    rw list.forall_mem_cons at HL1,
    rw [list.map_cons, list.sum_cons],
    refine subalgebra.add_mem _ _ (ih HL1.2),
    cases HL1 with HL HL', clear HL' ih tl,
    induction hd with hd tl ih, { exact subalgebra.one_mem _ },
    rw list.forall_mem_cons at HL,
    rw list.prod_cons,
    refine subalgebra.mul_mem _ _ (ih HL.2),
    rcases HL.1 with hs | rfl,
    { exact algebra.subset_adjoin (set.mem_image_of_mem _ hs) },
    exact subalgebra.neg_mem _ (subalgebra.one_mem _) },
  replace hmp := congr_arg subtype.val hmp,
  replace hmp := congr_arg subtype.val hmp,
  exact subtype.eq hmp
end

end

section algebra
open algebra
variables {R : Type*} {A : Type*} {B : Type*}
variables [comm_ring R] [comm_ring A] [comm_ring B]
variables [algebra A B] [algebra R B]

lemma is_integral_trans_aux (x : B) {p : polynomial A} (pmonic : monic p) (hp : aeval x p = 0) :
  is_integral (adjoin R (↑(p.map $ algebra_map A B).frange : set B)) x :=
begin
  generalize hS : (↑(p.map $ algebra_map A B).frange : set B) = S,
  have coeffs_mem : ∀ i, (p.map $ algebra_map A B).coeff i ∈ adjoin R S,
  { intro i, by_cases hi : (p.map $ algebra_map A B).coeff i = 0,
    { rw hi, exact subalgebra.zero_mem _ },
    rw ← hS, exact subset_adjoin (finsupp.mem_frange.2 ⟨hi, i, rfl⟩) },
  obtain ⟨q, hq⟩ : ∃ q : polynomial (adjoin R S), q.map (algebra_map (adjoin R S) B) =
      (p.map $ algebra_map A B),
  { rw ← set.mem_range, exact (polynomial.mem_map_range _).2 (λ i, ⟨⟨_, coeffs_mem i⟩, rfl⟩) },
  use q,
  split,
  { suffices h : (q.map (algebra_map (adjoin R S) B)).monic,
    { refine monic_of_injective _ h,
      exact subtype.val_injective },
    { rw hq, exact monic_map _ pmonic } },
  { convert hp using 1,
    replace hq := congr_arg (eval x) hq,
    convert hq using 1; symmetry; apply eval_map },
end

variables [algebra R A] [is_algebra_tower R A B]

/-- If A is an R-algebra all of whose elements are integral over R,
and x is an element of an A-algebra that is integral over A, then x is integral over R.-/
lemma is_integral_trans (A_int : ∀ x : A, is_integral R x) (x : B) (hx : is_integral A x) :
  is_integral R x :=
begin
  rcases hx with ⟨p, pmonic, hp⟩,
  let S : set B := ↑(p.map $ algebra_map A B).frange,
  refine is_integral_of_mem_of_fg (adjoin R (S ∪ {x})) _ _ (subset_adjoin $ or.inr rfl),
  refine fg_trans (fg_adjoin_of_finite (finset.finite_to_set _) (λ x hx, _)) _,
  { rw [finset.mem_coe, finsupp.mem_frange] at hx, rcases hx with ⟨_, i, rfl⟩,
    show is_integral R ((p.map $ algebra_map A B).coeff i), rw coeff_map,
    convert is_integral_alg_hom (is_algebra_tower.to_alg_hom R A B) (A_int _) },
  { apply fg_adjoin_singleton_of_integral,
    exact is_integral_trans_aux _ pmonic hp }
end

/-- If A is an R-algebra all of whose elements are integral over R,
and B is an A-algebra all of whose elements are integral over A,
then all elements of B are integral over R.-/
lemma algebra.is_integral_trans (A_int : ∀ x : A, is_integral R x)(B_int : ∀ x:B, is_integral A x) :
  ∀ x:B, is_integral R x :=
λ x, is_integral_trans A_int x (B_int x)

end algebra

section integral_domain
variables {R S : Type*} [comm_ring R] [integral_domain S] [algebra R S]

instance : integral_domain (integral_closure R S) :=
{ exists_pair_ne := ⟨0, 1, mt subtype.ext_iff_val.mp zero_ne_one⟩,
  eq_zero_or_eq_zero_of_mul_eq_zero := λ ⟨a, ha⟩ ⟨b, hb⟩ h,
    or.imp subtype.ext_iff_val.mpr subtype.ext_iff_val.mpr (eq_zero_or_eq_zero_of_mul_eq_zero (subtype.ext_iff_val.mp h)),
  ..(integral_closure R S).comm_ring R S }

end integral_domain
