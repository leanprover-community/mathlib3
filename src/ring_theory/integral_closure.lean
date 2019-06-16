/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Integral closure of a subring.
-/

import ring_theory.adjoin

universes u v

open polynomial submodule

variables (R : Type u) {A : Type v}
variables [comm_ring R] [comm_ring A]
variables [decidable_eq R] [decidable_eq A]
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

theorem is_integral_of_noetherian (M : subalgebra R A)
  (H : is_noetherian R (M : submodule R A)) (x : A) (hx : x ∈ M) :
  is_integral R x :=
begin
  letI : algebra R M := M.algebra,
  letI : comm_ring M := M.comm_ring R A,
  suffices : is_integral R (⟨x, hx⟩ : M),
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
theorem is_integral_of_mem_of_fg (M : subalgebra R A)
  (HM : (M : submodule R A).fg) (x : A) (hx : x ∈ M) : is_integral R x :=
begin
  cases HM with m hm,
  have hxm : x ∈ (M : submodule R A) := hx,
  rw [← hm, mem_span_iff_lc] at hxm,
  rcases hxm with ⟨lx, hlx1, hlx2⟩,
  have : ∀ (jk : (↑(m.product m) : set (A × A))), jk.1.1 * jk.1.2 ∈ (span R ↑m : submodule R A),
  { intros jk,
    let j : ↥(↑m : set A) := ⟨jk.1.1, (finset.mem_product.1 jk.2).1⟩,
    let k : ↥(↑m : set A) := ⟨jk.1.2, (finset.mem_product.1 jk.2).2⟩,
    have hj : j.1 ∈ (span R ↑m : submodule R A) := subset_span j.2,
    have hk : k.1 ∈ (span R ↑m : submodule R A) := subset_span k.2,
    revert hj hk, rw hm, exact @is_submonoid.mul_mem A _ M _ j.1 k.1 },
  simp only [mem_span_iff_lc] at this,
  choose lm hlm1 hlm2,
  let S₀' : finset R := lx.frange ∪ finset.bind finset.univ (finsupp.frange ∘ lm),
  let S₀ : set R := ring.closure ↑S₀',
  refine is_integral_of_subring (ring.closure ↑S₀') _,
  letI : algebra S₀ (algebra.comap S₀ R A) := algebra.comap.algebra _ _ _,
  letI : module S₀ (algebra.comap S₀ R A) := algebra.module,
  have : (span S₀ (insert 1 (↑m:set A) : set (algebra.comap S₀ R A)) : submodule S₀ (algebra.comap S₀ R A)) =
      (algebra.adjoin S₀ ((↑m : set A) : set (algebra.comap S₀ R A)) : subalgebra S₀ (algebra.comap S₀ R A)),
  { apply le_antisymm,
    { rw [span_le, set.insert_subset, mem_coe], split,
      change _ ∈ ring.closure _, exact is_submonoid.one_mem _, exact algebra.subset_adjoin },
    rw [algebra.adjoin_eq_span, span_le], intros r hr, refine monoid.in_closure.rec_on hr _ _ _,
    { intros r hr, exact subset_span (set.mem_insert_of_mem _ hr) },
    { exact subset_span (set.mem_insert _ _) },
    intros r1 r2 hr1 hr2 ih1 ih2, simp only [mem_coe, mem_span_iff_lc] at ih1 ih2,
    have ih1' := ih1, have ih2' := ih2,
    rcases ih1' with ⟨l1, hl1, rfl⟩, rcases ih2' with ⟨l2, hl2, rfl⟩,
    simp only [lc.total_apply, finsupp.sum_mul, finsupp.mul_sum, mem_coe],
    rw [finsupp.sum], refine sum_mem _ _, intros r2 hr2,
    rw [finsupp.sum], refine sum_mem _ _, intros r1 hr1,
    rw [algebra.mul_smul_comm, algebra.smul_mul_assoc],
    letI : module ↥S₀ A := _inst_6, refine smul_mem _ _ (smul_mem _ _ _),
    rcases hl1 hr1 with rfl | hr1,
    { change 1 * r2 ∈ _, rw one_mul r2, exact subset_span (hl2 hr2) },
    rcases hl2 hr2 with rfl | hr2,
    { change r1 * 1 ∈ _, rw mul_one, exact subset_span (set.mem_insert_of_mem _ hr1) },
    let jk : ↥(↑(finset.product m m) : set (A × A)) := ⟨(r1, r2), finset.mem_product.2 ⟨hr1, hr2⟩⟩,
    specialize hlm2 jk, change _ = r1 * r2 at hlm2, rw [← hlm2, lc.total_apply],
    rw [finsupp.sum], refine sum_mem _ _, intros z hz,
    have : lm jk z ∈ S₀,
    { apply ring.subset_closure,
      apply finset.mem_union_right, apply finset.mem_bind.2,
      exact ⟨jk, finset.mem_univ _, finset.mem_image_of_mem _ hz⟩ },
    change @has_scalar.smul S₀ (algebra.comap S₀ R A) _inst_6.to_has_scalar ⟨lm jk z, this⟩ z ∈ _,
    exact smul_mem _ _ (subset_span (set.mem_insert_of_mem _ (hlm1 _ hz))) },
  haveI : is_noetherian_ring ↥S₀ :=(by convert is_noetherian_ring_closure _ (finset.finite_to_set _); apply_instance),
  apply is_integral_of_noetherian
    (algebra.adjoin S₀ ((↑m : set A) : set (algebra.comap S₀ R A)) : subalgebra S₀ (algebra.comap S₀ R A))
    (is_noetherian_of_fg_of_noetherian _ ⟨insert 1 m, by rw finset.coe_insert; convert this⟩),
  show x ∈ ((algebra.adjoin S₀ ((↑m : set A) : set (algebra.comap S₀ R A)) : subalgebra S₀ (algebra.comap S₀ R A)) : submodule S₀ (algebra.comap S₀ R A)),
  rw [← hlx2, lc.total_apply, finsupp.sum], refine sum_mem _ _, intros r hr,
  rw ← this,
  have : lx r ∈ ring.closure ↑S₀' :=
    ring.subset_closure (finset.mem_union_left _ (finset.mem_image_of_mem _ hr)),
  change @has_scalar.smul S₀ (algebra.comap S₀ R A) _inst_6.to_has_scalar ⟨lx r, this⟩ r ∈ _,
  exact smul_mem _ _ (subset_span (set.mem_insert_of_mem _ (hlx1 hr)))
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
