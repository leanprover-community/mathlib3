/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import ring_theory.local_properties
import ring_theory.localization.inv_submonoid

namespace ring_hom

-- open_locale tensor_product

-- open tensor_product algebra.tensor_product

lemma finite_type_stable_under_composition :
  stable_under_composition @finite_type :=
by { introv R hf hg, exactI hg.comp hf }

-- lemma algebra.adjoin_adjoin_of_tower (R : Type*) {S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
--   [algebra R S] [algebra S T] [algebra R T] [is_scalar_tower R S T] (s : set T) :
--   algebra.adjoin S ↑(algebra.adjoin R s) = algebra.adjoin S s :=
-- le_antisymm (algebra.adjoin_le $
--   show algebra.adjoin R s ≤ (algebra.adjoin S s).restrict_scalars R,
--     from algebra.adjoin_le algebra.subset_adjoin)
--   (algebra.adjoin_mono algebra.subset_adjoin)

-- lemma stable_under_base_change_finite_type :
--   stable_under_base_change @finite_type :=
-- begin
--   classical,
--   introv R h,
--   resetI,
--   replace h : algebra.finite_type R T := by { convert h, ext, rw algebra.smul_def, refl },
--   obtain ⟨s, hs⟩ := h.out,
--   letI := (include_left : S →ₐ[R] S ⊗[R] T).to_ring_hom.to_algebra,
--   suffices : algebra.finite_type S (S ⊗[R] T),
--   { sorry },
--   refine ⟨⟨s.image include_right, eq_top_iff.mpr $ λ x _, _⟩⟩,
--   apply tensor_product.induction_on x,
--   { exact zero_mem _ },
--   { intros x y,
--     rw [finset.coe_image, ← algebra.adjoin_adjoin_of_tower R, algebra.adjoin_image, hs,
--       algebra.map_top, ← mul_one x, ← smul_eq_mul, ← smul_tmul'],
--     any_goals { apply_instance },
--     convert subalgebra.smul_mem _ _ _, },
--   { exact λ _ _, submodule.add_mem _ }
-- end

lemma finite_type_holds_for_localization_away :
  holds_for_localization_away @finite_type :=
begin
  introv R _,
  resetI,
  suffices : algebra.finite_type R S,
  { change algebra.finite_type _ _, convert this, ext, rw algebra.smul_def, refl },
  exact is_localization.finite_type_of_monoid_fg (submonoid.powers r) S,
end


/-- Suppose we are given `∑ i, lᵢ * sᵢ = 1` in `S`, and `S'` a subalgebra of `S` that contains
`lᵢ` and `sᵢ`. To check that an `x : S` falls in `S'`, we only need to show that
`r ^ n • x ∈ M'` for some `n` for each `r : s`. -/
lemma subalgebra.mem_of_span_eq_top_of_smul_pow_mem {R S : Type*} [comm_ring R] [comm_ring S] [algebra R S]
  (S' : subalgebra R S) (s : set S) (l : s →₀ S) (hs : finsupp.total s S S coe l = 1)
  (hs' : s ⊆ S') (hl : ∀ i, l i ∈ S') (x : S)
  (H : ∀ r : s, ∃ (n : ℕ), (r ^ n : S) • x ∈ S') : x ∈ S' :=
begin
  let s' : set S' := coe ⁻¹' s,
  let e : s' ≃ s := ⟨λ x, ⟨x.1, x.2⟩, λ x, ⟨⟨_, hs' x.2⟩, x.2⟩, λ ⟨⟨_, _⟩, _⟩, rfl, λ ⟨_, _⟩, rfl⟩,
  let l' : s →₀ S' := ⟨l.support, λ x, ⟨_, hl x⟩,
    λ _, finsupp.mem_support_iff.trans $ iff.not $ by { rw ← subtype.coe_inj, refl }⟩,
  have : ideal.span s' = ⊤,
  { rw [ideal.eq_top_iff_one, ideal.span, finsupp.mem_span_iff_total],
    refine ⟨finsupp.equiv_map_domain e.symm l', subtype.ext $ eq.trans _ hs⟩,
    rw finsupp.total_equiv_map_domain,
    exact finsupp.apply_total _ (algebra.of_id S' S).to_linear_map _ _ },
  obtain ⟨s'', hs₁, hs₂⟩ := (ideal.span_eq_top_iff_finite _).mp this,
  replace H : ∀ r : s'', ∃ (n : ℕ), (r ^ n : S) • x ∈ S' := λ r, H ⟨r, hs₁ r.2⟩,
  choose n₁ n₂ using H,
  let N := s''.attach.sup n₁,
  have hs' := ideal.span_pow_eq_top _ hs₂ N,
  have : ∀ {x : S}, x ∈ (algebra.of_id S' S).range.to_submodule ↔ x ∈ S' :=
    λ x, ⟨by { rintro ⟨x, rfl⟩, exact x.2 }, λ h, ⟨⟨x, h⟩, rfl⟩⟩,
  rw ← this,
  apply (algebra.of_id S' S).range.to_submodule.mem_of_span_top_of_smul_mem _ hs',
  rintro ⟨_, r, hr, rfl⟩,
  convert submodule.smul_mem _ (r ^ (N - n₁ ⟨r, hr⟩)) (this.mpr $ n₂ ⟨r, hr⟩) using 1,
  simp only [_root_.coe_coe, subtype.coe_mk,
    subalgebra.smul_def, smul_smul, ← pow_add, subalgebra.coe_pow],
  rw tsub_add_cancel_of_le (finset.le_sup (s''.mem_attach _) : n₁ ⟨r, hr⟩ ≤ N),
end

open_locale pointwise

lemma algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin {R A B : Type*} [comm_ring R] [comm_ring A]
  [comm_ring B] [algebra R A] [algebra R B] [algebra A B] [is_scalar_tower R A B]
  (r : A) (s : set B) (B' : subalgebra R B) (hs : r • s ⊆ B') {x : B} (hx : x ∈ algebra.adjoin R s)
  (hr : algebra_map A B r ∈ B') :
  ∃ n₀ : ℕ, ∀ n ≥ n₀, r ^ n • x ∈ B' :=
begin
  change x ∈ (algebra.adjoin R s).to_submodule at hx,
  rw [algebra.adjoin_eq_span, finsupp.mem_span_iff_total] at hx,
  rcases hx with ⟨l, rfl : l.sum (λ (i : submonoid.closure s) (c : R), c • ↑i) = x⟩,
  choose n₁ n₂ using (λ x : submonoid.closure s, submonoid.pow_smul_mem_closure_smul r s x.prop),
  use l.support.sup n₁,
  intros n hn,
  rw finsupp.smul_sum,
  refine B'.to_submodule.sum_mem _,
  intros a ha,
  have : n ≥ n₁ a := le_trans (finset.le_sup ha) hn,
  dsimp only,
  rw [← tsub_add_cancel_of_le this, pow_add, ← smul_smul,
    ← is_scalar_tower.algebra_map_smul A (l a) (a : B), smul_smul (r ^ n₁ a),
    mul_comm, ← smul_smul, algebra.smul_def, map_pow, is_scalar_tower.algebra_map_smul],
  apply subalgebra.mul_mem _ (subalgebra.pow_mem _ hr _) _,
  refine subalgebra.smul_mem _ _ _,
  change _ ∈ B'.to_submonoid,
  rw ← submonoid.closure_eq B'.to_submonoid,
  apply submonoid.closure_mono hs (n₂ a),
end

lemma is_localization.exists_smul_mem_of_mem_adjoin {R S S' : Type*} [comm_ring R]
  [comm_ring S] [comm_ring S'] [algebra S S'] [algebra R S] (M : submonoid S) [decidable_eq S]
  [algebra R S'] [is_scalar_tower R S S']
  [is_localization M S'] (x : S) (s : finset S') (A : subalgebra R S)
  (hA₁ : (is_localization.finset_integer_multiple M s : set S) ⊆ A)
  (hA₂ : M ≤ A.to_submonoid)
  (hx : algebra_map S S' x ∈ algebra.adjoin R (s : set S')) :
    ∃ m : M, m • x ∈ A :=
begin
  let g : S →ₐ[R] S' := is_scalar_tower.to_alg_hom R S S',
  let y := is_localization.common_denom_of_finset M s,
  have hx₁ : (y : S) • ↑s = g '' _ := (is_localization.finset_integer_multiple_image _ s).symm,
  obtain ⟨n, hn⟩ := algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin (y : S) (s : set S')
    (A.map g) (by { rw hx₁, exact set.image_subset _ hA₁ }) hx (set.mem_image_of_mem _ (hA₂ y.2)),
  obtain ⟨x', hx', hx''⟩ := hn n (le_of_eq rfl),
  rw [algebra.smul_def, ← _root_.map_mul] at hx'',
  obtain ⟨a, ha₂⟩ := (is_localization.eq_iff_exists M S').mp hx'',
  use a * y ^ n,
  convert A.mul_mem hx' (hA₂ a.2),
  convert ha₂.symm,
  simp only [submonoid.smul_def, submonoid.coe_pow, smul_eq_mul, submonoid.coe_mul],
  ring,
end

lemma finite_type_of_localization_span_target : of_localization_span_target @finite_type :=
begin
  -- Setup algebra intances.
  rw of_localization_span_target_iff_finite,
  introv R hs H,
  resetI,
  classical,
  letI := f.to_algebra,
  replace H : ∀ r : s, algebra.finite_type R (localization.away (r : S)),
  { intro r, convert H r, ext, rw algebra.smul_def, refl },
  replace H := λ r, (H r).1,
  constructor,
  -- Suppose `s : finset S` spans `S`, and each `Sᵣ` is finitely generated as an `R`-algebra.
  -- Say `t r : finset Sᵣ` generates `Sᵣ`. By assumption, we may find `lᵢ` such that
  -- `∑ lᵢ * sᵢ = 1`. I claim that all `s` and `l` denominators of `t` and generates `S`.
  choose t ht using H,
  obtain ⟨l, hl⟩ := (finsupp.mem_span_iff_total S (s : set S) 1).mp
    (show (1 : S) ∈ ideal.span (s : set S), by { rw hs, trivial }),
  let sf := λ (x : s), is_localization.finset_integer_multiple (submonoid.powers (x : S)) (t x),
  use s.attach.bUnion sf ∪ s ∪ l.support.image l,
  rw eq_top_iff,
  -- We need to show that every `x` falls in the subalgebra generated by those elements.
  -- Since all `s` and `l` are in the subalgebra, it suffices to check that `sᵢ ^ nᵢ • x` falls in
  -- the algebra for each `sᵢ` and some `nᵢ`.
  rintro x -,
  apply subalgebra.mem_of_span_eq_top_of_smul_pow_mem _ (s : set S) l hl _ _ x _,
  { intros x hx,
    apply algebra.subset_adjoin,
    rw [finset.coe_union, finset.coe_union],
    exact or.inl (or.inr hx) },
  { intros i,
    by_cases h : l i = 0, { rw h, exact zero_mem _ },
    apply algebra.subset_adjoin,
    rw [finset.coe_union, finset.coe_image],
    exact or.inr (set.mem_image_of_mem _ (finsupp.mem_support_iff.mpr h)) },
  { intro r,
    rw [finset.coe_union, finset.coe_union, finset.coe_bUnion],
    -- Since all `sᵢ` and denominators of `t r` are in the algebra, it suffices to show that the
    -- image of `x` in `Sᵣ` falls in the `R`-adjoin of `t r`, which is of course true.
    obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := is_localization.exists_smul_mem_of_mem_adjoin
      (submonoid.powers (r : S)) x (t r)
      (algebra.adjoin R _) _ _ _,
    { exact ⟨n₂, hn₂⟩ },
    { intros x hx,
      apply algebra.subset_adjoin,
      refine or.inl (or.inl ⟨_, ⟨r, rfl⟩, _, ⟨s.mem_attach r, rfl⟩, hx⟩) },
    { rw [submonoid.powers_eq_closure, submonoid.closure_le, set.singleton_subset_iff],
      apply algebra.subset_adjoin,
      exact or.inl (or.inr r.2) },
    { rw ht, trivial } }
end

lemma finite_is_local :
  property_is_local @finite_type :=
⟨localization_finite_type, finite_type_of_localization_span_target,
  finite_type_stable_under_composition, finite_type_holds_for_localization_away⟩


end ring_hom
