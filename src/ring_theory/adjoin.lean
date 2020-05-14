/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Adjoining elements to form subalgebras.
-/
import ring_theory.polynomial
import ring_theory.principal_ideal_domain

universes u v w

open submodule ring

namespace algebra

variables {R : Type u} {A : Type v}
variables [comm_ring R] [comm_ring A]
variables [algebra R A] {s t : set A}

theorem subset_adjoin : s ⊆ adjoin R s :=
set.subset.trans (set.subset_union_right _ _) subset_closure

theorem adjoin_le {S : subalgebra R A} (H : s ⊆ S) : adjoin R s ≤ S :=
closure_subset $ set.union_subset S.3 H

theorem adjoin_le_iff {S : subalgebra R A} : adjoin R s ≤ S ↔ s ⊆ S:=
⟨set.subset.trans subset_adjoin, adjoin_le⟩

theorem adjoin_mono (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
closure_subset (set.subset.trans (set.union_subset_union_right _ H) subset_closure)

variables (R A)
@[simp] theorem adjoin_empty : adjoin R (∅ : set A) = ⊥ :=
eq_bot_iff.2 $ adjoin_le $ set.empty_subset _
variables {A}

variables (s t)
theorem adjoin_union : adjoin R (s ∪ t) = (adjoin R s).under (adjoin (adjoin R s) t) :=
le_antisymm
  (closure_mono $ set.union_subset
    (set.range_subset_iff.2 $ λ r, or.inl ⟨algebra_map R (adjoin R s) r, rfl⟩)
    (set.union_subset_union_left _ $ λ x hxs, ⟨⟨_, subset_adjoin hxs⟩, rfl⟩))
  (closure_subset $ set.union_subset
    (set.range_subset_iff.2 $ λ x, adjoin_mono (set.subset_union_left _ _) x.2)
    (set.subset.trans (set.subset_union_right _ _) subset_adjoin))

theorem adjoin_eq_span : (adjoin R s : submodule R A) = span R (monoid.closure s) :=
begin
  apply le_antisymm,
  { intros r hr, rcases ring.exists_list_of_mem_closure hr with ⟨L, HL, rfl⟩, clear hr,
    induction L with hd tl ih, { rw mem_coe, exact zero_mem _ },
    rw list.forall_mem_cons at HL,
    rw [list.map_cons, list.sum_cons, mem_coe],
    refine submodule.add_mem _ _ (ih HL.2),
    replace HL := HL.1, clear ih tl,
    suffices : ∃ z r (hr : r ∈ monoid.closure s), has_scalar.smul.{u v} z r = list.prod hd,
    { rcases this with ⟨z, r, hr, hzr⟩, rw ← hzr,
      exact smul_mem _ _ (subset_span hr) },
    induction hd with hd tl ih, { exact ⟨1, 1, is_submonoid.one_mem, one_smul _ _⟩ },
    rw list.forall_mem_cons at HL,
    rcases (ih HL.2) with ⟨z, r, hr, hzr⟩, rw [list.prod_cons, ← hzr],
    rcases HL.1 with ⟨⟨hd, rfl⟩ | hs⟩ | rfl,
    { refine ⟨hd * z, r, hr, _⟩,
      rw [smul_def, smul_def, (algebra_map _ _).map_mul, _root_.mul_assoc] },
    { refine ⟨z, hd * r, is_submonoid.mul_mem (monoid.subset_closure hs) hr, _⟩,
      rw [smul_def, smul_def, mul_left_comm] },
    { refine ⟨-z, r, hr, _⟩, rw [neg_smul, neg_one_mul] } },
  exact span_le.2 (show monoid.closure s ⊆ adjoin R s, from monoid.closure_subset subset_adjoin)
end

theorem adjoin_eq_range :
  adjoin R s = (mv_polynomial.aeval R A (coe : s → A)).range :=
le_antisymm
  (adjoin_le $ λ x hx, ⟨mv_polynomial.X ⟨x, hx⟩, mv_polynomial.eval₂_X _ _ _⟩)
  (λ x ⟨p, hp⟩, hp ▸ mv_polynomial.induction_on p
    (λ r, by rw [mv_polynomial.aeval_def, mv_polynomial.eval₂_C]; exact (adjoin R s).3 ⟨r, rfl⟩)
    (λ p q hp hq, by rw alg_hom.map_add; exact is_add_submonoid.add_mem hp hq)
    (λ p ⟨n, hn⟩ hp, by rw [alg_hom.map_mul, mv_polynomial.aeval_def _ _ _ (mv_polynomial.X _),
      mv_polynomial.eval₂_X]; exact is_submonoid.mul_mem hp (subset_adjoin hn)))

theorem adjoin_singleton_eq_range (x : A) :
  adjoin R {x} = (polynomial.aeval R A x).range :=
le_antisymm
  (adjoin_le $ set.singleton_subset_iff.2 ⟨polynomial.X, polynomial.eval₂_X _ _⟩)
  (λ y ⟨p, hp⟩, hp ▸ polynomial.induction_on p
    (λ r, by rw [polynomial.aeval_def, polynomial.eval₂_C]; exact (adjoin R _).3 ⟨r, rfl⟩)
    (λ p q hp hq, by rw alg_hom.map_add; exact is_add_submonoid.add_mem hp hq)
    (λ n r ih, by { rw [pow_succ', ← ring.mul_assoc, alg_hom.map_mul,
      polynomial.aeval_def _ polynomial.X, polynomial.eval₂_X],
      exact is_submonoid.mul_mem ih (subset_adjoin $ or.inl rfl) }))

theorem adjoin_union_coe_submodule : (adjoin R (s ∪ t) : submodule R A) =
  (adjoin R s) * (adjoin R t) :=
begin
  rw [adjoin_eq_span, adjoin_eq_span, adjoin_eq_span, span_mul_span],
  congr' 1,
  ext z,
  rw monoid.mem_closure_union_iff,
  split;
  { rintro ⟨y, hys, z, hzt, rfl⟩, exact ⟨_, hys, _, hzt, rfl⟩ }
end
variables {R s t}

theorem adjoin_int (s : set R) : adjoin ℤ s = subalgebra_of_subring (ring.closure s) :=
le_antisymm (adjoin_le subset_closure) (closure_subset subset_adjoin)

local attribute [instance] set.pointwise_mul_semiring

theorem fg_trans (h1 : (adjoin R s : submodule R A).fg)
  (h2 : (adjoin (adjoin R s) t : submodule (adjoin R s) A).fg) :
  (adjoin R (s ∪ t) : submodule R A).fg :=
begin
  rcases fg_def.1 h1 with ⟨p, hp, hp'⟩,
  rcases fg_def.1 h2 with ⟨q, hq, hq'⟩,
  refine fg_def.2 ⟨p * q, set.pointwise_mul_finite hp hq, le_antisymm _ _⟩,
  { rw [span_le],
    rintros _ ⟨x, hx, y, hy, rfl⟩,
    change x * y ∈ _,
    refine is_submonoid.mul_mem _ _,
    { have : x ∈ (adjoin R s : submodule R A),
      { rw ← hp', exact subset_span hx },
      exact adjoin_mono (set.subset_union_left _ _) this },
    have : y ∈ (adjoin (adjoin R s) t : submodule (adjoin R s) A),
    { rw ← hq', exact subset_span hy },
    change y ∈ adjoin R (s ∪ t), rwa adjoin_union },
  { intros r hr,
    change r ∈ adjoin R (s ∪ t) at hr,
    rw adjoin_union at hr,
    change r ∈ (adjoin (adjoin R s) t : submodule (adjoin R s) A) at hr,
    haveI := classical.dec_eq A,
    haveI := classical.dec_eq R,
    rw [← hq', ← set.image_id q, finsupp.mem_span_iff_total (adjoin R s)] at hr,
    rcases hr with ⟨l, hlq, rfl⟩,
    have := @finsupp.total_apply A A (adjoin R s),
    rw [this, finsupp.sum, mem_coe],
    refine sum_mem _ _,
    intros z hz, change (l z).1 * _ ∈ _,
    have : (l z).1 ∈ (adjoin R s : submodule R A) := (l z).2,
    rw [← hp', ← set.image_id p, finsupp.mem_span_iff_total R] at this,
    rcases this with ⟨l2, hlp, hl⟩,
    have := @finsupp.total_apply A A R,
    rw this at hl,
    rw [←hl, finsupp.sum_mul],
    refine sum_mem _ _,
    intros t ht, change _ * _ ∈ _, rw smul_mul_assoc, refine smul_mem _ _ _,
    exact subset_span ⟨t, hlp ht, z, hlq hz, rfl⟩ }
end

end algebra

namespace subalgebra

variables {R : Type u} {A : Type v}
variables [comm_ring R] [comm_ring A] [algebra R A]

/-- A subalgebra `S` is finitely generated if there exists `t : finset A` such that
`algebra.adjoin R t = S`. -/
def fg (S : subalgebra R A) : Prop :=
∃ t : finset A, algebra.adjoin R ↑t = S

theorem fg_def {S : subalgebra R A} : S.fg ↔ ∃ t : set A, set.finite t ∧ algebra.adjoin R t = S :=
⟨λ ⟨t, ht⟩, ⟨↑t, set.finite_mem_finset t, ht⟩,
λ ⟨t, ht1, ht2⟩, ⟨ht1.to_finset, by rwa set.finite.coe_to_finset⟩⟩

theorem fg_bot : (⊥ : subalgebra R A).fg :=
⟨∅, algebra.adjoin_empty R A⟩

end subalgebra

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B]

instance alg_hom.is_noetherian_ring_range (f : A →ₐ[R] B) [is_noetherian_ring A] :
  is_noetherian_ring f.range :=
is_noetherian_ring_range f.to_ring_hom

theorem is_noetherian_ring_of_fg {S : subalgebra R A} (HS : S.fg)
  [is_noetherian_ring R] : is_noetherian_ring S :=
let ⟨t, ht⟩ := HS in ht ▸ (algebra.adjoin_eq_range R (↑t : set A)).symm ▸
by haveI : is_noetherian_ring (mv_polynomial (↑t : set A) R) :=
mv_polynomial.is_noetherian_ring;
convert alg_hom.is_noetherian_ring_range _; apply_instance

theorem is_noetherian_ring_closure (s : set R) (hs : s.finite) :
  is_noetherian_ring (ring.closure s) :=
show is_noetherian_ring (subalgebra_of_subring (ring.closure s)), from
algebra.adjoin_int s ▸ is_noetherian_ring_of_fg (subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
