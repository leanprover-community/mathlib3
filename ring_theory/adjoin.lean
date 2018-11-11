/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Adjoining elements to a subring.
-/

import linear_algebra.tensor_product
import ring_theory.noetherian
import ring_theory.subring

universe u

open lattice submodule

namespace ring

section ring

variables {R : Type u} [ring R]

instance subring.module (S : set R) [is_subring S] : module S R :=
module.of_core { 
  smul := λ r x , r.1 * x,
  smul_add := λ r, mul_add _,
  add_smul := λ r s, add_mul _ _,
  mul_smul := λ r s, mul_assoc _ _,
  one_smul := one_mul }

def adjoin (S s : set R) : set R :=
closure (S ∪ s)

variables (S s t : set R)

instance adjoin.is_subring : is_subring (adjoin S s) :=
ring.is_subring

variables {S s t}

theorem base_subset_adjoin : S ⊆ adjoin S s :=
set.subset.trans (set.subset_union_left _ _) subset_closure

theorem subset_adjoin : s ⊆ adjoin S s :=
set.subset.trans (set.subset_union_right _ _) subset_closure

theorem adjoin_mono (H : s ⊆ t) : adjoin S s ⊆ adjoin S t :=
closure_subset (set.subset.trans (set.union_subset_union_right _ H) subset_closure)

theorem adjoin_adjoin : adjoin (adjoin S s) t = adjoin S (s ∪ t) :=
set.subset.antisymm
  (closure_subset (set.union_subset
    (closure_mono (set.union_subset_union_right _ (set.subset_union_left _ _)))
    (set.subset.trans (set.subset_union_right _ _) subset_adjoin)))
  (closure_mono (set.union_subset
    (set.subset.trans base_subset_adjoin (set.subset_union_left _ _))
    (set.union_subset_union_left _ subset_adjoin)))

end ring

section comm_ring

variables {R : Type u} [comm_ring R]
variables (S : set R) [is_subring S] (s : set R)
include S

protected theorem mul_smul (r1 : R) (s : S) (r2 : R) :
  r1 * @has_scalar.smul S R (ring.subring.module S).to_has_scalar s r2 =
  @has_scalar.smul S R (ring.subring.module S).to_has_scalar s (r1 * r2) :=
mul_left_comm _ _ _

protected theorem smul_mul (s : S) (r1 r2 : R) :
  (@has_scalar.smul S R (ring.subring.module S).to_has_scalar s r1) * r2 =
  @has_scalar.smul S R (ring.subring.module S).to_has_scalar s (r1 * r2) :=
mul_assoc _ _ _

def madjoin : submodule S R :=
⟨adjoin S s, is_add_submonoid.zero_mem _, λ _ _, is_add_submonoid.add_mem,
λ s r hr, is_submonoid.mul_mem (base_subset_adjoin s.2) hr⟩

instance madjoin.is_subring : is_subring (↑(madjoin S s) : set R) :=
ring.is_subring

theorem madjoin_eq_adjoin {S : set R} [is_subring S] {s : set R} :
  ↑(madjoin S s) = adjoin S s := rfl

def linear_map.module : module S (R →ₗ R) := linear_map.module

local attribute [instance] linear_map.module

def lmul₁ (t : R) : @linear_map S R R _ _ _ _ _ :=
⟨(*) t, mul_add t, λ _, ring.mul_smul _ _ _⟩

def lmul₂ : @linear_map S R (@linear_map S R R _ _ _ _ _) _ _ _ _ _ :=
⟨lmul₁ S, λ x y, linear_map.ext $ λ t, add_mul x y t,
λ s r, linear_map.ext $ λ t, mul_assoc s.1 r t⟩

instance : has_mul (submodule S R) :=
⟨λ S1 S2, ⨆ s : S1, S2.map $ lmul₁ S s.1⟩

variables {S s} {S1 S2 T : submodule S R} {s1 s2 : R}

theorem mul_mem_mul (hs1 : s1 ∈ S1) (hs2 : s2 ∈ S2) : s1 * s2 ∈ S1 * S2 :=
have _ ≤ S1 * S2 := le_supr _ ⟨s1, hs1⟩, this ⟨s2, hs2, rfl⟩

theorem mul_le : S1 * S2 ≤ T ↔ ∀ (s1 ∈ S1) (s2 ∈ S2), s1 * s2 ∈ T :=
⟨λ H s1 hs1 s2 hs2, H (mul_mem_mul hs1 hs2),
λ H, supr_le $ λ ⟨s1, hs1⟩, map_le_iff_le_comap.2 $ λ s2 hs2, H s1 hs1 s2 hs2⟩

@[elab_as_eliminator] protected theorem mul_induction {r : R} {C : R → Prop} (hr : r ∈ S1 * S2)
  (hm : ∀ (s1 ∈ S1) (s2 ∈ S2), C (s1 * s2))
  (h0 : C 0) (ha : ∀ x y, C x → C y → C (x + y))
  (hs : ∀ (s ∈ S) r, C r → C (s * r)) : C r :=
(@mul_le _ _ _ _ _ _ ⟨C, h0, ha, subtype.forall.2 hs⟩).2 hm hr

variables {t : set R}

theorem madjoin_union : madjoin S (s ∪ t) = madjoin S s * madjoin S t :=
begin
  apply le_antisymm,
  { intros r hr, refine add_group.in_closure.rec_on hr _ _ _ _,
    { intros r hr,
      suffices : ∃ (s' ∈ madjoin S s) (t' ∈ madjoin S t), s' * t' = r,
      { rcases this with ⟨s', hs', t', ht', rfl⟩, exact mul_mem_mul hs' ht' },
      refine monoid.in_closure.rec_on hr _ _ _,
      { rintros r (hrS | hrs | hrt),
        { exact ⟨r, base_subset_adjoin hrS, 1, (mem_coe _).1 (is_submonoid.one_mem _), mul_one _⟩ },
        { exact ⟨r, subset_adjoin hrs, 1, (mem_coe _).1 (is_submonoid.one_mem _), mul_one _⟩ },
        { exact ⟨1, (mem_coe _).1 (is_submonoid.one_mem _), r, subset_adjoin hrt, one_mul _⟩ } },
      { exact ⟨1, (mem_coe _).1 (is_submonoid.one_mem _), 1, (mem_coe _).1 (is_submonoid.one_mem _), mul_one _⟩ },
      { rintros x y hx hy ⟨p1, hp1, q1, hq1, rfl⟩ ⟨p2, hp2, q2, hq2, rfl⟩,
        rw [mul_assoc, mul_left_comm q1, ← mul_assoc],
        exact ⟨p1 * p2, (mem_coe _).1 (is_submonoid.mul_mem hp1 hp2), q1 * q2, (mem_coe _).1 (is_submonoid.mul_mem hq1 hq2), rfl⟩ } },
    { rw mem_coe, exact zero_mem _ },
    { intros r hr ih, rw ← neg_one_smul, rw mem_coe, exact smul_mem _ _ ih },
    { intros p q hp hq ihp ihq, rw mem_coe, exact add_mem _ ihp ihq } },
  { refine mul_le.2 (λ s1 hs1 s2 hs2, (mem_coe _).1 _),
    exact is_submonoid.mul_mem (adjoin_mono (set.subset_union_left _ _) hs1)
      (adjoin_mono (set.subset_union_right _ _) hs2) }
end

variables (S)
theorem span_mul_span (s1 : set R) (s2 : set R) :
  (span s1 * span s2 : submodule S R) = span ((s1.prod s2).image (λ p, p.1 * p.2)) :=
le_antisymm
  (mul_le.2 $ λ x1 hx1 x2 hx2, span_induction hx1
    (λ y1 hy1, span_induction hx2
      (λ y2 hy2, subset_span ⟨(y1, y2), ⟨hy1, hy2⟩, rfl⟩)
      ((mul_zero y1).symm ▸ zero_mem _)
      (λ r1 r2, (mul_add y1 r1 r2).symm ▸ add_mem _)
      (λ s r, (ring.mul_smul S y1 s r).symm ▸ smul_mem _ _))
    ((zero_mul x2).symm ▸ zero_mem _)
    (λ r1 r2, (add_mul r1 r2 x2).symm ▸ add_mem _)
    (λ s r, (ring.smul_mul S s r x2).symm ▸ smul_mem _ _))
  (span_le.2 (set.image_subset_iff.2 $ λ ⟨x1, x2⟩ ⟨hx1, hx2⟩,
    mul_mem_mul (subset_span hx1) (subset_span hx2)))
variables {S}

theorem fg_mul (hs1 : S1.fg) (hs2 : S2.fg) : (S1 * S2).fg :=
let ⟨s1, hf1, hs1⟩ := fg_def.1 hs1, ⟨s2, hf2, hs2⟩ := fg_def.1 hs2 in
fg_def.2 ⟨(s1.prod s2).image (λ p, p.1 * p.2),
set.finite_image _ (set.finite_prod hf1 hf2),
span_mul_span S s1 s2 ▸ hs1 ▸ hs2 ▸ rfl⟩

theorem madjoin_eq_span : ring.madjoin S s = span (monoid.closure s) :=
begin
  letI := ring.subring.module S,
  letI := (ring.subring.module S).to_has_scalar,
  apply le_antisymm,
  { intros r hr, rcases ring.exists_list_of_mem_closure hr with ⟨L, HL, rfl⟩, clear hr,
    induction L with hd tl ih, { rw mem_coe, exact zero_mem _ },
    rw list.forall_mem_cons at HL,
    rw [list.map_cons, list.sum_cons, mem_coe],
    refine submodule.add_mem _ _ (ih HL.2),
    replace HL := HL.1, clear ih tl,
    suffices : ∃ z (hz : z ∈ S) r (hr : r ∈ monoid.closure s), (⟨z, hz⟩ : S) • r = list.prod hd,
    { rcases this with ⟨z, hz, r, hr, hzr⟩, rw ← hzr,
      exact smul_mem _ _ (subset_span hr) },
    induction hd with hd tl ih, { exact ⟨1, is_submonoid.one_mem _, 1, is_submonoid.one_mem _, mul_one _⟩ },
    rw list.forall_mem_cons at HL,
    rcases (ih HL.2) with ⟨z, hz, r, hr, hzr⟩, rw [list.prod_cons, ← hzr],
    rcases HL.1 with ⟨hS | hs⟩ | rfl,
    { refine ⟨hd * z, is_submonoid.mul_mem hS hz, r, hr, mul_assoc _ _ _⟩ },
    { refine ⟨z, hz, hd * r, is_submonoid.mul_mem (monoid.subset_closure hs) hr, mul_left_comm _ _ _⟩ },
    { refine ⟨(-1) * z, is_submonoid.mul_mem _ hz, r, hr, mul_assoc _ _ _⟩,
      exact is_add_subgroup.neg_mem (is_submonoid.one_mem _) } },
  exact span_le.2 (monoid.closure_subset ring.subset_adjoin)
end

end comm_ring

end ring