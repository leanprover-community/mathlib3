/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ring_theory.adjoin.polynomial

/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of finitely-generated subalgebras.

## Definitions

* `fg (S : subalgebra R A)` : A predicate saying that the subalgebra is finitely-generated
as an A-algebra

## Tags

adjoin, algebra, finitely-generated algebra

-/

universes u v w

open subsemiring ring submodule
open_locale pointwise

namespace algebra

variables {R : Type u} {A : Type v} {B : Type w}
  [comm_semiring R] [comm_semiring A] [algebra R A] {s t : set A}

theorem fg_trans (h1 : (adjoin R s).to_submodule.fg)
  (h2 : (adjoin (adjoin R s) t).to_submodule.fg) :
  (adjoin R (s ∪ t)).to_submodule.fg :=
begin
  rcases fg_def.1 h1 with ⟨p, hp, hp'⟩,
  rcases fg_def.1 h2 with ⟨q, hq, hq'⟩,
  refine fg_def.2 ⟨p * q, hp.mul hq, le_antisymm _ _⟩,
  { rw [span_le],
    rintros _ ⟨x, y, hx, hy, rfl⟩,
    change x * y ∈ _,
    refine subalgebra.mul_mem _ _ _,
    { have : x ∈ (adjoin R s).to_submodule,
      { rw ← hp', exact subset_span hx },
      exact adjoin_mono (set.subset_union_left _ _) this },
    have : y ∈ (adjoin (adjoin R s) t).to_submodule,
    { rw ← hq', exact subset_span hy },
    change y ∈ adjoin R (s ∪ t), rwa adjoin_union_eq_adjoin_adjoin },
  { intros r hr,
    change r ∈ adjoin R (s ∪ t) at hr,
    rw adjoin_union_eq_adjoin_adjoin at hr,
    change r ∈ (adjoin (adjoin R s) t).to_submodule at hr,
    rw [← hq', ← set.image_id q, finsupp.mem_span_image_iff_total (adjoin R s)] at hr,
    rcases hr with ⟨l, hlq, rfl⟩,
    have := @finsupp.total_apply A A (adjoin R s),
    rw [this, finsupp.sum],
    refine sum_mem _ _,
    intros z hz, change (l z).1 * _ ∈ _,
    have : (l z).1 ∈ (adjoin R s).to_submodule := (l z).2,
    rw [← hp', ← set.image_id p, finsupp.mem_span_image_iff_total R] at this,
    rcases this with ⟨l2, hlp, hl⟩,
    have := @finsupp.total_apply A A R,
    rw this at hl,
    rw [←hl, finsupp.sum_mul],
    refine sum_mem _ _,
    intros t ht, change _ * _ ∈ _, rw smul_mul_assoc, refine smul_mem _ _ _,
    exact subset_span ⟨t, z, hlp ht, hlq hz, rfl⟩ }
end

end algebra

namespace subalgebra

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B]

/-- A subalgebra `S` is finitely generated if there exists `t : finset A` such that
`algebra.adjoin R t = S`. -/
def fg (S : subalgebra R A) : Prop :=
∃ t : finset A, algebra.adjoin R ↑t = S

lemma fg_adjoin_finset (s : finset A) : (algebra.adjoin R (↑s : set A)).fg :=
⟨s, rfl⟩

theorem fg_def {S : subalgebra R A} : S.fg ↔ ∃ t : set A, set.finite t ∧ algebra.adjoin R t = S :=
⟨λ ⟨t, ht⟩, ⟨↑t, set.finite_mem_finset t, ht⟩,
λ ⟨t, ht1, ht2⟩, ⟨ht1.to_finset, by rwa set.finite.coe_to_finset⟩⟩

theorem fg_bot : (⊥ : subalgebra R A).fg :=
⟨∅, algebra.adjoin_empty R A⟩

theorem fg_of_fg_to_submodule {S : subalgebra R A} : S.to_submodule.fg → S.fg :=
λ ⟨t, ht⟩, ⟨t, le_antisymm
  (algebra.adjoin_le (λ x hx, show x ∈ S.to_submodule, from ht ▸ subset_span hx)) $
  show S.to_submodule ≤ (algebra.adjoin R ↑t).to_submodule,
  from (λ x hx, span_le.mpr
    (λ x hx, algebra.subset_adjoin hx)
      (show x ∈ span R ↑t, by { rw ht, exact hx }))⟩

theorem fg_of_noetherian [is_noetherian R A] (S : subalgebra R A) : S.fg :=
fg_of_fg_to_submodule (is_noetherian.noetherian S.to_submodule)

lemma fg_of_submodule_fg (h : (⊤ : submodule R A).fg) : (⊤ : subalgebra R A).fg :=
let ⟨s, hs⟩ := h in ⟨s, to_submodule_injective $
by { rw [algebra.top_to_submodule, eq_top_iff, ← hs, span_le], exact algebra.subset_adjoin }⟩

lemma fg_prod {S : subalgebra R A} {T : subalgebra R B} (hS : S.fg) (hT : T.fg) : (S.prod T).fg :=
begin
  obtain ⟨s, hs⟩ := fg_def.1 hS,
  obtain ⟨t, ht⟩ := fg_def.1 hT,
  rw [← hs.2, ← ht.2],
  exact fg_def.2 ⟨(linear_map.inl R A B '' (s ∪ {1})) ∪ (linear_map.inr R A B '' (t ∪ {1})),
    set.finite.union (set.finite.image _ (set.finite.union hs.1 (set.finite_singleton _)))
    (set.finite.image _ (set.finite.union ht.1 (set.finite_singleton _))),
    algebra.adjoin_inl_union_inr_eq_prod R s t⟩
end

section
open_locale classical
lemma fg_map (S : subalgebra R A) (f : A →ₐ[R] B) (hs : S.fg) : (S.map f).fg :=
let ⟨s, hs⟩ := hs in ⟨s.image f, by rw [finset.coe_image, algebra.adjoin_image, hs]⟩
end

lemma fg_of_fg_map (S : subalgebra R A) (f : A →ₐ[R] B) (hf : function.injective f)
  (hs : (S.map f).fg) : S.fg :=
let ⟨s, hs⟩ := hs in ⟨s.preimage f $ λ _ _ _ _ h, hf h, map_injective f hf $
by { rw [← algebra.adjoin_image, finset.coe_preimage, set.image_preimage_eq_of_subset, hs],
  rw [← alg_hom.coe_range, ← algebra.adjoin_le_iff, hs, ← algebra.map_top], exact map_mono le_top }⟩

lemma fg_top (S : subalgebra R A) : (⊤ : subalgebra R S).fg ↔ S.fg :=
⟨λ h, by { rw [← S.range_val, ← algebra.map_top], exact fg_map _ _ h },
λ h, fg_of_fg_map _ S.val subtype.val_injective $ by { rw [algebra.map_top, range_val], exact h }⟩

lemma induction_on_adjoin [is_noetherian R A] (P : subalgebra R A → Prop)
  (base : P ⊥) (ih : ∀ (S : subalgebra R A) (x : A), P S → P (algebra.adjoin R (insert x S)))
  (S : subalgebra R A) : P S :=
begin
  classical,
  obtain ⟨t, rfl⟩ := S.fg_of_noetherian,
  refine finset.induction_on t _ _,
  { simpa using base },
  intros x t hxt h,
  rw [finset.coe_insert],
  simpa only [algebra.adjoin_insert_adjoin] using ih _ x h,
end

end subalgebra

section semiring

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B]

/-- The image of a Noetherian R-algebra under an R-algebra map is a Noetherian ring. -/
instance alg_hom.is_noetherian_ring_range (f : A →ₐ[R] B) [is_noetherian_ring A] :
  is_noetherian_ring f.range :=
is_noetherian_ring_range f.to_ring_hom

end semiring

section ring

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B]

theorem is_noetherian_ring_of_fg {S : subalgebra R A} (HS : S.fg)
  [is_noetherian_ring R] : is_noetherian_ring S :=
let ⟨t, ht⟩ := HS in ht ▸ (algebra.adjoin_eq_range R (↑t : set A)).symm ▸
by haveI : is_noetherian_ring (mv_polynomial (↑t : set A) R) :=
mv_polynomial.is_noetherian_ring;
convert alg_hom.is_noetherian_ring_range _; apply_instance

theorem is_noetherian_subring_closure (s : set R) (hs : s.finite) :
  is_noetherian_ring (subring.closure s) :=
show is_noetherian_ring (subalgebra_of_subring (subring.closure s)), from
algebra.adjoin_int s ▸ is_noetherian_ring_of_fg (subalgebra.fg_def.2 ⟨s, hs, rfl⟩)

end ring
