/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.algebra.subalgebra
import linear_algebra.prod

/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of subalgebras of an R-algebra generated
by a set of elements. A basic interface for `adjoin` is set up, and various
results about finitely-generated subalgebras and submodules are proved.

## Definitions

* `fg (S : subalgebra R A)` : A predicate saying that the subalgebra is finitely-generated
as an A-algebra

## Tags

adjoin, algebra, finitely-generated algebra

-/

universes u v w

open submodule
open_locale pointwise

namespace algebra

variables {R : Type u} {A : Type v} {B : Type w}

section semiring
variables [comm_semiring R] [semiring A] [semiring B]
variables [algebra R A] [algebra R B] {s t : set A}
open subsemiring

theorem subset_adjoin : s ⊆ adjoin R s :=
algebra.gc.le_u_l s

theorem adjoin_le {S : subalgebra R A} (H : s ⊆ S) : adjoin R s ≤ S :=
algebra.gc.l_le H

theorem adjoin_le_iff {S : subalgebra R A} : adjoin R s ≤ S ↔ s ⊆ S:=
algebra.gc _ _

theorem adjoin_mono (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
algebra.gc.monotone_l H

theorem adjoin_eq_of_le (S : subalgebra R A) (h₁ : s ⊆ S) (h₂ : S ≤ adjoin R s) : adjoin R s = S :=
le_antisymm (adjoin_le h₁) h₂

theorem adjoin_eq (S : subalgebra R A) : adjoin R ↑S = S :=
adjoin_eq_of_le _ (set.subset.refl _) subset_adjoin

@[elab_as_eliminator] theorem adjoin_induction {p : A → Prop} {x : A} (h : x ∈ adjoin R s) 
  (Hs : ∀ x ∈ s, p x)
  (Halg : ∀ r, p (algebra_map R A r))
  (Hadd : ∀ x y, p x → p y → p (x + y))
  (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
let S : subalgebra R A :=
{ carrier := p, mul_mem' := Hmul, add_mem' := Hadd, algebra_map_mem' := Halg } in
adjoin_le (show s ≤ S, from Hs) h

lemma adjoin_union (s t : set A) : adjoin R (s ∪ t) = adjoin R s ⊔ adjoin R t :=
(algebra.gc : galois_connection _ (coe : subalgebra R A → set A)).l_sup

variables (R A)
@[simp] theorem adjoin_empty : adjoin R (∅ : set A) = ⊥ :=
show adjoin R ⊥ = ⊥, by { apply galois_connection.l_bot, exact algebra.gc }

@[simp] theorem adjoin_univ : adjoin R (set.univ : set A) = ⊤ :=
eq_top_iff.2 $ λ x, subset_adjoin $ set.mem_univ _

variables (R) {A} (s)

theorem adjoin_eq_span : (adjoin R s).to_submodule = span R (submonoid.closure s) :=
begin
  apply le_antisymm,
  { intros r hr, rcases subsemiring.mem_closure_iff_exists_list.1 hr with ⟨L, HL, rfl⟩, clear hr,
    induction L with hd tl ih, { exact zero_mem _ },
    rw list.forall_mem_cons at HL,
    rw [list.map_cons, list.sum_cons],
    refine submodule.add_mem _ _ (ih HL.2),
    replace HL := HL.1, clear ih tl,
    suffices : ∃ z r (hr : r ∈ submonoid.closure s), has_scalar.smul z r = list.prod hd,
    { rcases this with ⟨z, r, hr, hzr⟩, rw ← hzr,
      exact smul_mem _ _ (subset_span hr) },
    induction hd with hd tl ih, { exact ⟨1, 1, (submonoid.closure s).one_mem', one_smul _ _⟩ },
    rw list.forall_mem_cons at HL,
    rcases (ih HL.2) with ⟨z, r, hr, hzr⟩, rw [list.prod_cons, ← hzr],
    rcases HL.1 with ⟨hd, rfl⟩ | hs,
    { refine ⟨hd * z, r, hr, _⟩,
      rw [algebra.smul_def, algebra.smul_def, (algebra_map _ _).map_mul, _root_.mul_assoc] },
    { exact ⟨z, hd * r, submonoid.mul_mem _ (submonoid.subset_closure hs) hr,
        (mul_smul_comm _ _ _).symm⟩ } },
  refine span_le.2 _,
  change submonoid.closure s ≤ (adjoin R s).to_subsemiring.to_submonoid,
  exact submonoid.closure_le.2 subset_adjoin
end

lemma span_le_adjoin (s : set A) : span R s ≤ (adjoin R s).to_submodule :=
span_le.mpr subset_adjoin

lemma adjoin_to_submodule_le {s : set A} {t : submodule R A} :
  (adjoin R s).to_submodule ≤ t ↔ ↑(submonoid.closure s) ⊆ (t : set A) :=
by rw [adjoin_eq_span, span_le]

lemma adjoin_eq_span_of_subset {s : set A} (hs : ↑(submonoid.closure s) ⊆ (span R s : set A)) :
  (adjoin R s).to_submodule = span R s :=
le_antisymm ((adjoin_to_submodule_le R).mpr hs) (span_le_adjoin R s)

lemma adjoin_image (f : A →ₐ[R] B) (s : set A) :
  adjoin R (f '' s) = (adjoin R s).map f :=
le_antisymm (adjoin_le $ set.image_subset _ subset_adjoin) $
subalgebra.map_le.2 $ adjoin_le $ set.image_subset_iff.1 subset_adjoin

@[simp] lemma adjoin_insert_adjoin (x : A) :
  adjoin R (insert x ↑(adjoin R s)) = adjoin R (insert x s) :=
le_antisymm
  (adjoin_le (set.insert_subset.mpr
    ⟨subset_adjoin (set.mem_insert _ _), adjoin_mono (set.subset_insert _ _)⟩))
  (algebra.adjoin_mono (set.insert_subset_insert algebra.subset_adjoin))

lemma adjoint_prod_le (s : set A) (t : set B) :
  adjoin R (set.prod s t) ≤ (adjoin R s).prod (adjoin R t) :=
adjoin_le $ set.prod_mono subset_adjoin subset_adjoin

lemma adjoin_inl_union_inr_le_prod (s) (t) :
  adjoin R (linear_map.inl R A B '' (s ∪ {1}) ∪
  linear_map.inr R A B '' (t ∪ {1})) ≤ (adjoin R s).prod (adjoin R t) :=
begin
  rw [set.image_union, set.image_union],
  refine adjoin_le (λ x hx, subalgebra.mem_prod.2 _),
  rcases hx with (⟨x₁, ⟨hx₁, rfl⟩⟩ | ⟨x₂, ⟨hx₂, rfl⟩⟩) | (⟨x₃, ⟨hx₃, rfl⟩⟩ | ⟨x₄, ⟨hx₄, rfl⟩⟩),
  { exact ⟨subset_adjoin hx₁, subalgebra.zero_mem _⟩ },
  { rw set.mem_singleton_iff.1 hx₂,
    exact ⟨subalgebra.one_mem _, subalgebra.zero_mem _⟩ },
  { exact ⟨subalgebra.zero_mem _, subset_adjoin hx₃⟩ },
  { rw set.mem_singleton_iff.1 hx₄,
    exact ⟨subalgebra.zero_mem _, subalgebra.one_mem _⟩ }
end

lemma mem_adjoin_of_map_mul {s} {x : A} {f : A →ₗ[R] B} (hf : ∀ a₁ a₂, f(a₁ * a₂) = f a₁ * f a₂)
  (h : x ∈ adjoin R s) : f x ∈ adjoin R (f '' (s ∪ {1})) :=
begin
  refine @adjoin_induction R A _ _ _ _ (λ a, f a ∈ adjoin R (f '' (s ∪ {1}))) x h
  (λ a ha, subset_adjoin ⟨a, ⟨set.subset_union_left _ _ ha, rfl⟩⟩)
  (λ r, _)
  (λ y z hy hz, by simpa [hy, hz] using subalgebra.add_mem _ hy hz)
  (λ y z hy hz, by simpa [hy, hz, hf y z] using subalgebra.mul_mem _ hy hz),
  have : f 1 ∈ adjoin R (f '' (s ∪ {1})) :=
  subset_adjoin ⟨1, ⟨set.subset_union_right _ _ $ set.mem_singleton 1, rfl⟩⟩,
  replace this := subalgebra.smul_mem (adjoin R (f '' (s ∪ {1}))) this r,
  convert this,
  rw algebra_map_eq_smul_one,
  exact f.map_smul _ _
end

lemma adjoin_inl_union_inr_eq_prod (s) (t) :
  adjoin R (linear_map.inl R A B '' (s ∪ {1}) ∪
  linear_map.inr R A B '' (t ∪ {1})) = (adjoin R s).prod (adjoin R t) :=
begin
  let P := adjoin R (linear_map.inl R A B '' (s ∪ {1}) ∪ linear_map.inr R A B '' (t ∪ {1})),
  refine le_antisymm (adjoin_inl_union_inr_le_prod R s t) _,
  rintro ⟨a, b⟩ ⟨ha, hb⟩,
  have Ha : (a, (0 : B)) ∈ adjoin R ((linear_map.inl R A B) '' (s ∪ {1})) :=
    mem_adjoin_of_map_mul R (linear_map.inl_map_mul) ha,
  have Hb : ((0 : A), b) ∈ adjoin R ((linear_map.inr R A B) '' (t ∪ {1})) :=
    mem_adjoin_of_map_mul R (linear_map.inr_map_mul) hb,
  replace Ha : (a, (0 : B)) ∈ P :=
    adjoin_mono (set.subset_union_of_subset_left (set.subset.refl _) _) Ha,
  replace Hb : ((0 : A), b) ∈ P :=
    adjoin_mono (set.subset_union_of_subset_right (set.subset.refl _) _) Hb,
  simpa using subalgebra.add_mem _ Ha Hb
end

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A]
variables [algebra R A] {s t : set A}
open subsemiring

variables (R s t)
theorem adjoin_union_eq_under : adjoin R (s ∪ t) = (adjoin R s).under (adjoin (adjoin R s) t) :=
le_antisymm
  (closure_mono $ set.union_subset
    (set.range_subset_iff.2 $ λ r, or.inl ⟨algebra_map R (adjoin R s) r, rfl⟩)
    (set.union_subset_union_left _ $ λ x hxs, ⟨⟨_, subset_adjoin hxs⟩, rfl⟩))
  (closure_le.2 $ set.union_subset
    (set.range_subset_iff.2 $ λ x, adjoin_mono (set.subset_union_left _ _) x.2)
    (set.subset.trans (set.subset_union_right _ _) subset_adjoin))

lemma adjoin_singleton_one : adjoin R ({1} : set A) = ⊥ :=
eq_bot_iff.2 $ adjoin_le $ set.singleton_subset_iff.2 $ set_like.mem_coe.2 $ one_mem _

theorem adjoin_union_coe_submodule : (adjoin R (s ∪ t)).to_submodule =
  (adjoin R s).to_submodule * (adjoin R t).to_submodule :=
begin
  rw [adjoin_eq_span, adjoin_eq_span, adjoin_eq_span, span_mul_span],
  congr' 1 with z, simp [submonoid.closure_union, submonoid.mem_sup, set.mem_mul]
end

end comm_semiring

section ring
variables [comm_ring R] [ring A]
variables [algebra R A] {s t : set A}
variables {R s t}

theorem adjoin_int (s : set R) : adjoin ℤ s = subalgebra_of_subring (subring.closure s) :=
le_antisymm (adjoin_le subring.subset_closure)
  (subring.closure_le.2 subset_adjoin : subring.closure s ≤ (adjoin ℤ s).to_subring)

theorem mem_adjoin_iff {s : set A} {x : A} :
  x ∈ adjoin R s ↔ x ∈ subring.closure (set.range (algebra_map R A) ∪ s) :=
⟨λ hx, subsemiring.closure_induction hx subring.subset_closure (subring.zero_mem _)
  (subring.one_mem _) (λ _ _, subring.add_mem _) ( λ _ _, subring.mul_mem _),
  suffices subring.closure (set.range ⇑(algebra_map R A) ∪ s) ≤ (adjoin R s).to_subring,
    from @this x, subring.closure_le.2 subsemiring.subset_closure⟩

theorem adjoin_eq_ring_closure (s : set A) :
  (adjoin R s).to_subring = subring.closure (set.range (algebra_map R A) ∪ s) :=
subring.ext $ λ x, mem_adjoin_iff

end ring

end algebra
