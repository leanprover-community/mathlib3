/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser
-/
import linear_algebra.span
import linear_algebra.bilinear_map

/-!
# Images of pairs of submodules under bilinear maps

This file provides `submodule.map₂`, which is later used to implement `submodule.has_mul`.

## Main results

* `submodule.map₂_eq_span_image2`: the image of two submodules under a bilinear map is the span of
  their `set.image2`.

## Notes

This file is quite similar to the n-ary section of `data.set.basic` and to `order.filter.n_ary`.
Please keep them in sync.
-/

universes uι u v

open set
open_locale big_operators
open_locale pointwise

namespace submodule

variables {ι : Sort uι} {R M N P : Type*}
variables [comm_semiring R] [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P]
variables [module R M] [module R N] [module R P]

/-- Map a pair of submodules under a bilinear map.

This is the submodule version of `set.image2`.  -/
def map₂ (f : M →ₗ[R] N →ₗ[R] P) (p : submodule R M) (q : submodule R N) : submodule R P :=
⨆ s : p, q.map $ f s

theorem apply_mem_map₂ (f : M →ₗ[R] N →ₗ[R] P) {m : M} {n : N}
  {p : submodule R M} {q : submodule R N} (hm : m ∈ p) (hn : n ∈ q) : f m n ∈ map₂ f p q :=
(le_supr _ ⟨m, hm⟩ : _ ≤ map₂ f p q) ⟨n, hn, rfl⟩

theorem map₂_le {f : M →ₗ[R] N →ₗ[R] P}
  {p : submodule R M} {q : submodule R N} {r : submodule R P} :
  map₂ f p q ≤ r ↔ ∀ (m ∈ p) (n ∈ q), f m n ∈ r :=
⟨λ H m hm n hn, H $ apply_mem_map₂ _ hm hn,
 λ H, supr_le $ λ ⟨m, hm⟩, map_le_iff_le_comap.2 $ λ n hn, H m hm n hn⟩

variables R
theorem map₂_span_span (f : M →ₗ[R] N →ₗ[R] P) (s : set M) (t : set N) :
  map₂ f (span R s) (span R t) = span R (set.image2 (λ m n, f m n) s t) :=
begin
  apply le_antisymm,
  { rw map₂_le, intros a ha b hb,
    apply span_induction ha,
    work_on_goal 1 { intros, apply span_induction hb,
      work_on_goal 1 { intros, exact subset_span ⟨_, _, ‹_›, ‹_›, rfl⟩ } },
    all_goals {
      intros,
      simp only [linear_map.map_zero, linear_map.zero_apply, zero_mem,
        linear_map.map_add, linear_map.add_apply, linear_map.map_smul, linear_map.smul_apply] },
    all_goals {
      solve_by_elim [add_mem _ _, zero_mem _, smul_mem _ _ _]
        { max_depth := 4, discharger := tactic.interactive.apply_instance } } },
  { rw span_le, rintros _ ⟨a, b, ha, hb, rfl⟩,
    exact apply_mem_map₂ _ (subset_span ha) (subset_span hb) }
end
variables {R}

@[simp] theorem map₂_bot_right (f : M →ₗ[R] N →ₗ[R] P) (p : submodule R M) : map₂ f p ⊥ = ⊥ :=
eq_bot_iff.2 $ map₂_le.2 $ λ m hm n hn,
  by { rw [submodule.mem_bot] at hn ⊢, rw [hn, linear_map.map_zero] }

@[simp] theorem map₂_bot_left (f : M →ₗ[R] N →ₗ[R] P) (q : submodule R N) : map₂ f ⊥ q = ⊥ :=
eq_bot_iff.2 $ map₂_le.2 $ λ m hm n hn,
  by { rw [submodule.mem_bot] at hm ⊢, rw [hm, linear_map.map_zero₂] }

@[mono] theorem map₂_le_map₂ {f : M →ₗ[R] N →ₗ[R] P}
  {p₁ p₂ : submodule R M} {q₁ q₂ : submodule R N} (hp : p₁ ≤ p₂) (hq : q₁ ≤ q₂) :
  map₂ f p₁ q₁ ≤ map₂ f p₂ q₂ :=
map₂_le.2 $ λ m hm n hn, apply_mem_map₂ _ (hp hm) (hq hn)

theorem map₂_le_map₂_left {f : M →ₗ[R] N →ₗ[R] P}
  {p₁ p₂ : submodule R M} {q : submodule R N} (h : p₁ ≤ p₂) : map₂ f p₁ q ≤ map₂ f p₂ q :=
map₂_le_map₂ h (le_refl q)

theorem map₂_le_map₂_right {f : M →ₗ[R] N →ₗ[R] P}
  {p : submodule R M} {q₁ q₂ : submodule R N} (h : q₁ ≤ q₂): map₂ f p q₁ ≤ map₂ f p q₂ :=
map₂_le_map₂ (le_refl p) h

theorem map₂_sup_right (f : M →ₗ[R] N →ₗ[R] P) (p : submodule R M) (q₁ q₂ : submodule R N) :
  map₂ f p (q₁ ⊔ q₂) = map₂ f p q₁ ⊔ map₂ f p q₂ :=
le_antisymm (map₂_le.2 $ λ m hm np hnp, let ⟨n, hn, p, hp, hnp⟩ := mem_sup.1 hnp in
  mem_sup.2 ⟨_, apply_mem_map₂ _ hm hn, _, apply_mem_map₂ _ hm hp, hnp ▸ (map_add _ _ _).symm⟩)
(sup_le (map₂_le_map₂_right le_sup_left) (map₂_le_map₂_right le_sup_right))

theorem map₂_sup_left (f : M →ₗ[R] N →ₗ[R] P) (p₁ p₂ : submodule R M) (q : submodule R N) :
  map₂ f (p₁ ⊔ p₂) q = map₂ f p₁ q ⊔ map₂ f p₂ q :=
le_antisymm (map₂_le.2 $ λ mn hmn p hp, let ⟨m, hm, n, hn, hmn⟩ := mem_sup.1 hmn in
  mem_sup.2 ⟨_, apply_mem_map₂ _ hm hp, _, apply_mem_map₂ _ hn hp,
    hmn ▸ (linear_map.map_add₂ _ _ _ _).symm⟩)
(sup_le (map₂_le_map₂_left le_sup_left) (map₂_le_map₂_left le_sup_right))

lemma image2_subset_map₂ (f : M →ₗ[R] N →ₗ[R] P) (p : submodule R M) (q : submodule R N) :
  set.image2 (λ m n, f m n) (↑p : set M) (↑q : set N) ⊆ (↑(map₂ f p q) : set P) :=
by { rintros _ ⟨i, j, hi, hj, rfl⟩, exact apply_mem_map₂ _ hi hj }

lemma map₂_eq_span_image2 (f : M →ₗ[R] N →ₗ[R] P) (p : submodule R M) (q : submodule R N) :
  map₂ f p q = span R (set.image2 (λ m n, f m n) (p : set M) (q : set N)) :=
by rw [← map₂_span_span, span_eq, span_eq]

lemma map₂_supr_left (f : M →ₗ[R] N →ₗ[R] P) (s : ι → submodule R M) (t : submodule R N) :
  map₂ f (⨆ i, s i) t = ⨆ i, map₂ f (s i) t :=
begin
  suffices :
    map₂ f (⨆ i, span R (s i : set M)) (span R t) = (⨆ i, map₂ f (span R (s i)) (span R t)),
  { simpa only [span_eq] using this },
  simp_rw [map₂_span_span, ← span_Union, map₂_span_span, set.image2_Union_left],
end

lemma map₂_supr_right (f : M →ₗ[R] N →ₗ[R] P) (s : submodule R M) (t : ι → submodule R N) :
  map₂ f s (⨆ i, t i) = ⨆ i, map₂ f s (t i) :=
begin
  suffices :
    map₂ f (span R s) (⨆ i, span R (t i : set N)) = (⨆ i, map₂ f (span R s) (span R (t i))),
  { simpa only [span_eq] using this },
  simp_rw [map₂_span_span, ← span_Union, map₂_span_span, set.image2_Union_right],
end

end submodule
