/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import topology.algebra.algebra
import topology.continuous_function.compact
import topology.urysohns_lemma
import data.complex.is_R_or_C

/-!
# Ideals of continuous functions

For a topological ring `R` and a topological space `X` there is a Galois connection between
`ideal C(X, R)` and `set X` given by sending each `I : ideal C(X, R)` to
`{x : X | ∀ f ∈ I, f x = 0}ᶜ` and mapping `s : set X` to the ideal with carrier
`{f : C(X, R) | ∀ x ∈ sᶜ, f x = 0}`, and we call these maps `continuous_map.set_of_ideal` and
`continuous_map.ideal_of_set`. As long as `R` is Hausdorff, `continuous_map.set_of_ideal I` is open,
and if, in addition, `X` is locally compact, then `continuous_map.set_of_ideal s` is closed.

When `R = 𝕜` with `is_R_or_C 𝕜` and `X` is compact Hausdorff, then this Galois connection can be
improved to a true Galois correspondence (i.e., order isomorphism) between the type `opens X` and
the subtype of closed ideals of `C(X, R)`.

## Main definitions

* `continuous_map.ideal_of_set`: ideal of functions which vanish on the complement of a set.
* `continuous_map.set_of_ideal`: complement of the set on which all functions in the ideal vanish.
* `continuous_map.opens_of_ideal`: `continuous_map.set_of_ideal` as a term of `opens X`.
* `continuous_map.ideal_opens_gi`: The Galois insertion `continuous_map.opens_of_ideal` and
  `λ s, continuous_map.ideal_of_set ↑s`.

## Main statements

* `ideal_of_set_of_ideal_eq_closure`: when `X` is compact Hausdorff and `is_R_or_C 𝕜`,
  `ideal_of_set 𝕜 (set_of_ideal I) = I.closure` for any ideal `I : ideal C(X, 𝕜)`.
* `set_of_ideal_of_set_eq_interior`: when `X` is compact Hausdorff and `is_R_or_C 𝕜`,
  `set_of_ideal (ideal_of_set 𝕜 s) = interior s` for any `s : set X`.

## Implementation details

Because there does not currently exist a bundled type of closed ideals, we don't provide the actual
order isomorphism described above, and instead we only consider the Galois insertion
`continuous_map.ideal_opens_gi`.

## TODO

* Show that maximal ideals in `C(X, 𝕜)` correspond to (complements of) singletons.

## Tags

ideal, continuous function, compact, Hausdorff
-/


open_locale nnreal

namespace continuous_map

open topological_space

section topological_ring

variables {X R : Type*} [topological_space X] [ring R] [topological_space R] [topological_ring R]

variable (R)

/-- Given a topological ring `R` and `s : set X`, construct the ideal in `C(X, R)` of functions
which vanish on the complement of `s`. -/
def ideal_of_set (s : set X) : ideal C(X, R) :=
{ carrier := {f : C(X, R) | ∀ x ∈ sᶜ, f x = 0},
  add_mem' := λ f g hf hg x hx, by simp only [hf x hx, hg x hx, coe_add, pi.add_apply, add_zero],
  zero_mem' := λ _ _, rfl,
  smul_mem' := λ c f hf x hx, mul_zero (c x) ▸ congr_arg (λ y, c x * y) (hf x hx), }

lemma ideal_of_set_closed [locally_compact_space X] [t2_space R] (s : set X) :
  is_closed (ideal_of_set R s : set C(X, R) ) :=
begin
  simp only [ideal_of_set, submodule.coe_set_mk, set.set_of_forall],
  exact is_closed_Inter (λ x, is_closed_Inter $
    λ hx, is_closed_eq (continuous_eval_const' x) continuous_const),
end

variable {R}

lemma mem_ideal_of_set {s : set X} {f : C(X, R)} :
  f ∈ ideal_of_set R s ↔ ∀ ⦃x : X⦄, x ∈ sᶜ → f x = 0 := iff.rfl

lemma not_mem_ideal_of_set {s : set X} {f : C(X, R)} :
  f ∉ ideal_of_set R s ↔ ∃ x ∈ sᶜ, f x ≠ 0 :=
by { simp_rw [mem_ideal_of_set, exists_prop], push_neg }

/-- Given an ideal `I` of `C(X, R)`, construct the set of points for which every function in the
ideal vanishes on the complement. -/
def set_of_ideal (I : ideal C(X, R)) : set X :=
{x : X | ∀ f ∈ I, (f : C(X, R)) x = 0}ᶜ

lemma not_mem_set_of_ideal {I : ideal C(X, R)} {x : X} :
  x ∉ set_of_ideal I ↔ ∀ ⦃f : C(X, R)⦄, f ∈ I → f x = 0 :=
by rw [←set.mem_compl_iff, set_of_ideal, compl_compl, set.mem_set_of]

lemma mem_set_of_ideal {I : ideal C(X, R)} {x : X} :
  x ∈ set_of_ideal I ↔ ∃ f ∈ I, (f : C(X, R)) x ≠ 0 :=
by { simp_rw [set_of_ideal, set.mem_compl_iff, set.mem_set_of, exists_prop], push_neg }

lemma set_of_ideal_open [t2_space R] (I : ideal C(X, R)) : is_open (set_of_ideal I) :=
begin
  simp only [set_of_ideal, set.set_of_forall, is_open_compl_iff],
  exact is_closed_Inter (λ f, is_closed_Inter $
    λ hf, is_closed_eq (map_continuous f) continuous_const)
end

/-- The open set `set_of_ideal I` realized as a term of `opens X`. -/
@[simps] def opens_of_ideal [t2_space R] (I : ideal C(X, R)) : opens X :=
⟨set_of_ideal I, set_of_ideal_open I⟩

@[simp] lemma set_of_top_eq_univ [nontrivial R] : (set_of_ideal (⊤ : ideal C(X, R))) = set.univ :=
set.univ_subset_iff.mp $ λ x hx, mem_set_of_ideal.mpr ⟨1, submodule.mem_top, one_ne_zero⟩

@[simp] lemma ideal_of_empty_eq_bot : (ideal_of_set R (∅ : set X)) = ⊥ :=
ideal.ext (λ f, by simpa only [mem_ideal_of_set, set.compl_empty, set.mem_univ, forall_true_left,
  ideal.mem_bot, fun_like.ext_iff] using iff.rfl)

variables (X R)
lemma ideal_gc : galois_connection (set_of_ideal : ideal C(X, R) → set X) (ideal_of_set R) :=
begin
  refine λ I s, ⟨λ h f hf, _, λ h x hx, _⟩,
  { by_contra h',
    rcases not_mem_ideal_of_set.mp h' with ⟨x, hx, hfx⟩,
    exact hfx (not_mem_set_of_ideal.mp (mt (@h x) hx) hf) },
  { obtain ⟨f, hf, hfx⟩ := mem_set_of_ideal.mp hx,
    by_contra hx',
    exact not_mem_ideal_of_set.mpr ⟨x, hx', hfx⟩ (h hf) },
end

end topological_ring

section is_R_or_C
open is_R_or_C

variables {X 𝕜 : Type*} [is_R_or_C 𝕜] [topological_space X]

/-- An auxiliary lemma used in the proof of `ideal_of_set_of_ideal_eq_closure` which may be useful
on its own. -/
lemma exists_mul_le_one_eq_on_ge (f : C(X, ℝ≥0)) {c : ℝ≥0} (hc : 0 < c) :
  ∃ g : C(X, ℝ≥0), (∀ x : X, (g * f) x ≤ 1) ∧ {x : X | c ≤ f x}.eq_on (g * f) 1 :=
⟨{ to_fun := (f ⊔ (const X c))⁻¹,
   continuous_to_fun := ((map_continuous f).sup $ map_continuous _).inv₀
     (λ _, (hc.trans_le le_sup_right).ne')},
 λ x, (inv_mul_le_iff (hc.trans_le le_sup_right)).mpr ((mul_one (f x ⊔ c)).symm ▸ le_sup_left),
 λ x hx, by simpa only [coe_const, coe_mk, pi.mul_apply, pi.inv_apply, pi.sup_apply,
   function.const_apply, pi.one_apply, sup_eq_left.mpr (set.mem_set_of.mp hx)]
   using inv_mul_cancel (hc.trans_le hx).ne'⟩

@[simp] lemma ideal_of_set_of_ideal_eq_closure [compact_space X] [t2_space X] (I : ideal C(X, 𝕜)) :
  ideal_of_set 𝕜 (set_of_ideal I) = I.closure :=
begin
  /- Since `ideal_of_set 𝕜 (set_of_ideal I)` is closed and contains `I`, it contains `I.closure`.
  For the reverse inclusion, given `f ∈ ideal_of_set 𝕜 (set_of_ideal I)` and `(ε : ℝ≥0) > 0` it
  suffices to show that `f` is within `ε` of `I`.-/
  refine le_antisymm (λ f hf, metric.mem_closure_iff.mpr (λ ε hε, _))
    ((ideal_of_set_closed 𝕜 $ set_of_ideal I).closure_subset_iff.mpr $
    λ f hf x hx, not_mem_set_of_ideal.mp hx hf),
  lift ε to ℝ≥0 using hε.lt.le,
  replace hε := (show (0 : ℝ≥0) < ε, from hε),
  simp_rw dist_nndist,
  norm_cast,
  -- Let `t := {x : X | ε / 2 ≤ ∥f x∥₊}}` which is closed and disjoint from `set_of_ideal I`.
  set t := {x : X | ε / 2 ≤ ∥f x∥₊},
  have ht : is_closed t := is_closed_le continuous_const (map_continuous f).nnnorm,
  have htI : disjoint t (set_of_ideal I)ᶜ,
  { refine set.subset_compl_iff_disjoint_left.mp (λ x hx, _),
    simpa only [t, set.mem_set_of, set.mem_compl_iff, not_le]
      using (nnnorm_eq_zero.mpr (mem_ideal_of_set.mp hf hx)).trans_lt (half_pos hε), },
  /- It suffices to produce `g : C(X, ℝ≥0)` which takes values in `[0,1]` and is constantly `1` on
  `t` such that when composed with the natural embedding of `ℝ≥0` into `𝕜` lies in the ideal `I`.
  Indeed, then `∥f - f * ↑g∥ ≤ ∥f * (1 - ↑g)∥ ≤ ⨆ ∥f * (1 - ↑g) x∥`. When `x ∉ t`, `∥f x∥ < ε / 2`
  and `∥(1 - ↑g) x∥ ≤ 1`, and when `x ∈ t`, `(1 - ↑g) x = 0`, and clearly `f * ↑g ∈ I`. -/
  suffices : ∃ g : C(X, ℝ≥0),
    (algebra_map_clm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g ∈ I ∧ (∀ x, g x ≤ 1) ∧ t.eq_on g 1,
  { obtain ⟨g, hgI, hg, hgt⟩ := this,
    refine ⟨f * (algebra_map_clm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g, I.mul_mem_left f hgI, _⟩,
    rw nndist_eq_nnnorm,
    refine (nnnorm_lt_iff _ hε).2 (λ x, _),
    simp only [coe_sub, coe_mul, pi.sub_apply, pi.mul_apply],
    by_cases hx : x ∈ t,
    { simpa only [hgt hx, comp_apply, pi.one_apply, continuous_map.coe_coe, algebra_map_clm_apply,
        map_one, mul_one, sub_self, nnnorm_zero] using hε, },
    { refine lt_of_le_of_lt _ (half_lt_self hε),
      have := calc ∥((1 - (algebra_map_clm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) x : 𝕜)∥₊
            = ∥1 - algebra_map ℝ≥0 𝕜 (g x)∥₊
            : by simp only [coe_sub, coe_one, coe_comp, continuous_map.coe_coe, pi.sub_apply,
                pi.one_apply, function.comp_app, algebra_map_clm_apply]
        ... = ∥algebra_map ℝ≥0 𝕜 (1 - g x)∥₊
            : by simp only [algebra.algebra_map_eq_smul_one, nnreal.smul_def, nnreal.coe_sub (hg x),
                sub_smul, nonneg.coe_one, one_smul]
        ... ≤ 1 : (nnnorm_algebra_map_nnreal 𝕜 (1 - g x)).trans_le tsub_le_self,
      calc ∥f x - f x * (algebra_map_clm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g x∥₊
          = ∥f x * (1 - (algebra_map_clm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) x∥₊
          : by simp only [mul_sub, coe_sub, coe_one, pi.sub_apply, pi.one_apply, mul_one]
      ... ≤ (ε / 2) * ∥(1 - (algebra_map_clm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) x∥₊
          : (nnnorm_mul_le _ _).trans (mul_le_mul_right'
              (not_le.mp $ show ¬ ε / 2 ≤ ∥f x∥₊, from hx).le _)
      ... ≤ ε / 2 : by simpa only [mul_one] using mul_le_mul_left' this _, } },
  /- There is some `g' : C(X, ℝ≥0)` which is strictly positive on `t` such that the composition
  `↑g` with the natural embedding of `ℝ≥0` into `𝕜` lies in `I`. This follows from compactness of
  `t` and that we can do it in any neighborhood of a point `x ∈ t`. Indeed, since `x ∈ t`, then
  `fₓ x ≠ 0` for some `fₓ ∈ I` and so `λ y, ∥(star fₓ * fₓ) y∥₊` is strictly posiive in a
  neighborhood of `y`. Moreover, `(∥(star fₓ * fₓ) y∥₊ : 𝕜) = (star fₓ * fₓ) y`, so composition of
  this map with the natural embedding is just `star fₓ * fₓ ∈ I`. -/
  have : ∃ g' : C(X, ℝ≥0), (algebra_map_clm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g' ∈ I ∧ (∀ x ∈ t, 0 < g' x),
  { refine @is_compact.induction_on _ _ _ ht.is_compact (λ s, ∃ g' : C(X, ℝ≥0),
      (algebra_map_clm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g' ∈ I ∧ (∀ x ∈ s, 0 < g' x)) _ _ _ _,
    { refine ⟨0, _, λ x hx, false.elim hx⟩,
      convert I.zero_mem,
      ext,
      simp only [coe_zero, pi.zero_apply, continuous_map.coe_coe, continuous_map.coe_comp,
        map_zero, pi.comp_zero] },
    { rintro s₁ s₂ hs ⟨g, hI, hgt⟩, exact ⟨g, hI, λ x hx, hgt x (hs hx)⟩, },
    { rintro s₁ s₂ ⟨g₁, hI₁, hgt₁⟩ ⟨g₂, hI₂, hgt₂⟩,
      refine ⟨g₁ + g₂, _, λ x hx, _⟩,
      { convert I.add_mem hI₁ hI₂,
        ext y,
        simp only [coe_add, pi.add_apply, map_add, coe_comp, function.comp_app,
          continuous_map.coe_coe]},
      { rcases hx with (hx | hx),
        simpa only [zero_add] using add_lt_add_of_lt_of_le (hgt₁ x hx) zero_le',
        simpa only [zero_add] using add_lt_add_of_le_of_lt zero_le' (hgt₂ x hx), } },
    { intros x hx,
      replace hx := htI.subset_compl_right hx,
      rw [compl_compl, mem_set_of_ideal] at hx,
      obtain ⟨g, hI, hgx⟩ := hx,
      have := (map_continuous g).continuous_at.eventually_ne hgx,
      refine ⟨{y : X | g y ≠ 0} ∩ t, mem_nhds_within_iff_exists_mem_nhds_inter.mpr
        ⟨_, this, set.subset.rfl⟩, ⟨⟨λ x, ∥g x∥₊ ^ 2, (map_continuous g).nnnorm.pow 2⟩, _,
        λ x hx, pow_pos (norm_pos_iff.mpr hx.1) 2⟩⟩,
      convert I.mul_mem_left (star g) hI,
      ext,
      simp only [comp_apply, coe_mk, algebra_map_clm_coe, map_pow, coe_mul, coe_star,
        pi.mul_apply, pi.star_apply, star_def, continuous_map.coe_coe],
      simpa only [norm_sq_eq_def', conj_mul_eq_norm_sq_left, of_real_pow], }, },
  /- Get the function `g'` which is guaranteed to exist above. By the extreme value theorem and
  compactness of `t`, there is some `0 < c` such that `c ≤ g' x` for all `x ∈ t`. Then by
  `main_lemma_aux` there is some `g` for which `g * g'` is the desired function. -/
  obtain ⟨g', hI', hgt'⟩ := this,
  obtain (⟨c, hc, hgc'⟩ : ∃ c (hc : 0 < c), ∀ y : X, y ∈ t → c ≤ g' y) :=
  t.eq_empty_or_nonempty.elim (λ ht', ⟨1, zero_lt_one, λ y hy, false.elim (by rwa ht' at hy)⟩)
    (λ ht', let ⟨x, hx, hx'⟩ := ht.is_compact.exists_forall_le ht' (map_continuous g').continuous_on
      in ⟨g' x, hgt' x hx, hx'⟩),
  obtain ⟨g, hg, hgc⟩ := exists_mul_le_one_eq_on_ge g' hc,
  refine ⟨g * g', _, hg, hgc.mono hgc'⟩,
  convert I.mul_mem_left ((algebra_map_clm ℝ≥0 𝕜 : C(ℝ≥0, 𝕜)).comp g) hI',
  ext,
  simp only [algebra_map_clm_coe, continuous_map.coe_coe, comp_apply, coe_mul, pi.mul_apply,
    map_mul],
end

lemma ideal_of_set_of_ideal_is_closed [compact_space X] [t2_space X] {I : ideal C(X, 𝕜)}
  (hI : is_closed (I : set C(X, 𝕜))) : ideal_of_set 𝕜 (set_of_ideal I) = I :=
(ideal_of_set_of_ideal_eq_closure I).trans (ideal.ext $ set.ext_iff.mp hI.closure_eq)

variable (𝕜)

@[simp] lemma set_of_ideal_of_set_eq_interior [compact_space X] [t2_space X] (s : set X) :
  set_of_ideal (ideal_of_set 𝕜 s) = interior s:=
begin
  refine set.subset.antisymm ((set_of_ideal_open (ideal_of_set 𝕜 s)).subset_interior_iff.mpr
    (λ x hx, let ⟨f, hf, hfx⟩ := mem_set_of_ideal.mp hx
    in set.not_mem_compl_iff.mp (mt (@hf x) hfx))) (λ x hx, _),
  /- If `x ∉ closure sᶜ`, we must produce `f : C(X, 𝕜)` which is zero on `sᶜ` and `f x ≠ 0`. -/
  rw [←compl_compl (interior s), ←closure_compl] at hx,
  simp_rw [mem_set_of_ideal, mem_ideal_of_set],
  haveI : normal_space X := normal_of_compact_t2,
  /- Apply Urysohn's lemma to get `g : C(X, ℝ)` which is zero on `sᶜ` and `g x ≠ 0`, then compose
  with the natural embedding `ℝ ↪ 𝕜` to produce the desired `f`. -/
  obtain ⟨g, hgs, (hgx : set.eq_on g 1 {x}), -⟩ := exists_continuous_zero_one_of_closed
    is_closed_closure is_closed_singleton (set.disjoint_singleton_right.mpr hx),
  exact ⟨⟨λ x, g x, continuous_of_real.comp (map_continuous g)⟩,
    by simpa only [coe_mk, of_real_eq_zero] using λ x hx, hgs (subset_closure hx),
    by simpa only [coe_mk, hgx (set.mem_singleton x), pi.one_apply, is_R_or_C.of_real_one]
      using one_ne_zero⟩,
end

lemma set_of_ideal_of_set_of_is_open [compact_space X] [t2_space X] {s : set X}
  (hs : is_open s) : set_of_ideal (ideal_of_set 𝕜 s) = s :=
(set_of_ideal_of_set_eq_interior 𝕜 s).trans hs.interior_eq

variable (X)

/-- The Galois insertion `continuous_map.opens_of_ideal : ideal C(X, 𝕜) → opens X` and
`λ s, continuous_map.ideal_of_set ↑s`. -/
@[simps] def ideal_opens_gi [compact_space X] [t2_space X] :
  galois_insertion (opens_of_ideal : ideal C(X, 𝕜) → opens X) (λ s, ideal_of_set 𝕜 s) :=
{ choice := λ I hI, opens_of_ideal I.closure,
  gc := λ I s, ideal_gc X 𝕜 I s,
  le_l_u := λ s, (set_of_ideal_of_set_of_is_open 𝕜 s.prop).ge,
  choice_eq := λ I hI, congr_arg _ $ ideal.ext (set.ext_iff.mp (is_closed_of_closure_subset $
    (ideal_of_set_of_ideal_eq_closure I ▸ hI : I.closure ≤ I)).closure_eq) }

end is_R_or_C

end continuous_map
