/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.complex.basic
import topology.fiber_bundle.is_homeomorphic_trivial_bundle

/-!
# Closure, interior, and frontier of preimages under `re` and `im`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this fact we use the fact that `ℂ` is naturally homeomorphic to `ℝ × ℝ` to deduce some
topological properties of `complex.re` and `complex.im`.

## Main statements

Each statement about `complex.re` listed below has a counterpart about `complex.im`.

* `complex.is_homeomorphic_trivial_fiber_bundle_re`: `complex.re` turns `ℂ` into a trivial
  topological fiber bundle over `ℝ`;
* `complex.is_open_map_re`, `complex.quotient_map_re`: in particular, `complex.re` is an open map
  and is a quotient map;
* `complex.interior_preimage_re`, `complex.closure_preimage_re`, `complex.frontier_preimage_re`:
  formulas for `interior (complex.re ⁻¹' s)` etc;
* `complex.interior_set_of_re_le` etc: particular cases of the above formulas in the cases when `s`
  is one of the infinite intervals `set.Ioi a`, `set.Ici a`, `set.Iio a`, and `set.Iic a`,
  formulated as `interior {z : ℂ | z.re ≤ a} = {z | z.re < a}` etc.

## Tags

complex, real part, imaginary part, closure, interior, frontier
-/

open set
noncomputable theory

namespace complex

/-- `complex.re` turns `ℂ` into a trivial topological fiber bundle over `ℝ`. -/
lemma is_homeomorphic_trivial_fiber_bundle_re : is_homeomorphic_trivial_fiber_bundle ℝ re :=
⟨equiv_real_prod_clm.to_homeomorph, λ z, rfl⟩

/-- `complex.im` turns `ℂ` into a trivial topological fiber bundle over `ℝ`. -/
lemma is_homeomorphic_trivial_fiber_bundle_im : is_homeomorphic_trivial_fiber_bundle ℝ im :=
⟨equiv_real_prod_clm.to_homeomorph.trans (homeomorph.prod_comm ℝ ℝ), λ z, rfl⟩

lemma is_open_map_re : is_open_map re := is_homeomorphic_trivial_fiber_bundle_re.is_open_map_proj
lemma is_open_map_im : is_open_map im := is_homeomorphic_trivial_fiber_bundle_im.is_open_map_proj

lemma quotient_map_re : quotient_map re := is_homeomorphic_trivial_fiber_bundle_re.quotient_map_proj
lemma quotient_map_im : quotient_map im := is_homeomorphic_trivial_fiber_bundle_im.quotient_map_proj

lemma interior_preimage_re (s : set ℝ) : interior (re ⁻¹' s) = re ⁻¹' (interior s) :=
(is_open_map_re.preimage_interior_eq_interior_preimage continuous_re _).symm

lemma interior_preimage_im (s : set ℝ) : interior (im ⁻¹' s) = im ⁻¹' (interior s) :=
(is_open_map_im.preimage_interior_eq_interior_preimage continuous_im _).symm

lemma closure_preimage_re (s : set ℝ) : closure (re ⁻¹' s) = re ⁻¹' (closure s) :=
(is_open_map_re.preimage_closure_eq_closure_preimage continuous_re _).symm

lemma closure_preimage_im (s : set ℝ) : closure (im ⁻¹' s) = im ⁻¹' (closure s) :=
(is_open_map_im.preimage_closure_eq_closure_preimage continuous_im _).symm

lemma frontier_preimage_re (s : set ℝ) : frontier (re ⁻¹' s) = re ⁻¹' (frontier s) :=
(is_open_map_re.preimage_frontier_eq_frontier_preimage continuous_re _).symm

lemma frontier_preimage_im (s : set ℝ) : frontier (im ⁻¹' s) = im ⁻¹' (frontier s) :=
(is_open_map_im.preimage_frontier_eq_frontier_preimage continuous_im _).symm

@[simp] lemma interior_set_of_re_le (a : ℝ) : interior {z : ℂ | z.re ≤ a} = {z | z.re < a} :=
by simpa only [interior_Iic] using interior_preimage_re (Iic a)

@[simp] lemma interior_set_of_im_le (a : ℝ) : interior {z : ℂ | z.im ≤ a} = {z | z.im < a} :=
by simpa only [interior_Iic] using interior_preimage_im (Iic a)

@[simp] lemma interior_set_of_le_re (a : ℝ) : interior {z : ℂ | a ≤ z.re} = {z | a < z.re} :=
by simpa only [interior_Ici] using interior_preimage_re (Ici a)

@[simp] lemma interior_set_of_le_im (a : ℝ) : interior {z : ℂ | a ≤ z.im} = {z | a < z.im} :=
by simpa only [interior_Ici] using interior_preimage_im (Ici a)

@[simp] lemma closure_set_of_re_lt (a : ℝ) : closure {z : ℂ | z.re < a} = {z | z.re ≤ a} :=
by simpa only [closure_Iio] using closure_preimage_re (Iio a)

@[simp] lemma closure_set_of_im_lt (a : ℝ) : closure {z : ℂ | z.im < a} = {z | z.im ≤ a} :=
by simpa only [closure_Iio] using closure_preimage_im (Iio a)

@[simp] lemma closure_set_of_lt_re (a : ℝ) : closure {z : ℂ | a < z.re} = {z | a ≤ z.re} :=
by simpa only [closure_Ioi] using closure_preimage_re (Ioi a)

@[simp] lemma closure_set_of_lt_im (a : ℝ) : closure {z : ℂ | a < z.im} = {z | a ≤ z.im} :=
by simpa only [closure_Ioi] using closure_preimage_im (Ioi a)

@[simp] lemma frontier_set_of_re_le (a : ℝ) : frontier {z : ℂ | z.re ≤ a} = {z | z.re = a} :=
by simpa only [frontier_Iic] using frontier_preimage_re (Iic a)

@[simp] lemma frontier_set_of_im_le (a : ℝ) : frontier {z : ℂ | z.im ≤ a} = {z | z.im = a} :=
by simpa only [frontier_Iic] using frontier_preimage_im (Iic a)

@[simp] lemma frontier_set_of_le_re (a : ℝ) : frontier {z : ℂ | a ≤ z.re} = {z | z.re = a} :=
by simpa only [frontier_Ici] using frontier_preimage_re (Ici a)

@[simp] lemma frontier_set_of_le_im (a : ℝ) : frontier {z : ℂ | a ≤ z.im} = {z | z.im = a} :=
by simpa only [frontier_Ici] using frontier_preimage_im (Ici a)

@[simp] lemma frontier_set_of_re_lt (a : ℝ) : frontier {z : ℂ | z.re < a} = {z | z.re = a} :=
by simpa only [frontier_Iio] using frontier_preimage_re (Iio a)

@[simp] lemma frontier_set_of_im_lt (a : ℝ) : frontier {z : ℂ | z.im < a} = {z | z.im = a} :=
by simpa only [frontier_Iio] using frontier_preimage_im (Iio a)

@[simp] lemma frontier_set_of_lt_re (a : ℝ) : frontier {z : ℂ | a < z.re} = {z | z.re = a} :=
by simpa only [frontier_Ioi] using frontier_preimage_re (Ioi a)

@[simp] lemma frontier_set_of_lt_im (a : ℝ) : frontier {z : ℂ | a < z.im} = {z | z.im = a} :=
by simpa only [frontier_Ioi] using frontier_preimage_im (Ioi a)

lemma closure_re_prod_im (s t : set ℝ) : closure (s ×ℂ t) = closure s ×ℂ closure t :=
by simpa only [← preimage_eq_preimage equiv_real_prod_clm.symm.to_homeomorph.surjective,
  equiv_real_prod_clm.symm.to_homeomorph.preimage_closure]
  using @closure_prod_eq _ _ _ _ s t

lemma interior_re_prod_im (s t : set ℝ) : interior (s ×ℂ t) = interior s ×ℂ interior t :=
by rw [re_prod_im, re_prod_im, interior_inter, interior_preimage_re, interior_preimage_im]

lemma frontier_re_prod_im (s t : set ℝ) :
  frontier (s ×ℂ t) = (closure s ×ℂ frontier t) ∪ (frontier s ×ℂ closure t) :=
by simpa only [← preimage_eq_preimage equiv_real_prod_clm.symm.to_homeomorph.surjective,
  equiv_real_prod_clm.symm.to_homeomorph.preimage_frontier]
  using frontier_prod_eq s t

lemma frontier_set_of_le_re_and_le_im (a b : ℝ) :
  frontier {z | a ≤ re z ∧ b ≤ im z} = {z | a ≤ re z ∧ im z = b ∨ re z = a ∧ b ≤ im z} :=
by simpa only [closure_Ici, frontier_Ici] using frontier_re_prod_im (Ici a) (Ici b)

lemma frontier_set_of_le_re_and_im_le (a b : ℝ) :
  frontier {z | a ≤ re z ∧ im z ≤ b} = {z | a ≤ re z ∧ im z = b ∨ re z = a ∧ im z ≤ b} :=
by simpa only [closure_Ici, closure_Iic, frontier_Ici, frontier_Iic]
  using frontier_re_prod_im (Ici a) (Iic b)

end complex

open complex metric

variables {s t : set ℝ}

lemma is_open.re_prod_im (hs : is_open s) (ht : is_open t) : is_open (s ×ℂ t) :=
(hs.preimage continuous_re).inter (ht.preimage continuous_im)

lemma is_closed.re_prod_im (hs : is_closed s) (ht : is_closed t) : is_closed (s ×ℂ t) :=
(hs.preimage continuous_re).inter (ht.preimage continuous_im)

lemma metric.bounded.re_prod_im (hs : bounded s) (ht : bounded t) : bounded (s ×ℂ t) :=
antilipschitz_equiv_real_prod.bounded_preimage (hs.prod ht)
