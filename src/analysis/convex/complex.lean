/-
Copyright (c) 2019 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Yaël Dillies
-/
import analysis.convex.basic
import data.complex.module

/-!
# Convexity of half spaces in ℂ

The open and closed half-spaces in ℂ given by an inequality on either the real or imaginary part
are all convex over ℝ.
-/

lemma convex_halfspace_re_lt (r : ℝ) : convex ℝ {c : ℂ | c.re < r} :=
convex_halfspace_lt (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_le (r : ℝ) : convex ℝ {c : ℂ | c.re ≤ r} :=
convex_halfspace_le (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_gt (r : ℝ) : convex ℝ {c : ℂ | r < c.re } :=
convex_halfspace_gt (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_ge (r : ℝ) : convex ℝ {c : ℂ | r ≤ c.re} :=
convex_halfspace_ge (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_im_lt (r : ℝ) : convex ℝ {c : ℂ | c.im < r} :=
convex_halfspace_lt (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_le (r : ℝ) : convex ℝ {c : ℂ | c.im ≤ r} :=
convex_halfspace_le (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_gt (r : ℝ) : convex ℝ {c : ℂ | r < c.im} :=
convex_halfspace_gt (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_ge (r : ℝ) : convex ℝ {c : ℂ | r ≤ c.im} :=
convex_halfspace_ge (is_linear_map.mk complex.add_im complex.smul_im) _
