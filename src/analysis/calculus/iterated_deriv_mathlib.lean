/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import analysis.calculus.iterated_deriv

/-!
# Stuff for analysis.calculus.iterated_deriv
-/

noncomputable theory
open_locale classical topology big_operators
open filter asymptotics set


variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]

-- lemma iterated_deriv_within_univ {n : ℕ} {f : 𝕜 → F} {n : ℕ} :
--   iterated_deriv_within n f univ = iterated_deriv n f :=

lemma iterated_fderiv_within_nhds {u : set E} {x : E} {f : E → F} {n : ℕ} (hu : u ∈ 𝓝 x) :
  iterated_fderiv_within 𝕜 n f u x = iterated_fderiv 𝕜 n f x :=
by rw [←iterated_fderiv_within_univ, ←univ_inter u, iterated_fderiv_within_inter hu]

lemma iterated_deriv_within_of_is_open {s : set 𝕜} {f : 𝕜 → F} (n : ℕ) (hs : is_open s) :
  eq_on (iterated_deriv_within n f s) (iterated_deriv n f) s :=
λ x hx, by rw [iterated_deriv_within, iterated_deriv, iterated_fderiv_within_of_is_open _ hs hx]

lemma iterated_deriv_within_nhds {u : set 𝕜} {x : 𝕜} {f : 𝕜 → F} {n : ℕ} (hu : u ∈ 𝓝 x) :
  iterated_deriv_within n f u x = iterated_deriv n f x :=
by rw [iterated_deriv_within, iterated_deriv, iterated_fderiv_within_nhds hu]
