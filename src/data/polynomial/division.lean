
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.semiring_division


/-!
# Theory of univariate polynomials


-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

-- local attribute [instance, priority 10] is_semiring_hom.comp is_ring_hom.comp

open finsupp finset add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u v w z
variables {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}





end polynomial
