/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.definitions.basic
/-!
# General Theorems for Continued Fractions
-/

namespace generalized_continued_fraction
open generalized_continued_fraction as gcf
variables {α : Type*}

/-- Two gcfs `g` and `g'` are equal if and only if their components are equal. -/
protected lemma ext_iff {g g' : gcf α} : g = g' ↔ g.h = g'.h ∧ g.s = g'.s :=
by { cases g, cases g', simp }

@[extensionality]
protected lemma ext {g g' : gcf α} (hyp : g.h = g'.h ∧ g.s = g'.s) : g = g' :=
generalized_continued_fraction.ext_iff.elim_right hyp

end generalized_continued_fraction
