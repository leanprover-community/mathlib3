/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import ring_theory.hahn_series
import ring_theory.localization

/-!
# Laurent Series

## Main Definitions

-/

open_locale big_operators classical
noncomputable theory

abbreviation laurent_series (R : Type*) [has_zero R] := hahn_series ℤ R

def foo : fraction_map (power_series R) (hahn_series ℤ R) :=
