/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebra.category.Ring.basic
import ring_theory.localization.away

/-!
# Ring-theoretic results in terms of categorical languages
-/

open category_theory

instance localization_unit_is_iso (R : CommRing) :
  is_iso (CommRing.of_hom $ algebra_map R (localization.away (1 : R))) :=
is_iso.of_iso (is_localization.at_one R (localization.away (1 : R))).to_ring_equiv.to_CommRing_iso

instance localization_unit_is_iso' (R : CommRing) :
  @is_iso CommRing _ R _ (CommRing.of_hom $ algebra_map R (localization.away (1 : R))) :=
by { cases R, exact localization_unit_is_iso _ }
