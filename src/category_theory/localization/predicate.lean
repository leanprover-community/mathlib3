/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.localization.construction

/-!

# Predicate for localized categories

In this file, a predicate `L.is_localization W` is introduced for a functor `L : C ⥤ D`
and `W : morphism_property C`. It expresses that `L` identifies `D` with the localized
category of `C` with respect to `W` (up to equivalence).

-/

namespace category_theory

variables {C D : Type*} [category C] [category D]
variables (L : C ⥤ D) (W : morphism_property C)

namespace functor

/-- The predicate expressing that, up to equivalence, a functor `L : C ⥤ D`
identifies the category `D` with the localized category of `C` with respect
to `W : morphism_property C`. -/
class is_localization : Prop :=
(inverts : W.is_inverted_by L)
(nonempty_is_equivalence : nonempty (is_equivalence (localization.construction.lift L inverts)))

instance Q_is_localization : W.Q.is_localization W :=
{ inverts := W.Q_inverts,
  nonempty_is_equivalence := begin
    suffices : localization.construction.lift W.Q W.Q_inverts = 𝟭 _,
    { apply nonempty.intro, rw this, apply_instance, },
    apply localization.construction.uniq,
    simpa only [localization.construction.fac],
  end, }

end functor

end category_theory
