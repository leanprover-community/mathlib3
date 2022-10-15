import algebra.category.RingModPair.basic
import algebra.category.Ring.colimits
import algebra.category.Group.colimits

namespace CommRingModPair

universe v

open category_theory category_theory.limits

variables {J : Type v} [small_category J] (F : J ⥤ CommRingModPair.{v v})

local notation `FCR` := F ⋙ CommRingModPair.forget_to_CommRing

local notation `FAb` := F ⋙ CommRingModPair.forget_to_Ab


instance : has_colimits CommRingModPair.{v v} :=
{ has_colimits_of_shape := λ J iJ,
  { has_colimit := λ F, { exists_colimit := nonempty.intro
  _ } } }

end CommRingModPair
