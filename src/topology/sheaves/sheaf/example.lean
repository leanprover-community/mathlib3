import algebra.category.CommRing.limits
import topology.sheaves.sheaf.concrete_category

open Top
open category_theory

universes u

instance : reflects_isomorphisms (forget CommRing.{u}) :=
{ reflects := λ X Y f _, by exactI
  { ..(ring_equiv.to_CommRing_iso { ..f, ..(as_iso.{u} ((forget CommRing).map f)).CommRing_iso_to_ring_equiv })} }

example (X : Top) (F : presheaf CommRing X) (h : sheaf_condition (F ⋙ (forget CommRing))) :
  sheaf_condition F :=
(sheaf_condition_equiv_sheaf_condition_forget F).symm h
