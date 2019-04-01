import category_theory.instances.monoids
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.binary_products
import category_theory.limits.types

universes u v

open category_theory
open category_theory.limits
open category_theory.instances

class filtered (J : Sort u) [category.{v+1} J] extends inhabited J :=
(cofan : Π (X Y : J), cofan (two.map X Y))
(cofork : Π {X Y : J} (f g : X ⟶ Y), cofork f g)

variables {J : Type u} [small_category J] [filtered J]

def colimit_type (F : J ⥤ Mon.{u}) := colimit (F ⋙ forget)

instance monoid_instance (F : J ⥤ Mon.{u}) (X : J) : monoid ((F ⋙ forget).obj X) := (F.obj X).str

def colimit_mul (F : J ⥤ Mon.{u}) : colimit_type F → colimit_type F → colimit_type F :=
begin
  -- We need to build something in a quotient
  fapply @quot.lift _ _ (colimit_type F → colimit_type F),
  intro x,
  fapply quot.lift,
  intro y,
  apply quot.mk,
  { -- We take some later point in the filtered category J.
    have c := filtered.cofan x.1 y.1,
    use c.X,
    have f_x := F.map (c.ι.app two.left),
    have f_y := F.map (c.ι.app two.right),
    dsimp at f_x f_y,
    exact f_x.val x.2 * f_y.val y.2 },
  { intros,
    dsimp,
    apply quot.sound, -- no, that's not quite it; we need to go higher up
    fsplit,
    dsimp,
    sorry, sorry },
  sorry
end

instance colimit_comm_ring (F : J ⥤ Mon.{u}) : monoid (colimit_type F) :=
{ one := quot.mk _ ⟨default J, (1 : (F.obj (default J)).α)⟩,
  mul := colimit_mul F,
  one_mul := sorry,
  mul_one := sorry,
  mul_assoc := sorry }


def colimit (F : J ⥤ Mon.{u}) : cocone F :=
{ X := ⟨colimit_type F, by apply_instance⟩,
  ι := sorry }

local attribute [elab_with_expected_type] quot.lift

def colimit_is_colimit (F : J ⥤ Mon.{u}) : is_colimit (colimit F) :=
{ desc := sorry,
  fac' := sorry,
  uniq' := sorry }

-- instance : has_filtered_colimits.{u} (Mon.{u}) :=
-- λ J 𝒥 F, by exactI { cocone := colimit F, is_colimit := colimit_is_colimit F }
