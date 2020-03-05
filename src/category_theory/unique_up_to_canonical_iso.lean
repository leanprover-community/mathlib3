import category_theory.eq_to_hom

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

open category_theory

namespace category_theory

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

/--
A predicate `P` on a category `C` is 'unique up to canonical isomorphism' if all elements are coherently isomorphic.

Typical examples might be `is_limit` on the category `cone F`, or `is_binary_product X Y`.
-/
structure unique_up_to_canonical_iso (P : C → Sort*) :=
(iso_ext : Π {X Y : C} (x : P X) (y : P Y), X ≅ Y)
(refl' : Π {X : C} (x : P X), iso_ext x x = iso.refl X . obviously)
(trans' : Π {X Y Z : C} (x : P X) (y : P Y) (z : P Z), iso_ext x y ≪≫ iso_ext y z = iso_ext x z . obviously)

restate_axiom unique_up_to_canonical_iso.refl'
restate_axiom unique_up_to_canonical_iso.trans'
attribute [simp] unique_up_to_canonical_iso.refl unique_up_to_canonical_iso.trans

namespace unique_up_to_canonical_iso

variables {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒟

/--
A construction to transport uniqueness up to canonical isomorphism.

As an example, we can use this to show that `is_binary_product X Y` is
unique up to canonical isomorphism, starting from the fact that `is_limit`
is (on the category `cone (pair X Y)`). In this instance we would have
`F = cones.forget`.
-/
def transport {P : C → Sort*} {Q : D → Sort*} (c : unique_up_to_canonical_iso.{v₁} P)
  (F : C ⥤ D)
  (t : Π {d : D} (y : Q d), C)
  (e : Π {d : D} (y : Q d), P (t y))
  (r : ∀ {d} (y : Q d), F.obj (t y) = d) :
  unique_up_to_canonical_iso.{v₂} Q :=
{ iso_ext := λ X Y x y, (eq_to_iso (r x)).symm ≪≫ F.map_iso (c.iso_ext (e x) (e y)) ≪≫ (eq_to_iso (r y)),
  refl' := λ X x, by simp,
  trans' := λ X Y Z x y z,
  begin
    simp only [iso.self_symm_id_assoc, iso.trans_assoc],
    rw [←functor.map_iso_trans_assoc, unique_up_to_canonical_iso.trans],
  end }

end unique_up_to_canonical_iso
end category_theory
