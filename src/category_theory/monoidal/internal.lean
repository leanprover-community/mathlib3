import category_theory.monoidal.category
import algebra.category.CommRing.basic

/-!
# The category of monoids in a monoidal category, and modules over an internal monoid.
-/

universes v u

open category_theory

variables (C : Type u) [category.{v} C] [monoidal_category.{v} C]

structure Mon_ :=
(X : C)
(one : 𝟙_ C ⟶ X)
(mul : X ⊗ X ⟶ X)
(one_mul' : (one ⊗ 𝟙 X) ≫ mul = (λ_ X).hom . obviously)
(mul_one' : (𝟙 X ⊗ one) ≫ mul = (ρ_ X).hom . obviously)
-- Obviously there is some flexibility stating this axiom.
-- This one has left- and right-hand sides matching the statement of `monoid.mul_assoc`,
-- and choosing to place the associator on the right-hand side.
-- The heuristic is that unitors and associators "don't have much weight".
(mul_assoc' : (mul ⊗ 𝟙 X) ≫ mul = (α_ X X X).hom ≫ (𝟙 X ⊗ mul) ≫ mul . obviously)

restate_axiom Mon_.one_mul'
restate_axiom Mon_.mul_one'
restate_axiom Mon_.mul_assoc'
attribute [simp, reassoc] Mon_.one_mul Mon_.mul_one Mon_.mul_assoc

namespace Mon_

variables {C}

@[ext]
structure hom (M N : Mon_ C) :=
(hom : M.X ⟶ N.X)
(one_hom' : M.one ≫ hom = N.one . obviously)
(mul_hom' : M.mul ≫ hom = (hom ⊗ hom) ≫ N.mul . obviously)

restate_axiom hom.one_hom'
restate_axiom hom.mul_hom'
attribute [simp, reassoc] hom.one_hom hom.mul_hom

@[simps]
def id (M : Mon_ C) : hom M M :=
{ hom := 𝟙 M.X, }

@[simps]
def comp {M N O : Mon_ C} (f : hom M N) (g : hom N O) : hom M O :=
{ hom := f.hom ≫ g.hom, }

instance : category (Mon_ C) :=
{ hom := λ M N, hom M N,
  id := id,
  comp := λ M N O f g, comp f g, }

/-- The forgetful functor from monoid objects to the ambient category. -/
def forget : Mon_ C ⥤ C :=
{ obj := λ A, A.X,
  map := λ A B f, f.hom, }

end Mon_

-- TODO lax monoidal functors `C ⥤ D` induce functors `Mon_ C ⥤ Mon_ D`.

variables {C}

structure Mod (A : Mon_ C) :=
(X : C)
(act : A.X ⊗ X ⟶ X)
(one_act' : (A.one ⊗ 𝟙 X) ≫ act = (λ_ X).hom . obviously)
(assoc' : (𝟙 A.X ⊗ act) ≫ act = (α_ A.X A.X X).inv ≫ (A.mul ⊗ 𝟙 X) ≫ act . obviously)

restate_axiom Mod.one_act'
restate_axiom Mod.assoc'
attribute [simp, reassoc] Mod.one_act Mod.assoc

namespace Mod

variables {A : Mon_ C} (M : Mod A)

@[ext]
structure hom (M N : Mod A) :=
(hom : M.X ⟶ N.X)
(act_hom' : M.act ≫ hom = (𝟙 A.X ⊗ hom) ≫ N.act . obviously)

restate_axiom hom.act_hom'
attribute [simp, reassoc] hom.act_hom

@[simps]
def id (M : Mod A) : hom M M :=
{ hom := 𝟙 M.X, }

@[simps]
def comp {M N O : Mod A} (f : hom M N) (g : hom N O) : hom M O :=
{ hom := f.hom ≫ g.hom, }

instance : category (Mod A) :=
{ hom := λ M N, hom M N,
  id := id,
  comp := λ M N O f g, comp f g, }

open category_theory.monoidal_category

@[simps]
def comap {A B : Mon_ C} (f : A ⟶ B) : Mod B ⥤ Mod A :=
{ obj := λ M,
  { X := M.X,
    act := (f.hom ⊗ 𝟙 M.X) ≫ M.act,
    one_act' :=
    begin
      slice_lhs 1 2 { rw [←comp_tensor_id], simp, },
      simp,
    end,
    assoc' :=
    begin
      -- oh, for homotopy.io in a widget!
      slice_lhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
      rw id_tensor_comp,
      slice_lhs 3 4 { rw Mod.assoc, },
      slice_lhs 2 3 { rw associator_inv_naturality, },
      slice_lhs 1 2 { rw [←tensor_id, associator_inv_naturality], },
      slice_lhs 2 3 { rw [←comp_tensor_id, tensor_id_comp_id_tensor], },
      slice_lhs 2 3 { rw [←comp_tensor_id, ←f.mul_hom], },
      rw [comp_tensor_id, category.assoc],
    end, },
  map := λ M N g,
  { hom := g.hom,
    act_hom' :=
    begin
      dsimp,
      slice_rhs 1 2 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
      slice_rhs 2 3 { rw ←g.act_hom, },
      rw category.assoc,
    end }, }

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.

end Mod

/-!
Projects:
* Check that `Mon_ Type ≌ Mon`.
* Check that `Mon_ Mon ≌ CommMon`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `Mon` first, available in #3463)
* Check that `Mon_ AddCommGroup ≌ Ring`.
  (You'll have to hook up the monoidal structure on `AddCommGroup`.
  Currently we have the monoidal structure on `Module R`; perhaps one could specialize to `R = ℤ`
  and transport the monoidal structure across an equivalence? This sounds like some work!)
* Check that `Mon_ (Module R) ≌ Algebra R`.
* Show that if `C` is braided (see #3550) then `Mon_ C` is naturally monoidal.
* Can you transport this monoidal structure to `Ring` or `Algebra R`?
  How does it compare to the "native" one?
-/
