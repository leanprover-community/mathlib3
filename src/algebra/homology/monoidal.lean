import category_theory.monoidal.CommMon_
import algebra.homology.single
import category_theory.limits.shapes.biproducts
import data.finset.nat_antidiagonal
import category_theory.monoidal.functorial
import algebra.category.Module.monoidal
import algebra.category.Module.abelian
import category_theory.monoidal.preadditive

open category_theory
open category_theory.limits

universes v u

noncomputable theory

variables {C : Type u} [category.{0} C] [has_zero_object C] [preadditive C]
  [has_finite_biproducts C] [monoidal_category C] [monoidal_preadditive C]

open_locale big_operators

open category_theory.monoidal_category

def antidiagonal (i : ℕ) := { p : ℕ × ℕ // p.1 + p.2 = i }
instance (i : ℕ) : fintype (antidiagonal i) := sorry

namespace cochain_complex

def tensor_d (X Y : cochain_complex C ℕ) (i j : ℕ) (p : antidiagonal i) (q : antidiagonal j) :
  X.X p.1.1 ⊗ Y.X p.1.2 ⟶ X.X q.1.1 ⊗ Y.X q.1.2 :=
if h : p.1.1 = q.1.1 then
  (-1 : ℤ)^p.1.1 • eq_to_hom (congr_arg X.X h) ⊗ Y.d p.1.2 q.1.2
else if h : p.1.2 = q.1.2 then
  X.d p.1.1 q.1.1 ⊗ eq_to_hom (congr_arg Y.X h)
else
  0

def tensor_obj (X Y : cochain_complex C ℕ) : cochain_complex C ℕ :=
{ X := λ i, ⨁ (λ p : antidiagonal i, X.X p.1.1 ⊗ Y.X p.1.2),
  d := λ i j, biproduct.matrix (tensor_d X Y i j),
  shape' := sorry,
  d_comp_d' := sorry, }

def tensor_hom {X₁ X₂ Y₁ Y₂ : cochain_complex C ℕ} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
  tensor_obj X₁ Y₁ ⟶ tensor_obj X₂ Y₂ :=
{ f := λ i, biproduct.map (λ p, f.f p.1.1 ⊗ g.f p.1.2),
  comm' := sorry, }

def tensor_unit : cochain_complex C ℕ := (cochain_complex.single₀ C).obj (𝟙_ C)

def associator_hom_aux (X Y Z : ℕ → C) (i : ℕ)
  (p q : antidiagonal i) (j : antidiagonal p.1.1) (k : antidiagonal q.1.2) :
    (X j.1.1 ⊗ Y j.1.2) ⊗ Z p.1.2 ⟶ X q.1.1 ⊗ (Y k.1.1 ⊗ Z k.1.2) :=
if h : j.1.1 = q.1.1 ∧ j.1.2 = k.1.1 ∧ p.1.2 = k.1.2 then
  (α_ _ _ _).hom ≫
    (eq_to_hom (congr_arg X h.1) ⊗ eq_to_hom (congr_arg Y h.2.1) ⊗
      eq_to_hom (congr_arg Z h.2.2))
else
  0

def associator_hom (X Y Z : cochain_complex C ℕ) :
  tensor_obj (tensor_obj X Y) Z ⟶ tensor_obj X (tensor_obj Y Z) :=
{ f := λ i, biproduct.matrix (λ p q,
  (right_distributor _ _).hom ≫ biproduct.matrix (associator_hom_aux X.X Y.X Z.X i p q) ≫
    (left_distributor _ _).inv),
  comm' := sorry }

def associator_inv_aux (X Y Z : ℕ → C) (i : ℕ)
  (p q : antidiagonal i) (j : antidiagonal p.1.2) (k : antidiagonal q.1.1) :
    X p.1.1 ⊗ (Y j.1.1 ⊗ Z j.1.2) ⟶ (X k.1.1 ⊗ Y k.1.2) ⊗ Z q.1.2 :=
if h : p.1.1 = k.1.1 ∧ j.1.1 = k.1.2 ∧ j.1.2 = q.1.2 then
  (eq_to_hom (congr_arg X h.1) ⊗ eq_to_hom (congr_arg Y h.2.1) ⊗
      eq_to_hom (congr_arg Z h.2.2)) ≫ (α_ _ _ _).inv
else
  0

def associator_inv (X Y Z : cochain_complex C ℕ) :
  tensor_obj X (tensor_obj Y Z) ⟶ tensor_obj (tensor_obj X Y) Z :=
{ f := λ i, biproduct.matrix (λ p q,
  (left_distributor _ _).hom ≫ biproduct.matrix (associator_inv_aux X.X Y.X Z.X i p q) ≫
    (right_distributor _ _).inv),
  comm' := sorry }

def associator (X Y Z : cochain_complex C ℕ) :
  tensor_obj (tensor_obj X Y) Z ≅ tensor_obj X (tensor_obj Y Z) :=
{ hom := associator_hom X Y Z,
  inv := associator_inv X Y Z,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

def left_unitor_hom (X : cochain_complex C ℕ) :
  tensor_obj tensor_unit X ⟶ X :=
{ f := λ i, biproduct.π _ ⟨⟨0, i⟩, by simp⟩ ≫ (λ_ (X.X i)).hom,
  comm' := sorry, }

def left_unitor_inv (X : cochain_complex C ℕ) :
  X ⟶ tensor_obj tensor_unit X :=
{ f := λ i, (λ_ (X.X i)).inv ≫ biproduct.ι (λ p : antidiagonal i, tensor_unit.X p.1.1 ⊗ X.X p.1.2) ⟨⟨0, i⟩, by simp⟩,
  comm' := sorry, }

def left_unitor (X : cochain_complex C ℕ) :
  tensor_obj tensor_unit X ≅ X :=
{ hom := left_unitor_hom X,
  inv := left_unitor_inv X,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

def right_unitor_hom (X : cochain_complex C ℕ) :
  tensor_obj X tensor_unit ⟶ X :=
{ f := λ i, biproduct.π _ ⟨⟨i, 0⟩, by simp⟩ ≫ (ρ_ (X.X i)).hom,
  comm' := sorry, }

def right_unitor_inv (X : cochain_complex C ℕ) :
  X ⟶ tensor_obj X tensor_unit :=
{ f := λ i, (ρ_ (X.X i)).inv ≫ biproduct.ι (λ p : antidiagonal i, X.X p.1.1 ⊗ tensor_unit.X p.1.2) ⟨⟨i, 0⟩, by simp⟩,
  comm' := sorry, }

def right_unitor (X : cochain_complex C ℕ) :
  tensor_obj X tensor_unit ≅ X :=
{ hom := right_unitor_hom X,
  inv := right_unitor_inv X,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

end cochain_complex

instance : monoidal_category (cochain_complex C ℕ) :=
{ tensor_obj := λ X Y, cochain_complex.tensor_obj X Y,
  tensor_hom := λ X₁ X₂ Y₁ Y₂ f g, cochain_complex.tensor_hom f g,
  tensor_unit := cochain_complex.tensor_unit,
  associator := cochain_complex.associator,
  left_unitor := cochain_complex.left_unitor,
  right_unitor := cochain_complex.right_unitor,
  tensor_id' := sorry,
  tensor_comp' := sorry,
  associator_naturality' := sorry,
  left_unitor_naturality' := sorry,
  right_unitor_naturality' := sorry,
  pentagon' := sorry,
  triangle' := sorry, }

variables [braided_category C]

namespace cochain_complex

def braiding_hom (X Y : cochain_complex C ℕ) : X ⊗ Y ⟶ Y ⊗ X :=
{ f := λ i, biproduct.lift (λ p, biproduct.π (λ p : antidiagonal i, X.X p.1.1 ⊗ Y.X p.1.2) ⟨⟨p.1.2, p.1.1⟩, sorry⟩ ≫ (β_ _ _).hom),
  comm' := sorry, }

def braiding_inv (X Y : cochain_complex C ℕ) : Y ⊗ X ⟶ X ⊗ Y :=
{ f := λ i, biproduct.desc (λ p, (β_ _ _).inv ≫ biproduct.ι (λ p : antidiagonal i, X.X p.1.1 ⊗ Y.X p.1.2) ⟨⟨p.1.2, p.1.1⟩, sorry⟩),
  comm' := sorry, }

def braiding (X Y : cochain_complex C ℕ) : X ⊗ Y ≅ Y ⊗ X :=
{ hom := braiding_hom X Y,
  inv := braiding_inv X Y,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

end cochain_complex

instance : braided_category (cochain_complex C ℕ) :=
{ braiding := cochain_complex.braiding,
  braiding_naturality' := sorry,
  hexagon_forward' := sorry,
  hexagon_reverse' := sorry, }

namespace graded_object

def tensor_obj (X Y : graded_object ℕ C) : graded_object ℕ C :=
λ i, ⨁ (λ p : antidiagonal i, X p.1.1 ⊗ Y p.1.2)

def tensor_hom {X₁ X₂ Y₁ Y₂ : graded_object ℕ C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
  tensor_obj X₁ Y₁ ⟶ tensor_obj X₂ Y₂ :=
-- I can't write this in term mode and have it typecheck... ?
by exact λ i, biproduct.map (λ p, f p.1.1 ⊗ g p.1.2)

local attribute [instance] has_zero_object.has_zero

def tensor_unit : graded_object ℕ C :=
λ i, match i with
| 0 := 𝟙_ C
| n+1 := 0
end

def associator_hom (X Y Z : graded_object ℕ C) :
  tensor_obj (tensor_obj X Y) Z ⟶ tensor_obj X (tensor_obj Y Z) :=
by exact λ i, biproduct.matrix (λ p q,
  (right_distributor _ _).hom ≫ biproduct.matrix (cochain_complex.associator_hom_aux X Y Z i p q) ≫
    (left_distributor _ _).inv)

def associator_inv (X Y Z : graded_object ℕ C) :
  tensor_obj X (tensor_obj Y Z) ⟶ tensor_obj (tensor_obj X Y) Z :=
by exact λ i, biproduct.matrix (λ p q,
  (left_distributor _ _).hom ≫ biproduct.matrix (cochain_complex.associator_inv_aux X Y Z i p q) ≫
    (right_distributor _ _).inv)

def associator (X Y Z : graded_object ℕ C) :
  tensor_obj (tensor_obj X Y) Z ≅ tensor_obj X (tensor_obj Y Z) :=
{ hom := associator_hom X Y Z,
  inv := associator_inv X Y Z,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

def left_unitor (X : graded_object ℕ C) :
  tensor_obj tensor_unit X ≅ X :=
{ hom := λ i, biproduct.π _ ⟨⟨0, i⟩, by simp⟩ ≫ (λ_ (X i)).hom,
  inv := λ i, (λ_ (X i)).inv ≫ biproduct.ι (λ p : antidiagonal i, tensor_unit p.1.1 ⊗ X p.1.2) ⟨⟨0, i⟩, by simp⟩,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

def right_unitor (X : graded_object ℕ C) :
  tensor_obj X tensor_unit ≅ X :=
{ hom := λ i, biproduct.π _ ⟨⟨i, 0⟩, by simp⟩ ≫ (ρ_ (X i)).hom,
  inv := λ i, (ρ_ (X i)).inv ≫ biproduct.ι (λ p : antidiagonal i, X p.1.1 ⊗ tensor_unit p.1.2) ⟨⟨i, 0⟩, by simp⟩,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

end graded_object

instance : monoidal_category (graded_object ℕ C) :=
{ tensor_obj := λ X Y, graded_object.tensor_obj X Y,
  tensor_hom := λ X₁ X₂ Y₁ Y₂ f g, graded_object.tensor_hom f g,
  tensor_unit := graded_object.tensor_unit,
  associator := graded_object.associator,
  left_unitor := graded_object.left_unitor,
  right_unitor := graded_object.right_unitor,
  tensor_id' := sorry,
  tensor_comp' := sorry,
  associator_naturality' := sorry,
  left_unitor_naturality' := sorry,
  right_unitor_naturality' := sorry,
  pentagon' := sorry,
  triangle' := sorry, }

namespace graded_object

def braiding_hom (X Y : graded_object ℕ C) : X ⊗ Y ⟶ Y ⊗ X :=
λ i, biproduct.lift (λ p, biproduct.π (λ p : antidiagonal i, X p.1.1 ⊗ Y p.1.2) ⟨⟨p.1.2, p.1.1⟩, sorry⟩ ≫ (β_ _ _).hom)

def braiding_inv (X Y : graded_object ℕ C) : Y ⊗ X ⟶ X ⊗ Y :=
λ i, biproduct.desc (λ p, (β_ _ _).inv ≫ biproduct.ι (λ p : antidiagonal i, X p.1.1 ⊗ Y p.1.2) ⟨⟨p.1.2, p.1.1⟩, sorry⟩)

def braiding (X Y : graded_object ℕ C) : X ⊗ Y ≅ Y ⊗ X :=
{ hom := braiding_hom X Y,
  inv := braiding_inv X Y,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

end graded_object

instance : braided_category (graded_object ℕ C) :=
{ braiding := graded_object.braiding,
  braiding_naturality' := sorry,
  hexagon_forward' := sorry,
  hexagon_reverse' := sorry, }

/-!
At this point we specialise to `C = Module R`,
and prove that the homology functor is lax monoidal.
I'm not certain how far this could be generalised.
-/

variables (R : Type) [comm_ring R]

def lax_monoidal_ε :
  𝟙_ (graded_object ℕ (Module.{0} R)) ⟶
    (graded_homology_functor (Module.{0} R) (complex_shape.up ℕ)).obj (𝟙_ _) :=
by exact λ i, match i with
| 0 := sorry
| n+1 := 0
end

def lax_monoidal_μ (X Y : cochain_complex (Module.{0} R) ℕ) :
  (graded_homology_functor (Module.{0} R) (complex_shape.up ℕ)).obj X ⊗
    (graded_homology_functor (Module.{0} R) (complex_shape.up ℕ)).obj Y ⟶
  (graded_homology_functor (Module.{0} R) (complex_shape.up ℕ)).obj (X ⊗ Y) :=
by exact λ i, biproduct.desc (λ ⟨⟨j,k⟩,h⟩,
begin dsimp, sorry end)

instance : lax_monoidal (graded_homology_functor (Module.{0} R) (complex_shape.up ℕ)).obj :=
{ ε := lax_monoidal_ε R,
  μ := lax_monoidal_μ R,
  μ_natural' := sorry,
  associativity' := sorry,
  left_unitality' := sorry,
  right_unitality' := sorry, }

def graded_homology_lax_monoidal_functor : lax_monoidal_functor (cochain_complex (Module.{0} R) ℕ) (graded_object ℕ (Module.{0} R)) :=
lax_monoidal_functor.of (graded_homology_functor (Module.{0} R) (complex_shape.up ℕ)).obj

def graded_homology_lax_braided_functor : lax_braided_functor (cochain_complex (Module.{0} R) ℕ) (graded_object ℕ (Module.{0} R)) :=
{ braided' := sorry,
  ..graded_homology_lax_monoidal_functor R }

def CDGA_challenge : CommMon_ (cochain_complex (Module.{0} R) ℕ) ⥤ CommMon_ (graded_object ℕ (Module.{0} R)) :=
(graded_homology_lax_braided_functor R).map_CommMon
