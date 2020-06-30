/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.graded_object
import category_theory.differential_object

/-!
# Chain complexes

We define a chain complex in `V` as a differential `ℤ`-graded object in `V`.

This is fancy language for the obvious definition,
and it seems we can use it straightforwardly:

```
example (C : chain_complex V) : C.X 5 ⟶ C.X 6 := C.d 5
```

We define the forgetful functor to `ℤ`-graded objects, and show that
`chain_complex V` is concrete when `V` is, and `V` has coproducts.
-/

universes v u

open category_theory
open category_theory.limits

section
variables (V : Type u) [𝒱 : category.{v} V]
include 𝒱

variables [has_zero_morphisms.{v} V]

/--
A chain complex in `V` is "just" a differential `ℤ`-graded object in `V`,
with differential graded `-1`.
-/
abbreviation chain_complex : Type (max v u) :=
differential_object.{v} (graded_object_with_shift (-1 : ℤ) V)

/--
A cochain complex in `V` is "just" a differential `ℤ`-graded object in `V`,
with differential graded `+1`.
-/
abbreviation cochain_complex : Type (max v u) :=
differential_object.{v} (graded_object_with_shift (1 : ℤ) V)

-- The chain groups of a chain complex `C` are accessed as `C.X i`,
-- and the differentials as `C.d i : C.X i ⟶ C.X (i-1)`.
example (C : chain_complex V) : C.X 5 ⟶ C.X 4 := C.d 5

end

namespace cochain_complex
variables {V : Type u} [𝒱 : category.{v} V]
include 𝒱

variables [has_zero_morphisms.{v} V]

@[simp]
lemma d_squared (C : cochain_complex.{v} V) (i : ℤ) :
  C.d i ≫ C.d (i+1) = 0 :=
congr_fun (C.d_squared) i

/--
A convenience lemma for morphisms of cochain complexes,
picking out one component of the commutation relation.
-/
-- I haven't been able to get this to work with projection notation: `f.comm_at i`
@[simp]
lemma comm_at {C D : cochain_complex V} (f : C ⟶ D) (i : ℤ) :
    C.d i ≫ f.f (i+1) = f.f i ≫ D.d i :=
congr_fun f.comm i

@[simp]
lemma comm {C D : cochain_complex V} (f : C ⟶ D) : C.d ≫ f.f⟦1⟧' = f.f ≫ D.d := differential_object.hom.comm _

-- The components of a cochain map `f : C ⟶ D` are accessed as `f.f i`.
example {C D : cochain_complex V} (f : C ⟶ D) : C.X 5 ⟶ D.X 5 := f.f 5
example {C D : cochain_complex V} (f : C ⟶ D) : C.d ≫ f.f⟦1⟧' = f.f ≫ D.d := by simp
example {C D : cochain_complex V} (f : C ⟶ D) : C.d 5 ≫ f.f 6 = f.f 5 ≫ D.d 5 := comm_at f 5

variables (V)

/-- The forgetful functor from cochain complexes to graded objects, forgetting the differential. -/
abbreviation forget : (cochain_complex V) ⥤ (graded_object ℤ V) :=
differential_object.forget _

section
omit 𝒱
local attribute [instance] has_zero_object.has_zero

instance : inhabited (cochain_complex.{v} (discrete punit.{v+1})) := ⟨0⟩
end

end cochain_complex

namespace chain_complex
variables {V : Type u} [𝒱 : category.{v} V]
include 𝒱

variables [has_zero_morphisms.{v} V]

@[simp]
lemma d_squared (C : chain_complex.{v} V) (i : ℤ) :
  C.d i ≫ C.d (i-1) = 0 :=
congr_fun (C.d_squared) i

/--
A convenience lemma for morphisms of chain complexes,
picking out one component of the commutation relation.
-/
@[simp]
lemma comm_at {C D : chain_complex V} (f : C ⟶ D) (i : ℤ) :
    C.d i ≫ f.f (i-1) = f.f i ≫ D.d i :=
congr_fun f.comm i

@[simp]
lemma comm {C D : chain_complex V} (f : C ⟶ D) : C.d ≫ f.f⟦1⟧' = f.f ≫ D.d := differential_object.hom.comm _

variables (V)

/-- The forgetful functor from chain complexes to graded objects, forgetting the differential. -/
abbreviation forget : (chain_complex V) ⥤ (graded_object ℤ V) :=
differential_object.forget _

section
omit 𝒱
local attribute [instance] has_zero_object.has_zero

instance : inhabited (chain_complex.{v} (discrete punit.{v+1})) := ⟨0⟩
end

end chain_complex

-- TODO when V is enriched in W, what do we need to ensure
-- `chain_complex V` is also enriched in W?

-- TODO `chain_complex V` is a module category for `V` when `V` is monoidal

-- TODO When V is enriched in AddCommGroup, and has coproducts,
-- we can collapse a double complex to obtain a complex.
-- If the double complex is supported in a quadrant, we only need finite coproducts.

-- TODO when V is monoidal, enriched in `AddCommGroup`,
-- and has coproducts then
-- `chain_complex V` is monoidal too.
-- If the complexes are bounded below we only need finite coproducts.
