/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.int.basic
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

variables (V : Type u) [category.{v} V]
variables [has_zero_morphisms V]

section

/--
A `homological_complex V b` for `b : β` is a (co)chain complex graded by `β`,
with differential in grading `b`.

(We use the somewhat cumbersome `homological_complex` to avoid the name conflict with `ℂ`.)
-/
abbreviation homological_complex {β : Type} [add_comm_group β] (b : β) : Type (max v u) :=
differential_object (graded_object_with_shift b V)

/--
A chain complex in `V` is "just" a differential `ℤ`-graded object in `V`,
with differential graded `-1`.
-/
abbreviation chain_complex : Type (max v u) :=
homological_complex V (-1 : ℤ)

/--
A cochain complex in `V` is "just" a differential `ℤ`-graded object in `V`,
with differential graded `+1`.
-/
abbreviation cochain_complex : Type (max v u) :=
homological_complex V (1 : ℤ)

-- The chain groups of a chain complex `C` are accessed as `C.X i`,
-- and the differentials as `C.d i : C.X i ⟶ C.X (i-1)`.
example (C : chain_complex V) : C.X 5 ⟶ C.X 4 := C.d 5

end

namespace homological_complex

variables {V}
variables {β : Type} [add_comm_group β] {b : β}

@[simp]
lemma d_squared (C : homological_complex V b) (i : β) :
  C.d i ≫ C.d (i+b) = 0 :=
congr_fun (C.d_squared) i

/--
A convenience lemma for morphisms of cochain complexes,
picking out one component of the commutation relation.
-/
-- I haven't been able to get this to work with projection notation: `f.comm_at i`
@[simp]
lemma comm_at {C D : homological_complex V b} (f : C ⟶ D) (i : β) :
    C.d i ≫ f.f (i+b) = f.f i ≫ D.d i :=
congr_fun f.comm i

@[simp]
lemma comm {C D : homological_complex V b} (f : C ⟶ D) : C.d ≫ f.f⟦1⟧' = f.f ≫ D.d :=
differential_object.hom.comm _

variables (V)

/-- The forgetful functor from cochain complexes to graded objects, forgetting the differential. -/
abbreviation forget : (homological_complex V b) ⥤ (graded_object β V) :=
differential_object.forget _

section
local attribute [instance] has_zero_object.has_zero

instance : inhabited (homological_complex (discrete punit) b) := ⟨0⟩
end

end homological_complex

open homological_complex

-- The components of a cochain map `f : C ⟶ D` are accessed as `f.f i`.
example {C D : cochain_complex V} (f : C ⟶ D) : C.X 5 ⟶ D.X 5 := f.f 5
example {C D : cochain_complex V} (f : C ⟶ D) : C.d ≫ f.f⟦1⟧' = f.f ≫ D.d := by simp
example {C D : cochain_complex V} (f : C ⟶ D) : C.d 5 ≫ f.f 6 = f.f 5 ≫ D.d 5 := comm_at f 5

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
