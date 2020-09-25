/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.int.basic
import category_theory.graded_object
import category_theory.differential_object
import data.nat.enat

/-!
# Chain complexes

We define a chain complex in `V` as a differential `ℤ`-graded object in `V`.

This is fancy language for the obvious definition,
and it seems we can use it straightforwardly:

```
example (C : chain_complex V) : C.X 5 ⟶ C.X 6 := C.d 5
```

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

namespace homological_complex
variables {V} [has_zero_object V] {b : ℤ}

local attribute [instance] has_zero_object.has_zero

/-- Construct a chain complex without the scary signature. -/
def chain_complex.mk (X : Π i : ℤ, V) (d : Π i, X i ⟶ X (i - 1)) (hd : ∀ i, d i ≫ d (i - 1) = 0) :
  chain_complex V :=
{ X := X, d := d, d_squared' := funext hd }

/-- Bounded below -/
def bounded_below_by (C : homological_complex V b) (n : ℤ) : Prop := ∀ m < n, nonempty (C.X m ≅ 0)

/-- Bounded above -/
def bounded_above_by (C : homological_complex V b) (n : ℤ) : Prop := ∀ m > n, nonempty (C.X m ≅ 0)

open_locale classical
noncomputable theory

/-- The length of a homological complex is the index of the highest-index nontrivial entry in the
    upper half of the chain complex.  -/
def length (C : homological_complex V b) : with_top ℕ :=
if h : ∃ n : ℕ, bounded_above_by C n then nat.find h else ⊤

@[simps]
def single (n : ℤ) (M : V) : chain_complex V :=
{ X := λ i, if i = n then M else 0,
  d := λ i, 0,
  d_squared' := funext $ λ i, by simp }

def single_at_n (n : ℤ) (M : V) : (single n M).X n ≅ M :=
eq_to_iso $ by simp

def single_not_at_n (n : ℤ) (M : V) (i : ℤ) (h : i ≠ n) : (single n M).X i ≅ 0 :=
eq_to_iso $ by simp [h]

@[simp]
def graded.glue (n : ℤ) (L R : graded_object ℤ V) : graded_object ℤ V :=
λ i, if i ≥ n then L i else R i

def graded.glue_iso_left (n : ℤ) (L R : graded_object ℤ V) (i : ℤ) (h : n ≤ i) :
  graded.glue n L R i ≅ L i :=
eq_to_iso $ by simp [h]

def graded.glue_iso_right (n : ℤ) (L R : graded_object ℤ V) (i : ℤ) (h : i < n) :
  graded.glue n L R i ≅ R i :=
eq_to_iso $ by simp [not_le.2 h]

def glue (n : ℤ) (L R : chain_complex V) (d : L.X n ⟶ R.X (n - 1)) : chain_complex V :=
{ X := graded.glue n L.X R.X,
  d := λ i,
    if h : i = n then (graded.glue_iso_left n L.X R.X i (by rw h)).hom ≫ eq_to_hom (by rw h) ≫
      d ≫ eq_to_hom (by rw h) ≫
      (graded.glue_iso_right n L.X R.X (i - 1) (by { rw [h], exact sub_one_lt _ })).inv else _,
  d_squared' := _,
}

end homological_complex
