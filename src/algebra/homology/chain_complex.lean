import category_theory.graded_object
import category_theory.differential_object

universes v u

open category_theory
open category_theory.limits

section
variables (V : Type u) [𝒱 : category.{v} V]
include 𝒱

variables [has_zero_morphisms.{v} V]

/--
A chain complex in `V` is "just" a differential `ℤ`-graded object in `V`.
-/
-- Actually, because I chose the "shift" to correspond to the +1 direction,
-- this is what would usually be called a cochain complex.
-- We should definitely bikeshed this. :-)
@[nolint has_inhabited_instance]
def chain_complex : Type (max v u) :=
differential_object.{v} (graded_object ℤ V)

-- The chain groups of a chain complex `C` are accessed as `C.X i`,
-- and the differentials as `C.d i : C.X i ⟶ C.X (i+1)`.
example (C : chain_complex V) : C.X 5 ⟶ C.X 6 := C.d 5

variables {V}
/--
A convenience lemma for morphisms of differential graded objects,
picking out one component of the commutation relation.
-/
-- Could this be a simp lemma? Which way?
lemma category_theory.differential_object.hom.comm_at {X Y : differential_object.{v} (graded_object ℤ V)}
  (f : X ⟶ Y) (i : ℤ) : f.f i ≫ Y.d i = X.d i ≫ f.f (i+1) := congr_fun f.comm i
end

namespace chain_complex
variables (V : Type u) [𝒱 : category.{v} V]
include 𝒱

variables [has_zero_morphisms.{v} V]

@[simp]
lemma chain_complex.d_squared (C : chain_complex.{v} V) (i : ℤ) :
  C.d i ≫ C.d (i+1) = 0 :=
congr_fun (C.d_squared) i

instance category_of_chain_complexes : category.{v} (chain_complex V) :=
by { dsimp [chain_complex], apply_instance }.

-- The components of a chain map `f : C ⟶ D` are accessed as `f.f i`.
example {C D : chain_complex V} (f : C ⟶ D) : C.X 5 ⟶ D.X 5 := f.f 5
example {C D : chain_complex V} (f : C ⟶ D) : f.f ≫ D.d = C.d ≫ f.f[[1]] := f.comm
example {C D : chain_complex V} (f : C ⟶ D) : f.f 5 ≫ D.d 5 = C.d 5 ≫ f.f 6 := congr_fun f.comm 5

/-- The forgetful functor from chain complexes to graded objects, forgetting the differential. -/
def forget : (chain_complex V) ⥤ (graded_object ℤ V) :=
differential_object.forget _

instance forget_faithful : faithful (forget V) :=
differential_object.forget_faithful _

instance has_zero_morphisms : has_zero_morphisms.{v} (chain_complex V) :=
by { dsimp [chain_complex], apply_instance }.

end chain_complex

namespace chain_complex
variables (V : Type u) [𝒱 : category.{v} V]
include 𝒱

variables [has_zero_object.{v} V]

private def has_zero_morphisms_V : has_zero_morphisms.{v} V := has_zero_object.zero_morphisms_of_zero_object
local attribute [instance] has_zero_morphisms_V

instance has_zero_object : has_zero_object.{v} (chain_complex V) :=
begin
  dsimp [chain_complex],
  -- FIXME this should just be `apply_instance`, but a `has_zero_morphisms` instance has gone wrong.
  -- We fix it below, knowing that `subsingleton (has_zero_morphisms C)`.
  convert differential_object.has_zero_object.{v} (graded_object ℤ V),
  dsimp [chain_complex.category_of_chain_complexes],
  congr,
  apply subsingleton.elim,
end

end chain_complex

namespace chain_complex
variables
  {V : Type (u+1)} [𝒱 : concrete_category V] [has_zero_morphisms.{u} V] [has_coproducts.{u} V]
include 𝒱

instance : concrete_category (chain_complex.{u} V) :=
differential_object.concrete_category_of_differential_objects (graded_object ℤ V)

instance : has_forget₂ (chain_complex.{u} V) (graded_object ℤ V) :=
by { dsimp [chain_complex], apply_instance }

end chain_complex

-- TODO when V is enriched in W, what do we need to ensure
-- `chain_complex V` is also enriched in W?

-- TODO `chain_complex V` is a module category for `V` when `V` is monoidal

-- TODO When V is enriched in AddCommGroup, and has coproducts(?),
-- we can collapse a double complex to obtain a complex.
-- (Do we need boundedness assumptions)

-- TODO when V is monoidal, enriched in `AddCommGroup`,
-- and has coproducts(?) then
-- `chain_complex V` is monoidal too.
