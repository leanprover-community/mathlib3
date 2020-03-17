import category_theory.graded_objects
import category_theory.full_subcategory
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.products
import category_theory.limits.shapes.images
import category_theory.limits.shapes.kernels

universes v u

open category_theory
open category_theory.limits

/--
A chain complex in the category `V` consists of
* a collection of objects `C` indexed by `ℤ`
* a differential `d i : C i ⟶ C (i-1)`
* so d^2 = 0
 -/
structure chain_complex (V : Type u) [𝒱 : category.{v} V] [has_zero_morphisms.{v} V] :=
(C : ℤ → V)
(d : Π i, C i ⟶ C (i-1))
(d_squared : ∀ i, d i ≫ d (i-1) = 0)

attribute [simp] chain_complex.d_squared

namespace chain_complex

variables {V : Type u} [𝒱 : category.{v} V] [has_zero_morphisms.{v} V]
include 𝒱

/--
A chain map is a collection of morphisms commuting with the differentials.
-/
@[ext]
structure hom (C D : chain_complex.{v} V) :=
(f : Π i, C.C i ⟶ D.C i)
(comm' : ∀ i, f i ≫ D.d i = C.d i ≫ f (i-1) . obviously)

restate_axiom hom.comm'

namespace hom
@[simps]
def id (C : chain_complex.{v} V) : hom C C :=
{ f := λ i, 𝟙 (C.C i), }

@[simps]
def comp {C D E : chain_complex.{v} V} (f : hom C D) (g : hom D E) : hom C E :=
{ f := λ i, f.f i ≫ g.f i,
  comm' := λ i, by rw [category.assoc, g.comm, ←category.assoc, f.comm, category.assoc], }

end hom

/-- The category of chain complexes and chain maps. -/
instance : category (chain_complex.{v} V) :=
{ hom  := hom,
  id   := hom.id,
  comp := @hom.comp _ _ _,  }.

@[simp]
lemma id_hom (C : chain_complex.{v} V) (i) : (𝟙 C : hom C C).f i = 𝟙 (C.C i) := rfl
@[simp]
lemma comp_hom {C D E : chain_complex.{v} V} (f : C ⟶ D) (g : D ⟶ E) (i) :
  (f ≫ g : hom C E).f i = f.f i ≫ g.f i :=
rfl

instance : has_zero_morphisms.{v} (chain_complex.{v} V) :=
{ has_zero := λ C C', ⟨{ f := λ i, 0 }⟩, }

end chain_complex

namespace chain_complex
variables {V : Type u} [𝒱 : category.{v} V] [has_zero_object.{v} V]
include 𝒱

local attribute [instance] has_zero_object.has_zero
local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

instance : has_zero_object.{v} (chain_complex.{v} V) :=
{ zero :=
  { C := λ i, 0,
    d := λ i, 0,
    d_squared := by tidy },
  unique_to := sorry,
  unique_from := sorry, }

end chain_complex

namespace chain_complex
variables {V : Type u} [𝒱 : category.{v} V] [has_zero_morphisms.{v} V]
include 𝒱

section
variables (V) [has_coproducts.{v} V]

/--
The total object of a chain complex is the coproduct of the chain groups.
-/
def total : chain_complex.{v} V ⥤ V :=
{ obj := λ C, ∐ (λ i : ulift ℤ, C.C i.down),
  map := λ C C' f, limits.sigma.map (λ i, f.f i.down) }.

/--
The `total` functor taking a chain complex to the coproduct of its chain groups is faithful.
To prove this, we need to know that the coprojections into the coproduct are monomorphisms,
which follows from the fact we have zero morphisms.
-/
instance : faithful (total V) :=
{ injectivity' := λ C C' f g w,
  begin
    ext i,
    replace w := sigma.ι (λ i : ulift ℤ, C.C i.down) ⟨i⟩ ≫= w,
    erw [colimit.ι_map, colimit.ι_map] at w,
    exact mono.right_cancellation _ _ w,
  end }
end

variables [has_images.{v} V] [has_equalizers.{v} V]

/-- The connecting morphism from the image of `d i` to the kernel of `d (i-1)`. -/
def image_to_kernel_map (C : chain_complex.{v} V) (i : ℤ) :
image (C.d i) ⟶ kernel (C.d (i-1)) :=
kernel.lift _ (image.ι (C.d i))
begin
  apply @epi.left_cancellation _ _ _ _ (factor_thru_image (C.d i)) _ _ _ _ _,
  simp,
end

def induced_map_on_cycles {C C' : chain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
  kernel (C.d i) ⟶ kernel (C'.d i) :=
kernel.lift _ (kernel.ι _ ≫ f.f i)
(by rw [category.assoc, f.comm, ←category.assoc, kernel.condition, has_zero_morphisms.zero_comp])

-- TODO:
-- At this level of generality, it's just not true that a chain map
-- induces maps on boundaries
--
-- Let's add these later, with appropriate (but hopefully fairly minimal)
-- assumptions; perhaps that the category is regular.

-- def induced_map_on_boundaries {C C' : chain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
--   image (C.d i) ⟶ image (C'.d i) :=
-- sorry

-- lemma induced_maps_commute {C C' : chain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
-- image_to_kernel_map C i ≫ induced_map_on_cycles f (i-1) =
--   induced_map_on_boundaries f i ≫ image_to_kernel_map C' i :=
-- sorry

variables [has_cokernels.{v} V]

/-- The `i`-th homology group of the chain complex `C`. -/
def homology_group (C : chain_complex.{v} V) (i : ℤ) : V :=
cokernel (image_to_kernel_map C i)

-- As noted above, as we don't get induced maps on boundaries with this generality,
-- we can't assemble the homology groups into a functor. Hopefully, however,
-- the commented out code below will work
-- (with whatever added assumptions are needed above.)

-- def induced_map_on_homology {C C' : chain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
--   C.homology_group i ⟶ C'.homology_group i :=
-- cokernel.desc _ (induced_map_on_cycles f (i-1) ≫ cokernel.π _)
-- begin
--   rw [←category.assoc, induced_maps_commute, category.assoc, cokernel.condition],
--   erw [has_zero_morphisms.comp_zero],
-- end

-- /-- The homology functor from chain complexes to `ℤ` graded objects in `V`. -/
-- def homology : chain_complex.{v} V ⥤ (ulift.{u} ℤ → V) :=
-- { obj := λ C i, homology_group C i.down,
--   map := λ C C' f i, induced_map_on_homology f i.down,
--   map_id' := sorry,
--   map_comp' := sorry, }

end chain_complex

section
local attribute [instance] has_zero_object.has_zero
local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

variables (V : Type u) [category.{v} V] [has_zero_object.{v} V]

structure bounded_chain_complex extends chain_complex.{v} V :=
(bound : ℤ)
(bounded_below : Π i, i < bound → (C i ≅ 0))
(bounded_above : Π i, i > bound → (C i ≅ 0))

instance : category.{v} (bounded_chain_complex.{v} V) :=
induced_category.category (λ C : bounded_chain_complex.{v} V, C.to_chain_complex)

instance : has_zero_object.{v} (bounded_chain_complex.{v} V) :=
{ zero :=
  { bound := 0,
    bounded_below := λ i h, iso.refl _,
    bounded_above := λ i h, iso.refl _,
    ..(0 : chain_complex.{v} V) },
  unique_to := sorry,
  unique_from := sorry, }

end

namespace chain_complex
variables
  {V : Type (u+1)} [𝒱 : concrete_category V] [has_zero_morphisms.{u} V] [has_coproducts.{u} V]
include 𝒱

instance : concrete_category (chain_complex.{u} V) :=
{ forget := total V ⋙ forget V }

instance : has_forget₂ (chain_complex.{u} V) V :=
{ forget₂ := total V }
end chain_complex

namespace bounded_chain_complex
variables
  {V : Type (u+1)} [𝒱 : concrete_category V] [has_zero_object.{u} V] [has_coproducts.{u} V]
include 𝒱

local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

instance : concrete_category (bounded_chain_complex.{u} V) :=
{ forget := induced_functor (λ C : bounded_chain_complex.{u} V, C.to_chain_complex) ⋙ forget (chain_complex.{u} V),
  forget_faithful := sorry, }

instance : has_forget₂ (bounded_chain_complex.{u} V) (chain_complex.{u} V) :=
{ forget₂ := induced_functor _ }

end bounded_chain_complex

/--
A double complex in the category `V` consists of
* a collection of objects `C` indexed by `ℤ × ℤ`
* differentials `d₁ i j : C i j ⟶ C (i-1) j` and `d₂ i j : C i j ⟶ C i (j-1)`
* so `dᵢ^2 = 0` and `d₁ d₂ = d₂ d₁`
 -/
structure double_complex (V : Type u) [𝒱 : category.{v} V] [has_zero_morphisms.{v} V] :=
(C : ℤ → ℤ → V)
(d₁ : Π i j, C i j ⟶ C (i-1) j)
(d₂ : Π i j, C i j ⟶ C i (j-1))
(d₁_squared : ∀ i j, d₁ i j ≫ d₁ (i-1) j = 0)
(d₂_squared : ∀ i j, d₂ i j ≫ d₁ i (j-1) = 0)
(d_comm : ∀ i j, d₁ i j ≫ d₂ (i-1) j = d₂ i j ≫ d₁ i (j-1))

attribute [simp] double_complex.d₁_squared double_complex.d₂_squared

section
local attribute [instance] has_zero_object.has_zero
local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

structure bounded_double_complex (V : Type u) [𝒱 : category.{v} V] [has_zero_object.{v} V] extends double_complex.{v} V :=
(bound : ℤ)
(bounded_below : Π i j, i < bound → (C i j ≅ 0))
(bounded_above : Π i j, i > bound → (C i j ≅ 0))
(bounded_left : Π i j, j < bound → (C i j ≅ 0))
(bounded_right : Π i j, j > bound → (C i j ≅ 0))
end

namespace double_complex
variables {V : Type u} [𝒱 : category.{v} V] [has_zero_morphisms.{v} V]
include 𝒱

def of (C : chain_complex (chain_complex V)) : double_complex V :=
{ C := λ i j, (C.C i).C j,
  d₁ := λ i j, (C.d i).f j,
  d₂ := λ i j, (C.C i).d j,
  d₁_squared := sorry,
  d₂_squared := sorry,
  d_comm := sorry, }
-- TODO continue proving the equivalence of categories

end double_complex

namespace bounded_double_complex
variables {V : Type u} [𝒱 : category.{v} V] [has_zero_object.{v} V]
include 𝒱

local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

def of (C : bounded_chain_complex.{v} (bounded_chain_complex.{v} V)) : bounded_double_complex.{v} V :=
{ C := λ i j, (C.C i).C j,
  d₁ := λ i j, (C.d i).f j,
  d₂ := λ i j, (C.C i).d j,
  d₁_squared := sorry,
  d₂_squared := sorry,
  d_comm := sorry,
  bound := sorry,
  bounded_below := sorry,
  bounded_above := sorry,
  bounded_left := sorry,
  bounded_right := sorry, }

end bounded_double_complex

-- TODO When V is enriched in AddCommGroup, we can collapse a bounded double complex
-- to obtain a complex. We'll later use this to define the tensor product of complexes.

-- TODO when V is monoidal, and enriched in `AddCommGroup`, then
-- `chain_complex V` is monoidal too.

-- TODO when V is enriched in W, what extra structure do we need to ensure
-- `chain_complex V` is also enriched in W?
