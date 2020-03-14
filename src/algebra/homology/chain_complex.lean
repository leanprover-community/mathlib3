import category_theory.limits.shapes.zero
import category_theory.limits.shapes.products
import category_theory.limits.shapes.images
import category_theory.limits.shapes.kernels

universes v u

open category_theory
open category_theory.limits

structure chain_complex (V : Type u) [𝒱 : category.{v} V] [has_zero_morphisms.{v} V] :=
(C : ℤ → V)
(d : Π i, C i ⟶ C (i+1))
(d_squared : ∀ i, d i ≫ d (i+1) = 0)

attribute [simp] chain_complex.d_squared

namespace chain_complex

variables {V : Type u} [𝒱 : category.{v} V] [has_zero_morphisms.{v} V]
include 𝒱

@[ext]
structure hom (C D : chain_complex.{v} V) :=
(f : Π i, C.C i ⟶ D.C i)
(comm' : ∀ i, f i ≫ D.d i = C.d i ≫ f (i + 1) . obviously)

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

section
variables (V) [has_coproducts.{v} V]

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

def image_to_kernel_hom (C : chain_complex.{v} V) (i : ℤ) :
image (C.d i) ⟶ kernel (C.d (i+1)) :=
kernel.lift (image.ι (C.d i))
begin
  apply @epi.left_cancellation _ _ _ _ (factor_thru_image (C.d i)) _ _ _ _ _,
  simp,
end

variables [has_cokernels.{v} V]

def homology (C : chain_complex.{v} V) (i : ℤ) : V :=
cokernel (image_to_kernel_hom C i)

end chain_complex

namespace chain_complex
variables
  {V : Type (u+1)} [𝒱 : concrete_category V]
  [has_zero_morphisms.{u} V] [has_coproducts.{u} V]
include 𝒱

instance : concrete_category (chain_complex.{u} V) :=
{ forget := total V ⋙ forget V }

instance : has_forget₂ (chain_complex.{u} V) V :=
{ forget₂ := total V }

end chain_complex

-- TODO when V is monoidal, and enriched in `AddCommGroup`, then
-- `chain_complex V` is monoidal too.

-- TODO when V is enriched in W, what extra structure do we need to ensure
-- `chain_complex V` is also enriched in W?
