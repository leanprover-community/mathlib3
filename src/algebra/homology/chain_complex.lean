import category_theory.limits.shapes.zero
import category_theory.limits.shapes.products

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
  comm' := sorry }

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

end chain_complex

namespace chain_complex
variables
  (V : Type) [𝒱 : category.{0} V]
  [has_zero_morphisms.{0} V] [has_coproducts.{0} V]
include 𝒱

def total : chain_complex.{0} V ⥤ V :=
{ obj := λ C, ∐ C.C,
  map := λ C C' f, limits.sigma.map f.f }.

/--
The `total` functor taking a chain complex to the coproduct of its chain groups is faithful.
To prove this, we need to know that the coprojections into the coproduct are monomorphisms,
which follows from the fact we have zero morphisms.
-/
instance : faithful (total V) :=
{ injectivity' := λ C C' f g w,
  begin
    ext i,
    replace w := sigma.ι C.C i ≫= w,
    erw [colimit.ι_map, colimit.ι_map] at w,
    exact mono.right_cancellation _ _ w,
  end }

end chain_complex

namespace chain_complex
variables
  {V : Type (u+1)} [𝒱 : concrete_category V]
  [has_zero_morphisms.{u} V]
include 𝒱

def forget : chain_complex.{u} V ⥤ Type u :=
{ obj := λ C, Π i, (forget V).obj (C.C i),
  map := λ C D f, λ g i, (forget V).map (f.f i) (g i) }

instance : concrete_category (chain_complex.{u} V) :=
{ forget := forget,
  forget_faithful :=
  { injectivity' := λ X Y f g w,
    begin
      ext i,
      apply faithful.injectivity (category_theory.forget V),
      ext x,
      dsimp [forget] at w,
      have w' := congr_fun (congr_fun w (λ j, if h : j = i then by { subst h, exact x } else sorry)) i,
      dsimp at w',
      rw [dif_pos rfl] at w',
      exact w',
    end }, }

-- TODO, using [has_coproducts.{u} V], define the "total object" functor to V?

end chain_complex

-- TODO when V is monoidal, and enriched in `AddCommGroup`, then
-- `chain_complex V` is monoidal too.

-- TODO when V is enriched in W, what extra structure do we need to ensure
-- `chain_complex V` is also enriched in W?
