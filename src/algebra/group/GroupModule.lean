import algebra.category.Group.basic
import category_theory.endomorphism

universes u₁

open category_theory

variables (𝕍 : Type (u₁+1)) [𝒱 : large_category 𝕍]
include 𝒱

/--
An `Action 𝕍 G` represents a bundled action of
the monoid `G` on an object of some category `𝕍`.
(Note: it is _not_ a categorical action of `G` on `𝕍`.)

As an example, when `𝕍 = Module R`, this is an `R`-linear representation of `G`.
-/
structure Action (G : Mon.{u₁}) :=
(V : 𝕍)
(ρ : G ⟶ Mon.of (End V))

namespace Action
variable {𝕍}

@[simp]
lemma ρ_1 {G : Mon.{u₁}} (A : Action 𝕍 G) : A.ρ 1 = 𝟙 A.V :=
by { rw [monoid_hom.map_one], refl, }

/-- When a group acts, we can lift the action to the group of automorphisms. -/
def ρ_Aut {G : Group.{u₁}} (A : Action 𝕍 (Mon.of G)) : G ⟶ Group.of (Aut A.V) :=
{ to_fun := λ g,
  { hom := A.ρ g,
    inv := A.ρ g⁻¹,
    -- FIXME inconsistent naming in core: `inv_mul_self` but `mul_inv_self`
    hom_inv_id' := ((A.ρ).map_mul g⁻¹ g).symm.trans (by rw [mul_left_inv, ρ_1]),
    inv_hom_id' := ((A.ρ).map_mul g g⁻¹).symm.trans (by rw [mul_inv_self, ρ_1]), },
  map_one' := by { ext, exact A.ρ.map_one },
  map_mul' := λ x y, by { ext, exact A.ρ.map_mul x y }, }

@[simp]
lemma ρ_Aut_apply_hom {G : Group.{u₁}} (A : Action 𝕍 (Mon.of G)) (g : G) : (A.ρ_Aut g).hom = A.ρ g := rfl

@[simp]
lemma ρ_Aut_apply_inv {G : Group.{u₁}} (A : Action 𝕍 (Mon.of G)) (g : G) : (A.ρ_Aut g).inv = A.ρ g⁻¹ := rfl

variable (G : Mon.{u₁})

section
omit 𝒱

/-- The trivial representation of a group. -/
-- TODO What is the correct generalisation for an arbitrary `𝕍`?
-- When 𝕍 is monoidal, the monoidal unit.
def trivial : Action AddCommGroup G :=
{ V := 0,
  ρ := 1, }

instance : inhabited (Action AddCommGroup G) := ⟨trivial G⟩
end

variables {G 𝕍}

/--
A homomorphism of `Action 𝕍 G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
structure hom (M N : Action 𝕍 G) :=
(hom : M.V ⟶ N.V)
(comm' : ∀ g : G, M.ρ g ≫ hom = hom ≫ N.ρ g . obviously)

restate_axiom hom.comm'

namespace hom

/-- The identity morphism on a `Action 𝕍 G`. -/
@[simps]
def id (M : Action 𝕍 G) : Action.hom M M :=
{ hom := 𝟙 M.V }

instance (M : Action 𝕍 G) : inhabited (Action.hom M M) := ⟨id M⟩

/--
The composition of two `Action 𝕍 G` homomorphisms is the composite of the underlying maps.
-/
@[simps]
def comp {M N K : Action 𝕍 G} (p : Action.hom M N) (q : Action.hom N K) :
  Action.hom M K :=
{ hom := p.hom ≫ q.hom,
  comm' := λ g, by rw [←category.assoc, p.comm, category.assoc, q.comm, ←category.assoc] }

end hom

instance : category (Action 𝕍 G) :=
{ hom := λ M N, hom M N,
  id := λ M, hom.id M,
  comp := λ M N K f g, hom.comp f g, }

@[simp]
lemma id_hom (M : Action 𝕍 G) : (𝟙 M : hom M M).hom = 𝟙 M.V := rfl
@[simp]
lemma comp_hom {M N K : Action 𝕍 G} (f : M ⟶ N) (g : N ⟶ K) :
  (f ≫ g : hom M K).hom = f.hom ≫ g.hom :=
rfl

section forget

/-- (implementation) The forgetful functor from bundled actions to the underlying objects.

Use the `category_theory.forget` API provided by the `concrete_category` instance below,
rather than using this directly.
-/
def forget : Action 𝕍 G ⥤ 𝕍 :=
{ obj := λ M, M.V,
  map := λ M N f, f.hom, }

omit 𝒱
instance [concrete_category 𝕍] : concrete_category (Action 𝕍 G) :=
{ forget := forget ⋙ (concrete_category.forget 𝕍),
  forget_faithful :=
  { injectivity' := λ M N f g w,
    begin
      ext,
      apply faithful.injectivity (concrete_category.forget 𝕍),
      exact w,
    end } }

instance has_forget_to_𝕍 [concrete_category 𝕍] : has_forget₂ (Action 𝕍 G) 𝕍 :=
{ forget₂ := forget }

end forget

variables (𝕍)
/--
The restriction functor along a monoid homomorphism `f : G ⟶ H`,
taking actions for `H` to action for `G`.
-/
@[simps]
def res {G H : Mon} (f : G ⟶ H) : Action 𝕍 H ⥤ Action 𝕍 G :=
{ obj := λ M,
  { V := M.V,
    ρ := f ≫ M.ρ },
  map := λ M N p,
  { hom := p.hom,
    comm' := λ g, p.comm (f g) } }

/--
The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `GroupModule G`.
-/
@[simps]
def res_id {G : Mon} : res 𝕍 (𝟙 G) ≅ 𝟭 (Action 𝕍 G) :=
{ hom := { app := λ M, ⟨𝟙 M.V⟩ },
  inv := { app := λ M, ⟨𝟙 M.V⟩ }, }

/--
The natural isomorphism from the composite of restrictions along homomorphisms
to the restriction along the composite homomorphism.
-/
@[simps]
def res_comp {G H K : Mon} (f : G ⟶ H) (g : H ⟶ K) : res 𝕍 g ⋙ res 𝕍 f ≅ res 𝕍 (f ≫ g) :=
{ hom := { app := λ M, ⟨𝟙 M.V⟩ },
  inv := { app := λ M, ⟨𝟙 M.V⟩ }, }

-- TODO prove `Action 𝕍 punit ≅ 𝕍`
-- TODO after `monoid_algebra` lands, prove the equivalence of categories
--   `Action (Module R) G ≅ Module (monoid_algebra R G)`
-- TODO limits, colimits, images, etc
-- TODO symmetric monoidal category structure
-- TODO regular representation, induction functors (adjoint to `res`)

end Action

namespace category_theory.functor

variables {𝕍} {𝕎 : Type (u₁+1)} [𝒲 : large_category 𝕎]
include 𝒲

@[simps]
def map_Action (F : 𝕍 ⥤ 𝕎) (G : Mon.{u₁}) : Action 𝕍 G ⥤ Action 𝕎 G :=
{ obj := λ M,
  { V := F.obj M.V,
    ρ :=
    { to_fun := λ g, F.map (M.ρ g),
      map_one' := by tidy,
      map_mul' := by simp, }},
  map := λ M N f,
  { hom := F.map f.hom,
    comm' := λ g, by { dsimp, rw [←F.map_comp, f.comm, F.map_comp] } }, }

-- TODO natural isomorphisms for the identity functor and compositions of functors

end category_theory.functor
