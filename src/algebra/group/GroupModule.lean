import algebra.category.Group
import category_theory.endomorphism

universes u₁

open category_theory

variables (𝕍 : Type (u₁+1)) [𝒱 : large_category 𝕍]
include 𝒱

/--
A `GroupModule 𝕍 G`, where
`𝕍` is a category (for example `AddCommGroup` or vector spaces) and
`G : Group`,
consists of an underlying `V : 𝕍`,
and a group homomorphism from `G` to the group of automorphisms of `V`.
-/
structure GroupModule (G : Group.{u₁}) :=
(V : 𝕍)
(ρ : G ⟶ Group.of (Aut V))

namespace GroupModule
variable (G : Group.{u₁})

/-- The trivial representation of a group. -/
-- TODO What is the correct generalisation for an arbitrary `𝕍`?
def trivial : GroupModule AddCommGroup G :=
{ V := 0,
  ρ := 1, }

instance : inhabited (GroupModule AddCommGroup G) := ⟨trivial AddCommGroup G⟩

variables {G 𝕍}

/--
A homomorphism of `GroupModule G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
structure hom (M N : GroupModule 𝕍 G) :=
(hom : M.V ⟶ N.V)
(comm' : ∀ g : G, (M.ρ g).hom ≫ hom = hom ≫ (N.ρ g).hom . obviously)

restate_axiom hom.comm'

namespace hom

/-- The identity morphism on a `GroupModule G`. -/
@[simps]
def id (M : GroupModule 𝕍 G) : GroupModule.hom M M :=
{ hom := 𝟙 M.V }

instance (M : GroupModule 𝕍 G) : inhabited (GroupModule.hom M M) := ⟨id M⟩

/--
The composition of two `GroupModule G` homomorphisms is the composite of the underlying maps.
-/
@[simps]
def comp {M N K : GroupModule 𝕍 G} (p : GroupModule.hom M N) (q : GroupModule.hom N K) :
  GroupModule.hom M K :=
{ hom := p.hom ≫ q.hom,
  comm' := λ g, by rw [←category.assoc, p.comm, category.assoc, q.comm, ←category.assoc] }

end hom

instance : category (GroupModule 𝕍 G) :=
{ hom := λ M N, hom M N,
  id := λ M, hom.id M,
  comp := λ M N K f g, hom.comp f g, }

@[simp]
lemma id_hom (M : GroupModule 𝕍 G) : (𝟙 M : hom M M).hom = 𝟙 M.V := rfl
@[simp]
lemma comp_hom {M N K : GroupModule 𝕍 G} (f : M ⟶ N) (g : N ⟶ K) :
  (f ≫ g : hom M K).hom = f.hom ≫ g.hom :=
rfl

section forget

def forget : GroupModule 𝕍 G ⥤ 𝕍 :=
{ obj := λ M, M.V,
  map := λ M N f, f.hom, }

omit 𝒱
instance [concrete_category 𝕍] : concrete_category (GroupModule 𝕍 G) :=
{ forget := forget ⋙ (concrete_category.forget 𝕍),
  forget_faithful :=
  { injectivity' := λ M N f g w,
    begin
      ext,
      apply faithful.injectivity (concrete_category.forget 𝕍),
      exact w,
    end } }

instance has_forget_to_𝕍 [concrete_category 𝕍] : has_forget₂ (GroupModule 𝕍 G) 𝕍 :=
{ forget₂ := forget }

end forget

variables (𝕍)
/--
The restriction functor along a group homomorphism `f : G ⟶ H`,
taking modules for `H` to modules for `G`.
-/
@[simps]
def res {G H : Group} (f : G ⟶ H) : GroupModule 𝕍 H ⥤ GroupModule 𝕍 G :=
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
def res_id {G : Group} : res 𝕍 (𝟙 G) ≅ 𝟭 (GroupModule 𝕍 G) :=
{ hom := { app := λ M, ⟨𝟙 M.V⟩ },
  inv := { app := λ M, ⟨𝟙 M.V⟩ }, }

/--
The natural isomorphism from the composite of restrictions along homomorphisms
to the restriction along the composite homomorphism.
-/
@[simps]
def res_comp {G H K : Group} (f : G ⟶ H) (g : H ⟶ K) : res 𝕍 g ⋙ res 𝕍 f ≅ res 𝕍 (f ≫ g) :=
{ hom := { app := λ M, ⟨𝟙 M.V⟩ },
  inv := { app := λ M, ⟨𝟙 M.V⟩ }, }

-- TODO prove `GroupModule 𝕍 punit ≅ 𝕍`
-- TODO after `monoid_algebra` lands, prove the equivalence of categories
--   `GroupModule AddCommGroup G ≅ Module ℤ (monoid_algebra G ℤ)`
-- TODO limits, colimits, images, etc
-- TODO symmetric monoidal category structure
-- TODO regular representation, induction functors (adjoint to `res`)

-- TODO generalise so `G` could be a `Monoid`, or a `LieGroup`, or a ...?
end GroupModule
