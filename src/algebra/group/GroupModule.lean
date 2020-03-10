import algebra.category.Group.basic
import category_theory.endomorphism

universe u₁

open category_theory

structure GroupModule (G : Group.{u₁}) :=
(V : AddCommGroup.{u₁})
(ρ : G ⟶ Group.of (Aut V))

namespace GroupModule
variable {G : Group.{u₁}}

@[ext]
structure hom (M N : GroupModule G) :=
(hom : M.V ⟶ N.V)
(comm' : ∀ g : G, (M.ρ g).hom ≫ hom = hom ≫ (N.ρ g).hom . obviously)

restate_axiom hom.comm'

namespace hom

@[simps]
def id (M : GroupModule G) : GroupModule.hom M M :=
{ hom := 𝟙 M.V }

@[simps]
def comp {M N K : GroupModule G} (p : GroupModule.hom M N) (q : GroupModule.hom N K) :
  GroupModule.hom M K :=
{ hom := p.hom ≫ q.hom,
  comm' := λ g, by rw [←category.assoc, p.comm, category.assoc, q.comm, ←category.assoc] }

end hom

instance : category (GroupModule G) :=
{ hom := λ M N, hom M N,
  id := λ M, hom.id M,
  comp := λ M N K f g, hom.comp f g, }

instance : concrete_category (GroupModule G) :=
{ forget :=
  { obj := λ M, M.V,
    map := λ M N f, f.hom },
  forget_faithful :=
  { injectivity' := λ M N f g w,
    begin
      -- TODO make this less tedious
      ext, apply add_monoid_hom.ext, intro x, change (M.V : Type u₁) at x,
      dsimp at w,
      rw w,
    end } }

instance has_forget_to_AddCommGroup : has_forget₂ (GroupModule G) AddCommGroup :=
{ forget₂ :=
  { obj := λ M, M.V,
    map := λ M N f, f.hom } }

@[simps]
def map {G H : Group} (f : G ⟶ H) : GroupModule H ⥤ GroupModule G :=
{ obj := λ M,
  { V := M.V,
    ρ := f ≫ M.ρ },
  map := λ M N p,
  { hom := p.hom,
    comm' := λ g, p.comm (f g) } }

@[simps]
def map_id {G : Group} : map (𝟙 G) ≅ 𝟭 (GroupModule G) :=
{ hom := { app := λ M, ⟨𝟙 M.V⟩ },
  inv := { app := λ M, ⟨𝟙 M.V⟩ }, }

@[simps]
def map_comp {G H K : Group} (f : G ⟶ H) (g : H ⟶ K) : map g ⋙ map f ≅ map (f ≫ g) :=
{ hom := { app := λ M, ⟨𝟙 M.V⟩ },
  inv := { app := λ M, ⟨𝟙 M.V⟩ }, }

-- TODO prove `GroupModule punit ≅ AddCommGroup`
-- TODO after `monoid_algebra` lands, prove the equivalence of categories
--   `GroupModule G ≅ Module (monoid_algebra G ℤ)`
-- TODO limits, colimits, images, etc
-- TODO symmetric monoidal category structure
-- TODO regular representation, induction functors (adjoint to `map`)

-- TODO generalise all this so `V` could equally well be an `AddCommGroup` or a k-vector space, or a ...?
-- TODO harder: generalise so `G` could be a `Monoid`, or a `LieGroup`, or a ...?
end GroupModule
