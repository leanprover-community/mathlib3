import algebra.category.Group
import category_theory.endomorphism

universe u₁

open category_theory

/--
A `GroupModule G` consists of an underlying `V : AddCommGroup`,
and a group homomorphism from `G` to the group of automorphisms of `V`.
-/
structure GroupModule (G : Group.{u₁}) :=
(V : AddCommGroup.{u₁})
(ρ : G ⟶ Group.of (Aut V))

namespace GroupModule
variable (G : Group.{u₁})

def trivial : GroupModule G :=
{ V := 0,
  ρ := 1, }

instance : inhabited (GroupModule G) := ⟨trivial G⟩

variable {G}

/--
A homomorphism of `GroupModule G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
structure hom (M N : GroupModule G) :=
(hom : M.V ⟶ N.V)
(comm' : ∀ g : G, (M.ρ g).hom ≫ hom = hom ≫ (N.ρ g).hom . obviously)

restate_axiom hom.comm'

namespace hom

/-- The identity morphism on a `GroupModule G`. -/
@[simps]
def id (M : GroupModule G) : GroupModule.hom M M :=
{ hom := 𝟙 M.V }

instance (M : GroupModule G) : inhabited (GroupModule.hom M M) := ⟨id M⟩

/--
The composition of two `GroupModule G` homomorphisms is the composite of the underlying maps.
-/
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

/--
The restriction functor along a group homomorphism `f : G ⟶ H`,
taking modules for `H` to modules for `G`.
-/
@[simps]
def res {G H : Group} (f : G ⟶ H) : GroupModule H ⥤ GroupModule G :=
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
def res_id {G : Group} : res (𝟙 G) ≅ 𝟭 (GroupModule G) :=
{ hom := { app := λ M, ⟨𝟙 M.V⟩ },
  inv := { app := λ M, ⟨𝟙 M.V⟩ }, }

/--
The natural isomorphism from the composite of restrictions along homomorphisms
to the restriction along the composite homomorphism.
-/
@[simps]
def res_comp {G H K : Group} (f : G ⟶ H) (g : H ⟶ K) : res g ⋙ res f ≅ res (f ≫ g) :=
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
