import algebraic_geometry.pullbacks
import category_theory.limits.constructions.over.products

universes v u w
open algebraic_geometry category_theory category_theory.limits
variables (k : CommRing.{u})

abbreviation Over := over (Scheme.Spec.obj (opposite.op k))

abbreviation GroupScheme :=
full_subcategory ({ G : (Over k)ᵒᵖ ⥤ Group.{u} | (G ⋙ forget _).representable })

#exit
local attribute [instance] over.construct_products.over_binary_product_of_pullback
  over.over_has_terminal

structure GroupScheme :=
(G : Over k)
(mul : G ⨯ G ⟶ G)
(one : over.mk (𝟙 _) ⟶ G)
(inv : G ⟶ G)
(assoc : limits.prod.map mul (𝟙 G) ≫ mul = (limits.prod.associator G G G).hom
  ≫ limits.prod.map (𝟙 G) mul ≫ mul)
(one_mul : limits.prod.map one (𝟙 G) ≫ mul = limits.prod.snd)
(mul_left_inv : limits.diag G ≫ limits.prod.map inv (𝟙 G) ≫ mul = terminal.from G ≫ one)

variables {k}

structure GroupScheme.hom {k : CommRing.{u}} (G H : GroupScheme k) :=
(f : G.G ⟶ H.G)
(comm : G.mul ≫ f = limits.prod.map f f ≫ H.mul)
