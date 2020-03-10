import category_theory.enriched.enriched_over
import algebra.category.Group.monoidal

universes u

open category_theory

namespace AddCommGroup

-- TODO generalise the next three, to anything with a forgetful functor preserving limits

-- def forget_unit : (forget AddCommGroup).obj (𝟙_ AddCommGroup) ≅ 𝟙_ (Type u) :=
-- (limits.preserves_limit_iso (functor.empty AddCommGroup) (forget AddCommGroup)).trans
--   (limits.lim.map_iso (functor.empty_comp (forget AddCommGroup)))

-- def forget_tensor (G H : AddCommGroup.{u}) :
--   (forget AddCommGroup).obj (G ⊗ H) ≅ (forget AddCommGroup).obj G ⊗ (forget AddCommGroup).obj H :=
-- (limits.preserves_limit_iso _ (forget AddCommGroup)).trans
--   (limits.lim.map_iso (limits.pair_comp G H (forget AddCommGroup)))

instance : concrete_monoidal_category AddCommGroup.{u} :=
{ lax_monoidal :=
  { ε := forget_unit.inv,
    μ := λ G H, (forget_tensor G H).inv,
    μ_natural' := λ X Y X' Y' f g, begin dsimp, ext, dsimp, end,
    associativity' := λ X Y Z, begin dsimp, ext, dsimp, end, }}

example : enriched_over AddCommGroup.{u} AddCommGroup.{u} :=
{ e_hom := λ X Y, AddCommGroup.of (X ⟶ Y),
  e_id := λ X, begin fsplit, exact λ x, 𝟙 X, end,
  e_comp := λ X Y Z p, p.val (limits.walking_pair.left) ≫ p.val (limits.walking_pair.right), -- that was ugly...
  e_hom_forget := λ X Y, equiv.refl _ }

-- TODO modules over a ring are enriched over themselves
-- TODO deduce from this that they are enriched over AddCommGroup

end AddCommGroup
