import category_theory.functor

universes u₁ v₁ u₂

open category_theory

variables (C : Sort u₁) [𝒞 : category.{v₁} C]
variables (D : Sort u₂) [𝒟 : category.{0} D]
include 𝒞 𝒟

namespace category_theory.functor

/--
For functors into Prop-level categories, we can use extensionality without risking
generating `eq.rec`.
-/
@[extensionality] lemma ext_prop (F G : C ⥤ D) (w : ∀ X : C, F.obj X = G.obj X) : F = G :=
begin
  cases F, cases G,
  congr,
  funext,
  exact w x,
end

end category_theory.functor
