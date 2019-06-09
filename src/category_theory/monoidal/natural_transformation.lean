import category_theory.monoidal.functor

open category_theory

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open category_theory.category

namespace category_theory

variables {C : Type u₁} [𝒞 : monoidal_category.{v₁} C]
          {D : Type u₂} [𝒟 : monoidal_category.{v₂} D]
variables (F G : monoidal_functor.{v₁ v₂} C D)

open monoidal_category

structure monoidal_nat_trans extends nat_trans F.to_functor G.to_functor :=
(monoidal' : Π X Y : C,
  app (X ⊗ Y) = inv (F.μ X Y) ≫ (app X ⊗ app Y) ≫ G.μ X Y . obviously )

restate_axiom monoidal_nat_trans.monoidal'
attribute [simp] monoidal_nat_trans.monoidal

namespace monoidal_nat_trans

def id : monoidal_nat_trans F F :=
{ ..(nat_trans.id F.to_functor) }

variables {F G}
variable {H : monoidal_functor.{v₁ v₂} C D}

section
variables (σ : monoidal_nat_trans F G) (τ : monoidal_nat_trans G H)

def vcomp : monoidal_nat_trans F H :=
{ ..(nat_trans.vcomp σ.to_nat_trans τ.to_nat_trans) }

end

-- variables {E : Type u₃} [ℰ : monoidal_category.{v₃} E]
-- variables {K L : monoidal_functor.{v₂ v₃} D E}

-- section

-- variables (σ : monoidal_nat_trans F G) (τ : monoidal_nat_trans K L)

-- def hcomp  : monoidal_nat_trans (F.comp K) (G.comp L) :=
-- { monoidal' :=
--   begin
--     tidy?,
--   end,
--   ..(nat_trans.hcomp σ.to_nat_trans τ.to_nat_trans) }

-- end

end monoidal_nat_trans
end category_theory
