import category_theory.groupoid
import category_theory.groupoid.quotient_two_steps
import category_theory.groupoid.free_groupoid


open set classical function
local attribute [instance] prop_decidable


namespace category_theory

universes u v

namespace groupoid

variables {V : Type u} [quiver.{v+1} V] (W : ∀ (x y : free_groupoid V), set $ x ⟶ y)

def presented :=
  quotient _ ( subgroupoid.generated_normal_is_normal W )

instance : groupoid (presented W) :=
  quotient.quotient_groupoid _ ( subgroupoid.generated_normal_is_normal W )

namespace presented

noncomputable def of : prefunctor V (presented W) :=
  (free.of V).comp (quotient.of _ ( subgroupoid.generated_normal_is_normal W )).to_prefunctor

section ump

variables {V' : Type*} [groupoid V'] (φ : prefunctor V V')
  (hφ : ∀ (x y : free_groupoid V), W x y ⊆ (subgroupoid.ker $ free.lift φ).arrws x y)

include φ hφ
def lift : presented W ⥤ V' :=
begin
  fapply quotient.lift,
  { apply free.lift φ, },
  { apply subgroupoid.generated_normal_le_of_containing_normal,
    apply subgroupoid.ker_is_normal,
    apply hφ },
end

def lift_spec : (of W).comp (lift W φ hφ).to_prefunctor = φ :=
begin
  dsimp only [of, lift],
  rw [prefunctor.comp_assoc, functor.to_prefunctor_comp],
  rw [quotient.lift_spec, free.lift_spec],
end

def lift_unique (Φ : presented W ⥤ V') (hΦ : (of W).comp Φ.to_prefunctor = φ) :
  Φ = (lift W φ hφ) :=
begin
  dsimp only [of, lift],
  apply quotient.lift_unique,
  apply free.lift_unique,
  exact hΦ,
end

end ump

end presented

end groupoid

end category_theory
