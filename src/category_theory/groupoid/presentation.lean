import category_theory.groupoid.vertex_group
import category_theory.groupoid.subgroupoid
import category_theory.groupoid
import category_theory.groupoid.basic
import category_theory.groupoid.quotient_two_steps
import category_theory.groupoid.free_groupoid


open set classical function
local attribute [instance] prop_decidable


namespace category_theory

universes u v

namespace groupoid

variables {V : Type u} [quiver.{v+1} V]

def word (x y : V) :=
  @quiver.path (quiver.symmetrify V) (quiver.symmetrify_quiver V) x y

def as_free (x : V) : free_groupoid V := ⟨x⟩

def word.as_free {x y : V} (w : word x y) : as_free x ⟶ as_free y :=
quot.mk _ w

variable  (W : ∀ (x y : free_groupoid V), set $ x ⟶ y)

def presented :=
  subgroupoid.quotient _ ( subgroupoid.generated_normal_is_normal W )

instance : groupoid (presented W) :=
  subgroupoid.quotient_groupoid _ ( subgroupoid.generated_normal_is_normal W )

noncomputable def of : prefunctor V (presented W) :=
  (free.of V).comp (subgroupoid.of _ ( subgroupoid.generated_normal_is_normal W )).to_prefunctor

section ump

variables {V' : Type*} [groupoid V'] (φ : prefunctor V V')
  (hφ : ∀ (x y : free_groupoid V), W x y ⊆ (subgroupoid.ker $ free.lift φ).arrws x y)

include φ hφ
def lift : presented W ⥤ V' :=
begin
  fapply subgroupoid.quotient.lift,
  apply free.lift φ,
  apply subgroupoid.generated_normal_le_of_containing_normal,
  apply subgroupoid.ker_is_normal,
  apply hφ,
end

def lift_spec : (of W).comp (lift W φ hφ).to_prefunctor = φ :=
begin
  dsimp only [of, lift],
  rw [prefunctor.comp_assoc, functor.to_prefunctor_comp],
  rw [subgroupoid.quotient.lift_spec, free.lift_spec],
end

def lift_unique (Φ : presented W ⥤ V') (hΦ : (of W).comp Φ.to_prefunctor = φ) :
  Φ = (lift W φ hφ) :=
begin
  dsimp only [of, lift],
  apply subgroupoid.quotient.lift_unique,
  apply free.lift_unique,
  exact hΦ,
end

end ump


end groupoid

end category_theory
