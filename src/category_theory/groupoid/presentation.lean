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

variables (V : Type u) [quiver V]

def word (V : Type u) [quiver V] (x y : V) :=
  @quiver.path (quiver.symmetrify V) (quiver.symmetrify_quiver V) x y

def as_free {V : Type u} [quiver V] (x : V) : free.free_groupoid V := ⟨x⟩

def word.as_free {V : Type u} [quiver V] {x y : V} (w : word V x y) : as_free x ⟶ as_free y :=
quot.mk _ w

def presented (V : Type u) [quiver V] (W : ∀ (x y : free.free_groupoid V), set $ x ⟶ y) :=
  subgroupoid.quotient _ ( subgroupoid.generated_normal_is_normal W )

def words_as_free {V : Type u} [quiver V] (W : ∀ (x y : V), set $ word V x y) :
  (∀ (x y : free.free_groupoid V), set $ x ⟶ y) :=
begin -- tactic mode because otherwise conversions don't work :(
  rintros ⟨x⟩ ⟨y⟩,
  exact (@word.as_free _ _ x y) '' (W x y),
end


end groupoid

end category_theory
