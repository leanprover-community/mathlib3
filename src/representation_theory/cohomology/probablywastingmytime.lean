#exit
import algebra.category.Group.limits
import category_theory.Fintype
-- a file that is definitely not long for this world.
universes v u

open category_theory

structure FinGroup :=
(to_Group : Group)
[has_fintype : fintype to_Group]

namespace FinGroup

def of (X : Type*) [group X] [fintype X] : FinGroup := ⟨⟨X⟩⟩

instance : inhabited FinGroup := ⟨FinGroup.of punit⟩
instance : has_coe_to_sort FinGroup Type* := ⟨λ X, X.to_Group⟩
instance (X : FinGroup) : group X := by apply_instance
instance (X : FinGroup) : fintype X := X.has_fintype
def to_Fintype (X : FinGroup) : Fintype := Fintype.of X

instance category : category FinGroup := induced_category.category to_Group
instance concrete_category : concrete_category FinGroup := induced_category.concrete_category _
instance has_forget₂_to_Group : has_forget₂ FinGroup Group := induced_category.has_forget₂ _
instance has_forget₂_to_Fintype : has_forget₂ FinGroup Fintype :=
{ forget₂ := { obj := λ X, Fintype.of X, map := λ X Y f, f } }

@[simp] lemma coe_to_Group {X : FinGroup} : (X.to_Group : Type*) = X := rfl
@[simp] lemma coe_to_Fintype {X : FinGroup} : (X.to_Fintype : Type*) = X := rfl

@[simp] lemma coe_id (X : Fintype) : (𝟙 X : X → X) = id := rfl

@[simp] lemma coe_comp {X Y Z : Fintype} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f := rfl

end FinGroup

@[simps, derive [full, faithful]]
def FinGroup_to_Group : FinGroup ⥤ Group := induced_functor _

@[simps, derive [faithful]]
def FinGroup_to_Fintype : FinGroup ⥤ Fintype := forget₂ _ _
