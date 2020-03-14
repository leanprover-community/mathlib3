import category_theory.enriched.enriched_over
import algebra.category.Module.monoidal

universes u

open category_theory

namespace Module

/-
𝟙_ is monoidal_category.tensor_unit

-/

--#check monoidal_category.tensor_unit

--def fooz : monoidal_category Type := by apply_instance

--#print fooz

--def fooz : monoidal_category Type := by apply_instance
--def barz : concrete_monoidal_category Type := by apply_instance

--example : monoidal_category.tensor_unit Type = pempty → pempty := rfl

-- 𝟙_ Type : Type
--example : monoidal_category.tensor_unit Type = unit := rfl
--example : monoidal_category.tensor_unit Type = limits.terminal Type := rfl

--def foo := monoidal_category.tensor_unit (Module ℤ)

-- example : false :=
-- begin
--   set X := monoidal_category.tensor_unit (Module ℤ) with hX,
--   unfold monoidal_category.tensor_unit at hX,
--   unfold of at hX,
--   sorry

-- end



--set_option pp.notation false
instance : concrete_monoidal_category (Module ℤ) :=
{ lax_monoidal :=
  { ε := λ _, 0,
    μ := λ G H, sorry,
    μ_natural' := λ X Y X' Y' f g, sorry,
    associativity' := λ X Y Z, sorry,
    left_unitality' := sorry,
    right_unitality' := sorry
  }
}

#exit
example : enriched_over (Module ℤ) (Module ℤ) :=
{ e_hom := λ X Y, Module.of ℤ (X ⟶ Y),
  e_id := λ X, sorry,
  e_comp := λ X Y Z p, sorry,
  e_hom_forget := λ X Y, equiv.refl _ }

-- TODO modules over a ring are enriched over themselves
-- TODO deduce from this that they are enriched over AddCommGroup

end AddCommGroup
