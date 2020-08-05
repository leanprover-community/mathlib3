import category_theory.limits.shapes.binary_products
import data.equiv.fin
import algebra

/-!

# Experiments with Lawvere Theories

This is just some experimentation, for now.

-/

open category_theory

class Lawvere (C : Type*) extends category C :=
(pow : ℕ ≃ C)
(π₁ {a b : ℕ} : pow (a + b) ⟶ pow a)
(π₂ {a b : ℕ} : pow (a + b) ⟶ pow b)
(lift {a b c : ℕ} : (pow c ⟶ pow a) → (pow c ⟶ pow b) → (pow c ⟶ pow (a + b)))
(lift_π₁ {a b c : ℕ} (f : pow c ⟶ pow a) (g : pow c ⟶ pow b) : lift f g ≫ π₁ = f)
(lift_π₂ {a b c : ℕ} (f : pow c ⟶ pow a) (g : pow c ⟶ pow b) : lift f g ≫ π₂ = g)
(lift_unique {a b c : ℕ} (f : pow c ⟶ pow a) (g : pow c ⟶ pow b) (h : pow c ⟶ pow (a + b)):
  h ≫ π₁ = f → h ≫ π₂ = g → h = lift f g)

open Lawvere
structure LawvereHom (C : Type*) [Lawvere C] (D : Type*) [Lawvere D] :=
(to_func : C ⥤ D)
(obj_compat {n} : to_func.obj (pow n) = pow n)

@[derive add_comm_monoid]
def prods (A : Type*) := ℕ

namespace prods

instance {A : Type*} : Lawvere (prods A) :=
{ hom := λ a b, (fin a → A) → (fin b → A),
  id := λ a, id,
  comp := λ _ _ _ f g, g ∘ f,
  pow := equiv.cast rfl,
  π₁ := λ a b f x, f $ sum_fin_sum_equiv $ sum.inl x,
  π₂ := λ a b f x, f $ sum_fin_sum_equiv $ sum.inr x,
  lift := λ a b c f g h x, sum.cases_on (sum_fin_sum_equiv.symm x) (f h) (g h),
  lift_π₁ := begin
    intros a b c f g,
    ext,
    simp only [function.comp_app],
    rw equiv.symm_apply_apply,
  end,
  lift_π₂ := begin
    intros a b c f g,
    ext,
    simp only [function.comp_app],
    rw equiv.symm_apply_apply,
  end,
  lift_unique := begin
    intros a b c f g h h1 h2,
    ext as,
    rw ←sum_fin_sum_equiv.apply_symm_apply x,
    cases sum_fin_sum_equiv.symm x,
    { rw [equiv.symm_apply_apply, ←h1] },
    { rw [equiv.symm_apply_apply, ←h2] }
  end }

class model (C : Type*) [Lawvere C] (A : Type*) extends LawvereHom C (prods A)

end prods
