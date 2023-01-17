import logic.function.basic
import algebra.hom.aut
import algebra.group.pi
import group_theory.subgroup.basic
import group_theory.semidirect_product
import group_theory.group_action.defs

section bare_def

variables (A : Type*) (B : Type*) (L : Type*)

@[ext]
structure wreath_product :=
(left: L → B) (right : A)

end bare_def

section group

variables (A : Type*) (B : Type*) (L : Type*) [group A] [group B] [mul_action A L]


instance wreath_product_group : group (wreath_product A B L) :=
{ one := ⟨1, 1⟩,
  mul := λ g h, ⟨g.1 * (λ l, h.1 (g.2⁻¹ • l)) , g.2 * h.2⟩,
  inv := λ x, ⟨ (λ l, x.1⁻¹ (x.2 • l)), x.2⁻¹⟩,
  mul_assoc := begin
    rintros ⟨f1, a1⟩ ⟨f2, a2⟩ ⟨f3, a3⟩,
    ext l,
    {
      simp only [pi.mul_apply, mul_assoc, mul_inv_rev, mul_smul],
    },
    {
      simp only [mul_assoc],
    }
  end,
  one_mul := begin
    rintros ⟨f, a⟩,
    ext l,
    {
      simp only [inv_one, one_smul, one_mul],
    },
    {
      simp only [one_mul],
    }
  end,
  mul_one := begin
    rintros ⟨f, a⟩,
    ext l,
    {
      simp only [pi.one_apply, pi.mul_apply, mul_one],
    },
    {
      simp only [mul_one],
    }
  end,
  mul_left_inv := begin
    rintros ⟨f, a⟩,
    ext l,
    {
      have goal : (((λ l, f⁻¹ (a • l)) * (λ l, f ((a⁻¹)⁻¹ • l))) l = 1),
      {
        simp,
      },
      exact goal,
    },
    {
      have goal : a⁻¹ * a = 1 := by simp,
      exact goal,
    }
  end,
}

end group

notation B` ≀[`:35 L:35`] `:0 A :35 := wreath_product A B L
