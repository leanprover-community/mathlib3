import algebra.category.Group
import algebra.category.Module.epi_mono

section

open category_theory

universe u

variables {A B : Type u} [add_comm_group A] [add_comm_group B]
variables (f : AddCommGroup.of A ⟶ AddCommGroup.of B)

lemma AddCommGroup.mono_iff_injective :
  category_theory.mono f ↔ function.injective f :=
begin
  set f' : (⟨A⟩ : Module ℤ) ⟶ (⟨B⟩ : Module ℤ) :=
  { to_fun := f,
    map_add' := λ x y, by simp only [map_add],
    map_smul' := λ z a, begin
      induction z using int.induction_on with n hn n hn,
      { simp only [ring_hom.id_apply, zero_smul, map_zero], },
      { simp only [add_smul, map_add, one_smul, hn, ring_hom.id_apply], },
      { simp only [sub_smul, map_sub, one_smul, hn, ring_hom.id_apply], },
    end } with f'_eq,
  have iff1 : mono f' ↔ function.injective f' := Module.mono_iff_injective _,
  have iff2 : function.injective f ↔ function.injective f',
  { split,
    { rintros hf a b (eq1 : f a = f b),
      exact hf eq1, },
    { rintros hf' a b (eq1 : f' a = f' b),
      exact hf' eq1, }, },
  have iff3 : mono f ↔ mono f',
  { split,
    { intros m,
      split,
      rintros Z g h eq1,
      set g' : AddCommGroup.of Z ⟶ AddCommGroup.of A := g.to_add_monoid_hom,
      set h' : AddCommGroup.of Z ⟶ AddCommGroup.of A := h.to_add_monoid_hom,
      have eq2 : g' ≫ f = h' ≫ f,
      { ext,
        have := fun_like.congr_fun eq1 x,
        exact this, },
      resetI,
      rw cancel_mono f at eq2,
      ext,
      convert fun_like.congr_fun eq2 x, },
    { intros m,
      split,
      intros Z g h eq1,
      set g' : (Module.mk Z : Module ℤ) ⟶ Module.mk A :=
      { to_fun := g, map_add' := λ _ _, by rw map_add, map_smul' := λ z a,
        begin
          induction z using int.induction_on with n hn n hn,
          { simp only [zero_smul, map_zero, ring_hom.id_apply], },
          { simp only [add_smul, map_add, hn, one_smul, ring_hom.id_apply], },
          { simp only [sub_smul, map_sub, hn, one_smul, ring_hom.id_apply], }
        end },
      set h' : (Module.mk Z : Module ℤ) ⟶ Module.mk A :=
      { to_fun := h, map_add' := λ _ _, by rw map_add, map_smul' := λ z a,
        begin
          induction z using int.induction_on with n hn n hn,
          { simp only [zero_smul, map_zero, ring_hom.id_apply], },
          { simp only [add_smul, map_add, hn, one_smul, ring_hom.id_apply], },
          { simp only [sub_smul, map_sub, hn, one_smul, ring_hom.id_apply], }
        end },
      have eq2 : g' ≫ f' = h' ≫ f',
      { ext,
        convert fun_like.congr_fun eq1 x, },
      resetI,
      rw cancel_mono at eq2,
      ext,
      convert fun_like.congr_fun eq2 x, }, },
  rw [iff3, iff2, iff1],
end

end
