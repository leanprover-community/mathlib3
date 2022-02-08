import category_theory.abelian.exact
import category_theory.preadditive.injective_resolution

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory

open category_theory.injective

variables {C : Type u} [category.{v} C]

section

variables [enough_injectives C] [abelian C]

lemma exact_d_f {X Y : C} (f : X ⟶ Y) : exact f (d f) :=
(abelian.exact_iff _ _).2 $
  ⟨by simp, zero_of_comp_mono (ι _) $ by rw [category.assoc, kernel.condition]⟩

end

namespace InjectiveResolution

variables [abelian C] [enough_injectives C]

@[simps]
def of_cocomplex (Z : C) : cochain_complex C ℕ :=
cochain_complex.mk'
  (injective.under Z) (injective.syzygies (injective.ι Z)) (injective.d (injective.ι Z))
  (λ ⟨X, Y, f⟩, ⟨injective.syzygies f, injective.d f, (exact_d_f f).w⟩)

@[irreducible] def of (Z : C) : InjectiveResolution Z :=
{ cocomplex := of_cocomplex Z,
  ι := cochain_complex.mk_hom _ _ (injective.ι Z) 0
    (by { simp only [of_cocomplex_d, eq_self_iff_true, eq_to_hom_refl, category.comp_id,
      dite_eq_ite, if_true, exact.w],
      exact (exact_d_f (injective.ι Z)).w, } ) (λ n _, ⟨0, by ext⟩),
  injective := by { rintros (_|_|_|n); { apply injective.injective_under, } },
  exact₀ := by simpa using exact_d_f (injective.ι Z),
  exact := by { rintros (_|n); { simp, apply exact_d_f } },
  mono := injective.ι_mono Z }

@[priority 100]
instance (Z : C) : has_injective_resolution Z :=
{ out := ⟨of Z⟩ }

@[priority 100]
instance : has_injective_resolutions C :=
{ out := λ _, infer_instance }

end InjectiveResolution

end category_theory
