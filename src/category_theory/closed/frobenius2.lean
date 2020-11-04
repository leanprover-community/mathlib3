import category_theory.adjunction.limits
import category_theory.closed.cartesian
import category_theory.conj
import logic.basic

universes v₁ v₂ u₁ u₂

namespace category_theory
namespace monoidal

open category limits

variables {C : Type u₁} [category.{v₁} C] [has_finite_products C] [cartesian_closed C]
variables {D : Type u₂} [category.{v₂} D] [has_finite_products D] [cartesian_closed D]
variables (fb : D ⥤ C) (fs : C ⥤ D) (adj : fb ⊣ fs)

namespace frobenius_internal

def phis : Type (max u₁ v₂) :=
{ φ : Π (A B : C), fs.obj (A ⟹ B) ⟶ fs.obj A ⟹ fs.obj B //
  (∀ (A A' B : C) (f : A ⟶ A'), φ A' B ≫ pre _ (fs.map f) = fs.map (pre _ f) ≫ φ A B) ∧
  (∀ (A B B' : C) (g : B ⟶ B'), φ A B ≫ (exp _).map (fs.map g) = fs.map ((exp _).map g) ≫ φ A B') }

def phis2 :=
{ q : Π (A B c), (c ⟶ fs.obj (A ⟹ B)) → (c ⟶ fs.obj A ⟹ fs.obj B) //
  (∀ A B c c' (h : c ⟶ c') t, h ≫ q A B c' t = q A B c (h ≫ t)) ∧
  (∀ A A' B (f : A ⟶ A') c t, q A' B c t ≫ pre _ (fs.map f) = q A B c (t ≫ fs.map (pre _ f))) ∧
  (∀ A B B' (g : B ⟶ B') c t, q A B c t ≫ (exp _).map (fs.map g) = q A B' c (t ≫ fs.map ((exp _).map g))) }

lemma eq_iff_comp_right_eq {Y Z : C} (f g : Y ⟶ Z) :
  (∀ (X : C) (h : X ⟶ Y), h ≫ f = h ≫ g) ↔ f = g :=
⟨eq_of_comp_right_eq, λ t X h, t ▸ rfl⟩

noncomputable def equiv12 : phis fs ≃ phis2 fs :=
begin
  apply equiv.trans _ (equiv.subtype_subtype_equiv_subtype_inter _ _),
  apply equiv.subtype_congr _ _,
  { refine ⟨λ q, ⟨λ A B c t, t ≫ q _ _, λ A B c c' h t, by simp⟩, λ q A B, q.1 A B _ (𝟙 _), _, _⟩,
    { intros q,
      ext A B,
      simp },
    { rintro ⟨q, hq⟩,
      ext,
      simp [hq] } },
  intros q,
  dsimp,
  simp_rw [assoc],
  apply and_congr,
  { apply forall₄_congr,
    intro A,
    apply forall_congr,
    intro A',
    apply forall_congr,
    intro B,
    apply forall_congr,
    intro f,
    simp_rw [eq_iff_comp_right_eq] },
  { apply forall_congr,
    intro A,
    apply forall_congr,
    intro A',
    apply forall_congr,
    intro B,
    apply forall_congr,
    intro f,
    rw eq_iff_comp_right_eq }
end

def phis3 :=
{ q : Π (A B c), (fb.obj c ⟶ (A ⟹ B)) → (fs.obj A ⨯ c ⟶ fs.obj B) //
  (∀ A B c c' (h : c ⟶ c') t, limits.prod.map (𝟙 _) h ≫ q A B c' t = q A B c (fb.map h ≫ t)) ∧
  (∀ A A' B (f : A ⟶ A') c t, limits.prod.map (fs.map f) (𝟙 _) ≫ q A' B c t = q A B c (t ≫ pre _ f)) ∧
  (∀ A B B' (g : B ⟶ B') c t, q A B c t ≫ fs.map g = q A B' c (t ≫ (exp A).map g)) }

noncomputable def equiv12 (adj : fb ⊣ fs) : phis2 fs ≃ phis3 fb fs :=
begin
  -- apply equiv.trans _ (equiv.subtype_subtype_equiv_subtype_inter _ _),
  apply equiv.subtype_congr _ _,
  { apply equiv.Pi_congr_right,
    intro A,
    apply equiv.Pi_congr_right,
    intro B,
    apply equiv.Pi_congr_right,
    intro c,
    apply equiv.arrow_congr,
    { apply (adj.hom_equiv _ _).symm },
    { apply ((exp.adjunction _).hom_equiv _ _).symm } },
  { intro q,
    apply and_congr,
    { dsimp [equiv.Pi_congr_right],
      simp_rw [← uncurry_natural_left, ← uncurry.injective_iff, equiv.symm_symm,
               adjunction.hom_equiv_naturality_left],


      split,
      { intros hq A B c c' h t,
        dsimp [equiv.Pi_congr_right],
        rw [← uncurry_natural_left, hq],
        simp },
      { intros hq A B c c' h t,
        specialize hq A B c c' h ((adj.hom_equiv c' ((exp A).obj B)).symm t),
        dsimp [equiv.Pi_congr_right] at hq,
        simp only [equiv.symm_symm, adjunction.hom_equiv_naturality_left, equiv.apply_symm_apply] at hq,
        erw ← (exp.adjunction _).hom_equiv_naturality_left_symm at hq,
        apply ((exp.adjunction (fs.obj A)).hom_equiv c (fs.obj B)).symm.injective hq } },
    apply and_congr,
    { dsimp [equiv.Pi_congr_right],
      simp only [equiv.symm_symm],
      -- change _ ↔ ∀ (A A' B : C) (f : A ⟶ A') (c : D) (t : _),
      --            limits.prod.map _ (𝟙 _) ≫ cartesian_closed.uncurry _ = cartesian_closed.uncurry _,


      -- conv_rhs in ( _) {},

    },
    {

    }

  }

end


end frobenius_internal

end monoidal
end category_theory
