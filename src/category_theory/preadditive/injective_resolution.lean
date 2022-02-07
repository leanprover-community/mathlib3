import category_theory.preadditive.injective
import algebra.homology.single
import algebra.homology.homotopy_category

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

open injective

section
variables [has_zero_object C] [has_zero_morphisms C] [has_equalizers C] [has_images C]

@[nolint has_inhabited_instance]
structure InjectiveResolution (Z : C) :=
(cocomplex : cochain_complex C ℕ)
(ι: ((cochain_complex.single₀ C).obj Z) ⟶ cocomplex)
(injective : ∀ n, injective (cocomplex.X n) . tactic.apply_instance)
(exact₀ : exact (ι.f 0) (cocomplex.d 0 1) . tactic.apply_instance)
(exact : ∀ n, exact (cocomplex.d n (n+1)) (cocomplex.d (n+1) (n+2)) . tactic.apply_instance)
(mono : mono (ι.f 0) . tactic.apply_instance)

attribute [instance] InjectiveResolution.injective InjectiveResolution.exact₀
  InjectiveResolution.exact InjectiveResolution.mono

class has_injective_resolution (Z : C) : Prop :=
(out [] : nonempty (InjectiveResolution Z))

end

section
variables (C) [has_zero_object C] [has_zero_morphisms C] [has_equalizers C] [has_images C]

/--
You will rarely use this typeclass directly: it is implied by the combination
`[enough_projectives C]` and `[abelian C]`.
By itself it's enough to set up the basic theory of derived functors.
-/
class has_injective_resolutions : Prop :=
(out : ∀ Z : C, has_injective_resolution Z)

attribute [instance, priority 100] has_injective_resolutions.out

end

namespace InjectiveResolution
variables [has_zero_object C] [has_zero_morphisms C] [has_equalizers C] [has_images C]

@[simp] lemma ι_f_succ {Z : C} (P : InjectiveResolution Z) (n : ℕ) :
  P.ι.f (n+1) = 0 :=
begin
  apply zero_of_source_iso_zero,
  dsimp, refl,
end

instance {Z : C} (P : InjectiveResolution Z) (n : ℕ) : category_theory.mono (P.ι.f n) :=
by cases n; apply_instance

def self (Z : C) [category_theory.injective Z] : InjectiveResolution Z :=
{ cocomplex := (cochain_complex.single₀ C).obj Z,
  ι := 𝟙 ((cochain_complex.single₀ C).obj Z),
  injective := λ n, begin
    cases n;
    { dsimp, apply_instance },
  end,
  exact₀ := by { dsimp, apply_instance },
  exact := λ n, by { dsimp, apply_instance, },
  mono := by { dsimp, apply_instance, }, }

def desc_f_zero {Y Z : C} (f : Z ⟶ Y) (P : InjectiveResolution Y) (Q : InjectiveResolution Z) :
  Q.cocomplex.X 0 ⟶ P.cocomplex.X 0 :=
factor_of (f ≫ P.ι.f 0) (Q.ι.f 0)

def desc_f_one [has_equalizers Cᵒᵖ] [has_images Cᵒᵖ] {Y Z : C}
  (f : Z ⟶ Y) (P : InjectiveResolution Y) (Q : InjectiveResolution Z) :
  Q.cocomplex.X 1 ⟶ P.cocomplex.X 1 :=
exact.desc (desc_f_zero f P Q ≫ P.cocomplex.d 0 1) (Q.ι.f 0) (Q.cocomplex.d 0 1)
  (by simp [←category.assoc, desc_f_zero])

@[simp] lemma desc_f_one_zero_comm [has_equalizers Cᵒᵖ] [has_images Cᵒᵖ] {Y Z : C}
  (f : Z ⟶ Y) (P : InjectiveResolution Y) (Q : InjectiveResolution Z) :
  Q.cocomplex.d 0 1 ≫ desc_f_one f P Q = desc_f_zero f P Q ≫ P.cocomplex.d 0 1 :=
begin
  dsimp only [desc_f_zero, desc_f_one],
  simp only [exact.desc_comp],
end

def desc_f_succ [has_equalizers Cᵒᵖ] [has_images Cᵒᵖ] {Y Z : C}
  (f : Z ⟶ Y) (P : InjectiveResolution Y) (Q : InjectiveResolution Z)
  (n : ℕ) (g : Q.cocomplex.X n ⟶ P.cocomplex.X n) (g' : Q.cocomplex.X (n+1) ⟶ P.cocomplex.X (n+1))
  (w : Q.cocomplex.d n (n+1) ≫ g' = g ≫ P.cocomplex.d n (n+1)) :
  Σ' g'' : Q.cocomplex.X (n+2) ⟶ P.cocomplex.X (n+2),
    Q.cocomplex.d (n+1) (n+2) ≫ g'' = g' ≫ P.cocomplex.d (n+1) (n+2):=
⟨exact.desc (g' ≫ P.cocomplex.d (n+1) (n+2)) (Q.cocomplex.d n (n+1)) (Q.cocomplex.d (n+1) (n+2))
  (by simp [←category.assoc, w]), (by simp)⟩

def desc [has_equalizers Cᵒᵖ] [has_images Cᵒᵖ] {Y Z : C}
  (f : Z ⟶ Y) (P : InjectiveResolution Y) (Q : InjectiveResolution Z) :
  Q.cocomplex ⟶ P.cocomplex :=
begin
  fapply cochain_complex.mk_hom,
  apply desc_f_zero f,
  apply desc_f_one f,
  symmetry,
  apply desc_f_one_zero_comm f,
  rintro n ⟨g, g', w⟩,
  obtain ⟨g'', eq1⟩ := desc_f_succ f P Q n g g' w.symm,
  refine ⟨g'', eq1.symm⟩,
end

@[simp, reassoc]
lemma desc_commutes [has_equalizers Cᵒᵖ] [has_images Cᵒᵖ] {Y Z : C}
  (f : Z ⟶ Y) (P : InjectiveResolution Y) (Q : InjectiveResolution Z) :
  Q.ι ≫ desc f P Q = (cochain_complex.single₀ C).map f ≫ P.ι :=
begin
  ext n,
  rcases n with (_|_|n),
  { dsimp [desc, desc_f_zero], simp, },
  { dsimp [desc, desc_f_one], simp, },
  { dsimp, simp, },
end

attribute [irreducible] desc

end InjectiveResolution

end category_theory
