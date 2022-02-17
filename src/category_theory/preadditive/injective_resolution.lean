import category_theory.preadditive.injective
import algebra.homology.single
import algebra.homology.homological_complex
import algebra.homology.homotopy_category
import category_theory.abelian.exact

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

section
variables (C)

class has_injective_resolutions : Prop :=
(out : ∀ Z : C, has_injective_resolution Z)

attribute [instance, priority 100] has_injective_resolutions.out

end

end

namespace InjectiveResolution

section
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
end

section abelian
variables [abelian C]

def desc_f_one {Y Z : C}
  (f : Z ⟶ Y) (P : InjectiveResolution Y) (Q : InjectiveResolution Z) :
  Q.cocomplex.X 1 ⟶ P.cocomplex.X 1 :=
exact.desc (desc_f_zero f P Q ≫ P.cocomplex.d 0 1) (Q.ι.f 0) (Q.cocomplex.d 0 1)
  (by simp [←category.assoc, desc_f_zero])

@[simp] lemma desc_f_one_zero_comm {Y Z : C}
  (f : Z ⟶ Y) (P : InjectiveResolution Y) (Q : InjectiveResolution Z) :
  Q.cocomplex.d 0 1 ≫ desc_f_one f P Q = desc_f_zero f P Q ≫ P.cocomplex.d 0 1 :=
begin
  dsimp only [desc_f_zero, desc_f_one],
  simp only [exact.desc_comp],
end

def desc_f_succ {Y Z : C}
  (f : Z ⟶ Y) (P : InjectiveResolution Y) (Q : InjectiveResolution Z)
  (n : ℕ) (g : Q.cocomplex.X n ⟶ P.cocomplex.X n) (g' : Q.cocomplex.X (n+1) ⟶ P.cocomplex.X (n+1))
  (w : Q.cocomplex.d n (n+1) ≫ g' = g ≫ P.cocomplex.d n (n+1)) :
  Σ' g'' : Q.cocomplex.X (n+2) ⟶ P.cocomplex.X (n+2),
    Q.cocomplex.d (n+1) (n+2) ≫ g'' = g' ≫ P.cocomplex.d (n+1) (n+2) :=
⟨@exact.desc C _ _ _ _ _ _ _ _ _
  (g' ≫ P.cocomplex.d (n+1) (n+2))
  (Q.cocomplex.d n (n+1))
  (Q.cocomplex.d (n+1) (n+2)) _
  (by simp [←category.assoc, w]), (by simp)⟩

def desc {Y Z : C}
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
lemma desc_commutes {Y Z : C}
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

def desc_homotopy_zero_zero {Y Z : C} {P : InjectiveResolution Y} {Q : InjectiveResolution Z}
  (f : P.cocomplex ⟶ Q.cocomplex)
  (comm : P.ι ≫ f = 0) : P.cocomplex.X 1 ⟶ Q.cocomplex.X 0 :=
exact.desc (f.f 0) (P.ι.f 0) (P.cocomplex.d 0 1)
  (congr_fun (congr_arg homological_complex.hom.f comm) 0)

def desc_homotopy_zero_one {Y Z : C} {P : InjectiveResolution Y} {Q : InjectiveResolution Z}
  (f : P.cocomplex ⟶ Q.cocomplex)
  (comm : P.ι ≫ f = (0 : _ ⟶ Q.cocomplex)) : P.cocomplex.X 2 ⟶ Q.cocomplex.X 1 :=
exact.desc (f.f 1 - desc_homotopy_zero_zero f comm ≫ Q.cocomplex.d 0 1)
  (P.cocomplex.d 0 1) (P.cocomplex.d 1 2)
  (begin
    simp only [desc_homotopy_zero_zero, ←category.assoc, preadditive.comp_sub, exact.desc_comp, homological_complex.hom.comm, sub_self],
  end)

def desc_homotopy_zero_succ {Y Z : C} {P : InjectiveResolution Y} {Q : InjectiveResolution Z}
  (f : P.cocomplex ⟶ Q.cocomplex) (n : ℕ)
  (g : P.cocomplex.X (n + 1) ⟶ Q.cocomplex.X n)
  (g' : P.cocomplex.X (n + 2) ⟶ Q.cocomplex.X (n + 1))
  (w : f.f (n + 1) = P.cocomplex.d (n+1) (n+2) ≫ g' + g ≫ Q.cocomplex.d n (n+1)) :
  P.cocomplex.X (n + 3) ⟶ Q.cocomplex.X (n + 2) :=
exact.desc (f.f (n+2) - g' ≫ Q.cocomplex.d _ _) (P.cocomplex.d (n+1) (n+2)) (P.cocomplex.d (n+2) (n+3))
  begin
    have w' : f.f (n + 1) - g ≫ Q.cocomplex.d n (n+1)= P.cocomplex.d (n+1) (n+2) ≫ g',
    { rw w, simp only [add_sub_cancel], },
    simp [preadditive.comp_sub, ←category.assoc, ←w', preadditive.sub_comp],
  end

def desc_homotopy_zero {Y Z : C} {P : InjectiveResolution Y} {Q : InjectiveResolution Z}
  (f : P.cocomplex ⟶ Q.cocomplex)
  (comm : P.ι ≫ f = 0) :
  homotopy f 0 :=
begin
  fapply homotopy.mk_coinductive,
  { exact desc_homotopy_zero_zero f comm, },
  { simp [desc_homotopy_zero_zero], },
  { exact desc_homotopy_zero_one f comm, },
  { simp [desc_homotopy_zero_one], },
  { rintro n ⟨g, g', w⟩,
    fsplit,
    { refine desc_homotopy_zero_succ f n g g' _,
      simp only [w, add_comm], },
    { simp [desc_homotopy_zero_succ, w], }, }
end

def desc_homotopy {Y Z : C} (f : Y ⟶ Z) {P : InjectiveResolution Y} {Q : InjectiveResolution Z}
  (g h : P.cocomplex ⟶ Q.cocomplex)
  (g_comm : P.ι ≫ g = (cochain_complex.single₀ C).map f ≫ Q.ι)
  (h_comm : P.ι ≫ h = (cochain_complex.single₀ C).map f ≫ Q.ι) :
  homotopy g h :=
begin
  apply homotopy.equiv_sub_zero.inv_fun,
  apply desc_homotopy_zero,
  simp [g_comm, h_comm],
end

def desc_id_homotopy (X : C) (P : InjectiveResolution X) :
  homotopy (desc (𝟙 X) P P) (𝟙 P.cocomplex) :=
by { apply desc_homotopy (𝟙 X); simp, }

def desc_comp_homotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  (P : InjectiveResolution X) (Q : InjectiveResolution Y) (R : InjectiveResolution Z) :
  homotopy (desc (f ≫ g) R P) (desc f Q P ≫ desc g R Q)  :=
by { apply desc_homotopy (f ≫ g); simp, }

attribute [irreducible] desc_homotopy_zero desc_homotopy desc_id_homotopy desc_comp_homotopy

def homotopy_equiv {X : C} (P Q : InjectiveResolution X) :
  homotopy_equiv P.cocomplex Q.cocomplex :=
{ hom := desc (𝟙 X) Q P,
  inv := desc (𝟙 X) P Q,
  homotopy_hom_inv_id := begin
    refine (desc_comp_homotopy (𝟙 X) (𝟙 X) P Q P).symm.trans _,
    simp [category.id_comp],
    apply desc_id_homotopy,
  end,
  homotopy_inv_hom_id := begin
    refine (desc_comp_homotopy (𝟙 X) (𝟙 X) Q P Q).symm.trans _,
    simp [category.id_comp],
    apply desc_id_homotopy,
  end, }

@[simp, reassoc] lemma homotopy_equiv_hom_π {X : C} (P Q : InjectiveResolution X) :
  P.ι ≫ (homotopy_equiv P Q).hom = Q.ι :=
by simp [homotopy_equiv]

@[simp, reassoc] lemma homotopy_equiv_inv_π {X : C} (P Q : InjectiveResolution X) :
  Q.ι ≫ (homotopy_equiv P Q).inv = P.ι :=
by simp [homotopy_equiv]

end abelian

end InjectiveResolution

section

variables [abelian C]

/-- An arbitrarily chosen projective resolution of an object. -/
abbreviation injective_resolution (Z : C) [has_injective_resolution Z] : cochain_complex C ℕ :=
(has_injective_resolution.out Z).some.cocomplex

abbreviation injective_resolution.ι (Z : C) [has_injective_resolution Z] :
  (cochain_complex.single₀ C).obj Z ⟶ injective_resolution Z :=
(has_injective_resolution.out Z).some.ι

abbreviation injective_resolution.desc {X Y : C} (f : Y ⟶ X)
  [has_injective_resolution X] [has_injective_resolution Y] :
  injective_resolution Y ⟶ injective_resolution X :=
InjectiveResolution.desc f _ _

end

variables (C) [abelian C] [has_injective_resolutions C]

/--
Taking projective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed chain complexes and chain maps up to homotopy).
-/
def injective_resolutions : C ⥤ homotopy_category C (complex_shape.up ℕ) :=
{ obj := λ X, (homotopy_category.quotient _ _).obj (injective_resolution X),
  map := λ X Y f, (homotopy_category.quotient _ _).map (injective_resolution.desc f),
  map_id' := λ X, begin
    rw ←(homotopy_category.quotient _ _).map_id,
    apply homotopy_category.eq_of_homotopy,
    apply InjectiveResolution.desc_id_homotopy,
  end,
  map_comp' := λ X Y Z f g, begin
    rw ←(homotopy_category.quotient _ _).map_comp,
    apply homotopy_category.eq_of_homotopy,
    apply InjectiveResolution.desc_comp_homotopy,
  end, }

end category_theory
