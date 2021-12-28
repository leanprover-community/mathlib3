import algebra.homology.homological_complex
import category_theory.abelian.basic
import algebra.homology.shift
import category_theory.triangulated.basic
import algebra.homology.homotopy_category
import algebra.homology.additive

noncomputable theory

universes v u

open_locale classical

open category_theory category_theory.limits

namespace homological_complex

variables {V : Type u} [category.{v} V] [abelian V]
variables (A B : cochain_complex V ℤ) (f : A ⟶ B)

@[simp, reassoc]
lemma homotopy.comp_X_eq_to_iso {X Y : cochain_complex V ℤ} {f g : X ⟶ Y} (h : homotopy f g)
  (i : ℤ) {j k : ℤ} (e : j = k) : h.hom i j ≫ (Y.X_eq_to_iso e).hom = h.hom i k :=
by { subst e, simp }

@[simp, reassoc]
lemma homotopy.X_eq_to_iso_comp {X Y : cochain_complex V ℤ} {f g : X ⟶ Y} (h : homotopy f g)
  {i j : ℤ} (e : i = j) (k : ℤ) : (X.X_eq_to_iso e).hom ≫ h.hom j k = h.hom i k :=
by { subst e, simp }


def cone.X : ℤ → V := λ i, A.X (i + 1) ⊞ B.X i

variables {A B}

def cone.d : Π (i j : ℤ), cone.X A B i ⟶ cone.X A B j :=
λ i j, if hij : i + 1 = j then biprod.lift
  (biprod.desc (-A.d _ _)                         0        )
  (biprod.desc (f.f _ ≫ (B.X_eq_to_iso hij).hom) (B.d _ _))
else 0

/-- The mapping cone of a morphism `f : A → B` of homological complexes. -/
def cone : cochain_complex V ℤ :=
{ X := cone.X A B,
  d := cone.d f,
  shape' := λ i j hij, dif_neg hij,
  d_comp_d' := λ i j k (hij : _ = _) (hjk : _ = _),
  begin
    substs hij hjk,
    ext; simp [cone.d],
  end }
.

@[simp]
lemma cone_X (i : ℤ) : (cone f).X i = (A.X (i + 1) ⊞ B.X i) := rfl

@[simp]
lemma cone_d : (cone f).d = cone.d f := rfl

def cone.in : B ⟶ cone f :=
{ f := λ i, biprod.inr,
  comm' := λ i j hij,
  begin
    dsimp [cone_d, cone.d], dsimp at hij, rw [dif_pos hij],
    ext;
    simp only [comp_zero, category.assoc, category.comp_id,
      biprod.inr_desc, biprod.inr_fst, biprod.lift_fst, biprod.inr_snd, biprod.lift_snd],
  end }
.
local attribute [instance] endofunctor_monoidal_category discrete.add_monoidal

def cone.out : cone f ⟶ A⟦(1 : ℤ)⟧ :=
{ f := λ i, biprod.fst,
  comm' := λ i j (hij : _ = _),
  begin
    subst hij,
    dsimp [cone_d, cone.d],
    ext; simp,
  end }

@[simps]
def cone.triangle : triangulated.triangle (cochain_complex V ℤ) :=
{ obj₁ := A,
  obj₂ := B,
  obj₃ := cone f,
  mor₁ := f,
  mor₂ := cone.in f,
  mor₃ := cone.out f }

@[simps]
def cone.triangleₕ : triangulated.triangle (homotopy_category V (complex_shape.up ℤ)) :=
{ obj₁ := ⟨A⟩,
  obj₂ := ⟨B⟩,
  obj₃ := ⟨cone f⟩,
  mor₁ := (homotopy_category.quotient _ _).map f,
  mor₂ := (homotopy_category.quotient _ _).map $ cone.in f,
  mor₃ := (homotopy_category.quotient _ _).map $ cone.out f }

variables {f} {A' B' : cochain_complex V ℤ} {f' : A' ⟶ B'} {i₁ : A ⟶ A'} {i₂ : B ⟶ B'}
variables (comm : homotopy (f ≫ i₂) (i₁ ≫ f'))

include comm

def cone.map : cone f ⟶ cone f' :=
{ f := λ i, biprod.lift
  (biprod.desc (i₁.f _) 0)
  (biprod.desc (comm.hom _ _) (i₂.f _)),
  comm' := λ i j r,
  begin
    change i+1 = j at r,
    dsimp [cone_d, cone.d],
    simp_rw dif_pos r,
    ext,
    { simp },
    { simp only [biprod.lift_desc, X_eq_to_iso_f, biprod.lift_snd, preadditive.comp_add,
        biprod.inl_desc_assoc, category.assoc, preadditive.neg_comp],
      have := comm.comm (i+1),
      dsimp at this,
      rw [reassoc_of this],
      subst r,
      simp only [category.comp_id, ← add_assoc, category.assoc,
        X_eq_to_iso_refl, preadditive.add_comp],
      simpa [d_next, prev_d] using add_comm _ _ },
    { simp },
    { simp }
  end }

@[simp, reassoc]
lemma cone.in_map : cone.in f ≫ cone.map comm = i₂ ≫ cone.in f' :=
by ext; { dsimp [cone.map, cone.in], simp }
.
@[simp, reassoc]
lemma cone.map_out : cone.map comm ≫ cone.out f' = cone.out f ≫ i₁⟦(1 : ℤ)⟧' :=
by ext; { dsimp [cone.map, cone.out], simp }
.

omit comm

lemma biprod.sub_lift {C : Type*} [category C] [abelian C] {X Y Z : C}
  (f f' : X ⟶ Y) (g g' : X ⟶ Z) :
    biprod.lift f g - biprod.lift f' g' = biprod.lift (f - f') (g - g') := by ext; simp

lemma biprod.sub_desc {C : Type*} [category C] [abelian C] {X Y Z : C}
  (f f' : X ⟶ Z) (g g' : Y ⟶ Z) :
    biprod.desc f g - biprod.desc f' g' = biprod.desc (f - f') (g - g') := by ext; simp

-- This times out if they are combined in one proof
namespace cone.map_homotopy_of_homotopy
variables {i₁' : A ⟶ A'} {i₂' : B ⟶ B'} (h₁ : homotopy i₁ i₁') (h₂ : homotopy i₂ i₂') (i : ℤ)

lemma aux1 : biprod.inl ≫ (cone.map ((h₂.comp_left f).symm.trans
  (comm.trans (h₁.comp_right f')))).f i ≫ biprod.fst =
  biprod.inl ≫ (cone.d f i (i + 1) ≫ biprod.map (h₁.hom (i + 1 + 1) (i + 1)) (-h₂.hom (i + 1) i) +
    biprod.map (h₁.hom (i + 1) (i - 1 + 1)) (-h₂.hom i (i - 1)) ≫ cone.d f' (i - 1) i +
    (cone.map comm).f i) ≫ biprod.fst :=
begin
  suffices : h₁.hom (i + 1) i ≫ A'.d i (i + 1) =
    h₁.hom (i + 1) (i - 1 + 1) ≫ A'.d (i - 1 + 1) (i + 1),
  { simpa [cone.d, cone_d, cone.map, h₁.comm, d_next, prev_d,
      ← add_assoc, ← sub_eq_neg_add, sub_eq_zero] },
  congr; ring
end
.
lemma aux2 : biprod.inl ≫ (cone.map ((h₂.comp_left f).symm.trans
  (comm.trans (h₁.comp_right f')))).f i ≫ biprod.snd =
  biprod.inl ≫ (cone.d f i (i + 1) ≫ biprod.map (h₁.hom (i + 1 + 1) (i + 1)) (-h₂.hom (i + 1) i) +
    biprod.map (h₁.hom (i + 1) (i - 1 + 1)) (-h₂.hom i (i - 1)) ≫ cone.d f' (i - 1) i +
    (cone.map comm).f i) ≫ biprod.snd :=
begin
  suffices : comm.hom (i + 1) i + h₁.hom (i + 1) i ≫ f'.f i = h₁.hom (i + 1) (i - 1 + 1) ≫
    f'.f (i - 1 + 1) ≫ (X_eq_to_iso B' (sub_add_cancel _ _)).hom + comm.hom (i + 1) i,
  { simpa [cone.d, cone_d, cone.map, d_next, prev_d, add_assoc] },
  rw [← X_eq_to_iso_f, homotopy.comp_X_eq_to_iso_assoc],
  exact add_comm _ _
end
.
lemma aux3 : biprod.inr ≫ (cone.map ((h₂.comp_left f).symm.trans
  (comm.trans (h₁.comp_right f')))).f i ≫ biprod.fst =
  biprod.inr ≫ (cone.d f i (i + 1) ≫ biprod.map (h₁.hom (i + 1 + 1) (i + 1)) (-h₂.hom (i + 1) i) +
    biprod.map (h₁.hom (i + 1) (i - 1 + 1)) (-h₂.hom i (i - 1)) ≫ cone.d f' (i - 1) i +
    (cone.map comm).f i) ≫ biprod.fst :=
by { simp [cone.d, cone_d, cone.map, d_next, prev_d] }
.
lemma aux4 : biprod.inr ≫ (cone.map ((h₂.comp_left f).symm.trans
  (comm.trans (h₁.comp_right f')))).f i ≫ biprod.snd =
  biprod.inr ≫ (cone.d f i (i + 1) ≫ biprod.map (h₁.hom (i + 1 + 1) (i + 1)) (-h₂.hom (i + 1) i) +
    biprod.map (h₁.hom (i + 1) (i - 1 + 1)) (-h₂.hom i (i - 1)) ≫ cone.d f' (i - 1) i +
    (cone.map comm).f i) ≫ biprod.snd :=
by { simp [cone.d, cone_d, cone.map, d_next, prev_d, h₂.comm, ← add_assoc] }
.
lemma aux : (cone.map ((h₂.comp_left f).symm.trans (comm.trans (h₁.comp_right f')))).f i =
  cone.d f i (i + 1) ≫ biprod.map (h₁.hom (i + 1 + 1) (i + 1)) (-h₂.hom (i + 1) i) +
  biprod.map (h₁.hom (i + 1) (i - 1 + 1)) (-h₂.hom i (i - 1)) ≫ cone.d f' (i - 1) i +
    (cone.map comm).f i :=
by { ext; simp_rw category.assoc, apply aux1, apply aux2, apply aux3, apply aux4 }

end cone.map_homotopy_of_homotopy

def cone.map_homotopy_of_homotopy {i₁' i₂'} (h₁ : homotopy i₁ i₁') (h₂ : homotopy i₂ i₂') :
  homotopy (cone.map ((h₂.comp_left f).symm.trans $ comm.trans (h₁.comp_right f')))
    (cone.map comm) :=
{ hom := λ i j, biprod.map (h₁.hom _ _) (-h₂.hom _ _),
  comm := λ i, by { simpa [d_next, prev_d] using cone.map_homotopy_of_homotopy.aux comm h₁ h₂ i },
  zero' := by { introv r, have r' : ¬j + 1 + 1 = i + 1, { simpa using r },
    ext; simp [h₁.zero _ _ r', h₂.zero _ _ r] } }

-- I suppose this is not true?
def cone.map_homotopy_of_homotopy' (comm' : homotopy (f ≫ i₂) (i₁ ≫ f')) :
  homotopy (cone.map comm) (cone.map comm') := sorry

@[simps]
def cone.triangleₕ_map : cone.triangleₕ f ⟶ cone.triangleₕ f' :=
{ hom₁ := (homotopy_category.quotient _ _).map i₁,
  hom₂ := (homotopy_category.quotient _ _).map i₂,
  hom₃ := (homotopy_category.quotient _ _).map $ cone.map comm,
  comm₁' := by { dsimp [cone.triangleₕ], simp_rw ← functor.map_comp,
    exact homotopy_category.eq_of_homotopy _ _ comm },
  comm₂' := by { dsimp [cone.triangleₕ], simp_rw ← functor.map_comp, simp },
  comm₃' := by { dsimp [cone.triangleₕ], simp_rw ← functor.map_comp, simp } }
.

@[simps]
def cone.triangle_map (h : f ≫ i₂ = i₁ ≫ f') : cone.triangle f ⟶ cone.triangle f' :=
{ hom₁ := i₁,
  hom₂ := i₂,
  hom₃ := cone.map (homotopy.of_eq h),
  comm₁' := by simpa [cone.triangle],
  comm₂' := by { dsimp [cone.triangle], simp },
  comm₃' := by { dsimp [cone.triangle], simp } }
.
@[simp]
lemma cone.map_id (f : A ⟶ B) :
  cone.map (homotopy.of_eq $ (category.comp_id f).trans (category.id_comp f).symm) = 𝟙 _ :=
by { ext; dsimp [cone.map, cone, cone.X]; simp }
.
@[simp]
lemma cone.triangle_map_id (f : A ⟶ B) :
  cone.triangle_map ((category.comp_id f).trans (category.id_comp f).symm) = 𝟙 _ :=
by { ext; dsimp [cone.map, cone, cone.X]; simp }
.

def cone.triangle_functorial :
  arrow (cochain_complex V ℤ) ⥤ triangulated.triangle (cochain_complex V ℤ) :=
{ obj := λ f, cone.triangle f.hom,
  map := λ f g c, cone.triangle_map c.w.symm,
  map_id' := λ X, cone.triangle_map_id _,
  map_comp' := λ X Y Z f g, by { ext; dsimp [cone.map, cone, cone.X]; simp } }
.

-- I suppose this is also not true?
def cone.triangleₕ_functorial :
  arrow (homotopy_category V (complex_shape.up ℤ)) ⥤
    triangulated.triangle (homotopy_category V (complex_shape.up ℤ)) :=
{ obj := λ f, cone.triangleₕ f.hom.out,
  map := λ f g c, @cone.triangleₕ_map _ _ _ _ _ _ _ _ _ c.left.out c.right.out
  begin
    refine homotopy_category.homotopy_of_eq _ _ _,
    simpa [-arrow.w] using c.w.symm
  end,
  map_id' := sorry,
  map_comp' := sorry }
.
variables {C : cochain_complex V ℤ} (g : B ⟶ C)

instance : preadditive (cochain_complex V ℤ) := {}

def cone.desc_of_null_homotopic (h : homotopy (f ≫ g) 0) : cone f ⟶ C :=
{ f := λ i, by { have := h.trans (homotopy.of_eq (show (0 : A ⟶ C) = (0 : A ⟶ 0) ≫ 0, by { })), }

}


end homological_complex
