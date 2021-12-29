import algebra.homology.homological_complex
import category_theory.abelian.basic
import algebra.homology.shift
import category_theory.triangulated.basic
import algebra.homology.homotopy_category
import algebra.homology.additive
import category_theory.limits.constructions.finite_products_of_binary_products

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

-- lemma biprod.sub_lift {C : Type*} [category C] [abelian C] {X Y Z : C}
--   (f f' : X ⟶ Y) (g g' : X ⟶ Z) :
--     biprod.lift f g - biprod.lift f' g' = biprod.lift (f - f') (g - g') := by ext; simp

-- lemma biprod.sub_desc {C : Type*} [category C] [abelian C] {X Y Z : C}
--   (f f' : X ⟶ Z) (g g' : Y ⟶ Z) :
--     biprod.desc f g - biprod.desc f' g' = biprod.desc (f - f') (g - g') := by ext; simp

-- -- This times out if they are combined in one proof
-- namespace cone.map_homotopy_of_homotopy
-- variables {i₁' : A ⟶ A'} {i₂' : B ⟶ B'} (h₁ : homotopy i₁ i₁') (h₂ : homotopy i₂ i₂') (i : ℤ)

-- lemma aux1 : biprod.inl ≫ (cone.map ((h₂.comp_left f).symm.trans
--   (comm.trans (h₁.comp_right f')))).f i ≫ biprod.fst =
--   biprod.inl ≫ (cone.d f i (i + 1) ≫ biprod.map (h₁.hom (i + 1 + 1) (i + 1)) (-h₂.hom (i + 1) i) +
--     biprod.map (h₁.hom (i + 1) (i - 1 + 1)) (-h₂.hom i (i - 1)) ≫ cone.d f' (i - 1) i +
--     (cone.map comm).f i) ≫ biprod.fst :=
-- begin
--   suffices : h₁.hom (i + 1) i ≫ A'.d i (i + 1) =
--     h₁.hom (i + 1) (i - 1 + 1) ≫ A'.d (i - 1 + 1) (i + 1),
--   { simpa [cone.d, cone_d, cone.map, h₁.comm, d_next, prev_d,
--       ← add_assoc, ← sub_eq_neg_add, sub_eq_zero] },
--   congr; ring
-- end
-- .
-- lemma aux2 : biprod.inl ≫ (cone.map ((h₂.comp_left f).symm.trans
--   (comm.trans (h₁.comp_right f')))).f i ≫ biprod.snd =
--   biprod.inl ≫ (cone.d f i (i + 1) ≫ biprod.map (h₁.hom (i + 1 + 1) (i + 1)) (-h₂.hom (i + 1) i) +
--     biprod.map (h₁.hom (i + 1) (i - 1 + 1)) (-h₂.hom i (i - 1)) ≫ cone.d f' (i - 1) i +
--     (cone.map comm).f i) ≫ biprod.snd :=
-- begin
--   suffices : comm.hom (i + 1) i + h₁.hom (i + 1) i ≫ f'.f i = h₁.hom (i + 1) (i - 1 + 1) ≫
--     f'.f (i - 1 + 1) ≫ (X_eq_to_iso B' (sub_add_cancel _ _)).hom + comm.hom (i + 1) i,
--   { simpa [cone.d, cone_d, cone.map, d_next, prev_d, add_assoc] },
--   rw [← X_eq_to_iso_f, homotopy.comp_X_eq_to_iso_assoc],
--   exact add_comm _ _
-- end
-- .
-- lemma aux3 : biprod.inr ≫ (cone.map ((h₂.comp_left f).symm.trans
--   (comm.trans (h₁.comp_right f')))).f i ≫ biprod.fst =
--   biprod.inr ≫ (cone.d f i (i + 1) ≫ biprod.map (h₁.hom (i + 1 + 1) (i + 1)) (-h₂.hom (i + 1) i) +
--     biprod.map (h₁.hom (i + 1) (i - 1 + 1)) (-h₂.hom i (i - 1)) ≫ cone.d f' (i - 1) i +
--     (cone.map comm).f i) ≫ biprod.fst :=
-- by { simp [cone.d, cone_d, cone.map, d_next, prev_d] }
-- .
-- lemma aux4 : biprod.inr ≫ (cone.map ((h₂.comp_left f).symm.trans
--   (comm.trans (h₁.comp_right f')))).f i ≫ biprod.snd =
--   biprod.inr ≫ (cone.d f i (i + 1) ≫ biprod.map (h₁.hom (i + 1 + 1) (i + 1)) (-h₂.hom (i + 1) i) +
--     biprod.map (h₁.hom (i + 1) (i - 1 + 1)) (-h₂.hom i (i - 1)) ≫ cone.d f' (i - 1) i +
--     (cone.map comm).f i) ≫ biprod.snd :=
-- by { simp [cone.d, cone_d, cone.map, d_next, prev_d, h₂.comm, ← add_assoc] }
-- .
-- lemma aux : (cone.map ((h₂.comp_left f).symm.trans (comm.trans (h₁.comp_right f')))).f i =
--   cone.d f i (i + 1) ≫ biprod.map (h₁.hom (i + 1 + 1) (i + 1)) (-h₂.hom (i + 1) i) +
--   biprod.map (h₁.hom (i + 1) (i - 1 + 1)) (-h₂.hom i (i - 1)) ≫ cone.d f' (i - 1) i +
--     (cone.map comm).f i :=
-- by { ext; simp_rw category.assoc, apply aux1, apply aux2, apply aux3, apply aux4 }

-- end cone.map_homotopy_of_homotopy

-- def cone.map_homotopy_of_homotopy {i₁' i₂'} (h₁ : homotopy i₁ i₁') (h₂ : homotopy i₂ i₂') :
--   homotopy (cone.map ((h₂.comp_left f).symm.trans $ comm.trans (h₁.comp_right f')))
--     (cone.map comm) :=
-- { hom := λ i j, biprod.map (h₁.hom _ _) (-h₂.hom _ _),
--   comm := λ i, by { simpa [d_next, prev_d] using cone.map_homotopy_of_homotopy.aux comm h₁ h₂ i },
--   zero' := by { introv r, have r' : ¬j + 1 + 1 = i + 1, { simpa using r },
--     ext; simp [h₁.zero _ _ r', h₂.zero _ _ r] } }

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

open_locale zero_object

instance : has_zero_object (cochain_complex V ℤ) := infer_instance

def cone_from_zero (A : cochain_complex V ℤ) : cone (0 : 0 ⟶ A) ≅ A :=
{ hom :=
  { f := λ i, biprod.snd, comm' := by { introv r, ext, dsimp [cone.d] at *, simp [if_pos r] } },
  inv := cone.in _,
  inv_hom_id' := by { intros, ext, dsimp [cone.in], simp } }
.
def cone_to_zero (A : cochain_complex V ℤ) : cone (0 : A ⟶ 0) ≅ A⟦(1 : ℤ)⟧ :=
{ hom := cone.out _,
  inv :=
    { f := λ i, biprod.inl, comm' := by { introv r, ext, dsimp [cone.d] at *, simp [if_pos r] } },
  hom_inv_id' := by { intros, ext, dsimp [cone.out], simp },
  inv_hom_id' := by { intros, ext, dsimp [cone.out], simp } }

def cone.desc_of_null_homotopic (h : homotopy (f ≫ g) 0) : cone f ⟶ C :=
cone.map (h.trans (homotopy.of_eq (comp_zero.symm : 0 = 0 ≫ 0))) ≫ (cone_from_zero _).hom

def cone.lift_of_null_homotopic (h : homotopy (f ≫ g) 0) : A ⟶ cone g⟦(-1 : ℤ)⟧ :=
(shift_shift_neg A (1 : ℤ)).inv ≫ (shift_functor _ (-1 : ℤ)).map ((cone_to_zero _).inv ≫
  cone.map (h.trans (homotopy.of_eq (comp_zero.symm : 0 = 0 ≫ 0))).symm)

@[simps]
def of_termwise_split_mono [H : ∀ i, split_mono (f.f i)] : B ⟶ B' :=
{ f := λ i, i₂.f i - (H i).retraction ≫ comm.hom i (i-1) ≫ B'.d (i-1) i -
    B.d i (i+1) ≫ (H (i+1)).retraction ≫ comm.hom (i+1) i,
  comm' := λ i j (r : i + 1 = j), by { subst r, simp only [d_comp_d, sub_zero, category.assoc,
    comp_zero, preadditive.comp_sub, hom.comm, preadditive.sub_comp, zero_comp, sub_right_inj,
    d_comp_d_assoc], congr; ring } }

@[simp, reassoc]
lemma of_termwise_split_mono_commutes [H : ∀ i, split_mono (f.f i)] :
  f ≫ of_termwise_split_mono comm = i₁ ≫ f' :=
begin
  ext i,
  dsimp,
  have : f.f i ≫ i₂.f i = A.d i (i + 1) ≫ comm.hom (i + 1) i + comm.hom i (i - 1) ≫
    B'.d (i - 1) i + i₁.f i ≫ f'.f i := by simpa [d_next, prev_d] using comm.comm i,
  simp only [hom.comm_assoc, preadditive.comp_sub, this],
  erw [split_mono.id_assoc, split_mono.id_assoc],
  simp [add_right_comm]
end

@[simps]
def of_termwise_split_epi [H : ∀ i, split_epi (f'.f i)] : A ⟶ A' :=
{ f := λ i, i₁.f i + comm.hom i (i-1) ≫ (H (i-1)).section_ ≫ A'.d (i-1) i +
    A.d i (i+1) ≫ comm.hom (i+1) i ≫ (H i).section_,
  comm' := λ i j (r : i + 1 = j), by { subst r, simp only [add_zero, d_comp_d, preadditive.comp_add,
    category.assoc, comp_zero, add_right_inj, hom.comm, zero_comp, preadditive.add_comp,
    d_comp_d_assoc], congr; ring } }

@[simp, reassoc]
lemma of_termwise_split_epi_commutes [H : ∀ i, split_epi (f'.f i)] :
  of_termwise_split_epi comm ≫ f' = f ≫ i₂ :=
begin
  ext i,
  dsimp,
  have : f.f i ≫ i₂.f i = A.d i (i + 1) ≫ comm.hom (i + 1) i + comm.hom i (i - 1) ≫
    B'.d (i - 1) i + i₁.f i ≫ f'.f i := by simpa [d_next, prev_d] using comm.comm i,
  simp only [this, category.assoc, preadditive.add_comp, ← f'.comm],
  erw [split_epi.id, split_epi.id_assoc],
  rw [add_comm, add_comm (i₁.f i ≫ f'.f i), ← add_assoc, category.comp_id]
end
.
section
variables {ι : Type*} {c : complex_shape ι} {X Y Z : homological_complex V c}

@[simps]
def biproduct (X Y : homological_complex V c) : homological_complex V c :=
{ X := λ i, X.X i ⊞ Y.X i,
  d := λ i j, biprod.map (X.d i j) (Y.d i j),
  shape' := λ i j r, by ext; simp [X.shape _ _ r, Y.shape _ _ r] }
.
@[simps] def biproduct.inl : X ⟶ biproduct X Y := { f := λ i, biprod.inl }
@[simps] def biproduct.inr : Y ⟶ biproduct X Y := { f := λ i, biprod.inr }
@[simps] def biproduct.fst : biproduct X Y ⟶ X := { f := λ i, biprod.fst }
@[simps] def biproduct.snd : biproduct X Y ⟶ Y := { f := λ i, biprod.snd }
@[simps] def biproduct.lift (f : X ⟶ Y) (g : X ⟶ Z) : X ⟶ biproduct Y Z :=
{ f := λ i, biprod.lift (f.f i) (g.f i) }
@[simps] def biproduct.desc (f : X ⟶ Z) (g : Y ⟶ Z) : biproduct X Y ⟶ Z :=
{ f := λ i, biprod.desc (f.f i) (g.f i) }
.
variables (X Y)
@[simps]
def biproduct_bicone : binary_bicone X Y :=
{ X := biproduct X Y,
  fst := biproduct.fst,
  snd := biproduct.snd,
  inl := biproduct.inl,
  inr := biproduct.inr }
.
local attribute [tidy] tactic.case_bash

def biproduct_bicone_is_prod : is_limit (biproduct_bicone X Y).to_cone :=
{ lift := λ (Z : binary_fan _ _), biproduct.lift Z.fst Z.snd,
  uniq' := by { intros, delta binary_fan.fst binary_fan.snd, ext; simp [← w] } }
.
def biproduct_bicone_is_coprod : is_colimit (biproduct_bicone X Y).to_cocone :=
{ desc := λ (Z : binary_cofan _ _), biproduct.desc Z.inl Z.inr,
  uniq' := by { intros, delta binary_cofan.inl binary_cofan.inr, ext; simp [← w] } }
.
def biproduct_is_biprod : binary_biproduct_data X Y :=
{ bicone := biproduct_bicone X Y,
  is_limit := biproduct_bicone_is_prod X Y,
  is_colimit := biproduct_bicone_is_coprod X Y }

instance : has_binary_biproducts (cochain_complex V ℤ) :=
⟨λ X Y, ⟨⟨biproduct_is_biprod X Y⟩⟩⟩

instance : has_finite_products (cochain_complex V ℤ) :=
has_finite_products_of_has_binary_and_terminal

end

@[simps]
def termwise_split_mono_lift (f : A ⟶ B) : A ⟶ biproduct B (cone (𝟙 A)) :=
biproduct.lift f (cone.in _)

@[simps]
def termwise_split_mono_desc (f : A ⟶ B) : biproduct B (cone (𝟙 A)) ⟶ B :=
biproduct.fst

@[simps]
def termwise_split_mono_section (f : A ⟶ B) : B ⟶ biproduct B (cone (𝟙 A)) :=
biproduct.inl

@[simp, reassoc] lemma termwise_split_mono_section_desc (f : A ⟶ B) :
  termwise_split_mono_section f ≫ termwise_split_mono_desc f = 𝟙 _ :=
by { ext, simp }
.
lemma termwise_split_mono_desc_section_aux (i : ℤ) :
  𝟙 (B.X i ⊞ (A.X (i + 1) ⊞ A.X i)) = biprod.snd ≫ biprod.desc (𝟙 (A.X (i + 1))) (A.d i (i + 1)) ≫
    biprod.inl ≫ biprod.inr + biprod.snd ≫ biprod.snd ≫
    (X_eq_to_iso A (sub_add_cancel i 1).symm).hom ≫ biprod.inl ≫ biprod.lift
    (biprod.desc (-A.d (i - 1 + 1) (i + 1)) 0) (biprod.desc (X_eq_to_iso A (sub_add_cancel i 1)).hom
    (A.d (i - 1) i)) ≫ biprod.inr + biprod.fst ≫ biprod.inl :=
begin
  ext1; simp only [zero_comp, preadditive.comp_add, zero_add, add_zero, biprod.inr_fst_assoc,
    biprod.inl_fst_assoc, biprod.inl_snd_assoc, biprod.inr_snd_assoc, category.comp_id],
  ext1, { simp },
  ext1, { simp only [add_zero, preadditive.add_comp, comp_zero, biprod.inr_fst, category.assoc] },
  ext1; simp,
end
.
def termwise_split_mono_desc_section (f : A ⟶ B) :
  homotopy (𝟙 _) (termwise_split_mono_desc f ≫ termwise_split_mono_section f) :=
{ hom := λ i j, if h : i = j + 1 then
    biprod.snd ≫ biprod.snd ≫ (A.X_eq_to_iso h).hom ≫ biprod.inl ≫ biprod.inr else 0,
  zero' := λ i j r, dif_neg (ne.symm r),
  comm := λ i, by { dsimp,
    simpa [d_next, prev_d, cone.d] using termwise_split_mono_desc_section_aux i } }


instance (f : A ⟶ B) (i : ℤ) : split_mono ((termwise_split_mono_lift f).f i) :=
{ retraction := biprod.snd ≫ biprod.snd, id' := by simp [cone.in] }



end homological_complex
