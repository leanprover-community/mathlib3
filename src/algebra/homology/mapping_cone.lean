import algebra.homology.homological_complex
import category_theory.abelian.basic
import algebra.homology.shift
import category_theory.triangulated.basic
import algebra.homology.homotopy_category

noncomputable theory

universes v u

open_locale classical

open category_theory category_theory.limits

namespace homological_complex

variables {V : Type u} [category.{v} V] [abelian V]
variables (A B : cochain_complex V ℤ) (f : A ⟶ B)

-- -- move this
-- @[simp, reassoc] lemma d_comp_d_from (i j : β) : A.d i j ≫ A.d_from j = 0 :=
-- begin
--   rcases h₁ : (complex_shape.up' (ι 1)).next j with _ | ⟨k,w₁⟩,
--   { rw [d_from_eq_zero _ h₁, comp_zero], },
--   { rw [d_from_eq _ w₁, d_comp_d_assoc, zero_comp], },
-- end

-- -- move this
-- @[simp, reassoc] lemma d_to_comp_d (i j : β) : A.d_to i ≫ A.d i j = 0 :=
-- begin
--   rcases h₁ : (complex_shape.up' (ι 1)).prev i with _ | ⟨k,w₁⟩,
--   { rw [d_to_eq_zero _ h₁, zero_comp], },
--   { rw [d_to_eq _ w₁, category.assoc, d_comp_d, comp_zero], },
-- end

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


lemma cone_X (i : ℤ) : (cone f).X i = (A.X (i + 1) ⊞ B.X i) := rfl

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

def cone.triangle : triangulated.triangle (cochain_complex V ℤ) :=
{ obj₁ := A,
  obj₂ := B,
  obj₃ := cone f,
  mor₁ := f,
  mor₂ := cone.in f,
  mor₃ := cone.out f }

variables {A' B' : cochain_complex V ℤ} (f' : A' ⟶ B') (i₁ : A ⟶ A') (i₂ : B ⟶ B')
variables (comm : homotopy (i₁ ≫ f') (f ≫ i₂))

example (P : Prop) (a b : Type) (x : P) : dite P (λ _, a) (λ _, b) = a := by library_search

include comm

example (a b c : ℕ) : a + b + c = a + c + b := by library_search

def cone.map : cone f ⟶ cone f' :=
{ f := λ i, biprod.lift
  (biprod.desc (i₁.f _) 0)
  (biprod.desc (-comm.hom _ _) (i₂.f _)),
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
      rw ← sub_eq_add_neg,
      simp only [category.comp_id, preadditive.comp_neg, category.assoc, add_monoid_hom.mk'_apply,
        neg_neg, X_eq_to_iso_refl, preadditive.add_comp],
      rw add_right_comm,
      simp [d_next, prev_d] },
    { simp },
    { simp }
  end }
.
lemma cone.in_map : cone.in f ≫ cone.map f f' i₁ i₂ comm = i₂ ≫ cone.in f' :=
by ext; { dsimp [cone.map, cone.in], simp }
.
lemma cone.map_out : cone.map f f' i₁ i₂ comm ≫ cone.out f' = cone.out f ≫ i₁⟦(1 : ℤ)⟧' :=
by ext; { dsimp [cone.map, cone.out], simp }
.
def cone.triangle_map : cone.triangle f ⟶ cone.triangle f' :=
{ hom₁ := i₁,
  hom₂ := i₂,
  hom₃ := cone.map f f' i₁ i₂ comm,
  comm₁' := by { ext, dsimp [cone.triangle], simp, },
  comm₂' := _,
  comm₃' := _ }
end homological_complex
