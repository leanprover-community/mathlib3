import algebra.homology.homological_complex
import category_theory.abelian.basic

noncomputable theory

universes v u

open category_theory category_theory.limits

namespace homological_complex

variables {V : Type u} [category.{v} V] [abelian V]
variables {ι : Type*} {c : complex_shape ι}
variables (A B : homological_complex V c) (f : A ⟶ B)

-- move this
@[simp, reassoc] lemma d_comp_d_from (i j : ι) : A.d i j ≫ A.d_from j = 0 :=
begin
  rcases h₁ : c.next j with _ | ⟨k,w₁⟩,
  { rw [d_from_eq_zero _ h₁, comp_zero], },
  { rw [d_from_eq _ w₁, d_comp_d_assoc, zero_comp], },
end

-- move this
@[simp, reassoc] lemma d_to_comp_d (i j : ι) : A.d_to i ≫ A.d i j = 0 :=
begin
  rcases h₁ : c.prev i with _ | ⟨k,w₁⟩,
  { rw [d_to_eq_zero _ h₁, zero_comp], },
  { rw [d_to_eq _ w₁, category.assoc, d_comp_d, comp_zero], },
end

def cone.X : ι → V := λ i, A.X_next i ⊞ B.X i

variables {A B}

def cone.d [decidable_rel c.rel] : Π (i j : ι), cone.X A B i ⟶ cone.X A B j :=
λ i j, if hij : c.rel i j then biprod.lift
  (biprod.desc (- ((A.X_next_iso hij).hom ≫ A.d_from _))  0       )
  (biprod.desc (f.next _ ≫ (B.X_next_iso hij).hom)       (B.d _ _))
else 0

/-- The mapping cone of a morphism `f : A → B` of homological complexes. -/
def cone [decidable_rel c.rel] : homological_complex V c :=
{ X := cone.X A B,
  d := cone.d f,
  shape' := λ i j hij, dif_neg hij,
  d_comp_d' := λ i j k hij hjk,
  begin
    dsimp only [cone.d], rw [dif_pos hij, dif_pos hjk],
    ext;
    simp only [d_from_comp_X_next_iso, zero_add, add_zero, zero_comp, comp_zero, neg_zero, neg_neg,
      preadditive.comp_add, preadditive.add_comp,
      biprod.lift_fst, biprod.lift_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc,
      biprod.inl_desc, biprod.inr_desc, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
      biprod.lift_desc,
      preadditive.neg_comp, preadditive.neg_comp_assoc, preadditive.comp_neg, category.assoc,
      d_comp_d, d_comp_d_from],
    rw [neg_add_eq_zero, ← f.comm_from_assoc, d_from_comp_X_next_iso, f.next_eq hij],
    simp only [iso.inv_hom_id_assoc, category.assoc],
  end }
.


lemma cone_X {_ : decidable_rel c.rel} (i : ι) : (cone f).X i = (A.X_next i ⊞ B.X i) := rfl

lemma cone_d {_ : decidable_rel c.rel} : (cone f).d = cone.d f := rfl

def cone.in [decidable_rel c.rel] : B ⟶ cone f :=
{ f := λ i, biprod.inr,
  comm' := λ i j hij,
  begin
    dsimp [cone_d, cone.d], rw [dif_pos hij],
    ext;
    simp only [comp_zero, category.assoc, category.comp_id,
      biprod.inr_desc, biprod.inr_fst, biprod.lift_fst, biprod.inr_snd, biprod.lift_snd],
  end }

/- TODO: `cone.out : cone f ⟶ A⟦1⟧ `-/

end homological_complex
