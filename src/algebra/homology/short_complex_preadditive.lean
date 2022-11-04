import algebra.homology.short_complex
import category_theory.preadditive.additive_functor

open category_theory category_theory.preadditive

variables {C : Type*} [category C] [preadditive C]

namespace short_complex

variables [preadditive C] {S₁ S₂ : short_complex C}

/-- The negation of morphisms of short complexes in `C` is obtained by the
  taking the respective negations of morphisms in the preadditive category `C`. -/
@[simps]
def hom.neg (φ : S₁ ⟶ S₂) : S₁ ⟶ S₂ :=
⟨-φ.τ₁, -φ.τ₂, -φ.τ₃,
    by simp only [neg_comp, comp_neg, neg_inj, hom.comm₁₂],
    by simp only [neg_comp, comp_neg, neg_inj, hom.comm₂₃]⟩

/-- The addition of morphisms in `short_complex C` is defined by adding
morphisms in the preadditive category `C`. -/
@[simps]
def hom.add (φ φ' : S₁ ⟶ S₂) : S₁ ⟶ S₂ :=
⟨φ.τ₁ + φ'.τ₁, φ.τ₂ + φ'.τ₂, φ.τ₃ + φ'.τ₃,
    by simp only [add_comp, comp_add, hom.comm₁₂],
    by simp only [add_comp, comp_add, hom.comm₂₃]⟩

@[simps]
instance : add_comm_group (S₁ ⟶ S₂) :=
{ add := hom.add,
  zero := hom.zero S₁ S₂,
  neg := hom.neg,
  add_assoc := λ φ φ' φ'', by { ext; apply add_assoc, },
  zero_add := λ φ, by { ext; apply zero_add, },
  add_zero := λ φ, by { ext; apply add_zero, },
  add_left_neg := λ φ, by { ext; apply add_left_neg, },
  add_comm := λ φ φ', by { ext; apply add_comm, }, }

instance : preadditive (short_complex C) := { }

end short_complex

namespace short_complex_with_homology

variables {Z₁ Z₂ : short_complex_with_homology C}

/-- The negation of morphisms in `short_complex_with_homology C` is obtained
  by negating the data. -/
@[simps]
def hom.neg (ψ : Z₁ ⟶ Z₂) : Z₁ ⟶ Z₂ :=
⟨-ψ.φ, -ψ.φK, -ψ.φQ, -ψ.φH, by simp [ψ.commi], by simp [ψ.commp], by simp [ψ.commf'],
  by simp [ψ.commg'], by simp [ψ.commπ], by simp [ψ.commι]⟩

/-- The addition of morphisms in `short_complex_with_homology C` is obtained
  by adding the data. -/
@[simps]
def hom.add (ψ ψ' : Z₁ ⟶ Z₂) : Z₁ ⟶ Z₂ :=
⟨ψ.φ + ψ'.φ, ψ.φK + ψ'.φK, ψ.φQ + ψ'.φQ, ψ.φH + ψ'.φH, by simp [hom.commi], by simp [hom.commp],
  by simp [hom.commf'], by simp [hom.commg'], by simp [hom.commπ], by simp [hom.commι]⟩

@[simps]
instance : add_comm_group (Z₁ ⟶ Z₂) :=
{ add := hom.add,
  zero := hom.zero Z₁ Z₂,
  neg := hom.neg,
  add_assoc := λ φ φ' φ'', by { ext; apply add_assoc, },
  zero_add := λ φ, by { ext; apply zero_add, },
  add_zero := λ φ, by { ext; apply add_zero, },
  add_left_neg := λ φ, by { ext; apply add_left_neg, },
  add_comm := λ φ φ', by { ext; apply add_comm, }, }

instance : preadditive (short_complex_with_homology C) := { }

instance : functor.additive (short_complex_with_homology.forget C) := { }

end short_complex_with_homology
