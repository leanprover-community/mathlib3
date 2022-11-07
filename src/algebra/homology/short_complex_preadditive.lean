import algebra.homology.short_complex_homology
import category_theory.preadditive.additive_functor

open category_theory category_theory.preadditive category_theory.category category_theory.limits

variables {C : Type*} [category C] [preadditive C]

namespace short_complex

variables {S₁ S₂ S₃ : short_complex C} {φ φ' : S₁ ⟶ S₂}

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
def hom.sub (φ φ' : S₁ ⟶ S₂) : S₁ ⟶ S₂ :=
⟨φ.τ₁ - φ'.τ₁, φ.τ₂ - φ'.τ₂, φ.τ₃ - φ'.τ₃,
    by simp only [sub_eq_add_neg, add_comp, comp_add, neg_comp, comp_neg, hom.comm₁₂],
    by simp only [sub_eq_add_neg, add_comp, comp_add, neg_comp, comp_neg, hom.comm₂₃]⟩

instance : add_comm_group (S₁ ⟶ S₂) :=
{ add := hom.add,
  zero := 0,
  neg := hom.neg,
  sub := hom.sub,
  add_assoc := λ φ φ' φ'', by { ext; apply add_assoc, },
  sub_eq_add_neg := λ φ φ', by { ext; apply sub_eq_add_neg, },
  zero_add := λ φ, by { ext; apply zero_add, },
  add_zero := λ φ, by { ext; apply add_zero, },
  add_left_neg := λ φ, by { ext; apply add_left_neg, },
  add_comm := λ φ φ', by { ext; apply add_comm, }, }

@[simp] lemma neg_τ₁ (φ : S₁ ⟶ S₂) : (-φ).τ₁ = -φ.τ₁ := rfl
@[simp] lemma neg_τ₂ (φ : S₁ ⟶ S₂) : (-φ).τ₂ = -φ.τ₂ := rfl
@[simp] lemma neg_τ₃ (φ : S₁ ⟶ S₂) : (-φ).τ₃ = -φ.τ₃ := rfl
@[simp] lemma add_τ₁ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₁ = φ.τ₁ + φ'.τ₁ := rfl
@[simp] lemma add_τ₂ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₂ = φ.τ₂ + φ'.τ₂ := rfl
@[simp] lemma add_τ₃ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₃ = φ.τ₃ + φ'.τ₃ := rfl
@[simp] lemma sub_τ₁ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₁ = φ.τ₁ - φ'.τ₁ := rfl
@[simp] lemma sub_τ₂ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₂ = φ.τ₂ - φ'.τ₂ := rfl
@[simp] lemma sub_τ₃ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₃ = φ.τ₃ - φ'.τ₃ := rfl

instance : preadditive (short_complex C) := { }

section left_homology

variables {h₁ : S₁.left_homology_data} {h₂ : S₂.left_homology_data}
  (γ : left_homology_map_data φ h₁ h₂) (γ' : left_homology_map_data φ' h₁ h₂)

namespace left_homology_map_data

@[simps]
def neg : left_homology_map_data (-φ) h₁ h₂ :=
{ φK := -γ.φK,
  φH := -γ.φH,
  commi := by simp [γ.commi],
  commf' := by simp [γ.commf'],
  commπ := by simp [γ.commπ], }

@[simps]
def add : left_homology_map_data (φ + φ') h₁ h₂ :=
{ φK := γ.φK + γ'.φK,
  φH := γ.φH + γ'.φH,
  commi := by simp [γ.commi, γ'.commi],
  commf' := by simp [γ.commf', γ'.commf'],
  commπ := by simp [γ.commπ, γ'.commπ], }

end left_homology_map_data

variables (φ φ' h₁ h₂)

@[simp]
lemma left_homology_map'_neg :
  left_homology_map' (-φ) h₁ h₂ = -left_homology_map' φ h₁ h₂ :=
begin
  let γ := left_homology_map_data.some φ h₁ h₂,
  rw [γ.left_homology_map'_eq, γ.neg.left_homology_map'_eq, left_homology_map_data.neg_φH],
end

@[simp]
lemma cycles_map'_neg :
  cycles_map' (-φ) h₁ h₂ = -cycles_map' φ h₁ h₂ :=
begin
  let γ := left_homology_map_data.some φ h₁ h₂,
  rw [γ.cycles_map'_eq, γ.neg.cycles_map'_eq, left_homology_map_data.neg_φK],
end

@[simp]
lemma left_homology_map_neg [has_left_homology S₁] [has_left_homology S₂] :
  left_homology_map (-φ) = -left_homology_map φ :=
left_homology_map'_neg _ _ _

@[simp]
lemma cycles_map_neg [has_left_homology S₁] [has_left_homology S₂] :
  cycles_map (-φ) = -cycles_map φ :=
cycles_map'_neg _ _ _

@[simp]
lemma left_homology_map'_add :
  left_homology_map' (φ + φ') h₁ h₂ = left_homology_map' φ h₁ h₂ + left_homology_map' φ' h₁ h₂ :=
begin
  let γ := left_homology_map_data.some φ h₁ h₂,
  let γ' := left_homology_map_data.some φ' h₁ h₂,
  rw [γ.left_homology_map'_eq, γ'.left_homology_map'_eq, (γ.add γ').left_homology_map'_eq,
    left_homology_map_data.add_φH],
end

@[simp]
lemma cycles_map'_add :
  cycles_map' (φ + φ') h₁ h₂ = cycles_map' φ h₁ h₂ + cycles_map' φ' h₁ h₂ :=
begin
  let γ := left_homology_map_data.some φ h₁ h₂,
  let γ' := left_homology_map_data.some φ' h₁ h₂,
  rw [γ.cycles_map'_eq, γ'.cycles_map'_eq, (γ.add γ').cycles_map'_eq,
    left_homology_map_data.add_φK],
end

@[simp]
lemma left_homology_map_add [has_left_homology S₁] [has_left_homology S₂] :
  left_homology_map (φ + φ') = left_homology_map φ + left_homology_map φ' :=
left_homology_map'_add _ _ _ _

@[simp]
lemma cycles_map_add [has_left_homology S₁] [has_left_homology S₂] :
  cycles_map (φ + φ') = cycles_map φ + cycles_map φ':=
cycles_map'_add _ _ _ _

instance left_homology_functor_additive [category_with_left_homology C] :
  functor.additive (left_homology_functor C) := { }
instance cycles_functor_additive [category_with_left_homology C] :
  functor.additive (cycles_functor C) := { }

end left_homology

section right_homology

variables {h₁ : S₁.right_homology_data} {h₂ : S₂.right_homology_data}
  (γ : right_homology_map_data φ h₁ h₂) (γ' : right_homology_map_data φ' h₁ h₂)

namespace right_homology_map_data

@[simps]
def neg : right_homology_map_data (-φ) h₁ h₂ :=
{ φQ := -γ.φQ,
  φH := -γ.φH,
  commp := by simp [γ.commp],
  commg' := by simp [γ.commg'],
  commι := by simp [γ.commι], }

@[simps]
def add : right_homology_map_data (φ + φ') h₁ h₂ :=
{ φQ := γ.φQ + γ'.φQ,
  φH := γ.φH + γ'.φH,
  commp := by simp [γ.commp, γ'.commp],
  commg' := by simp [γ.commg', γ'.commg'],
  commι := by simp [γ.commι, γ'.commι], }

end right_homology_map_data

variables (φ φ' h₁ h₂)

@[simp]
lemma right_homology_map'_neg :
  right_homology_map' (-φ) h₁ h₂ = -right_homology_map' φ h₁ h₂ :=
begin
  let γ := right_homology_map_data.some φ h₁ h₂,
  rw [γ.right_homology_map'_eq, γ.neg.right_homology_map'_eq, right_homology_map_data.neg_φH],
end

@[simp]
lemma cycles_co_map'_neg :
  cycles_co_map' (-φ) h₁ h₂ = -cycles_co_map' φ h₁ h₂ :=
begin
  let γ := right_homology_map_data.some φ h₁ h₂,
  rw [γ.cycles_co_map'_eq, γ.neg.cycles_co_map'_eq, right_homology_map_data.neg_φQ],
end

@[simp]
lemma right_homology_map_neg [has_right_homology S₁] [has_right_homology S₂] :
  right_homology_map (-φ) = -right_homology_map φ :=
right_homology_map'_neg _ _ _

@[simp]
lemma cycles_co_map_neg [has_left_homology S₁] [has_left_homology S₂] :
  cycles_map (-φ) = -cycles_map φ :=
cycles_map'_neg _ _ _

@[simp]
lemma right_homology_map'_add :
  right_homology_map' (φ + φ') h₁ h₂ = right_homology_map' φ h₁ h₂ + right_homology_map' φ' h₁ h₂ :=
begin
  let γ := right_homology_map_data.some φ h₁ h₂,
  let γ' := right_homology_map_data.some φ' h₁ h₂,
  rw [γ.right_homology_map'_eq, γ'.right_homology_map'_eq, (γ.add γ').right_homology_map'_eq,
    right_homology_map_data.add_φH],
end

@[simp]
lemma cycles_co_map'_add :
  cycles_co_map' (φ + φ') h₁ h₂ = cycles_co_map' φ h₁ h₂ + cycles_co_map' φ' h₁ h₂ :=
begin
  let γ := right_homology_map_data.some φ h₁ h₂,
  let γ' := right_homology_map_data.some φ' h₁ h₂,
  rw [γ.cycles_co_map'_eq, γ'.cycles_co_map'_eq, (γ.add γ').cycles_co_map'_eq,
    right_homology_map_data.add_φQ],
end

@[simp]
lemma right_homology_map_add [has_right_homology S₁] [has_right_homology S₂] :
  right_homology_map (φ + φ') = right_homology_map φ + right_homology_map φ' :=
right_homology_map'_add _ _ _ _

@[simp]
lemma cycles_co_map_add [has_right_homology S₁] [has_right_homology S₂] :
  cycles_co_map (φ + φ') = cycles_co_map φ + cycles_co_map φ':=
cycles_co_map'_add _ _ _ _

instance right_homology_functor_additive [category_with_right_homology C] :
  functor.additive (right_homology_functor C) := { }
instance cycles_co_functor_additive [category_with_right_homology C] :
  functor.additive (cycles_co_functor C) := { }

end right_homology

section homology

variables {h₁ : S₁.homology_data} {h₂ : S₂.homology_data}
  (γ : homology_map_data φ h₁ h₂) (γ' : homology_map_data φ' h₁ h₂)

namespace homology_map_data

@[simps]
def neg : homology_map_data (-φ) h₁ h₂ :=
{ left := γ.left.neg,
  right := γ.right.neg,
  comm := by simp [γ.comm], }

@[simps]
def add : homology_map_data (φ + φ') h₁ h₂ :=
{ left := γ.left.add γ'.left,
  right := γ.right.add γ'.right,
  comm := by simp [γ.comm, γ'.comm], }

end homology_map_data

variables (φ φ' h₁ h₂)

@[simp]
lemma homology_map'_neg :
  homology_map' (-φ) h₁ h₂ = -homology_map' φ h₁ h₂ :=
begin
  let γ := homology_map_data.some φ h₁ h₂,
  rw [γ.homology_map'_eq, γ.neg.homology_map'_eq,
    homology_map_data.neg_left, left_homology_map_data.neg_φH],
end

@[simp]
lemma homology_map_neg [has_homology S₁] [has_homology S₂] :
  homology_map (-φ) = -homology_map φ :=
homology_map'_neg _ _ _

@[simp]
lemma homology_map'_add :
  homology_map' (φ + φ') h₁ h₂ = homology_map' φ h₁ h₂ + homology_map' φ' h₁ h₂ :=
begin
  let γ := homology_map_data.some φ h₁ h₂,
  let γ' := homology_map_data.some φ' h₁ h₂,
  rw [γ.homology_map'_eq, γ'.homology_map'_eq, (γ.add γ').homology_map'_eq,
    homology_map_data.add_left, left_homology_map_data.add_φH],
end

@[simp]
lemma homology_map_add [has_homology S₁] [has_homology S₂] :
  homology_map (φ + φ') = homology_map φ + homology_map φ' :=
homology_map'_add _ _ _ _

instance homology_functor_additive [category_with_homology C] :
  functor.additive (homology_functor C) := { }

end homology

section homotopy

variables (φ) (φ₁ φ₂ φ₃ φ₄ : S₁ ⟶ S₂)

@[ext]
structure homotopy :=
(h₀ : S₁.X₁ ⟶ S₂.X₁)
(h₀_f : h₀ ≫ S₂.f = 0)
(h₁ : S₁.X₂ ⟶ S₂.X₁)
(h₂ : S₁.X₃ ⟶ S₂.X₂)
(h₃ : S₁.X₃ ⟶ S₂.X₃)
(g_h₃ : S₁.g ≫ h₃ = 0)
(comm₁ : φ₁.τ₁ + h₀ + S₁.f ≫ h₁ = φ₂.τ₁)
(comm₂ : φ₁.τ₂ + h₁ ≫ S₂.f + S₁.g ≫ h₂ = φ₂.τ₂)
(comm₃ : φ₁.τ₃ + h₃ + h₂ ≫ S₂.g = φ₂.τ₃)

@[simps]
def null_homotopic (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
(h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) : S₁ ⟶ S₂ :=
{ τ₁ := h₀ + S₁.f ≫ h₁,
  τ₂ := h₁ ≫ S₂.f + S₁.g ≫ h₂,
  τ₃ := h₂ ≫ S₂.g + h₃,
  comm₁₂ := by simp [h₀_f],
  comm₂₃ := by simp [g_h₃], }

namespace homotopy

attribute [reassoc] h₀_f g_h₃

variables {φ₁ φ₂ φ₃ φ₄}

@[simp]
def of_eq (h : φ₁ = φ₂) : homotopy φ₁ φ₂ :=
{ h₀ := 0,
  h₀_f := by simp,
  h₁ := 0,
  h₂ := 0,
  h₃ := 0,
  g_h₃ := by simp,
  comm₁ := by simp [h],
  comm₂ := by simp [h],
  comm₃ := by simp [h], }

@[simps]
def refl : homotopy φ φ := of_eq rfl

@[simp]
def symm (h : homotopy φ₁ φ₂) : homotopy φ₂ φ₁ :=
{ h₀ := -h.h₀,
  h₀_f := by simp only [neg_comp, neg_eq_zero, h.h₀_f],
  h₁ := -h.h₁,
  h₂ := -h.h₂,
  h₃ := -h.h₃,
  g_h₃ := by simp only [h.g_h₃, comp_neg, neg_zero],
  comm₁ := by { simp only [← h.comm₁, comp_neg], abel, },
  comm₂ := by { simp only [← h.comm₂, neg_comp, comp_neg], abel, },
  comm₃ := by { simp only [←h.comm₃, neg_comp], abel, }, }

@[simp]
def trans (h : homotopy φ₁ φ₂) (h' : homotopy φ₂ φ₃) : homotopy φ₁ φ₃ :=
{ h₀ := h.h₀ + h'.h₀,
  h₀_f := by simp only [add_comp, h.h₀_f, h'.h₀_f, add_zero],
  h₁ := h.h₁ + h'.h₁,
  h₂ := h.h₂ + h'.h₂,
  h₃ := h.h₃ + h'.h₃,
  g_h₃ := by simp only [h.g_h₃, h'.g_h₃, comp_add, add_zero],
  comm₁ := by { simp only [← h.comm₁, ←h'.comm₁, comp_add], abel, },
  comm₂ := by { simp only [← h.comm₂, ← h'.comm₂, add_comp, comp_add], abel, },
  comm₃ := by { simp only [← h.comm₃, ←h'.comm₃, add_comp], abel, }, }

@[simp]
def neg (h : homotopy φ₁ φ₂) : homotopy (-φ₁) (-φ₂) :=
{ h₀ := -h.h₀,
  h₀_f := by simp only [h.h₀_f, neg_comp, neg_zero],
  h₁ := -h.h₁,
  h₂ := -h.h₂,
  h₃ := -h.h₃,
  g_h₃ := by simp only [h.g_h₃, comp_neg, neg_zero],
  comm₁ := by { simp only [← h.comm₁, neg_τ₁, comp_neg, neg_add_rev], abel, },
  comm₂ := by { simp only [← h.comm₂, neg_τ₂, neg_comp, comp_neg, neg_add_rev], abel, },
  comm₃ := by { simp only [← h.comm₃, neg_τ₃, neg_comp, neg_add_rev], abel, }, }

@[simp]
def add (h : homotopy φ₁ φ₂) (h' : homotopy φ₃ φ₄) : homotopy (φ₁ + φ₃) (φ₂ + φ₄) :=
{ h₀ := h.h₀ + h'.h₀,
  h₀_f := by simp only [h.h₀_f, h'.h₀_f, add_comp, add_zero],
  h₁ := h.h₁ + h'.h₁,
  h₂ := h.h₂ + h'.h₂,
  h₃ := h.h₃ + h'.h₃,
  g_h₃ := by simp only [h.g_h₃, h'.g_h₃, comp_add, add_zero],
  comm₁ := by { simp only [← h.comm₁, ← h'.comm₁, add_τ₁, comp_add], abel, },
  comm₂:= by { simp only [← h.comm₂, ← h'.comm₂, add_τ₂, add_comp, comp_add], abel, },
  comm₃ := by { simp only [← h.comm₃, ← h'.comm₃, add_τ₃, add_comp], abel, }, }

@[simp]
def sub (h : homotopy φ₁ φ₂) (h' : homotopy φ₃ φ₄) : homotopy (φ₁ - φ₃) (φ₂ - φ₄) :=
{ h₀ := h.h₀ - h'.h₀,
  h₀_f := by simp only [h.h₀_f, h'.h₀_f, sub_comp, sub_zero],
  h₁ := h.h₁ - h'.h₁,
  h₂ := h.h₂ - h'.h₂,
  h₃ := h.h₃ - h'.h₃,
  g_h₃ := by simp only [h.g_h₃, h'.g_h₃, comp_sub, sub_self],
  comm₁ := by { simp only [← h.comm₁, ←h'.comm₁, sub_τ₁, comp_sub], abel, },
  comm₂ := by { simp only [← h.comm₂, ← h'.comm₂, sub_τ₂, sub_comp, comp_sub], abel, },
  comm₃ := by { simp only [← h.comm₃, ← h'.comm₃, sub_τ₃, sub_comp], abel, }, }

@[simp]
def comp_right (h : homotopy φ₁ φ₂) (φ' : S₂ ⟶ S₃) :
  homotopy (φ₁ ≫ φ') (φ₂ ≫ φ') :=
{ h₀ := h.h₀ ≫ φ'.τ₁,
  h₀_f := by simp only [assoc, φ'.comm₁₂, h.h₀_f_assoc, zero_comp],
  h₁ := h.h₁ ≫ φ'.τ₁,
  h₂ := h.h₂ ≫ φ'.τ₂,
  h₃ := h.h₃ ≫ φ'.τ₃,
  g_h₃ := by simp only [h.g_h₃_assoc, zero_comp],
  comm₁ := by simp only [←h.comm₁, comp_τ₁, add_comp, assoc],
  comm₂ := by simp only [← h.comm₂, comp_τ₂, assoc, add_comp,
    add_left_inj, add_right_inj, φ'.comm₁₂],
  comm₃ := by simp only [←h.comm₃, comp_τ₃, assoc, add_comp, add_right_inj, φ'.comm₂₃], }

@[simp]
def comp_left (h : homotopy φ₁ φ₂) (φ' : S₃ ⟶ S₁) :
  homotopy (φ' ≫ φ₁) (φ' ≫ φ₂) :=
{ h₀ := φ'.τ₁ ≫ h.h₀,
  h₀_f := by simp only [assoc, h.h₀_f, comp_zero],
  h₁ := φ'.τ₂ ≫ h.h₁,
  h₂ := φ'.τ₃ ≫ h.h₂,
  h₃ := φ'.τ₃ ≫ h.h₃,
  g_h₃ := by simp only [← φ'.comm₂₃_assoc, h.g_h₃, comp_zero],
  comm₁ := by { simp only [←h.comm₁, comp_τ₁, comp_add, add_right_inj, φ'.comm₁₂_assoc], },
  comm₂ := by simp only [← h.comm₂, comp_τ₂, assoc, comp_add,
    add_right_inj, φ'.comm₂₃_assoc],
  comm₃ := by simp only [←h.comm₃, comp_τ₃, assoc, comp_add], }

@[simp]
def equiv_sub_zero : homotopy φ₁ φ₂ ≃ homotopy (φ₁ - φ₂) 0 :=
{ to_fun := λ h, (h.sub (refl φ₂)).trans (of_eq (sub_self φ₂)),
  inv_fun := λ h, ((of_eq (sub_add_cancel φ₁ φ₂).symm).trans
    (h.add (refl φ₂))).trans (of_eq (zero_add φ₂)),
  left_inv := by tidy,
  right_inv := by tidy, }

lemma eq_add_null_homotopic (h : homotopy φ₁ φ₂) :
  φ₂ = φ₁ + null_homotopic h.h₀ h.h₀_f h.h₁ h.h₂ h.h₃ h.g_h₃ :=
begin
  ext,
  { simp only [← h.comm₁, add_τ₁, null_homotopic_τ₁], abel, },
  { simp only [← h.comm₂, add_τ₂, null_homotopic_τ₂], abel, },
  { simp only [← h.comm₃, add_τ₃, null_homotopic_τ₃], abel, },
end

variables (S₁ S₂)

@[simps]
def of_null_homotopic (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  homotopy (null_homotopic h₀ h₀_f h₁ h₂ h₃ g_h₃) 0 :=
{ h₀ := -h₀,
  h₀_f := by rw [neg_comp, h₀_f, neg_zero],
  h₁ := -h₁,
  h₂ := -h₂,
  h₃ := -h₃,
  g_h₃ := by rw [comp_neg, g_h₃, neg_zero],
  comm₁ := by simp,
  comm₂ := by simp,
  comm₃ := by simp, }

end homotopy

@[simps]
def left_homology_map_data.of_null_homotopic
  (H₁ : S₁.left_homology_data) (H₂ : S₂.left_homology_data)
  (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  left_homology_map_data (null_homotopic h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ :=
{ φK := H₂.lift_K (H₁.i ≫ h₁ ≫ S₂.f) (by simp),
  φH := 0,
  commi := by simp,
  commf' := by simp only [← cancel_mono H₂.i, h₀_f, assoc, null_homotopic_τ₁,
    add_comp, left_homology_data.lift_K_i, left_homology_data.f'_i_assoc,
    left_homology_data.f'_i, zero_add],
  commπ := by rw [H₂.lift_K_π_eq_zero_of_boundary (H₁.i ≫ h₁ ≫ S₂.f)
    (H₁.i ≫ h₁) (by rw assoc), comp_zero], }

@[simps]
def right_homology_map_data.of_null_homotopic
  (H₁ : S₁.right_homology_data) (H₂ : S₂.right_homology_data)
  (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  right_homology_map_data (null_homotopic h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ :=
{ φQ := H₁.desc_Q (S₁.g ≫ h₂ ≫ H₂.p) (by simp),
  φH := 0,
  commp := by simp,
  commg' := by simp only [←cancel_epi H₁.p, g_h₃, null_homotopic_τ₃, comp_add, assoc,
    add_right_eq_self, right_homology_data.p_g'_assoc, right_homology_data.p_desc_Q_assoc,
    right_homology_data.p_g'],
  commι := by rw [H₁.ι_desc_Q_eq_zero_of_boundary (S₁.g ≫ h₂ ≫ H₂.p) (h₂ ≫ H₂.p) rfl,
    zero_comp], }

namespace homotopy

variables {φ₁ φ₂}

@[simp]
lemma left_homology_map'_null_homotopic
  (H₁ : S₁.left_homology_data) (H₂ : S₂.left_homology_data)
  (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  left_homology_map' (null_homotopic h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 :=
(left_homology_map_data.of_null_homotopic H₁ H₂ h₀ h₀_f h₁ h₂ h₃ g_h₃).left_homology_map'_eq

@[simp]
lemma right_homology_map'_null_homotopic
  (H₁ : S₁.right_homology_data) (H₂ : S₂.right_homology_data)
  (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  right_homology_map' (null_homotopic h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 :=
(right_homology_map_data.of_null_homotopic H₁ H₂ h₀ h₀_f h₁ h₂ h₃ g_h₃).right_homology_map'_eq

@[simp]
lemma homology_map'_null_homotopic
  (H₁ : S₁.homology_data) (H₂ : S₂.homology_data)
  (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  homology_map' (null_homotopic h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 :=
by apply left_homology_map'_null_homotopic

variables (S₁ S₂)

@[simp]
lemma left_homology_map_null_homotopic [S₁.has_left_homology] [S₂.has_left_homology]
  (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  left_homology_map (null_homotopic h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0 :=
by apply left_homology_map'_null_homotopic

@[simp]
lemma right_homology_map_null_homotopic [S₁.has_right_homology] [S₂.has_right_homology]
  (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  right_homology_map (null_homotopic h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0 :=
by apply right_homology_map'_null_homotopic

@[simp]
lemma homology_map_null_homotopic [S₁.has_homology] [S₂.has_homology]
  (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  homology_map (null_homotopic h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0 :=
by apply homology_map'_null_homotopic

variables {S₁ S₂}

lemma congr_left_homology_map'
  (h : homotopy φ₁ φ₂) (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data) :
  left_homology_map' φ₁ h₁ h₂ = left_homology_map' φ₂ h₁ h₂ :=
by rw [h.eq_add_null_homotopic, left_homology_map'_add,
  left_homology_map'_null_homotopic, add_zero]

lemma congr_left_homology_map (h : homotopy φ₁ φ₂) [S₁.has_left_homology] [S₂.has_left_homology] :
  left_homology_map φ₁ = left_homology_map φ₂ :=
congr_left_homology_map' h _ _

lemma congr_right_homology_map'
  (h : homotopy φ₁ φ₂) (h₁ : S₁.right_homology_data) (h₂ : S₂.right_homology_data) :
  right_homology_map' φ₁ h₁ h₂ = right_homology_map' φ₂ h₁ h₂ :=
by rw [h.eq_add_null_homotopic, right_homology_map'_add,
  right_homology_map'_null_homotopic, add_zero]

lemma congr_right_homology_map (h : homotopy φ₁ φ₂) [S₁.has_right_homology] [S₂.has_right_homology] :
  right_homology_map φ₁ = right_homology_map φ₂ :=
congr_right_homology_map' h _ _

lemma congr_homology_map'
  (h : homotopy φ₁ φ₂) (h₁ : S₁.homology_data) (h₂ : S₂.homology_data) :
  homology_map' φ₁ h₁ h₂ = homology_map' φ₂ h₁ h₂ :=
by rw [h.eq_add_null_homotopic, homology_map'_add,
  homology_map'_null_homotopic, add_zero]

lemma congr_homology_map (h : homotopy φ₁ φ₂) [S₁.has_homology] [S₂.has_homology] :
  homology_map φ₁ = homology_map φ₂ :=
congr_homology_map' h _ _

end homotopy

end homotopy

end short_complex
