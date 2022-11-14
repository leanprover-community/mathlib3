import algebra.homology.short_complex.homology
import category_theory.preadditive.additive_functor

noncomputable theory

open category_theory category_theory.preadditive category_theory.category category_theory.limits
open_locale zero_object

variables {C : Type*} [category C]

namespace category_theory

section

variables [has_zero_morphisms C] [has_zero_object C]
def is_colimit_cokernel_cofork_of_epi {X Y : C} (f : X ⟶ Y) [epi f]  :
  is_colimit (cokernel_cofork.of_π (0 : Y ⟶ 0) (comp_zero : f ≫ 0 = 0)) :=
cokernel_cofork.is_colimit.of_π _ _
  (λ A x hx, 0)
  (λ A x hx, by simp only [comp_zero, ← cancel_epi f, hx])
  (λ A x hx b hb, subsingleton.elim _ _)

def is_limit_kernel_fork_of_mono {X Y : C} (f : X ⟶ Y) [mono f]  :
  is_limit (kernel_fork.of_ι (0 : 0 ⟶ X) (zero_comp : 0 ≫ f = 0)) :=
kernel_fork.is_limit.of_ι _ _
  (λ A x hx, 0)
  (λ A x hx, by simp only [zero_comp, ← cancel_mono f, hx])
  (λ A x hx b hb, subsingleton.elim _ _)

@[priority 100]
instance has_cokernel_of_epi {X Y : C} (f : X ⟶ Y) [epi f] :
  has_cokernel f :=
⟨⟨⟨_, is_colimit_cokernel_cofork_of_epi f⟩⟩⟩

@[priority 100]
instance has_kernel_of_mono {X Y : C} (f : X ⟶ Y) [mono f] :
  has_kernel f :=
⟨⟨⟨_, is_limit_kernel_fork_of_mono f⟩⟩⟩

end

variable [preadditive C]

lemma mono_of_is_zero_kernel' {X Y : C} {f : X ⟶ Y}
  (c : kernel_fork f) (hc₁ : is_limit c) (hc₂ : is_zero c.X) : mono f :=
⟨λ Z g₁ g₂ hg, begin
  rw ← sub_eq_zero at ⊢ hg,
  rw ← sub_comp at hg,
  simpa only [hc₂.eq_of_src (fork.ι c) 0, comp_zero]
    using (kernel_fork.is_limit.lift_ι hc₁ (kernel_fork.of_ι _ hg)).symm,
end⟩

lemma mono_of_is_zero_kernel {X Y : C} {f : X ⟶ Y} [has_kernel f]
  (h : is_zero (kernel f)) : mono f :=
category_theory.mono_of_is_zero_kernel' _ (kernel_is_kernel f) h

lemma is_zero_kernel_of_mono {X Y : C} (f : X ⟶ Y) [mono f] [has_zero_object C] :
  is_zero (kernel f) :=
is_zero.of_iso (is_zero_zero C)
  (limits.is_limit.cone_point_unique_up_to_iso (kernel_is_kernel f)
  (is_limit_kernel_fork_of_mono f))

lemma mono_iff_is_zero_kernel {X Y : C} (f : X ⟶ Y) [has_kernel f] [has_zero_object C]:
  mono f ↔ is_zero (kernel f) :=
begin
  split,
  { introI,
    exact is_zero_kernel_of_mono f, },
  { exact mono_of_is_zero_kernel, },
end
lemma epi_of_is_zero_cokernel' {X Y : C} {f : X ⟶ Y}
  (c : cokernel_cofork f) (hc₁ : is_colimit c) (hc₂ : is_zero c.X) : epi f :=
⟨λ Z g₁ g₂ hg, begin
  rw ← sub_eq_zero at ⊢ hg,
  rw ← comp_sub at hg,
  simpa only [hc₂.eq_of_tgt (cofork.π c) 0, zero_comp]
    using (cokernel_cofork.is_colimit.π_desc hc₁ (cokernel_cofork.of_π _ hg)).symm,
end⟩

lemma epi_of_is_zero_cokernel {X Y : C} {f : X ⟶ Y} [has_cokernel f]
  (h : is_zero (cokernel f)) : epi f :=
category_theory.epi_of_is_zero_cokernel' _ (cokernel_is_cokernel f) h

lemma is_zero_cokernel_of_epi {X Y : C} (f : X ⟶ Y) [epi f] [has_zero_object C] :
  is_zero (cokernel f) :=
is_zero.of_iso (is_zero_zero C)
  (limits.is_colimit.cocone_point_unique_up_to_iso (cokernel_is_cokernel f)
  (is_colimit_cokernel_cofork_of_epi f))

lemma epi_iff_is_zero_cokernel {X Y : C} (f : X ⟶ Y) [has_cokernel f] [has_zero_object C]:
  epi f ↔ is_zero (cokernel f) :=
begin
  split,
  { introI,
    exact is_zero_cokernel_of_epi f, },
  { exact epi_of_is_zero_cokernel, },
end

end category_theory

variable [preadditive C]

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
  commi' := by simp [γ.commi],
  commf'' := by simp [γ.commf'],
  commπ' := by simp [γ.commπ], }

@[simps]
def add : left_homology_map_data (φ + φ') h₁ h₂ :=
{ φK := γ.φK + γ'.φK,
  φH := γ.φH + γ'.φH,
  commi' := by simp [γ.commi, γ'.commi],
  commf'' := by simp [γ.commf', γ'.commf'],
  commπ' := by simp [γ.commπ, γ'.commπ], }

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
  commp' := by simp [γ.commp],
  commg'' := by simp [γ.commg'],
  commι' := by simp [γ.commι], }

@[simps]
def add : right_homology_map_data (φ + φ') h₁ h₂ :=
{ φQ := γ.φQ + γ'.φQ,
  φH := γ.φH + γ'.φH,
  commp' := by simp [γ.commp, γ'.commp],
  commg'' := by simp [γ.commg', γ'.commg'],
  commι' := by simp [γ.commι, γ'.commι], }

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
lemma cycles_co_map_neg [has_right_homology S₁] [has_right_homology S₂] :
  cycles_co_map (-φ) = -cycles_co_map φ :=
cycles_co_map'_neg _ _ _

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
  right := γ.right.neg, }

@[simps]
def add : homology_map_data (φ + φ') h₁ h₂ :=
{ left := γ.left.add γ'.left,
  right := γ.right.add γ'.right, }

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
(comm₁ : φ₁.τ₁ = S₁.f ≫ h₁ + h₀ + φ₂.τ₁)
(comm₂ : φ₁.τ₂ = S₁.g ≫ h₂ + h₁ ≫ S₂.f + φ₂.τ₂)
(comm₃ : φ₁.τ₃ = h₃ + h₂ ≫ S₂.g + φ₂.τ₃)

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
  comm₁ := by { simp only [h.comm₁, comp_neg], abel, },
  comm₂ := by { simp only [h.comm₂, neg_comp, comp_neg], abel, },
  comm₃ := by { simp only [h.comm₃, neg_comp], abel, }, }

@[simp]
def trans (h : homotopy φ₁ φ₂) (h' : homotopy φ₂ φ₃) : homotopy φ₁ φ₃ :=
{ h₀ := h.h₀ + h'.h₀,
  h₀_f := by simp only [add_comp, h.h₀_f, h'.h₀_f, add_zero],
  h₁ := h.h₁ + h'.h₁,
  h₂ := h.h₂ + h'.h₂,
  h₃ := h.h₃ + h'.h₃,
  g_h₃ := by simp only [h.g_h₃, h'.g_h₃, comp_add, add_zero],
  comm₁ := by { simp only [h.comm₁, h'.comm₁, comp_add], abel, },
  comm₂ := by { simp only [h.comm₂, h'.comm₂, add_comp, comp_add], abel, },
  comm₃ := by { simp only [h.comm₃, h'.comm₃, add_comp], abel, }, }

@[simp]
def neg (h : homotopy φ₁ φ₂) : homotopy (-φ₁) (-φ₂) :=
{ h₀ := -h.h₀,
  h₀_f := by simp only [h.h₀_f, neg_comp, neg_zero],
  h₁ := -h.h₁,
  h₂ := -h.h₂,
  h₃ := -h.h₃,
  g_h₃ := by simp only [h.g_h₃, comp_neg, neg_zero],
  comm₁ := by { simp only [h.comm₁, neg_τ₁, comp_neg, neg_add_rev], abel, },
  comm₂ := by { simp only [h.comm₂, neg_τ₂, neg_comp, comp_neg, neg_add_rev], abel, },
  comm₃ := by { simp only [h.comm₃, neg_τ₃, neg_comp, neg_add_rev], abel, }, }

@[simp]
def add (h : homotopy φ₁ φ₂) (h' : homotopy φ₃ φ₄) : homotopy (φ₁ + φ₃) (φ₂ + φ₄) :=
{ h₀ := h.h₀ + h'.h₀,
  h₀_f := by simp only [h.h₀_f, h'.h₀_f, add_comp, add_zero],
  h₁ := h.h₁ + h'.h₁,
  h₂ := h.h₂ + h'.h₂,
  h₃ := h.h₃ + h'.h₃,
  g_h₃ := by simp only [h.g_h₃, h'.g_h₃, comp_add, add_zero],
  comm₁ := by { simp only [h.comm₁, h'.comm₁, add_τ₁, comp_add], abel, },
  comm₂:= by { simp only [h.comm₂, h'.comm₂, add_τ₂, add_comp, comp_add], abel, },
  comm₃ := by { simp only [h.comm₃, h'.comm₃, add_τ₃, add_comp], abel, }, }

@[simp]
def sub (h : homotopy φ₁ φ₂) (h' : homotopy φ₃ φ₄) : homotopy (φ₁ - φ₃) (φ₂ - φ₄) :=
{ h₀ := h.h₀ - h'.h₀,
  h₀_f := by simp only [h.h₀_f, h'.h₀_f, sub_comp, sub_zero],
  h₁ := h.h₁ - h'.h₁,
  h₂ := h.h₂ - h'.h₂,
  h₃ := h.h₃ - h'.h₃,
  g_h₃ := by simp only [h.g_h₃, h'.g_h₃, comp_sub, sub_self],
  comm₁ := by { simp only [h.comm₁, h'.comm₁, sub_τ₁, comp_sub], abel, },
  comm₂ := by { simp only [h.comm₂, h'.comm₂, sub_τ₂, sub_comp, comp_sub], abel, },
  comm₃ := by { simp only [h.comm₃, h'.comm₃, sub_τ₃, sub_comp], abel, }, }

@[simp]
def comp_right (h : homotopy φ₁ φ₂) (φ' : S₂ ⟶ S₃) :
  homotopy (φ₁ ≫ φ') (φ₂ ≫ φ') :=
{ h₀ := h.h₀ ≫ φ'.τ₁,
  h₀_f := by simp only [assoc, φ'.comm₁₂, h.h₀_f_assoc, zero_comp],
  h₁ := h.h₁ ≫ φ'.τ₁,
  h₂ := h.h₂ ≫ φ'.τ₂,
  h₃ := h.h₃ ≫ φ'.τ₃,
  g_h₃ := by simp only [h.g_h₃_assoc, zero_comp],
  comm₁ := by simp only [h.comm₁, comp_τ₁, add_comp, assoc],
  comm₂ := by simp only [h.comm₂, comp_τ₂, assoc, add_comp,
    add_left_inj, add_right_inj, φ'.comm₁₂],
  comm₃ := by simp only [h.comm₃, comp_τ₃, assoc, add_comp, add_right_inj, φ'.comm₂₃], }

@[simp]
def comp_left (h : homotopy φ₁ φ₂) (φ' : S₃ ⟶ S₁) :
  homotopy (φ' ≫ φ₁) (φ' ≫ φ₂) :=
{ h₀ := φ'.τ₁ ≫ h.h₀,
  h₀_f := by simp only [assoc, h.h₀_f, comp_zero],
  h₁ := φ'.τ₂ ≫ h.h₁,
  h₂ := φ'.τ₃ ≫ h.h₂,
  h₃ := φ'.τ₃ ≫ h.h₃,
  g_h₃ := by simp only [← φ'.comm₂₃_assoc, h.g_h₃, comp_zero],
  comm₁ := by { simp only [h.comm₁, comp_τ₁, comp_add, add_right_inj, φ'.comm₁₂_assoc], },
  comm₂ := by simp only [h.comm₂, comp_τ₂, assoc, comp_add,
    add_right_inj, φ'.comm₂₃_assoc],
  comm₃ := by simp only [h.comm₃, comp_τ₃, assoc, comp_add], }

@[simp]
def equiv_sub_zero : homotopy φ₁ φ₂ ≃ homotopy (φ₁ - φ₂) 0 :=
{ to_fun := λ h, (h.sub (refl φ₂)).trans (of_eq (sub_self φ₂)),
  inv_fun := λ h, ((of_eq (sub_add_cancel φ₁ φ₂).symm).trans
    (h.add (refl φ₂))).trans (of_eq (zero_add φ₂)),
  left_inv := by tidy,
  right_inv := by tidy, }

lemma eq_add_null_homotopic (h : homotopy φ₁ φ₂) :
  φ₁ = φ₂ + null_homotopic h.h₀ h.h₀_f h.h₁ h.h₂ h.h₃ h.g_h₃ :=
begin
  ext,
  { simp only [h.comm₁, add_τ₁, null_homotopic_τ₁], abel, },
  { simp only [h.comm₂, add_τ₂, null_homotopic_τ₂], abel, },
  { simp only [h.comm₃, add_τ₃, null_homotopic_τ₃], abel, },
end

variables (S₁ S₂)

@[simps]
def of_null_homotopic (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  homotopy (null_homotopic h₀ h₀_f h₁ h₂ h₃ g_h₃) 0 :=
{ h₀ := h₀,
  h₀_f := h₀_f,
  h₁ := h₁,
  h₂ := h₂,
  h₃ := h₃,
  g_h₃ := g_h₃,
  comm₁ := by { simp only [null_homotopic_τ₁, hom.zero_τ₁, add_zero], abel, },
  comm₂ := by { simp only [null_homotopic_τ₂, hom.zero_τ₂, add_zero], abel, },
  comm₃ := by rw [null_homotopic_τ₃, hom.zero_τ₃, add_zero, add_comm], }

end homotopy

@[simps]
def left_homology_map_data.of_null_homotopic
  (H₁ : S₁.left_homology_data) (H₂ : S₂.left_homology_data)
  (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  left_homology_map_data (null_homotopic h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ :=
{ φK := H₂.lift_K (H₁.i ≫ h₁ ≫ S₂.f) (by simp),
  φH := 0,
  commi' := by simp,
  commf'' := by simp only [← cancel_mono H₂.i, h₀_f, assoc, null_homotopic_τ₁,
    add_comp, left_homology_data.lift_K_i, left_homology_data.f'_i_assoc,
    left_homology_data.f'_i, zero_add],
  commπ' := by rw [H₂.lift_K_π_eq_zero_of_boundary (H₁.i ≫ h₁ ≫ S₂.f)
    (H₁.i ≫ h₁) (by rw assoc), comp_zero], }

@[simps]
def right_homology_map_data.of_null_homotopic
  (H₁ : S₁.right_homology_data) (H₂ : S₂.right_homology_data)
  (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
  (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
  right_homology_map_data (null_homotopic h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ :=
{ φQ := H₁.desc_Q (S₁.g ≫ h₂ ≫ H₂.p) (by simp),
  φH := 0,
  commp' := by simp,
  commg'' := by simp only [←cancel_epi H₁.p, g_h₃, null_homotopic_τ₃,
    comp_add, right_homology_data.p_desc_Q_assoc, assoc,
    right_homology_data.p_g', right_homology_data.p_g'_assoc, add_zero],
  commι' := by rw [H₁.ι_desc_Q_eq_zero_of_boundary (S₁.g ≫ h₂ ≫ H₂.p) (h₂ ≫ H₂.p) rfl,
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

variables (S₁ S₂)

@[ext]
structure homotopy_equiv :=
(hom : S₁ ⟶ S₂)
(inv : S₂ ⟶ S₁)
(homotopy_hom_inv_id : homotopy (hom ≫ inv) (𝟙 S₁))
(homotopy_inv_hom_id : homotopy (inv ≫ hom) (𝟙 S₂))

namespace homotopy_equiv

variables {S₁ S₂}

@[simps]
def symm (e : homotopy_equiv S₁ S₂) : homotopy_equiv S₂ S₁ :=
{ hom := e.inv,
  inv := e.hom,
  homotopy_hom_inv_id := e.homotopy_inv_hom_id,
  homotopy_inv_hom_id := e.homotopy_hom_inv_id, }

@[simps]
def left_homology_iso' (e : homotopy_equiv S₁ S₂) (h₁ : S₁.left_homology_data)
  (h₂ : S₂.left_homology_data) :
  h₁.H ≅ h₂.H :=
{ hom := left_homology_map' e.hom h₁ h₂,
  inv := left_homology_map' e.inv h₂ h₁,
  hom_inv_id' := by rw [← left_homology_map'_comp,
    e.homotopy_hom_inv_id.congr_left_homology_map' h₁ h₁, left_homology_map'_id],
  inv_hom_id' := by rw [← left_homology_map'_comp,
    e.homotopy_inv_hom_id.congr_left_homology_map' h₂ h₂, left_homology_map'_id], }

@[simps]
def left_homology_iso (e : homotopy_equiv S₁ S₂) [S₁.has_left_homology] [S₂.has_left_homology] :
  S₁.left_homology ≅ S₂.left_homology :=
{ hom := left_homology_map e.hom,
  inv := left_homology_map e.inv,
  hom_inv_id' := by rw [← left_homology_map_comp,
    e.homotopy_hom_inv_id.congr_left_homology_map, left_homology_map_id],
  inv_hom_id' := by rw [← left_homology_map_comp,
    e.homotopy_inv_hom_id.congr_left_homology_map, left_homology_map_id], }

@[simps]
def right_homology_iso' (e : homotopy_equiv S₁ S₂) (h₁ : S₁.right_homology_data)
  (h₂ : S₂.right_homology_data) :
  h₁.H ≅ h₂.H :=
{ hom := right_homology_map' e.hom h₁ h₂,
  inv := right_homology_map' e.inv h₂ h₁,
  hom_inv_id' := by rw [← right_homology_map'_comp,
    e.homotopy_hom_inv_id.congr_right_homology_map' h₁ h₁, right_homology_map'_id],
  inv_hom_id' := by rw [← right_homology_map'_comp,
    e.homotopy_inv_hom_id.congr_right_homology_map' h₂ h₂, right_homology_map'_id], }

@[simps]
def right_homology_iso (e : homotopy_equiv S₁ S₂) [S₁.has_right_homology] [S₂.has_right_homology] :
  S₁.right_homology ≅ S₂.right_homology :=
{ hom := right_homology_map e.hom,
  inv := right_homology_map e.inv,
  hom_inv_id' := by rw [← right_homology_map_comp,
    e.homotopy_hom_inv_id.congr_right_homology_map, right_homology_map_id],
  inv_hom_id' := by rw [← right_homology_map_comp,
    e.homotopy_inv_hom_id.congr_right_homology_map, right_homology_map_id], }

@[simps]
def homology_iso' (e : homotopy_equiv S₁ S₂) (h₁ : S₁.homology_data) (h₂ : S₂.homology_data) :
  h₁.left.H ≅ h₂.left.H :=
{ hom := homology_map' e.hom h₁ h₂,
  inv := homology_map' e.inv h₂ h₁,
  hom_inv_id' := by rw [← homology_map'_comp,
    e.homotopy_hom_inv_id.congr_homology_map' h₁ h₁, homology_map'_id],
  inv_hom_id' := by rw [← homology_map'_comp,
    e.homotopy_inv_hom_id.congr_homology_map' h₂ h₂, homology_map'_id], }

@[simps]
def homology_iso (e : homotopy_equiv S₁ S₂) [S₁.has_homology] [S₂.has_homology] :
  S₁.homology ≅ S₂.homology :=
{ hom := homology_map e.hom,
  inv := homology_map e.inv,
  hom_inv_id' := by rw [← homology_map_comp,
    e.homotopy_hom_inv_id.congr_homology_map, homology_map_id],
  inv_hom_id' := by rw [← homology_map_comp,
    e.homotopy_inv_hom_id.congr_homology_map, homology_map_id], }

lemma to_quasi_iso (e : homotopy_equiv S₁ S₂) [S₁.has_homology] [S₂.has_homology] :
  short_complex.quasi_iso e.hom :=
is_iso.of_iso e.homology_iso

end homotopy_equiv

end homotopy

end short_complex
