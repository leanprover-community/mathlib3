import algebra.homology.short_complex_right_homology

noncomputable theory

open category_theory category_theory.limits category_theory.category

variables {C : Type*} [category C] [has_zero_morphisms C]

namespace short_complex

variables (S S₁ S₂ S₃ : short_complex C)

structure homology_data :=
(left : S.left_homology_data)
(right : S.right_homology_data)
(iso : left.H ≅ right.H)
(comm : left.π ≫ iso.hom ≫ right.ι = left.i ≫ right.p)

attribute [reassoc, simp] homology_data.comm

variables {S₁ S₂ S₃} (φ : S₁ ⟶ S₂) (h₁ : S₁.homology_data) (h₂ : S₂.homology_data)

structure homology_map_data :=
(left : left_homology_map_data φ h₁.left h₂.left)
(right : right_homology_map_data φ h₁.right h₂.right)
(comm : left.φH ≫ h₂.iso.hom = h₁.iso.hom ≫ right.φH)

namespace homology_map_data

attribute [reassoc] comm

instance : subsingleton (homology_map_data φ h₁ h₂) :=
⟨begin
  rintro ⟨left₁, right₁, comm₁⟩ ⟨left₂, right₂, comm₂⟩,
  simp only [eq_iff_true_of_subsingleton, and_self],
end⟩

instance : inhabited (homology_map_data φ h₁ h₂) :=
begin
  let left : left_homology_map_data φ h₁.left h₂.left := default,
  let right : right_homology_map_data φ h₁.right h₂.right := default,
  refine ⟨⟨left, right, _⟩⟩,
  simp only [← cancel_mono h₂.right.ι, ← cancel_epi h₁.left.π,
    assoc, left.commπ_assoc, h₂.comm, ← right.commι],
  slice_rhs 1 3 { rw h₁.comm, },
  simp only [assoc, ← left.commi_assoc, ← right.commp],
end

instance : unique (homology_map_data φ h₁ h₂) := unique.mk' _

def some : homology_map_data φ h₁ h₂ := default

variables {φ h₁ h₂}

lemma congr_left_φH {γ₁ γ₂ : homology_map_data φ h₁ h₂} (eq : γ₁ = γ₂) :
  γ₁.left.φH = γ₂.left.φH := by rw eq

end homology_map_data

namespace homology_data

@[simps]
def of_colimit_cokernel_cofork (hg : S.g = 0) (c : cokernel_cofork S.f) (hc : is_colimit c) :
  S.homology_data :=
{ left := left_homology_data.of_colimit_cokernel_cofork S hg c hc,
  right := right_homology_data.of_colimit_cokernel_cofork S hg c hc,
  iso := iso.refl _,
  comm := by tidy, }

@[simps]
def of_has_cokernel [has_cokernel S.f] (hg : S.g = 0) : S.homology_data :=
{ left := left_homology_data.of_has_cokernel S hg,
  right := right_homology_data.of_has_cokernel S hg,
  iso := iso.refl _,
  comm := by tidy, }

@[simps]
def of_limit_kernel_fork (hf : S.f = 0) (c : kernel_fork S.g) (hc : is_limit c) :
  S.homology_data :=
{ left := left_homology_data.of_limit_kernel_fork S hf c hc,
  right := right_homology_data.of_limit_kernel_fork S hf c hc,
  iso := iso.refl _,
  comm := by tidy, }

@[simp]
def of_has_kernel [has_kernel S.g] (hf : S.f = 0) : S.homology_data :=
of_limit_kernel_fork S hf _ (kernel_is_kernel _)

@[simps]
def of_zeros (hf : S.f = 0) (hg : S.g = 0) : S.homology_data :=
{ left := left_homology_data.of_zeros S hf hg,
  right := right_homology_data.of_zeros S hf hg,
  iso := iso.refl _,
  comm := by tidy, }

variable {S}

@[simps]
def op (h : S.homology_data) : S.op.homology_data :=
{ left := h.right.op,
  right := h.left.op,
  iso := h.iso.op,
  comm := quiver.hom.unop_inj (by simp), }

@[simps]
def unop' {S : short_complex Cᵒᵖ} (h : S.homology_data) : S.unop.homology_data :=
{ left := h.right.unop',
  right := h.left.unop',
  iso := h.iso.unop,
  comm := quiver.hom.op_inj (by simp), }

@[simps]
def unop {S : short_complex C} (h : S.op.homology_data) : S.homology_data :=
{ left := h.right.unop,
  right := h.left.unop,
  iso := h.iso.unop,
  comm := quiver.hom.op_inj (by simp), }

end homology_data

class has_homology : Prop :=
(cond : nonempty S.homology_data)

def some_homology_data [has_homology S] :
  S.homology_data := has_homology.cond.some

variable {S}

lemma has_homology.mk' (h : S.homology_data) : has_homology S :=
⟨nonempty.intro h⟩

instance [has_homology S] : has_homology S.op :=
has_homology.mk' S.some_homology_data.op

@[priority 100]
instance has_left_homology_of_has_homology [has_homology S] : has_left_homology S :=
has_left_homology.mk' S.some_homology_data.left

@[priority 100]
instance has_right_homology_of_has_homology [has_homology S] : has_right_homology S :=
has_right_homology.mk' S.some_homology_data.right

instance has_homology_of_has_cokernel {X Y : C} (f : X ⟶ Y) (Z : C)
  [has_cokernel f] :
  (short_complex.mk f (0 : Y ⟶ Z) comp_zero).has_homology :=
has_homology.mk' (homology_data.of_has_cokernel _ rfl)

instance has_homology_of_has_kernel {Y Z : C} (g : Y ⟶ Z) (X : C)
  [has_kernel g] :
  (short_complex.mk (0 : X ⟶ Y) g zero_comp).has_homology :=
has_homology.mk' (homology_data.of_has_kernel _ rfl)

instance has_homology_of_zeros (X Y Z : C) :
  (short_complex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).has_homology :=
has_homology.mk' (homology_data.of_zeros _ rfl rfl)

namespace homology_map_data

@[simps]
def id (h : S.homology_data) :
  homology_map_data (𝟙 S) h h :=
{ left := left_homology_map_data.id h.left,
  right := right_homology_map_data.id h.right,
  comm := by tidy, }

@[simps]
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.homology_data}
  {h₂ : S₂.homology_data} {h₃ : S₃.homology_data}
  (ψ : homology_map_data φ h₁ h₂) (ψ' : homology_map_data φ' h₂ h₃) :
  homology_map_data (φ ≫ φ') h₁ h₃ :=
{ left := ψ.left.comp ψ'.left,
  right := ψ.right.comp ψ'.right,
  comm := by simp only [left_homology_map_data.comp_φH, assoc, right_homology_map_data.comp_φH,
      ψ'.comm, ψ.comm_assoc], }

@[simps]
def op {φ : S₁ ⟶ S₂} {h₁ : S₁.homology_data} {h₂ : S₂.homology_data}
  (ψ : homology_map_data φ h₁ h₂) :
  homology_map_data (op_map φ) h₂.op h₁.op :=
{ left := ψ.right.op,
  right := ψ.left.op,
  comm := quiver.hom.unop_inj (ψ.comm.symm), }

@[simps]
def unop {S₁ S₂ : short_complex C} {φ : S₁.op ⟶ S₂.op}
  {h₁ : S₁.op.homology_data} {h₂ : S₂.op.homology_data}
  (ψ : homology_map_data φ h₁ h₂) :
  homology_map_data (unop_map φ) h₂.unop h₁.unop :=
{ left := ψ.right.unop,
  right := ψ.left.unop,
  comm := quiver.hom.op_inj ψ.comm.symm, }

@[simps]
def unop' {S₁ S₂ : short_complex Cᵒᵖ} {φ : S₁ ⟶ S₂} {h₁ : S₁.homology_data} {h₂ : S₂.homology_data}
  (ψ : homology_map_data φ h₁ h₂) :
  homology_map_data (unop'_map φ) h₂.unop' h₁.unop' :=
{ left := ψ.right.unop',
  right := ψ.left.unop',
  comm := quiver.hom.op_inj (ψ.comm.symm), }

end homology_map_data

variable (S)

def homology [has_homology S] : C := S.some_homology_data.left.H

def homology_map' (φ : S₁ ⟶ S₂) (h₁ : S₁.homology_data) (h₂ : S₂.homology_data) :
  h₁.left.H ⟶ h₂.left.H := left_homology_map' φ _ _

def homology_map [has_homology S₁] [has_homology S₂]
  (φ : S₁ ⟶ S₂) : S₁.homology ⟶ S₂.homology :=
homology_map' φ _ _

variable {S}
lemma homology_map'_id (h : S.homology_data) :
  homology_map' (𝟙 S) h h = 𝟙 _ :=
homology_map_data.congr_left_φH (subsingleton.elim default (homology_map_data.id h))

@[simp]
lemma homology_map_id [has_homology S] :
  homology_map (𝟙 S) = 𝟙 _ :=
homology_map'_id _

lemma homology_map'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  (h₁ : S₁.homology_data) (h₂ : S₂.homology_data) (h₃ : S₃.homology_data) :
  homology_map' (φ₁ ≫ φ₂) h₁ h₃ = homology_map' φ₁ h₁ h₂ ≫
    homology_map' φ₂ h₂ h₃ :=
homology_map_data.congr_left_φH
  (subsingleton.elim default ((homology_map_data.some φ₁ h₁ h₂).comp
    (homology_map_data.some φ₂ h₂ h₃)))

@[simp]
lemma homology_map_comp [has_homology S₁] [has_homology S₂] [has_homology S₃]
  (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
  homology_map (φ₁ ≫ φ₂) = homology_map φ₁ ≫ homology_map φ₂ :=
homology_map'_comp _ _ _ _ _

@[simps]
def homology_map_iso' (e : S₁ ≅ S₂) (h₁ : S₁.homology_data)
  (h₂ : S₂.homology_data) : h₁.left.H ≅ h₂.left.H :=
{ hom := homology_map' e.hom h₁ h₂,
  inv := homology_map' e.inv h₂ h₁,
  hom_inv_id' := by rw [← homology_map'_comp, e.hom_inv_id, homology_map'_id],
  inv_hom_id' := by rw [← homology_map'_comp, e.inv_hom_id, homology_map'_id], }

instance is_iso_homology_map'_of_iso (φ : S₁ ⟶ S₂) [is_iso φ]
  (h₁ : S₁.homology_data) (h₂ : S₂.homology_data) :
  is_iso (homology_map' φ h₁ h₂) :=
by { change is_iso (homology_map_iso' (as_iso φ) h₁ h₂).hom, apply_instance, }

@[simps]
def homology_map_iso (e : S₁ ≅ S₂) [S₁.has_homology]
  [S₂.has_homology] : S₁.homology ≅ S₂.homology :=
{ hom := homology_map e.hom,
  inv := homology_map e.inv,
  hom_inv_id' := by rw [← homology_map_comp, e.hom_inv_id, homology_map_id],
  inv_hom_id' := by rw [← homology_map_comp, e.inv_hom_id, homology_map_id], }

instance is_iso_homology_map_of_iso (φ : S₁ ⟶ S₂) [is_iso φ] [S₁.has_homology] [S₂.has_homology] :
  is_iso (homology_map φ) :=
by { change is_iso (homology_map_iso (as_iso φ)).hom, apply_instance, }

def homology_data.homology_iso (h₁ : S.homology_data) [S.has_homology] :
  S.homology ≅ h₁.left.H := homology_map_iso' (iso.refl _) _ _

namespace homology_map_data

variables {φ h₁ h₂} (γ : homology_map_data φ h₁ h₂)

lemma homology_map'_eq : homology_map' φ h₁ h₂ = γ.left.φH := γ.left.left_homology_map'_eq

lemma homology_map_eq [S₁.has_homology] [S₂.has_homology] :
  homology_map φ = h₁.homology_iso.hom ≫ γ.left.φH ≫ h₂.homology_iso.inv :=
begin
  dsimp [homology_data.homology_iso, homology_map_iso'],
  rw [← γ.homology_map'_eq, ← homology_map'_comp, ← homology_map'_comp, comp_id, id_comp],
  refl,
end

lemma map_comm [S₁.has_homology] [S₂.has_homology] :
  homology_map φ ≫ h₂.homology_iso.hom = h₁.homology_iso.hom ≫ γ.left.φH :=
by simp only [γ.homology_map_eq, assoc, iso.inv_hom_id, comp_id]

end homology_map_data

namespace left_homology_data

def homology_iso (h : S.left_homology_data) [S.has_homology] :
  S.homology ≅ h.H :=
left_homology_map_iso' (iso.refl S) _ _

end left_homology_data

variables {C}

def left_right_homology_comparison' (h₁ : S.left_homology_data) (h₂ : S.right_homology_data) :
  h₁.H ⟶ h₂.H :=
h₂.lift_H (h₁.desc_H (h₁.i ≫ h₂.p) (by simp)) (by simp [← cancel_epi h₁.π])

lemma left_right_homology_comparison'_eq₁ (h₁ : S.left_homology_data) (h₂ : S.right_homology_data) :
left_right_homology_comparison' h₁ h₂ =
  h₂.lift_H (h₁.desc_H (h₁.i ≫ h₂.p) (by simp)) (by simp [← cancel_epi h₁.π]) := rfl

@[simp, reassoc]
lemma comp_left_right_homology_comparison'_comp (h₁ : S.left_homology_data) (h₂ : S.right_homology_data) :
  h₁.π ≫ left_right_homology_comparison' h₁ h₂ ≫ h₂.ι = h₁.i ≫ h₂.p :=
by simp [left_right_homology_comparison'_eq₁]

lemma left_right_homology_comparison'_eq₂ (h₁ : S.left_homology_data) (h₂ : S.right_homology_data) :
left_right_homology_comparison' h₁ h₂ =
  h₁.desc_H (h₂.lift_H (h₁.i ≫ h₂.p) (by simp)) (by simp [← cancel_mono h₂.ι]) :=
by simp [← cancel_mono h₂.ι, ← cancel_epi h₁.π]

variable (S)

def left_right_homology_comparison [S.has_left_homology] [S.has_right_homology] :
  S.left_homology ⟶ S.right_homology :=
left_right_homology_comparison' _ _

@[reassoc]
lemma left_right_homology_comparison'_naturality (φ : S₁ ⟶ S₂) (h₁ : S₁.left_homology_data)
  (h₂ : S₁.right_homology_data) (h₁' : S₂.left_homology_data) (h₂' : S₂.right_homology_data) :
  left_homology_map' φ h₁ h₁' ≫ left_right_homology_comparison' h₁' h₂' =
    left_right_homology_comparison' h₁ h₂ ≫ right_homology_map' φ h₂ h₂' :=
by simp only [← cancel_epi h₁.π, ← cancel_mono h₂'.ι, assoc,
    ← left_homology_π_naturality'_assoc, right_homology_ι_naturality',
    comp_left_right_homology_comparison'_comp,
    comp_left_right_homology_comparison'_comp_assoc,
    cycles_map'_i_assoc, p_cycles_co_map']

variable {S}

lemma left_right_homology_comparison'_compatibility (h₁ h₁' : S.left_homology_data) (h₂ h₂' : S.right_homology_data) :
  left_right_homology_comparison' h₁ h₂ = left_homology_map' (𝟙 S) h₁ h₁' ≫
    left_right_homology_comparison' h₁' h₂' ≫ right_homology_map' (𝟙 S) _ _ :=
by rw [left_right_homology_comparison'_naturality_assoc (𝟙 S) h₁ h₂ h₁' h₂',
    ← right_homology_map'_comp, comp_id, right_homology_map'_id, comp_id]

lemma left_right_homology_comparison_eq [S.has_left_homology] [S.has_right_homology]
  (h₁ : S.left_homology_data) (h₂ : S.right_homology_data) :
  S.left_right_homology_comparison = h₁.left_homology_iso.hom ≫ left_right_homology_comparison' h₁ h₂ ≫
    h₂.right_homology_iso.inv :=
left_right_homology_comparison'_compatibility _ _ _ _

@[simp]
lemma left_right_homology_comparison'_eq_iso_hom (h : homology_data S) :
  left_right_homology_comparison' h.left h.right = h.iso.hom :=
by simp only [←cancel_epi h.left.π, ←cancel_mono h.right.ι,
    comp_left_right_homology_comparison'_comp, homology_data.comm]

instance is_iso_left_right_homology_comparison'_of_homology_data (h : homology_data S) :
  is_iso (left_right_homology_comparison' h.left h.right) :=
by { rw left_right_homology_comparison'_eq_iso_hom, apply_instance, }

instance is_iso_left_right_homology_comparison' [S.has_homology]
  (h₁ : S.left_homology_data) (h₂ : S.right_homology_data) :
  is_iso (left_right_homology_comparison' h₁ h₂) :=
begin
  rw left_right_homology_comparison'_compatibility h₁ S.some_homology_data.left h₂
    S.some_homology_data.right,
  apply_instance,
end

instance is_iso_left_right_homology_comparison [S.has_homology] :
  is_iso S.left_right_homology_comparison :=
by { change is_iso (left_right_homology_comparison' _ _), apply_instance, }

namespace right_homology_data

def homology_iso (h : S.right_homology_data) [S.has_homology] :
  S.homology ≅ h.H :=
as_iso (left_right_homology_comparison' S.some_homology_data.left h)

end right_homology_data

namespace homology_data

@[simps]
def of_is_iso_left_right_homology_comparison'
  (h₁ : S.left_homology_data) (h₂ : S.right_homology_data)
  [is_iso (left_right_homology_comparison' h₁ h₂)] :
  S.homology_data :=
{ left := h₁,
  right := h₂,
  iso := as_iso (left_right_homology_comparison' h₁ h₂),
  comm := by simp only [as_iso_hom, comp_left_right_homology_comparison'_comp], }

lemma has_homology_of_is_iso_left_right_homology_comparison'
  (h₁ : S.left_homology_data) (h₂ : S.right_homology_data)
  [is_iso (left_right_homology_comparison' h₁ h₂)] :
  S.has_homology :=
has_homology.mk' (of_is_iso_left_right_homology_comparison' h₁ h₂)

lemma has_homology_of_is_iso_left_right_homology_comparison [S.has_left_homology]
  [S.has_right_homology] [h : is_iso S.left_right_homology_comparison] :
  S.has_homology :=
begin
  haveI : is_iso (left_right_homology_comparison' S.some_left_homology_data
    S.some_right_homology_data) := h,
  exact has_homology_of_is_iso_left_right_homology_comparison' S.some_left_homology_data
    S.some_right_homology_data,
end

end homology_data

variable (S)

def left_homology_iso_homology [S.has_homology] :
  S.left_homology ≅ S.homology :=
S.some_left_homology_data.homology_iso.symm

def homology_iso_right_homology [S.has_homology] :
  S.homology ≅ S.right_homology :=
S.some_right_homology_data.homology_iso

variable {S}

lemma left_homology_map'_comp_iso_hom_comp_right_homology_map'
  (h : S.homology_data) (h₁ : S.left_homology_data) (h₂ : S.right_homology_data) :
  left_homology_map' (𝟙 S) h₁ h.left ≫ h.iso.hom ≫ right_homology_map' (𝟙 S) h.right h₂ =
    left_right_homology_comparison' h₁ h₂ :=
by simpa using (left_right_homology_comparison'_compatibility h₁ h.left h₂ h.right).symm

variable (S)

lemma left_right_homology_comparison_fac [S.has_homology] :
  S.left_right_homology_comparison =
    S.left_homology_iso_homology.hom ≫ S.homology_iso_right_homology.hom :=
begin
  have eq : S.some_homology_data.iso.hom ≫ right_homology_map' (𝟙 S) _ _ =
    S.homology_iso_right_homology.hom := by simpa only [left_homology_map'_id, id_comp]
    using left_homology_map'_comp_iso_hom_comp_right_homology_map' S.some_homology_data
      S.some_homology_data.left S.some_right_homology_data,
  simpa only [eq.symm] using (left_homology_map'_comp_iso_hom_comp_right_homology_map' _ _ _).symm,
end

variable (C)
/-- We shall say that a category with homology is a category for which
all short complexes have homology. -/
abbreviation _root_.category_with_homology := ∀ (S : short_complex C), S.has_homology

/-- Assuming that all short complexes have homology, this is the homology functor. -/
@[simps]
def homology_functor [category_with_homology C] :
  short_complex C ⥤ C :=
{ obj := λ S, S.homology,
  map := λ S₁ S₂, homology_map, }

instance (φ : S₁ ⟶ S₂) [S₁.has_homology] [S₂.has_homology]
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
  is_iso (homology_map φ) :=
by { dsimp only [homology_map, homology_map'], apply_instance, }

end short_complex


/-
@[simp]
lemma category_theory.limits.kernel_is_kernel_lift₀ {X Y A : C} (f : X ⟶ Y) (k : A ⟶ X)
  (w : k ≫ f = 0) [has_kernel f] :
  (kernel_is_kernel f).lift (kernel_fork.of_ι k w) = kernel.lift₀ f k w :=
  rfl

@[simp]
lemma category_theory.limits.cokernel_is_cokernel_desc₀ {X Y A : C} (f : X ⟶ Y) (k : Y ⟶ A)
  (w : f ≫ k = 0) [has_cokernel f] :
  (cokernel_is_cokernel f).desc (cokernel_cofork.of_π k w) = cokernel.desc₀ f k w := rfl

open category_theory.limits

namespace short_complex

variable (S : short_complex C)

section instances

variable [S.has_homology]

instance : has_kernel S.g :=
⟨nonempty.intro ⟨_, S.some_homology_full_data.hi⟩⟩

instance : has_cokernel S.f :=
⟨nonempty.intro ⟨_, S.some_homology_full_data.hp⟩⟩

instance : has_cokernel (kernel.lift₀ S.g S.f S.zero) :=
begin
  let h := S.some_homology_full_data,
  let f' := kernel.lift₀ S.g S.f S.zero,
  let e₁ := is_limit.cone_point_unique_up_to_iso (kernel_is_kernel _) h.hi,
  have hπ₀' : f' ≫ e₁.hom ≫ h.π = 0,
  { dsimp [e₁, is_limit.cone_point_unique_up_to_iso],
    rw ← assoc,
    convert h.hπ₀,
    rw [← cancel_mono h.i, assoc],
    erw h.hi.fac (kernel_fork.of_ι (kernel.ι S.g) (kernel.condition _))
      walking_parallel_pair.zero,
    dsimp [f'],
    rw kernel.lift₀_ι,
    symmetry,
    exact h.hi.fac _ walking_parallel_pair.zero, },
  refine ⟨nonempty.intro ⟨cokernel_cofork.of_π _ hπ₀', _⟩⟩,
  let e₂ : parallel_pair h.f' 0 ≅ parallel_pair f' 0,
  { refine parallel_pair.ext (iso.refl _) e₁.symm _ (by simp),
    dsimp [e₁, is_limit.cone_point_unique_up_to_iso],
    simp only [kernel_is_kernel_lift₀, id_comp, ← cancel_mono (kernel.ι S.g),
      assoc, kernel.lift₀_ι, h.f'_i], },
  equiv_rw (is_colimit.precompose_hom_equiv e₂ _).symm,
  refine is_colimit.of_iso_colimit h.hπ (cofork.ext (iso.refl _) _),
  change h.π ≫ 𝟙 _ = e₁.inv ≫ e₁.hom ≫ h.π,
  rw [comp_id, e₁.inv_hom_id_assoc],
end

instance : has_kernel (cokernel.desc₀ S.f S.g S.zero) :=
begin
  let h := S.some_homology_full_data,
  let g' := cokernel.desc₀ S.f S.g S.zero,
  let e₁ := is_colimit.cocone_point_unique_up_to_iso (cokernel_is_cokernel _) h.hp,
  have hι₀' : (h.ι ≫ e₁.inv) ≫ g' = 0,
  { dsimp [e₁, is_colimit.cocone_point_unique_up_to_iso],
    rw assoc,
    convert h.hι₀,
    rw [← cancel_epi h.p, ← assoc],
    erw h.hp.fac (cokernel_cofork.of_π (cokernel.π S.f) (cokernel.condition _))
      walking_parallel_pair.one,
    dsimp [g'],
    rw cokernel.π_desc₀,
    symmetry,
    exact h.hp.fac _ walking_parallel_pair.one, },
  refine ⟨nonempty.intro ⟨kernel_fork.of_ι _ hι₀', _⟩⟩,
  let e₂ : parallel_pair h.g' 0 ≅ parallel_pair g' 0,
  { refine parallel_pair.ext e₁.symm (iso.refl _) _ (by simp),
    dsimp [e₁, is_colimit.cocone_point_unique_up_to_iso],
    rw [comp_id, ← cancel_epi h.p, h.p_g'],
    erw h.hp.fac_assoc _ walking_parallel_pair.one,
    simp only [cofork.of_π_ι_app, cokernel.π_desc₀], },
  equiv_rw (is_limit.postcompose_hom_equiv e₂.symm _).symm,
  refine is_limit.of_iso_limit h.hι (fork.ext (iso.refl _) _),
  change 𝟙 _ ≫ ((h.ι ≫ e₁.inv) ≫ e₁.hom) = h.ι,
  simp only [assoc, iso.inv_hom_id, comp_id, id_comp],
end

end instances

variable [has_homology S]

def homology_lift {A : C} (f : A ⟶ S.X₂) (hf : f ≫ S.g = 0) :
  A ⟶ S.homology :=
S.some_homology_full_data.hi.lift (kernel_fork.of_ι f hf) ≫ S.some_homology_full_data.π

def homology_lift' (c : kernel_fork S.g) : c.X ⟶ S.homology :=
S.homology_lift c.ι (kernel_fork.condition _)

def homology_iso_cokernel_lift' (c : kernel_fork S.g) (hc : is_limit c)
  (c' : cokernel_cofork (hc.lift (kernel_fork.of_ι S.f S.zero))) (hc' : is_colimit c') :
  S.homology ≅ c'.X :=
{ hom := sorry,
  inv := begin
    have pif := S.homology_lift' c,
    have pif := hc'.desc (cokernel_cofork.of_π c'.π sorry),
    sorry,
  end,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }
#exit

def homology_iso_cokernel_lift :
  S.homology ≅ cokernel (kernel.lift₀ S.g S.f S.zero) :=
begin
  let e := S.homology_iso_cokernel_lift' _ (kernel_is_kernel S.g) _ (cokernel_is_cokernel _),
  exact e,
end

#exit

/-- The cokernel of `kernel.lift g f w`. This is isomorphic to `homology f g w`.
  See `homology_iso_cokernel_lift`. -/
abbreviation homology_c [has_homology S] : C :=
cokernel (kernel.lift S.g S.f S.zero)

/-- The kernel of `cokernel.desc f g w`. This is isomorphic to `homology f g w`.
  See `homology_iso_kernel_desc`. -/
abbreviation homology_k [has_homology S]: C :=
kernel (cokernel.desc S.f S.g S.zero)

/-- The canonical map from `homology_c` to `homology_k`.
  This is an isomorphism, and it is used in obtaining the API for `homology f g w`
  in the bottom of this file. -/
abbreviation homology_c_to_k [has_homology S] : S.homology_c ⟶ S.homology_k :=
cokernel.desc _ (kernel.lift _ (kernel.ι _ ≫ cokernel.π _) (by simp)) begin
  apply limits.equalizer.hom_ext,
  simp,
end

instance : is_iso (S.homology_c_to_k) :=
begin
  sorry,
end
#exit


end short_complex

-/
