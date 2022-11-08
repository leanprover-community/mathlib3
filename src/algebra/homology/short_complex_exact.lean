import algebra.homology.short_complex_homology
import algebra.homology.short_complex_preadditive
import category_theory.preadditive.opposite

open category_theory
open_locale zero_object

variables {C : Type*} [category C]

namespace category_theory.limits

lemma is_zero.op {X : C} (h : is_zero X) : is_zero (opposite.op X) :=
⟨λ Y, ⟨⟨⟨(h.from (opposite.unop Y)).op⟩, λ f, quiver.hom.unop_inj (h.eq_of_tgt _ _)⟩⟩,
  λ Y, ⟨⟨⟨(h.to (opposite.unop Y)).op⟩, λ f, quiver.hom.unop_inj (h.eq_of_src _ _)⟩⟩⟩

lemma is_zero.unop {X : Cᵒᵖ} (h : is_zero X) : is_zero (opposite.unop X) :=
⟨λ Y, ⟨⟨⟨(h.from (opposite.op Y)).unop⟩, λ f, quiver.hom.op_inj (h.eq_of_tgt _ _)⟩⟩,
  λ Y, ⟨⟨⟨(h.to (opposite.op Y)).unop⟩, λ f, quiver.hom.op_inj (h.eq_of_src _ _)⟩⟩⟩

instance [has_zero_object C] : has_zero_object Cᵒᵖ :=
⟨⟨opposite.op 0, is_zero.op (is_zero_zero C)⟩⟩

end category_theory.limits

open category_theory category_theory.category category_theory.limits

namespace short_complex

section

variable [has_zero_morphisms C]

variables (S : short_complex C) {S₁ S₂ : short_complex C}

def exact :=
(∃ (h : S.homology_data), is_zero h.left.H)

variable {S}

lemma homology_data.exact_iff (h : S.homology_data) :
  S.exact ↔ is_zero h.left.H :=
begin
  split,
  { rintro ⟨h₁, z⟩,
    exact is_zero.of_iso z (homology_map_iso' (iso.refl S) h h₁), },
  { intro z,
    exact ⟨h, z⟩, },
end

lemma homology_data.exact_iff' (h : S.homology_data) :
  S.exact ↔ is_zero h.right.H :=
begin
  suffices : is_zero h.left.H ↔ is_zero h.right.H,
  { exact h.exact_iff.trans this, },
  exact ⟨λ z, is_zero.of_iso z h.iso.symm,
    λ z, is_zero.of_iso z h.iso⟩,
end

variable (S)

lemma exact_iff_is_zero_homology [S.has_homology] :
  S.exact ↔ is_zero S.homology :=
by apply homology_data.exact_iff

variable {S}

lemma left_homology_data.exact_iff (h : S.left_homology_data) [S.has_homology] :
  S.exact ↔ is_zero h.H :=
S.exact_iff_is_zero_homology.trans
  ⟨λ z, is_zero.of_iso z h.homology_iso.symm, λ z, is_zero.of_iso z h.homology_iso⟩

lemma right_homology_data.exact_iff (h : S.right_homology_data) [S.has_homology] :
  S.exact ↔ is_zero h.H :=
S.exact_iff_is_zero_homology.trans
  ⟨λ z, is_zero.of_iso z h.homology_iso.symm, λ z, is_zero.of_iso z h.homology_iso⟩

variable (S)

lemma exact_iff_is_zero_left_homology [S.has_homology] :
  S.exact ↔ is_zero S.left_homology :=
by apply left_homology_data.exact_iff

lemma exact_iff_is_zero_right_homology [S.has_homology] :
  S.exact ↔ is_zero S.right_homology :=
by apply right_homology_data.exact_iff

lemma exact_of_is_zero_X₂ (h : is_zero S.X₂) : S.exact :=
begin
  rw (homology_data.of_zeros S (is_zero.eq_of_tgt h _ _) (is_zero.eq_of_src h _ _)).exact_iff,
  exact h,
end

lemma exact_iff_of_iso (e : S₁ ≅ S₂) : S₁.exact ↔ S₂.exact :=
begin
  suffices : ∀ ⦃S₁ S₂ : short_complex C⦄ (e : S₁ ≅ S₂), S₁.exact → S₂.exact,
  { exact ⟨this e, this e.symm⟩, },
  rintros S₁ S₂ e h,
  haveI := has_homology.mk' h.some,
  haveI := has_homology_of_iso e,
  rw exact_iff_is_zero_homology at ⊢ h,
  exact is_zero.of_iso h (homology_map_iso e.symm),
end

lemma exact_iff_of_epi_of_is_iso_of_mono (φ : S₁ ⟶ S₂) [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
  S₁.exact ↔ S₂.exact :=
begin
  split,
  { rintro ⟨h₁, z₁⟩,
    exact ⟨homology_data.of_epi_of_is_iso_of_mono φ h₁, z₁⟩, },
  { rintro ⟨h₁, z₁⟩,
    exact ⟨homology_data.of_epi_of_is_iso_of_mono' φ h₁, z₁⟩, },
end

lemma exact_iff_op : S.exact ↔ S.op.exact :=
begin
  split,
  { rintro ⟨h, z⟩,
    exact ⟨h.op, (is_zero.of_iso z h.iso.symm).op⟩, },
  { rintro ⟨h, z⟩,
    refine ⟨h.unop, (is_zero.of_iso z h.iso.symm).unop⟩, },
end

lemma exact_iff_unop (S : short_complex Cᵒᵖ) : S.exact ↔ S.unop.exact :=
begin
  rw S.unop.exact_iff_op,
  exact exact_iff_of_iso S.unop_op.symm,
end

end

section preadditive

variables [preadditive C] {S₁ S₂ : short_complex C}

lemma homotopy_equiv.exact_iff (e : homotopy_equiv S₁ S₂) [S₁.has_homology] [S₂.has_homology] :
  S₁.exact ↔ S₂.exact :=
begin
  simp only [exact_iff_is_zero_homology],
  exact ⟨λ h, is_zero.of_iso h e.homology_iso.symm, λ h, is_zero.of_iso h e.homology_iso⟩,
end

lemma exact_iff_mono [has_zero_object C] (S : short_complex C) (hf : S.f = 0) :
  S.exact ↔ mono S.g :=
begin
  split,
  { intro h,
    haveI : S.has_homology := has_homology.mk' h.some,
    rw exact_iff_is_zero_homology at h,
    haveI : is_iso S.p_cycles_co := S.is_iso_p_cycles_co_of hf,
    haveI : mono S.from_cycles_co := mono_of_is_zero_ker _ S.homology_is_kernel h,
    rw ← S.p_from_cycles_co,
    apply mono_comp, },
  { introI,
    have h : is_limit (kernel_fork.of_ι (0 : 0 ⟶ S.X₂) (zero_comp : _ ≫ S.g = 0)) :=
      kernel_fork.is_limit.of_ι _ _
        (λ A x hx, 0) (λ A x hx, by simp only [← cancel_mono S.g, zero_comp, hx])
        (λ A x hx b hb, is_zero.eq_of_tgt (is_zero_zero _) _ _),
    exact ⟨homology_data.of_limit_kernel_fork S hf _ h, is_zero_zero _⟩, },
end

lemma exact_iff_epi [has_zero_object C] (S : short_complex C) (hg : S.g = 0) :
  S.exact ↔ epi S.f :=
begin
  rw [S.exact_iff_op, S.op.exact_iff_mono (by simp only [hg, op_f, op_zero])],
  dsimp,
  split,
  { introI,
    change epi (S.f.op.unop),
    apply_instance, },
  { introI,
    apply_instance, },
end

end preadditive

end short_complex
