import algebra.homology.short_complex.exact
import algebra.homology.short_complex.preadditive

noncomputable theory

open category_theory category_theory.category category_theory.limits
open_locale zero_object

namespace short_complex

variables {C : Type*} [category C]

section

variables [has_zero_morphisms C] (S : short_complex C) {S₁ S₂ : short_complex C}

structure short_exact : Prop :=
[mono_f : mono S.f]
[epi_g  : epi S.g]
(exact  : S.exact)

local attribute [instance] mono_comp epi_comp

namespace short_exact

variable {S}

lemma of_iso (e : S₁ ≅ S₂) (h : S₁.short_exact) : S₂.short_exact :=
begin
  haveI := h.mono_f,
  haveI := h.epi_g,
  have eq₁ : S₂.f = e.inv.τ₁ ≫ S₁.f ≫ e.hom.τ₂,
  { simp only [← e.hom.comm₁₂, ← comp_τ₁_assoc, e.inv_hom_id, id_τ₁, id_comp], },
  have eq₂ : S₂.g = e.inv.τ₂ ≫ S₁.g ≫ e.hom.τ₃,
  { simp only [← e.hom.comm₂₃, ← comp_τ₂_assoc, e.inv_hom_id, id_τ₂, id_comp], },
  haveI : mono S₂.f := by { rw eq₁, apply_instance, },
  haveI : epi S₂.g := by { rw eq₂, apply_instance, },
  constructor,
  simpa only [exact_iff_of_iso e.symm] using h.exact,
end

lemma iff_of_iso (e : S₁ ≅ S₂) : S₁.short_exact ↔ S₂.short_exact :=
begin
  split,
  { exact short_exact.of_iso e, },
  { exact short_exact.of_iso e.symm, },
end

variable {S}

lemma op (h : S.short_exact) : S.op.short_exact :=
begin
  haveI := h.mono_f,
  haveI := h.epi_g,
  haveI : mono S.op.f := (infer_instance : mono S.g.op),
  haveI : epi S.op.g := (infer_instance : epi S.f.op),
  exact ⟨h.exact.op⟩,
end

lemma unop (h : S.op.short_exact) : S.short_exact :=
begin
  haveI : mono S.g.op := h.mono_f,
  haveI : epi S.f.op := h.epi_g,
  haveI : mono S.f := (infer_instance : mono S.f.op.unop),
  haveI : epi S.g := (infer_instance : epi S.g.op.unop),
  exact ⟨h.exact.unop⟩,
end

lemma op' {S : short_complex Cᵒᵖ}
  (h : S.unop.short_exact) : S.short_exact :=
begin
  haveI : mono S.g.unop := h.mono_f,
  haveI : epi S.f.unop := h.epi_g,
  haveI : mono S.f := (infer_instance : mono S.f.unop.op),
  haveI : epi S.g := (infer_instance : epi S.g.unop.op),
  exact ⟨h.exact.op'⟩,
end

lemma unop' {S : short_complex Cᵒᵖ} (h : S.short_exact) : S.unop.short_exact :=
begin
  haveI := h.mono_f,
  haveI := h.epi_g,
  haveI : mono S.unop.f := (infer_instance : mono S.g.unop),
  haveI : epi S.unop.g := (infer_instance : epi S.f.unop),
  exact ⟨h.exact.unop'⟩,
end

end short_exact

end

section preadditive

variables [preadditive C] {S : short_complex C}

lemma splitting.short_exact [has_zero_object C] (s : S.splitting) :
  S.short_exact :=
begin
  haveI := s.mono_f,
  haveI := s.epi_g,
  exact ⟨s.exact⟩,
end

def exact.f_is_kernel (hS : S.exact) [mono S.f] [balanced C] :
  is_limit (kernel_fork.of_ι S.f S.zero) :=
begin
  haveI : S.has_homology := hS.has_homology,
  let h := S.some_left_homology_data,
  rw h.exact_iff at hS,
  haveI : mono (h.f' ≫ h.i),
  { rw h.f'_i,
    apply_instance, },
  haveI : mono h.f' := mono_of_mono h.f' h.i,
  haveI : epi h.f':= epi_of_is_zero_cokernel' _ h.hπ hS,
  haveI := is_iso_of_mono_of_epi h.f',
  exact is_limit.of_iso_limit h.hi (fork.ext (as_iso h.f').symm (by simp)),
end

def exact.g_is_cokernel (hS : S.exact) [epi S.g] [balanced C] :
  is_colimit (cokernel_cofork.of_π S.g S.zero) :=
begin
  haveI : S.has_homology := hS.has_homology,
  let h := S.some_right_homology_data,
  rw h.exact_iff at hS,
  haveI : epi (h.p ≫ h.g'),
  { rw h.p_g',
    apply_instance, },
  haveI : epi h.g' := epi_of_epi h.p h.g',
  haveI : mono h.g':= mono_of_is_zero_kernel' _ h.hι hS,
  haveI := is_iso_of_mono_of_epi h.g',
  exact is_colimit.of_iso_colimit h.hp (cofork.ext (as_iso h.g') (by simp)),
end

namespace short_exact

def lift (hS : S.short_exact) {A : C} [balanced C]
  (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ S.X₁ :=
begin
  haveI := hS.mono_f,
  exact hS.exact.f_is_kernel.lift (kernel_fork.of_ι k hk),
end

@[simp, reassoc]
lemma lift_f (hS : S.short_exact) {A : C} [balanced C]
  (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) :
  hS.lift k hk ≫ S.f = k :=
fork.is_limit.lift_ι _

def desc (hS : S.short_exact) {A : C} [balanced C]
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : S.X₃ ⟶ A :=
begin
  haveI := hS.epi_g,
  exact hS.exact.g_is_cokernel.desc (cokernel_cofork.of_π k hk),
end

@[simp, reassoc]
lemma g_desc (hS : S.short_exact) {A : C} [balanced C]
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) :
  S.g ≫ hS.desc k hk = k :=
begin
  haveI := hS.epi_g,
  apply cofork.is_colimit.π_desc (hS.exact.g_is_cokernel),
end

end short_exact

end preadditive

end short_complex
