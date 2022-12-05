import algebra.homology.short_complex.exact
import algebra.homology.short_complex.preadditive
import algebra.homology.short_complex.preserves_homology

noncomputable theory

namespace category_theory

open category limits
open_locale zero_object

namespace short_complex

variables {C D : Type*} [category C] [category D]

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

lemma map_of_exact (hS : S.short_exact) [has_zero_morphisms D]
  (F : C ⥤ D) [F.preserves_zero_morphisms] [preserves_finite_limits F]
  [preserves_finite_colimits F] : (S.map F).short_exact :=
begin
  haveI := hS.mono_f,
  haveI := hS.epi_g,
  haveI : mono (S.map F).f := preserves_mono_of_preserves_limit F S.f,
  haveI : epi (S.map F).g := preserves_epi_of_preserves_colimit F S.g,
  exact short_exact.mk (exact_map_of_preserves_homology hS.exact F),
end

end short_exact

end

section preadditive

variables [preadditive C] [preadditive D] {S : short_complex C}

lemma splitting.short_exact [has_zero_object C] (s : S.splitting) :
  S.short_exact :=
begin
  haveI := s.mono_f,
  haveI := s.epi_g,
  exact ⟨s.exact⟩,
end

namespace exact

def f_is_kernel (hS : S.exact) [mono S.f] [balanced C] :
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

def g_is_cokernel (hS : S.exact) [epi S.g] [balanced C] :
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

lemma of_f_is_kernel [mono S.f] [S.has_homology]
  (hS : is_limit (kernel_fork.of_ι S.f S.zero)) :
  S.exact :=
begin
  rw exact_iff_epi_to_cycles,
  haveI : is_split_epi S.to_cycles,
  { refine is_split_epi.mk' _,
    refine split_epi.mk (hS.lift (kernel_fork.of_ι S.cycles_i S.cycles_i_g)) _,
    rw ← cancel_mono S.cycles_i,
    dsimp,
    simp only [assoc, to_cycles_i, id_comp],
    apply fork.is_limit.lift_ι, },
  apply is_split_epi.epi,
end

lemma of_g_is_cokernel [epi S.g] [S.has_homology]
  (hS : is_colimit (cokernel_cofork.of_π S.g S.zero)) :
  S.exact :=
begin
  rw exact_iff_mono_from_cycles_co,
  haveI : is_split_mono S.from_cycles_co,
  { refine is_split_mono.mk' _,
    refine split_mono.mk (hS.desc (cokernel_cofork.of_π S.p_cycles_co S.f_cycles_co_p)) _,
    rw ← cancel_epi S.p_cycles_co,
    dsimp,
    simp only [p_from_cycles_co_assoc, comp_id],
    apply cofork.is_colimit.π_desc hS, },
  apply is_split_mono.mono,
end

def lift (hS : S.exact) {A : C} [balanced C] [mono S.f]
  (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ S.X₁ :=
hS.f_is_kernel.lift (kernel_fork.of_ι k hk)

@[simp, reassoc]
lemma lift_f (hS : S.exact) {A : C} [balanced C] [mono S.f]
  (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) :
  hS.lift k hk ≫ S.f = k :=
fork.is_limit.lift_ι _

def desc (hS : S.exact) {A : C} [balanced C] [epi S.g]
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : S.X₃ ⟶ A :=
hS.g_is_cokernel.desc (cokernel_cofork.of_π k hk)

@[simp, reassoc]
lemma g_desc (hS : S.exact) {A : C} [balanced C] [epi S.g]
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) :
  S.g ≫ hS.desc k hk = k :=
cofork.is_colimit.π_desc (hS.g_is_cokernel)

end exact

namespace short_exact

def lift (hS : S.short_exact) {A : C} [balanced C]
  (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ S.X₁ :=
by { haveI := hS.mono_f, exact hS.exact.lift k hk, }

@[simp, reassoc]
lemma lift_f (hS : S.short_exact) {A : C} [balanced C]
  (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) :
  hS.lift k hk ≫ S.f = k :=
by apply exact.lift_f

def desc (hS : S.short_exact) {A : C} [balanced C]
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : S.X₃ ⟶ A :=
by { haveI := hS.epi_g, exact hS.exact.desc k hk, }

@[simp, reassoc]
lemma g_desc (hS : S.short_exact) {A : C} [balanced C]
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) :
  S.g ≫ hS.desc k hk = k :=
by apply exact.g_desc

end short_exact

namespace exact

lemma map_of_mono_f {S : short_complex C} (h : S.exact) [mono S.f]
  (F : C ⥤ D) [F.preserves_zero_morphisms] [balanced C]
  [(S.map F).has_homology] [mono (F.map S.f)] [preserves_limit (parallel_pair S.g 0) F]:
  (S.map F).exact :=
begin
  haveI : mono (S.map F).f := (infer_instance : mono (F.map S.f)),
  apply exact.of_f_is_kernel,
  equiv_rw (is_limit.postcompose_inv_equiv (parallel_pair.comp_nat_iso F S.g) _).symm,
  refine is_limit.of_iso_limit (is_limit_of_preserves F h.f_is_kernel) _,
  refine cones.ext (iso.refl _) _,
  rintros (_|_),
  { dsimp, simp only [comp_id, id_comp], },
  { dsimp, simp only [F.map_zero, comp_id, id_comp, ← F.map_comp, S.zero], }
end

lemma map_of_epi_g {S : short_complex C} (h : S.exact) [epi S.g]
  (F : C ⥤ D) [F.preserves_zero_morphisms] [balanced C]
  [(S.map F).has_homology] [epi (F.map S.g)] [preserves_colimit (parallel_pair S.f 0) F]:
  (S.map F).exact :=
begin
  haveI : epi (S.map F).g := (infer_instance : epi (F.map S.g)),
  apply exact.of_g_is_cokernel,
  equiv_rw (is_colimit.precompose_hom_equiv (parallel_pair.comp_nat_iso F S.f) _).symm,
  refine is_colimit.of_iso_colimit (is_colimit_of_preserves F h.g_is_cokernel) _,
  refine cocones.ext (iso.refl _) _,
  rintros (_|_),
  { dsimp, simp only [zero, F.map_zero, ← F.map_comp, id_comp, comp_id], },
  { dsimp, simp only [comp_id, id_comp], },
end

end exact

end preadditive

end short_complex

end category_theory
