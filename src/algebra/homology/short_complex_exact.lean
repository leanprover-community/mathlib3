import algebra.homology.short_complex_homology
import algebra.homology.short_complex_abelian
import algebra.homology.short_complex_preserves_homology
import category_theory.preadditive.opposite

noncomputable theory

open category_theory category_theory.preadditive
open_locale zero_object

variables {C D : Type*} [category C] [category D]

namespace category_theory.limits

lemma is_zero.op {X : C} (h : is_zero X) : is_zero (opposite.op X) :=
⟨λ Y, ⟨⟨⟨(h.from (opposite.unop Y)).op⟩, λ f, quiver.hom.unop_inj (h.eq_of_tgt _ _)⟩⟩,
  λ Y, ⟨⟨⟨(h.to (opposite.unop Y)).op⟩, λ f, quiver.hom.unop_inj (h.eq_of_src _ _)⟩⟩⟩

lemma is_zero.unop {X : Cᵒᵖ} (h : is_zero X) : is_zero (opposite.unop X) :=
⟨λ Y, ⟨⟨⟨(h.from (opposite.op Y)).unop⟩, λ f, quiver.hom.op_inj (h.eq_of_tgt _ _)⟩⟩,
  λ Y, ⟨⟨⟨(h.to (opposite.op Y)).unop⟩, λ f, quiver.hom.op_inj (h.eq_of_src _ _)⟩⟩⟩

lemma is_zero.iff_of_iso {X Y : C} (e : X ≅ Y) :
  is_zero X ↔ is_zero Y :=
begin
  split,
  { exact λ h, is_zero.of_iso h e.symm, },
  { exact λ h, is_zero.of_iso h e, },
end

instance [has_zero_object C] : has_zero_object Cᵒᵖ :=
⟨⟨opposite.op 0, is_zero.op (is_zero_zero C)⟩⟩

end category_theory.limits

open category_theory category_theory.category category_theory.limits

namespace short_complex

section

variables [has_zero_morphisms C] [has_zero_morphisms D]
  (S : short_complex C) {S₁ S₂ : short_complex C}

def exact :=
(∃ (h : S.homology_data), is_zero h.left.H)

variable {S}

lemma exact.has_homology (h : S.exact) : has_homology S :=
has_homology.mk' h.some

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

lemma exact_iff_homology_zero [S.has_homology] [has_zero_object C] :
  S.exact ↔ nonempty (S.homology ≅ 0) :=
begin
  rw exact_iff_is_zero_homology,
  split,
  { exact λ h, ⟨h.iso_zero⟩, },
  { exact λ e, is_zero.of_iso (is_zero_zero C) e.some, },
end

variable {S}

lemma left_homology_data.exact_iff (h : S.left_homology_data) [S.has_homology] :
  S.exact ↔ is_zero h.H :=
S.exact_iff_is_zero_homology.trans
  ⟨λ z, is_zero.of_iso z h.homology_iso.symm, λ z, is_zero.of_iso z h.homology_iso⟩

lemma right_homology_data.exact_iff (h : S.right_homology_data) [S.has_homology] :
  S.exact ↔ is_zero h.H :=
S.exact_iff_is_zero_homology.trans
  ⟨λ z, is_zero.of_iso z h.homology_iso.symm, λ z, is_zero.of_iso z h.homology_iso⟩

lemma left_homology_data.exact_map_iff (h : S.left_homology_data) (F : C ⥤ D)
  [F.preserves_zero_morphisms] [h.is_preserved_by F] [(S.map F).has_homology]:
  (S.map F).exact ↔ is_zero (F.obj h.H) :=
(h.map F).exact_iff

lemma right_homology_data.exact_map_iff (h : S.right_homology_data) (F : C ⥤ D)
  [F.preserves_zero_morphisms] [h.is_preserved_by F] [(S.map F).has_homology]:
  (S.map F).exact ↔ is_zero (F.obj h.H) :=
(h.map F).exact_iff

lemma homology_data.exact_iff_i_p_zero (h : S.homology_data) :
  S.exact ↔ h.left.i ≫ h.right.p = 0 :=
begin
  haveI : S.has_homology := has_homology.mk' h,
  rw [h.left.exact_iff, ← h.comm],
  split,
  { intro h',
    simp only [h'.eq_of_src h.iso.hom 0, zero_comp, comp_zero], },
  { intro eq,
    rw [is_zero.iff_id_eq_zero, ← cancel_mono h.iso.hom, id_comp,
      ← cancel_mono h.right.ι, ← cancel_epi h.left.π, zero_comp, zero_comp, comp_zero, eq], },
end

lemma exact_map_of_preserves_homology (hS : S.exact)
  (F : C ⥤ D) [F.preserves_zero_morphisms] [F.preserves_left_homology_of S]
  [F.preserves_right_homology_of S] : (S.map F).exact :=
begin
  haveI : S.has_homology := hS.has_homology,
  let h := S.some_homology_data,
  haveI := functor.preserves_left_homology_of.condition F S,
  haveI := functor.preserves_right_homology_of.condition F S,
  rw [h.exact_iff, is_zero.iff_id_eq_zero] at hS,
  simpa only [(h.map F).exact_iff, is_zero.iff_id_eq_zero,
    category_theory.functor.map_id, functor.map_zero] using F.congr_map hS,
end

variable (S)

lemma exact_map_iff_of_preserves_homology [S.has_homology]
  (F : C ⥤ D) [F.preserves_zero_morphisms] [F.preserves_left_homology_of S]
  [F.preserves_right_homology_of S] [faithful F] :
  (S.map F).exact ↔ S.exact :=
begin
  let h := S.some_homology_data,
  have e : F.map (𝟙 h.left.H) = 0 ↔ (𝟙 h.left.H) = 0,
  { split,
    { intro eq,
      apply F.map_injective,
      rw [eq, F.map_zero], },
    { intro eq,
      rw [eq, F.map_zero], }, },
  haveI := functor.preserves_left_homology_of.condition F S,
  haveI := functor.preserves_right_homology_of.condition F S,
  simpa only [h.exact_iff, is_zero.iff_id_eq_zero, (h.map F).exact_iff,
    F.map_id] using e,
end

lemma exact_iff_is_zero_left_homology [S.has_homology] :
  S.exact ↔ is_zero S.left_homology :=
by apply left_homology_data.exact_iff

lemma exact_iff_is_zero_right_homology [S.has_homology] :
  S.exact ↔ is_zero S.right_homology :=
by apply right_homology_data.exact_iff

lemma exact_iff_i_p_zero [S.has_homology] (h₁ : S.left_homology_data)
  (h₂ : S.right_homology_data) :
  S.exact ↔ h₁.i ≫ h₂.p = 0 :=
(homology_data.of_is_iso_left_right_homology_comparison' h₁ h₂).exact_iff_i_p_zero

lemma exact_iff_cycles_i_p_cycles_co_zero [S.has_homology] :
  S.exact ↔ S.cycles_i ≫ S.p_cycles_co = 0 :=
S.exact_iff_i_p_zero _ _

lemma exact_iff_kernel_ι_comp_cokernel_π_zero [S.has_homology]
  [has_kernel S.g] [has_cokernel S.f] :
  S.exact ↔ kernel.ι S.g ≫ cokernel.π S.f = 0 :=
begin
  haveI := has_left_homology.has_cokernel S,
  haveI := has_right_homology.has_kernel S,
  exact S.exact_iff_i_p_zero (left_homology_data.of_ker_of_coker S)
    (right_homology_data.of_coker_of_ker S),
end

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
  haveI := h.has_homology,
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

variable {S}

lemma exact.comp_eq_zero (h : S.exact) {X Y : C} {ι : X ⟶ S.X₂} (hι : ι ≫ S.g = 0)
  {π : S.X₂ ⟶ Y} (hπ : S.f ≫ π = 0) : ι ≫ π = 0 :=
begin
  haveI : S.has_homology := h.has_homology,
  rw exact_iff_cycles_i_p_cycles_co_zero at h,
  rw [← S.lift_cycles_i ι hι, ← S.p_desc_cycles_co π hπ, assoc,
    reassoc_of h, zero_comp, comp_zero],
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

variable (S : short_complex C)

structure splitting (S : short_complex C) :=
(r : S.X₂ ⟶ S.X₁)
(s : S.X₃ ⟶ S.X₂)
(f_r : S.f ≫ r = 𝟙 _)
(s_g : s ≫ S.g = 𝟙 _)
(id : r ≫ S.f + S.g ≫ s = 𝟙 _)

namespace splitting

attribute [reassoc] f_r s_g

variable {S}

@[simps] def split_mono_f (s : S.splitting) : split_mono S.f := ⟨s.r, s.f_r⟩
lemma is_split_mono_f (s : S.splitting) : is_split_mono S.f := ⟨⟨s.split_mono_f⟩⟩
lemma mono_f (s : S.splitting) : mono S.f := by { haveI := s.is_split_mono_f, apply_instance, }

@[simps] def split_epi_g (s : S.splitting) : split_epi S.g := ⟨s.s, s.s_g⟩
lemma is_split_epi_g (s : S.splitting) : is_split_epi S.g := ⟨⟨s.split_epi_g⟩⟩
lemma epi_g (s : S.splitting) : epi S.g := by { haveI := s.is_split_epi_g, apply_instance, }

@[simp]
def left_homology_data [has_zero_object C] (s : S.splitting) :
  left_homology_data S :=
begin
  have hi := kernel_fork.is_limit.of_ι S.f S.zero (λ A x hx, x ≫ s.r)
    (λ A x hx, by { conv_rhs { rw [← comp_id x, ← s.id, comp_add, reassoc_of hx,
      zero_comp, add_zero, ← assoc], }, })
    (λ A x hx b hb, by { dsimp, rw [← hb, assoc, s.f_r, comp_id], }),
  let f' := hi.lift (kernel_fork.of_ι S.f S.zero),
  have hf' : f' = 𝟙 _,
  { apply kernel_fork.is_limit.hom_ext hi,
    simp only [fork.is_limit.lift_ι, id_comp], },
  have hπ₀ : f' ≫ (0 : _ ⟶ 0) = 0 := comp_zero,
  have hπ := cokernel_cofork.is_colimit.of_π 0 hπ₀
    (λ A x hx, 0)
    (λ A x hx, begin
      dsimp,
      rw [hf', id_comp] at hx,
      rw [hx, comp_zero],
    end)
    (λ A x hx b hb, is_zero.eq_of_src (is_zero_zero _) _ _),
  exact ⟨S.X₁, 0, S.f, 0, S.zero, hi, hπ₀, hπ⟩,
end

@[simp]
def right_homology_data [has_zero_object C] (s : S.splitting) :
  right_homology_data S :=
begin
  have hp := cokernel_cofork.is_colimit.of_π S.g S.zero (λ A x hx, s.s ≫ x)
    (λ A x hx, by { dsimp, conv_rhs { rw [← id_comp x, ← s.id, add_comp, assoc,
      hx, comp_zero, zero_add, assoc], }, })
  (λ A x hx b hb, by { dsimp, rw [← hb, s.s_g_assoc], }),
  let g' := hp.desc (cokernel_cofork.of_π S.g S.zero),
  have hg' : g' = 𝟙 _,
  { apply cokernel_cofork.is_colimit.hom_ext hp,
    simp only [cofork.is_colimit.π_desc],
    erw comp_id, },
  have hι₀ : (0 : 0 ⟶ _) ≫ g' = 0 := zero_comp,
  have hι := kernel_fork.is_limit.of_ι 0 hι₀
    (λ A x hx, 0)
    (λ A x hx, begin
      dsimp,
      rw [hg', comp_id] at hx,
      rw [hx, zero_comp],
    end)
    (λ A x hx b hb, is_zero.eq_of_tgt (is_zero_zero _) _ _),
  exact ⟨S.X₃, 0, S.g, 0, S.zero, hp, hι₀, hι⟩,
end

@[simps]
def homology_data [has_zero_object C] (s : S.splitting) :
  homology_data S :=
{ left := s.left_homology_data,
  right := s.right_homology_data,
  iso := iso.refl 0,
  comm := by tidy, }

lemma exact [has_zero_object C] (s : S.splitting) : S.exact :=
⟨s.homology_data, is_zero_zero _⟩

end splitting

end preadditive

end short_complex
