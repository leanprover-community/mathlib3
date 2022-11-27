import algebra.homology.short_complex.limits
import algebra.homology.short_complex.pseudoelements
import category_theory.limits.preserves.shapes.kernels

noncomputable theory

open category_theory category_theory.limits category_theory.category
  category_theory.preadditive

variables (C : Type*) [category C] [abelian C]

open category_theory

namespace short_complex

structure snake_input :=
(L₀ L₁ L₂ L₃ : short_complex C)
(v₀₁ : L₀ ⟶ L₁)
(v₁₂ : L₁ ⟶ L₂)
(v₂₃ : L₂ ⟶ L₃)
(w₀₂' : v₀₁ ≫ v₁₂ = 0 . obviously)
(w₁₃' : v₁₂ ≫ v₂₃ = 0 . obviously)
(h₀ : is_limit (kernel_fork.of_ι _ w₀₂'))
(h₃ : is_colimit (cokernel_cofork.of_π _ w₁₃'))
(epi_L₁_g : epi L₁.g)
(L₁_exact  : L₁.exact)
(mono_L₂_f : mono L₂.f)
(L₂_exact : L₂.exact)

namespace snake_input

restate_axiom w₀₂'
restate_axiom w₁₃'
attribute [simp, reassoc] w₀₂ w₁₃

variables {C} (S : snake_input C)

attribute [instance] epi_L₁_g
attribute [instance] mono_L₂_f

@[simp, reassoc] lemma w₀₂_τ₁ : S.v₀₁.τ₁ ≫ S.v₁₂.τ₁ = 0 := by rw [← comp_τ₁, S.w₀₂, zero_τ₁]
@[simp, reassoc] lemma w₀₂_τ₂ : S.v₀₁.τ₂ ≫ S.v₁₂.τ₂ = 0 := by rw [← comp_τ₂, S.w₀₂, zero_τ₂]
@[simp, reassoc] lemma w₀₂_τ₃ : S.v₀₁.τ₃ ≫ S.v₁₂.τ₃ = 0 := by rw [← comp_τ₃, S.w₀₂, zero_τ₃]
@[simp, reassoc] lemma w₁₃_τ₁ : S.v₁₂.τ₁ ≫ S.v₂₃.τ₁ = 0 := by rw [← comp_τ₁, S.w₁₃, zero_τ₁]
@[simp, reassoc] lemma w₁₃_τ₂ : S.v₁₂.τ₂ ≫ S.v₂₃.τ₂ = 0 := by rw [← comp_τ₂, S.w₁₃, zero_τ₂]
@[simp, reassoc] lemma w₁₃_τ₃ : S.v₁₂.τ₃ ≫ S.v₂₃.τ₃ = 0 := by rw [← comp_τ₃, S.w₁₃, zero_τ₃]

def h₀_τ₁ : is_limit (kernel_fork.of_ι S.v₀₁.τ₁ S.w₀₂_τ₁) :=
is_limit_fork_map_of_is_limit' π₁ S.w₀₂ S.h₀
def h₀_τ₂ : is_limit (kernel_fork.of_ι S.v₀₁.τ₂ S.w₀₂_τ₂) :=
is_limit_fork_map_of_is_limit' π₂ S.w₀₂ S.h₀
def h₀_τ₃ : is_limit (kernel_fork.of_ι S.v₀₁.τ₃ S.w₀₂_τ₃) :=
is_limit_fork_map_of_is_limit' π₃ S.w₀₂ S.h₀

instance mono_v₀₁_τ₁ : mono S.v₀₁.τ₁ := fork.is_limit.mono_ι S.h₀_τ₁
instance mono_v₀₁_τ₂ : mono S.v₀₁.τ₂ := fork.is_limit.mono_ι S.h₀_τ₂
instance mono_v₀₁_τ₃ : mono S.v₀₁.τ₃ := fork.is_limit.mono_ι S.h₀_τ₃

lemma C₁_up_exact : (short_complex.mk S.v₀₁.τ₁ S.v₁₂.τ₁
  (by rw [← comp_τ₁, S.w₀₂, zero_τ₁])).exact :=
exact.of_f_is_kernel S.h₀_τ₁
lemma C₂_up_exact : (short_complex.mk S.v₀₁.τ₂ S.v₁₂.τ₂
  (by rw [← comp_τ₂, S.w₀₂, zero_τ₂])).exact :=
exact.of_f_is_kernel S.h₀_τ₂
lemma C₃_up_exact : (short_complex.mk S.v₀₁.τ₃ S.v₁₂.τ₃
  (by rw [← comp_τ₃, S.w₀₂, zero_τ₃])).exact :=
exact.of_f_is_kernel S.h₀_τ₃

instance mono_L₀_f [mono S.L₁.f] : mono S.L₀.f :=
begin
  haveI : mono (S.L₀.f ≫ S.v₀₁.τ₂),
  { rw ← S.v₀₁.comm₁₂,
    apply mono_comp, },
  exact mono_of_mono _ S.v₀₁.τ₂,
end

def is_limit_kernel_fork_L₀ [mono S.L₁.f] :
  is_limit (kernel_fork.of_ι _ S.L₀.zero) :=
kernel_fork.is_limit.of_ι _ _
  (λ A x hx, S.h₀_τ₁.lift
    (kernel_fork.of_ι (S.L₁_exact.lift (x ≫ S.v₀₁.τ₂)
      (by rw [assoc, S.v₀₁.comm₂₃, reassoc_of hx, zero_comp]))
      (by simp only [← cancel_mono S.L₂.f, assoc, S.v₁₂.comm₁₂, zero_comp,
          exact.lift_f_assoc, w₀₂_τ₂, comp_zero])))
  (λ A x hx, begin
    simp only [← cancel_mono S.v₀₁.τ₂, assoc, ← S.v₀₁.comm₁₂],
    erw fork.is_limit.lift_ι_assoc,
    simp only [kernel_fork.ι_of_ι, exact.lift_f],
  end)
  (λ A x hx b hb, by erw [← cancel_mono S.L₀.f, hb, ← cancel_mono S.v₀₁.τ₂, assoc,
    ← S.v₀₁.comm₁₂, fork.is_limit.lift_ι_assoc, kernel_fork.ι_of_ι, exact.lift_f])

lemma ex₀ [mono S.L₁.f] : S.L₀.exact := exact.of_f_is_kernel (S.is_limit_kernel_fork_L₀)

def h₃_τ₁ : is_colimit (cokernel_cofork.of_π S.v₂₃.τ₁ S.w₁₃_τ₁) :=
is_colimit_cofork_map_of_is_colimit' π₁ S.w₁₃ S.h₃
def h₃_τ₂ : is_colimit (cokernel_cofork.of_π S.v₂₃.τ₂ S.w₁₃_τ₂) :=
is_colimit_cofork_map_of_is_colimit' π₂ S.w₁₃ S.h₃
def h₃_τ₃ : is_colimit (cokernel_cofork.of_π S.v₂₃.τ₃ S.w₁₃_τ₃) :=
is_colimit_cofork_map_of_is_colimit' π₃ S.w₁₃ S.h₃

instance epi_v₂₃_τ₁ : epi S.v₂₃.τ₁ := cofork.is_colimit.epi_π S.h₃_τ₁
instance epi_v₂₃_τ₂ : epi S.v₂₃.τ₂ := cofork.is_colimit.epi_π S.h₃_τ₂
instance epi_v₂₃_τ₃ : epi S.v₂₃.τ₃ := cofork.is_colimit.epi_π S.h₃_τ₃

lemma C₁_down_exact : (short_complex.mk S.v₁₂.τ₁ S.v₂₃.τ₁
  (by rw [← comp_τ₁, S.w₁₃, zero_τ₁])).exact :=
exact.of_g_is_cokernel S.h₃_τ₁
lemma C₂_down_exact : (short_complex.mk S.v₁₂.τ₂ S.v₂₃.τ₂
  (by rw [← comp_τ₂, S.w₁₃, zero_τ₂])).exact :=
exact.of_g_is_cokernel S.h₃_τ₂
lemma C₃_down_exact : (short_complex.mk S.v₁₂.τ₃ S.v₂₃.τ₃
  (by rw [← comp_τ₃, S.w₁₃, zero_τ₃])).exact :=
exact.of_g_is_cokernel S.h₃_τ₃

instance epi_L₃_g [epi S.L₂.g] : epi S.L₃.g :=
begin
  haveI : epi (S.v₂₃.τ₂ ≫ S.L₃.g),
  { rw S.v₂₃.comm₂₃,
    apply epi_comp, },
  exact epi_of_epi S.v₂₃.τ₂ _,
end

def is_colimit_cokernel_cofork_L₃ [epi S.L₂.g] : is_colimit (cokernel_cofork.of_π _ S.L₃.zero) :=
cokernel_cofork.is_colimit.of_π _ _
  (λ A x hx, S.h₃_τ₃.desc
    (cokernel_cofork.of_π (S.L₂_exact.desc (S.v₂₃.τ₂ ≫ x)
      (by rw [← S.v₂₃.comm₁₂_assoc, hx, comp_zero]))
      (by simp only [← cancel_epi S.L₁.g, ← S.v₁₂.comm₂₃_assoc,
        comp_zero, exact.g_desc, w₁₃_τ₂_assoc, zero_comp])))
  (λ A x hx, begin
    simp only [← cancel_epi S.v₂₃.τ₂, S.v₂₃.comm₂₃_assoc],
    erw cofork.is_colimit.π_desc S.h₃_τ₃,
    simp only [exact.g_desc, cokernel_cofork.π_of_π],
  end)
  (λ A x hx b hb, by erw [← cancel_epi S.L₃.g, hb, ← cancel_epi S.v₂₃.τ₂, S.v₂₃.comm₂₃_assoc,
      cofork.is_colimit.π_desc S.h₃_τ₃, exact.g_desc])

lemma ex₃ [epi S.L₂.g] : S.L₃.exact := exact.of_g_is_cokernel (S.is_colimit_cokernel_cofork_L₃)

def P := pullback S.L₁.g S.v₀₁.τ₃

def P' := pushout S.L₂.f S.v₂₃.τ₁

@[simp] def φ₂ : S.P ⟶ S.L₂.X₂ := pullback.fst ≫ S.v₁₂.τ₂
def φ₁ : S.P ⟶ S.L₂.X₁ :=
S.L₂_exact.lift S.φ₂
  (by simp only [φ₂, assoc, S.v₁₂.comm₂₃, pullback.condition_assoc, w₀₂_τ₃, comp_zero])

@[simp, reassoc] lemma φ₁_L₂_f : S.φ₁ ≫ S.L₂.f = S.φ₂ :=
S.L₂_exact.lift_f _ _

def L₀' : short_complex C :=
{ X₁ := S.L₁.X₁,
  X₂ := S.P,
  X₃ := S.L₀.X₃,
  f := pullback.lift S.L₁.f 0 (by simp),
  g := pullback.snd,
  zero := by simp, }

@[simp, reassoc] lemma L₁_f_φ₁ : S.L₀'.f ≫ S.φ₁ = S.v₁₂.τ₁ :=
begin
  dsimp only [L₀'],
  simp only [← cancel_mono S.L₂.f, assoc, φ₁_L₂_f, φ₂, pullback.lift_fst_assoc,
    S.v₁₂.comm₁₂],
end

instance : epi S.L₀'.g := by { dsimp only [L₀'], apply_instance, }
instance [mono S.L₁.f] : mono S.L₀'.f :=
⟨λ Z h₁ h₂ eq, begin
  replace eq := eq =≫ pullback.fst,
  dsimp [L₀'] at eq,
  simpa only [assoc, pullback.lift_fst, cancel_mono] using eq,
end⟩

@[simps]
def v₀₁' : S.L₀' ⟶ S.L₁ :=
{ τ₁ := 𝟙 _,
  τ₂ := pullback.fst,
  τ₃ := S.v₀₁.τ₃,
  comm₁₂' := by { dsimp [L₀'], simp only [id_comp, pullback.lift_fst], },
  comm₂₃' := pullback.condition, }

instance : epi S.L₁.to_cycles :=
by { rw ← S.L₁.exact_iff_epi_to_cycles, exact S.L₁_exact }

instance : is_iso (cycles_map S.v₀₁') :=
begin
  refine ⟨⟨S.L₀'.lift_cycles (pullback.lift (S.L₁.cycles_i) 0 (by simp))
    (by { dsimp [L₀'], simp,}), _, _⟩⟩,
  { simp only [← cancel_mono S.L₀'.cycles_i, assoc, id_comp, lift_cycles_i],
    ext,
    { simp only [assoc, pullback.lift_fst, cycles_map_i, v₀₁'_τ₂], },
    { simp only [assoc, pullback.lift_snd, comp_zero],
      exact S.L₀'.cycles_i_g.symm, }, },
  { simp only [← cancel_mono S.L₁.cycles_i, assoc, cycles_map_i, v₀₁'_τ₂,
      lift_cycles_i_assoc, pullback.lift_fst, id_comp], },
end

lemma L₀'_exact : S.L₀'.exact :=
begin
  rw [S.L₀'.exact_iff_epi_to_cycles, ← comp_id S.L₀'.to_cycles,
    ← is_iso.hom_inv_id (cycles_map S.v₀₁'), ← assoc],
  haveI : epi (S.L₀'.to_cycles ≫ cycles_map S.v₀₁'),
  { simp only [to_cycles_naturality S.v₀₁', v₀₁'_τ₁, id_comp],
    apply_instance, },
  apply epi_comp,
end

def δ : S.L₀.X₃ ⟶ S.L₃.X₁ :=
S.L₀'_exact.desc (S.φ₁ ≫ S.v₂₃.τ₁) (by simp only [L₁_f_φ₁_assoc, w₁₃_τ₁])

@[simp, reassoc]
lemma snd_δ : (pullback.snd : S.P ⟶ _) ≫ S.δ = S.φ₁ ≫ S.v₂₃.τ₁ :=
S.L₀'_exact.g_desc _ _

lemma snd_δ_inr : (pullback.snd : S.P ⟶ _) ≫ S.δ ≫ (pushout.inr : _ ⟶ S.P') =
  pullback.fst ≫ S.v₁₂.τ₂ ≫ pushout.inl :=
by simp only [snd_δ_assoc, ← pushout.condition, φ₂, φ₁_L₂_f_assoc, assoc]

@[simp]
def L₀_X₂_to_P : S.L₀.X₂ ⟶ S.P := pullback.lift S.v₀₁.τ₂ S.L₀.g S.v₀₁.comm₂₃

@[reassoc]
lemma L₀_X₂_to_P_comp_pullback_snd : S.L₀_X₂_to_P ≫ pullback.snd = S.L₀.g := by simp

@[reassoc]
lemma L₀_X₂_to_P_comp_φ₁ : S.L₀_X₂_to_P ≫ S.φ₁ = 0 :=
by simp only [← cancel_mono S.L₂.f, L₀_X₂_to_P, assoc, φ₂, φ₁_L₂_f,
  pullback.lift_fst_assoc, w₀₂_τ₂, zero_comp]

lemma L₀_g_δ : S.L₀.g ≫ S.δ = 0 :=
by erw [← L₀_X₂_to_P_comp_pullback_snd, assoc, S.L₀'_exact.g_desc,
  L₀_X₂_to_P_comp_φ₁_assoc, zero_comp]

lemma δ_L₃_f : S.δ ≫ S.L₃.f = 0 :=
by erw [← cancel_epi S.L₀'.g, S.L₀'_exact.g_desc_assoc, assoc, S.v₂₃.comm₁₂, S.φ₁_L₂_f_assoc,
  φ₂, assoc, w₁₃_τ₂, comp_zero, comp_zero]

@[simps]
def L₁' : short_complex C := short_complex.mk _ _ S.L₀_g_δ

@[simps]
def L₂' : short_complex C := short_complex.mk _ _ S.δ_L₃_f

lemma L₁'_exact : S.L₁'.exact :=
begin
  apply short_complex.exact.of_pseudo_exact',
  intros A₀ k₃ hk₃,
  dsimp at k₃ hk₃,
  obtain ⟨A₁, π₁, hπ₁, p, hp⟩ := abelian.pseudo_surjective_of_epi' S.L₀'.g k₃,
  dsimp [L₀'] at p hp,
  have hp' : (p ≫ S.φ₁) ≫ S.v₂₃.τ₁ = 0,
  { rw [assoc, ← S.snd_δ, ← reassoc_of hp, hk₃, comp_zero], },
  obtain ⟨A₂, π₂, hπ₂, x₁, hx₁⟩ := S.C₁_down_exact.pseudo_exact' (p ≫ S.φ₁) hp',
  dsimp at x₁ hx₁,
  let x₂' := x₁ ≫ S.L₁.f,
  let x₂ := π₂ ≫ p ≫ pullback.fst,
  have hx₂' : (x₂ - x₂') ≫ S.v₁₂.τ₂ = 0,
  { dsimp [x₂, x₂'],
    simp only [sub_comp, assoc, ← S.v₁₂.comm₁₂, ← reassoc_of hx₁, φ₂, φ₁_L₂_f, sub_self], },
  let k₂ := S.C₂_up_exact.lift _ hx₂',
  dsimp at k₂,
  have hk₂ : k₂ ≫ S.v₀₁.τ₂ = x₂ - x₂' := S.C₂_up_exact.lift_f _ _,
  have hk₂' : k₂ ≫ S.L₀.g = π₂ ≫ p ≫ pullback.snd,
  { dsimp [x₂, x₂'] at hk₂,
    simp only [← cancel_mono S.v₀₁.τ₃, assoc, ← S.v₀₁.comm₂₃, reassoc_of hk₂, sub_comp, S.L₁.zero,
      comp_zero, sub_zero, pullback.condition], },
  haveI := hπ₁,
  haveI := hπ₂,
  refine ⟨_, π₂ ≫ π₁, epi_comp _ _, k₂, _⟩,
  simp only [assoc, L₁'_f, ← hk₂', hp],
end

@[simps]
def op : snake_input Cᵒᵖ :=
{ L₀ := S.L₃.op,
  L₁ := S.L₂.op,
  L₂ := S.L₁.op,
  L₃ := S.L₀.op,
  epi_L₁_g := by { dsimp, apply_instance, },
  mono_L₂_f := by { dsimp, apply_instance, },
  v₀₁ := op_map S.v₂₃,
  v₁₂ := op_map S.v₁₂,
  v₂₃ := op_map S.v₀₁,
  w₀₂' := congr_arg op_map S.w₁₃,
  w₁₃' := congr_arg op_map S.w₀₂,
  h₀ := is_limit_fork_map_of_is_limit'
    (short_complex.op_equiv C).functor _ (cokernel_cofork.is_colimit.of_π_op _ _ S.h₃),
  h₃ := is_colimit_cofork_map_of_is_colimit'
    (short_complex.op_equiv C).functor _ (kernel_fork.is_limit.of_ι_op _ _ S.h₀),
  L₁_exact := S.L₂_exact.op,
  L₂_exact := S.L₁_exact.op, }

@[simp]
def P_iso_unop_op_P' : S.P ≅ opposite.unop S.op.P' :=
pullback_iso_unop_pushout _ _

@[simp]
def P'_iso_unop_op_P : S.P' ≅ opposite.unop S.op.P :=
pushout_iso_unop_pullback _ _

lemma op_δ : S.op.δ = S.δ.op :=
quiver.hom.unop_inj begin
  rw [quiver.hom.unop_op, ← cancel_mono (pushout.inr : _ ⟶ S.P'),
    ← cancel_epi (pullback.snd : S.P ⟶ _), S.snd_δ_inr],
  simp only [← cancel_mono S.P'_iso_unop_op_P.hom, ← cancel_epi S.P_iso_unop_op_P'.inv,
    P'_iso_unop_op_P, P_iso_unop_op_P', assoc,
    pushout_iso_unop_pullback_inl_hom, pushout_iso_unop_pullback_inr_hom,
    pullback_iso_unop_pushout_inv_snd_assoc, pullback_iso_unop_pushout_inv_fst_assoc],
  apply quiver.hom.op_inj,
  simp only [op_comp, quiver.hom.op_unop, assoc],
  exact S.op.snd_δ_inr,
end

def L₂'_op_iso : S.L₂'.op ≅ S.op.L₁' :=
short_complex.mk_iso (iso.refl _) (iso.refl _) (iso.refl _) (by tidy)
  (by { dsimp, simp only [id_comp, comp_id, S.op_δ], })

lemma L₂'_exact : S.L₂'.exact :=
begin
  rw [short_complex.exact_iff_op, short_complex.exact_iff_of_iso S.L₂'_op_iso],
  exact S.op.L₁'_exact,
end

end snake_input

end short_complex
