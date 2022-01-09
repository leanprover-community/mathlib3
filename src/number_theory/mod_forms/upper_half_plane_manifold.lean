import analysis.complex.upper_half_plane
import geometry.manifold.mfderiv
import number_theory.mod_forms.mod_forms2
import number_theory.mod_forms.holomorphic_functions

local notation `ℍ`:=upper_half_plane



noncomputable theory

open_locale classical topological_space manifold


instance : topological_space ℍ := infer_instance

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

def I : model_with_corners ℂ ℂ ℂ :=
begin
apply  model_with_corners_self,
end

instance : charted_space ℂ ℂ := infer_instance

instance : charted_space ℂ ℍ' := infer_instance

variable (f : ℍ' → ℂ)

lemma df : is_holomorphic_on f :=
begin
sorry,
end

instance : nonempty ℍ' :=
begin
sorry,
end

lemma ext_chart (z : ℍ') : (extend_by_zero f) z = (f ∘ ⇑((chart_at ℂ z).symm)) z :=
begin
simp_rw chart_at,
simp_rw extend_by_zero,
simp,
have :=  (local_homeomorph.subtype_restr_coe  (local_homeomorph.refl ℂ) ℍ').symm,
congr,
simp_rw local_homeomorph.subtype_restr,
simp,
have hf:= topological_space.opens.local_homeomorph_subtype_coe_coe ℍ',
simp_rw ← hf,
apply symm,
apply local_homeomorph.left_inv,
simp [z.2],
end

lemma df2 : mdifferentiable I I f :=
begin
have hf := df f,
rw ← is_holomorphic_on_iff_differentiable_on at hf,
simp_rw differentiable_on at hf,

simp_rw mdifferentiable,
 simp only [mdifferentiable_at, differentiable_within_at_univ] with mfld_simps,
intro x,
split,

sorry,
have hfx := hf x x.2,
convert hfx,
funext y,
simp,

sorry,
sorry,
end
