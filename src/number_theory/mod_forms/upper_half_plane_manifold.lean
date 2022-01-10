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
simp only [topological_space.opens.local_homeomorph_subtype_coe_source],
end

lemma df2 : mdifferentiable I I f :=
begin
have hf := df f,
rw ← is_holomorphic_on_iff_differentiable_on at hf,


simp_rw mdifferentiable,
 simp only [mdifferentiable_at, differentiable_within_at_univ] with mfld_simps,
intro x,
split,

sorry,
have hfx := hf x x.2,
apply differentiable_at.differentiable_within_at,
have hH: ℍ'.1 ∈ 𝓝 (I ((chart_at ℂ x) x)), by {simp_rw metric.mem_nhds_iff, simp_rw I, simp,
simp_rw chart_at, simp, have:= upper_half_plane_is_open, rw metric.is_open_iff at this,
have ht:= this x.1 x.2, simp at ht, exact ht,},
apply differentiable_on.differentiable_at _ hH,
apply differentiable_on.congr hf,
intros y hy,
have HH:= ext_chart f (⟨y,hy⟩ : ℍ'),
simp at HH,
simp_rw I,
simp,
simp_rw HH,
congr,
end
