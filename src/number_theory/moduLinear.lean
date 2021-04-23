import topology.algebra.module
import analysis.normed_space.finite_dimension
import order.filter.basic

open function
open filter

variables (k U V W: Type*)  [field k] [topological_space k]
[topological_space U] [topological_space V] [topological_space W]
 [add_comm_group U] [add_comm_group V]
[add_comm_group W] [module k U] [module k V] [module k W]
[has_continuous_add U]
[has_continuous_add V]
[has_continuous_add W]
 [has_continuous_smul k U]
(f : continuous_linear_map k U V) (g : continuous_linear_map k U W)


-- make this a general linear algebra theorem, no topology
theorem thm3 {A B C : Type*} (f : A → B) (g : A → C ) (p : C ) (h : injective (λ x, (f x, g x))) :
injective (f ∘ (coe: (g ⁻¹' {p}) → A ))
:=
begin
  intros x y hf,
  simp at hf,
  have x2 := x.2,
  have : g x = g y,
  {
    have := set.mem_preimage.mp (subtype.mem x),
    have gxp := set.eq_of_mem_singleton this,
    have := set.mem_preimage.mp (subtype.mem y),
    have gyp := set.eq_of_mem_singleton this,
    simp [gxp, gyp],
  },
  have : (f x, g x ) = (f y , g y),
  {
    simp [hf, this],
  },
  have := h this,
  exact subtype.ext (h (congr_arg (λ (x : A), (f x, g x)) this)),
end


-- ALEX HOMEWORK
--make this a general linear algebra theorem, no topology
def thm5 {A B C : Type*}
(F : equiv A (B×C)) (p : C ):
equiv ((prod.snd ∘ F) ⁻¹' {p}) B :=  --(F.fst ∘ (coe: ((snd∘ F) ⁻¹' {p}) → A ))
{ to_fun :=  λ x, prod.fst (F x),
  inv_fun :=  λ b,  ⟨ F.symm (b, p), by simp⟩,
  left_inv := _,
  right_inv := _ }


-- make this a general linear algebra theorem, no topology
def thm4 {A B C : Type*} [topological_space A] [topological_space B] [topological_space C]
(F : homeomorph A (B×C)) (p : C ):
homeomorph ((prod.snd ∘ F) ⁻¹' {p}) B :=  --(F.fst ∘ (coe: ((snd∘ F) ⁻¹' {p}) → A ))
{ to_fun :=  λ x, prod.fst (F x) ,
  inv_fun := λ b,  ⟨ F.symm (b, p), by simp⟩ ,
  left_inv :=
  begin
    rw left_inverse,
    intros x,
    have x1 := x.1,
    have x2 := x.2,
    have := F.left_inv x,

  end,
  right_inv := _,
  continuous_to_fun := _,
  continuous_inv_fun := _ }


theorem thm2 (p : W) (h₁ : injective (continuous_linear_map.prod f g))
(h₂ : is_open_map (f∘(coe : (g ⁻¹' {p}) → U))) :
open_embedding (f∘(coe : (g ⁻¹' {p}) → U)) :=
begin
  apply open_embedding_of_continuous_injective_open,
  -- (continuous_linear_map.continuous f),
  exact continuous.comp (continuous_linear_map.continuous f) continuous_subtype_coe,
  --have:= injective.comp,
  exact thm3 f g p h₁,
  exact h₂,
end

-- Heather homework
theorem thm1 (p : W) (h₁ : embedding (continuous_linear_map.prod f g))
(h₂ : is_open_map (f∘(coe : (g ⁻¹' {p}) → U))) :
tendsto (f∘(coe : (g ⁻¹' {p}) → U)) (cocompact _) (cocompact _) :=
begin
  sorry,
end



theorem thm0 {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {E : Type*} [normed_group E]
[normed_space 𝕜 E] [complete_space 𝕜] [finite_dimensional 𝕜 E]
{F : Type*} [normed_group F]
[normed_space 𝕜 F] [finite_dimensional 𝕜 F]
(f : linear_map 𝕜 E F) (h: surjective f)
 :
is_open_map f :=
begin
  have f_cont := linear_map.continuous_of_finite_dimensional f,

  sorry,
end
