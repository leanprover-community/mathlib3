import topology.algebra.module
import analysis.normed_space.finite_dimension
import order.filter.basic

open function
open filter

section
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

end



-- ********* HM new idea!!!



-- ALEX HOMEWORK
-- Natural bijection from the fibre over `p : C`, in a product type `B × C`, to `B`.
def fibre_embed {B C : Type*} (p : C) :
  equiv (prod.snd ⁻¹' {p} : set (B × C)) B :=
{ to_fun := prod.fst ∘ (coe : _ → B × C),
  inv_fun := _,
  left_inv := _,
  right_inv := _ }

-- ALEX HOMEWORK
-- Natural homeomorphism from the fibre over `p : C`, in a product space `B × C`, to `B`.
def fibre_embed_homeomorph {B C : Type*} [topological_space B] [topological_space C] (p : C) :
  homeomorph (prod.snd ⁻¹' {p} : set (B × C)) B :=
{ continuous_to_fun := _,
  continuous_inv_fun := _,
  .. fibre_embed p }


-- ALEX HOMEWORK
-- A closed embedding is proper
-- for `topology.subset_properties`
lemma closed_embedding.tendsto_cocompact {A B : Type*} [topological_space A] [topological_space B]
  {f : A → B} (hf : closed_embedding f) : tendsto f (cocompact A) (cocompact B) :=
begin
  rw has_basis_cocompact.tendsto_iff has_basis_cocompact,
  intros K hK,
  refine ⟨f ⁻¹' (K ∩ (set.range f)), _, λ x hx, by simpa using hx⟩,
  have : is_compact (K ∩ set.range f) := hK.inter_right hf.closed_range,
  -- goal: `⊢ is_compact (f ⁻¹' (K ∩ set.range f))`
  -- this should be true, since `f` restricts to a homeomorphism from `A` onto its image
  sorry
end

/-- If the composition of a continuous function `f` with a closed embedding `g` is a closed
embedding, then `f` is a closed embedding -/
-- for `topology.maps`
lemma closed_embedding_of_closed_embedding_compose {A X Y : Type*} [topological_space A]
  [topological_space X] [topological_space Y]
  {f : A → X} {g : X → Y} (hf : continuous f) (hg : closed_embedding g)
  (hfg : closed_embedding (g ∘ f)) :
  closed_embedding f :=
begin
  refine ⟨embedding_of_embedding_compose hf hg.continuous hfg.to_embedding, _⟩,
  simpa [hg.closed_iff_image_closed, set.range_comp g f] using hfg.closed_range
end

/-- Given a closed embedding, the codomain-restriction to any closed subset is also a closed
embedding -/
-- for `topology.constructions`
lemma closed_embedding.cod_restrict {B X : Type*} [topological_space B]
  [topological_space X]
  {F : B → X} (hF : closed_embedding F) {s : set X} (hs : is_closed s) (hgs : ∀ x, F x ∈ s) :
  closed_embedding (set.cod_restrict F s hgs) :=
begin
  refine closed_embedding_of_closed_embedding_compose _ (closed_embedding_subtype_coe hs) hF,
  exact continuous_subtype_mk _ hF.continuous
end

variables {k U V : Type*} [nondiscrete_normed_field k] [complete_space k]
  [normed_group U] [normed_group V] [normed_space k U] [normed_space k V]
  {f : linear_map k U V}

-- for `analysis.normed_space.finite_dimension`
/-- An injective linear map with finite-dimensional domain is a closed embedding. -/
lemma linear_equiv.closed_embedding_of_injective (hf : f.ker = ⊥) [finite_dimensional k U] :
  closed_embedding ⇑f :=
let g := linear_equiv.of_injective f hf in
{ closed_range := begin
    haveI := f.finite_dimensional_range,
    simpa [f.range_coe] using f.range.closed_of_finite_dimensional
  end,
  .. embedding_subtype_coe.comp g.to_continuous_linear_equiv.to_homeomorph.embedding }

variables {W : Type*} [normed_group W] [normed_space k W] {g : linear_map k U W}

/-- Here's how to do the big theorem, although this is a bit too specific to actually join the library -/
theorem big_thm [finite_dimensional k U] (p : W) (h₁ : (f.prod g).ker = ⊥) :
  tendsto (f ∘ (coe : (g ⁻¹' {p}) → U)) (cocompact _) (cocompact _) :=
begin
  let hf := linear_equiv.closed_embedding_of_injective h₁,
  let hs : is_closed (prod.snd ⁻¹' {p} : set (V × W)) := is_closed_singleton.preimage continuous_snd,
  have := (hf.comp (closed_embedding_subtype_coe (hs.preimage hf.continuous))).cod_restrict hs (by simp),
  exact ((fibre_embed_homeomorph p).closed_embedding.comp this).tendsto_cocompact,
end
