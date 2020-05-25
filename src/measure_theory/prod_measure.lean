/-
Various lemmas intended for mathlib.
Some parts of this file are originally from
https://github.com/johoelzl/mathlib/blob/c9507242274ac18defbceb917f30d6afb8b839a5/src/measure_theory/measurable_space.lean

Authors: Johannes Holzl, John Tristan, Koundinya Vajjha
-/
import tactic.tidy
import measure_theory.giry_monad measure_theory.integration measure_theory.borel_space .dvector
import .probability_theory
import analysis.special_functions.exp_log

local attribute [instance] classical.prop_decidable

noncomputable theory

-- set_option pp.implicit true
-- set_option pp.coercions true
-- set_option trace.class_instances true
-- set_option class.instance_max_depth 39
-- local attribute [instance] classical.prop_decidable

universes u v


open nnreal measure_theory nat list measure_theory.measure set lattice ennreal measurable_space probability_measure

infixl ` >>=ₐ `:55 :=  measure.bind
infixl ` <$>ₐ `:55 := measure.map

local notation `doₐ` binders ` ←ₐ ` m ` ; ` t:(scoped p, m >>=ₐ p) := t

local notation `ret` := measure.dirac

namespace to_integration
variables {α : Type u} {β : Type u}

-- Auxilary results about simple functions and characteristic functions. The results in this section should go into integration.lean in mathlib.

@[simp] lemma integral_sum [measurable_space α] (m : measure α) (f g : α → ennreal) [hf : measurable f] [hg : measurable g] : m.integral (f + g) = m.integral f + m.integral g := begin
  rw [integral, integral, integral,←lintegral_add], refl,
  repeat{assumption},
end

@[simp] lemma integral_const_mul [measurable_space α] (m : measure α) {f : α → ennreal} (hf : measurable f) (k:ennreal): m.integral (λ x, k*f(x)) = k * m.integral f :=
by rw [integral,lintegral_const_mul,integral] ; assumption


/-- The characteristic function (indicator function) of a set A. -/
noncomputable def char_fun [measurable_space α] (A : set α) := simple_func.restrict (simple_func.const α (1 : ennreal)) A

notation `χ` `⟦` A `⟧` := char_fun A
notation `∫` f `ð`m := integral m f

-- variables (A : set α) (a : α) [measurable_space α]

@[simp] lemma char_fun_apply [measurable_space α] {A : set α} (hA : is_measurable A)(a : α):
(χ ⟦A⟧ : simple_func α ennreal) a = ite (a ∈ A) 1 0 := by
unfold_coes ; apply (simple_func.restrict_apply _ hA)

@[simp] lemma integral_char_fun [measurable_space α] [ne : nonempty α] (m : measure α) {A : set α} (hA : is_measurable A) :
(∫ χ⟦A⟧ ðm) = m A :=
begin
   rw [char_fun, integral, simple_func.lintegral_eq_integral, simple_func.restrict_integral],
   unfold set.preimage, dsimp, erw [simple_func.range_const α], simp, rw [←set.univ_def, set.univ_inter], refl, assumption,
end

lemma dirac_char_fun [measurable_space α] {A : set α} (hA : is_measurable A) : (λ (x : α), (ret x : measure α) A) = χ⟦A⟧ :=
begin
  funext,rw [measure.dirac_apply _ hA, char_fun_apply hA],
  by_cases x ∈ A, split_ifs, simp [h],
  split_ifs, simp [h],
end

lemma prob.dirac_char_fun [measurable_space α] {B: set α} (hB : is_measurable B) : (λ x:α,((retₚ x).to_measure : measure α) B) = χ⟦B⟧ :=
begin
  conv {congr, funext, rw ret_to_measure},
  exact dirac_char_fun hB,
end

lemma measurable_dirac_fun [measurable_space α] {A : set α} (hA : is_measurable A) : measurable (λ (x : α), (ret x : measure α) A) := by rw dirac_char_fun hA ; apply simple_func.measurable


instance simple_func.add_comm_monoid [measurable_space α] [add_comm_monoid β] : add_comm_monoid (simple_func α β) :=
{
  add_comm := assume a b, simple_func.ext (assume a, add_comm _ _),
  .. simple_func.add_monoid
}

lemma integral_finset_sum [measurable_space α] (m : measure α) (s : finset (set α))
(hX : ∀ (A : set α) , is_measurable (A)) :
m.integral (s.sum (λ A, χ ⟦ A ⟧)) = s.sum (λ A, m A) :=
begin
  rw integral,
  refine finset.induction_on s _ _,
  { simp, erw lintegral_zero },
  { assume a s has ih, simp [has], erw [lintegral_add],
    rw simple_func.lintegral_eq_integral,unfold char_fun,
    erw simple_func.restrict_const_integral, dsimp, erw ih, ext1,cases a_1, dsimp at *, simp at *, refl, exact(hX a),
    { intros i h, dsimp at *, solve_by_elim [hX] },
    { intros a b, dsimp at *, solve_by_elim },
  },
end

lemma integral_le_integral [measurable_space α] (m : measure α) (f g : α → ennreal) (h : f ≤ g) :
(∫ f ðm) ≤ (∫ g ðm) :=
begin
rw integral, rw integral, apply lintegral_mono, assumption,
end


noncomputable def char_prod [measurable_space α]{f : α → ennreal}{ε : ennreal}(hf : measurable f)(eh : ε > 0): simple_func α ennreal :=
⟨
  λ x, if (f(x) ≥ ε) then ε else 0,
  assume x, by letI : measurable_space ennreal := borel ennreal; exact
   measurable.if (is_measurable_le measurable_const hf) measurable_const measurable_const _ (is_closed_singleton.is_measurable),
  begin apply finite_subset (finite_union (finite_singleton ε) ((finite_singleton 0))),
  rintro _ ⟨a, rfl⟩,
  by_cases (f a ≥ ε); simp [h],
  end
⟩

@[simp] lemma char_prod_apply [measurable_space α]{f : α → ennreal}{ε : ennreal}(hf : measurable f)(eh : ε > 0) (a : α): (char_prod hf eh) a = if (f a ≥ ε) then ε else 0 := rfl


/-- Markov's inequality. -/
theorem measure_fun_ge_le_integral [measurable_space α] [nonempty α] (m : measure α) {f : α → ennreal} (hf : measurable f) : ∀ (ε > 0),
 ε*m({x | f(x) ≥ ε}) ≤ ∫ f ðm :=
begin
  intros ε eh,
  let s := char_prod hf eh,
  have hsf : ∀ x, s x ≤ f x, {
    intro x,
    by_cases g : (f(x) ≥ ε),
    dsimp [s], split_ifs, exact g,
    dsimp [s], split_ifs, exact zero_le (f x),
  },
  convert (integral_le_integral _ _ _ hsf),
  have seq : s = (simple_func.const α ε) * (χ ⟦{x : α | f x ≥ ε} ⟧),{
    apply simple_func.ext,
    intro a, simp * at *,
    dunfold char_fun,
    rw [simple_func.restrict_apply, simple_func.const_apply],
    split_ifs, rw mul_one, rw mul_zero,
    apply (@is_measurable_le ennreal α _ _), exact measurable_const, assumption,
  },
  rw seq, simp, rw [integral_const_mul m, integral_char_fun],
  apply (@is_measurable_le ennreal α _ _), exact measurable_const, assumption,
  apply simple_func.measurable,
end


/-- Chebyshev's inequality for a nondecreasing function `g`. -/
theorem measure_fun_ge_le_integral_comp [measurable_space α][nonempty α] (m : measure α) {f : α → ennreal} {g : ennreal → ennreal}(hf : measurable f) (hg : measurable g) (nondec : ∀ x y,x ≤ y → g x ≤ g y): ∀ (t > 0),
 g(t)*m({x | f(x) ≥ t}) ≤ ∫ g ∘ f ðm :=
begin
  intros t ht,
  have hsf : ∀ x, g(t) * (χ ⟦{x : α | f x ≥ t} ⟧ x) ≤ (g (f x)), {
    intro x,
    dunfold char_fun,
    rw [simple_func.restrict_apply, simple_func.const_apply],
    split_ifs,
    rw [mul_one], apply (@nondec _ _ h),
    finish,
    apply (@is_measurable_le ennreal α _ _), exact measurable_const, assumption,
  },
  rw [←integral_char_fun, ←integral_const_mul m],
  apply (integral_le_integral m),
  exact hsf,
  apply simple_func.measurable,
  apply (@is_measurable_le ennreal α _ _), exact measurable_const, assumption,
end


end to_integration

namespace giry_pi
-- Auxilary results about infinite products of measure spaces.
-- This section has to go back to `constructions` in `measure_theory/measurable_space`. Originally from Johannes' fork.

instance pi.measurable_space (ι : Type*) (α : ι → Type*) [m : ∀i, measurable_space (α i)] :
  measurable_space (Πi, α i) :=
⨆i, (m i).comap (λf, f i)

instance pi.measurable_space_Prop (ι : Prop) (α : ι → Type*) [m : ∀i, measurable_space (α i)] :
  measurable_space (Πi, α i) :=
⨆i, (m i).comap (λf, f i)

lemma measurable_pi {ι : Type*} {α : ι → Type*} {β : Type*}
  [m : ∀i, measurable_space (α i)] [measurable_space β] {f : β → Πi, α i} :
  measurable f ↔ (∀i, measurable (λb, f b i)):=
begin
  rw [measurable, pi.measurable_space, supr_le_iff],
  refine forall_congr (assume i, _),
  rw [measurable_space.comap_le_iff_le_map, measurable_space.map_comp],
  refl
end

lemma measurable_apply {ι : Type*} {α : ι → Type*} {β : Type*}
  [m : ∀i, measurable_space (α i)] [measurable_space β] (f : β → Πi, α i) (i : ι)
  (hf : measurable f) :
  measurable (λb, f b i) :=
measurable_pi.1 hf _

lemma measurable_pi_Prop {ι : Prop} {α : ι → Type*} {β : Type*}
  [m : ∀i, measurable_space (α i)] [measurable_space β] {f : β → Πi, α i} :
  measurable f ↔ (∀i, measurable (λb, f b i)):=
begin
  rw [measurable, pi.measurable_space_Prop, supr_le_iff],
  refine forall_congr (assume i, _),
  rw [measurable_space.comap_le_iff_le_map, measurable_space.map_comp],
  refl
end

lemma measurable_apply_Prop {p : Prop} {α : p → Type*} {β : Type*}
  [m : ∀i, measurable_space (α i)] [measurable_space β] (f : β → Πi, α i) (h : p)
  (hf : measurable f) :
  measurable (λb, f b h) :=
measurable_pi_Prop.1 hf _

end giry_pi

section giry_prod

open to_integration

variables {α : Type u} {β : Type u} {γ : Type v}

/- Auxilary results about the Giry monad and binary products. The following results should go back to giry_monad.lean -/

/-- Right identity monad law for the Giry monad. -/
lemma giry.bind_return_comp [measurable_space α][measurable_space β] (D : measure α) {p : α → β} (hp : measurable p) :
(doₐ (x : α) ←ₐ D ;
 ret (p x)) = p <$>ₐ D :=
measure.ext $ assume s hs, begin
  rw [measure.bind_apply hs _],
  rw [measure.map_apply hp hs],
  conv_lhs{congr, skip, funext, rw [measure.dirac_apply _ hs]},
  transitivity,
  apply lintegral_supr_const, exact hp _ hs,
   rw one_mul, refl,
  exact measurable.comp measurable_dirac hp,
end

/-- Left identity monad law for compositions in the Giry monad -/
lemma giry.return_bind_comp [measurable_space α][measurable_space β] {p : α → measure β} {f : α → α} (hf : measurable f)(hp : measurable p) (a : α) :
 (doₐ x ←ₐ dirac a ; p (f x))  = p (f a) :=
measure.ext $ assume s hs, begin
rw measure.bind_apply hs, rw measure.integral_dirac a,
swap, exact measurable.comp hp hf,
exact measurable.comp (measurable_coe hs) (measurable.comp hp hf),
end

def prod_measure [measurable_space α] [measurable_space β] (μ : measure α) (ν : measure β) : measure (α × β) :=
doₐ x ←ₐ μ ;
doₐ y ←ₐ ν ;
  ret (x, y)

infixl ` ⊗ₐ `:55 :=  prod_measure

instance prod.measure_space [measurable_space α] [measurable_space β] (μ : measure α) (ν : measure β) : measure_space (α × β) := ⟨ μ ⊗ₐ ν ⟩

@[to_additive]
instance pi.measure_space (ι : Type*) (α : ι → Type*) [fintype ι] [m : ∀i, measurable_space (α i)]
  (μ : Π i, @measure_theory.measure (α i) (m i)) :
  measure_space (Πi, α i) :=
{ μ := begin
  unfreezeI,
  induction hn : fintype.card ι with n IH generalizing ι,
  {
    rw fintype.card_eq_zero_iff at hn,
    sorry,
  },

end,
..giry_pi.pi.measurable_space }


lemma inl_measurable [measurable_space α][measurable_space β] : ∀ y : β, measurable (λ x : α, (x,y)) := assume y, begin
apply measurable.prod, dsimp, exact measurable_id, dsimp, exact measurable_const,
end

lemma inr_measurable [measurable_space α][measurable_space β] : ∀ x : α, measurable (λ y : β, (x,y)) := assume y, begin
apply measurable.prod, dsimp, exact measurable_const, dsimp, exact measurable_id,
end

lemma inl_measurable_dirac [measurable_space α][measurable_space β]  : ∀ y : β,  measurable (λ (x : α), ret (x, y)) := assume y, begin
  apply measurable_of_measurable_coe,
  intros s hs,
  simp [hs, supr_eq_if, mem_prod_eq],
  apply measurable_const.if _ measurable_const,
  apply measurable.preimage _ hs,
  apply measurable.prod, dsimp, exact measurable_id,
  dsimp, exact measurable_const,
end

lemma inr_measurable_dirac [measurable_space β][measurable_space α] : ∀ x : α,  measurable (λ (y : β), ret (x, y)) := assume x, begin
  apply measurable_of_measurable_coe,
  intros s hs,
  simp [hs, supr_eq_if, mem_prod_eq],
  apply measurable_const.if _ measurable_const, apply measurable.preimage _ hs,
  apply measurable.prod, dsimp, exact measurable_const,
  dsimp, exact measurable_id,
end

lemma inr_section_is_measurable [measurable_space α] [measurable_space β]  {E : set (α × β)} (hE : is_measurable E) (x : α) :
is_measurable ({ y:β | (x,y) ∈ E}) :=
begin
  change (is_measurable ((λ z:β, (x,z))⁻¹' E)),
  apply inr_measurable, assumption,
end

lemma inl_section_is_measurable [measurable_space α] [measurable_space β]  {E : set (α × β)} (hE : is_measurable E) (y : β) :
is_measurable ({ x:α | (x,y) ∈ E}) :=
begin
  change (is_measurable ((λ z:α, (z,y))⁻¹' E)),
  apply inl_measurable, assumption,
end

lemma snd_comp_measurable [measurable_space α] [measurable_space β] [measurable_space γ] {f : α × β → γ} (hf : measurable f) (x : α) : measurable (λ y:β, f (x, y)) := (measurable.comp hf (inr_measurable _))

lemma fst_comp_measurable [measurable_space α] [measurable_space β] [measurable_space γ] {f : α × β → γ} (hf : measurable f) (y : β) : measurable ((λ x:α, f (x, y))) := (measurable.comp hf (inl_measurable _))

lemma measurable_pair_iff [measurable_space α] [measurable_space β] [measurable_space γ] (f : γ → α × β) :
measurable f ↔ (measurable (prod.fst ∘ f) ∧ measurable (prod.snd ∘ f)) :=
iff.intro
(assume h, and.intro (measurable.fst h) (measurable.snd h))
(assume ⟨h₁, h₂⟩, measurable.prod h₁ h₂)


@[simp] lemma dirac.prod_apply [measurable_space α][measurable_space β]{A : set α} {B : set β} (hA : is_measurable A) (hB : is_measurable B) (a : α) (b : β) :
 (ret (a,b) : measure (α × β)) (A.prod B) = ((ret a : measure α) A) * ((ret b : measure β) B) :=
begin
  rw [dirac_apply, dirac_apply, dirac_apply, mem_prod_eq],
  dsimp,
  by_cases Ha: (a ∈ A); by_cases Hb: (b ∈ B),
  repeat {simp [Ha, Hb]},
  repeat {assumption},
  exact is_measurable.prod hA hB,
end

lemma prod.bind_ret_comp [measurable_space α] [measurable_space β]
(μ : measure α) : ∀ y : β,
(doₐ (x : α) ←ₐ μ;
 ret (x,y)) = (λ x, (x,y)) <$>ₐ μ := assume y, begin apply  giry.bind_return_comp, apply measurable.prod, dsimp, exact measurable_id,
dsimp, exact measurable_const, end

-- TODO(Kody) : move this back to mathlib/measurable_space.lean
lemma measure_rect_generate_from [measurable_space α] [measurable_space β] : prod.measurable_space = generate_from {E | ∃ (A : set α) (B : set β), E = A.prod B ∧ is_measurable A ∧ is_measurable B} :=
begin
rw eq_iff_le_not_lt,
split,
  {
    apply generate_from_le_generate_from, intros s hs,
    rcases hs with ⟨A₀, hA, rfl⟩ | ⟨B₀, hB, rfl⟩,
    existsi [A₀, univ],
    fsplit, ext1, cases x, simp, exact and.intro hA is_measurable.univ,
    existsi [univ, B₀],
    fsplit, ext1, cases x, simp, exact and.intro is_measurable.univ hB,
  },
  {
    apply not_lt_of_le,
    apply measurable_space.generate_from_le,
    intros t ht, dsimp at ht, rcases ht with ⟨A, B, rfl, hA, hB⟩, exact is_measurable.prod hA hB,
  }
end

def measurable_prod_bind_ret [measurable_space α] [measurable_space β] (ν : probability_measure β): set(α × β) → Prop := λ s, measurable (λ (x : α), (doₚ (y : β) ←ₚ ν ; retₚ (x, y)) s)

lemma measure_rect_inter [measurable_space α] [measurable_space β] : ∀t₁ t₂, t₁ ∈ {E | ∃ (A : set α) (B : set β), E = A.prod B ∧ is_measurable A ∧ is_measurable B} → t₂ ∈ {E | ∃ (A : set α) (B : set β), E = A.prod B ∧ is_measurable A ∧ is_measurable B} → (t₁ ∩ t₂).nonempty → t₁ ∩ t₂ ∈ {E | ∃ (A : set α) (B : set β), E = A.prod B ∧ is_measurable A ∧ is_measurable B} :=
begin
  rintros t₁ t₂ ⟨A, B, rfl, hA, hB⟩ ⟨A', B', rfl, hA', hB'⟩ hI,
  rw prod_inter_prod,
  existsi [(A ∩ A'),(B ∩ B')],
  fsplit, refl,
  exact and.intro (is_measurable.inter hA hA') (is_measurable.inter hB hB'),
end

lemma measurable_prod_bind_ret_empty [measurable_space α] [measurable_space β] (ν : probability_measure β): measurable (λ (x : α), (doₚ (y : β) ←ₚ ν ; retₚ (x, y)) ∅):=
by simp ; exact measurable_const

lemma measurable_prod_bind_ret_compl [measurable_space α] [measurable_space β] (ν : probability_measure β) :  ∀ t : set (α × β), is_measurable t → measurable (λ (x : α), (doₚ (y : β) ←ₚ ν ; retₚ (x, y)) t) → measurable (λ (x : α), (doₚ (y : β) ←ₚ ν ; retₚ (x, y)) (- t)) :=
begin
  intros t ht hA,
  rw compl_eq_univ_diff,
  conv{congr, funext, rw [probability_measure.prob_diff _ (subset_univ _) is_measurable.univ ht]}, simp,
  refine measurable.comp _ hA,
  refine measurable.comp _ (measurable.sub measurable_const _),
  exact nnreal.continuous_of_real.measurable,
  exact nnreal.continuous_coe.measurable,
end

lemma measurable_prod_bind_ret_basic [measurable_space α] [measurable_space β] (ν : probability_measure β) : ∀ (t : set (α × β)),t ∈ {E : set (α × β) | ∃ (A : set α) (B : set β), E = set.prod A B ∧ is_measurable A ∧ is_measurable B} → measurable (λ (x : α), (doₚ (y : β) ←ₚ ν ; retₚ (x, y)) t) :=
begin
  rintros t ⟨A, B, rfl, hA, hB⟩,
  conv{congr,funext,rw [_root_.bind_apply (is_measurable.prod hA hB)  (prob_inr_measurable_dirac x)],},
  refine measurable.comp _ _, exact measurable_to_nnreal,
  dsimp,
  conv{congr,funext,simp [coe_eq_to_measure]},
  simp [prob.dirac_apply' hA hB],
  have h : measurable (λ (x : β), ((retₚ x).to_measure : measure β) B),{
    conv{congr,funext,rw ret_to_measure,}, exact measurable_dirac_fun hB,
  },
  conv {congr, funext, rw [integral_const_mul ν.to_measure h],},
  refine measurable.ennreal_mul _ _,
  exact measurable_dirac_fun hA,
  exact measurable_const,
end

lemma measurable_prod_bind_ret_union [measurable_space α] [measurable_space β] (ν : probability_measure β): ∀h:ℕ → set (α × β), (∀i j, i ≠ j → h i ∩ h j ⊆ ∅) → (∀i, is_measurable (h i)) → (∀i, measurable(λ (x : α), (doₚ (y : β) ←ₚ ν ; retₚ (x, y)) (h i))) → measurable (λ (x : α), (doₚ (y : β) ←ₚ ν ; retₚ (x, y)) (⋃i, h i)) :=
begin
  rintros h hI hA hB,
  unfold_coes,
  refine measurable.comp (measurable_of_measurable_nnreal measurable_id) _,
  conv{congr,funext,rw [m_Union _ hA hI,ennreal.tsum_eq_supr_nat]},
  apply measurable_supr, intro i,
  apply finset.measurable_sum,
  intros i,
  have h := hB i, clear hB,
  refine measurable_of_ne_top _ _ _, assume x,
  refine probability_measure.to_measure_ne_top _ _, assumption,
end

-- Push this back to ennreal.lean
lemma to_nnreal_mul (a b : ennreal) : ennreal.to_nnreal(a*b) = ennreal.to_nnreal(a) * ennreal.to_nnreal(b) :=
begin
  cases a; cases b,
  { simp [none_eq_top] },
  { by_cases h : b = 0; simp [none_eq_top, some_eq_coe, h, top_mul] },
  { by_cases h : a = 0; simp [none_eq_top, some_eq_coe, h, mul_top] },
  { simp [some_eq_coe, coe_mul.symm, -coe_mul] }
end

@[simp] theorem prod.prob_measure_apply [measurable_space α] [measurable_space β][nonempty α] [nonempty β] (μ : probability_measure α) (ν : probability_measure β) {A : set α} {B : set β}
(hA : is_measurable A) (hB : is_measurable B) :
(μ ⊗ₚ ν) (A.prod B) = μ (A) * ν (B) :=
begin
  dunfold prod.prob_measure,
  rw _root_.bind_apply (is_measurable.prod hA hB),
  conv_lhs{congr, congr, skip, funext, erw [_root_.bind_apply ( is_measurable.prod hA hB) (prob_inr_measurable_dirac a)]},
  simp[coe_eq_to_measure, prob.dirac_apply' hA hB],
    -- move this to probability_theory
  have h : measurable (λ (x : β), ((retₚ x).to_measure : measure β) B),
    {
      conv{congr,funext,rw ret_to_measure,},
      exact measurable_dirac_fun hB,
    },
  conv {congr, funext, congr, congr, skip, funext, rw [integral_const_mul ν.to_measure h,ret_to_measure,mul_comm],},
  rw [prob.dirac_char_fun hB, integral_char_fun ν.to_measure hB],
  -- move this to measurable_space
  have g : ∀ a:α, ((ret a : measure α) A) < ⊤,
    {
      assume a, rw dirac_apply _ hA, by_cases(a ∈ A),
      simp[h],exact lt_top_iff_ne_top.2 one_ne_top,
      simp[h],
    },
  conv_lhs{congr, congr, skip, funext, rw [coe_to_nnreal (lt_top_iff_ne_top.1 (mul_lt_top (to_measure_lt_top _ _) (g a)))]},
  conv_lhs{congr, rw [integral_const_mul μ.to_measure (measurable_dirac_fun hA)]},
    rw [dirac_char_fun hA, integral_char_fun _ hA, mul_comm, to_nnreal_mul], refl,
    apply prob.measurable_of_measurable_coe,
    exact (
      @induction_on_inter _
      (measurable_prod_bind_ret ν)
      ({E | ∃ (A : set α) (B : set β), (E = A.prod B) ∧ is_measurable A ∧ is_measurable B})
      _ measure_rect_generate_from measure_rect_inter (measurable_prod_bind_ret_empty ν) (measurable_prod_bind_ret_basic ν) (measurable_prod_bind_ret_compl ν) (measurable_prod_bind_ret_union ν)
      ),
end


end giry_prod


section fubini

variables {α : Type u} {β : Type u} [measure_space α] [measure_space β]

open to_integration






local notation  `∫` f `𝒹`m := integral m.to_measure f


lemma integral_char_rect [measurable_space α] [measurable_space β] [n₁ : nonempty α] [n₂ : nonempty β](μ : probability_measure α) (ν : probability_measure β)  {A : set α} {B : set β} (hA : is_measurable A) (hB : is_measurable B) :
(∫ χ ⟦ A.prod B ⟧ 𝒹(μ ⊗ₚ ν)) = (μ A) * (ν B) :=
begin
  haveI := (nonempty_prod.2 (and.intro n₁ n₂)),
  rw [integral_char_fun _ (is_measurable.prod hA hB),←coe_eq_to_measure,
  (prod.prob_measure_apply _ _ hA hB)], simp,
end


--lemma measurable_integral_fst {f : α × β → ennreal}(hf : measurable f) (ν : probability_measure β) : measurable (λ x:α, (∫ (λ y:β, f(x,y)) 𝒹 ν)) :=
--begin
--  conv{congr,funext,rw integral, rw @lintegral_eq_supr_eapprox_integral β {μ := ν.to_measure} (λ y, f(x,y)) (snd_comp_measurable hf _),},
--  refine measurable.supr _,
--  assume i,
--  dunfold simple_func.integral,
--  sorry,
--end




end fubini


section prod_measure_measurable

/-
This section aims to prove `measurable (λ x : α , f x ⊗ₚ g x)` using Dynkin's π-λ theorem.
Push this back to giry_monad.lean
-/

variables {α : Type u} {β : Type u} {γ : Type u}

def measurable_prod_measure_pred [measurable_space α] [measurable_space β] [measurable_space γ] {f : α → probability_measure β} {g : α → probability_measure γ} (hf : measurable f) (hg : measurable g) : set (β × γ) → Prop := λ s : set (β × γ), measurable (λ b:α,(f b ⊗ₚ g b) s)


lemma measurable_rect_empty {γ : Type u} [measurable_space α] [measurable_space β] [measurable_space γ] {f : α → probability_measure β} {g : α → probability_measure γ} (hf : measurable f) (hg : measurable g): measurable (λ b:α,(f b ⊗ₚ g b) ∅) :=
by simp ; exact measurable_const


lemma measure_rect_union {γ : Type u} [measurable_space α] [measurable_space β] [measurable_space γ] (f : α → probability_measure β) (g : α → probability_measure γ) : ∀h:ℕ → set (β × γ), (∀i j, i ≠ j → h i ∩ h j ⊆ ∅) → (∀i, is_measurable (h i)) → (∀i, measurable (λ b:α,(f b ⊗ₚ g b) (h i))) → measurable (λ b:α,(f b ⊗ₚ g b) (⋃i, h i)) :=
begin
  rintros h hI hA hB,
  unfold_coes,
  conv{congr,funext,rw [m_Union _ hA hI]},
  dsimp,
  conv{congr,funext,rw ennreal.tsum_eq_supr_nat,},
  refine measurable.comp measurable_to_nnreal _,
  apply measurable_supr, intro i,
  apply finset.measurable_sum, assume i,
  refine measurable_of_ne_top _ _ _, assume a,
  refine probability_measure.to_measure_ne_top _ _, solve_by_elim,
end


lemma measurable_rect_compl {γ : Type u} [measurable_space α] [measurable_space β] [measurable_space γ](f : α → probability_measure β) (g : α → probability_measure γ) :  ∀ t : set (β × γ), is_measurable t → measurable (λ b:α,(f b ⊗ₚ g b) t) → measurable (λ b:α,(f b ⊗ₚ g b) (- t)) :=
begin
  intros t ht hA,
  rw compl_eq_univ_diff,
  conv{congr, funext, rw [probability_measure.prob_diff _ (subset_univ _) is_measurable.univ ht]}, simp,
  refine measurable.comp _ hA,
  refine measurable.comp _ (measurable.sub measurable_const _),
  exact nnreal.continuous_of_real.measurable,
  exact nnreal.continuous_coe.measurable,
end

-- Move back to Giry monad
lemma measurable_measure_kernel [measurable_space α] [measurable_space β] {f : α → measure β} {A : set β} (hf : measurable f) (hA : is_measurable A) : measurable (λ a, f a A) :=
 measurable.comp (measurable_coe hA) hf


lemma measurable_rect_basic {γ : Type u} [measurable_space α] [measurable_space β] [measurable_space γ] [nonempty β] [nonempty γ] {f : α → probability_measure β} {g : α → probability_measure γ} (hf : measurable f) (hg : measurable g) : ∀ (t : set (β × γ)),t ∈ {E : set (β × γ) | ∃ (A : set β) (B : set γ), E = set.prod A B ∧ is_measurable A ∧ is_measurable B} → measurable (λ b:α,(f b ⊗ₚ g b) t) :=
begin
  rintros t ⟨A, B, rfl, hA, hB⟩,
  simp [prod.prob_measure_apply _ _ hA hB],
  exact measurable.mul (prob.measurable_measure_kernel hf hA) (prob.measurable_measure_kernel hg hB),
end

theorem measurable_pair_measure {γ : Type u} [measurable_space α] [measurable_space β] [measurable_space γ] [nonempty β] [nonempty γ]{f : α → probability_measure β} {g : α → probability_measure γ} (hf : measurable f) (hg : measurable g) : measurable (λ x : α , f x ⊗ₚ g x) :=
begin
  apply prob.measurable_of_measurable_coe,
  exact
    @induction_on_inter _
    (measurable_prod_measure_pred hf hg)
    ({E | ∃ (A : set β) (B : set γ), (E = A.prod B) ∧ is_measurable A ∧ is_measurable B}) _
    (measure_rect_generate_from)  (measure_rect_inter) (measurable_rect_empty hf hg) (measurable_rect_basic hf hg) (measurable_rect_compl f g)   (measure_rect_union f g),
end


end prod_measure_measurable



section giry_vec
/-
Auxilary lemmas about vectors as iterated binary prodcuts.
-/
variable {α : Type u}

def vec : Type u → ℕ → Type u
| A 0 := A
| A (succ k) := A × vec A k

@[simp] def kth_projn : Π {n}, vec α n → dfin (succ n) → α
| 0 x  _             := x
| (succ n) x dfin.fz := x.fst
| (succ n) (x,xs) (dfin.fs k) := kth_projn xs k

def vec.set_prod {n : ℕ}(A : set α) (B : set (vec α n)) : set (vec α (succ n)) :=
do l ← A, xs ← B, pure $ (l,xs)

instance nonempty.vec [nonempty α] : ∀ n, nonempty (vec α n) :=
λ n,
begin
induction n with k ih,
rwa vec,
rw vec, apply nonempty_prod.2, exact (and.intro _inst_1 ih)
end

instance vec.measurable_space (n : ℕ) [m : measurable_space α]: measurable_space (vec α n) :=
begin
  induction n with k ih, exact m,
  rw vec,
  exact (m.comap prod.fst ⊔ ih.comap prod.snd)
end

noncomputable def vec.prod_measure [measurable_space α] (μ : probability_measure α)
: Π n : ℕ, probability_measure (vec α n)
| 0 := μ
| (succ k) := doₚ x ←ₚ μ ;
              doₚ xs ←ₚ (vec.prod_measure k);
              retₚ (x,xs)

noncomputable def vec.prod_measure' [measurable_space α] (μ : measure α)
: Π n : ℕ, measure (vec α n)
| 0 := μ
| (succ k) := doₐ x ←ₐ μ ;
              doₐ xs ←ₐ (vec.prod_measure' k);
              ret (x, xs)

instance vec.measure_space  [measurable_space α] (μ : probability_measure α) : Π n:ℕ, measure_space (vec α n)
| 0 := ⟨ μ.to_measure ⟩
| (succ k) := ⟨ (vec.prod_measure μ _).to_measure ⟩

-- Why doesn't refl work here?!
@[simp] lemma vec.prod_measure_eq (n : ℕ) [measurable_space α](μ : probability_measure α) :
(vec.prod_measure μ (n+1)) = μ ⊗ₚ (vec.prod_measure μ n)
:=
by dunfold vec.prod_measure;refl


lemma vec.inl_measurable [measurable_space α] (n : ℕ): ∀ xs : vec α n, measurable (λ x : α, (x, xs)) := inl_measurable

lemma vec.inr_measurable [measurable_space α] (n : ℕ): ∀ x : α, measurable (λ xs : vec α n,(x,xs)) := inr_measurable

lemma vec.dirac_prod_apply [measurable_space α]{A : set α} {n : ℕ} {B : set (vec α n)} (hA : is_measurable A) (hB : is_measurable B) (a : α) (as : vec α n) :
(ret (a,as) : measure (vec α (succ n))) (A.prod B) = ((ret a : measure α) A) * ((ret as : measure (vec α n)) B) := dirac.prod_apply hA hB _ _

@[simp] lemma vec.prod_measure_apply {n : ℕ} [measurable_space α][nonempty α] (μ : probability_measure α) (ν : probability_measure (vec α n)) {A : set α} {B : set (vec α n)}
(hA : is_measurable A) (hB : is_measurable B) :
(μ ⊗ₚ ν) (A.prod B) = μ (A) * ν (B) := prod.prob_measure_apply _ _ hA hB


def vec_map {α: Type} {β: Type} (f: α → β): Π n: ℕ, vec α n → vec β n
| 0 := λ x, f x
| (nat.succ n) := λ v, (f v.fst,vec_map n v.snd)

lemma kth_projn_map_comm {α: Type} {β: Type}:
    ∀ f: α → β,
    ∀ n: ℕ, ∀ v: vec α n,
    ∀ i: dfin (succ n),
    f (kth_projn v i) = kth_projn (vec_map f n v) i :=
begin
  intros f n,
  induction n; intros,
  {
      dunfold vec_map,
      cases i, simp,
      refl,
  },
  {
      cases v,
      cases i,
      {
          simp, dunfold vec_map, simp,
      },
      {
          simp,rw n_ih, refl,
      }
  }
end

lemma measurable_map {α: Type} {β: Type} [measurable_space α] [measurable_space β]:
    ∀ n: ℕ,
    ∀ f: α → β,
    measurable f →
    measurable (vec_map f n) :=
begin
    intros,
    induction n,
    {
        intros,
        dunfold vec_map,
        assumption,
    },
    {
        intros,
        dunfold vec_map,
        apply measurable.prod; simp,
        {
            apply measurable.comp,
            assumption,
            apply measurable.fst,
            apply measurable_id,
        },
        {
            apply measurable.comp,
            assumption,
            apply measurable.snd,
            apply measurable_id,
        }
    },
end

end giry_vec


section hoeffding_aux
open complex real

lemma abs_le_one_iff_ge_neg_one_le_one {x : ℝ} : (complex.abs x ≤ 1) ↔ (-1 ≤ x ∧ x ≤ 1) := by rw abs_of_real ; apply abs_le

lemma abs_neg_exp_sub_one_le_double {x : ℝ} (h₁ : complex.abs x ≤ 1)(h₂ : x ≥ 0): complex.abs(exp(-x) - 1) ≤ 2*x :=
calc
complex.abs(exp(-x) - 1)
    ≤ 2*complex.abs(-x) : @abs_exp_sub_one_le (-x) ((complex.abs_neg x).symm ▸ h₁)
... = 2*complex.abs(x)  : by rw (complex.abs_neg x)
... = 2*x               : by rw [abs_of_real,((abs_eq h₂).2)]; left; refl


lemma neg_exp_ge {x : ℝ} (h₀ : 0 ≤ x) (h₁ : x ≤ 1) : 1 - 2 * x ≤ exp (-x)
:=
begin
have h : -(2*x) ≤ exp(-x) -1, {
  apply (abs_le.1 _).left,
  rw ←abs_of_real, simp [-add_comm, -sub_eq_add_neg],
  apply abs_neg_exp_sub_one_le_double _ h₀, rw abs_le_one_iff_ge_neg_one_le_one, split, linarith, assumption,
  },
  linarith,
end


-- lemma pow_neg_exp_ge {x : ℝ} (h₀ : 0 ≤ x) (h₁ : x ≤ 1) (n : ℕ) : (1 - 2*x)^n ≤ exp (-n*x) :=
-- begin
-- induction n with k ih,
-- simp,
-- rw _root_.pow_succ, simp [-sub_eq_add_neg],
-- conv in (_ * x) {rw right_distrib}, rw real.exp_add,
-- rw (neg_eq_neg_one_mul x).symm,
-- apply mul_le_mul (neg_exp_ge h₀ h₁) ih _ _, swap,
-- apply le_of_lt (exp_pos (-x)),
-- sorry
-- end

end hoeffding_aux

instance : conditionally_complete_linear_order nnreal :=
{
 Sup := Sup,
  Inf     := Inf,
  le_cSup := assume s a x has, le_cSup x has,
  cSup_le := assume s a hs h,show Sup ((coe : nnreal → ℝ) '' s) ≤ a, from
    cSup_le (by simp [hs]) $ assume r ⟨b, hb, eq⟩, eq ▸ h hb,
  cInf_le := assume s a x has, cInf_le x has,
  le_cInf := assume s a hs h, show (↑a : ℝ) ≤ Inf ((coe : nnreal → ℝ) '' s), from
    le_cInf (by simp [hs]) $ assume r ⟨b, hb, eq⟩, eq ▸ h hb,
 decidable_le := begin assume x y, apply classical.dec end,
 .. nnreal.linear_ordered_semiring,
 .. lattice_of_decidable_linear_order,
 .. nnreal.order_bot
}
