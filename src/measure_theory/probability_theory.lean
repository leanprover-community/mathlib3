/-
Probability theory generalities. 
Some parts of this file are originally from 
https://github.com/johoelzl/mathlib/blob/c9507242274ac18defbceb917f30d6afb8b839a5/src/probability_theory/basic.lean

Authors: Johannes Holzl, Koundinya Vajjha
-/
import measure_theory.measure_space tactic.tidy measure_theory.giry_monad 

local attribute [instance] classical.prop_decidable

noncomputable theory 
open measure_theory ennreal lattice  measure_theory  measure_theory.measure set 

universe u



section
variables (α : Type*) [measurable_space α]

structure probability_measure extends measure_theory.measure α :=
(measure_univ : to_measure univ = 1)

instance : measurable_space (probability_measure α) :=
measure.measurable_space.comap probability_measure.to_measure

lemma measurable_to_measure :
  measurable (@probability_measure.to_measure α _) :=
measurable_space.le_map_comap

instance prob_measure_coe : has_coe (probability_measure α) (measure α) :=
⟨probability_measure.to_measure⟩

instance : has_coe_to_fun (probability_measure α) :=
⟨λ_, set α → nnreal, λp s, ennreal.to_nnreal (p.to_measure s)⟩
end


namespace probability_measure
section
parameters {α : Type*} [measurable_space α] (p : probability_measure α)


lemma to_measure_lt_top (s : set α) : p.to_measure s < ⊤ :=
lt_of_le_of_lt (measure_mono $ subset_univ s) $ p.measure_univ.symm ▸ coe_lt_top

lemma to_measure_ne_top (s : set α) : p.to_measure s ≠ ⊤ :=
lt_top_iff_ne_top.1 (to_measure_lt_top s)

lemma coe_eq_to_measure (s : set α) : (p s : ennreal) = p.to_measure s :=
coe_to_nnreal (to_measure_ne_top s)

@[simp] lemma prob_apply {α : Type u} [measurable_space α] {s : set α}(hs : is_measurable s) (p : probability_measure α) : 
(p : probability_measure α) s = ennreal.to_nnreal (p.to_measure s)
:= rfl

@[ext] lemma prob.ext {α} [measurable_space α] :
  ∀ {μ₁ μ₂ : probability_measure α}, (∀s, is_measurable s → μ₁ s = μ₂ s) → μ₁ = μ₂
| ⟨m₁, u₁⟩ ⟨m₂, u₂⟩ H := begin
  congr, refine measure.ext (λ s hs, _),
  have : (ennreal.to_nnreal (m₁ s) : ennreal) = ennreal.to_nnreal (m₂ s) :=
    congr_arg coe (H s hs),
  rwa [coe_to_nnreal, coe_to_nnreal] at this,
  apply lt_top_iff_ne_top.1 (lt_of_le_of_lt (measure_mono $ subset_univ s) $ by rw u₂ ; exact ennreal.lt_top_iff_ne_top.2 one_ne_top),
  apply lt_top_iff_ne_top.1 (lt_of_le_of_lt (measure_mono $ subset_univ s) $ by rw u₁ ; exact ennreal.lt_top_iff_ne_top.2 one_ne_top) 
end

@[simp] lemma prob_empty : p ∅ = 0 :=
by rw [← coe_eq_coe, coe_eq_to_measure, measure_empty, coe_zero]

@[simp] lemma prob_univ : p univ = 1 :=
by rw [← coe_eq_coe, coe_eq_to_measure]; exact p.measure_univ

@[simp] lemma prob_mono {s t} (h : s ⊆ t) : p s ≤ p t :=
by rw [← coe_le_coe, coe_eq_to_measure, coe_eq_to_measure]; exact measure_mono h

lemma prob_le_1 (a : set α):
 p a ≤ (1:nnreal) :=
begin
  intros,
  rewrite ← prob_univ p,
  apply prob_mono,
  apply subset_univ,
end

lemma prob_mono_null {s t} (h : t ⊆ s) (h₂ : p s = 0) : p t = 0 :=
by rw [← le_zero_iff_eq, ← h₂]; exact prob_mono p h

lemma prob_Union_null {β} [encodable β] {s : β → set α} (h : ∀ i, p (s i) = 0) : p (⋃i, s i) = 0 :=
begin
  rw [← coe_eq_coe, coe_eq_to_measure, measure_Union_null, coe_zero],
  assume i, specialize h i, rwa [← coe_eq_coe, coe_eq_to_measure] at h
end

theorem prob_union_le (s₁ s₂ : set α) : p (s₁ ∪ s₂) ≤ p s₁ + p s₂ :=
by simp only [coe_le_coe.symm, coe_add, coe_eq_to_measure]; exact measure_union_le _ _

lemma prob_union {s₁ s₂ : set α}
  (hd : disjoint s₁ s₂) (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) :
  p (s₁ ∪ s₂) = p s₁ + p s₂ :=
by simp only [coe_eq_coe.symm, coe_add, coe_eq_to_measure]; exact measure_union hd h₁ h₂

lemma prob_diff {s₁ s₂ : set α} (h : s₂ ⊆ s₁) (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) :
  p (s₁ \ s₂) = p s₁ - p s₂ :=
by simp only [coe_eq_coe.symm, coe_sub, coe_eq_to_measure];
  exact measure_diff h h₁ h₂ (to_measure_lt_top _ _)

lemma prob_diff_inter 
{a b : set α} (h₁ : is_measurable a) (h₂ : is_measurable b) :
p(b ∩ -a) + p(b ∩ a) = p(b) :=
begin
  have h :p(b) = p(b ∩ univ),
  by rewrite inter_univ b,
  rewrite [h,← compl_union_self a,set.inter_distrib_left,prob_union],
  have g : (b ∩ -a) ∩ (b ∩ a) = ∅, by rw [inter_left_comm,set.inter_assoc, compl_inter_self,inter_empty,inter_empty],
  apply disjoint_iff.2 g,
  {
    rewrite ← diff_eq,
    apply is_measurable.diff h₂ h₁,
  },
  apply is_measurable.inter h₂ h₁,
end

lemma prob_union_inter
(a b : set α) (g₁ : is_measurable a) (g₂ : is_measurable b) :
p(a ∪ b) + p(a ∩ b) = p(a) + p(b) :=
begin
  have h₁ : a ∪ b = a ∪ (b ∩ -a),by
    rw [set.union_distrib_left, union_compl_self a,inter_univ],
  have h₂ : is_measurable(b ∩ -a), by exact is_measurable.diff g₂ g₁,
  have h₃ : a ∩ (b ∩ -a) = ∅, by tidy,
  rw h₁, 
  rw [prob_union p (disjoint_iff.2 h₃) g₁ h₂],
  rw [←prob_diff_inter p g₁ g₂],
  rw add_assoc,
  rw inter_comm _ a,
end

lemma prob_comp (a : set α) (h: is_measurable a) : p(-a) + p(a) = 1 :=
begin
  intros, rw ← prob_univ p, rw [←prob_union], simp,
  exact disjoint_iff.2 (@compl_inter_self _ a),
  apply is_measurable.compl h,
  assumption,
end

/-- The Bonnferroni inequality. -/
lemma prob_add_le_inter_add_one
(a b : set α) (h_1 : is_measurable a) (h_2 : is_measurable b) :
p(a) + p(b) ≤ p(a ∩ b) + 1 :=
begin
  rw [← prob_union_inter p a b h_1 h_2, ← add_comm],
  exact add_le_add_left' (prob_le_1 p (a ∪ b)),
end

protected lemma nonempty : nonempty α :=
classical.by_contradiction $ assume h,
  have 0 = p univ, by rw [univ_eq_empty_iff.2 h]; exact p.prob_empty.symm,
  @zero_ne_one nnreal _ $ by rwa [p.prob_univ] at this

@[simp] lemma integral_const (r : ennreal) : integral p.to_measure (λa, r) = r :=
suffices integral p.to_measure (λa, ⨆ (h : a ∈ (univ : set α)), r) =
  r * p.to_measure univ, by rw [← coe_eq_to_measure] at this; simpa,
@lintegral_supr_const α { μ := p.to_measure } r _ is_measurable.univ


lemma integral_univ : integral p.to_measure (λ a, 1) = 1 := by simp

-- somehow we need δ ≤ 1 o/w coercion hell. 
lemma neq_prob_set {α : Type} [measurable_space α] (f : α → nnreal) (μ : probability_measure α) (ε δ : nnreal) (hd : δ ≤ 1) (hS : is_measurable ({x : α | f x > ε})) : μ({x : α | f x > ε}) ≤ δ ↔ μ ({x : α | f x ≤ ε}) ≥ 1 - δ :=
begin
  rw ← nnreal.coe_le_coe,
  have h₀ : {x : α | f x > ε} = - {x : α | f x ≤ ε},by tidy, 
  have h₁ : - {x : α | f x > ε} = {x : α | f x ≤ ε}, by tidy,
  have h₃ : (μ ({x : α | f x > ε}) : ℝ) + μ{x : α | f x ≤ ε} = 1, {
    rw ←nnreal.coe_add, rw h₀, rw prob_comp, simp, rw ←h₁, 
    apply is_measurable.compl hS,
  },
  have h₅ : (μ ({x : α | f x > ε}) : ℝ) = 1 - μ ({x : α | f x ≤ ε}),
  {
    rw ←h₃, symmetry, rw add_sub_cancel,
  },
  rw h₅, rw sub_le_iff_le_add',
  rw add_comm, rw ←sub_le_iff_le_add', rw ←nnreal.coe_one,
  rw ←nnreal.coe_sub, rw nnreal.coe_le_coe, exact hd,
end


lemma neq_prob_set' {α : Type} [measurable_space α] (f : α → nnreal) (μ : probability_measure α) (ε δ : nnreal) (hd : δ ≤ 1) (hS : is_measurable ({x : α | f x > ε})) : μ({x : α | f x > ε}) ≤ δ ↔ μ ({x : α | f x ≤ ε}) + δ ≥ 1 :=
begin
  have h₀ : {x : α | f x > ε} = - {x : α | f x ≤ ε},by tidy, 
  have h₁ : - {x : α | f x > ε} = {x : α | f x ≤ ε}, by tidy,
  have h₃ : (μ ({x : α | f x > ε})) + μ{x : α | f x ≤ ε} = 1, {
    rw h₀, rw prob_comp, rw ←h₁, apply is_measurable.compl hS,
  },
  symmetry, rw ← h₃, rw add_comm, 
  rw ←add_le_add_iff_right,
end

lemma prob_trivial {α: Type} [measurable_space α]:
    ∀ P: α → Prop, ∀ μ: probability_measure α, 
    (∀ x, P x) → μ {x: α | P x} = 1 :=
begin
    intros, 
    have UNIV : {x: α | P x} = univ, 
    {
        apply eq_univ_of_forall,
        intro,
        rw mem_set_of_eq,
        apply a,
    },
    rw UNIV,
    apply prob_univ,
end 

end


end probability_measure


section giry_monad

variables {α : Type*} {β : Type*} {γ : Type*}
variables [measurable_space α] [measurable_space β] [measurable_space γ]

def pure (a : α) : probability_measure α :=
⟨measure.dirac a, by rw [measure_theory.measure.dirac_apply a is_measurable.univ]; simp⟩

def map (f : α → β) (p : probability_measure α) : probability_measure β :=
if h : measurable f then
  ⟨measure.map f p, by rw [measure_theory.measure.map_apply h is_measurable.univ, preimage_univ]; exact p.measure_univ⟩
else
  pure (f $ classical.choice p.nonempty)

def join (m : probability_measure (probability_measure α)) : probability_measure α :=
⟨measure_theory.measure.bind m.to_measure probability_measure.to_measure,
  by rw [measure_theory.measure.bind_apply is_measurable.univ (measurable_to_measure α)];
    simp [probability_measure.measure_univ]⟩

def bind (m : probability_measure α) (f : α → probability_measure β) : probability_measure β :=
join (map f m)

def dirac (a : α) : probability_measure α :=
⟨ measure.dirac a , by rw [dirac_apply _ is_measurable.univ]; simp ⟩



@[simp] theorem map_apply {f : α → β} (μ : probability_measure α) (hf : measurable f)
  {s : set β} (hs : is_measurable s) :
  (map f μ : probability_measure β) s = μ (f ⁻¹' s) := 
begin
  rw _root_.map, rw dif_pos hf, unfold_coes, congr, simp, apply measure_theory.measure.map_apply hf hs,
end
 

@[simp] lemma join_apply {m : probability_measure (probability_measure α)} :
  ∀{s : set α}, is_measurable s → (join m : probability_measure α) s = (integral m.to_measure (λμ, μ s)).to_nnreal :=
begin
  intros s hs,
  rw _root_.join, 
  transitivity, 
  unfold_coes, congr, simp, transitivity,
  refine measure_theory.measure.bind_apply hs (measurable_to_measure _),
  congr, funext, symmetry, transitivity,
  apply coe_to_nnreal, apply probability_measure.to_measure_ne_top, refl,
end


lemma prob.measurable_coe {s : set α} (hs : is_measurable s) : measurable (λμ : probability_measure α, μ s) :=
begin
  have h : (λ (μ : probability_measure α), μ s) = 
  (λ μ:measure α, (μ s).to_nnreal) ∘ (λ μ:probability_measure α, μ.to_measure),by refl,
  rw h,
  refine measurable.comp _ (measurable_to_measure _),
  refine measurable.comp _ (measurable_coe hs),
  refine measurable_of_measurable_nnreal _, simp,
  exact measurable_id,
end

-- TODO(Kody) : Get rid of the tidy part at the end. (Makes it slow!)
lemma prob.measurable_coe_iff_measurable_to_measure (f : β → probability_measure α) :
measurable f ↔ measurable ((λ μ:probability_measure α, μ.to_measure) ∘ f ) := 
begin
  fsplit, 
  {intro hf, exact measurable.comp (measurable_to_measure _) hf},
  {intros hf s hs,
  refine measurable_space.comap_le_iff_le_map.1 _ _ _, 
  exact measure.measurable_space.comap probability_measure.to_measure
  ,
  simp, tidy,}
end


lemma prob.measurable_measure_kernel [measurable_space α] [measurable_space β] {f : α → probability_measure β} {A : set β} (hf : measurable f) (hA : is_measurable A) : measurable (λ a, f a A) :=
 measurable.comp (prob.measurable_coe hA) hf

-- Rethink and rename these. 
instance (β : Type u): measurable_space (set β) := ⊤ 

lemma prob_super [measurable_space α] [measurable_space β] {f: α → set β} (hf : measurable f) (μ : probability_measure β) :
measurable (λ x, μ (f x)) := 
begin
refine measurable.comp _ hf,
intros i a, fsplit,  
end

lemma measurable_to_nnreal : measurable (ennreal.to_nnreal) := measurable_of_measurable_nnreal measurable_id

lemma measurable_to_nnreal_comp_of_measurable  (f: α → ennreal) : (measurable f) → measurable (λ x, ennreal.to_nnreal (f x)) :=
assume h, measurable.comp measurable_to_nnreal h


lemma measurable_of_ne_top (f : α → ennreal) (h : ∀ x, (f x) ≠ ⊤) (hf : measurable(λ x, ennreal.to_nnreal (f x))): measurable (λ x, f x)  :=
begin
  have h₀ : ∀ x, ↑((f x).to_nnreal) = f x, assume x, rw coe_to_nnreal (h x),
  conv{congr,funext, rw ←h₀,},
  apply measurable.comp measurable_coe hf, 
end

lemma prob.measurable_of_measurable_coe (f : β → probability_measure α)
  (h : ∀(s : set α) (hs : is_measurable s), measurable (λb, f b s)) :
  measurable f :=
begin
  rw prob.measurable_coe_iff_measurable_to_measure, 
  apply measurable_of_measurable_coe,
  intros s hs,
  conv{congr,funext,rw function.comp_apply,},
  refine measurable_of_ne_top _ _ _,
  intro x, refine probability_measure.to_measure_ne_top _ _,
  exact h _ hs,
 end

@[simp] lemma bind_apply {m : probability_measure α} {f : α → probability_measure β} {s : set β}
  (hs : is_measurable s) (hf : measurable f) : (bind m f : probability_measure β) s = (integral m.to_measure (λa, f a s)).to_nnreal :=
begin
  rw _root_.bind, rw _root_.join_apply hs, congr,
  have h : (_root_.map f m).to_measure = map f m.to_measure,{
    apply measure.ext, intros s hs, rw measure_theory.measure.map_apply hf hs, 
    rw _root_.map, rw dif_pos hf,unfold_coes, simp, apply measure_theory.measure.map_apply hf hs,
  },
  rw h, rw integral_map _ hf,
  refine measurable.comp measurable_coe _,
  exact prob.measurable_coe hs,
end

attribute [irreducible] pure map join bind

infixl ` >>=ₚ `:55 :=  _root_.bind 
infixl ` <$>ₚ `:55 := _root_.map 

notation `doₚ` binders ` ←ₚ ` m ` ; ` t:(scoped p, m >>=ₚ p) := t

notation `retₚ` := _root_.dirac  

lemma ret_to_measure {γ : Type u} [measurable_space γ] : ∀  (x:γ), (retₚ x).to_measure = measure.dirac x := assume x, rfl

def prod.prob_measure [measurable_space α][measurable_space β] (μ : probability_measure α) (ν : probability_measure β) : probability_measure (α × β) := 
doₚ x ←ₚ μ ; 
doₚ y ←ₚ ν ;
  retₚ (x, y)

infixl ` ⊗ₚ `:55 :=  prod.prob_measure 

/- TODO(Kody) : 
   1) shorten these proofs by using the ones proven for measures.
   2) Make a simp lemma to get rid of the conv block.
-/ 
lemma prob_inl_measurable_dirac [measurable_space α][measurable_space β]  : ∀ y : β,  measurable (λ (x : α), retₚ (x, y)) := assume y, 
begin
  rw prob.measurable_coe_iff_measurable_to_measure,
  apply measurable_of_measurable_coe, intros s hs,
  conv{congr,funext,rw function.comp_apply, rw _root_.dirac,},
  simp [hs,mem_prod_eq,supr_eq_if],
  apply measurable_const.if _ measurable_const,
  apply measurable.preimage _ hs,  
  apply measurable.prod, dsimp, exact measurable_id, 
  dsimp, exact measurable_const, 
end

lemma prob_inr_measurable_dirac [measurable_space β][measurable_space α] : ∀ x : α,  measurable (λ (y : β), retₚ (x, y)) := assume x, begin
  rw prob.measurable_coe_iff_measurable_to_measure,
  apply measurable_of_measurable_coe, intros s hs,
  conv{congr,funext,rw function.comp_apply, rw _root_.dirac,},
  simp [hs,mem_prod_eq,supr_eq_if],
  apply measurable_const.if _ measurable_const,
  apply measurable.preimage _ hs,  
  apply measurable.prod, dsimp,  exact measurable_const, 
  dsimp, exact measurable_id,  
end

/- TODO(Kody): Duplication of proofs.
  Why do I need to manually `change` the goal? 
-/
@[simp] lemma prob.dirac_apply {A : set α} {B : set β} (hA : is_measurable A) (hB : is_measurable B) (a : α) (b : β) :
 (retₚ (a,b) : measure (α × β)) (A.prod B) = ((retₚ a : measure α) A) * ((retₚ b : measure β) B) :=
begin
  rw _root_.dirac, rw _root_.dirac,rw _root_.dirac, 
  unfold_coes, simp,
  change ((( measure.dirac (a,b) : measure (α × β)) (A.prod B)) = (measure.dirac a : measure α) A * (measure.dirac b : measure β) B),
  rw [dirac_apply, dirac_apply, dirac_apply, mem_prod_eq], 
  dsimp,
  by_cases Ha: (a ∈ A); by_cases Hb: (b ∈ B), 
  repeat {simp [Ha, Hb]},
  repeat {assumption}, 
  exact is_measurable.prod hA hB, 
end

@[simp] lemma prob.dirac_apply' {A : set α} {B : set β} (hA : is_measurable A) (hB : is_measurable B) (a : α) (b : β) :
 ((retₚ(a,b)).to_measure : measure (α × β)) (A.prod B) = (((retₚ a).to_measure : measure α) A) * (((retₚ b).to_measure : measure β) B)
:=
begin
rw _root_.dirac,rw _root_.dirac,rw _root_.dirac,
unfold_coes, simp, 
 change ((( measure.dirac (a,b) : measure (α × β)) (A.prod B)) = (measure.dirac a : measure α) A * (measure.dirac b : measure β) B),
  rw [dirac_apply, dirac_apply, dirac_apply, mem_prod_eq], 
  dsimp,
  by_cases Ha: (a ∈ A); by_cases Hb: (b ∈ B), 
  repeat {simp [Ha, Hb]},
  repeat {assumption}, 
  exact is_measurable.prod hA hB, 
end

end giry_monad

section cond_prob

noncomputable def cond_prob {α : Type*} [measurable_space α] (p : probability_measure α) (a b : set α) := p(a ∩ b)/p(b)


notation `ℙ^`:95 p `[[`:95 a ` | `:95 b `]]`:0 := cond_prob p a b

parameters {α : Type*} [measurable_space α] (p : probability_measure α)


lemma cond_prob_rw
(a b : set α) (h₁ : p(b) ≠ 0):
p(a ∩ b) = ℙ^p [[ a | b ]] * p(b) :=
begin
  unfold cond_prob,
  rw [nnreal.div_def,mul_assoc],
  have g₁ : (1 : ennreal) < ⊤,
  {
    rw lt_top_iff_ne_top,
    apply ennreal.one_ne_top,
  },
  have g₂ : ∀ a, (p(a) ≠ 0) → (p(a))⁻¹ * p(a) = 1,
  {
    intros a k,
    rw mul_comm,
    apply nnreal.mul_inv_cancel, exact k,
  },
  rw g₂ b h₁, simp,
end

/-- Bayes theorem for two sets. -/
theorem cond_prob_swap
{a b : set α} (h₁ : p a ≠ 0) (h₂ : p b ≠ 0) :
ℙ^p [[ b | a ]] * p(a) =  ℙ^p [[ a | b ]] * p(b) :=
begin
  unfold cond_prob,
  rw [nnreal.div_def,mul_assoc],
  have g₁ : (1 : ennreal) < ⊤,
  {
    rw lt_top_iff_ne_top,
    apply ennreal.one_ne_top,
  },
  have g₂ : ∀ a, (p(a) ≠ 0) → (p(a))⁻¹ * p(a) = 1,
  {
    intros a k,
    rw mul_comm,
    apply nnreal.mul_inv_cancel, exact k,
  },
  rw [g₂ a,nnreal.div_def,mul_assoc,g₂ b, mul_one],
  symmetry, rw [mul_one,set.inter_comm],
  assumption, assumption,
end

end cond_prob

section giry_prod



end giry_prod