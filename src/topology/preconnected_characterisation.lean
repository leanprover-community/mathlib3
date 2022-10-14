/-
Copyright (c) 2022 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import topology.connected
import algebra.indicator_function

/-!
# Characterisation of preconnected spaces in terms of continuous maps with discrete target

In this file we prove that a topological space is preconnected if,
and only if, every continuous map into a discrete space is constant.#check

## Main results

- `preconnected_space_iff_continuous_to_bool_imp_constant`: a topological space X is a
  preconnected_space if and only if every continuous map X → bool is constant
- `is_preconnected_iff_continuous_to_discrete_imp_constant`: a subset α of a topological
  space X is_preconnected if and only if for every discrete space Y, every map X → Y, which is
  continuous on α, is constant on α.
-/

noncomputable theory

instance has_zero_bool : has_zero bool := ⟨⊥⟩
def cst_top (X : Type*) : X → bool := λ x, ⊤
def cst_top' (X : Type) : X → bool := λ x, ⊤

lemma mem_iff_indicator_eq_top {X : Type*} (U : set X) (x : X) :
  x ∈ U ↔ set.indicator U (cst_top X) x = ⊤ :=
begin
  split,
  { intros hx,
    have hx' : set.indicator U (cst_top X) x = cst_top X x := set.indicator_of_mem hx _,
    rw hx',
    triv },
  { intros hx,
    have htop : ⊤ ≠ (0 : bool) := by tauto,
    rw ← hx at htop,
    exact set.mem_of_indicator_ne_zero htop },
end

lemma indicator_fibre_of_top_eq_set {X : Type*} (U : set X) :
  (set.indicator U (cst_top X) ) ⁻¹' {⊤} = U :=
begin
  ext,
  rw mem_iff_indicator_eq_top U x,
  triv,
end

lemma indicator_continuous_iff_clopen {X : Type*} (U : set X) [topological_space X] :
  continuous (set.indicator U (cst_top X)) ↔ is_clopen U :=
begin
  let f := (set.indicator U (cst_top X)),
  have h : ∀ s : set bool, (f ⁻¹' s) ∈ {set.univ, U, Uᶜ, ∅} :=
    λ s, set.indicator_const_preimage U s ⊤,
  split,
  { intros hc,
    have h₁ : ∀ s : set bool, is_open (f ⁻¹' s) := λ s, continuous_def.mp hc s trivial,
    have h₂ : ∀ s : set bool, is_closed (f ⁻¹' s) :=
      λ s, continuous_iff_is_closed.mp hc s (is_closed_discrete s),
    simp at *,
    specialize h {⊤},
    have hfibre : f ⁻¹' {⊤} = U := indicator_fibre_of_top_eq_set U,
    specialize h₁ {⊤},
    specialize h₂ {⊤},
    rw ← hfibre,
    exact ⟨h₁, h₂⟩ },
  { intros hU,
    refine {is_open_preimage := _},
    intros s hs,
    specialize h s,
    simp at *,
    cases h,
    { rw h, exact is_open_univ },
    cases h,
    { rw h, exact hU.1 },
    cases h,
    { rw h, refine is_open_compl_iff.mpr _, exact hU.2 },
    rw h, exact is_open_empty },
end

lemma indicator_continuous_on_iff_clopen {X : Type*} (α U : set X) [topological_space X] :
  continuous_on (set.indicator U (cst_top X)) α ↔ is_clopen (α.restrict U) :=
begin
  rw ← indicator_continuous_iff_clopen (α.restrict U),
  exact continuous_on_iff_continuous_restrict,
end

def continuous_to_discrete {X Y : Type*} (f : X → Y) [topological_space X] : Prop :=
  ∀ s : set Y, is_open (f ⁻¹' s)

lemma continuous_to_discrete_iff_continuous {X Y : Type*} (f : X → Y) [topological_space X]
  [topological_space Y] [discrete_topology Y] :
  continuous_to_discrete f ↔ continuous f :=
begin
  split, swap, { exact λ hf s, continuous_def.mp hf s (is_open_discrete s) },
  tidy,
end

def continuous_to_discrete_imp_constant {X Y : Type*} (α : set X) (f : X → Y)
  [topological_space X] : Prop :=
  continuous_to_discrete f → ∀ a b : X, a ∈ α → b ∈ α → f a = f b

def continuous_on_to_discrete {X Y : Type*} (α : set X) (f : X → Y) [topological_space X] : Prop :=
  ∀ s : set Y, is_open (α.restrict (f ⁻¹' s))

def continuous_on_to_discrete_imp_constant {X Y : Type*} (α : set X) (f : X → Y)
  [topological_space X] : Prop :=
  continuous_on_to_discrete α f → ∀ a b : X, a ∈ α → b ∈ α → f a = f b

lemma preconnected_space_iff_continuous_to_bool_imp_constant (X : Type*) [topological_space X] :
  preconnected_space X ↔ ∀ f : X → bool, continuous_to_discrete_imp_constant set.univ f :=
begin
  split,
  { intros hp f hf a b ha hb,
    by_contra,
    let U := f ⁻¹' {f a},
    let V := f ⁻¹' ({f a}ᶜ),
    rw continuous_to_discrete_iff_continuous f at hf,
    have hU : is_closed U,
    { refine is_closed.preimage hf _,
      exact is_closed_discrete _ },
    have hV : is_closed V,
    { refine is_closed.preimage hf _,
    exact is_closed_discrete _, },
    have haU : (set.univ ∩ U).nonempty,
    { use a,
      tidy },
    have haV : (set.univ ∩ V).nonempty,
    { use b,
      tidy },
    have haUuV : set.univ ⊆ U ∪ V,
    { intros x hx,
      by_cases hf : f x = f a,
      { left,
        exact hf },
      { right,
        exact hf } },
    have haUV : ¬(set.univ ∩ (U ∩ V)).nonempty := by tidy,
    apply haUV,
    cases hp,
    exact is_preconnected_closed_iff.mp hp U V hU hV haUuV haU haV },
  { intros h,
    fconstructor,
    intros U V hU hV hUnion hneU hneV,
    simp at *,
    by_contra h1,
    have heUV : (U ∩ V) = ∅,
    { rw ←  set.ne_empty_iff_nonempty at h1,
      tidy, },
    have h_V_in_Uc : V ⊆ Uᶜ :=
      disjoint.subset_compl_left (set.disjoint_iff_inter_eq_empty.mpr heUV),
    have hUnion' : set.univ = U ∪ V := by tidy,
    have h_V_eq_Uc : V = Uᶜ,
    { ext, split, { exact λ hx, h_V_in_Uc hx },
      intros hx,
      have hx' : x ∈ U ∪ V := hUnion trivial,
      cases hx',
      exfalso, { exact hx hx' }, { exact hx' } },
    have hcU : is_clopen U,
    { split, { exact hU },
      { refine {is_open_compl := _},
        rw ← h_V_eq_Uc, exact hV } },
    rw ← indicator_continuous_iff_clopen U at hcU,
    specialize h (set.indicator U (cst_top X)),
    rw ← continuous_to_discrete_iff_continuous _ at hcU, swap, { apply_instance },
    have habU := h hcU,
    obtain ⟨u, hu⟩ := hneU,
    obtain ⟨v, hv⟩ := hneV,
    specialize habU u v trivial trivial,
    rw h_V_eq_Uc at hv,
    apply hv,
    rw mem_iff_indicator_eq_top at hu,
    rw hu at habU,
    exact (mem_iff_indicator_eq_top U v).mpr habU.symm },
end

lemma is_preconnected_iff_continuous_to_bool_imp_constant {X : Type*} (α : set X)
  [topological_space X] [decidable_pred (∈ α)] :
  is_preconnected α ↔ ∀ f : X → bool, continuous_on_to_discrete_imp_constant α f :=
begin
  rw is_preconnected_iff_preconnected_space,
  rw preconnected_space_iff_continuous_to_bool_imp_constant α,
  split,
  { intros h f,
    specialize h (α.restrict f),
    intros hf a b ha hb,
    have hf' : continuous_to_discrete (α.restrict f) := hf,
    have h' := h hf' ⟨a, ha⟩ ⟨b, hb⟩ trivial trivial,
    exact h' },
  { intros h f,
    let f' : X → bool := λ x, if hx : x ∈ α then f ⟨x, hx⟩ else 0,
    specialize h f',
    intros hf a b ha hb,
    have hf' : f = α.restrict f' := by tidy,
    rw hf' at hf,
    have hf'' : continuous_on_to_discrete α f' := hf,
    have h' := h hf'',
    rw hf',
    tidy },
end

lemma is_preconnected_iff_continuous_to_discrete_imp_constant {X : Type*} (α : set X)
  [topological_space X] [decidable_pred (∈ α)] :
  is_preconnected α ↔ ∀ Y : Type, ∀ f : X → Y, continuous_on_to_discrete_imp_constant α f :=
begin
  rw is_preconnected_iff_continuous_to_bool_imp_constant α,
  split, swap, { exact λ h b, h bool b, },
  intros h Y f hf a b ha hb,
  specialize h ((set.indicator {f a} (cst_top' Y)) ∘ f),
  have hf' : continuous_on_to_discrete α ((set.indicator {f a} (cst_top' Y)) ∘ f),
  { intros s,
    have hs : is_open (α.restrict f ⁻¹' ((set.indicator {f a} (cst_top' Y)) ⁻¹' s)) := hf _,
    exact hs, },
  have hh := h hf',
  specialize hh a b,
  have hi := hh ha hb,
  have hia : ((set.indicator {f a} (cst_top' Y)) ∘ f) a = ⊤ := by tidy,
  rw hia at hi,
  have hib := @indicator_fibre_of_top_eq_set Y {f a},
  rw hi at hib,
  have hib' : {f b} ⊆ {f a},
  { rw ← hib,
    norm_num,
    simp at *,
    have hfb : {(set.indicator {f a} (cst_top' Y)) (f b)} =
      (set.indicator {f a} (cst_top' Y)) '' {f b} := by tidy,
    have hfb' := set.subset_preimage_image (set.indicator {f a} (cst_top' Y)) {f b},
    rw ← hfb at hfb',
    exact hfb', },
  tauto,
end
