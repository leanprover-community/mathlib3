/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import topology.local_homeomorph
import topology.homotopy.basic

universes u v w

structure covering_map (X' : Type u) (X : Type v) [topological_space X'] [topological_space X]
  extends C(X', X) :=
(nbhd : X → set X)
(mem_nbhd : ∀ y, y ∈ nbhd y)
(local_homeos : X → set (local_homeomorph X' X))
(local_homeos_target : ∀ y, ∀ (f : local_homeomorph X' X),
  f ∈ local_homeos y → f.target = nbhd y)
(local_homeos_source_disjoint : ∀ y, ∀ (f g : local_homeomorph X' X),
  f ∈ local_homeos y → g ∈ local_homeos y → f ≠ g → f.source ∩ g.source = ∅)
(local_homeos_restrict : ∀ y, ∀ (f : local_homeomorph X' X), f ∈ local_homeos y →
  ∀ x ∈ f.source, f x = to_fun x)
(local_homeos_cover' : ∀ y, ∀ x ∈ to_fun ⁻¹' nbhd y,
  ∃ (f : local_homeomorph X' X), f ∈ local_homeos y ∧ x ∈ f.source)

namespace covering_map

variables {X' : Type u} {X : Type v} {Y : Type w}
variables [topological_space X'] [topological_space X] [topological_space Y]

def sources (p : covering_map X' X) (x : X) : set (set X') :=
(λ f : local_homeomorph X' X, f.source) '' p.local_homeos x

instance : has_coe_to_fun (covering_map X' X) (λ _, X' → X):= ⟨λ p, p.to_fun⟩

lemma local_homeos_cover (p : covering_map X' X) (x : X) (y : X') (hy : p y ∈ p.nbhd x) :
  ∃ V ∈ p.sources x, y ∈ V :=
begin
  rcases p.local_homeos_cover' x y hy with ⟨f, hf₀, hf₁⟩,
  refine ⟨f.source, ⟨f, hf₀, rfl⟩, hf₁⟩,
end

lemma is_open_of_mem_sources (p : covering_map X' X) {x : X} {V : set X'} (hV : V ∈ p.sources x) :
  is_open V :=
begin
  rcases hV with ⟨f, hf₀, hf₁⟩,
  rw ←hf₁,
  exact f.open_source,
end

def of_homeomorph (h : X' ≃ₜ X) : covering_map X' X :=
{ to_fun := h,
  nbhd := λ _, set.univ,
  mem_nbhd := λ _, trivial,
  local_homeos := λ _, {h.to_local_homeomorph},
  local_homeos_target := λ y f hf, by simp * at *,
  local_homeos_source_disjoint := λ y f g hf hg h, by simp * at *,
  local_homeos_restrict := λ y f hf x hx, by simp * at *,
  local_homeos_cover' := λ y x hx, ⟨h.to_local_homeomorph, by simp * at *⟩ }

example (p : covering_map X' X) (f : C(Y, X)) (f₀ f₁ : C(Y, X'))
  (hf₀ : p.to_continuous_map.comp f₀ = f) (hf₁ : p.to_continuous_map.comp f₁ = f) :
  is_clopen {y | f₀ y = f₁ y} :=
begin
  split,
  { rw is_open_iff_forall_mem_open,
    rintros y (hy : f₀ y = f₁ y),
    have hpf₀y : p (f₀ y) ∈ p.nbhd (f y),
    { change p (f₀ y) with p.to_continuous_map.comp f₀ y,
      rw hf₀,
      exact p.mem_nbhd _ },
    rcases p.local_homeos_cover (f y) (f₀ y) hpf₀y with ⟨V, hV₀, hV₁⟩,
    have hVopen : is_open V := p.is_open_of_mem_sources hV₀,
    let N := f₀ ⁻¹' V ∩ f₁ ⁻¹' V,
    have hNopen : is_open N :=
      (hVopen.preimage f₀.continuous).inter (hVopen.preimage f₁.continuous),
    refine ⟨N, _, hNopen, ⟨hV₁, (hy ▸ hV₁ : f₁ y ∈ V)⟩⟩,
    rcases hV₀ with ⟨F, hF₀, hF₁⟩,
    intros n hn,
    have hn₀ : f₀ n ∈ V := hn.1,
    have hn₁ : f₁ n ∈ V := hn.2,
    rw ←hF₁ at hn₀ hn₁,
    have hp₀ := p.local_homeos_restrict _ _ hF₀ _ hn₀,
    have hp₁ := p.local_homeos_restrict _ _ hF₀ _ hn₁,
    have : F (f₀ n) = F (f₁ n),
    { rw [hp₀, hp₁],
      rw ←hf₁ at hf₀,
      exact congr_fun (congr_arg coe_fn hf₀) _ },
    exact F.inj_on hn₀ hn₁ this },
  { rw is_closed_iff_nhds,
    intros y hy,
    let U := p.nbhd (f y),
    have hU₀ : p (f₀ y) ∈ U,
    { change p (f₀ y) with p.to_continuous_map.comp f₀ y,
      rw hf₀,
      exact p.mem_nbhd _ },
    have hU₁ : p (f₁ y) ∈ U,
    { change p (f₁ y) with p.to_continuous_map.comp f₁ y,
      rw hf₁,
      exact p.mem_nbhd _ },
    rcases p.local_homeos_cover (f y) (f₀ y) hU₀ with ⟨V, hV₀, hV₁⟩,
    rcases p.local_homeos_cover (f y) (f₁ y) hU₁ with ⟨W, hW₀, hW₁⟩,
    let N := f₀ ⁻¹' V ∩ f₁ ⁻¹' W,
    have hNopen : is_open N :=
      ((p.is_open_of_mem_sources hV₀).preimage f₀.continuous).inter
        ((p.is_open_of_mem_sources hW₀).preimage f₁.continuous),
    have hNnhds : N ∈ nhds y,
    { rw mem_nhds_iff,
      exact ⟨N, set.subset.refl _, hNopen, hV₁, hW₁⟩ },
    rcases hy N hNnhds with ⟨t, ⟨ht₁, ht₂⟩, ht₃⟩,
    sorry }
end

end covering_map
