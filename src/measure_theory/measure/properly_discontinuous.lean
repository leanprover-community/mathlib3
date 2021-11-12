import topology.homeomorph
import group_theory.group_action.basic
import topology.algebra.mul_action

namespace homeomorph

lemma trans_assoc {T₁ T₂ T₃ T₄ : Type*} [topological_space T₁] [topological_space T₂]
[topological_space T₃] [topological_space T₄] (a : T₁ ≃ₜ T₂) (b : T₂ ≃ₜ T₃) (c : T₃ ≃ₜ T₄)
: (a.trans b).trans c = a.trans (b.trans c) := ext $ λ e, rfl

theorem trans_apply {T₁ T₂ T₃: Type*} [topological_space T₁] [topological_space T₂]
[topological_space T₃] (f : T₁ ≃ₜ T₂) (g : T₂ ≃ₜ T₃) (a : T₁) : (f.trans g) a = g (f a) := rfl

@[simp] theorem trans_refl {T₁ T₂ : Type*} [topological_space T₁] [topological_space T₂]
(e : T₁ ≃ₜ T₂) : e.trans (homeomorph.refl T₂) = e := ext $ λ x, rfl

@[simp] theorem refl_trans {T₁ T₂ : Type*} [topological_space T₁] [topological_space T₂]
(e : T₁ ≃ₜ T₂) : (homeomorph.refl T₁).trans e = e := ext $ λ x, rfl

@[simp] theorem symm_trans  {T₁ T₂ : Type*} [topological_space T₁] [topological_space T₂]
(e : T₁ ≃ₜ T₂) : e.symm.trans e = homeomorph.refl T₂ := ext $ λ x, e.apply_symm_apply x

@[simp] theorem trans_symm  {T₁ T₂ : Type*} [topological_space T₁] [topological_space T₂]
(e : T₁ ≃ₜ T₂) : e.trans e.symm = homeomorph.refl T₁ := ext $ λ x, e.symm_apply_apply x

instance {T : Type*} [topological_space T] : group (homeomorph T T) :=
{ mul := homeomorph.trans,
  mul_assoc := trans_assoc,
  one := homeomorph.refl T,
  one_mul := refl_trans,
  mul_one := trans_refl,
  inv := homeomorph.symm,
  mul_left_inv := symm_trans }

end homeomorph

variables {T : Type*} [topological_space T] {Γ : Type*} [group Γ] (φ : Γ →* (homeomorph T T))
--[mul_action G T] [has_continuous_smul G T]

def foo : setoid T := { r := λ x y, ∃ γ, φ γ x = y,
  iseqv := begin
    split,
    sorry,
    split,
    sorry,
    sorry,
  end}

def properly_discontinuous : Prop := ∀ (K L : set T), is_compact K → is_compact L →
  set.finite {γ : Γ | ((φ γ) '' K) ∩ L ≠ ∅ }

lemma is_t2_of_properly_discontinuous_of_t2 [t2_space T] [locally_compact_space T]
(h : properly_discontinuous φ) : t2_space (quotient (foo φ)) :=
{ t2 := begin
  let f : T → quotient (foo φ) := @quotient.mk _ (foo φ),
  intros x y hxy,
  obtain ⟨x₀, hx₀⟩ := @quotient.exists_rep _ (foo φ) x,
  obtain ⟨y₀, hy₀⟩ := @quotient.exists_rep _ (foo φ) y,
  have hγx₀y₀ : ∀ γ : Γ, φ γ x₀ ≠ y₀,
  {
    intros γ,
    sorry,
    -- exact hxy,
  },
  have hx₀y₀ : x₀ ≠ y₀ := sorry,
  obtain ⟨u₀, v₀, open_u₀, open_v₀, x₀_in_u₀, y₀_in_v₀, hu₀v₀⟩ := t2_separation hx₀y₀,
  obtain ⟨K₀, K₀_is_cpt, x₀_in_K₀, K₀_in_u₀⟩ := exists_compact_subset open_u₀ x₀_in_u₀,
  obtain ⟨L₀, L₀_is_cpt, y₀_in_L₀, L₀_in_v₀⟩ := exists_compact_subset open_v₀ y₀_in_v₀,
  let bad_Γ_set := {γ : Γ | ((φ γ) '' K₀) ∩ L₀ ≠ ∅ },
  have bad_Γ_finite : bad_Γ_set.finite := h K₀ L₀ K₀_is_cpt L₀_is_cpt,
  choose uγ vγ is_open_uγ is_open_vγ γx₀_in_uγ y₀_in_vγ uγ_vγ_disjoin using
    λ γ, t2_separation (hγx₀y₀ γ),



  let cut_out_bits := ⋂ γ ∈ bad_Γ_set, ((φ γ) '' K₀)ᶜ,
  have all_open : ∀ γ, γ ∈ bad_Γ_set → is_open ((φ γ) '' K₀)ᶜ :=
    λ γ hγ, ( (K₀_is_cpt.image _).is_closed).is_open_compl,
  have cut_out_bits_is_open : is_open cut_out_bits := is_open_bInter bad_Γ_finite all_open,
  let V₀ := v₀ ∩ cut_out_bits,
  have V₀_is_open : is_open V₀ := is_open.inter open_v₀ cut_out_bits_is_open,
  let V := f '' V₀,
  have f_is_open_map : is_open_map f := sorry,
 -- := is_open.is_open_map_subtype_coe U₀_is_open,
  have V_open : is_open V := f_is_open_map _ V₀_is_open,
  let U := f '' (u₀),
  have U_open : is_open U := f_is_open_map _ open_u₀,
  have x_in_U : x ∈ U := ⟨x₀, x₀_in_u₀, by convert hx₀⟩,
  have y_in_V : y ∈ V,
  {
    refine ⟨y₀, _, _⟩,
    {
      refine (set.mem_inter_iff y₀ _ _).mpr ⟨y₀_in_v₀, _⟩,
      apply set.mem_bInter,
      intros γ hγ,
    },
    sorry,
    repeat {sorry},
  },
  refine ⟨U, V, U_open, V_open, _⟩,

end}
