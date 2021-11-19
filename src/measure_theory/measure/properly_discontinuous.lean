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

lemma quotient_preimage_image_eq_union (U : set T) :
(@quotient.mk _ (foo φ)) ⁻¹' ((@quotient.mk _ (foo φ)) '' U) = ⋃ γ : Γ, (φ γ) '' U :=
begin
  set f : T → quotient (foo φ) := @quotient.mk _ (foo φ),
  ext,
  split,
  { rintros ⟨y , hy, hxy⟩,
    obtain ⟨γ, rfl⟩ := @quotient.exact _ (foo φ) _ _  hxy,
    rw set.mem_Union,
    refine ⟨γ, y, ⟨hy, rfl⟩⟩, },
  {
    intros hx,
-- ALEX HOMEWORK
    sorry,
  },
end

lemma is_open_map_quotient_mk : is_open_map (@quotient.mk _ (foo φ)) :=
begin
  intros U hU,
  rw is_open_coinduced,
  let f : T → quotient (foo φ) := @quotient.mk _ (foo φ),
  rw quotient_preimage_image_eq_union φ U,
  apply is_open_Union,
  intros γ,
  exact (φ γ).is_open_map U hU,
end

lemma is_t2_of_properly_discontinuous_of_t2 [t2_space T] [locally_compact_space T]
(h : properly_discontinuous φ) : t2_space (quotient (foo φ)) :=
{ t2 := begin
  let f : T → quotient (foo φ) := @quotient.mk _ (foo φ),
  intros x y hxy,
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ = x := @quotient.exists_rep _ (foo φ) x,
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, f y₀ = y := @quotient.exists_rep _ (foo φ) y,

  have hγx₀y₀ : ∀ γ : Γ, φ γ x₀ ≠ y₀,
  { --- rewrite this as a calc proof
    intros γ,
    contrapose! hxy,
    have := congr_arg f hxy,
    rw ← hy₀,
    convert this,
    rw ← hx₀,
    apply quotient.sound _,
    use γ, },
  have hx₀y₀ : x₀ ≠ y₀ := by simpa using (hγx₀y₀ 1),
  obtain ⟨u₀, v₀, open_u₀, open_v₀, x₀_in_u₀, y₀_in_v₀, hu₀v₀⟩ := t2_separation hx₀y₀,
  obtain ⟨K₀, K₀_is_cpt, x₀_in_K₀, K₀_in_u₀⟩ := exists_compact_subset open_u₀ x₀_in_u₀,
  obtain ⟨L₀, L₀_is_cpt, y₀_in_L₀, L₀_in_v₀⟩ := exists_compact_subset open_v₀ y₀_in_v₀,
  let bad_Γ_set := {γ : Γ | ((φ γ) '' K₀) ∩ L₀ ≠ ∅ },
  have bad_Γ_finite : bad_Γ_set.finite := h K₀ L₀ K₀_is_cpt L₀_is_cpt,
  choose uγ vγ is_open_uγ is_open_vγ γx₀_in_uγ y₀_in_vγ uγ_vγ_disjoint using
    λ γ, t2_separation (hγx₀y₀ γ),

  let U₀₀ := ⋂ γ ∈ bad_Γ_set, ((φ γ) ⁻¹' (uγ γ)),
  have all_open : ∀ γ, γ ∈ bad_Γ_set → is_open ((φ γ) ⁻¹' (uγ γ)) :=
    λ γ hγ, is_open.preimage (φ γ).continuous (is_open_uγ γ),
  have U₀₀_is_open : is_open U₀₀ := is_open_bInter bad_Γ_finite all_open,
  let U₀ := U₀₀ ∩ (interior K₀),
  have U₀_is_open : is_open U₀ := is_open.inter U₀₀_is_open is_open_interior,
  let V₀₀ := ⋂ γ ∈ bad_Γ_set, (vγ γ),
  have V₀₀_is_open : is_open V₀₀ := is_open_bInter bad_Γ_finite (λ γ _, is_open_vγ γ),
  let V₀ := V₀₀ ∩ (interior L₀),
  have V₀_is_open : is_open V₀ := is_open.inter V₀₀_is_open is_open_interior,
  let V := f '' V₀,
  let U := f '' U₀,
  have f_is_open_map : is_open_map f := is_open_map_quotient_mk _,
  have V_open : is_open V := f_is_open_map _ V₀_is_open,
  have U_open : is_open U := f_is_open_map _ U₀_is_open,
  have x_in_U : x ∈ U,
  { refine ⟨x₀, _, hx₀⟩,
    rw set.mem_inter_iff,
    split,
    { apply set.mem_bInter,
      intros γ hγ,
      exact γx₀_in_uγ γ, },
    exact x₀_in_K₀, },
  have y_in_V : y ∈ V,
  { refine ⟨y₀, _, hy₀⟩,
    rw set.mem_inter_iff,
    split,
    { apply set.mem_bInter,
      intros γ hγ,
      exact y₀_in_vγ γ, },
    exact y₀_in_L₀, },
  have UV_disjoint : U ∩ V = ∅,
  { rw set.eq_empty_iff_forall_not_mem,
    intros z,
    rintros ⟨⟨x₁,x₁_in_U₀, f_x₁_z⟩, ⟨y₁,y₁_in_V₀, f_y₁_z⟩⟩,
    obtain ⟨γ₁, hγ₁⟩ := @quotient.exact _ (foo φ) _ _  (f_x₁_z.trans f_y₁_z.symm),
    by_cases hγ₁_bad : γ₁ ∈ bad_Γ_set,
    {
      have y₁_in_vγ₁ : y₁ ∈ vγ γ₁,
      { have := set.Inter_subset _ γ₁ (y₁_in_V₀.1),
        have := set.Inter_subset _ hγ₁_bad this,
        exact this, },
      have y₁_in_uγ₁ : y₁ ∈ uγ γ₁,
      { rw ← hγ₁,
        have := set.Inter_subset _ γ₁ (x₁_in_U₀.1),
        have := set.Inter_subset _ hγ₁_bad this,
        exact this, },
      have : y₁ ∈ uγ γ₁ ∩ vγ γ₁ := ⟨y₁_in_uγ₁, y₁_in_vγ₁⟩,
      rw (uγ_vγ_disjoint γ₁) at this,
      exact this,
    },
    { have y₁_in_L₀ : y₁ ∈ L₀ := interior_subset y₁_in_V₀.2,
      have x₁_in_K₀ : x₁ ∈ K₀ := interior_subset x₁_in_U₀.2,
      have y₁_in_γ₁K₀ : y₁ ∈ (φ γ₁) '' K₀,
      { rw ← hγ₁,
        exact ⟨x₁, ⟨x₁_in_K₀, rfl⟩⟩, },
      have γ₁K₀L₀_disjoint : (φ γ₁) '' K₀ ∩ L₀ = ∅ := by simpa [bad_Γ_set] using hγ₁_bad,
      have : y₁ ∈ (φ γ₁) '' K₀ ∩ L₀ := ⟨y₁_in_γ₁K₀, y₁_in_L₀⟩,
      rw (γ₁K₀L₀_disjoint) at this,
      exact this, }, },
  exact ⟨U, V, U_open, V_open, x_in_U, y_in_V, UV_disjoint⟩,
end}
