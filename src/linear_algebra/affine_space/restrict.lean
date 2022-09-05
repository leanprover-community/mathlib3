import linear_algebra.affine_space.affine_subspace

variables {k V₁ P₁ V₂ P₂ : Type} [ring k]
  [add_comm_group V₁] [add_comm_group V₂]
  [module k V₁] [module k V₂]
  [add_torsor V₁ P₁] [add_torsor V₂ P₂]

include V₁ V₂

/- not an instance because it loops with `nonempty` -/
lemma affine_subspace.nonempty_map {E : affine_subspace k P₁} [Ene : nonempty E]
  {φ : P₁ →ᵃ[k] P₂} : nonempty (E.map φ) :=
begin
  obtain ⟨x, hx⟩ := id Ene,
  refine ⟨⟨φ x, affine_subspace.mem_map.mpr ⟨x, hx, rfl⟩⟩⟩,
end

local attribute [instance, nolint fails_quickly] affine_subspace.nonempty_map

/-- Restrict domain and codomain of an affine map to the given submodules. -/
def affine_map.restrict
  (φ : P₁ →ᵃ[k] P₂) {E : affine_subspace k P₁} {F : affine_subspace k P₂}
  [nonempty E] [nonempty F]
  (hEF : E.map φ ≤ F) : E →ᵃ[k] F :=
begin
  refine ⟨_, _, _⟩,
  { exact λ x, ⟨φ x, hEF $ affine_subspace.mem_map.mpr ⟨x, x.property, rfl⟩⟩ },
  { refine φ.linear.restrict' _,
    rw [←affine_subspace.map_direction],
    exact affine_subspace.direction_le hEF },
  { intros p v,
    simp only [subtype.ext_iff, subtype.coe_mk, affine_subspace.coe_vadd],
    apply affine_map.map_vadd },
end

lemma affine_map.restrict.coe_apply
  (φ : P₁ →ᵃ[k] P₂) {E : affine_subspace k P₁} {F : affine_subspace k P₂}
  [nonempty E] [nonempty F]
  (hEF : E.map φ ≤ F) (x : E) :
↑(φ.restrict hEF x) = φ x := rfl

lemma affine_map.restrict.linear
  (φ : P₁ →ᵃ[k] P₂) {E : affine_subspace k P₁} {F : affine_subspace k P₂}
  [nonempty E] [nonempty F]
  (hEF : E.map φ ≤ F) :
(φ.restrict hEF).linear = φ.linear.restrict'
  (by { rw [←affine_subspace.map_direction], exact affine_subspace.direction_le hEF }) := rfl

lemma affine_map.restrict.injective
  {φ : P₁ →ᵃ[k] P₂}
  (hφ : function.injective φ) {E : affine_subspace k P₁} {F : affine_subspace k P₂}
  [nonempty E] [nonempty F]
  (hEF : E.map φ ≤ F) :
function.injective (affine_map.restrict φ hEF) :=
begin
  intros x y h,
  simp only [subtype.ext_iff, subtype.coe_mk, affine_map.restrict.coe_apply] at h ⊢,
  exact hφ h,
end

lemma affine_map.restrict.surjective
  (φ : P₁ →ᵃ[k] P₂) {E : affine_subspace k P₁} [nonempty E] :
function.surjective (affine_map.restrict φ (le_refl (E.map φ))) :=
begin
  rintro ⟨x, hx : x ∈ E.map φ⟩,
  rw [affine_subspace.mem_map] at hx,
  obtain ⟨y, hy, rfl⟩ := hx,
  exact ⟨⟨y, hy⟩, rfl⟩,
end

lemma affine_map.bijective_iff_linear_bijective
  (φ : P₁ →ᵃ[k] P₂) :
function.bijective φ ↔ function.bijective φ.linear :=
begin
  simp only [function.bijective,
    φ.injective_iff_linear_injective, φ.surjective_iff_linear_surjective],
end
