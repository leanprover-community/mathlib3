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

variables {T : Type*} [topological_space T] {G : Type*} [group G] (φ : G →* (homeomorph T T))
--[mul_action G T] [has_continuous_smul G T]

def foo : setoid T := { r := λ x y, ∃ g, φ g x = y,
  iseqv := begin
    split,
    sorry,
    split,
    sorry,
    sorry,
  end}

def properly_discontinuous : Prop := ∀ (K L : set T), is_compact K → is_compact L →
  set.finite {g : G | ((φ g) '' K) ∩ L ≠ ∅ }

lemma is_t2_of_properly_discontinuous_of_t2 [t2_space T] [locally_compact_space T]
(h : properly_discontinuous φ) : t2_space (quotient (foo φ)) :=
{ t2 := begin
  intros x y hxy,
  obtain ⟨x₀, hx₀⟩ := @quotient.exists_rep _ (foo φ) x,
  obtain ⟨y₀, hy₀⟩ := @quotient.exists_rep _ (foo φ) y,
  have hx₀y₀ : x₀ ≠ y₀ := sorry,
  obtain ⟨u₀, v₀, open_u₀, open_v₀, x₀_in_u₀, y₀_in_v₀, hu₀v₀⟩ := t2_separation hx₀y₀,

end}
