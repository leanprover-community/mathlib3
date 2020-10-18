import linear_algebra.affine_space.basic


structure affine_equiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [ring k]
  [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁]
  [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] extends P₁ ≃ P₂ :=
(linear : V₁ ≃ₗ[k] V₂)
(map_vadd' : ∀ (p : P₁) (v : V₁), to_equiv (v +ᵥ p) = linear v +ᵥ to_equiv p)

notation P₁ ` ≃ₐ[`:25 k:25 `] `:0 P₂:0 := affine_equiv k P₁ P₂

variables {k V₁ V₂ V₃ P₁ P₂ P₃ : Type*} [ring k]
  [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁]
  [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂]
  [add_comm_group V₃] [semimodule k V₃] [add_torsor V₃ P₃]

instance (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
    [ring k]
    [add_comm_group V1] [module k V1] [affine_space V1 P1]
    [add_comm_group V2] [module k V2] [affine_space V2 P2]:
    has_coe_to_fun (P1 ≃ₐ[k] P2) := ⟨_, λ e, e.to_fun⟩

namespace linear_equiv

/-- Interpret a linear equivalence between modules as an affine equivalence. -/
def to_affine_equiv (e : V₁ ≃ₗ[k] V₂) : V₁ ≃ₐ[k] V₂ :=
{ to_equiv := e.to_equiv,
  linear := e,
  map_vadd' := λ p v, e.map_add v p }

@[simp] lemma coe_to_affine_equiv (e : V₁ ≃ₗ[k] V₂) : ⇑e.to_affine_equiv = e := rfl

end linear_equiv

namespace affine_equiv

variables (k P₁)

include V₁

def refl : P₁ ≃ₐ[k] P₁ :=
{ to_equiv := equiv.refl P₁,
  linear := linear_equiv.refl k V₁,
  map_vadd' := λ _ _, rfl }

include V₂

lemma map_vadd (e : P₁ ≃ₐ[k] P₂) (p : P₁) (v : V₁) : e (v +ᵥ p) = 

end affine_equiv
