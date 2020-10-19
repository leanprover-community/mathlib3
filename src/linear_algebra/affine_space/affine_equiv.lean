import linear_algebra.affine_space.basic

open function set

/-- An affine equivalence is an equivalence between affine spaces such that both forward
and inverse maps are affine.

We define it using an `equiv` for the map and a `linear_equiv` for the linear part in order
to allow affine equivalences with good definitional equalities. -/
structure affine_equiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [ring k]
  [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁]
  [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂] extends P₁ ≃ P₂ :=
(linear : V₁ ≃ₗ[k] V₂)
(map_vadd' : ∀ (p : P₁) (v : V₁), to_equiv (v +ᵥ p) = linear v +ᵥ to_equiv p)

notation P₁ ` ≃ᵃ[`:25 k:25 `] `:0 P₂:0 := affine_equiv k P₁ P₂

variables {k V₁ V₂ V₃ P₁ P₂ P₃ : Type*} [ring k]
  [add_comm_group V₁] [semimodule k V₁] [add_torsor V₁ P₁]
  [add_comm_group V₂] [semimodule k V₂] [add_torsor V₂ P₂]
  [add_comm_group V₃] [semimodule k V₃] [add_torsor V₃ P₃]

instance (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
    [ring k]
    [add_comm_group V1] [module k V1] [affine_space V1 P1]
    [add_comm_group V2] [module k V2] [affine_space V2 P2]:
    has_coe_to_fun (P1 ≃ᵃ[k] P2) := ⟨_, λ e, e.to_fun⟩

namespace linear_equiv

/-- Interpret a linear equivalence between modules as an affine equivalence. -/
def to_affine_equiv (e : V₁ ≃ₗ[k] V₂) : V₁ ≃ᵃ[k] V₂ :=
{ to_equiv := e.to_equiv,
  linear := e,
  map_vadd' := λ p v, e.map_add v p }

@[simp] lemma coe_to_affine_equiv (e : V₁ ≃ₗ[k] V₂) : ⇑e.to_affine_equiv = e := rfl

end linear_equiv

namespace affine_equiv

variables (k P₁)

include V₁

/-- Identity map as an `affine_equiv`. -/
def refl : P₁ ≃ᵃ[k] P₁ :=
{ to_equiv := equiv.refl P₁,
  linear := linear_equiv.refl k V₁,
  map_vadd' := λ _ _, rfl }

variables {k P₁}

include V₂

@[simp] lemma map_vadd (e : P₁ ≃ᵃ[k] P₂) (p : P₁) (v : V₁) : e (v +ᵥ p) = e.linear v +ᵥ e p :=
e.map_vadd' p v

@[simp] lemma coe_to_equiv (e : P₁ ≃ᵃ[k] P₂) : ⇑e.to_equiv = e := rfl

/-- Reinterpret an `affine_equiv` as an `affine_map`. -/
def to_affine_map (e : P₁ ≃ᵃ[k] P₂) : P₁ →ᵃ[k] P₂ := { to_fun := e, .. e }

@[simp] lemma coe_to_affine_map (e : P₁ ≃ᵃ[k] P₂) :
  (e.to_affine_map : P₁ → P₂) = (e : P₁ → P₂) := 
rfl

@[simp] lemma to_affine_map_mk (f : P₁ ≃ P₂) (f' : V₁ ≃ₗ[k] V₂) (h) :
  to_affine_map (mk f f' h) = ⟨f, f', h⟩ :=
rfl

@[simp] lemma linear_to_affine_map (e : P₁ ≃ᵃ[k] P₂) : e.to_affine_map.linear = e.linear := rfl

lemma injective_to_affine_map : injective (to_affine_map : (P₁ ≃ᵃ[k] P₂) → (P₁ →ᵃ[k] P₂)) :=
begin
  rintros ⟨e₁, l₁, h₁⟩ ⟨e₂, l₂, h₂⟩ H,
  congr,
  {  }
end

/-- Inverse of an affine equivalence as an affine equivalence. -/
def symm (e : P₁ ≃ᵃ[k] P₂) : P₂ ≃ᵃ[k] P₁ :=
{ to_equiv := e.to_equiv.symm,
  linear := e.linear.symm,
  map_vadd' := λ v p, e.to_equiv.symm.apply_eq_iff_eq_symm_apply.2 $
    by simpa using (e.to_equiv.apply_symm_apply v).symm }

@[simp] lemma symm_to_equiv (e : P₁ ≃ᵃ[k] P₂) : e.to_equiv.symm = e.symm.to_equiv := rfl

@[simp] lemma symm_linear (e : P₁ ≃ᵃ[k] P₂) : e.linear.symm = e.symm.linear := rfl

protected lemma bijective (e : P₁ ≃ᵃ[k] P₂) : bijective e := e.to_equiv.bijective
protected lemma surjective (e : P₁ ≃ᵃ[k] P₂) : surjective e := e.to_equiv.surjective
protected lemma injective (e : P₁ ≃ᵃ[k] P₂) : injective e := e.to_equiv.injective

@[simp] lemma range_eq (e : P₁ ≃ᵃ[k] P₂) : range e = univ := e.surjective.range_eq

@[simp] lemma apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₂) : e (e.symm p) = p :=
e.to_equiv.apply_symm_apply p

@[simp] lemma symm_apply_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₁) : e.symm (e p) = p :=
e.to_equiv.symm_apply_apply p

lemma apply_eq_iff_eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.symm p₂ :=
e.to_equiv.apply_eq_iff_eq_symm_apply

@[simp] lemma apply_eq_iff_eq (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂ : P₁} : e p₁ = e p₂ ↔ p₁ = p₂ :=
e.to_equiv.apply_eq_iff_eq



end affine_equiv
