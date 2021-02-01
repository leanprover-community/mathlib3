import tactic
import group_theory.group_action.basic
import algebra.invertible
import linear_algebra

variables (K : Type*) [field K]
variables (V : Type*) [add_comm_group V] [vector_space K V]
variables {W : Type*} [add_comm_group W] [vector_space K W]

def nonzero := {v : V // v ≠ 0}

variables {K V}

namespace nonzero

instance : has_coe (nonzero V) V := ⟨λ v, v.1⟩

lemma coe_nonzero (v : nonzero V) : (v : V) ≠ 0 := v.2

def map {f : V →ₗ[K] W} (inj : function.injective f) : nonzero V → nonzero W := λ v,
{ val := f v,
  property := begin
    rw ← linear_map.ker_eq_bot at inj,
    intro c,
    apply coe_nonzero v,
    have : ↑v ∈ f.ker := c,
    rw inj at this,
    simpa,
  end }

@[simp] lemma coe_map {f : V →ₗ[K] W} {inj : function.injective f} {v : nonzero V} :
  (nonzero.map inj v : W) = f v := rfl

@[ext] lemma ext {v w : nonzero V} : (v : V) = w → v = w :=
by {cases v, cases w, simp}

@[simps]
instance : has_scalar (units K) (nonzero V) :=
{ smul := λ u v, ⟨(u : K) • v,
  begin
    intro c,
    apply_fun (λ t, (u⁻¹ : K) • t) at c,
    apply v.2,
    simpa using c,
  end⟩ }

instance : mul_action (units K) (nonzero V) :=
{ one_smul := λ x, by tidy,
  mul_smul :=
  begin
    intros x y v,
    ext,
    simp [mul_smul],
  end }

example (a b : Prop) : a = b → b = a :=
begin
  library_search,
end

lemma is_unit_of_smul_eq {v : V} {w : nonzero V} {a : K} : a • v = w → is_unit a :=
begin
  unfold is_unit,
  simp,
  intros he ha,
  cases w with w hw,
  rw ha at he,
  repeat {simp at he},
  replace he := eq.symm he,
  exact hw he,
end

end nonzero

variables (K V)
def proj_space := quotient (mul_action.orbit_rel (units K) (nonzero V))
variables {K V}

namespace proj_space

local attribute [instance] mul_action.orbit_rel

def mk : nonzero V → proj_space K V := quotient.mk

lemma mk_eq_mk {v w : nonzero V} : (mk v : proj_space K V) = mk w ↔
  ∃ (u : units K), u • w = v :=
begin
  change quotient.mk _ = quotient.mk _ ↔ _,
  rw quotient.eq,
  change v ∈ mul_action.orbit _ _ ↔ _,
  simp [mul_action.orbit],
end

lemma mk_eq_mk' {v w : nonzero V} : (mk v : proj_space K V) = mk w ↔
  ∃ (u : K), u • (w : V) = v :=
begin
  rw mk_eq_mk,
  split,
  { rintro ⟨u,rfl⟩,
    exact ⟨u,rfl⟩ },
  { rintro ⟨u,hu⟩,
    refine ⟨is_unit.unit (nonzero.is_unit_of_smul_eq hu), nonzero.ext _⟩,
    simp [← hu, is_unit.unit_spec] }
end

def map {f : V →ₗ[K] W} (inj : function.injective f) : proj_space K V → proj_space K W :=
quotient.lift (λ v, quotient.mk $ nonzero.map inj v)
begin
  rintros v w ⟨a,rfl⟩,
  dsimp,
  apply quotient.sound,
  refine ⟨a,_⟩,
  ext,
  simp,
end

end proj_space
