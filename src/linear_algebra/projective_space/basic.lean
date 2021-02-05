/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colter MacDonald, Adam Topaz
-/
import tactic
import group_theory.group_action.basic
import algebra.invertible
import linear_algebra

/-!
# Projective spaces

TODO : Add docs

-/

variables (K : Type*) [field K]
variables (V : Type*) [add_comm_group V] [vector_space K V]
variables {W : Type*} [add_comm_group W] [vector_space K W]

/-- The nonzero elements of a vector space. -/
def nonzero := {v : V // v ≠ 0}

variables {K V}

namespace nonzero

instance : has_coe (nonzero V) V := ⟨λ v, v.1⟩

noncomputable instance [nontrivial V] : inhabited (nonzero V) := inhabited.mk $
⟨classical.some $ exists_ne 0, classical.some_spec $ exists_ne 0⟩

lemma coe_nonzero (v : nonzero V) : (v : V) ≠ 0 := v.2

/-- Map a nonzero vector with respect to an injective map. -/
def map {f : V →ₗ[K] W} (inj : function.injective f) : nonzero V → nonzero W := λ v,
{ val := f v,
  property := by { rw ← f.map_zero, exact λ c, coe_nonzero v (inj c) } }

@[simp] lemma coe_map {f : V →ₗ[K] W} {inj : function.injective f} {v : nonzero V} :
  (nonzero.map inj v : W) = f v := rfl

@[ext] lemma ext {v w : nonzero V} : (v : V) = w → v = w :=
by {cases v, cases w, simp}

@[simps]
instance : has_scalar (units K) (nonzero V) :=
{ smul := λ u v, ⟨(u : K) • v, λ c, coe_nonzero v $ by simpa using c⟩ }

instance : mul_action (units K) (nonzero V) :=
{ one_smul := λ x, by tidy,
  mul_smul := λ x y v, nonzero.ext $ by simp [mul_smul] }

lemma ne_zero_of_smul_eq {v : V} {w : nonzero V} {a : K} : a • v = w → a ≠ 0 :=
λ h c, coe_nonzero w $ by simp [← h, c]

lemma eq_smul_inv_of_smul_eq {v : V} {w : nonzero V} { a : K } : a • v = w → v = a⁻¹ • w :=
λ h, by simp [← h, ← mul_smul, inv_mul_cancel (ne_zero_of_smul_eq h)]

lemma is_unit_of_smul_eq {v : V} {w : nonzero V} {a : K} : a • v = w → is_unit a :=
λ h, is_unit_iff_ne_zero.mpr $ ne_zero_of_smul_eq h

end nonzero

variables (K V)
/-- The Projectivization of `V` as a `K` vector space. -/
def proj_space := quotient (mul_action.orbit_rel (units K) (nonzero V))
variables {K V}

namespace proj_space

local attribute [instance] mul_action.orbit_rel

/-- Given a nonzero vector, construct an element in the projectivization of `V`. -/
def mk : nonzero V → proj_space K V := quotient.mk

noncomputable instance [nontrivial V] : inhabited (proj_space K V) := ⟨mk $ default _⟩

lemma exists_rep (v : proj_space K V) : ∃ (u : nonzero V), mk u = v := quotient.exists_rep _

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

/--
Map an element in the projecivization of a vector space with respect to an injective linear map.
-/
def map {f : V →ₗ[K] W} (inj : function.injective f) : proj_space K V → proj_space K W :=
quotient.lift (λ v, quotient.mk $ nonzero.map inj v) $
by {rintros v w ⟨a,rfl⟩, refine quotient.sound ⟨a,nonzero.ext $ by simp⟩}

instance : has_mem V (proj_space K V) := has_mem.mk $
λ v w, ∃ (u : nonzero V) (a : K), a • v = u ∧ w = mk u

lemma mem_def {v : V} {w : proj_space K V} : v ∈ w ↔ ∃ (u : nonzero V) (a : K), a • v = u ∧ w = mk u := iff.rfl

lemma ne_zero_of_mem {v : V} {w : proj_space K V} : v ∈ w → v ≠ 0 :=
begin
  intros h c,
  obtain ⟨u,a,h⟩ := mem_def.mp h,
  simp only [c, smul_zero] at h,
  exact u.coe_nonzero h.1.symm,
end

lemma smul_mem {v : V} {w : proj_space K V} {a : K} : a ≠ 0 → v ∈ w → a • v ∈ w :=
begin
  intros ha hv,
  rw mem_def at *,
  rcases hv with ⟨u, b, h1, rfl⟩,
  refine ⟨u, b * a⁻¹, _, rfl⟩,
  simpa [mul_smul b, ← mul_smul a⁻¹, inv_mul_cancel ha],
end

lemma mem_mk_iff {v : V} {w : nonzero V} : v ∈ (mk w : proj_space K V) ↔ ∃ a : K, a • v = w :=
begin
  rw mem_def,
  split,
  { rintro ⟨u,a,h1,h2⟩,
    rw mk_eq_mk' at h2,
    rcases h2 with ⟨b,h2⟩,
    rw [← h2, ← h1],
    refine ⟨b * a, _⟩,
    simp [mul_smul] },
  { rintro ⟨a,h⟩,
    exact ⟨w, a, h, rfl⟩ },
end

def to_subspace : proj_space K V → subspace K V := λ x,
{ carrier := {v | v = 0 ∨ v ∈ x},
  zero_mem' := or.inl rfl,
  add_mem' := begin
    rintros u v (h1|h1) (h2|h2),
    { left, simp [h1, h2] },
    { right, simpa [h1] },
    { right, simpa [h2] },
    rw mem_def at *,
    rcases h1 with ⟨v1,a1,ha1,rfl⟩,
    rcases h2 with ⟨v2,a2,ha2,ha3⟩,
    have : v ∈ (mk v2 : proj_space K V), by {rw mem_mk_iff, refine ⟨a2,ha2⟩},
    rw [← ha3, mem_mk_iff] at this,
    rcases this with ⟨b,hb⟩,
    replace ha1 := nonzero.eq_smul_inv_of_smul_eq ha1,
    replace ha2 := nonzero.eq_smul_inv_of_smul_eq ha2,
    replace hb := nonzero.eq_smul_inv_of_smul_eq hb,
    rw [hb, ha1, ← add_smul],
    by_cases h : a1⁻¹ + b⁻¹ = 0,
    { left,
      simp [h] },
    right,
    rw mem_mk_iff,
    refine ⟨(a1⁻¹ + b⁻¹)⁻¹,_⟩,
    simp [← mul_smul, inv_mul_cancel h],
  end,
  smul_mem' := begin
    rintros c v (h|h),
    { left, simp [h] },
    by_cases hc : c = 0,
    { left, simp [hc] },
    right,
    exact smul_mem hc h,
  end }

variables (K V)
/-- The type of linear subspaces of the projective space `proj_space K V`. -/
structure linear_subspace :=
(carrier : set (proj_space K V))
(add_mem' {u v : V} {a b c : proj_space K V} :
  u ∈ a → v ∈ b → (u + v) ∈ c → a ∈ carrier → b ∈ carrier → c ∈ carrier)
variables {K V}

namespace linear_subspace

instance : has_coe (linear_subspace K V) (set (proj_space K V)) := ⟨linear_subspace.carrier⟩

instance : has_mem (proj_space K V) (linear_subspace K V) := ⟨λ x X, x ∈ (X : set (proj_space K V))⟩

lemma add_mem (X : linear_subspace K V) {u v : V} {a b c : proj_space K V} :
  u ∈ a → v ∈ b → (u + v) ∈ c → a ∈ X → b ∈ X → c ∈ X := linear_subspace.add_mem' _

instance : has_bot (linear_subspace K V) := has_bot.mk $
{ carrier := ⊥,
  add_mem' := by tauto }

def to_subspace : linear_subspace K V → subspace K V :=
λ X, ⨆ (x : X), (x : proj_space K V).to_subspace

lemma to_subspace_mk_eq {v : nonzero V} : (proj_space.mk v : proj_space K V).to_subspace = K ∙ (v : V) :=
begin
  ext,
  split,
  { rintro (h|h),
    { simp [h] },
    rw mem_mk_iff at h,
    rcases h with ⟨a,ha⟩,
    replace ha := nonzero.eq_smul_inv_of_smul_eq ha,
    rw ha,
    exact (K ∙ (v : V)).smul_mem _ (submodule.subset_span rfl) },
  { intro h,
    rw submodule.mem_span_singleton at h,
    rcases h with ⟨a,rfl⟩,
    by_cases hx : a = 0,
    { left, simp [hx] },
    right,
    rw mem_mk_iff,
    refine ⟨a⁻¹, _⟩,
    rw [← mul_smul, inv_mul_cancel hx, one_smul] }
end

lemma to_subspace_mk_le_iff {v : nonzero V} (M : subspace K V) :
  (proj_space.mk v : proj_space K V).to_subspace ≤ M ↔ (v : V) ∈ M :=
by {rw [to_subspace_mk_eq, submodule.span_le], finish}

def of_subspace : subspace K V → linear_subspace K V := λ W,
{ carrier := {x | x.to_subspace ≤ W},
  add_mem' := begin
    intros u v a b c ha hb hc haW hbW,
    rcases a.exists_rep with ⟨a,rfl⟩,
    rcases b.exists_rep with ⟨b,rfl⟩,
    rcases c.exists_rep with ⟨c,rfl⟩,
    rw mem_mk_iff at *,
    rcases ha with ⟨a',ha⟩,
    rcases hb with ⟨b',hb⟩,
    rcases hc with ⟨c',hc⟩,
    change _ ≤ _,
    change _ ≤ _ at haW,
    change _ ≤ _ at hbW,
    rw to_subspace_mk_le_iff at *,
    rw [← hc, smul_add],
    apply W.add_mem,
    { apply W.smul_mem,
      replace ha := nonzero.eq_smul_inv_of_smul_eq ha,
      rw ha,
      exact W.smul_mem _ haW },
    { apply W.smul_mem,
      replace hb := nonzero.eq_smul_inv_of_smul_eq hb,
      rw hb,
      exact W.smul_mem _ hbW }
  end }

def equiv_subspace : linear_subspace K V ≃ subspace K V :=
{ to_fun := to_subspace,
  inv_fun := of_subspace,
  left_inv := sorry,
  right_inv := sorry }

end linear_subspace
end proj_space
