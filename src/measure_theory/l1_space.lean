/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou

Integrable functions and L¹ space
-/

import measure_theory.ae_eq_fun

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

set_option class.instance_max_depth 100

namespace measure_theory
open set lattice filter topological_space ennreal emetric

universes u v
variables {α : Type u} {β : Type v} [measure_space α]
variables {γ : Type*} [normed_group γ] [second_countable_topology γ]

infixr ` →ₘ `:25 := ae_eq_fun

def integrable (f : α → γ) : Prop := (∫⁻ a, nnnorm (f a)) < ⊤

@[simp] lemma lintegral_nnnorm_zero : (∫⁻ a : α, nnnorm (0 : γ)) = 0 := by simp

lemma integrable_zero : integrable (0 : α → γ) :=
by { have := coe_lt_top, simpa [integrable] }

lemma lintegral_nnnorm_add {f g : α → γ} (hf : measurable f) (hg : measurable g) :
  (∫⁻ a, nnnorm (f a) + nnnorm (g a)) = (∫⁻ a, nnnorm (f a)) + ∫⁻ a, nnnorm (g a) :=
lintegral_add (measurable_coe_nnnorm hf) (measurable_coe_nnnorm hg)

--cannot be proved in `metric_space` + `add_comm_group`?
lemma integrable_add {f g : α → γ} (hfm : measurable f) (hgm : measurable g) :
  integrable f → integrable g → integrable (f + g) :=
assume hfi hgi,
  calc
    (∫⁻ (a : α), ↑(nnnorm ((f + g) a))) ≤ ∫⁻ (a : α), ↑(nnnorm (f a)) + ↑(nnnorm (g a)) :
      lintegral_le_lintegral _ _
        (assume a, by { simp only [coe_add.symm, coe_le_coe], exact nnnorm_triangle _ _ })
    ... = _ :
      lintegral_nnnorm_add hfm hgm
    ... < ⊤ : add_lt_top.2 ⟨hfi, hgi⟩

lemma lintegral_nnnorm_neg {f : α → γ} (hf : measurable f) :
  (∫⁻ (a : α), ↑(nnnorm ((-f) a))) = ∫⁻ (a : α), ↑(nnnorm ((f) a)) :=
lintegral_congr_ae $ by { filter_upwards [], simp }

lemma integrable_neg {f : α → γ} (hfm : measurable f) : integrable f → integrable (-f) :=
assume hfi, calc _ = _ : lintegral_nnnorm_neg hfm
                 ... < ⊤ : hfi

section normed_space
variables {K : Type*} [normed_field K] [normed_space K γ]

lemma integrable_smul {c : K} {f : α → γ} (hfm : measurable f) : integrable f → integrable (c • f) :=
begin
  simp only [integrable], assume hfi,
  calc
    (∫⁻ (a : α), nnnorm ((c • f) a)) = (∫⁻ (a : α), (nnnorm c) * nnnorm (f a)) : by
    { apply lintegral_congr_ae, filter_upwards [], assume a, simp [nnnorm_smul] }
    ... < ⊤ :
    begin
      rw lintegral_const_mul, apply mul_lt_top,
      { simp }, { exact hfi }, { exact measurable_coe_nnnorm hfm }
    end
end

end normed_space -- section

namespace ae_eq_fun

def integrable (f : α →ₘ γ) : Prop := f ∈ ball (0 : α →ₘ γ) ⊤

@[simp] lemma integrable_mk (f : α → γ) (hf : measurable f) :
  (integrable (mk f hf)) ↔ measure_theory.integrable f :=
by simp [integrable, zero_def, comp_nndist, measure_theory.integrable, nndist_eq_nnnorm]

lemma integrable_zero : integrable (0 : α →ₘ γ) := mem_ball_self coe_lt_top

lemma integrable_add : ∀ {f g : α →ₘ γ}, integrable f → integrable g → integrable (f + g) :=
begin
  rintros ⟨f, hf⟩ ⟨g, hg⟩,
  have := measure_theory.integrable_add hf hg,
  simpa [mem_ball, zero_def]
end

lemma integrable_neg : ∀ {f : α →ₘ γ}, integrable f → integrable (-f) :=
by { rintros ⟨f, hf⟩, have := measure_theory.integrable_neg hf, simpa }

instance : is_add_subgroup (ball (0 : α →ₘ γ) ⊤) :=
{ zero_mem := integrable_zero,
  add_mem := λ _ _, integrable_add,
  neg_mem := λ _, integrable_neg }

section normed_space
variables {K : Type*} [normed_field K] [second_countable_topology K] [normed_space K γ]

lemma integrable_smul : ∀ {c : K} {f : α →ₘ γ}, integrable f → integrable (c • f) :=
by { assume c, rintros ⟨f, hf⟩, have := integrable_smul hf, simpa }

end normed_space -- section

end ae_eq_fun

section
variables (α γ)
def l1 : Type* := subtype (@ae_eq_fun.integrable α _ γ _ _)

local notation `L¹` := l1

infixr ` →₁ `:25 := l1

end

namespace l1
open ae_eq_fun

section normed_group

def mk (f : α → γ) : measurable f → integrable f → (α →₁ γ) :=
assume hfm hfi, ⟨mk f hfm, by { rw integrable_mk, assumption }⟩

@[simp] protected lemma eq {f g : α →₁ γ} : f = g ↔ f.1 = g.1 := ⟨congr rfl , subtype.eq⟩

instance : emetric_space (α →₁ γ) := subtype.emetric_space
instance : metric_space (α →₁ γ) := metric_space_emetric_ball 0 ⊤

@[simp] lemma dist_def (f g : α →₁ γ) : dist f g = ennreal.to_real (edist f.1 g.1) := rfl

instance : add_comm_group (α →₁ γ) := subtype.add_comm_group

@[simp] lemma zero_def : (0 : α →₁ γ) = ⟨(0 : α →ₘ γ), ae_eq_fun.integrable_zero⟩ := rfl

@[simp] lemma add_def (f g : α →₁ γ) : f + g = ⟨f.1 + g.1, ae_eq_fun.integrable_add f.2 g.2⟩ := rfl

instance : has_norm (α →₁ γ) := ⟨λ f, dist f 0⟩

@[simp] lemma norm_def (f : α →₁ γ) : (norm f) = ennreal.to_real (edist f.1 0) := rfl

instance : normed_group (α →₁ γ) := normed_group.of_add_dist (λ x, rfl) $ by
{ rintros ⟨f, _⟩ ⟨g, _⟩ ⟨h, _⟩, simp only [dist_def, add_def], rw [edist_eq_add_add] }

end normed_group -- section

section normed_space

variables {K : Type*} [normed_field K] [second_countable_topology K] [normed_space K γ]

protected def smul : K → (α →₁ γ) → (α →₁ γ) := λ x f, ⟨x • f.1, ae_eq_fun.integrable_smul f.2⟩

instance : has_scalar K (α →₁ γ) := ⟨l1.smul⟩

@[simp] lemma smul_def {x : K} {f : α →₁ γ} : x • f = ⟨x • f.1, ae_eq_fun.integrable_smul f.2⟩ := rfl

protected lemma one_smul : ∀ f : α →₁ γ, (1 : K) • f = f :=
by { rintros ⟨f, hf⟩, simp [ae_eq_fun.one_smul f] }

protected lemma mul_smul : ∀ (x y : K) (f : α →₁ γ), (x * y) • f = x • y • f :=
by { rintros x y ⟨f, hf⟩, simp [ae_eq_fun.mul_smul x y f] }

protected lemma smul_add : ∀ (x : K) (f g : α →₁ γ), x • (f + g) = x • f + x • g :=
by { rintros x ⟨f, hf⟩ ⟨g, hg⟩, simp [smul_add x f g] }

protected lemma smul_zero : ∀ (x : K), x • (0 : α →₁ γ) = 0 :=
by { assume x, simp [smul_zero x] }

protected lemma add_smul : ∀ (x y : K) (f : α →₁ γ), (x + y) • f = x • f + y • f :=
by { rintros x y ⟨f, hf⟩, simp [add_smul x y f] }

protected lemma zero_smul : ∀ f : α →₁ γ, (0 : K) • f = 0 :=
by { rintro ⟨f, hf⟩, simp [zero_smul K f] }

protected lemma norm_smul : ∀ (x : K) (f : α →₁ γ), norm (x • f) = norm x * norm f :=
begin
  rintros x ⟨f, hf⟩,
  show ennreal.to_real (edist (x • f) 0) = ∥x∥ * ennreal.to_real (edist f 0),
  rw [edist_smul, to_real_of_real_mul], exact norm_nonneg _
end

instance : semimodule K (α →₁ γ) :=
{ one_smul  := l1.one_smul,
  mul_smul  := l1.mul_smul,
  smul_add  := l1.smul_add,
  smul_zero := l1.smul_zero,
  add_smul  := l1.add_smul,
  zero_smul := l1.zero_smul }

instance : vector_space K (α →₁ γ) := { .. l1.semimodule }

instance : normed_space K (α →₁ γ) := ⟨l1.norm_smul⟩

end normed_space -- section

end l1

end measure_theory
