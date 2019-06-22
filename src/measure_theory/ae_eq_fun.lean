/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou

We define almost everywhere equal functions, and show that
  • they form a vector space if the codomain is a vector space
  • they form an emetric space under L¹ metric if the codomain is a metric space
-/
import measure_theory.integration

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

namespace measure_theory
open set lattice filter topological_space

universes u v
variables {α : Type u} {β : Type v} [measure_space α]

section measurable_space
variables [measurable_space β]

variables (α β)

instance ae_eq_fun.setoid : setoid { f : α → β // measurable f } :=
⟨ λf g, ∀ₘ a, f.1 a = g.1 a,
  assume ⟨f, hf⟩, by filter_upwards [] assume a, rfl,
  assume ⟨f, hf⟩ ⟨g, hg⟩ hfg, by filter_upwards [hfg] assume a, eq.symm,
  assume ⟨f, hf⟩ ⟨g, hg⟩ ⟨h, hh⟩ hfg hgh, by filter_upwards [hfg, hgh] assume a, eq.trans ⟩

def ae_eq_fun : Type (max u v) := quotient (ae_eq_fun.setoid α β)

variables {α β}

infixr ` →ₘ `:25 := ae_eq_fun

end measurable_space

namespace ae_eq_fun
variables [measurable_space β]
-- helper functions and lemmas dealing with quotient
def mk (f : α → β) (hf : measurable f) : α →ₘ β := quotient.mk ⟨f, hf⟩

@[simp] lemma quot_mk_eq_mk (f : {f : α → β // measurable f}) : quot.mk setoid.r f = mk f.1 f.2 :=
by cases f; refl

@[simp] lemma mk_eq_mk (f g : α → β) (hf hg) :
  mk f hf = mk g hg ↔ (∀ₘ a, f a = g a) :=
⟨quotient.exact, assume h, quotient.sound h⟩

def comp {γ : Type*} [measurable_space γ] (g : β → γ) (hg : measurable g) (f : α →ₘ β) : α →ₘ γ :=
quotient.lift_on f (λf, mk (g ∘ f.1)  (measurable.comp hg f.2)) $ assume f₁ f₂ eq,
  by refine quotient.sound _; filter_upwards [eq] assume a, congr_arg g

def comp₂ {γ δ : Type*} [measurable_space γ] [measurable_space δ]
  (g : β → γ → δ) (hg : measurable (λp:β×γ, g p.1 p.2)) (f₁ : α →ₘ β) (f₂ : α →ₘ γ) : α →ₘ δ :=
begin
  refine quotient.lift_on₂ f₁ f₂ (λf₁ f₂, mk (λa, g (f₁.1 a) (f₂.1 a)) $ _) _,
  { exact measurable.comp hg (measurable_prod_mk f₁.2 f₂.2) },
  { rintros ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩ h₁ h₂,
    refine quotient.sound _,
    filter_upwards [h₁, h₂],
    simp {contextual := tt} }
end

@[simp] lemma comp₂_mk_mk {γ δ : Type*} [measurable_space γ] [measurable_space δ]
  (g : β → γ → δ) (hg : measurable (λp:β×γ, g p.1 p.2)) (f₁ : α → β) (f₂ : α → γ) (hf₁ hf₂) :
  comp₂ g hg (mk f₁ hf₁) (mk f₂ hf₂) =
    mk (λa, g (f₁ a) (f₂ a)) (measurable.comp hg (measurable_prod_mk hf₁ hf₂)) :=
rfl

def lift_rel {γ : Type*} [measurable_space γ] (r : β → γ → Prop) (f : α →ₘ β) (g : α →ₘ γ) : Prop :=
quotient.lift_on₂ f g (λf g, ∀ₘ a, r (f.1 a) (g.1 a))
begin
  assume f₁ f₂ g₁ g₂ h₁ h₂, dsimp, refine propext (all_ae_congr _),
  filter_upwards [h₁, h₂], simp {contextual := tt}
end

def lift_rel_mk_mk {γ : Type*} [measurable_space γ] (r : β → γ → Prop)
  (f : α → β) (g : α → γ) (hf hg) : lift_rel r (mk f hf) (mk g hg) ↔ ∀ₘ a, r (f a) (g a) :=
iff.rfl

-- end of helper definitions and functions

section order
variables [measurable_space β]

instance [preorder β] : preorder (α →ₘ β) :=
{ le          := lift_rel (≤),
  le_refl     := by rintros ⟨⟨f, hf⟩⟩; exact univ_mem_sets' (assume a, le_refl _),
  le_trans    :=
  begin
    rintros ⟨⟨f, hf⟩⟩ ⟨⟨g, hg⟩⟩ ⟨⟨h, hh⟩⟩ hfg hgh,
    filter_upwards [hfg, hgh] assume a, le_trans
  end }

lemma mk_le_mk [preorder β] {f g : α → β} (hf hg) : mk f hf ≤ mk g hg ↔ ∀ₘ a, f a ≤ g a :=
iff.rfl

instance [partial_order β] : partial_order (α →ₘ β) :=
{ le_antisymm :=
  begin
    rintros ⟨⟨f, hf⟩⟩ ⟨⟨g, hg⟩⟩ hfg hgf,
    refine quotient.sound _,
    filter_upwards [hfg, hgf] assume a, le_antisymm
  end,
  .. measure_theory.ae_eq_fun.preorder }

end order -- section

variable (α)
def const (b : β) : α →ₘ β := mk (λa:α, b) measurable_const
variable {α}

instance [has_zero β] : has_zero (α →ₘ β) := ⟨const α 0⟩
lemma zero_def [has_zero β] : (0 : α →ₘ β) = mk (λa:α, 0) measurable_const := rfl

instance [has_one β] : has_one (α →ₘ β) := ⟨const α 1⟩
lemma one_def [has_one β] : (1 : α →ₘ β) = mk (λa:α, 1) measurable_const := rfl

section add_monoid
variables {γ : Type*}
  [topological_space γ] [second_countable_topology γ] [add_monoid γ] [topological_add_monoid γ]

protected def add : (α →ₘ γ) → (α →ₘ γ) → (α →ₘ γ) :=
comp₂ (+) (measurable_add (measurable_fst measurable_id) (measurable_snd  measurable_id))

instance : has_add (α →ₘ γ) := ⟨ae_eq_fun.add⟩

@[simp] lemma mk_add_mk (f g : α → γ) (hf hg) : (mk f hf) + (mk g hg) =
    mk (λa, (f a) + (g a)) (measurable_add hf hg) := rfl

protected lemma add_zero : ∀ (a : α →ₘ γ), a + 0 = a :=
by rintros ⟨a⟩; exact quotient.sound (univ_mem_sets' $ assume a, add_zero _)

protected lemma zero_add : ∀ (a : α →ₘ γ), 0 + a = a :=
by rintros ⟨a⟩; exact quotient.sound (univ_mem_sets' $ assume a, zero_add _)

protected lemma add_assoc : ∀ (a b c : α →ₘ γ), a + b + c = a + (b + c) :=
by rintros ⟨a⟩ ⟨b⟩ ⟨c⟩; exact quotient.sound (univ_mem_sets' $ assume a, add_assoc _ _ _)

instance : add_monoid (α →ₘ γ) :=
{ zero      := 0,
  add       := ae_eq_fun.add,
  add_zero  := ae_eq_fun.add_zero,
  zero_add  := ae_eq_fun.zero_add,
  add_assoc := ae_eq_fun.add_assoc }

end add_monoid

section add_comm_monoid
variables {γ : Type*}
  [topological_space γ] [second_countable_topology γ] [add_comm_monoid γ] [topological_add_monoid γ]

protected lemma add_comm : ∀ (a b : α →ₘ γ), a + b = b + a :=
by rintros ⟨a⟩ ⟨b⟩; exact quotient.sound (univ_mem_sets' $ assume a, add_comm _ _)

instance : add_comm_monoid (α →ₘ γ) :=
{ add_comm := ae_eq_fun.add_comm,
  .. ae_eq_fun.add_monoid }

end add_comm_monoid

section add_group

variables {γ : Type*}
  [topological_space γ] [second_countable_topology γ] [add_group γ] [topological_add_group γ]

protected def neg : (α →ₘ γ) → (α →ₘ γ) := comp has_neg.neg (measurable_neg measurable_id)

instance : has_neg (α →ₘ γ) := ⟨ae_eq_fun.neg⟩

@[simp] lemma neg_mk (f : α → γ) (hf) : -(mk f hf) = mk (-f) (measurable_neg hf) := rfl

protected lemma add_left_neg : ∀ (a : α →ₘ γ), -a + a = 0 :=
by rintros ⟨a⟩; exact quotient.sound (univ_mem_sets' $ assume a, add_left_neg _)

instance : add_group (α →ₘ γ) :=
{ neg          := ae_eq_fun.neg,
  add_left_neg := ae_eq_fun.add_left_neg,
  .. ae_eq_fun.add_monoid
 }

end add_group -- section

section add_comm_group

variables {γ : Type*}
  [topological_space γ] [second_countable_topology γ] [add_comm_group γ] [topological_add_group γ]

instance : add_comm_group (α →ₘ γ) :=
{ add_comm := ae_eq_fun.add_comm
  .. ae_eq_fun.add_group
}

end add_comm_group -- section

section semimodule

variables {K : Type*} [semiring K] [topological_space K] [second_countable_topology K]
variables {γ : Type*} [topological_space γ] [second_countable_topology γ]
          [add_comm_monoid γ] [semimodule K γ] [topological_semimodule K γ]

protected def smul : K → (α →ₘ γ) → (α →ₘ γ) :=
λ c f, comp (has_scalar.smul c) (measurable_smul measurable_id) f

instance : has_scalar K (α →ₘ γ) := ⟨ae_eq_fun.smul⟩

@[simp] lemma smul_mk (c : K) (f : α → γ) (hf) : c • (mk f hf) = mk (c • f) (measurable_smul hf) :=
rfl

protected lemma one_smul : ∀ (f : α →ₘ γ), (1 : K) • f = f :=
by { rintros ⟨f, hf⟩, simp only [quot_mk_eq_mk, smul_mk, one_smul] }

protected lemma mul_smul : ∀ (x y : K) (f : α →ₘ γ), (x * y) • f = x • y • f :=
by { rintros x y ⟨f, hf⟩, simp only [quot_mk_eq_mk, smul_mk, mul_action.mul_smul x y f], refl }

variables [topological_add_monoid γ]

protected lemma smul_add : ∀ (x : K) (f g : α →ₘ γ), x • (f + g) = x • f + x • g :=
begin
  rintros x ⟨f, hf⟩ ⟨g, hg⟩, simp only [quot_mk_eq_mk, smul_mk, mk_add_mk],
  congr, exact smul_add x f g
end

protected lemma smul_zero : ∀ (x : K), x • (0 : α →ₘ γ) = 0 :=
by { intro x, simp only [zero_def, smul_mk], congr, exact smul_zero x }

protected lemma add_smul : ∀ (x y : K) (f : α →ₘ γ), (x + y) • f = x • f + y • f :=
begin
  intros x y, rintro ⟨f, hf⟩, simp only [quot_mk_eq_mk, smul_mk, mk_add_mk], congr,
  exact add_smul x y f
end

protected lemma zero_smul : ∀ f : α →ₘ γ, (0 : K) • f = 0 :=
by { rintro ⟨f, hf⟩, simp only [quot_mk_eq_mk, smul_mk, zero_def], congr, exact zero_smul K f }

instance : semimodule K (α →ₘ γ) :=
{ one_smul  := ae_eq_fun.one_smul,
  mul_smul  := ae_eq_fun.mul_smul,
  smul_add  := ae_eq_fun.smul_add,
  smul_zero := ae_eq_fun.smul_zero,
  add_smul  := ae_eq_fun.add_smul,
  zero_smul := ae_eq_fun.zero_smul }

end semimodule -- section

section vector_space

variables {K : Type*} [discrete_field K] [topological_space K] [second_countable_topology K]
variables {γ : Type*} [topological_space γ] [second_countable_topology γ] [add_comm_group γ]
          [topological_add_group γ] [vector_space K γ] [topological_semimodule K γ]

instance : vector_space K (α →ₘ γ) := { .. ae_eq_fun.semimodule }

end vector_space -- section

open ennreal
-- integral on ae_eq_fun
def integral (f : α →ₘ nnreal) : ennreal :=
quotient.lift_on f (λf, ∫⁻ a, f.1 a)
  (assume ⟨f, hf⟩ ⟨g, hg⟩ eq, lintegral_congr_ae $ by simpa [coe_eq_coe])

@[simp] lemma integral_mk (f : α → nnreal) (hf) : integral (mk f hf) = ∫⁻ a, f a :=
rfl

@[simp] lemma integral_zero : integral (0 : α →ₘ nnreal) = 0 :=
lintegral_zero

@[simp] lemma integral_eq_zero_iff (f : α →ₘ nnreal) : integral f = 0 ↔ f = 0 :=
begin
  rcases f with ⟨f, hf⟩,
  refine iff.trans (lintegral_eq_zero_iff _) ⟨_, _⟩,
  { exact measurable_coe.comp hf },
  { assume h, simp only [coe_eq_zero] at h, exact quotient.sound h },
  { assume h, simp only [coe_eq_zero], exact quotient.exact h }
end

lemma integral_add : ∀(f g : α →ₘ nnreal), integral (f + g) = integral f + integral g :=
by rintros ⟨f⟩ ⟨g⟩; simp only [quot_mk_eq_mk, mk_add_mk, integral_mk, coe_add,
   lintegral_add (measurable_coe.comp f.2) (measurable_coe.comp g.2)]

lemma integral_le_integral {f g : α →ₘ nnreal} (h : f ≤ g) : integral f ≤ integral g :=
begin
  rcases f with ⟨f, hf⟩, rcases g with ⟨g, hg⟩,
  simp only [quot_mk_eq_mk, integral_mk, mk_le_mk] at *,
  refine lintegral_le_lintegral_ae _,
  filter_upwards [h], simp
end

section metric -- ae_eq_fun forms an emetric space if the codomain is a metric space

variables {γ : Type*} [metric_space γ] [second_countable_topology γ]

def comp_nndist (f g : α →ₘ γ) : α →ₘ nnreal := comp₂ nndist measurable_nndist' f g

lemma comp_nndist_self : ∀ (f : α →ₘ γ), comp_nndist f f = 0 :=
by rintro ⟨f⟩; refine quotient.sound _; simp only [nndist_self]

protected def edist (f g : α →ₘ γ) : ennreal := integral (comp_nndist f g)

instance : has_edist (α →ₘ γ) := ⟨ae_eq_fun.edist⟩

@[simp] lemma edist_mk_mk {f g : α → γ} (hf hg) :
  edist (mk f hf) (mk g hg) = integral (comp_nndist (mk f hf) (mk g hg)) := rfl

protected lemma edist_self : ∀ (f : α →ₘ γ), edist f f = 0 :=
assume f, (integral_eq_zero_iff _).2 (comp_nndist_self _)

protected lemma edist_comm : ∀ (f g : α →ₘ γ), edist f g = edist g f :=
by { rintros ⟨f⟩ ⟨g⟩, simp [comp_nndist, nndist_comm] }

protected lemma edist_triangle : ∀ (f g h : α →ₘ γ), edist f h ≤ edist f g + edist g h :=
begin
  rintros ⟨f, hf⟩ ⟨g, hg⟩ ⟨h, hh⟩,
  simp only [comp_nndist, edist, ae_eq_fun.edist, quot_mk_eq_mk,
             comp₂_mk_mk, (integral_add _ _).symm, mk_add_mk],
  refine integral_le_integral _, simp only [mk_le_mk],
  filter_upwards [], simp [nndist_triangle]
end

protected lemma eq_of_edist_eq_zero : ∀ (f g : α →ₘ γ), edist f g = 0 → f = g :=
by { rintros ⟨f⟩ ⟨g⟩, simp [comp_nndist, zero_def, -integral_mk] }

instance : emetric_space (α →ₘ γ) :=
{ edist_self          := ae_eq_fun.edist_self,
  edist_comm          := ae_eq_fun.edist_comm,
  edist_triangle      := ae_eq_fun.edist_triangle,
  eq_of_edist_eq_zero := ae_eq_fun.eq_of_edist_eq_zero }

end metric -- section

section normed_group

variables {γ : Type*} [normed_group γ] [second_countable_topology γ] [topological_add_group γ]

-- edist is translation invariant
lemma edist_eq_add_add : ∀ {f g h : α →ₘ γ}, edist f g = edist (f + h) (g + h) :=
by { rintros ⟨f⟩ ⟨g⟩ ⟨h⟩, apply lintegral_congr_ae, filter_upwards [], simp [nndist_eq_nnnorm] }

end normed_group -- section

section normed_space

set_option class.instance_max_depth 100

variables {K : Type*} [normed_field K] [second_countable_topology K]
variables {γ : Type*} [normed_group γ] [second_countable_topology γ] [normed_space K γ]

lemma edist_smul (x : K) : ∀ f : α →ₘ γ, edist (x • f) 0 = (ennreal.of_real ∥x∥) * edist f 0 :=
begin
  rintros ⟨f, hf⟩, show
  (∫⁻ (a : α), nndist (x • f a) 0) = (ennreal.of_real ∥x∥) * (∫⁻ (a : α), nndist (f a) 0),
  calc
    (∫⁻ (a : α), nndist (x • f a) 0) = (∫⁻ (a : α), (nnnorm x) * nnnorm (f a)) :
      lintegral_congr_ae $ by { filter_upwards [], assume a, simp [nndist_eq_nnnorm, nnnorm_smul] }
    ... = _ : lintegral_const_mul _ (measurable_coe_nnnorm hf)
    ... = _ :
    begin
      convert rfl,
      { rw ← coe_nnnorm, rw [ennreal.of_real], congr, exact nnreal.of_real_coe },
      { funext, simp [nndist_eq_nnnorm] }
    end
end

end normed_space -- section

end ae_eq_fun

end measure_theory
