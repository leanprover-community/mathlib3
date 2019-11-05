/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou
-/

import measure_theory.integration

/-!

# ALmost everywhere equal functions

Two measurable functions are treated as identical if they are almost everywhere equal. We form the
set of equivalence classes under the relation of being almost everywhere equal, which is sometimes
known as the L0 space.

See `l1_space.lean` for L1 space.


## Notation

* `α →ₘ β` is the type of L0 space. `f : α →ₘ β` is a "function" in L0.
  In comments, `[f]` is also used to denote an L0 function.

  `ₘ` can be typed as `\_m`. Sometimes it is shown as a box if font is missing.


## Main statements

* The linear structure of L0 :
    Addition and scalar multiplication are defined on L0 in the natural way, i.e.,
    `[f] + [g] := [f + g]`, `c • [f] := [c • f]`. So defined, `α →ₘ β` inherits the linear structure
    of `β`. For example, if `β` is a module, then `α →ₘ β` is a module over the same ring.

    See `mk_add_mk`,  `neg_mk`,     `mk_sub_mk`,  `smul_mk`,
        `add_to_fun`, `neg_to_fun`, `sub_to_fun`, `smul_to_fun`

* The order structure of L0 :
    `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
    And `α →ₘ β` inherits the preorder and partial order of `β`.

    TODO: Define `sup` and `inf` on L0 so that it forms a lattice. It seems that `β` must be a
    linear order, since otherwise `f ⊔ g` may not be a measurable function.

* Emetric on L0 :
    If `β` is an `emetric_space`, then L0 can be made into an `emetric_space`, where
    `edist [f] [g]` is defined to be `∫⁻ a, edist (f a) (g a)`.

    The integral used here is `lintegral : (α → ennreal) → ennreal`, which is defined in the file
    `integration.lean`.

    See `edist_mk_mk` and `edist_to_fun`.


## Implementation notes

`f.to_fun`  : To find a representative of `f : α →ₘ β`, use `f.to_fun`.
              For each operation `op` in L0, there is a lemma called `op_to_fun`, characterizing,
              say, `(f op g).to_fun`.

`mk`        : To constructs an L0 function from an ordinary function, use `mk`

`comp`      : If you want [g ∘ f], use `comp`.

`comp₂`     : If you want [λa, g (f₁ a) (f₂ a)], use `comp₂`. For example, [f + g] is `comp₂ (+)`


## Tags

function space, almost everywhere equal, L0, ae_eq_fun

-/
noncomputable theory
open_locale classical

namespace measure_theory
open set lattice filter topological_space

universes u v
variables {α : Type u} {β : Type v} [measure_space α]

section measurable_space
variables [measurable_space β]

variables (α β)

/-- The equivalence relation of being almost everywhere equal -/
instance ae_eq_fun.setoid : setoid { f : α → β // measurable f } :=
⟨ λf g, ∀ₘ a, f.1 a = g.1 a,
  assume ⟨f, hf⟩, by filter_upwards [] assume a, rfl,
  assume ⟨f, hf⟩ ⟨g, hg⟩ hfg, by filter_upwards [hfg] assume a, eq.symm,
  assume ⟨f, hf⟩ ⟨g, hg⟩ ⟨h, hh⟩ hfg hgh, by filter_upwards [hfg, hgh] assume a, eq.trans ⟩

/-- Quotient space by the above equivalence relation. -/
def ae_eq_fun : Type (max u v) := quotient (ae_eq_fun.setoid α β)

variables {α β}

infixr ` →ₘ `:25 := ae_eq_fun

end measurable_space

namespace ae_eq_fun
variables [measurable_space β]

/-- Construct the equivalence class `[f]` of a measurable function `f`. -/
def mk (f : α → β) (hf : measurable f) : α →ₘ β := quotient.mk ⟨f, hf⟩

/-- Find a representative of an `ae_eq_fun` [f] -/
protected def to_fun (f : α →ₘ β) : α → β := @quotient.out _ (ae_eq_fun.setoid α β) f

protected lemma measurable (f : α →ₘ β) : measurable f.to_fun :=
(@quotient.out _ (ae_eq_fun.setoid α β) f).2

instance : has_coe (α →ₘ β) (α → β) := ⟨λf, f.to_fun⟩

@[simp] lemma quot_mk_eq_mk (f : {f : α → β // measurable f}) : quot.mk setoid.r f = mk f.1 f.2 :=
by cases f; refl

@[simp] lemma mk_eq_mk (f g : α → β) (hf hg) :
  mk f hf = mk g hg ↔ (∀ₘ a, f a = g a) :=
⟨quotient.exact, assume h, quotient.sound h⟩

@[extensionality] lemma ext (f g : α →ₘ β) (f' g' : α → β) (hf' hg') (hf : mk f' hf' = f)
  (hg : mk g' hg' = g) (h : ∀ₘ a, f' a = g' a) : f = g :=
by { rw [← hf, ← hg], rw mk_eq_mk, assumption }

lemma self_eq_mk (f : α →ₘ β) : f = mk (f.to_fun) f.measurable :=
by simp [mk, ae_eq_fun.to_fun]

lemma all_ae_mk_to_fun (f : α → β) (hf) : ∀ₘ a, (mk f hf).to_fun a = f a :=
by rw [← mk_eq_mk _ f _ hf, ← self_eq_mk (mk f hf)]

/-- [g ∘ f] -/
def comp {γ : Type*} [measurable_space γ] (g : β → γ) (hg : measurable g) (f : α →ₘ β) : α →ₘ γ :=
quotient.lift_on f (λf, mk (g ∘ f.1)  (measurable.comp hg f.2)) $ assume f₁ f₂ eq,
  by refine quotient.sound _; filter_upwards [eq] assume a, congr_arg g

@[simp] lemma comp_mk {γ : Type*} [measurable_space γ] (g : β → γ) (hg : measurable g)
  (f : α → β) (hf) : comp g hg (mk f hf) = mk (g ∘ f) (measurable.comp hg hf) :=
rfl

lemma comp_eq_mk_to_fun {γ : Type*} [measurable_space γ] (g : β → γ) (hg : measurable g) (f : α →ₘ β) :
  comp g hg f = mk (g ∘ f.to_fun) (hg.comp f.measurable) :=
by conv_lhs { rw [self_eq_mk f, comp_mk] }

lemma comp_to_fun {γ : Type*} [measurable_space γ] (g : β → γ) (hg : measurable g) (f : α →ₘ β) :
  ∀ₘ a, (comp g hg f).to_fun a = (g ∘ f.to_fun) a :=
by { rw comp_eq_mk_to_fun, apply all_ae_mk_to_fun }

/-- `[λa, g (f₁ a) (f₂ a)]` -/
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

lemma comp₂_eq_mk_to_fun {γ δ : Type*} [measurable_space γ] [measurable_space δ]
  (g : β → γ → δ) (hg : measurable (λp:β×γ, g p.1 p.2)) (f₁ : α →ₘ β) (f₂ : α →ₘ γ) :
  comp₂ g hg f₁ f₂ = mk (λa, g (f₁.to_fun a) (f₂.to_fun a))
    (hg.comp (measurable_prod_mk f₁.measurable f₂.measurable)) :=
by conv_lhs { rw [self_eq_mk f₁, self_eq_mk f₂, comp₂_mk_mk] }

lemma comp₂_to_fun {γ δ : Type*} [measurable_space γ] [measurable_space δ]
  (g : β → γ → δ) (hg : measurable (λp:β×γ, g p.1 p.2)) (f₁ : α →ₘ β) (f₂ : α →ₘ γ) :
  ∀ₘ a, (comp₂ g hg f₁ f₂).to_fun a = g (f₁.to_fun a) (f₂.to_fun a) :=
by { rw comp₂_eq_mk_to_fun, apply all_ae_mk_to_fun }

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
    for almost all `a` -/
def lift_pred (p : β → Prop) (f : α →ₘ β) : Prop :=
quotient.lift_on f (λf, ∀ₘ a, p (f.1 a))
begin
  assume f g h, dsimp, refine propext (all_ae_congr _),
  filter_upwards [h], simp {contextual := tt}
end

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
    `(f a, g a)` for almost all `a` -/
def lift_rel {γ : Type*} [measurable_space γ] (r : β → γ → Prop) (f : α →ₘ β) (g : α →ₘ γ) : Prop :=
lift_pred (λp:β×γ, r p.1 p.2)
  (comp₂ prod.mk (measurable_prod_mk
    (measurable_fst measurable_id) (measurable_snd measurable_id)) f g)

lemma lift_rel_mk_mk {γ : Type*} [measurable_space γ] (r : β → γ → Prop)
  (f : α → β) (g : α → γ) (hf hg) : lift_rel r (mk f hf) (mk g hg) ↔ ∀ₘ a, r (f a) (g a) :=
iff.rfl

lemma lift_rel_iff_to_fun {γ : Type*} [measurable_space γ] (r : β → γ → Prop) (f : α →ₘ β)
  (g : α →ₘ γ) : lift_rel r f g ↔ ∀ₘ a, r (f.to_fun a) (g.to_fun a) :=
by conv_lhs { rw [self_eq_mk f, self_eq_mk g, lift_rel_mk_mk] }

section order

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

lemma le_iff_to_fun_le [preorder β] {f g : α →ₘ β} : f ≤ g ↔ ∀ₘ a, f.to_fun a ≤ g.to_fun a :=
by { conv_lhs { rw [self_eq_mk f, self_eq_mk g] }, rw mk_le_mk }

instance [partial_order β] : partial_order (α →ₘ β) :=
{ le_antisymm :=
  begin
    rintros ⟨⟨f, hf⟩⟩ ⟨⟨g, hg⟩⟩ hfg hgf,
    refine quotient.sound _,
    filter_upwards [hfg, hgf] assume a, le_antisymm
  end,
  .. ae_eq_fun.preorder }

/- TODO: Prove L0 space is a lattice if β is linear order.
         What if β is only a lattice? -/

-- instance [linear_order β] : semilattice_sup (α →ₘ β) :=
-- { sup := comp₂ (⊔) (_),
--    .. ae_eq_fun.partial_order }

end order

variable (α)
/-- Equivalence class of a constant function: `[λa:α, b]` -/
def const (b : β) : α →ₘ β := mk (λa:α, b) measurable_const

lemma const_to_fun (b : β) : ∀ₘ a, (const α b).to_fun a = b := all_ae_mk_to_fun _ _
variable {α}

instance [has_zero β] : has_zero (α →ₘ β) := ⟨const α 0⟩
lemma zero_def [has_zero β] : (0 : α →ₘ β) = mk (λa:α, 0) measurable_const := rfl
lemma zero_to_fun [has_zero β] : ∀ₘ a, (0 : α →ₘ β).to_fun a = 0 := const_to_fun _ _

instance [has_one β] : has_one (α →ₘ β) := ⟨const α 1⟩
lemma one_def [has_one β] : (1 : α →ₘ β) = mk (λa:α, 1) measurable_const := rfl
lemma one_to_fun [has_one β] : ∀ₘ a, (1 : α →ₘ β).to_fun a = 1 := const_to_fun _ _

section add_monoid
variables {γ : Type*}
  [topological_space γ] [second_countable_topology γ] [add_monoid γ] [topological_add_monoid γ]

protected def add : (α →ₘ γ) → (α →ₘ γ) → (α →ₘ γ) :=
comp₂ (+) (measurable_add (measurable_fst measurable_id) (measurable_snd  measurable_id))

instance : has_add (α →ₘ γ) := ⟨ae_eq_fun.add⟩

@[simp] lemma mk_add_mk (f g : α → γ) (hf hg) :
   (mk f hf) + (mk g hg) = mk (λa, (f a) + (g a)) (measurable_add hf hg) := rfl

lemma add_to_fun (f g : α →ₘ γ) : ∀ₘ a, (f + g).to_fun a = f.to_fun a + g.to_fun a :=
comp₂_to_fun _ _ _ _

instance : add_monoid (α →ₘ γ) :=
{ zero      := 0,
  add       := ae_eq_fun.add,
  add_zero  := by rintros ⟨a⟩; exact quotient.sound (univ_mem_sets' $ assume a, add_zero _),
  zero_add  := by rintros ⟨a⟩; exact quotient.sound (univ_mem_sets' $ assume a, zero_add _),
  add_assoc :=
    by rintros ⟨a⟩ ⟨b⟩ ⟨c⟩; exact quotient.sound (univ_mem_sets' $ assume a, add_assoc _ _ _) }

end add_monoid

section add_comm_monoid
variables {γ : Type*}
  [topological_space γ] [second_countable_topology γ] [add_comm_monoid γ] [topological_add_monoid γ]

instance : add_comm_monoid (α →ₘ γ) :=
{ add_comm := by rintros ⟨a⟩ ⟨b⟩; exact quotient.sound (univ_mem_sets' $ assume a, add_comm _ _),
  .. ae_eq_fun.add_monoid }

end add_comm_monoid

section add_group

variables {γ : Type*} [topological_space γ] [add_group γ] [topological_add_group γ]

protected def neg : (α →ₘ γ) → (α →ₘ γ) := comp has_neg.neg (measurable_neg measurable_id)

instance : has_neg (α →ₘ γ) := ⟨ae_eq_fun.neg⟩

@[simp] lemma neg_mk (f : α → γ) (hf) : -(mk f hf) = mk (-f) (measurable_neg hf) := rfl

lemma neg_to_fun (f : α →ₘ γ) : ∀ₘ a, (-f).to_fun a = - f.to_fun a := comp_to_fun _ _ _

variables [second_countable_topology γ]
instance : add_group (α →ₘ γ) :=
{ neg          := ae_eq_fun.neg,
  add_left_neg := by rintros ⟨a⟩; exact quotient.sound (univ_mem_sets' $ assume a, add_left_neg _),
  .. ae_eq_fun.add_monoid
 }

@[simp] lemma mk_sub_mk (f g : α → γ) (hf hg) :
   (mk f hf) - (mk g hg) = mk (λa, (f a) - (g a)) (measurable_sub hf hg) := rfl

lemma sub_to_fun (f g : α →ₘ γ) : ∀ₘ a, (f - g).to_fun a = f.to_fun a - g.to_fun a :=
begin
  rw sub_eq_add_neg,
  filter_upwards [add_to_fun f (-g), neg_to_fun g],
  assume a, simp only [mem_set_of_eq],
  repeat {assume h, rw h},
  refl
end

end add_group

section add_comm_group

variables {γ : Type*}
  [topological_space γ] [second_countable_topology γ] [add_comm_group γ] [topological_add_group γ]

instance : add_comm_group (α →ₘ γ) :=
{ add_comm := ae_eq_fun.add_comm_monoid.add_comm
  .. ae_eq_fun.add_group
}

end add_comm_group

section semimodule

variables {K : Type*} [semiring K] [topological_space K]
variables {γ : Type*} [topological_space γ]
          [add_comm_monoid γ] [semimodule K γ] [topological_semimodule K γ]

protected def smul : K → (α →ₘ γ) → (α →ₘ γ) :=
λ c f, comp (has_scalar.smul c) (measurable_smul measurable_id) f

instance : has_scalar K (α →ₘ γ) := ⟨ae_eq_fun.smul⟩

@[simp] lemma smul_mk (c : K) (f : α → γ) (hf) : c • (mk f hf) = mk (c • f) (measurable_smul hf) :=
rfl

lemma smul_to_fun (c : K) (f : α →ₘ γ) : ∀ₘ a, (c • f).to_fun a = c • f.to_fun a :=
comp_to_fun _ _ _

variables [second_countable_topology γ] [topological_add_monoid γ]

instance : semimodule K (α →ₘ γ) :=
{ one_smul  := by { rintros ⟨f, hf⟩, simp only [quot_mk_eq_mk, smul_mk, one_smul] },
  mul_smul  :=
    by { rintros x y ⟨f, hf⟩, simp only [quot_mk_eq_mk, smul_mk, mul_action.mul_smul x y f], refl },
  smul_add  :=
  begin
    rintros x ⟨f, hf⟩ ⟨g, hg⟩, simp only [quot_mk_eq_mk, smul_mk, mk_add_mk],
    congr, exact smul_add x f g
  end,
  smul_zero := by { intro x, simp only [zero_def, smul_mk], congr, exact smul_zero x },
  add_smul  :=
  begin
    intros x y, rintro ⟨f, hf⟩, simp only [quot_mk_eq_mk, smul_mk, mk_add_mk], congr,
    exact add_smul x y f
  end,
  zero_smul :=
    by { rintro ⟨f, hf⟩, simp only [quot_mk_eq_mk, smul_mk, zero_def], congr, exact zero_smul K f }}

end semimodule

section module

variables {K : Type*} [ring K] [topological_space K]
variables {γ : Type*} [topological_space γ] [second_countable_topology γ] [add_comm_group γ]
          [topological_add_group γ] [module K γ] [topological_semimodule K γ]

instance : module K (α →ₘ γ) := { .. ae_eq_fun.semimodule }

end module

section vector_space

variables {K : Type*} [discrete_field K] [topological_space K]
variables {γ : Type*} [topological_space γ] [second_countable_topology γ] [add_comm_group γ]
          [topological_add_group γ] [vector_space K γ] [topological_semimodule K γ]

instance : vector_space K (α →ₘ γ) := { .. ae_eq_fun.semimodule }

end vector_space

/- TODO : Prove that L0 is a complete space if the codomain is complete. -/
/- TODO : Multiplicative structure of L0 if useful -/

open ennreal

/-- For `f : α → ennreal`, Define `∫ [f]` to be `∫ f` -/
def eintegral (f : α →ₘ ennreal) : ennreal :=
quotient.lift_on f (λf, lintegral f.1) (assume ⟨f, hf⟩ ⟨g, hg⟩ eq, lintegral_congr_ae eq)

@[simp] lemma eintegral_mk (f : α → ennreal) (hf) : eintegral (mk f hf) = lintegral f := rfl

lemma eintegral_to_fun (f : α →ₘ ennreal) : eintegral f = lintegral (f.to_fun) :=
by conv_lhs { rw [self_eq_mk f, eintegral_mk] }

/-- `∫ [0] = 0` -/
@[simp] lemma eintegral_zero : eintegral (0 : α →ₘ ennreal) = 0 := lintegral_zero

/-- `∫ [f] = 0` if and only if `[f] = 0` -/
@[simp] lemma eintegral_eq_zero_iff (f : α →ₘ ennreal) : eintegral f = 0 ↔ f = 0 :=
begin
  rcases f with ⟨f, hf⟩,
  refine iff.trans (lintegral_eq_zero_iff hf) ⟨_, _⟩,
  { assume h, exact quotient.sound h },
  { assume h, exact quotient.exact h }
end

lemma eintegral_add : ∀(f g : α →ₘ ennreal), eintegral (f + g) = eintegral f + eintegral g :=
by rintros ⟨f⟩ ⟨g⟩; simp only [quot_mk_eq_mk, mk_add_mk, eintegral_mk, lintegral_add f.2 g.2]

lemma eintegral_le_eintegral {f g : α →ₘ ennreal} (h : f ≤ g) : eintegral f ≤ eintegral g :=
begin
  rcases f with ⟨f, hf⟩, rcases g with ⟨g, hg⟩,
  simp only [quot_mk_eq_mk, eintegral_mk, mk_le_mk] at *,
  refine lintegral_le_lintegral_ae _,
  filter_upwards [h], simp
end

section
variables {γ : Type*} [emetric_space γ] [second_countable_topology γ]

/-- `comp_edist f g a` will return `edist (f a) (g a) -/
def comp_edist (f g : α →ₘ γ) : α →ₘ ennreal := comp₂ edist measurable_edist' f g

lemma comp_edist_to_fun (f g : α →ₘ γ) :
  ∀ₘ a, (comp_edist f g).to_fun a = edist (f.to_fun a) (g.to_fun a) :=
comp₂_to_fun _ _ _ _

lemma comp_edist_self : ∀ (f : α →ₘ γ), comp_edist f f = 0 :=
by rintro ⟨f⟩; refine quotient.sound _; simp only [edist_self]

instance : emetric_space (α →ₘ γ) :=
{ edist               := λf g, eintegral (comp_edist f g),
  edist_self          := assume f, (eintegral_eq_zero_iff _).2 (comp_edist_self _),
  edist_comm          :=
    by rintros ⟨f⟩ ⟨g⟩; simp only [comp_edist, quot_mk_eq_mk, comp₂_mk_mk, edist_comm],
  edist_triangle      :=
  begin
    rintros ⟨f⟩ ⟨g⟩ ⟨h⟩,
    simp only [comp_edist, quot_mk_eq_mk, comp₂_mk_mk, (eintegral_add _ _).symm],
    exact lintegral_le_lintegral _ _ (assume a, edist_triangle _ _ _)
  end,
  eq_of_edist_eq_zero :=
  begin
    rintros ⟨f⟩ ⟨g⟩,
    simp only [edist, comp_edist, quot_mk_eq_mk, comp₂_mk_mk, eintegral_eq_zero_iff],
    simp only [zero_def, mk_eq_mk, edist_eq_zero],
    assume h, assumption
  end }

lemma edist_mk_mk {f g : α → γ} (hf hg) : edist (mk f hf) (mk g hg) = ∫⁻ x, edist (f x) (g x) := rfl

lemma edist_to_fun (f g : α →ₘ γ) : edist f g = ∫⁻ x, edist (f.to_fun x) (g.to_fun x) :=
by conv_lhs { rw [self_eq_mk f, self_eq_mk g, edist_mk_mk] }

lemma edist_zero_to_fun [has_zero γ] (f : α →ₘ γ) : edist f 0 = ∫⁻ x, edist (f.to_fun x) 0 :=
begin
  rw edist_to_fun,
  apply lintegral_congr_ae,
  have : ∀ₘ a:α, (0 : α →ₘ γ).to_fun a = 0 := zero_to_fun,
  filter_upwards [this],
  assume a, simp only [mem_set_of_eq],
  assume h, rw h
end

end

section metric
variables {γ : Type*} [metric_space γ] [second_countable_topology γ]

lemma edist_mk_mk' {f g : α → γ} (hf hg) :
  edist (mk f hf) (mk g hg) = ∫⁻ x, nndist (f x) (g x) :=
show  (∫⁻ x, edist (f x) (g x)) =  ∫⁻ x, nndist (f x) (g x), from
lintegral_congr_ae $all_ae_of_all $ assume a, edist_nndist _ _

lemma edist_to_fun' (f g : α →ₘ γ) : edist f g = ∫⁻ x, nndist (f.to_fun x) (g.to_fun x) :=
by conv_lhs { rw [self_eq_mk f, self_eq_mk g, edist_mk_mk'] }

end metric

section normed_group

variables {γ : Type*} [normed_group γ] [second_countable_topology γ]

lemma edist_eq_add_add : ∀ {f g h : α →ₘ γ}, edist f g = edist (f + h) (g + h) :=
begin
  rintros ⟨f⟩ ⟨g⟩ ⟨h⟩,
  simp only [quot_mk_eq_mk, mk_add_mk, edist_mk_mk'],
  apply lintegral_congr_ae,
  filter_upwards [], simp [nndist_eq_nnnorm]
end

end normed_group

section normed_space

set_option class.instance_max_depth 100

variables {K : Type*} [normed_field K]
variables {γ : Type*} [normed_group γ] [second_countable_topology γ] [normed_space K γ]

lemma edist_smul (x : K) : ∀ f : α →ₘ γ, edist (x • f) 0 = (ennreal.of_real ∥x∥) * edist f 0 :=
begin
  rintros ⟨f, hf⟩, simp only [zero_def, edist_mk_mk', quot_mk_eq_mk, smul_mk],
  exact calc
    (∫⁻ (a : α), nndist (x • f a) 0) = (∫⁻ (a : α), (nnnorm x) * nnnorm (f a)) :
      lintegral_congr_ae $ by { filter_upwards [], assume a, simp [nndist_eq_nnnorm, nnnorm_smul] }
    ... = _ : lintegral_const_mul _ (measurable_coe_nnnorm hf)
    ... = _ :
    begin
      convert rfl,
      { rw ← coe_nnnorm, rw [ennreal.of_real], congr, exact nnreal.of_real_coe },
      { funext, simp [nndist_eq_nnnorm] }
    end,
end

end normed_space

end ae_eq_fun

end measure_theory
