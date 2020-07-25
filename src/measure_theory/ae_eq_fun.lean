/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou
-/
import measure_theory.integration
import order.filter.germ

/-!

# Almost everywhere equal functions

Two measurable functions are treated as identical if they are almost everywhere equal. We form the
set of equivalence classes under the relation of being almost everywhere equal, which is sometimes
known as the `L⁰` space.

See `l1_space.lean` for `L¹` space.

## Notation

* `α →ₘ[μ] β` is the type of `L⁰` space, where `α` and `β` are measurable spaces and `μ`
  is a measure on `α`. `f : α →ₘ β` is a "function" in `L⁰`. In comments, `[f]` is also used
  to denote an `L⁰` function.

  `ₘ` can be typed as `\_m`. Sometimes it is shown as a box if font is missing.


## Main statements

* The linear structure of `L⁰` :
    Addition and scalar multiplication are defined on `L⁰` in the natural way, i.e.,
    `[f] + [g] := [f + g]`, `c • [f] := [c • f]`. So defined, `α →ₘ β` inherits the linear structure
    of `β`. For example, if `β` is a module, then `α →ₘ β` is a module over the same ring.

    See `mk_add_mk`,  `neg_mk`,     `mk_sub_mk`,  `smul_mk`,
        `add_to_fun`, `neg_to_fun`, `sub_to_fun`, `smul_to_fun`

* The order structure of `L⁰` :
    `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
    And `α →ₘ β` inherits the preorder and partial order of `β`.

    TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
    linear order, since otherwise `f ⊔ g` may not be a measurable function.

* Emetric on `L⁰` :
    If `β` is an `emetric_space`, then `L⁰` can be made into an `emetric_space`, where
    `edist [f] [g]` is defined to be `∫⁻ a, edist (f a) (g a)`.

    The integral used here is `lintegral : (α → ennreal) → ennreal`, which is defined in the file
    `integration.lean`.

    See `edist_mk_mk` and `edist_to_fun`.

## Implementation notes

* `f.to_fun`     : To find a representative of `f : α →ₘ β`, use `f.to_fun`.
                 For each operation `op` in `L⁰`, there is a lemma called `op_to_fun`, characterizing,
                 say, `(f op g).to_fun`.
* `ae_eq_fun.mk` : To constructs an `L⁰` function `α →ₘ β` from a measurable function `f : α → β`,
                 use `ae_eq_fun.mk`
* `comp`         : Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₘ γ`
* `comp₂`        : Use `comp₂ g f₁ f₂ to get `[λa, g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`


## Tags

function space, almost everywhere equal, `L⁰`, ae_eq_fun

-/

noncomputable theory
open_locale classical

namespace measure_theory
open set filter topological_space function

variables {α β γ δ : Type*} [measurable_space α]

section measurable_space
variables [measurable_space β]

variable (β)

/-- The equivalence relation of being almost everywhere equal -/
def measure.ae_eq_setoid (μ : measure α) : setoid { f : α → β // measurable f } :=
⟨λf g, (f : α → β) =ᵐ[μ] g, λ f, ae_eq_refl f, λ f g, ae_eq_symm, λ f g h, ae_eq_trans⟩

variable (α)

/-- The space of equivalence classes of measurable functions, where two measurable functions are
    equivalent if they agree almost everywhere, i.e., they differ on a set of measure `0`.  -/
def ae_eq_fun (μ : measure α) : Type* := quotient (μ.ae_eq_setoid β)

variables {α β}

notation α ` →ₘ[`:25 μ `] ` β := ae_eq_fun α β μ

end measurable_space

namespace ae_eq_fun
variables [measurable_space β] [measurable_space γ] [measurable_space δ] {μ : measure α}

/-- Construct the equivalence class `[f]` of a measurable function `f`, based on the equivalence
    relation of being almost everywhere equal. -/
def mk (f : α → β) (hf : measurable f) : α →ₘ[μ] β := quotient.mk' ⟨f, hf⟩

/-- A representative of an `ae_eq_fun` [f] -/
instance : has_coe_to_fun (α →ₘ[μ] β) :=
⟨_, λf, ((quotient.out' f : {f : α → β // measurable f}) : α → β)⟩

protected lemma measurable (f : α →ₘ[μ] β) : measurable f :=
(quotient.out' f).2

@[simp] lemma quot_mk_eq_mk (f : α → β) (hf) :
  (quot.mk (@setoid.r _ $ μ.ae_eq_setoid β) ⟨f, hf⟩ : α →ₘ[μ] β) = mk f hf :=
rfl

@[simp] lemma quotient_out'_eq_coe_fn (f : α →ₘ[μ] β) :
  quotient.out' f = ⟨f, f.measurable⟩ :=
subtype.eq rfl

@[simp] lemma mk_eq_mk {f g : α → β} {hf hg} :
  (mk f hf : α →ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
quotient.eq'

@[simp] lemma mk_coe_fn (f : α →ₘ[μ] β) : mk f f.measurable = f :=
by simpa using quotient.out_eq' f

@[ext] lemma ext {f g : α →ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g :=
by rwa [← f.mk_coe_fn, ← g.mk_coe_fn, mk_eq_mk]

lemma coe_fn_mk (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β) =ᵐ[μ] f :=
@quotient.mk_out' _ (μ.ae_eq_setoid β) (⟨f, hf⟩ : {f // measurable f})

@[elab_as_eliminator]
lemma induction_on (f : α →ₘ[μ] β) {p : (α →ₘ[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
quotient.induction_on' f $ subtype.forall.2 H

@[elab_as_eliminator]
lemma induction_on₂ {α' β' : Type*} [measurable_space α'] [measurable_space β'] {μ' : measure α'}
  (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → Prop}
  (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) :
  p f f' :=
induction_on f $ λ f hf, induction_on f' $ H f hf

@[elab_as_eliminator]
lemma induction_on₃ {α' β' : Type*} [measurable_space α'] [measurable_space β'] {μ' : measure α'}
  {α'' β'' : Type*} [measurable_space α''] [measurable_space β''] {μ'' : measure α''}
  (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') (f'' : α'' →ₘ[μ''] β'')
  {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → (α'' →ₘ[μ''] β'') → Prop}
  (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) :
  p f f' f'' :=
induction_on f $ λ f hf, induction_on₂ f' f'' $ H f hf

/-- Given a measurable function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. -/
def comp (g : β → γ) (hg : measurable g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
quotient.lift_on' f (λ f, mk (g ∘ (f : α → β)) (hg.comp f.2)) $ λ f f' H, mk_eq_mk.2 $ H.fun_comp g

@[simp] lemma comp_mk (g : β → γ) (hg : measurable g)
  (f : α → β) (hf) :
  comp g hg (mk f hf : α →ₘ[μ] β) = mk (g ∘ f) (hg.comp hf) :=
rfl

lemma comp_eq_mk (g : β → γ) (hg : measurable g) (f : α →ₘ[μ] β) :
  comp g hg f = mk (g ∘ f) (hg.comp f.measurable) :=
by rw [← comp_mk g hg f f.measurable, mk_coe_fn]

lemma coe_fn_comp (g : β → γ) (hg : measurable g) (f : α →ₘ[μ] β) :
  comp g hg f =ᵐ[μ] g ∘ f :=
by { rw [comp_eq_mk], apply coe_fn_mk }

/-- The class of `x ↦ (f x, g x)`. -/
def pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : α →ₘ[μ] β × γ :=
quotient.lift_on₂' f g (λ f g, mk (λ x, (f.1 x, g.1 x)) (f.2.prod_mk g.2)) $
  λ f g f' g' Hf Hg, mk_eq_mk.2 $ Hf.prod_mk Hg

@[simp] lemma pair_mk_mk (f : α → β) (hf) (g : α → γ) (hg) :
  (mk f hf : α →ₘ[μ] β).pair (mk g hg) = mk (λ x, (f x, g x)) (hf.prod_mk hg) :=
rfl

lemma pair_eq_mk (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
  f.pair g = mk (λ x, (f x, g x)) (f.measurable.prod_mk g.measurable) :=
by simp only [← pair_mk_mk, mk_coe_fn]

lemma coe_fn_pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
  f.pair g =ᵐ[μ] (λ x, (f x, g x)) :=
by { rw pair_eq_mk, apply coe_fn_mk }

/-- Given a measurable function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `λa, g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[λa, g (f₁ a) (f₂ a)] : α →ₘ γ` -/
def comp₂ {γ δ : Type*} [measurable_space γ] [measurable_space δ] (g : β → γ → δ)
  (hg : measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) : α →ₘ[μ] δ :=
comp _ hg (f₁.pair f₂)

@[simp] lemma comp₂_mk_mk {γ δ : Type*} [measurable_space γ] [measurable_space δ]
  (g : β → γ → δ) (hg : measurable (uncurry g)) (f₁ : α → β) (f₂ : α → γ) (hf₁ hf₂) :
  comp₂ g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
    mk (λa, g (f₁ a) (f₂ a)) (hg.comp (hf₁.prod_mk hf₂)) :=
rfl

lemma comp₂_eq_pair {γ δ : Type*} [measurable_space γ] [measurable_space δ]
  (g : β → γ → δ) (hg : measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
rfl

lemma comp₂_eq_mk {γ δ : Type*} [measurable_space γ] [measurable_space δ]
  (g : β → γ → δ) (hg : measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  comp₂ g hg f₁ f₂ = mk (λ a, g (f₁ a) (f₂ a))
    (hg.comp (f₁.measurable.prod_mk f₂.measurable)) :=
by rw [comp₂_eq_pair, pair_eq_mk, comp_mk]; refl

lemma coe_fn_comp₂ {γ δ : Type*} [measurable_space γ] [measurable_space δ]
  (g : β → γ → δ) (hg : measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  comp₂ g hg f₁ f₂ =ᵐ[μ] λ a, g (f₁ a) (f₂ a) :=
by { rw comp₂_eq_mk, apply coe_fn_mk }

/-- Interpret `f : α →ₘ[μ] β` as a germ at `μ.ae` forgetting that `f` is measurable. -/
def to_germ (f : α →ₘ[μ] β) : germ μ.ae β :=
quotient.lift_on' f (λ f, ((f : α → β) : germ μ.ae β)) $ λ f g H, germ.coe_eq.2 H

@[simp] lemma mk_to_germ (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β).to_germ = f := rfl

lemma to_germ_eq (f : α →ₘ[μ] β) : f.to_germ = (f : α → β) :=
by rw [← mk_to_germ, mk_coe_fn]

lemma to_germ_injective : injective (to_germ : (α →ₘ[μ] β) → germ μ.ae β) :=
λ f g H, ext $ germ.coe_eq.1 $ by rwa [← to_germ_eq, ← to_germ_eq]

lemma comp_to_germ (g : β → γ) (hg : measurable g) (f : α →ₘ[μ] β) :
  (comp g hg f).to_germ = f.to_germ.map g :=
induction_on f $ λ f hf, by simp

lemma comp₂_to_germ (g : β → γ → δ) (hg : measurable (uncurry g))
  (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  (comp₂ g hg f₁ f₂).to_germ = f₁.to_germ.map₂ g f₂.to_germ :=
induction_on₂ f₁ f₂ $ λ f₁ hf₁ f₂ hf₂, by simp

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
    for almost all `a` -/
def lift_pred (p : β → Prop) (f : α →ₘ[μ] β) : Prop := f.to_germ.lift_pred p

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
    `(f a, g a)` for almost all `a` -/
def lift_rel (r : β → γ → Prop) (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : Prop :=
f.to_germ.lift_rel r g.to_germ

lemma lift_rel_mk_mk {r : β → γ → Prop} {f : α → β} {g : α → γ} {hf hg} :
  lift_rel r (mk f hf : α →ₘ[μ] β) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
iff.rfl

lemma lift_rel_iff_coe_fn {r : β → γ → Prop} {f : α →ₘ[μ] β} {g : α →ₘ[μ] γ} :
  lift_rel r f g ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
by rw [← lift_rel_mk_mk, mk_coe_fn, mk_coe_fn]

section order

instance [preorder β] : preorder (α →ₘ[μ] β) := preorder.lift to_germ

@[simp] lemma mk_le_mk [preorder β] {f g : α → β} (hf hg) :
  (mk f hf : α →ₘ[μ] β) ≤ mk g hg ↔ f ≤ᵐ[μ] g :=
iff.rfl

@[simp, norm_cast] lemma coe_fn_le [preorder β] {f g : α →ₘ[μ] β} :
  (f : α → β) ≤ᵐ[μ] g ↔ f ≤ g :=
lift_rel_iff_coe_fn.symm

instance [partial_order β] : partial_order (α →ₘ[μ] β) :=
partial_order.lift to_germ to_germ_injective

/- TODO: Prove `L⁰` space is a lattice if β is linear order.
         What if β is only a lattice? -/

-- instance [linear_order β] : semilattice_sup (α →ₘ β) :=
-- { sup := comp₂ (⊔) (_),
--    .. ae_eq_fun.partial_order }

end order

variable (α)
/-- The equivalence class of a constant function: `[λa:α, b]`, based on the equivalence relation of
    being almost everywhere equal -/
def const (b : β) : α →ₘ[μ] β := mk (λa:α, b) measurable_const

lemma coe_fn_const (b : β) : (const α b : α →ₘ[μ] β) =ᵐ[μ] function.const α b :=
coe_fn_mk _ _

variable {α}

instance [inhabited β] : inhabited (α →ₘ[μ] β) := ⟨const α (default β)⟩

@[to_additive] instance [has_one β] : has_one (α →ₘ[μ] β) := ⟨const α 1⟩
@[to_additive] lemma one_def [has_one β] : (1 : α →ₘ[μ] β) = mk (λa:α, 1) measurable_const := rfl
@[to_additive] lemma coe_fn_one [has_one β] : ⇑(1 : α →ₘ[μ] β) =ᵐ[μ] 1 := coe_fn_const _ _
@[simp, to_additive] lemma one_to_germ [has_one β] : (1 : α →ₘ[μ] β).to_germ = 1 := rfl

section monoid
variables
  [topological_space γ] [second_countable_topology γ] [borel_space γ]
  [monoid γ] [has_continuous_mul γ]

@[to_additive]
instance : has_mul (α →ₘ[μ] γ) := ⟨comp₂ (*) measurable_mul⟩

@[simp, to_additive] lemma mk_mul_mk (f g : α → γ) (hf hg) :
  (mk f hf : α →ₘ[μ] γ) * (mk g hg) = mk (f * g) (hf.mul hg) :=
rfl

@[to_additive] lemma coe_fn_mul (f g : α →ₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g := coe_fn_comp₂ _ _ _ _

@[simp, to_additive] lemma mul_to_germ (f g : α →ₘ[μ] γ) :
  (f * g).to_germ = f.to_germ * g.to_germ :=
comp₂_to_germ _ _ _ _

@[to_additive add_monoid]
instance : monoid (α →ₘ[μ] γ) :=
to_germ_injective.monoid to_germ one_to_germ mul_to_germ

end monoid

@[to_additive add_comm_monoid]
instance comm_monoid [topological_space γ] [second_countable_topology γ] [borel_space γ]
  [comm_monoid γ] [has_continuous_mul γ] : comm_monoid (α →ₘ[μ] γ) :=
to_germ_injective.comm_monoid to_germ one_to_germ mul_to_germ

section group

variables [topological_space γ] [borel_space γ] [group γ] [topological_group γ]

@[to_additive] instance : has_inv (α →ₘ[μ] γ) := ⟨comp has_inv.inv measurable_inv⟩

@[simp, to_additive] lemma inv_mk (f : α → γ) (hf) : (mk f hf : α →ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv := rfl

@[to_additive] lemma coe_fn_inv (f : α →ₘ[μ] γ) : ⇑(f⁻¹) =ᵐ[μ] f⁻¹ := coe_fn_comp _ _ _

@[to_additive] lemma inv_to_germ (f : α →ₘ[μ] γ) : (f⁻¹).to_germ = f.to_germ⁻¹ := comp_to_germ _ _ _

variables [second_countable_topology γ]
@[to_additive add_group]
instance : group (α →ₘ[μ] γ) := to_germ_injective.group _ one_to_germ mul_to_germ inv_to_germ

end group

section add_group

variables [topological_space γ] [borel_space γ] [add_group γ] [topological_add_group γ]
  [second_countable_topology γ]

@[simp] lemma mk_sub (f g : α → γ) (hf hg) :
  mk (f - g) (measurable.sub hf hg) = (mk f hf : α →ₘ[μ] γ) - (mk g hg) :=
rfl

lemma coe_fn_sub (f g : α →ₘ[μ] γ) : ⇑(f - g) =ᵐ[μ] f - g :=
(coe_fn_add f (-g)).trans $ (coe_fn_neg g).mono $ λ x hx, congr_arg ((+) (f x)) hx

end add_group

@[to_additive add_comm_group]
instance [topological_space γ] [borel_space γ] [comm_group γ] [topological_group γ]
  [second_countable_topology γ] : comm_group (α →ₘ[μ] γ) :=
{ .. ae_eq_fun.group, .. ae_eq_fun.comm_monoid }

section semimodule

variables {𝕜 : Type*} [semiring 𝕜] [topological_space 𝕜]
variables [topological_space γ] [borel_space γ] [add_comm_monoid γ] [semimodule 𝕜 γ]
  [topological_semimodule 𝕜 γ]

instance : has_scalar 𝕜 (α →ₘ[μ] γ) :=
⟨λ c f, comp ((•) c) (measurable_id.const_smul c) f⟩

@[simp] lemma smul_mk (c : 𝕜) (f : α → γ) (hf) :
  c • (mk f hf : α →ₘ[μ] γ) = mk (c • f) (hf.const_smul _) :=
rfl

lemma coe_fn_smul (c : 𝕜) (f : α →ₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • f := coe_fn_comp _ _ _

lemma smul_to_germ (c : 𝕜) (f : α →ₘ[μ] γ) : (c • f).to_germ = c • f.to_germ :=
comp_to_germ _ _ _

variables [second_countable_topology γ] [has_continuous_add γ]

instance : semimodule 𝕜 (α →ₘ[μ] γ) :=
to_germ_injective.semimodule 𝕜 ⟨@to_germ α γ _ _ μ, zero_to_germ, add_to_germ⟩ smul_to_germ

end semimodule

/- TODO : Prove that `L⁰` is a complete space if the codomain is complete. -/

open ennreal

/-- For `f : α → ennreal`, define `∫ [f]` to be `∫ f` -/
def lintegral (f : α →ₘ[μ] ennreal) : ennreal :=
quotient.lift_on' f (λf, ∫⁻ a, (f : α → ennreal) a ∂μ) (assume f g, lintegral_congr_ae)

@[simp] lemma lintegral_mk (f : α → ennreal) (hf) :
  (mk f hf : α →ₘ[μ] ennreal).lintegral = ∫⁻ a, f a ∂μ := rfl

lemma lintegral_coe_fn (f : α →ₘ[μ] ennreal) : ∫⁻ a, f a ∂μ = f.lintegral :=
by rw [← lintegral_mk, mk_coe_fn]

@[simp] lemma lintegral_zero : lintegral (0 : α →ₘ[μ] ennreal) = 0 := lintegral_zero

@[simp] lemma lintegral_eq_zero_iff {f : α →ₘ[μ] ennreal} : lintegral f = 0 ↔ f = 0 :=
induction_on f $ λ f hf, (lintegral_eq_zero_iff hf).trans mk_eq_mk.symm

lemma lintegral_add (f g : α →ₘ[μ] ennreal) : lintegral (f + g) = lintegral f + lintegral g :=
induction_on₂ f g $ λ f hf g hg, by simp [lintegral_add hf hg]

lemma lintegral_mono {f g : α →ₘ[μ] ennreal} : f ≤ g → lintegral f ≤ lintegral g :=
induction_on₂ f g $ λ f hf g hg hfg, lintegral_mono_ae hfg

section
variables [emetric_space γ] [second_countable_topology γ] [opens_measurable_space γ]

/-- `comp_edist [f] [g] a` will return `edist (f a) (g a) -/
protected def edist (f g : α →ₘ[μ] γ) : α →ₘ[μ] ennreal := comp₂ edist measurable_edist f g

protected lemma edist_comm (f g : α →ₘ[μ] γ) : f.edist g = g.edist f :=
induction_on₂ f g $ λ f hf g hg, mk_eq_mk.2 $ eventually_of_forall $ λ x, edist_comm (f x) (g x)

lemma coe_fn_edist (f g : α →ₘ[μ] γ) : ⇑(f.edist g) =ᵐ[μ] λ a, edist (f a) (g a) :=
coe_fn_comp₂ _ _ _ _

protected lemma edist_self (f : α →ₘ[μ] γ) : f.edist f = 0 :=
induction_on f $ λ f hf, mk_eq_mk.2 $ eventually_of_forall $ λ x, edist_self (f x)

/-- Almost everywhere equal functions form an `emetric_space`, with the emetric defined as
  `edist f g = ∫⁻ a, edist (f a) (g a)`. -/
instance : emetric_space (α →ₘ[μ] γ) :=
{ edist               := λf g, lintegral (f.edist g),
  edist_self          := assume f, lintegral_eq_zero_iff.2 f.edist_self,
  edist_comm          := λ f g, congr_arg lintegral $ f.edist_comm g,
  edist_triangle      := λ f g h, induction_on₃ f g h $ λ f hf g hg h hh,
    calc ∫⁻ a, edist (f a) (h a) ∂μ ≤ ∫⁻ a, edist (f a) (g a) + edist (g a) (h a) ∂μ :
      measure_theory.lintegral_mono (λ a, edist_triangle (f a) (g a) (h a))
    ... = ∫⁻ a, edist (f a) (g a) ∂μ + ∫⁻ a, edist (g a) (h a) ∂μ :
      measure_theory.lintegral_add (hf.edist hg) (hg.edist hh),
  eq_of_edist_eq_zero := λ f g, induction_on₂ f g $ λ f hf g hg H, mk_eq_mk.2 $
    ((measure_theory.lintegral_eq_zero_iff (hf.edist hg)).1 H).mono $ λ x, eq_of_edist_eq_zero }

lemma edist_mk_mk {f g : α → γ} (hf hg) :
  edist (mk f hf : α →ₘ[μ] γ) (mk g hg) = ∫⁻ x, edist (f x) (g x) ∂μ :=
rfl

lemma edist_eq_coe (f g : α →ₘ[μ] γ) : edist f g = ∫⁻ x, edist (f x) (g x) ∂μ :=
by rw [← edist_mk_mk, mk_coe_fn, mk_coe_fn]

lemma edist_zero_eq_coe [has_zero γ] (f : α →ₘ[μ] γ) : edist f 0 = ∫⁻ x, edist (f x) 0 ∂μ :=
by rw [← edist_mk_mk, mk_coe_fn, zero_def]

end

section metric
variables [metric_space γ] [second_countable_topology γ] [opens_measurable_space γ]

lemma edist_mk_mk' {f g : α → γ} (hf hg) :
  edist (mk f hf : α →ₘ[μ] γ) (mk g hg) = ∫⁻ x, nndist (f x) (g x) ∂μ :=
by simp only [edist_mk_mk, edist_nndist]

lemma edist_eq_coe' (f g : α →ₘ[μ] γ) : edist f g = ∫⁻ x, nndist (f x) (g x) ∂μ :=
by simp only [edist_eq_coe, edist_nndist]

end metric

lemma edist_add_right [normed_group γ] [second_countable_topology γ] [borel_space γ]
  (f g h : α →ₘ[μ] γ) :
  edist (f + h) (g + h) = edist f g :=
induction_on₃ f g h $ λ f hf g hg h hh, by simp [edist_mk_mk, edist_dist, dist_add_right]

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜]
variables [normed_group γ] [second_countable_topology γ] [normed_space 𝕜 γ] [borel_space γ]

lemma edist_smul (c : 𝕜) (f : α →ₘ[μ] γ) : edist (c • f) 0 = (ennreal.of_real ∥c∥) * edist f 0 :=
induction_on f $ λ f hf, by simp [edist_mk_mk, zero_def, smul_mk, edist_dist, norm_smul,
  ennreal.of_real_mul, lintegral_const_mul']

end normed_space

section pos_part

variables [topological_space γ] [decidable_linear_order γ] [order_closed_topology γ]
  [second_countable_topology γ] [has_zero γ] [opens_measurable_space γ]

/-- Positive part of an `ae_eq_fun`. -/
def pos_part (f : α →ₘ[μ] γ) : α →ₘ[μ] γ :=
comp (λ x, max x 0) (measurable_id.max measurable_const) f

@[simp] lemma pos_part_mk (f : α → γ) (hf) :
  pos_part (mk f hf : α →ₘ[μ] γ) = mk (λ x, max (f x) 0) (hf.max measurable_const) :=
rfl

lemma coe_fn_pos_part (f : α →ₘ[μ] γ) : ⇑(pos_part f) =ᵐ[μ] (λ a, max (f a) 0) :=
coe_fn_comp _ _ _

end pos_part

end ae_eq_fun

end measure_theory
