/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou
-/
import measure_theory.integral.lebesgue
import order.filter.germ
import topology.continuous_function.algebra
import measure_theory.function.strongly_measurable.basic

/-!

# Almost everywhere equal functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We build a space of equivalence classes of functions, where two functions are treated as identical
if they are almost everywhere equal. We form the set of equivalence classes under the relation of
being almost everywhere equal, which is sometimes known as the `L⁰` space.
To use this space as a basis for the `L^p` spaces and for the Bochner integral, we consider
equivalence classes of strongly measurable functions (or, equivalently, of almost everywhere
strongly measurable functions.)

See `l1_space.lean` for `L¹` space.

## Notation

* `α →ₘ[μ] β` is the type of `L⁰` space, where `α` is a measurable space, `β` is a topological
  space, and `μ` is a measure on `α`. `f : α →ₘ β` is a "function" in `L⁰`.
  In comments, `[f]` is also used to denote an `L⁰` function.

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

## Implementation notes

* `f.to_fun`     : To find a representative of `f : α →ₘ β`, use the coercion `(f : α → β)`, which
                 is implemented as `f.to_fun`.
                 For each operation `op` in `L⁰`, there is a lemma called `coe_fn_op`,
                 characterizing, say, `(f op g : α → β)`.
* `ae_eq_fun.mk` : To constructs an `L⁰` function `α →ₘ β` from an almost everywhere strongly
                 measurable function `f : α → β`, use `ae_eq_fun.mk`
* `comp`         : Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₘ γ` when `g` is
                 continuous. Use `comp_measurable` if `g` is only measurable (this requires the
                 target space to be second countable).
* `comp₂`        : Use `comp₂ g f₁ f₂ to get `[λ a, g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`


## Tags

function space, almost everywhere equal, `L⁰`, ae_eq_fun

-/

noncomputable theory
open_locale classical ennreal topology

open set filter topological_space ennreal emetric measure_theory function
variables {α β γ δ : Type*} [measurable_space α] {μ ν : measure α}

namespace measure_theory

section measurable_space
variables [topological_space β]

variable (β)

/-- The equivalence relation of being almost everywhere equal for almost everywhere strongly
measurable functions. -/
def measure.ae_eq_setoid (μ : measure α) : setoid { f : α → β // ae_strongly_measurable f μ } :=
⟨λ f g, (f : α → β) =ᵐ[μ] g, λ f, ae_eq_refl f, λ f g, ae_eq_symm, λ f g h, ae_eq_trans⟩

variable (α)

/-- The space of equivalence classes of almost everywhere strongly measurable functions, where two
    strongly measurable functions are equivalent if they agree almost everywhere, i.e.,
    they differ on a set of measure `0`.  -/
def ae_eq_fun (μ : measure α) : Type* := quotient (μ.ae_eq_setoid β)

variables {α β}

notation α ` →ₘ[`:25 μ `] ` β := ae_eq_fun α β μ

end measurable_space

namespace ae_eq_fun
variables [topological_space β] [topological_space γ] [topological_space δ]

/-- Construct the equivalence class `[f]` of an almost everywhere measurable function `f`, based
    on the equivalence relation of being almost everywhere equal. -/
def mk {β : Type*} [topological_space β]
  (f : α → β) (hf : ae_strongly_measurable f μ) : α →ₘ[μ] β := quotient.mk' ⟨f, hf⟩

/-- A measurable representative of an `ae_eq_fun` [f] -/
instance : has_coe_to_fun (α →ₘ[μ] β) (λ _, α → β) :=
⟨λ f, ae_strongly_measurable.mk _ (quotient.out' f : {f : α → β // ae_strongly_measurable f μ}).2⟩

protected lemma strongly_measurable (f : α →ₘ[μ] β) : strongly_measurable f :=
ae_strongly_measurable.strongly_measurable_mk _

protected lemma ae_strongly_measurable (f : α →ₘ[μ] β) : ae_strongly_measurable f μ :=
f.strongly_measurable.ae_strongly_measurable

protected lemma measurable [pseudo_metrizable_space β] [measurable_space β] [borel_space β]
  (f : α →ₘ[μ] β) : measurable f :=
ae_strongly_measurable.measurable_mk _

protected lemma ae_measurable [pseudo_metrizable_space β] [measurable_space β] [borel_space β]
  (f : α →ₘ[μ] β) :
  ae_measurable f μ :=
f.measurable.ae_measurable

@[simp] lemma quot_mk_eq_mk (f : α → β) (hf) :
  (quot.mk (@setoid.r _ $ μ.ae_eq_setoid β) ⟨f, hf⟩ : α →ₘ[μ] β) = mk f hf :=
rfl

@[simp] lemma mk_eq_mk {f g : α → β} {hf hg} :
  (mk f hf : α →ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
quotient.eq'

@[simp] lemma mk_coe_fn (f : α →ₘ[μ] β) : mk f f.ae_strongly_measurable = f :=
begin
  conv_rhs { rw ← quotient.out_eq' f },
  set g : {f : α → β // ae_strongly_measurable f μ} := quotient.out' f with hg,
  have : g = ⟨g.1, g.2⟩ := subtype.eq rfl,
  rw [this, ← mk, mk_eq_mk],
  exact (ae_strongly_measurable.ae_eq_mk _).symm,
end

@[ext] lemma ext {f g : α →ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g :=
by rwa [← f.mk_coe_fn, ← g.mk_coe_fn, mk_eq_mk]

lemma ext_iff {f g : α →ₘ[μ] β} : f = g ↔ f =ᵐ[μ] g :=
⟨λ h, by rw h, λ h, ext h⟩

lemma coe_fn_mk (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β) =ᵐ[μ] f :=
begin
  apply (ae_strongly_measurable.ae_eq_mk _).symm.trans,
  exact @quotient.mk_out' _ (μ.ae_eq_setoid β) (⟨f, hf⟩ : {f // ae_strongly_measurable f μ})
end

@[elab_as_eliminator]
lemma induction_on (f : α →ₘ[μ] β) {p : (α →ₘ[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
quotient.induction_on' f $ subtype.forall.2 H

@[elab_as_eliminator]
lemma induction_on₂ {α' β' : Type*} [measurable_space α'] [topological_space β']
  {μ' : measure α'}
  (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → Prop}
  (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) :
  p f f' :=
induction_on f $ λ f hf, induction_on f' $ H f hf

@[elab_as_eliminator]
lemma induction_on₃ {α' β' : Type*} [measurable_space α'] [topological_space β']
  {μ' : measure α'}
  {α'' β'' : Type*} [measurable_space α''] [topological_space β'']
  {μ'' : measure α''}
  (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') (f'' : α'' →ₘ[μ''] β'')
  {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → (α'' →ₘ[μ''] β'') → Prop}
  (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) :
  p f f' f'' :=
induction_on f $ λ f hf, induction_on₂ f' f'' $ H f hf

/-- Given a continuous function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. -/
def comp (g : β → γ) (hg : continuous g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
quotient.lift_on' f (λ f, mk (g ∘ (f : α → β)) (hg.comp_ae_strongly_measurable f.2)) $
  λ f f' H, mk_eq_mk.2 $ H.fun_comp g

@[simp] lemma comp_mk (g : β → γ) (hg : continuous g)
  (f : α → β) (hf) :
  comp g hg (mk f hf : α →ₘ[μ] β) = mk (g ∘ f) (hg.comp_ae_strongly_measurable hf) :=
rfl

lemma comp_eq_mk (g : β → γ) (hg : continuous g) (f : α →ₘ[μ] β) :
  comp g hg f = mk (g ∘ f) (hg.comp_ae_strongly_measurable f.ae_strongly_measurable) :=
by rw [← comp_mk g hg f f.ae_strongly_measurable, mk_coe_fn]

lemma coe_fn_comp (g : β → γ) (hg : continuous g) (f : α →ₘ[μ] β) :
  comp g hg f =ᵐ[μ] g ∘ f :=
by { rw [comp_eq_mk], apply coe_fn_mk }

section comp_measurable

variables [measurable_space β] [pseudo_metrizable_space β] [borel_space β]
  [measurable_space γ] [pseudo_metrizable_space γ] [opens_measurable_space γ]
  [second_countable_topology γ]

/-- Given a measurable function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. This requires that `γ` has a second countable topology. -/
def comp_measurable
  (g : β → γ) (hg : measurable g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
quotient.lift_on' f (λ f', mk (g ∘ (f' : α → β))
  (hg.comp_ae_measurable f'.2.ae_measurable).ae_strongly_measurable) $
  λ f f' H, mk_eq_mk.2 $ H.fun_comp g

@[simp] lemma comp_measurable_mk (g : β → γ) (hg : measurable g)
  (f : α → β) (hf : ae_strongly_measurable f μ) :
  comp_measurable g hg (mk f hf : α →ₘ[μ] β) =
    mk (g ∘ f) (hg.comp_ae_measurable hf.ae_measurable).ae_strongly_measurable :=
rfl

lemma comp_measurable_eq_mk (g : β → γ) (hg : measurable g) (f : α →ₘ[μ] β) :
  comp_measurable g hg f =
    mk (g ∘ f) (hg.comp_ae_measurable f.ae_measurable).ae_strongly_measurable :=
by rw [← comp_measurable_mk g hg f f.ae_strongly_measurable, mk_coe_fn]

lemma coe_fn_comp_measurable (g : β → γ) (hg : measurable g) (f : α →ₘ[μ] β) :
  comp_measurable g hg f =ᵐ[μ] g ∘ f :=
by { rw [comp_measurable_eq_mk], apply coe_fn_mk }

end comp_measurable

/-- The class of `x ↦ (f x, g x)`. -/
def pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : α →ₘ[μ] β × γ :=
quotient.lift_on₂' f g (λ f g, mk (λ x, (f.1 x, g.1 x)) (f.2.prod_mk g.2)) $
  λ f g f' g' Hf Hg, mk_eq_mk.2 $ Hf.prod_mk Hg

@[simp] lemma pair_mk_mk (f : α → β) (hf) (g : α → γ) (hg) :
  (mk f hf : α →ₘ[μ] β).pair (mk g hg) = mk (λ x, (f x, g x)) (hf.prod_mk hg) :=
rfl

lemma pair_eq_mk (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
  f.pair g = mk (λ x, (f x, g x)) (f.ae_strongly_measurable.prod_mk g.ae_strongly_measurable) :=
by simp only [← pair_mk_mk, mk_coe_fn]

lemma coe_fn_pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
  f.pair g =ᵐ[μ] (λ x, (f x, g x)) :=
by { rw pair_eq_mk, apply coe_fn_mk }

/-- Given a continuous function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `λ a, g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[λ a, g (f₁ a) (f₂ a)] : α →ₘ γ` -/
def comp₂ (g : β → γ → δ)
  (hg : continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) : α →ₘ[μ] δ :=
comp _ hg (f₁.pair f₂)

@[simp] lemma comp₂_mk_mk
  (g : β → γ → δ) (hg : continuous (uncurry g)) (f₁ : α → β) (f₂ : α → γ) (hf₁ hf₂) :
  comp₂ g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
    mk (λ a, g (f₁ a) (f₂ a)) (hg.comp_ae_strongly_measurable (hf₁.prod_mk hf₂)) :=
rfl

lemma comp₂_eq_pair
  (g : β → γ → δ) (hg : continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
rfl

lemma comp₂_eq_mk
  (g : β → γ → δ) (hg : continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  comp₂ g hg f₁ f₂ = mk (λ a, g (f₁ a) (f₂ a)) (hg.comp_ae_strongly_measurable
    (f₁.ae_strongly_measurable.prod_mk f₂.ae_strongly_measurable)) :=
by rw [comp₂_eq_pair, pair_eq_mk, comp_mk]; refl

lemma coe_fn_comp₂
  (g : β → γ → δ) (hg : continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  comp₂ g hg f₁ f₂ =ᵐ[μ] λ a, g (f₁ a) (f₂ a) :=
by { rw comp₂_eq_mk, apply coe_fn_mk }

section

variables
  [measurable_space β] [pseudo_metrizable_space β] [borel_space β] [second_countable_topology β]
  [measurable_space γ] [pseudo_metrizable_space γ] [borel_space γ] [second_countable_topology γ]
  [measurable_space δ] [pseudo_metrizable_space δ] [opens_measurable_space δ]
  [second_countable_topology δ]

/-- Given a measurable function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `λ a, g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[λ a, g (f₁ a) (f₂ a)] : α →ₘ γ`. This requires `δ` to have second-countable topology. -/
def comp₂_measurable (g : β → γ → δ)
  (hg : measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) : α →ₘ[μ] δ :=
comp_measurable _ hg (f₁.pair f₂)

@[simp] lemma comp₂_measurable_mk_mk
  (g : β → γ → δ) (hg : measurable (uncurry g)) (f₁ : α → β) (f₂ : α → γ) (hf₁ hf₂) :
  comp₂_measurable g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
  mk (λ a, g (f₁ a) (f₂ a))
    (hg.comp_ae_measurable (hf₁.ae_measurable.prod_mk hf₂.ae_measurable)).ae_strongly_measurable :=
rfl

lemma comp₂_measurable_eq_pair
  (g : β → γ → δ) (hg : measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  comp₂_measurable g hg f₁ f₂ = comp_measurable _ hg (f₁.pair f₂) :=
rfl

lemma comp₂_measurable_eq_mk
  (g : β → γ → δ) (hg : measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  comp₂_measurable g hg f₁ f₂ = mk (λ a, g (f₁ a) (f₂ a)) (hg.comp_ae_measurable
    (f₁.ae_measurable.prod_mk f₂.ae_measurable)).ae_strongly_measurable :=
by rw [comp₂_measurable_eq_pair, pair_eq_mk, comp_measurable_mk]; refl

lemma coe_fn_comp₂_measurable
  (g : β → γ → δ) (hg : measurable (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  comp₂_measurable g hg f₁ f₂ =ᵐ[μ] λ a, g (f₁ a) (f₂ a) :=
by { rw comp₂_measurable_eq_mk, apply coe_fn_mk }

end

/-- Interpret `f : α →ₘ[μ] β` as a germ at `μ.ae` forgetting that `f` is almost everywhere
    strongly measurable. -/
def to_germ (f : α →ₘ[μ] β) : germ μ.ae β :=
quotient.lift_on' f (λ f, ((f : α → β) : germ μ.ae β)) $ λ f g H, germ.coe_eq.2 H

@[simp] lemma mk_to_germ (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β).to_germ = f := rfl

lemma to_germ_eq (f : α →ₘ[μ] β) : f.to_germ = (f : α → β) :=
by rw [← mk_to_germ, mk_coe_fn]

lemma to_germ_injective : injective (to_germ : (α →ₘ[μ] β) → germ μ.ae β) :=
λ f g H, ext $ germ.coe_eq.1 $ by rwa [← to_germ_eq, ← to_germ_eq]

lemma comp_to_germ (g : β → γ) (hg : continuous g) (f : α →ₘ[μ] β) :
  (comp g hg f).to_germ = f.to_germ.map g :=
induction_on f $ λ f hf, by simp

lemma comp_measurable_to_germ [measurable_space β] [borel_space β] [pseudo_metrizable_space β]
  [pseudo_metrizable_space γ] [second_countable_topology γ] [measurable_space γ]
  [opens_measurable_space γ] (g : β → γ) (hg : measurable g) (f : α →ₘ[μ] β) :
  (comp_measurable g hg f).to_germ = f.to_germ.map g :=
induction_on f $ λ f hf, by simp

lemma comp₂_to_germ (g : β → γ → δ) (hg : continuous (uncurry g))
  (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  (comp₂ g hg f₁ f₂).to_germ = f₁.to_germ.map₂ g f₂.to_germ :=
induction_on₂ f₁ f₂ $ λ f₁ hf₁ f₂ hf₂, by simp

lemma comp₂_measurable_to_germ
  [pseudo_metrizable_space β] [second_countable_topology β] [measurable_space β] [borel_space β]
  [pseudo_metrizable_space γ] [second_countable_topology γ] [measurable_space γ] [borel_space γ]
  [pseudo_metrizable_space δ] [second_countable_topology δ] [measurable_space δ]
  [opens_measurable_space δ] (g : β → γ → δ) (hg : measurable (uncurry g))
  (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
  (comp₂_measurable g hg f₁ f₂).to_germ = f₁.to_germ.map₂ g f₂.to_germ :=
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

section lattice

section sup
variables [semilattice_sup β] [has_continuous_sup β]

instance : has_sup (α →ₘ[μ] β) :=
{ sup := λ f g, ae_eq_fun.comp₂ (⊔) continuous_sup f g }

lemma coe_fn_sup (f g : α →ₘ[μ] β) : ⇑(f ⊔ g) =ᵐ[μ] λ x, f x ⊔ g x :=
coe_fn_comp₂ _ _ _ _

protected lemma le_sup_left (f g : α →ₘ[μ] β) : f ≤ f ⊔ g :=
by { rw ← coe_fn_le, filter_upwards [coe_fn_sup f g] with _ ha, rw ha, exact le_sup_left, }

protected lemma le_sup_right (f g : α →ₘ[μ] β) : g ≤ f ⊔ g :=
by { rw ← coe_fn_le, filter_upwards [coe_fn_sup f g] with _ ha, rw ha, exact le_sup_right, }

protected lemma sup_le (f g f' : α →ₘ[μ] β) (hf : f ≤ f') (hg : g ≤ f') : f ⊔ g ≤ f' :=
begin
  rw ← coe_fn_le at hf hg ⊢,
  filter_upwards [hf, hg, coe_fn_sup f g] with _ haf hag ha_sup,
  rw ha_sup,
  exact sup_le haf hag,
end

end sup

section inf
variables [semilattice_inf β] [has_continuous_inf β]

instance : has_inf (α →ₘ[μ] β) :=
{ inf := λ f g, ae_eq_fun.comp₂ (⊓) continuous_inf f g }

lemma coe_fn_inf (f g : α →ₘ[μ] β) : ⇑(f ⊓ g) =ᵐ[μ] λ x, f x ⊓ g x :=
coe_fn_comp₂ _ _ _ _

protected lemma inf_le_left (f g : α →ₘ[μ] β) : f ⊓ g ≤ f :=
by { rw ← coe_fn_le, filter_upwards [coe_fn_inf f g] with _ ha, rw ha, exact inf_le_left, }

protected lemma inf_le_right (f g : α →ₘ[μ] β) : f ⊓ g ≤ g :=
by { rw ← coe_fn_le, filter_upwards [coe_fn_inf f g] with _ ha, rw ha, exact inf_le_right, }

protected lemma le_inf (f' f g : α →ₘ[μ] β) (hf : f' ≤ f) (hg : f' ≤ g) : f' ≤ f ⊓ g :=
begin
  rw ← coe_fn_le at hf hg ⊢,
  filter_upwards [hf, hg, coe_fn_inf f g] with _ haf hag ha_inf,
  rw ha_inf,
  exact le_inf haf hag,
end

end inf

instance [lattice β] [topological_lattice β] : lattice (α →ₘ[μ] β) :=
{ sup           := has_sup.sup,
  le_sup_left   := ae_eq_fun.le_sup_left,
  le_sup_right  := ae_eq_fun.le_sup_right,
  sup_le        := ae_eq_fun.sup_le,
  inf           := has_inf.inf,
  inf_le_left   := ae_eq_fun.inf_le_left,
  inf_le_right  := ae_eq_fun.inf_le_right,
  le_inf        := ae_eq_fun.le_inf,
  ..ae_eq_fun.partial_order}

end lattice

end order

variable (α)
/-- The equivalence class of a constant function: `[λ a:α, b]`, based on the equivalence relation of
    being almost everywhere equal -/
def const (b : β) : α →ₘ[μ] β := mk (λ a:α, b) ae_strongly_measurable_const

lemma coe_fn_const (b : β) : (const α b : α →ₘ[μ] β) =ᵐ[μ] function.const α b :=
coe_fn_mk _ _

variable {α}

instance [inhabited β] : inhabited (α →ₘ[μ] β) := ⟨const α default⟩

@[to_additive] instance [has_one β] : has_one (α →ₘ[μ] β) := ⟨const α 1⟩
@[to_additive] lemma one_def [has_one β] :
  (1 : α →ₘ[μ] β) = mk (λ a:α, 1) ae_strongly_measurable_const := rfl
@[to_additive] lemma coe_fn_one [has_one β] : ⇑(1 : α →ₘ[μ] β) =ᵐ[μ] 1 := coe_fn_const _ _
@[simp, to_additive] lemma one_to_germ [has_one β] : (1 : α →ₘ[μ] β).to_germ = 1 := rfl

-- Note we set up the scalar actions before the `monoid` structures in case we want to
-- try to override the `nsmul` or `zsmul` fields in future.
section has_smul

variables {𝕜 𝕜' : Type*}
variables [has_smul 𝕜 γ] [has_continuous_const_smul 𝕜 γ]
variables [has_smul 𝕜' γ] [has_continuous_const_smul 𝕜' γ]

instance : has_smul 𝕜 (α →ₘ[μ] γ) :=
⟨λ c f, comp ((•) c) (continuous_id.const_smul c) f⟩

@[simp] lemma smul_mk (c : 𝕜) (f : α → γ) (hf : ae_strongly_measurable f μ) :
  c • (mk f hf : α →ₘ[μ] γ) = mk (c • f) (hf.const_smul _) :=
rfl

lemma coe_fn_smul (c : 𝕜) (f : α →ₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • f := coe_fn_comp _ _ _

lemma smul_to_germ (c : 𝕜) (f : α →ₘ[μ] γ) : (c • f).to_germ = c • f.to_germ :=
comp_to_germ _ _ _

instance [smul_comm_class 𝕜 𝕜' γ] : smul_comm_class 𝕜 𝕜' (α →ₘ[μ] γ) :=
⟨λ a b f, induction_on f $ λ f hf, by simp_rw [smul_mk, smul_comm]⟩

instance [has_smul 𝕜 𝕜'] [is_scalar_tower 𝕜 𝕜' γ] : is_scalar_tower 𝕜 𝕜' (α →ₘ[μ] γ) :=
⟨λ a b f, induction_on f $ λ f hf, by simp_rw [smul_mk, smul_assoc]⟩

instance [has_smul 𝕜ᵐᵒᵖ γ] [is_central_scalar 𝕜 γ] : is_central_scalar 𝕜 (α →ₘ[μ] γ) :=
⟨λ a f, induction_on f $ λ f hf, by simp_rw [smul_mk, op_smul_eq_smul]⟩

end has_smul

section has_mul
variables [has_mul γ] [has_continuous_mul γ]

@[to_additive]
instance : has_mul (α →ₘ[μ] γ) := ⟨comp₂ (*) continuous_mul⟩

@[simp, to_additive] lemma mk_mul_mk (f g : α → γ) (hf : ae_strongly_measurable f μ)
  (hg : ae_strongly_measurable g μ) :
  (mk f hf : α →ₘ[μ] γ) * (mk g hg) = mk (f * g) (hf.mul hg) :=
rfl

@[to_additive] lemma coe_fn_mul (f g : α →ₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g := coe_fn_comp₂ _ _ _ _

@[simp, to_additive] lemma mul_to_germ (f g : α →ₘ[μ] γ) :
  (f * g).to_germ = f.to_germ * g.to_germ :=
comp₂_to_germ _ _ _ _

end has_mul

instance [add_monoid γ] [has_continuous_add γ] : add_monoid (α →ₘ[μ] γ) :=
to_germ_injective.add_monoid to_germ zero_to_germ add_to_germ (λ _ _, smul_to_germ _ _)

instance [add_comm_monoid γ] [has_continuous_add γ] : add_comm_monoid (α →ₘ[μ] γ) :=
to_germ_injective.add_comm_monoid to_germ zero_to_germ add_to_germ (λ _ _, smul_to_germ _ _)

section monoid
variables [monoid γ] [has_continuous_mul γ]

instance : has_pow (α →ₘ[μ] γ) ℕ := ⟨λ f n, comp _ (continuous_pow n) f⟩

@[simp] lemma mk_pow (f : α → γ) (hf) (n : ℕ) :
  (mk f hf : α →ₘ[μ] γ) ^ n =
    mk (f ^ n) ((_root_.continuous_pow n).comp_ae_strongly_measurable hf) :=
rfl

lemma coe_fn_pow (f : α →ₘ[μ] γ) (n : ℕ) : ⇑(f ^ n) =ᵐ[μ] f ^ n :=
coe_fn_comp _ _ _

@[simp] lemma pow_to_germ (f : α →ₘ[μ] γ) (n : ℕ) :
  (f ^ n).to_germ = f.to_germ ^ n :=
comp_to_germ _ _ _

@[to_additive]
instance : monoid (α →ₘ[μ] γ) :=
to_germ_injective.monoid to_germ one_to_germ mul_to_germ pow_to_germ

/-- `ae_eq_fun.to_germ` as a `monoid_hom`. -/
@[to_additive "`ae_eq_fun.to_germ` as an `add_monoid_hom`.", simps]
def to_germ_monoid_hom : (α →ₘ[μ] γ) →* μ.ae.germ γ :=
{ to_fun := to_germ,
  map_one' := one_to_germ,
  map_mul' := mul_to_germ }

end monoid

@[to_additive]
instance [comm_monoid γ] [has_continuous_mul γ] : comm_monoid (α →ₘ[μ] γ) :=
to_germ_injective.comm_monoid to_germ one_to_germ mul_to_germ pow_to_germ

section group
variables [group γ] [topological_group γ]

section inv

@[to_additive] instance : has_inv (α →ₘ[μ] γ) := ⟨comp has_inv.inv continuous_inv⟩

@[simp, to_additive] lemma inv_mk (f : α → γ) (hf) : (mk f hf : α →ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv := rfl

@[to_additive] lemma coe_fn_inv (f : α →ₘ[μ] γ) : ⇑(f⁻¹) =ᵐ[μ] f⁻¹ := coe_fn_comp _ _ _

@[to_additive] lemma inv_to_germ (f : α →ₘ[μ] γ) : (f⁻¹).to_germ = f.to_germ⁻¹ := comp_to_germ _ _ _

end inv

section div

@[to_additive] instance : has_div (α →ₘ[μ] γ) := ⟨comp₂ has_div.div continuous_div'⟩

@[simp, to_additive] lemma mk_div (f g : α → γ)
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  mk (f / g) (hf.div hg) = (mk f hf : α →ₘ[μ] γ) / (mk g hg) :=
rfl

@[to_additive] lemma coe_fn_div (f g : α →ₘ[μ] γ) : ⇑(f / g) =ᵐ[μ] f / g := coe_fn_comp₂ _ _ _ _

@[to_additive] lemma div_to_germ (f g : α →ₘ[μ] γ) : (f / g).to_germ = f.to_germ / g.to_germ :=
comp₂_to_germ _ _ _ _

end div

section zpow

instance has_int_pow : has_pow (α →ₘ[μ] γ) ℤ :=
⟨λ f n, comp _ (continuous_zpow n) f⟩

@[simp] lemma mk_zpow (f : α → γ) (hf) (n : ℤ) :
  (mk f hf : α →ₘ[μ] γ) ^ n = mk (f ^ n) ((continuous_zpow n).comp_ae_strongly_measurable hf) :=
rfl

lemma coe_fn_zpow (f : α →ₘ[μ] γ) (n : ℤ) : ⇑(f ^ n) =ᵐ[μ] f ^ n :=
coe_fn_comp _ _ _

@[simp] lemma zpow_to_germ (f : α →ₘ[μ] γ) (n : ℤ) :
  (f ^ n).to_germ = f.to_germ ^ n :=
comp_to_germ _ _ _

end zpow

end group

instance [add_group γ] [topological_add_group γ] :
  add_group (α →ₘ[μ] γ) :=
to_germ_injective.add_group to_germ zero_to_germ add_to_germ neg_to_germ sub_to_germ
  (λ _ _, smul_to_germ _ _) (λ _ _, smul_to_germ _ _)

instance [add_comm_group γ] [topological_add_group γ] :
  add_comm_group (α →ₘ[μ] γ) :=
to_germ_injective.add_comm_group to_germ zero_to_germ add_to_germ neg_to_germ sub_to_germ
  (λ _ _, smul_to_germ _ _) (λ _ _, smul_to_germ _ _)

@[to_additive]
instance [group γ] [topological_group γ] : group (α →ₘ[μ] γ) :=
to_germ_injective.group _ one_to_germ mul_to_germ inv_to_germ div_to_germ pow_to_germ zpow_to_germ

@[to_additive]
instance [comm_group γ] [topological_group γ] : comm_group (α →ₘ[μ] γ) :=
to_germ_injective.comm_group _
  one_to_germ mul_to_germ inv_to_germ div_to_germ pow_to_germ zpow_to_germ

section module

variables {𝕜 : Type*}

instance [monoid 𝕜] [mul_action 𝕜 γ] [has_continuous_const_smul 𝕜 γ] :
  mul_action 𝕜 (α →ₘ[μ] γ) :=
to_germ_injective.mul_action to_germ smul_to_germ

instance [monoid 𝕜] [add_monoid γ] [has_continuous_add γ]
  [distrib_mul_action 𝕜 γ] [has_continuous_const_smul 𝕜 γ] :
  distrib_mul_action 𝕜 (α →ₘ[μ] γ) :=
to_germ_injective.distrib_mul_action (to_germ_add_monoid_hom : (α →ₘ[μ] γ) →+ _)
  (λ c : 𝕜, smul_to_germ c)

instance [semiring 𝕜] [add_comm_monoid γ] [has_continuous_add γ] [module 𝕜 γ]
  [has_continuous_const_smul 𝕜 γ] :
  module 𝕜 (α →ₘ[μ] γ) :=
to_germ_injective.module 𝕜 (to_germ_add_monoid_hom : (α →ₘ[μ] γ) →+ _) smul_to_germ

end module

open ennreal

/-- For `f : α → ℝ≥0∞`, define `∫ [f]` to be `∫ f` -/
def lintegral (f : α →ₘ[μ] ℝ≥0∞) : ℝ≥0∞ :=
quotient.lift_on' f (λ f, ∫⁻ a, (f : α → ℝ≥0∞) a ∂μ) (assume f g, lintegral_congr_ae)

@[simp] lemma lintegral_mk (f : α → ℝ≥0∞) (hf) :
  (mk f hf : α →ₘ[μ] ℝ≥0∞).lintegral = ∫⁻ a, f a ∂μ := rfl

lemma lintegral_coe_fn (f : α →ₘ[μ] ℝ≥0∞) : ∫⁻ a, f a ∂μ = f.lintegral :=
by rw [← lintegral_mk, mk_coe_fn]

@[simp] lemma lintegral_zero : lintegral (0 : α →ₘ[μ] ℝ≥0∞) = 0 := lintegral_zero

@[simp] lemma lintegral_eq_zero_iff {f : α →ₘ[μ] ℝ≥0∞} : lintegral f = 0 ↔ f = 0 :=
induction_on f $ λ f hf, (lintegral_eq_zero_iff' hf.ae_measurable).trans mk_eq_mk.symm

lemma lintegral_add (f g : α →ₘ[μ] ℝ≥0∞) : lintegral (f + g) = lintegral f + lintegral g :=
induction_on₂ f g $ λ f hf g hg, by simp [lintegral_add_left' hf.ae_measurable]

lemma lintegral_mono {f g : α →ₘ[μ] ℝ≥0∞} : f ≤ g → lintegral f ≤ lintegral g :=
induction_on₂ f g $ λ f hf g hg hfg, lintegral_mono_ae hfg

section abs

lemma coe_fn_abs {β} [topological_space β] [lattice β] [topological_lattice β]
  [add_group β] [topological_add_group β]
  (f : α →ₘ[μ] β) :
  ⇑|f| =ᵐ[μ] λ x, |f x| :=
begin
  simp_rw abs_eq_sup_neg,
  filter_upwards [ae_eq_fun.coe_fn_sup f (-f), ae_eq_fun.coe_fn_neg f] with x hx_sup hx_neg,
  rw [hx_sup, hx_neg, pi.neg_apply],
end

end abs

section pos_part

variables [linear_order γ] [order_closed_topology γ] [has_zero γ]

/-- Positive part of an `ae_eq_fun`. -/
def pos_part (f : α →ₘ[μ] γ) : α →ₘ[μ] γ :=
comp (λ x, max x 0) (continuous_id.max continuous_const) f

@[simp] lemma pos_part_mk (f : α → γ) (hf) :
  pos_part (mk f hf : α →ₘ[μ] γ) =
    mk (λ x, max (f x) 0) ((continuous_id.max continuous_const).comp_ae_strongly_measurable hf) :=
rfl

lemma coe_fn_pos_part (f : α →ₘ[μ] γ) : ⇑(pos_part f) =ᵐ[μ] (λ a, max (f a) 0) :=
coe_fn_comp _ _ _

end pos_part

end ae_eq_fun

end measure_theory

namespace continuous_map

open measure_theory

variables [topological_space α] [borel_space α] (μ)
variables [topological_space β] [second_countable_topology_either α β] [pseudo_metrizable_space β]

/-- The equivalence class of `μ`-almost-everywhere measurable functions associated to a continuous
map. -/
def to_ae_eq_fun (f : C(α, β)) : α →ₘ[μ] β :=
ae_eq_fun.mk f f.continuous.ae_strongly_measurable

lemma coe_fn_to_ae_eq_fun (f : C(α, β)) : f.to_ae_eq_fun μ =ᵐ[μ] f :=
ae_eq_fun.coe_fn_mk f _

variables [group β] [topological_group β]

/-- The `mul_hom` from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
@[to_additive "The `add_hom` from the group of continuous maps from `α` to `β` to the group of
equivalence classes of `μ`-almost-everywhere measurable functions."]
def to_ae_eq_fun_mul_hom : C(α, β) →* α →ₘ[μ] β :=
{ to_fun := continuous_map.to_ae_eq_fun μ,
  map_one' := rfl,
  map_mul' := λ f g, ae_eq_fun.mk_mul_mk _ _
    f.continuous.ae_strongly_measurable g.continuous.ae_strongly_measurable }

variables {𝕜 : Type*} [semiring 𝕜]
variables [topological_space γ] [pseudo_metrizable_space γ] [add_comm_group γ]
  [module 𝕜 γ] [topological_add_group γ] [has_continuous_const_smul 𝕜 γ]
  [second_countable_topology_either α γ]

/-- The linear map from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
def to_ae_eq_fun_linear_map : C(α, γ) →ₗ[𝕜] α →ₘ[μ] γ :=
{ map_smul' := λ c f, ae_eq_fun.smul_mk c f f.continuous.ae_strongly_measurable,
  .. to_ae_eq_fun_add_hom μ }

end continuous_map

-- Guard against import creep
assert_not_exists inner_product_space
