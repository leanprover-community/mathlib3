/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import measure_theory.constructions.borel_space
import algebra.indicator_function
import algebra.support

/-!
# Simple functions

A function `f` from a measurable space to any type is called *simple*, if every preimage `f ⁻¹' {x}`
is measurable, and the range is finite. In this file, we define simple functions and establish their
basic properties; and we construct a sequence of simple functions approximating an arbitrary Borel
measurable function `f : α → ℝ≥0∞`.

The theorem `measurable.ennreal_induction` shows that in order to prove something for an arbitrary
measurable function into `ℝ≥0∞`, it is sufficient to show that the property holds for (multiples of)
characteristic functions and is closed under addition and supremum of increasing sequences of
functions.
-/
noncomputable theory
open set (hiding restrict restrict_apply) filter ennreal function (support)
open_locale classical topology big_operators nnreal ennreal measure_theory

namespace measure_theory

variables {α β γ δ : Type*}

/-- A function `f` from a measurable space to any type is called *simple*,
if every preimage `f ⁻¹' {x}` is measurable, and the range is finite. This structure bundles
a function with these properties. -/
structure {u v} simple_func (α : Type u) [measurable_space α] (β : Type v) :=
(to_fun : α → β)
(measurable_set_fiber' : ∀ x, measurable_set (to_fun ⁻¹' {x}))
(finite_range' : (set.range to_fun).finite)

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

section measurable
variables [measurable_space α]
instance has_coe_to_fun : has_coe_to_fun (α →ₛ β) (λ _, α → β) := ⟨to_fun⟩

lemma coe_injective ⦃f g : α →ₛ β⦄ (H : (f : α → β) = g) : f = g :=
by cases f; cases g; congr; exact H

@[ext] theorem ext {f g : α →ₛ β} (H : ∀ a, f a = g a) : f = g :=
coe_injective $ funext H

lemma finite_range (f : α →ₛ β) : (set.range f).finite := f.finite_range'

lemma measurable_set_fiber (f : α →ₛ β) (x : β) : measurable_set (f ⁻¹' {x}) :=
f.measurable_set_fiber' x

@[simp] lemma apply_mk (f : α → β) (h h') (x : α) : simple_func.mk f h h' x = f x := rfl

/-- Simple function defined on the empty type. -/
def of_is_empty [is_empty α] : α →ₛ β :=
{ to_fun := is_empty_elim,
  measurable_set_fiber' := λ x, subsingleton.measurable_set,
  finite_range' := by simp [range_eq_empty] }

/-- Range of a simple function `α →ₛ β` as a `finset β`. -/
protected def range (f : α →ₛ β) : finset β := f.finite_range.to_finset

@[simp] theorem mem_range {f : α →ₛ β} {b} : b ∈ f.range ↔ b ∈ range f :=
finite.mem_to_finset _

theorem mem_range_self (f : α →ₛ β) (x : α) : f x ∈ f.range := mem_range.2 ⟨x, rfl⟩

@[simp] lemma coe_range (f : α →ₛ β) : (↑f.range : set β) = set.range f :=
f.finite_range.coe_to_finset

theorem mem_range_of_measure_ne_zero {f : α →ₛ β} {x : β} {μ : measure α} (H : μ (f ⁻¹' {x}) ≠ 0) :
  x ∈ f.range :=
let ⟨a, ha⟩ := nonempty_of_measure_ne_zero H in
mem_range.2 ⟨a, ha⟩

lemma forall_range_iff {f : α →ₛ β} {p : β → Prop} :
  (∀ y ∈ f.range, p y) ↔ ∀ x, p (f x) :=
by simp only [mem_range, set.forall_range_iff]

lemma exists_range_iff {f : α →ₛ β} {p : β → Prop} :
  (∃ y ∈ f.range, p y) ↔ ∃ x, p (f x) :=
by simpa only [mem_range, exists_prop] using set.exists_range_iff

lemma preimage_eq_empty_iff (f : α →ₛ β) (b : β) : f ⁻¹' {b} = ∅ ↔ b ∉ f.range :=
preimage_singleton_eq_empty.trans $ not_congr mem_range.symm

lemma exists_forall_le [nonempty β] [preorder β] [is_directed β (≤)] (f : α →ₛ β) :
  ∃ C, ∀ x, f x ≤ C :=
f.range.exists_le.imp $ λ C, forall_range_iff.1

/-- Constant function as a `simple_func`. -/
def const (α) {β} [measurable_space α] (b : β) : α →ₛ β :=
⟨λ a, b, λ x, measurable_set.const _, finite_range_const⟩

instance [inhabited β] : inhabited (α →ₛ β) := ⟨const _ default⟩

theorem const_apply (a : α) (b : β) : (const α b) a = b := rfl

@[simp] theorem coe_const (b : β) : ⇑(const α b) = function.const α b := rfl

@[simp] lemma range_const (α) [measurable_space α] [nonempty α] (b : β) :
  (const α b).range = {b} :=
finset.coe_injective $ by simp

lemma range_const_subset (α) [measurable_space α] (b : β) :
  (const α b).range ⊆ {b} :=
finset.coe_subset.1 $ by simp

lemma simple_func_bot {α} (f : @simple_func α ⊥ β) [nonempty β] : ∃ c, ∀ x, f x = c :=
begin
  have hf_meas := @simple_func.measurable_set_fiber α _ ⊥ f,
  simp_rw measurable_space.measurable_set_bot_iff at hf_meas,
  casesI is_empty_or_nonempty α,
  { simp only [is_empty.forall_iff, exists_const], },
  { specialize hf_meas (f h.some),
    cases hf_meas,
    { exfalso,
      refine set.not_mem_empty h.some _,
      rw [← hf_meas, set.mem_preimage],
      exact set.mem_singleton _, },
    { refine ⟨f h.some, λ x, _⟩,
      have : x ∈ f ⁻¹' {f h.some},
      { rw hf_meas, exact set.mem_univ x, },
      rwa [set.mem_preimage, set.mem_singleton_iff] at this, }, },
end

lemma simple_func_bot' {α} [nonempty β] (f : @simple_func α ⊥ β) :
  ∃ c, f = @simple_func.const α _ ⊥ c :=
begin
  obtain ⟨c, h_eq⟩ := simple_func_bot f,
  refine ⟨c, _⟩,
  ext1 x,
  rw [h_eq x, simple_func.coe_const],
end

lemma measurable_set_cut (r : α → β → Prop) (f : α →ₛ β)
  (h : ∀b, measurable_set {a | r a b}) : measurable_set {a | r a (f a)} :=
begin
  have : {a | r a (f a)} = ⋃ b ∈ range f, {a | r a b} ∩ f ⁻¹' {b},
  { ext a,
    suffices : r a (f a) ↔ ∃ i, r a (f i) ∧ f a = f i, by simpa,
    exact ⟨λ h, ⟨a, ⟨h, rfl⟩⟩, λ ⟨a', ⟨h', e⟩⟩, e.symm ▸ h'⟩ },
  rw this,
  exact measurable_set.bUnion f.finite_range.countable
    (λ b _, measurable_set.inter (h b) (f.measurable_set_fiber _))
end

@[measurability]
theorem measurable_set_preimage (f : α →ₛ β) (s) : measurable_set (f ⁻¹' s) :=
measurable_set_cut (λ _ b, b ∈ s) f (λ b, measurable_set.const (b ∈ s))

/-- A simple function is measurable -/
@[measurability]
protected theorem measurable [measurable_space β] (f : α →ₛ β) : measurable f :=
λ s _, measurable_set_preimage f s

@[measurability]
protected theorem ae_measurable [measurable_space β] {μ : measure α} (f : α →ₛ β) :
  ae_measurable f μ :=
f.measurable.ae_measurable

protected lemma sum_measure_preimage_singleton (f : α →ₛ β) {μ : measure α} (s : finset β) :
  ∑ y in s, μ (f ⁻¹' {y}) = μ (f ⁻¹' ↑s) :=
sum_measure_preimage_singleton _ (λ _ _, f.measurable_set_fiber _)

lemma sum_range_measure_preimage_singleton (f : α →ₛ β) (μ : measure α) :
  ∑ y in f.range, μ (f ⁻¹' {y}) = μ univ :=
by rw [f.sum_measure_preimage_singleton, coe_range, preimage_range]

/-- If-then-else as a `simple_func`. -/
def piecewise (s : set α) (hs : measurable_set s) (f g : α →ₛ β) : α →ₛ β :=
⟨s.piecewise f g,
 λ x, by letI : measurable_space β := ⊤; exact
   f.measurable.piecewise hs g.measurable trivial,
 (f.finite_range.union g.finite_range).subset range_ite_subset⟩

@[simp] theorem coe_piecewise {s : set α} (hs : measurable_set s) (f g : α →ₛ β) :
  ⇑(piecewise s hs f g) = s.piecewise f g :=
rfl

theorem piecewise_apply {s : set α} (hs : measurable_set s) (f g : α →ₛ β) (a) :
  piecewise s hs f g a = if a ∈ s then f a else g a :=
rfl

@[simp] lemma piecewise_compl {s : set α} (hs : measurable_set sᶜ) (f g : α →ₛ β) :
  piecewise sᶜ hs f g = piecewise s hs.of_compl g f :=
coe_injective $ by simp [hs]

@[simp] lemma piecewise_univ (f g : α →ₛ β) : piecewise univ measurable_set.univ f g = f :=
coe_injective $ by simp

@[simp] lemma piecewise_empty (f g : α →ₛ β) : piecewise ∅ measurable_set.empty f g = g :=
coe_injective $ by simp

lemma support_indicator [has_zero β] {s : set α} (hs : measurable_set s) (f : α →ₛ β) :
  function.support (f.piecewise s hs (simple_func.const α 0)) = s ∩ function.support f :=
set.support_indicator

lemma range_indicator {s : set α} (hs : measurable_set s)
  (hs_nonempty : s.nonempty) (hs_ne_univ : s ≠ univ) (x y : β) :
  (piecewise s hs (const α x) (const α y)).range = {x, y} :=
by simp only [← finset.coe_inj, coe_range, coe_piecewise, range_piecewise, coe_const,
  finset.coe_insert, finset.coe_singleton, hs_nonempty.image_const,
  (nonempty_compl.2 hs_ne_univ).image_const, singleton_union]

lemma measurable_bind [measurable_space γ] (f : α →ₛ β) (g : β → α → γ)
  (hg : ∀ b, measurable (g b)) : measurable (λ a, g (f a) a) :=
λ s hs, f.measurable_set_cut (λ a b, g b a ∈ s) $ λ b, hg b hs

/-- If `f : α →ₛ β` is a simple function and `g : β → α →ₛ γ` is a family of simple functions,
then `f.bind g` binds the first argument of `g` to `f`. In other words, `f.bind g a = g (f a) a`. -/
def bind (f : α →ₛ β) (g : β → α →ₛ γ) : α →ₛ γ :=
⟨λa, g (f a) a,
 λ c, f.measurable_set_cut (λ a b, g b a = c) $ λ b, (g b).measurable_set_preimage {c},
 (f.finite_range.bUnion (λ b _, (g b).finite_range)).subset $
 by rintro _ ⟨a, rfl⟩; simp; exact ⟨a, a, rfl⟩⟩

@[simp] theorem bind_apply (f : α →ₛ β) (g : β → α →ₛ γ) (a) :
  f.bind g a = g (f a) a := rfl

/-- Given a function `g : β → γ` and a simple function `f : α →ₛ β`, `f.map g` return the simple
    function `g ∘ f : α →ₛ γ` -/
def map (g : β → γ) (f : α →ₛ β) : α →ₛ γ := bind f (const α ∘ g)

theorem map_apply (g : β → γ) (f : α →ₛ β) (a) : f.map g a = g (f a) := rfl

theorem map_map (g : β → γ) (h: γ → δ) (f : α →ₛ β) : (f.map g).map h = f.map (h ∘ g) := rfl

@[simp] theorem coe_map (g : β → γ) (f : α →ₛ β) : (f.map g : α → γ) = g ∘ f := rfl

@[simp] theorem range_map [decidable_eq γ] (g : β → γ) (f : α →ₛ β) :
  (f.map g).range = f.range.image g :=
finset.coe_injective $ by simp only [coe_range, coe_map, finset.coe_image, range_comp]

@[simp] theorem map_const (g : β → γ) (b : β) : (const α b).map g = const α (g b) := rfl

lemma map_preimage (f : α →ₛ β) (g : β → γ) (s : set γ) :
  (f.map g) ⁻¹' s = f ⁻¹' ↑(f.range.filter (λb, g b ∈ s)) :=
by { simp only [coe_range, sep_mem_eq, set.mem_range, function.comp_app, coe_map, finset.coe_filter,
  ← mem_preimage, inter_comm, preimage_inter_range], apply preimage_comp }

lemma map_preimage_singleton (f : α →ₛ β) (g : β → γ) (c : γ) :
  (f.map g) ⁻¹' {c} = f ⁻¹' ↑(f.range.filter (λ b, g b = c)) :=
map_preimage _ _ _

/-- Composition of a `simple_fun` and a measurable function is a `simple_func`. -/
def comp [measurable_space β] (f : β →ₛ γ) (g : α → β) (hgm : measurable g) : α →ₛ γ :=
{ to_fun := f ∘ g,
  finite_range' := f.finite_range.subset $ set.range_comp_subset_range _ _,
  measurable_set_fiber' := λ z, hgm (f.measurable_set_fiber z) }

@[simp] lemma coe_comp [measurable_space β] (f : β →ₛ γ) {g : α → β} (hgm : measurable g) :
  ⇑(f.comp g hgm) = f ∘ g :=
rfl

lemma range_comp_subset_range [measurable_space β] (f : β →ₛ γ) {g : α → β} (hgm : measurable g) :
  (f.comp g hgm).range ⊆ f.range :=
finset.coe_subset.1 $ by simp only [coe_range, coe_comp, set.range_comp_subset_range]

/-- Extend a `simple_func` along a measurable embedding: `f₁.extend g hg f₂` is the function
`F : β →ₛ γ` such that `F ∘ g = f₁` and `F y = f₂ y` whenever `y ∉ range g`. -/
def extend [measurable_space β] (f₁ : α →ₛ γ) (g : α → β)
  (hg : measurable_embedding g) (f₂ : β →ₛ γ) : β →ₛ γ :=
{ to_fun := function.extend g f₁ f₂,
  finite_range' := (f₁.finite_range.union $ f₂.finite_range.subset
    (image_subset_range _ _)).subset (range_extend_subset _ _ _),
  measurable_set_fiber' :=
    begin
      letI : measurable_space γ := ⊤, haveI : measurable_singleton_class γ := ⟨λ _, trivial⟩,
      exact λ x, hg.measurable_extend f₁.measurable f₂.measurable (measurable_set_singleton _)
    end }

@[simp] lemma extend_apply [measurable_space β] (f₁ : α →ₛ γ) {g : α → β}
  (hg : measurable_embedding g) (f₂ : β →ₛ γ) (x : α) : (f₁.extend g hg f₂) (g x) = f₁ x :=
hg.injective.extend_apply _ _ _

@[simp] lemma extend_apply' [measurable_space β] (f₁ : α →ₛ γ) {g : α → β}
  (hg : measurable_embedding g) (f₂ : β →ₛ γ) {y : β} (h : ¬∃ x, g x = y) :
  (f₁.extend g hg f₂) y = f₂ y :=
function.extend_apply' _ _ _ h

@[simp] lemma extend_comp_eq' [measurable_space β] (f₁ : α →ₛ γ) {g : α → β}
  (hg : measurable_embedding g) (f₂ : β →ₛ γ) : (f₁.extend g hg f₂) ∘ g = f₁ :=
funext $ λ x, extend_apply _ _ _ _

@[simp] lemma extend_comp_eq [measurable_space β] (f₁ : α →ₛ γ) {g : α → β}
  (hg : measurable_embedding g) (f₂ : β →ₛ γ) : (f₁.extend g hg f₂).comp g hg.measurable = f₁ :=
coe_injective $ extend_comp_eq' _ _ _

/-- If `f` is a simple function taking values in `β → γ` and `g` is another simple function
with the same domain and codomain `β`, then `f.seq g = f a (g a)`. -/
def seq (f : α →ₛ (β → γ)) (g : α →ₛ β) : α →ₛ γ := f.bind (λf, g.map f)

@[simp] lemma seq_apply (f : α →ₛ (β → γ)) (g : α →ₛ β) (a : α) : f.seq g a = f a (g a) := rfl

/-- Combine two simple functions `f : α →ₛ β` and `g : α →ₛ β`
into `λ a, (f a, g a)`. -/
def pair (f : α →ₛ β) (g : α →ₛ γ) : α →ₛ (β × γ) := (f.map prod.mk).seq g

@[simp] lemma pair_apply (f : α →ₛ β) (g : α →ₛ γ) (a) : pair f g a = (f a, g a) := rfl

lemma pair_preimage (f : α →ₛ β) (g : α →ₛ γ) (s : set β) (t : set γ) :
  pair f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ∩ (g ⁻¹' t) := rfl

/- A special form of `pair_preimage` -/
lemma pair_preimage_singleton (f : α →ₛ β) (g : α →ₛ γ) (b : β) (c : γ) :
  (pair f g) ⁻¹' {(b, c)} = (f ⁻¹' {b}) ∩ (g ⁻¹' {c}) :=
by { rw ← singleton_prod_singleton, exact pair_preimage _ _ _ _ }

theorem bind_const (f : α →ₛ β) : f.bind (const α) = f := by ext; simp

@[to_additive] instance [has_one β] : has_one (α →ₛ β) := ⟨const α 1⟩
@[to_additive] instance [has_mul β] : has_mul (α →ₛ β) := ⟨λf g, (f.map (*)).seq g⟩
@[to_additive] instance [has_div β] : has_div (α →ₛ β) := ⟨λf g, (f.map (/)).seq g⟩
@[to_additive] instance [has_inv β] : has_inv (α →ₛ β) := ⟨λf, f.map (has_inv.inv)⟩
instance [has_sup β] : has_sup (α →ₛ β) := ⟨λf g, (f.map (⊔)).seq g⟩
instance [has_inf β] : has_inf (α →ₛ β) := ⟨λf g, (f.map (⊓)).seq g⟩
instance [has_le β] : has_le (α →ₛ β) := ⟨λf g, ∀a, f a ≤ g a⟩

@[simp, to_additive] lemma const_one [has_one β] : const α (1 : β) = 1 := rfl

@[simp, norm_cast, to_additive] lemma coe_one [has_one β] : ⇑(1 : α →ₛ β) = 1 := rfl
@[simp, norm_cast, to_additive] lemma coe_mul [has_mul β] (f g : α →ₛ β) : ⇑(f * g) = f * g := rfl
@[simp, norm_cast, to_additive] lemma coe_inv [has_inv β] (f : α →ₛ β) : ⇑(f⁻¹) = f⁻¹ := rfl
@[simp, norm_cast, to_additive] lemma coe_div [has_div β] (f g : α →ₛ β) : ⇑(f / g) = f / g := rfl
@[simp, norm_cast] lemma coe_le [preorder β] {f g : α →ₛ β} : (f : α → β) ≤ g ↔ f ≤ g := iff.rfl
@[simp, norm_cast] lemma coe_sup [has_sup β] (f g : α →ₛ β) : ⇑(f ⊔ g) = f ⊔ g := rfl
@[simp, norm_cast] lemma coe_inf [has_inf β] (f g : α →ₛ β) : ⇑(f ⊓ g) = f ⊓ g := rfl

@[to_additive] lemma mul_apply [has_mul β] (f g : α →ₛ β) (a : α) : (f * g) a = f a * g a := rfl
@[to_additive] lemma div_apply [has_div β] (f g : α →ₛ β) (x : α) : (f / g) x = f x / g x := rfl
@[to_additive] lemma inv_apply [has_inv β] (f : α →ₛ β) (x : α) : f⁻¹ x = (f x)⁻¹ := rfl
lemma sup_apply [has_sup β] (f g : α →ₛ β) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl
lemma inf_apply [has_inf β] (f g : α →ₛ β) (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl

@[simp, to_additive] lemma range_one [nonempty α] [has_one β] : (1 : α →ₛ β).range = {1} :=
finset.ext $ λ x, by simp [eq_comm]

@[simp] lemma range_eq_empty_of_is_empty {β} [hα : is_empty α] (f : α →ₛ β) :
  f.range = ∅ :=
begin
  rw ← finset.not_nonempty_iff_eq_empty,
  by_contra,
  obtain ⟨y, hy_mem⟩ := h,
  rw [simple_func.mem_range, set.mem_range] at hy_mem,
  obtain ⟨x, hxy⟩ := hy_mem,
  rw is_empty_iff at hα,
  exact hα x,
end

lemma eq_zero_of_mem_range_zero [has_zero β] : ∀ {y : β}, y ∈ (0 : α →ₛ β).range → y = 0 :=
forall_range_iff.2 $ λ x, rfl

@[to_additive]
lemma mul_eq_map₂ [has_mul β] (f g : α →ₛ β) : f * g = (pair f g).map (λp:β×β, p.1 * p.2) := rfl

lemma sup_eq_map₂ [has_sup β] (f g : α →ₛ β) : f ⊔ g = (pair f g).map (λp:β×β, p.1 ⊔ p.2) := rfl

@[to_additive]
lemma const_mul_eq_map [has_mul β] (f : α →ₛ β) (b : β) : const α b * f = f.map (λa, b * a) := rfl

@[to_additive]
theorem map_mul [has_mul β] [has_mul γ] {g : β → γ}
  (hg : ∀ x y, g (x * y) = g x * g y) (f₁ f₂ : α →ₛ β) : (f₁ * f₂).map g = f₁.map g * f₂.map g :=
ext $ λ x, hg _ _

variables {K : Type*}

instance [has_smul K β] : has_smul K (α →ₛ β) := ⟨λ k f, f.map ((•) k)⟩
@[simp] lemma coe_smul [has_smul K β] (c : K) (f : α →ₛ β) : ⇑(c • f) = c • f := rfl
lemma smul_apply [has_smul K β] (k : K) (f : α →ₛ β) (a : α) : (k • f) a = k • f a := rfl

instance has_nat_pow [monoid β] : has_pow (α →ₛ β) ℕ := ⟨λ f n, f.map (^ n)⟩
@[simp] lemma coe_pow [monoid β] (f : α →ₛ β) (n : ℕ) : ⇑(f ^ n) = f ^ n := rfl
lemma pow_apply [monoid β] (n : ℕ) (f : α →ₛ β) (a : α) : (f ^ n) a = f a ^ n := rfl

instance has_int_pow [div_inv_monoid β] : has_pow (α →ₛ β) ℤ := ⟨λ f n, f.map (^ n)⟩
@[simp] lemma coe_zpow [div_inv_monoid β] (f : α →ₛ β) (z : ℤ) : ⇑(f ^ z) = f ^ z := rfl
lemma zpow_apply [div_inv_monoid β] (z : ℤ) (f : α →ₛ β) (a : α) : (f ^ z) a = f a ^ z := rfl

-- TODO: work out how to generate these instances with `to_additive`, which gets confused by the
-- argument order swap between `coe_smul` and `coe_pow`.
section additive

instance [add_monoid β] : add_monoid (α →ₛ β) :=
function.injective.add_monoid (λ f, show α → β, from f) coe_injective coe_zero coe_add
  (λ _ _, coe_smul _ _)

instance [add_comm_monoid β] : add_comm_monoid (α →ₛ β) :=
function.injective.add_comm_monoid (λ f, show α → β, from f) coe_injective coe_zero coe_add
  (λ _ _, coe_smul _ _)

instance [add_group β] : add_group (α →ₛ β) :=
function.injective.add_group (λ f, show α → β, from f) coe_injective
  coe_zero coe_add coe_neg coe_sub (λ _ _, coe_smul _ _) (λ _ _, coe_smul _ _)

instance [add_comm_group β] : add_comm_group (α →ₛ β) :=
function.injective.add_comm_group (λ f, show α → β, from f) coe_injective
  coe_zero coe_add coe_neg coe_sub (λ _ _, coe_smul _ _) (λ _ _, coe_smul _ _)

end additive

@[to_additive] instance [monoid β] : monoid (α →ₛ β) :=
function.injective.monoid (λ f, show α → β, from f) coe_injective coe_one coe_mul coe_pow

@[to_additive] instance [comm_monoid β] : comm_monoid (α →ₛ β) :=
function.injective.comm_monoid (λ f, show α → β, from f) coe_injective coe_one coe_mul coe_pow

@[to_additive] instance [group β] : group (α →ₛ β) :=
function.injective.group (λ f, show α → β, from f) coe_injective
  coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive] instance [comm_group β] : comm_group (α →ₛ β) :=
function.injective.comm_group (λ f, show α → β, from f) coe_injective
  coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

instance [semiring K] [add_comm_monoid β] [module K β] : module K (α →ₛ β) :=
function.injective.module K ⟨λ f, show α → β, from f, coe_zero, coe_add⟩
  coe_injective coe_smul

lemma smul_eq_map [has_smul K β] (k : K) (f : α →ₛ β) : k • f = f.map ((•) k) := rfl

instance [preorder β] : preorder (α →ₛ β) :=
{ le_refl := λf a, le_rfl,
  le_trans := λf g h hfg hgh a, le_trans (hfg _) (hgh a),
  .. simple_func.has_le }

instance [partial_order β] : partial_order (α →ₛ β) :=
{ le_antisymm := assume f g hfg hgf, ext $ assume a, le_antisymm (hfg a) (hgf a),
  .. simple_func.preorder }

instance [has_le β] [order_bot β] : order_bot (α →ₛ β) :=
{ bot := const α ⊥, bot_le := λf a, bot_le }

instance [has_le β] [order_top β] : order_top (α →ₛ β) :=
{ top := const α ⊤, le_top := λf a, le_top }

instance [semilattice_inf β] : semilattice_inf (α →ₛ β) :=
{ inf := (⊓),
  inf_le_left := assume f g a, inf_le_left,
  inf_le_right := assume f g a, inf_le_right,
  le_inf := assume f g h hfh hgh a, le_inf (hfh a) (hgh a),
  .. simple_func.partial_order }

instance [semilattice_sup β] : semilattice_sup (α →ₛ β) :=
{ sup := (⊔),
  le_sup_left := assume f g a, le_sup_left,
  le_sup_right := assume f g a, le_sup_right,
  sup_le := assume f g h hfh hgh a, sup_le (hfh a) (hgh a),
  .. simple_func.partial_order }

instance [lattice β] : lattice (α →ₛ β) :=
{ .. simple_func.semilattice_sup,.. simple_func.semilattice_inf }

instance [has_le β] [bounded_order β] : bounded_order (α →ₛ β) :=
{ .. simple_func.order_bot, .. simple_func.order_top }

lemma finset_sup_apply [semilattice_sup β] [order_bot β] {f : γ → α →ₛ β} (s : finset γ) (a : α) :
  s.sup f a = s.sup (λc, f c a) :=
begin
  refine finset.induction_on s rfl _,
  assume a s hs ih,
  rw [finset.sup_insert, finset.sup_insert, sup_apply, ih]
end

section restrict

variables [has_zero β]

/-- Restrict a simple function `f : α →ₛ β` to a set `s`. If `s` is measurable,
then `f.restrict s a = if a ∈ s then f a else 0`, otherwise `f.restrict s = const α 0`. -/
def restrict (f : α →ₛ β) (s : set α) : α →ₛ β :=
if hs : measurable_set s then piecewise s hs f 0 else 0

theorem restrict_of_not_measurable {f : α →ₛ β} {s : set α}
  (hs : ¬measurable_set s) :
  restrict f s = 0 :=
dif_neg hs

@[simp] theorem coe_restrict (f : α →ₛ β) {s : set α} (hs : measurable_set s) :
  ⇑(restrict f s) = indicator s f :=
by { rw [restrict, dif_pos hs], refl }

@[simp] theorem restrict_univ (f : α →ₛ β) : restrict f univ = f :=
by simp [restrict]

@[simp] theorem restrict_empty (f : α →ₛ β) : restrict f ∅ = 0 :=
by simp [restrict]

theorem map_restrict_of_zero [has_zero γ] {g : β → γ} (hg : g 0 = 0) (f : α →ₛ β) (s : set α) :
  (f.restrict s).map g = (f.map g).restrict s :=
ext $ λ x,
if hs : measurable_set s then by simp [hs, set.indicator_comp_of_zero hg]
else by simp [restrict_of_not_measurable hs, hg]

theorem map_coe_ennreal_restrict (f : α →ₛ ℝ≥0) (s : set α) :
  (f.restrict s).map (coe : ℝ≥0 → ℝ≥0∞) = (f.map coe).restrict s :=
map_restrict_of_zero ennreal.coe_zero _ _

theorem map_coe_nnreal_restrict (f : α →ₛ ℝ≥0) (s : set α) :
  (f.restrict s).map (coe : ℝ≥0 → ℝ) = (f.map coe).restrict s :=
map_restrict_of_zero nnreal.coe_zero _ _

theorem restrict_apply (f : α →ₛ β) {s : set α} (hs : measurable_set s) (a) :
  restrict f s a = indicator s f a :=
by simp only [f.coe_restrict hs]

theorem restrict_preimage (f : α →ₛ β) {s : set α} (hs : measurable_set s)
  {t : set β} (ht : (0:β) ∉ t) : restrict f s ⁻¹' t = s ∩ f ⁻¹' t :=
by simp [hs, indicator_preimage_of_not_mem _ _ ht, inter_comm]

theorem restrict_preimage_singleton (f : α →ₛ β) {s : set α} (hs : measurable_set s)
  {r : β} (hr : r ≠ 0) : restrict f s ⁻¹' {r} = s ∩ f ⁻¹' {r} :=
f.restrict_preimage hs hr.symm

lemma mem_restrict_range {r : β} {s : set α} {f : α →ₛ β} (hs : measurable_set s) :
  r ∈ (restrict f s).range ↔ (r = 0 ∧ s ≠ univ) ∨ (r ∈ f '' s) :=
by rw [← finset.mem_coe, coe_range, coe_restrict _ hs, mem_range_indicator]

lemma mem_image_of_mem_range_restrict {r : β} {s : set α} {f : α →ₛ β}
  (hr : r ∈ (restrict f s).range) (h0 : r ≠ 0) :
  r ∈ f '' s :=
if hs : measurable_set s then by simpa [mem_restrict_range hs, h0] using hr
else by { rw [restrict_of_not_measurable hs] at hr,
  exact (h0 $ eq_zero_of_mem_range_zero hr).elim }

@[mono] lemma restrict_mono [preorder β] (s : set α) {f g : α →ₛ β} (H : f ≤ g) :
  f.restrict s ≤ g.restrict s :=
if hs : measurable_set s then λ x, by simp only [coe_restrict _ hs, indicator_le_indicator (H x)]
else by simp only [restrict_of_not_measurable hs, le_refl]

end restrict

section approx

section
variables [semilattice_sup β] [order_bot β] [has_zero β]

/-- Fix a sequence `i : ℕ → β`. Given a function `α → β`, its `n`-th approximation
by simple functions is defined so that in case `β = ℝ≥0∞` it sends each `a` to the supremum
of the set `{i k | k ≤ n ∧ i k ≤ f a}`, see `approx_apply` and `supr_approx_apply` for details. -/
def approx (i : ℕ → β) (f : α → β) (n : ℕ) : α →ₛ β :=
(finset.range n).sup (λk, restrict (const α (i k)) {a:α | i k ≤ f a})

lemma approx_apply [topological_space β] [order_closed_topology β] [measurable_space β]
  [opens_measurable_space β] {i : ℕ → β} {f : α → β} {n : ℕ} (a : α) (hf : measurable f) :
  (approx i f n : α →ₛ β) a = (finset.range n).sup (λk, if i k ≤ f a then i k else 0) :=
begin
  dsimp only [approx],
  rw [finset_sup_apply],
  congr,
  funext k,
  rw [restrict_apply],
  refl,
  exact (hf measurable_set_Ici)
end

lemma monotone_approx (i : ℕ → β) (f : α → β) : monotone (approx i f) :=
assume n m h, finset.sup_mono $ finset.range_subset.2 h

lemma approx_comp [topological_space β] [order_closed_topology β] [measurable_space β]
  [opens_measurable_space β] [measurable_space γ]
  {i : ℕ → β} {f : γ → β} {g : α → γ} {n : ℕ} (a : α)
  (hf : measurable f) (hg : measurable g) :
  (approx i (f ∘ g) n : α →ₛ β) a = (approx i f n : γ →ₛ β) (g a) :=
by rw [approx_apply _ hf, approx_apply _ (hf.comp hg)]

end

lemma supr_approx_apply [topological_space β] [complete_lattice β] [order_closed_topology β]
  [has_zero β] [measurable_space β] [opens_measurable_space β]
  (i : ℕ → β) (f : α → β) (a : α) (hf : measurable f) (h_zero : (0 : β) = ⊥) :
  (⨆n, (approx i f n : α →ₛ β) a) = (⨆k (h : i k ≤ f a), i k) :=
begin
  refine le_antisymm (supr_le $ assume n, _) (supr_le $ assume k, supr_le $ assume hk, _),
  { rw [approx_apply a hf, h_zero],
    refine finset.sup_le (assume k hk, _),
    split_ifs,
    exact le_supr_of_le k (le_supr _ h),
    exact bot_le },
  { refine le_supr_of_le (k+1) _,
    rw [approx_apply a hf],
    have : k ∈ finset.range (k+1) := finset.mem_range.2 (nat.lt_succ_self _),
    refine le_trans (le_of_eq _) (finset.le_sup this),
    rw [if_pos hk] }
end

end approx

section eapprox

/-- A sequence of `ℝ≥0∞`s such that its range is the set of non-negative rational numbers. -/
def ennreal_rat_embed (n : ℕ) : ℝ≥0∞ :=
ennreal.of_real ((encodable.decode ℚ n).get_or_else (0 : ℚ))

lemma ennreal_rat_embed_encode (q : ℚ) :
  ennreal_rat_embed (encodable.encode q) = real.to_nnreal q :=
by rw [ennreal_rat_embed, encodable.encodek]; refl

/-- Approximate a function `α → ℝ≥0∞` by a sequence of simple functions. -/
def eapprox : (α → ℝ≥0∞) → ℕ → α →ₛ ℝ≥0∞ :=
approx ennreal_rat_embed

lemma eapprox_lt_top (f : α → ℝ≥0∞) (n : ℕ) (a : α) : eapprox f n a < ∞ :=
begin
  simp only [eapprox, approx, finset_sup_apply, finset.sup_lt_iff, with_top.zero_lt_top,
    finset.mem_range, ennreal.bot_eq_zero, restrict],
  assume b hb,
  split_ifs,
  { simp only [coe_zero, coe_piecewise, piecewise_eq_indicator, coe_const],
    calc {a : α | ennreal_rat_embed b ≤ f a}.indicator (λ x, ennreal_rat_embed b) a
        ≤ ennreal_rat_embed b : indicator_le_self _ _ a
    ... < ⊤ : ennreal.coe_lt_top },
  { exact with_top.zero_lt_top },
end

@[mono] lemma monotone_eapprox (f : α → ℝ≥0∞) : monotone (eapprox f) :=
monotone_approx _ f

lemma supr_eapprox_apply (f : α → ℝ≥0∞) (hf : measurable f) (a : α) :
  (⨆n, (eapprox f n : α →ₛ ℝ≥0∞) a) = f a :=
begin
  rw [eapprox, supr_approx_apply ennreal_rat_embed f a hf rfl],
  refine le_antisymm (supr_le $ assume i, supr_le $ assume hi, hi) (le_of_not_gt _),
  assume h,
  rcases ennreal.lt_iff_exists_rat_btwn.1 h with ⟨q, hq, lt_q, q_lt⟩,
  have : (real.to_nnreal q : ℝ≥0∞) ≤
      (⨆ (k : ℕ) (h : ennreal_rat_embed k ≤ f a), ennreal_rat_embed k),
  { refine le_supr_of_le (encodable.encode q) _,
    rw [ennreal_rat_embed_encode q],
    refine le_supr_of_le (le_of_lt q_lt) _,
    exact le_rfl },
  exact lt_irrefl _ (lt_of_le_of_lt this lt_q)
end

lemma eapprox_comp [measurable_space γ] {f : γ → ℝ≥0∞} {g : α → γ} {n : ℕ}
  (hf : measurable f) (hg : measurable g) :
  (eapprox (f ∘ g) n : α → ℝ≥0∞) = (eapprox f n : γ →ₛ ℝ≥0∞) ∘ g :=
funext $ assume a, approx_comp a hf hg

/-- Approximate a function `α → ℝ≥0∞` by a series of simple functions taking their values
in `ℝ≥0`. -/
def eapprox_diff (f : α → ℝ≥0∞) : ∀ (n : ℕ), α →ₛ ℝ≥0
| 0 := (eapprox f 0).map ennreal.to_nnreal
| (n+1) := (eapprox f (n+1) - eapprox f n).map ennreal.to_nnreal

lemma sum_eapprox_diff (f : α → ℝ≥0∞) (n : ℕ) (a : α) :
  (∑ k in finset.range (n+1), (eapprox_diff f k a : ℝ≥0∞)) = eapprox f n a :=
begin
  induction n with n IH,
  { simp only [nat.nat_zero_eq_zero, finset.sum_singleton, finset.range_one], refl },
  { rw [finset.sum_range_succ, nat.succ_eq_add_one, IH, eapprox_diff, coe_map, function.comp_app,
        coe_sub, pi.sub_apply, ennreal.coe_to_nnreal,
        add_tsub_cancel_of_le (monotone_eapprox f (nat.le_succ _) _)],
    apply (lt_of_le_of_lt _ (eapprox_lt_top f (n+1) a)).ne,
    rw tsub_le_iff_right,
    exact le_self_add },
end

lemma tsum_eapprox_diff (f : α → ℝ≥0∞) (hf : measurable f) (a : α) :
  (∑' n, (eapprox_diff f n a : ℝ≥0∞)) = f a :=
by simp_rw [ennreal.tsum_eq_supr_nat' (tendsto_add_at_top_nat 1), sum_eapprox_diff,
  supr_eapprox_apply f hf a]

end eapprox

end measurable

section measure
variables {m : measurable_space α} {μ ν : measure α}

/-- Integral of a simple function whose codomain is `ℝ≥0∞`. -/
def lintegral {m : measurable_space α} (f : α →ₛ ℝ≥0∞) (μ : measure α) : ℝ≥0∞ :=
∑ x in f.range, x * μ (f ⁻¹' {x})

lemma lintegral_eq_of_subset (f : α →ₛ ℝ≥0∞) {s : finset ℝ≥0∞}
  (hs : ∀ x, f x ≠ 0 → μ (f ⁻¹' {f x}) ≠ 0 → f x ∈ s) :
  f.lintegral μ = ∑ x in s, x * μ (f ⁻¹' {x}) :=
begin
  refine finset.sum_bij_ne_zero (λr _ _, r) _ _ _ _,
  { simpa only [forall_range_iff, mul_ne_zero_iff, and_imp] },
  { intros, assumption },
  { intros b _ hb,
    refine ⟨b, _, hb, rfl⟩,
    rw [mem_range, ← preimage_singleton_nonempty],
    exact nonempty_of_measure_ne_zero (mul_ne_zero_iff.1 hb).2 },
  { intros, refl }
end

lemma lintegral_eq_of_subset' (f : α →ₛ ℝ≥0∞) {s : finset ℝ≥0∞}
  (hs : f.range \ {0} ⊆ s) :
  f.lintegral μ = ∑ x in s, x * μ (f ⁻¹' {x}) :=
f.lintegral_eq_of_subset $ λ x hfx _, hs $
  finset.mem_sdiff.2 ⟨f.mem_range_self x, mt finset.mem_singleton.1 hfx⟩

/-- Calculate the integral of `(g ∘ f)`, where `g : β → ℝ≥0∞` and `f : α →ₛ β`.  -/
lemma map_lintegral (g : β → ℝ≥0∞) (f : α →ₛ β) :
  (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x}) :=
begin
  simp only [lintegral, range_map],
  refine finset.sum_image' _ (assume b hb, _),
  rcases mem_range.1 hb with ⟨a, rfl⟩,
  rw [map_preimage_singleton, ← f.sum_measure_preimage_singleton, finset.mul_sum],
  refine finset.sum_congr _ _,
  { congr },
  { assume x, simp only [finset.mem_filter], rintro ⟨_, h⟩, rw h },
end

lemma add_lintegral (f g : α →ₛ ℝ≥0∞) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ :=
calc (f + g).lintegral μ =
      ∑ x in (pair f g).range, (x.1 * μ (pair f g ⁻¹' {x}) + x.2 * μ (pair f g ⁻¹' {x})) :
    by rw [add_eq_map₂, map_lintegral]; exact finset.sum_congr rfl (assume a ha, add_mul _ _ _)
  ... = ∑ x in (pair f g).range, x.1 * μ (pair f g ⁻¹' {x}) +
      ∑ x in (pair f g).range, x.2 * μ (pair f g ⁻¹' {x}) : by rw [finset.sum_add_distrib]
  ... = ((pair f g).map prod.fst).lintegral μ + ((pair f g).map prod.snd).lintegral μ :
    by rw [map_lintegral, map_lintegral]
  ... = lintegral f μ + lintegral g μ : rfl

lemma const_mul_lintegral (f : α →ₛ ℝ≥0∞) (x : ℝ≥0∞) :
  (const α x * f).lintegral μ = x * f.lintegral μ :=
calc (f.map (λa, x * a)).lintegral μ = ∑ r in f.range, x * r * μ (f ⁻¹' {r}) :
    map_lintegral _ _
  ... = ∑ r in f.range, x * (r * μ (f ⁻¹' {r})) :
    finset.sum_congr rfl (assume a ha, mul_assoc _ _ _)
  ... = x * f.lintegral μ :
    finset.mul_sum.symm

/-- Integral of a simple function `α →ₛ ℝ≥0∞` as a bilinear map. -/
def lintegralₗ {m : measurable_space α} : (α →ₛ ℝ≥0∞) →ₗ[ℝ≥0∞] measure α →ₗ[ℝ≥0∞] ℝ≥0∞ :=
{ to_fun := λ f,
  { to_fun := lintegral f,
    map_add' := by simp [lintegral, mul_add, finset.sum_add_distrib],
    map_smul' := λ c μ, by simp [lintegral, mul_left_comm _ c, finset.mul_sum] },
  map_add' := λ f g, linear_map.ext (λ μ, add_lintegral f g),
  map_smul' := λ c f, linear_map.ext (λ μ, const_mul_lintegral f c) }

@[simp] lemma zero_lintegral : (0 : α →ₛ ℝ≥0∞).lintegral μ = 0 :=
linear_map.ext_iff.1 lintegralₗ.map_zero μ

lemma lintegral_add {ν} (f : α →ₛ ℝ≥0∞) : f.lintegral (μ + ν) = f.lintegral μ + f.lintegral ν :=
(lintegralₗ f).map_add μ ν

lemma lintegral_smul (f : α →ₛ ℝ≥0∞) (c : ℝ≥0∞) :
  f.lintegral (c • μ) = c • f.lintegral μ :=
(lintegralₗ f).map_smul c μ

@[simp] lemma lintegral_zero [measurable_space α] (f : α →ₛ ℝ≥0∞) :
  f.lintegral 0 = 0 :=
(lintegralₗ f).map_zero

lemma lintegral_sum {m : measurable_space α} {ι} (f : α →ₛ ℝ≥0∞) (μ : ι → measure α) :
  f.lintegral (measure.sum μ) = ∑' i, f.lintegral (μ i) :=
begin
  simp only [lintegral, measure.sum_apply, f.measurable_set_preimage, ← finset.tsum_subtype,
    ← ennreal.tsum_mul_left],
  apply ennreal.tsum_comm
end

lemma restrict_lintegral (f : α →ₛ ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  (restrict f s).lintegral μ = ∑ r in f.range, r * μ (f ⁻¹' {r} ∩ s) :=
calc (restrict f s).lintegral μ = ∑ r in f.range, r * μ (restrict f s ⁻¹' {r}) :
  lintegral_eq_of_subset _ $ λ x hx, if hxs : x ∈ s
    then λ _, by simp only [f.restrict_apply hs, indicator_of_mem hxs, mem_range_self]
    else false.elim $ hx $ by simp [*]
... = ∑ r in f.range, r * μ (f ⁻¹' {r} ∩ s) :
  finset.sum_congr rfl $ forall_range_iff.2 $ λ b, if hb : f b = 0 then by simp only [hb, zero_mul]
    else by rw [restrict_preimage_singleton _ hs hb, inter_comm]

lemma lintegral_restrict {m : measurable_space α} (f : α →ₛ ℝ≥0∞) (s : set α) (μ : measure α) :
  f.lintegral (μ.restrict s) = ∑ y in f.range, y * μ (f ⁻¹' {y} ∩ s) :=
by simp only [lintegral, measure.restrict_apply, f.measurable_set_preimage]

lemma restrict_lintegral_eq_lintegral_restrict (f : α →ₛ ℝ≥0∞) {s : set α}
  (hs : measurable_set s) :
  (restrict f s).lintegral μ = f.lintegral (μ.restrict s) :=
by rw [f.restrict_lintegral hs, lintegral_restrict]

lemma const_lintegral (c : ℝ≥0∞) : (const α c).lintegral μ = c * μ univ :=
begin
  rw [lintegral],
  casesI is_empty_or_nonempty α,
  { simp [μ.eq_zero_of_is_empty] },
  { simp [preimage_const_of_mem] },
end

lemma const_lintegral_restrict (c : ℝ≥0∞) (s : set α) :
  (const α c).lintegral (μ.restrict s) = c * μ s :=
by rw [const_lintegral, measure.restrict_apply measurable_set.univ, univ_inter]

lemma restrict_const_lintegral (c : ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  ((const α c).restrict s).lintegral μ = c * μ s :=
by rw [restrict_lintegral_eq_lintegral_restrict _ hs, const_lintegral_restrict]

lemma le_sup_lintegral (f g : α →ₛ ℝ≥0∞) : f.lintegral μ ⊔ g.lintegral μ ≤ (f ⊔ g).lintegral μ :=
calc f.lintegral μ ⊔ g.lintegral μ =
      ((pair f g).map prod.fst).lintegral μ ⊔ ((pair f g).map prod.snd).lintegral μ : rfl
  ... ≤ ∑ x in (pair f g).range, (x.1 ⊔ x.2) * μ (pair f g ⁻¹' {x}) :
  begin
    rw [map_lintegral, map_lintegral],
    refine sup_le _ _;
      refine finset.sum_le_sum (λ a _, mul_le_mul_right' _ _),
    exact le_sup_left,
    exact le_sup_right
  end
  ... = (f ⊔ g).lintegral μ : by rw [sup_eq_map₂, map_lintegral]

/-- `simple_func.lintegral` is monotone both in function and in measure. -/
@[mono] lemma lintegral_mono {f g : α →ₛ ℝ≥0∞} (hfg : f ≤ g) (hμν : μ ≤ ν) :
  f.lintegral μ ≤ g.lintegral ν :=
calc f.lintegral μ ≤ f.lintegral μ ⊔ g.lintegral μ : le_sup_left
  ... ≤ (f ⊔ g).lintegral μ : le_sup_lintegral _ _
  ... = g.lintegral μ : by rw [sup_of_le_right hfg]
  ... ≤ g.lintegral ν : finset.sum_le_sum $ λ y hy, ennreal.mul_left_mono $
                          hμν _ (g.measurable_set_preimage _)

/-- `simple_func.lintegral` depends only on the measures of `f ⁻¹' {y}`. -/
lemma lintegral_eq_of_measure_preimage [measurable_space β] {f : α →ₛ ℝ≥0∞} {g : β →ₛ ℝ≥0∞}
  {ν : measure β} (H : ∀ y, μ (f ⁻¹' {y}) = ν (g ⁻¹' {y})) :
  f.lintegral μ = g.lintegral ν :=
begin
  simp only [lintegral, ← H],
  apply lintegral_eq_of_subset,
  simp only [H],
  intros,
  exact mem_range_of_measure_ne_zero ‹_›
end

/-- If two simple functions are equal a.e., then their `lintegral`s are equal. -/
lemma lintegral_congr {f g : α →ₛ ℝ≥0∞} (h : f =ᵐ[μ] g) :
  f.lintegral μ = g.lintegral μ :=
lintegral_eq_of_measure_preimage $ λ y, measure_congr $
  eventually.set_eq $ h.mono $ λ x hx, by simp [hx]

lemma lintegral_map' {β} [measurable_space β] {μ' : measure β} (f : α →ₛ ℝ≥0∞) (g : β →ₛ ℝ≥0∞)
  (m' : α → β) (eq : ∀ a, f a = g (m' a)) (h : ∀s, measurable_set s → μ' s = μ (m' ⁻¹' s)) :
  f.lintegral μ = g.lintegral μ' :=
lintegral_eq_of_measure_preimage $ λ y,
by { simp only [preimage, eq], exact (h (g ⁻¹' {y}) (g.measurable_set_preimage _)).symm }

lemma lintegral_map {β} [measurable_space β] (g : β →ₛ ℝ≥0∞) {f : α → β} (hf : measurable f) :
  g.lintegral (measure.map f μ) = (g.comp f hf).lintegral μ :=
eq.symm $ lintegral_map' _ _ f (λ a, rfl) (λ s hs, measure.map_apply hf hs)

end measure

section fin_meas_supp

open finset function

lemma support_eq [measurable_space α] [has_zero β] (f : α →ₛ β) :
  support f = ⋃ y ∈ f.range.filter (λ y, y ≠ 0), f ⁻¹' {y} :=
set.ext $ λ x, by simp only [mem_support, set.mem_preimage, mem_filter, mem_range_self, true_and,
  exists_prop, mem_Union, set.mem_range, mem_singleton_iff, exists_eq_right']

variables {m : measurable_space α} [has_zero β] [has_zero γ] {μ : measure α} {f : α →ₛ β}

lemma measurable_set_support [measurable_space α] (f : α →ₛ β) : measurable_set (support f) :=
by { rw f.support_eq, exact finset.measurable_set_bUnion _ (λ y hy, measurable_set_fiber _ _), }

/-- A `simple_func` has finite measure support if it is equal to `0` outside of a set of finite
measure. -/
protected def fin_meas_supp {m : measurable_space α} (f : α →ₛ β) (μ : measure α) : Prop :=
f =ᶠ[μ.cofinite] 0

lemma fin_meas_supp_iff_support : f.fin_meas_supp μ ↔ μ (support f) < ∞ := iff.rfl

lemma fin_meas_supp_iff : f.fin_meas_supp μ ↔ ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞ :=
begin
  split,
  { refine λ h y hy, lt_of_le_of_lt (measure_mono _) h,
    exact λ x hx (H : f x = 0), hy $ H ▸ eq.symm hx },
  { intro H,
    rw [fin_meas_supp_iff_support, support_eq],
    refine lt_of_le_of_lt (measure_bUnion_finset_le _ _) (sum_lt_top _),
    exact λ y hy, (H y (finset.mem_filter.1 hy).2).ne }
end

namespace fin_meas_supp

lemma meas_preimage_singleton_ne_zero (h : f.fin_meas_supp μ) {y : β} (hy : y ≠ 0) :
  μ (f ⁻¹' {y}) < ∞ :=
fin_meas_supp_iff.1 h y hy

protected lemma map {g : β → γ} (hf : f.fin_meas_supp μ) (hg : g 0 = 0) :
  (f.map g).fin_meas_supp μ :=
flip lt_of_le_of_lt hf (measure_mono $ support_comp_subset hg f)

lemma of_map {g : β → γ} (h : (f.map g).fin_meas_supp μ) (hg : ∀b, g b = 0 → b = 0) :
  f.fin_meas_supp μ :=
flip lt_of_le_of_lt h $ measure_mono $ support_subset_comp hg _

lemma map_iff {g : β → γ} (hg : ∀ {b}, g b = 0 ↔ b = 0) :
  (f.map g).fin_meas_supp μ ↔ f.fin_meas_supp μ :=
⟨λ h, h.of_map $ λ b, hg.1, λ h, h.map $ hg.2 rfl⟩

protected lemma pair {g : α →ₛ γ} (hf : f.fin_meas_supp μ) (hg : g.fin_meas_supp μ) :
  (pair f g).fin_meas_supp μ :=
calc μ (support $ pair f g) = μ (support f ∪ support g) : congr_arg μ $ support_prod_mk f g
... ≤ μ (support f) + μ (support g) : measure_union_le _ _
... < _ : add_lt_top.2 ⟨hf, hg⟩

protected lemma map₂ [has_zero δ] (hf : f.fin_meas_supp μ)
  {g : α →ₛ γ} (hg : g.fin_meas_supp μ) {op : β → γ → δ} (H : op 0 0 = 0) :
  ((pair f g).map (function.uncurry op)).fin_meas_supp μ :=
(hf.pair hg).map H

protected lemma add {β} [add_monoid β] {f g : α →ₛ β} (hf : f.fin_meas_supp μ)
  (hg : g.fin_meas_supp μ) :
  (f + g).fin_meas_supp μ :=
by { rw [add_eq_map₂], exact hf.map₂ hg (zero_add 0) }

protected lemma mul {β} [monoid_with_zero β] {f g : α →ₛ β} (hf : f.fin_meas_supp μ)
  (hg : g.fin_meas_supp μ) :
  (f * g).fin_meas_supp μ :=
by { rw [mul_eq_map₂], exact hf.map₂ hg (zero_mul 0) }

lemma lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hm : f.fin_meas_supp μ) (hf : ∀ᵐ a ∂μ, f a ≠ ∞) :
  f.lintegral μ < ∞ :=
begin
  refine sum_lt_top (λ a ha, _),
  rcases eq_or_ne a ∞ with rfl|ha,
  { simp only [ae_iff, ne.def, not_not] at hf,
    simp [set.preimage, hf] },
  { by_cases ha0 : a = 0,
    { subst a, rwa [zero_mul] },
    { exact mul_ne_top ha (fin_meas_supp_iff.1 hm _ ha0).ne } }
end

lemma of_lintegral_ne_top {f : α →ₛ ℝ≥0∞} (h : f.lintegral μ ≠ ∞) : f.fin_meas_supp μ :=
begin
  refine fin_meas_supp_iff.2 (λ b hb, _),
  rw [f.lintegral_eq_of_subset' (finset.subset_insert b _)] at h,
  refine ennreal.lt_top_of_mul_ne_top_right _ hb,
  exact (lt_top_of_sum_ne_top h (finset.mem_insert_self _ _)).ne
end

lemma iff_lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hf : ∀ᵐ a ∂μ, f a ≠ ∞) :
  f.fin_meas_supp μ ↔ f.lintegral μ < ∞ :=
⟨λ h, h.lintegral_lt_top hf, λ h, of_lintegral_ne_top h.ne⟩

end fin_meas_supp

end fin_meas_supp

/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under
addition (of functions with disjoint support).

It is possible to make the hypotheses in `h_add` a bit stronger, and such conditions can be added
once we need them (for example it is only necessary to consider the case where `g` is a multiple
of a characteristic function, and that this multiple doesn't appear in the image of `f`) -/
@[elab_as_eliminator]
protected lemma induction {α γ} [measurable_space α] [add_monoid γ] {P : simple_func α γ → Prop}
  (h_ind : ∀ c {s} (hs : measurable_set s),
    P (simple_func.piecewise s hs (simple_func.const _ c) (simple_func.const _ 0)))
  (h_add : ∀ ⦃f g : simple_func α γ⦄, disjoint (support f) (support g) → P f → P g → P (f + g))
  (f : simple_func α γ) : P f :=
begin
  generalize' h : f.range \ {0} = s,
  rw [← finset.coe_inj, finset.coe_sdiff, finset.coe_singleton, simple_func.coe_range] at h,
  revert s f h, refine finset.induction _ _,
  { intros f hf, rw [finset.coe_empty, diff_eq_empty, range_subset_singleton] at hf,
    convert h_ind 0 measurable_set.univ, ext x, simp [hf] },
  { intros x s hxs ih f hf,
    have mx := f.measurable_set_preimage {x},
    let g := simple_func.piecewise (f ⁻¹' {x}) mx 0 f,
    have Pg : P g,
    { apply ih, simp only [g, simple_func.coe_piecewise, range_piecewise],
      rw [image_compl_preimage, union_diff_distrib, diff_diff_comm, hf, finset.coe_insert,
        insert_diff_self_of_not_mem, diff_eq_empty.mpr, set.empty_union],
      { rw [set.image_subset_iff], convert set.subset_univ _,
        exact preimage_const_of_mem (mem_singleton _) },
      { rwa [finset.mem_coe] }},
    convert h_add _ Pg (h_ind x mx),
    { ext1 y, by_cases hy : y ∈ f ⁻¹' {x}; [simpa [hy], simp [hy]] },
    rw disjoint_iff_inf_le,
    rintro y, by_cases hy : y ∈ f ⁻¹' {x}; simp [hy] }
end

end simple_func

end measure_theory

open measure_theory measure_theory.simple_func
/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`. -/
@[elab_as_eliminator]
theorem measurable.ennreal_induction {α} [measurable_space α] {P : (α → ℝ≥0∞) → Prop}
  (h_ind : ∀ (c : ℝ≥0∞) ⦃s⦄, measurable_set s → P (indicator s (λ _, c)))
  (h_add : ∀ ⦃f g : α → ℝ≥0∞⦄, disjoint (support f) (support g) → measurable f → measurable g →
    P f → P g → P (f + g))
  (h_supr : ∀ ⦃f : ℕ → α → ℝ≥0∞⦄ (hf : ∀n, measurable (f n)) (h_mono : monotone f)
    (hP : ∀ n, P (f n)), P (λ x, ⨆ n, f n x))
  ⦃f : α → ℝ≥0∞⦄ (hf : measurable f) : P f :=
begin
  convert h_supr (λ n, (eapprox f n).measurable) (monotone_eapprox f) _,
  { ext1 x, rw [supr_eapprox_apply f hf] },
  { exact λ n, simple_func.induction (λ c s hs, h_ind c hs)
      (λ f g hfg hf hg, h_add hfg f.measurable g.measurable hf hg) (eapprox f n) }
end
