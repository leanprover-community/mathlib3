/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import tactic
import measure_theory.measure_space
import measure_theory.borel_space
import data.indicator_function
import data.support

/-!
# Lebesgue integral for `ennreal`-valued functions

We define simple functions and show that each Borel measurable function on `ennreal` can be
approximated by a sequence of simple functions.
-/

noncomputable theory
open set (hiding restrict restrict_apply) filter ennreal
open_locale classical topological_space big_operators nnreal

namespace measure_theory

variables {α β γ δ : Type*}

/-- A function `f` from a measurable space to any type is called *simple*,
if every preimage `f ⁻¹' {x}` is measurable, and the range is finite. This structure bundles
a function with these properties. -/
structure {u v} simple_func (α : Type u) [measurable_space α] (β : Type v) :=
(to_fun : α → β)
(is_measurable_fiber' : ∀ x, is_measurable (to_fun ⁻¹' {x}))
(finite_range' : (set.range to_fun).finite)

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

section measurable
variables [measurable_space α]
instance has_coe_to_fun : has_coe_to_fun (α →ₛ β) := ⟨_, to_fun⟩

lemma coe_injective ⦃f g : α →ₛ β⦄ (H : ⇑f = g) : f = g :=
by cases f; cases g; congr; exact H

@[ext] theorem ext {f g : α →ₛ β} (H : ∀ a, f a = g a) : f = g :=
coe_injective $ funext H

lemma finite_range (f : α →ₛ β) : (set.range f).finite := f.finite_range'

lemma is_measurable_fiber (f : α →ₛ β) (x : β) : is_measurable (f ⁻¹' {x}) :=
f.is_measurable_fiber' x

/-- Range of a simple function `α →ₛ β` as a `finset β`. -/
protected def range (f : α →ₛ β) : finset β := f.finite_range.to_finset

@[simp] theorem mem_range {f : α →ₛ β} {b} : b ∈ f.range ↔ b ∈ range f :=
finite.mem_to_finset

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

/-- Constant function as a `simple_func`. -/
def const (α) {β} [measurable_space α] (b : β) : α →ₛ β :=
⟨λ a, b, λ x, is_measurable.const _, finite_range_const⟩

instance [inhabited β] : inhabited (α →ₛ β) := ⟨const _ (default _)⟩

theorem const_apply (a : α) (b : β) : (const α b) a = b := rfl

@[simp] theorem coe_const (b : β) : ⇑(const α b) = function.const α b := rfl

@[simp] lemma range_const (α) [measurable_space α] [nonempty α] (b : β) :
  (const α b).range = {b} :=
finset.coe_injective $ by simp

lemma is_measurable_cut (r : α → β → Prop) (f : α →ₛ β)
  (h : ∀b, is_measurable {a | r a b}) : is_measurable {a | r a (f a)} :=
begin
  have : {a | r a (f a)} = ⋃ b ∈ range f, {a | r a b} ∩ f ⁻¹' {b},
  { ext a,
    suffices : r a (f a) ↔ ∃ i, r a (f i) ∧ f a = f i, by simpa,
    exact ⟨λ h, ⟨a, ⟨h, rfl⟩⟩, λ ⟨a', ⟨h', e⟩⟩, e.symm ▸ h'⟩ },
  rw this,
  exact is_measurable.bUnion f.finite_range.countable
    (λ b _, is_measurable.inter (h b) (f.is_measurable_fiber _))
end

theorem is_measurable_preimage (f : α →ₛ β) (s) : is_measurable (f ⁻¹' s) :=
is_measurable_cut (λ _ b, b ∈ s) f (λ b, is_measurable.const (b ∈ s))

/-- A simple function is measurable -/
protected theorem measurable [measurable_space β] (f : α →ₛ β) : measurable f :=
λ s _, is_measurable_preimage f s

/-- If-then-else as a `simple_func`. -/
def ite (s : set α) (hs : is_measurable s) (f g : α →ₛ β) : α →ₛ β :=
⟨s.piecewise f g,
 λ x, by letI : measurable_space β := ⊤; exact
   measurable.if hs f.measurable g.measurable _ trivial,
 (f.finite_range.union g.finite_range).subset range_ite_subset⟩

@[simp] theorem coe_ite {s : set α} (hs : is_measurable s) (f g : α →ₛ β) :
  ⇑(ite s hs f g) = s.piecewise f g :=
rfl

theorem ite_apply {s : set α} (hs : is_measurable s) (f g : α →ₛ β) (a) :
  ite s hs f g a = if a ∈ s then f a else g a :=
rfl

@[simp] lemma ite_compl {s : set α} (hs : is_measurable sᶜ) (f g : α →ₛ β) :
  ite sᶜ hs f g = ite s hs.of_compl g f :=
coe_injective $ by simp [hs]

@[simp] lemma ite_univ (f g : α →ₛ β) : ite univ is_measurable.univ f g = f :=
coe_injective $ by simp

@[simp] lemma ite_empty (f g : α →ₛ β) : ite ∅ is_measurable.empty f g = g :=
coe_injective $ by simp

/-- If `f : α →ₛ β` is a simple function and `g : β → α →ₛ γ` is a family of simple functions,
then `f.bind g` binds the first argument of `g` to `f`. In other words, `f.bind g a = g (f a) a`. -/
def bind (f : α →ₛ β) (g : β → α →ₛ γ) : α →ₛ γ :=
⟨λa, g (f a) a,
 λ c, is_measurable_cut (λa b, g b a ∈ ({c} : set γ)) f (λ b, (g b).is_measurable_fiber c),
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
finset.coe_injective $ by simp [range_comp]

lemma map_preimage (f : α →ₛ β) (g : β → γ) (s : set γ) :
  (f.map g) ⁻¹' s = f ⁻¹' ↑(f.range.filter (λb, g b ∈ s)) :=
by { simp only [coe_range, sep_mem_eq, set.mem_range, function.comp_app, coe_map, finset.coe_filter,
  ← mem_preimage, inter_comm, preimage_inter_range], apply preimage_comp }

lemma map_preimage_singleton (f : α →ₛ β) (g : β → γ) (c : γ) :
  (f.map g) ⁻¹' {c} = f ⁻¹' ↑(f.range.filter (λ b, g b = c)) :=
map_preimage _ _ _

/-- If `f` is a simple function taking values in `β → γ` and `g` is another simple function
with the same domain and codomain `β`, then `f.seq g = f a (g a)`. -/
def seq (f : α →ₛ (β → γ)) (g : α →ₛ β) : α →ₛ γ := f.bind (λf, g.map f)

@[simp] lemma seq_apply (f : α →ₛ (β → γ)) (g : α →ₛ β) (a : α) : f.seq g a = f a (g a) := rfl

/-- Combine two simple functions `f : α →ₛ β` and `g : α →ₛ β`
into `λ a, (f a, g a)`. -/
def pair (f : α →ₛ β) (g : α →ₛ γ) : α →ₛ (β × γ) := (f.map prod.mk).seq g

@[simp] lemma pair_apply (f : α →ₛ β) (g : α →ₛ γ) (a) : pair f g a = (f a, g a) := rfl

lemma pair_preimage (f : α →ₛ β) (g : α →ₛ γ) (s : set β) (t : set γ) :
  (pair f g) ⁻¹' (set.prod s t) = (f ⁻¹' s) ∩ (g ⁻¹' t) := rfl

/- A special form of `pair_preimage` -/
lemma pair_preimage_singleton (f : α →ₛ β) (g : α →ₛ γ) (b : β) (c : γ) :
  (pair f g) ⁻¹' {(b, c)} = (f ⁻¹' {b}) ∩ (g ⁻¹' {c}) :=
by { rw ← prod_singleton_singleton, exact pair_preimage _ _ _ _ }

theorem bind_const (f : α →ₛ β) : f.bind (const α) = f := by ext; simp

instance [has_zero β] : has_zero (α →ₛ β) := ⟨const α 0⟩
instance [has_add β] : has_add (α →ₛ β) := ⟨λf g, (f.map (+)).seq g⟩
instance [has_mul β] : has_mul (α →ₛ β) := ⟨λf g, (f.map (*)).seq g⟩
instance [has_sup β] : has_sup (α →ₛ β) := ⟨λf g, (f.map (⊔)).seq g⟩
instance [has_inf β] : has_inf (α →ₛ β) := ⟨λf g, (f.map (⊓)).seq g⟩
instance [has_le β] : has_le (α →ₛ β) := ⟨λf g, ∀a, f a ≤ g a⟩

@[simp, norm_cast] lemma coe_zero [has_zero β] : ⇑(0 : α →ₛ β) = 0 := rfl
@[simp] lemma const_zero [has_zero β] : const α 0 = 0 := rfl
@[simp, norm_cast] lemma coe_add [has_add β] (f g : α →ₛ β) : ⇑(f + g) = f + g := rfl
@[simp, norm_cast] lemma coe_mul [has_mul β] (f g : α →ₛ β) : ⇑(f * g) = f * g := rfl
@[simp, norm_cast] lemma coe_le [preorder β] {f g : α →ₛ β} : (f : α → β) ≤ g ↔ f ≤ g := iff.rfl

@[simp] lemma range_zero [nonempty α] [has_zero β] : (0 : α →ₛ β).range = {0} :=
finset.ext $ λ x, by simp [eq_comm]

lemma eq_zero_of_mem_range_zero [has_zero β] : ∀ {y : β}, y ∈ (0 : α →ₛ β).range → y = 0 :=
forall_range_iff.2 $ λ x, rfl

lemma sup_apply [has_sup β] (f g : α →ₛ β) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl
lemma mul_apply [has_mul β] (f g : α →ₛ β) (a : α) : (f * g) a = f a * g a := rfl
lemma add_apply [has_add β] (f g : α →ₛ β) (a : α) : (f + g) a = f a + g a := rfl

lemma add_eq_map₂ [has_add β] (f g : α →ₛ β) : f + g = (pair f g).map (λp:β×β, p.1 + p.2) :=
rfl

lemma mul_eq_map₂ [has_mul β] (f g : α →ₛ β) : f * g = (pair f g).map (λp:β×β, p.1 * p.2) :=
rfl

lemma sup_eq_map₂ [has_sup β] (f g : α →ₛ β) : f ⊔ g = (pair f g).map (λp:β×β, p.1 ⊔ p.2) :=
rfl

lemma const_mul_eq_map [has_mul β] (f : α →ₛ β) (b : β) : const α b * f = f.map (λa, b * a) := rfl

instance [add_monoid β] : add_monoid (α →ₛ β) :=
function.injective.add_monoid (λ f, show α → β, from f) coe_injective coe_zero coe_add

instance add_comm_monoid [add_comm_monoid β] : add_comm_monoid (α →ₛ β) :=
function.injective.add_comm_monoid (λ f, show α → β, from f) coe_injective coe_zero coe_add

instance [has_neg β] : has_neg (α →ₛ β) := ⟨λf, f.map (has_neg.neg)⟩

@[simp, norm_cast] lemma coe_neg [has_neg β] (f : α →ₛ β) : ⇑(-f) = -f := rfl

instance [add_group β] : add_group (α →ₛ β) :=
function.injective.add_group (λ f, show α → β, from f) coe_injective coe_zero coe_add coe_neg

@[simp, norm_cast] lemma coe_sub [add_group β] (f g : α →ₛ β) : ⇑(f - g) = f - g := rfl

instance [add_comm_group β] : add_comm_group (α →ₛ β) :=
function.injective.add_comm_group (λ f, show α → β, from f) coe_injective
  coe_zero coe_add coe_neg

variables {K : Type*}

instance [has_scalar K β] : has_scalar K (α →ₛ β) := ⟨λk f, f.map ((•) k)⟩

@[simp] lemma coe_smul [has_scalar K β] (c : K) (f : α →ₛ β) : ⇑(c • f) = c • f := rfl

lemma smul_apply [has_scalar K β] (k : K) (f : α →ₛ β) (a : α) : (k • f) a = k • f a := rfl

instance [semiring K] [add_comm_monoid β] [semimodule K β] : semimodule K (α →ₛ β) :=
function.injective.semimodule K ⟨λ f, show α → β, from f, coe_zero, coe_add⟩
  coe_injective coe_smul

lemma smul_eq_map [has_scalar K β] (k : K) (f : α →ₛ β) : k • f = f.map ((•) k) := rfl

instance [preorder β] : preorder (α →ₛ β) :=
{ le_refl := λf a, le_refl _,
  le_trans := λf g h hfg hgh a, le_trans (hfg _) (hgh a),
  .. simple_func.has_le }

instance [partial_order β] : partial_order (α →ₛ β) :=
{ le_antisymm := assume f g hfg hgf, ext $ assume a, le_antisymm (hfg a) (hgf a),
  .. simple_func.preorder }

instance [order_bot β] : order_bot (α →ₛ β) :=
{ bot := const α ⊥, bot_le := λf a, bot_le, .. simple_func.partial_order }

instance [order_top β] : order_top (α →ₛ β) :=
{ top := const α ⊤, le_top := λf a, le_top, .. simple_func.partial_order }

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

instance [semilattice_sup_bot β] : semilattice_sup_bot (α →ₛ β) :=
{ .. simple_func.semilattice_sup,.. simple_func.order_bot }

instance [lattice β] : lattice (α →ₛ β) :=
{ .. simple_func.semilattice_sup,.. simple_func.semilattice_inf }

instance [bounded_lattice β] : bounded_lattice (α →ₛ β) :=
{ .. simple_func.lattice, .. simple_func.order_bot, .. simple_func.order_top }

lemma finset_sup_apply [semilattice_sup_bot β] {f : γ → α →ₛ β} (s : finset γ) (a : α) :
  s.sup f a = s.sup (λc, f c a) :=
begin
  refine finset.induction_on s rfl _,
  assume a s hs ih,
  rw [finset.sup_insert, finset.sup_insert, sup_apply, ih]
end

/-- Restrict a simple function `f : α →ₛ β` to a set `s`. If `s` is measurable,
then `f.restrict s a = if a ∈ s then f a else 0`, otherwise `f.restrict s = const α 0`. -/
def restrict [has_zero β] (f : α →ₛ β) (s : set α) : α →ₛ β :=
if hs : is_measurable s then ite s hs f 0 else 0

theorem restrict_of_not_measurable [has_zero β] {f : α →ₛ β} {s : set α}
  (hs : ¬is_measurable s) :
  restrict f s = 0 :=
dif_neg hs

@[simp] theorem coe_restrict [has_zero β] (f : α →ₛ β) {s : set α} (hs : is_measurable s) :
  ⇑(restrict f s) = indicator s f :=
by { rw [restrict, dif_pos hs], refl }

@[simp] theorem restrict_univ [has_zero β] (f : α →ₛ β) : restrict f univ = f :=
by simp [restrict]

@[simp] theorem restrict_empty [has_zero β] (f : α →ₛ β) : restrict f ∅ = 0 :=
by simp [restrict]

theorem restrict_apply [has_zero β]
  (f : α →ₛ β) {s : set α} (hs : is_measurable s) (a) :
  restrict f s a = if a ∈ s then f a else 0 :=
by simp only [hs, coe_restrict]

theorem restrict_preimage [has_zero β]
  (f : α →ₛ β) {s : set α} (hs : is_measurable s)
  {t : set β} (ht : (0:β) ∉ t) : restrict f s ⁻¹' t = s ∩ f ⁻¹' t :=
by simp [hs, indicator_preimage_of_not_mem _ _ ht]

theorem restrict_preimage_singleton [has_zero β]
  (f : α →ₛ β) {s : set α} (hs : is_measurable s)
  {r : β} (hr : r ≠ 0) : restrict f s ⁻¹' {r} = s ∩ f ⁻¹' {r} :=
f.restrict_preimage hs hr.symm

lemma mem_restrict_range [has_zero β] {r : β} {s : set α} {f : α →ₛ β} (hs : is_measurable s) :
  r ∈ (restrict f s).range ↔ (r = 0 ∧ s ≠ univ) ∨ (r ∈ f '' s) :=
by rw [← finset.mem_coe, coe_range, coe_restrict _ hs, mem_range_indicator]

lemma mem_image_of_mem_range_restrict [has_zero β] {r : β} {s : set α} {f : α →ₛ β}
  (hr : r ∈ (restrict f s).range) (h0 : r ≠ 0) :
  r ∈ f '' s :=
if hs : is_measurable s then by simpa [mem_restrict_range hs, h0] using hr
else by { rw [restrict_of_not_measurable hs] at hr,
  exact (h0 $ eq_zero_of_mem_range_zero hr).elim }

@[mono] lemma restrict_mono [preorder β] [has_zero β] (s : set α) {f g : α →ₛ β} (H : f ≤ g) :
  f.restrict s ≤ g.restrict s :=
if hs : is_measurable s then λ x, by simp only [coe_restrict _ hs, indicator_le_indicator (H x)]
else by simp only [restrict_of_not_measurable hs, le_refl]

section approx

section
variables [semilattice_sup_bot β] [has_zero β]

/-- Fix a sequence `i : ℕ → β`. Given a function `α → β`, its `n`-th approximation
by simple functions is defined so that in case `β = ennreal` it sends each `a` to the supremum
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
  exact (hf.preimage is_measurable_Ici)
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

lemma supr_approx_apply [topological_space β] [complete_lattice β] [order_closed_topology β] [has_zero β]
  [measurable_space β] [opens_measurable_space β]
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

/-- A sequence of `ennreal`s such that its range is the set of non-negative rational numbers. -/
def ennreal_rat_embed (n : ℕ) : ennreal :=
ennreal.of_real ((encodable.decode ℚ n).get_or_else (0 : ℚ))

lemma ennreal_rat_embed_encode (q : ℚ) :
  ennreal_rat_embed (encodable.encode q) = nnreal.of_real q :=
by rw [ennreal_rat_embed, encodable.encodek]; refl

/-- Approximate a function `α → ennreal` by a sequence of simple functions. -/
def eapprox : (α → ennreal) → ℕ → α →ₛ ennreal :=
approx ennreal_rat_embed

lemma monotone_eapprox (f : α → ennreal) : monotone (eapprox f) :=
monotone_approx _ f

lemma supr_eapprox_apply (f : α → ennreal) (hf : measurable f) (a : α) :
  (⨆n, (eapprox f n : α →ₛ ennreal) a) = f a :=
begin
  rw [eapprox, supr_approx_apply ennreal_rat_embed f a hf rfl],
  refine le_antisymm (supr_le $ assume i, supr_le $ assume hi, hi) (le_of_not_gt _),
  assume h,
  rcases ennreal.lt_iff_exists_rat_btwn.1 h with ⟨q, hq, lt_q, q_lt⟩,
  have : (nnreal.of_real q : ennreal) ≤
      (⨆ (k : ℕ) (h : ennreal_rat_embed k ≤ f a), ennreal_rat_embed k),
  { refine le_supr_of_le (encodable.encode q) _,
    rw [ennreal_rat_embed_encode q],
    refine le_supr_of_le (le_of_lt q_lt) _,
    exact le_refl _ },
  exact lt_irrefl _ (lt_of_le_of_lt this lt_q)
end

lemma eapprox_comp [measurable_space γ] {f : γ → ennreal} {g : α → γ} {n : ℕ}
  (hf : measurable f) (hg : measurable g) :
  (eapprox (f ∘ g) n : α → ennreal) = (eapprox f n : γ →ₛ ennreal) ∘ g :=
funext $ assume a, approx_comp a hf hg

end eapprox

end measurable

section measure
variables [measurable_space α] {μ : measure α}

/-- Integral of a simple function whose codomain is `ennreal`. -/
def lintegral (f : α →ₛ ennreal) (μ : measure α) : ennreal :=
∑ x in f.range, x * μ (f ⁻¹' {x})

lemma lintegral_eq_of_subset (f : α →ₛ ennreal) {s : finset ennreal}
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

/-- Calculate the integral of `(g ∘ f)`, where `g : β → ennreal` and `f : α →ₛ β`.  -/
lemma map_lintegral (g : β → ennreal) (f : α →ₛ β) :
  (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x}) :=
begin
  simp only [lintegral, range_map],
  refine finset.sum_image' _ (assume b hb, _),
  rcases mem_range.1 hb with ⟨a, rfl⟩,
  rw [map_preimage_singleton, ← sum_measure_preimage_singleton _
    (λ _ _, f.is_measurable_preimage _), finset.mul_sum],
  refine finset.sum_congr _ _,
  { congr },
  { assume x, simp only [finset.mem_filter], rintro ⟨_, h⟩, rw h },
end

lemma add_lintegral (f g : α →ₛ ennreal) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ :=
calc (f + g).lintegral μ =
      ∑ x in (pair f g).range, (x.1 * μ (pair f g ⁻¹' {x}) + x.2 * μ (pair f g ⁻¹' {x})) :
    by rw [add_eq_map₂, map_lintegral]; exact finset.sum_congr rfl (assume a ha, add_mul _ _ _)
  ... = ∑ x in (pair f g).range, x.1 * μ (pair f g ⁻¹' {x}) +
      ∑ x in (pair f g).range, x.2 * μ (pair f g ⁻¹' {x}) : by rw [finset.sum_add_distrib]
  ... = ((pair f g).map prod.fst).lintegral μ + ((pair f g).map prod.snd).lintegral μ :
    by rw [map_lintegral, map_lintegral]
  ... = lintegral f μ + lintegral g μ : rfl

lemma const_mul_lintegral (f : α →ₛ ennreal) (x : ennreal) :
  (const α x * f).lintegral μ = x * f.lintegral μ :=
calc (f.map (λa, x * a)).lintegral μ = ∑ r in f.range, x * r * μ (f ⁻¹' {r}) :
    map_lintegral _ _
  ... = ∑ r in f.range, x * (r * μ (f ⁻¹' {r})) :
    finset.sum_congr rfl (assume a ha, mul_assoc _ _ _)
  ... = x * f.lintegral μ :
    finset.mul_sum.symm

/-- Integral of a simple function `α →ₛ ennreal` as a bilinear map. -/
def lintegralₗ : (α →ₛ ennreal) →ₗ[ennreal] measure α →ₗ[ennreal] ennreal :=
{ to_fun := λ f,
  { to_fun := lintegral f,
    map_add' := by simp [lintegral, mul_add, finset.sum_add_distrib],
    map_smul' := λ c μ, by simp [lintegral, mul_left_comm _ c, finset.mul_sum] },
  map_add' := λ f g, linear_map.ext (λ μ, add_lintegral f g),
  map_smul' := λ c f, linear_map.ext (λ μ, const_mul_lintegral f c) }

@[simp] lemma zero_lintegral : (0 : α →ₛ ennreal).lintegral μ = 0 :=
linear_map.ext_iff.1 lintegralₗ.map_zero μ

lemma lintegral_add {ν} (f : α →ₛ ennreal) : f.lintegral (μ + ν) = f.lintegral μ + f.lintegral ν :=
(lintegralₗ f).map_add μ ν

lemma lintegral_smul (f : α →ₛ ennreal) (c : ennreal) :
  f.lintegral (c • μ) = c • f.lintegral μ :=
(lintegralₗ f).map_smul c μ

@[simp] lemma lintegral_zero (f : α →ₛ ennreal) :
  f.lintegral 0 = 0 :=
(lintegralₗ f).map_zero

lemma restrict_lintegral (f : α →ₛ ennreal) {s : set α} (hs : is_measurable s) :
  (restrict f s).lintegral μ = ∑ r in f.range, r * μ (f ⁻¹' {r} ∩ s) :=
calc (restrict f s).lintegral μ = ∑ r in f.range, r * μ (restrict f s ⁻¹' {r}) :
  lintegral_eq_of_subset _ $ λ x hx, if hxs : x ∈ s
    then by simp [f.restrict_apply hs, if_pos hxs, mem_range_self]
    else false.elim $ hx $ by simp [*]
... = ∑ r in f.range, r * μ (f ⁻¹' {r} ∩ s) :
  finset.sum_congr rfl $ forall_range_iff.2 $ λ b, if hb : f b = 0 then by simp only [hb, zero_mul]
    else by rw [restrict_preimage_singleton _ hs hb, inter_comm]

lemma lintegral_restrict (f : α →ₛ ennreal) (s : set α) (μ : measure α) :
  f.lintegral (measure.restrict s μ) = ∑ y in f.range, y * μ (f ⁻¹' {y} ∩ s) :=
by simp only [lintegral, measure.restrict_apply, f.is_measurable_preimage]

lemma restrict_lintegral_eq_lintegral_restrict (f : α →ₛ ennreal) {s : set α}
  (hs : is_measurable s) :
  (restrict f s).lintegral μ = f.lintegral (measure.restrict s μ) :=
by rw [f.restrict_lintegral hs, lintegral_restrict]

lemma const_lintegral (c : ennreal) : (const α c).lintegral μ = c * μ univ :=
begin
  rw [lintegral],
  by_cases ha : nonempty α,
  { resetI, simp [preimage_const_of_mem] },
  { simp [μ.eq_zero_of_not_nonempty ha] }
end

lemma const_lintegral_restrict (c : ennreal) (s : set α) :
  (const α c).lintegral (measure.restrict s μ) = c * μ s :=
by rw [const_lintegral, measure.restrict_apply is_measurable.univ, univ_inter]

lemma restrict_const_lintegral (c : ennreal) {s : set α} (hs : is_measurable s) :
  ((const α c).restrict s).lintegral μ = c * μ s :=
by rw [restrict_lintegral_eq_lintegral_restrict _ hs, const_lintegral_restrict]

lemma le_sup_lintegral (f g : α →ₛ ennreal) : f.lintegral μ ⊔ g.lintegral μ ≤ (f ⊔ g).lintegral μ :=
calc f.lintegral μ ⊔ g.lintegral μ =
      ((pair f g).map prod.fst).lintegral μ ⊔ ((pair f g).map prod.snd).lintegral μ : rfl
  ... ≤ ∑ x in (pair f g).range, (x.1 ⊔ x.2) * μ (pair f g ⁻¹' {x}) :
  begin
    rw [map_lintegral, map_lintegral],
    refine sup_le _ _;
      refine finset.sum_le_sum (λ a _, canonically_ordered_semiring.mul_le_mul _ (le_refl _)),
    exact le_sup_left,
    exact le_sup_right
  end
  ... = (f ⊔ g).lintegral μ : by rw [sup_eq_map₂, map_lintegral]

/-- `simple_func.lintegral` is monotone both in function and in measure. -/
@[mono] lemma lintegral_mono {f g : α →ₛ ennreal} (hfg : f ≤ g) {μ ν : measure α} (hμν : μ ≤ ν) :
  f.lintegral μ ≤ g.lintegral ν :=
calc f.lintegral μ ≤ f.lintegral μ ⊔ g.lintegral μ : le_sup_left
  ... ≤ (f ⊔ g).lintegral μ : le_sup_lintegral _ _
  ... = g.lintegral μ : by rw [sup_of_le_right hfg]
  ... ≤ g.lintegral ν : finset.sum_le_sum $ λ y hy, ennreal.mul_left_mono $
                          hμν _ (g.is_measurable_preimage _)

/-- `simple_func.lintegral` depends only on the measures of `f ⁻¹' {y}`. -/
lemma lintegral_eq_of_measure_preimage [measurable_space β] {f : α →ₛ ennreal} {g : β →ₛ ennreal}
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
lemma lintegral_congr {f g : α →ₛ ennreal} (h : ∀ₘ a ∂ μ, f a = g a) :
  f.lintegral μ = g.lintegral μ :=
lintegral_eq_of_measure_preimage $ λ y, measure_congr $ h.mono $ λ x hx, by simp [hx]

lemma lintegral_map {β} [measurable_space β] {μ' : measure β} (f : α →ₛ ennreal) (g : β →ₛ ennreal)
  (m : α → β) (eq : ∀a:α, f a = g (m a)) (h : ∀s:set β, is_measurable s → μ' s = μ (m ⁻¹' s)) :
  f.lintegral μ = g.lintegral μ' :=
lintegral_eq_of_measure_preimage $ λ y,
by { simp only [preimage, eq], exact (h (g ⁻¹' {y}) (g.is_measurable_preimage _)).symm }

end measure

section fin_meas_supp

variables [measurable_space α] [has_zero β] [has_zero γ] {μ : measure α}

open finset ennreal function

lemma support_eq (f : α →ₛ β) : support f = ⋃ y ∈ f.range.filter (λ y, y ≠ 0), f ⁻¹' {y} :=
set.ext $ λ x, by simp only [finset.bUnion_preimage_singleton, mem_support, set.mem_preimage,
  finset.mem_coe, mem_filter, mem_range_self, true_and]

protected def fin_meas_supp (f : α →ₛ β) (μ : measure α) : Prop :=
μ (support f) < ⊤

lemma fin_meas_supp_iff {f : α →ₛ β} {μ : measure α} :
  f.fin_meas_supp μ ↔ ∀ y ≠ 0, μ (f ⁻¹' {y}) < ⊤ :=
begin
  split,
  { refine λ h y hy, lt_of_le_of_lt (measure_mono _) h,
    exact λ x hx H, hy $ H ▸ eq.symm hx },
  { intro H,
    rw [simple_func.fin_meas_supp, support_eq],
    refine lt_of_le_of_lt (measure_bUnion_finset_le _ _) (sum_lt_top _),
    exact λ y hy, H y (finset.mem_filter.1 hy).2 }
end

namespace fin_meas_supp

protected lemma map {f : α →ₛ β} {g : β → γ} (hf : f.fin_meas_supp μ) (hg : g 0 = 0) :
  (f.map g).fin_meas_supp μ :=
flip lt_of_le_of_lt hf (measure_mono $ support_comp_subset hg f)

lemma of_map (f : α →ₛ β) {g : β → γ} (h : (f.map g).fin_meas_supp μ) (hg : ∀b, g b = 0 → b = 0) :
  f.fin_meas_supp μ :=
flip lt_of_le_of_lt h $ measure_mono $ support_subset_comp hg _

protected lemma pair {f : α →ₛ β} {g : α →ₛ γ} (hf : f.fin_meas_supp μ) (hg : g.fin_meas_supp μ) :
  (pair f g).fin_meas_supp μ :=
calc μ (support $ pair f g) = μ (support f ∪ support g) : congr_arg μ $ support_prod_mk f g
... ≤ μ (support f) + μ (support g) : measure_union_le _ _
... < _ : add_lt_top.2 ⟨hf, hg⟩

protected lemma add {β} [add_monoid β] {f g : α →ₛ β} (hf : f.fin_meas_supp μ)
  (hg : g.fin_meas_supp μ) :
  (f + g).fin_meas_supp μ :=
by { rw [add_eq_map₂], exact (hf.pair hg).map (zero_add 0) }

protected lemma mul {β} [monoid_with_zero β] {f g : α →ₛ β} (hf : f.fin_meas_supp μ)
  (hg : g.fin_meas_supp μ) :
  (f * g).fin_meas_supp μ :=
by { rw [mul_eq_map₂], exact (hf.pair hg).map (zero_mul 0) }

lemma lintegral_lt_top {f : α →ₛ ennreal} (hm : f.fin_meas_supp μ) (hf : ∀ₘ a ∂μ, f a < ⊤) :
  f.lintegral μ < ⊤ :=
begin
  refine sum_lt_top (λ a ha, _),
  rcases eq_or_lt_of_le (le_top : a ≤ ⊤) with rfl|ha,
  { simp only [ae_iff, lt_top_iff_ne_top, ne.def, not_not] at hf,
    simp [set.preimage, hf] },
  { by_cases ha0 : a = 0,
    { subst a, rwa [zero_mul] },
    { exact mul_lt_top ha (fin_meas_supp_iff.1 hm _ ha0) } }
end

lemma of_lintegral_lt_top {f : α →ₛ ennreal} (h : f.lintegral μ < ⊤) : f.fin_meas_supp μ :=
begin
  refine fin_meas_supp_iff.2 (λ b hb, _),
  rw [lintegral, sum_lt_top_iff] at h,
  by_cases b_mem : b ∈ f.range,
  { rw ennreal.lt_top_iff_ne_top,
    have h : ¬ _ = ⊤ := ennreal.lt_top_iff_ne_top.1 (h b b_mem),
    simp only [mul_eq_top, not_or_distrib, not_and_distrib] at h,
    rcases h with ⟨h, h'⟩,
    refine or.elim h (λh, by contradiction) (λh, h) },
  { rw ← preimage_eq_empty_iff at b_mem,
    rw [b_mem, measure_empty],
    exact with_top.zero_lt_top }
end

end fin_meas_supp

end fin_meas_supp

end simple_func

section lintegral
open simple_func
variables [measurable_space α] {μ : measure α}

/-- The lower Lebesgue integral of a function `f` with respect to a measure `μ`. -/
def lintegral (μ : measure α) (f : α → ennreal) : ennreal :=
⨆ (g : α →ₛ ennreal) (hf : ⇑g ≤ f), g.lintegral μ

notation `∫⁻` binders ` in ` s `, ` r:(scoped:67 f, f) ` ∂ ` μ:50 :=
  lintegral (measure.restrict s μ) r
notation `∫⁻` binders ` in ` s `, ` r:(scoped:67 f, lintegral (measure.restrict s volume) f) := r

notation `∫⁻` binders `, ` r:(scoped:67 f, f) ` ∂ ` μ:50 := lintegral μ r
notation `∫⁻` binders `, ` r:(scoped:67 f, lintegral volume f) := r

theorem simple_func.lintegral_eq_lintegral (f : α →ₛ ennreal) (μ : measure α) :
  ∫⁻ a, f a ∂ μ = f.lintegral μ :=
le_antisymm
  (bsupr_le $ λ g hg, lintegral_mono hg $ le_refl _)
  (le_supr_of_le f $ le_supr_of_le (le_refl _) (le_refl _))

@[mono] lemma lintegral_mono ⦃μ ν : measure α⦄ (hμν : μ ≤ ν) ⦃f g : α →ₛ ennreal⦄ (hfg : f ≤ g) :
  ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂ν :=
supr_le_supr $ λ φ, supr_le_supr2 $ λ hφ, ⟨le_trans hφ hfg, lintegral_mono (le_refl φ) hμν⟩

/-- `∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`φ : α →ₛ ennreal` such that `φ ≤ f`. This lemma says that it suffices to take
functions `φ : α →ₛ ℝ≥0`. -/
lemma lintegral_eq_nnreal (f : α → ennreal) (μ : measure α) :
  (∫⁻ a, f a ∂μ) = (⨆ (φ : α →ₛ ℝ≥0) (hf : ∀ x, ↑(φ x) ≤ f x),
      (φ.map (coe : nnreal → ennreal)).lintegral μ) :=
begin
  refine le_antisymm
    (bsupr_le $ assume φ hφ, _)
    (supr_le_supr2 $ λ φ, ⟨φ.map (coe : ℝ≥0 → ennreal), le_refl _⟩),
  by_cases h : ∀ₘ a ∂μ, φ a ≠ ⊤,
  { let ψ := φ.map ennreal.to_nnreal,
    replace h : ψ.map (coe : ℝ≥0 → ennreal) =ᶠ[μ.ae] φ :=
      h.mono (λ a, ennreal.coe_to_nnreal),
    have : ∀ x, ↑(ψ x) ≤ f x := λ x, le_trans ennreal.coe_to_nnreal_le_self (hφ x),
    exact le_supr_of_le (φ.map ennreal.to_nnreal)
      (le_supr_of_le this (ge_of_eq $ lintegral_congr h)) },
  { have h_meas : μ (φ ⁻¹' {⊤}) ≠ 0, from mt measure_zero_iff_ae_nmem.1 h,
    refine le_trans le_top (ge_of_eq $ (supr_eq_top _).2 $ λ b hb, _),
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b < n * μ (φ ⁻¹' {⊤}), from exists_nat_mul_gt h_meas (ne_of_lt hb),
    use (const α (n : ℝ≥0)).restrict (φ ⁻¹' {⊤}),
    simp only [lt_supr_iff, exists_prop, coe_restrict, φ.is_measurable_preimage],
    
    -- { have : (b + 1) / μ (φ ⁻¹' {⊤}) ≠ ⊤ :=
    --     ennreal.mul_ne_top (add_ne_top.2 ⟨ne_of_lt hb, one_ne_top⟩) (inv_ne_top.2 h_meas),
      
    -- },
    let n : ℕ → (α →ₛ nnreal) := λn, restrict (const α (n : nnreal)) (s ⁻¹' {⊤}),
    have n_le_s : ∀i, (n i).map c ≤ s,
    { assume i a,
      dsimp [n, c],
      rw [restrict_apply _ (s.preimage_measurable _)],
      split_ifs with ha,
      { simp at ha, exact ha.symm ▸ le_top },
      { exact zero_le _ } },
    have approx_s : ∀ (i : ℕ), ↑i * volume {a : α | s a = ⊤} ≤ integral (map c (n i)),
    { assume i,
      have : {a : α | s a = ⊤} = s ⁻¹' {⊤} := rfl,
      rw [this, ← restrict_const_integral _ _ (s.preimage_measurable _)],
      { refine integral_le_integral _ _ (assume a, le_of_eq _),
        simp [n, c, restrict_apply, s.preimage_measurable],
        split_ifs; simp [ennreal.coe_nat] },
     },
    calc s.integral ≤ ⊤ : le_top
      ... = (⨆i:ℕ, (i : ennreal) * volume {a | s a = ⊤}) :
        by rw [← ennreal.supr_mul, ennreal.supr_coe_nat, ennreal.top_mul, if_neg h_vol_s]
      ... ≤ (⨆i, ((n i).map c).integral) : supr_le_supr approx_s
      ... ≤ ⨆ (s : α →ₛ nnreal) (hf : f ≥ s.map c), (s.map c).integral :
        have ∀i, ((n i).map c : α → ennreal) ≤ f := assume i, le_trans (n_le_s i) hs,
        (supr_le $ assume i, le_supr_of_le (n i) (le_supr (λh, ((n i).map c).integral) (this i))) }
end

theorem supr_lintegral_le {ι : Sort*} (f : ι → α → ennreal) :
  (⨆i, ∫⁻ a, f i a) ≤ (∫⁻ a, ⨆i, f i a) :=
by { simp only [← supr_apply], exact (monotone_lintegral α).le_map_supr }

theorem supr2_lintegral_le {ι : Sort*} {ι' : ι → Sort*} (f : Π i, ι' i → α → ennreal) :
  (⨆i (h : ι' i), ∫⁻ a, f i h a) ≤ (∫⁻ a, ⨆i (h : ι' i), f i h a) :=
by { convert (monotone_lintegral α).le_map_supr2 f, ext1 a, simp only [supr_apply] }

theorem le_infi_lintegral {ι : Sort*} (f : ι → α → ennreal) :
  (∫⁻ a, ⨅i, f i a) ≤ (⨅i, ∫⁻ a, f i a) :=
by { simp only [← infi_apply], exact (monotone_lintegral α).map_infi_le }

theorem le_infi2_lintegral {ι : Sort*} {ι' : ι → Sort*} (f : Π i, ι' i → α → ennreal) :
  (∫⁻ a, ⨅ i (h : ι' i), f i h a) ≤ (⨅ i (h : ι' i), ∫⁻ a, f i h a) :=
by { convert (monotone_lintegral α).map_infi2_le f, ext1 a, simp only [infi_apply] }

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence.

See `lintegral_supr_directed` for a more general form. -/
theorem lintegral_supr
  {f : ℕ → α → ennreal} (hf : ∀n, measurable (f n)) (h_mono : monotone f) :
  (∫⁻ a, ⨆n, f n a) = (⨆n, ∫⁻ a, f n a) :=
begin
  set c : nnreal → ennreal := coe,
  set F := λ a:α, ⨆n, f n a,
  have hF : measurable F := measurable_supr hf,
  refine le_antisymm _ (supr_lintegral_le _),
  rw [lintegral_eq_nnreal],
  refine supr_le (assume s, supr_le (assume hsf, _)),
  refine ennreal.le_of_forall_lt_one_mul_lt (assume a ha, _),
  rcases ennreal.lt_iff_exists_coe.1 ha with ⟨r, rfl, ha⟩,
  have ha : r < 1 := ennreal.coe_lt_coe.1 ha,
  let rs := s.map (λa, r * a),
  have eq_rs : (const α r : α →ₛ ennreal) * map c s = rs.map c,
  { ext1 a, exact ennreal.coe_mul.symm },
  have eq : ∀p, (rs.map c) ⁻¹' {p} = (⋃n, (rs.map c) ⁻¹' {p} ∩ {a | p ≤ f n a}),
  { assume p,
    rw [← inter_Union, ← inter_univ ((map c rs) ⁻¹' {p})] {occs := occurrences.pos [1]},
    refine set.ext (assume x, and_congr_right $ assume hx, (true_iff _).2 _),
    by_cases p_eq : p = 0, { simp [p_eq] },
    simp at hx, subst hx,
    have : r * s x ≠ 0, { rwa [(≠), ← ennreal.coe_eq_zero] },
    have : s x ≠ 0, { refine mt _ this, assume h, rw [h, mul_zero] },
    have : (rs.map c) x < ⨆ (n : ℕ), f n x,
    { refine lt_of_lt_of_le (ennreal.coe_lt_coe.2 (_)) (hsf x),
      suffices : r * s x < 1 * s x, simpa [rs],
      exact mul_lt_mul_of_pos_right ha (zero_lt_iff_ne_zero.2 this) },
    rcases lt_supr_iff.1 this with ⟨i, hi⟩,
    exact mem_Union.2 ⟨i, le_of_lt hi⟩ },
  have mono : ∀r:ennreal, monotone (λn, (rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}),
  { assume r i j h,
    refine inter_subset_inter (subset.refl _) _,
    assume x hx, exact le_trans hx (h_mono h x) },
  have h_meas : ∀n, is_measurable {a : α | ⇑(map c rs) a ≤ f n a} :=
    assume n, is_measurable_le (simple_func.measurable _) (hf n),
  calc (r:ennreal) * integral (s.map c) = ∑ r in (rs.map c).range, r * volume ((rs.map c) ⁻¹' {r}) :
      by rw [← const_mul_integral, integral, eq_rs]
    ... ≤ ∑ r in (rs.map c).range, r * volume (⋃n, (rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}) :
      le_of_eq (finset.sum_congr rfl $ assume x hx, by rw ← eq)
    ... ≤ ∑ r in (rs.map c).range, (⨆n, r * volume ((rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a})) :
      le_of_eq (finset.sum_congr rfl $ assume x hx,
        begin
          rw [measure_Union_eq_supr_nat _ (mono x), ennreal.mul_supr],
          { assume i,
            refine ((rs.map c).preimage_measurable _).inter _,
            exact (hf i).preimage is_measurable_Ici }
        end)
    ... ≤ ⨆n, ∑ r in (rs.map c).range, r * volume ((rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}) :
      begin
        refine le_of_eq _,
        rw [ennreal.finset_sum_supr_nat],
        assume p i j h,
        exact canonically_ordered_semiring.mul_le_mul (le_refl _) (measure_mono $ mono p h)
      end
    ... ≤ (⨆n:ℕ, ((rs.map c).restrict {a | (rs.map c) a ≤ f n a}).integral) :
    begin
      refine supr_le_supr (assume n, _),
      rw [restrict_integral _ _ (h_meas n)],
      { refine le_of_eq (finset.sum_congr rfl $ assume r hr, _),
        congr' 2,
        ext a,
        refine and_congr_right _,
        simp {contextual := tt} }
    end
    ... ≤ (⨆n, ∫⁻ a, f n a) :
    begin
      refine supr_le_supr (assume n, _),
      rw [← simple_func.lintegral_eq_integral],
      refine lintegral_mono (assume a, _),
      dsimp,
      rw [restrict_apply],
      split_ifs; simp, simpa using h,
      exact h_meas n
    end
end

lemma lintegral_eq_supr_eapprox_integral {f : α → ennreal} (hf : measurable f) :
  (∫⁻ a, f a) = (⨆n, (eapprox f n).integral) :=
calc (∫⁻ a, f a) = (∫⁻ a, ⨆n, (eapprox f n : α → ennreal) a) :
   by congr; ext a; rw [supr_eapprox_apply f hf]
 ... = (⨆n, ∫⁻ a, (eapprox f n : α → ennreal) a) :
 begin
   rw [lintegral_supr],
   { assume n, exact (eapprox f n).measurable },
   { assume i j h, exact (monotone_eapprox f h) }
 end
 ... = (⨆n, (eapprox f n).integral) : by congr; ext n; rw [(eapprox f n).lintegral_eq_integral]

lemma lintegral_add {f g : α → ennreal} (hf : measurable f) (hg : measurable g) :
  (∫⁻ a, f a + g a) = (∫⁻ a, f a) + (∫⁻ a, g a) :=
calc (∫⁻ a, f a + g a) =
    (∫⁻ a, (⨆n, (eapprox f n : α → ennreal) a) + (⨆n, (eapprox g n : α → ennreal) a)) :
    by congr; funext a; rw [supr_eapprox_apply f hf, supr_eapprox_apply g hg]
  ... = (∫⁻ a, (⨆n, (eapprox f n + eapprox g n : α → ennreal) a)) :
  begin
    congr, funext a,
    rw [ennreal.supr_add_supr_of_monotone], { refl },
    { assume i j h, exact monotone_eapprox _ h a },
    { assume i j h, exact monotone_eapprox _ h a },
  end
  ... = (⨆n, (eapprox f n).integral + (eapprox g n).integral) :
  begin
    rw [lintegral_supr],
    { congr, funext n, rw [← simple_func.add_integral, ← simple_func.lintegral_eq_integral], refl },
    { assume n, exact measurable.add (eapprox f n).measurable (eapprox g n).measurable },
    { assume i j h a, exact add_le_add (monotone_eapprox _ h _) (monotone_eapprox _ h _) }
  end
  ... = (⨆n, (eapprox f n).integral) + (⨆n, (eapprox g n).integral) :
  by refine (ennreal.supr_add_supr_of_monotone _ _).symm;
     { assume i j h, exact simple_func.integral_le_integral _ _ (monotone_eapprox _ h) }
  ... = (∫⁻ a, f a) + (∫⁻ a, g a) :
    by rw [lintegral_eq_supr_eapprox_integral hf, lintegral_eq_supr_eapprox_integral hg]

@[simp] lemma lintegral_zero : (∫⁻ a:α, 0) = 0 :=
show (∫⁻ a:α, (0 : α →ₛ ennreal) a) = 0, by rw [simple_func.lintegral_eq_integral, zero_integral]

lemma lintegral_finset_sum (s : finset β) {f : β → α → ennreal} (hf : ∀b, measurable (f b)) :
  (∫⁻ a, ∑ b in s, f b a) = ∑ b in s, ∫⁻ a, f b a :=
begin
  refine finset.induction_on s _ _,
  { simp },
  { assume a s has ih,
    simp only [finset.sum_insert has],
    rw [lintegral_add (hf _) (s.measurable_sum hf), ih] }
end

lemma lintegral_const_mul (r : ennreal) {f : α → ennreal} (hf : measurable f) :
  (∫⁻ a, r * f a) = r * (∫⁻ a, f a) :=
calc (∫⁻ a, r * f a) = (∫⁻ a, (⨆n, (const α r * eapprox f n) a)) :
    by { congr, funext a, rw [← supr_eapprox_apply f hf, ennreal.mul_supr], refl }
  ... = (⨆n, r * (eapprox f n).integral) :
  begin
    rw [lintegral_supr],
    { congr, funext n, rw [← simple_func.const_mul_integral, ← simple_func.lintegral_eq_integral] },
    { assume n, dsimp, exact simple_func.measurable _ },
    { assume i j h a, exact canonically_ordered_semiring.mul_le_mul (le_refl _)
        (monotone_eapprox _ h _) }
  end
  ... = r * (∫⁻ a, f a) : by rw [← ennreal.mul_supr, lintegral_eq_supr_eapprox_integral hf]

lemma lintegral_const_mul_le (r : ennreal) (f : α → ennreal) : r * (∫⁻ a, f a) ≤ (∫⁻ a, r * f a) :=
begin
  rw [lintegral, ennreal.mul_supr],
  refine supr_le (λs, _),
  rw [ennreal.mul_supr],
  simp only [supr_le_iff, ge_iff_le],
  assume hs,
  rw ← simple_func.const_mul_integral,
  refine le_supr_of_le (const α r * s) (le_supr_of_le (λx, _) (le_refl _)),
  exact canonically_ordered_semiring.mul_le_mul (le_refl _) (hs x)
end

lemma lintegral_const_mul' (r : ennreal) (f : α → ennreal) (hr : r ≠ ⊤) :
  (∫⁻ a, r * f a) = r * (∫⁻ a, f a) :=
begin
  by_cases h : r = 0,
  { simp [h] },
  apply le_antisymm _ (lintegral_const_mul_le r f),
  have rinv : r * r⁻¹  = 1 := ennreal.mul_inv_cancel h hr,
  have rinv' : r ⁻¹ * r = 1, by { rw mul_comm, exact rinv },
  have := lintegral_const_mul_le (r⁻¹) (λx, r * f x),
  simp [(mul_assoc _ _ _).symm, rinv'] at this,
  simpa [(mul_assoc _ _ _).symm, rinv]
    using canonically_ordered_semiring.mul_le_mul (le_refl r) this
end

lemma lintegral_supr_const (r : ennreal) {s : set α} (hs : is_measurable s) :
  (∫⁻ a, ⨆(h : a ∈ s), r) = r * volume s :=
begin
  rw [← restrict_const_integral r s hs, ← (restrict (const α r) s).lintegral_eq_integral],
  congr; ext a; by_cases a ∈ s; simp [h, hs]
end

lemma lintegral_le_lintegral_ae {f g : α → ennreal} (h : ∀ₘ a, f a ≤ g a) :
  (∫⁻ a, f a) ≤ (∫⁻ a, g a) :=
begin
  rcases exists_is_measurable_superset_of_measure_eq_zero h with ⟨t, hts, ht, ht0⟩,
  have : tᶜ ∈ (@volume α _).ae,
  { rw [mem_ae_iff, compl_compl, ht0] },
  refine (supr_le $ assume s, supr_le $ assume hfs,
    le_supr_of_le (s.restrict tᶜ) $ le_supr_of_le _ _),
  { assume a,
    by_cases a ∈ t;
      simp [h, restrict_apply, ht.compl],
    exact le_trans (hfs a) (by_contradiction $ assume hnfg, h (hts hnfg)) },
  { refine le_of_eq (s.integral_congr _ _),
    filter_upwards [this],
    refine assume a hnt, _,
    by_cases hat : a ∈ t; simp [hat, ht.compl],
    exact (hnt hat).elim }
end

lemma lintegral_congr_ae {f g : α → ennreal} (h : ∀ₘ a, f a = g a) :
  (∫⁻ a, f a) = (∫⁻ a, g a) :=
le_antisymm
  (lintegral_le_lintegral_ae $ h.mono $ assume a h, le_of_eq h)
  (lintegral_le_lintegral_ae $ h.mono $ assume a h, le_of_eq h.symm)

lemma lintegral_congr {f g : α → ennreal} (h : ∀ a, f a = g a) :
  (∫⁻ a, f a) = (∫⁻ a, g a) :=
by simp only [h]

-- TODO: Need a better way of rewriting inside of a integral
lemma lintegral_rw₁ {f f' : α → β} (h : ∀ₘ a, f a = f' a) (g : β → ennreal) :
  (∫⁻ a, g (f a)) = (∫⁻ a, g (f' a)) :=
lintegral_congr_ae $ h.mono $ λ a h, by rw h

-- TODO: Need a better way of rewriting inside of a integral
lemma lintegral_rw₂ {f₁ f₁' : α → β} {f₂ f₂' : α → γ} (h₁ : ∀ₘ a, f₁ a = f₁' a)
  (h₂ : ∀ₘ a, f₂ a = f₂' a) (g : β → γ → ennreal) :
  (∫⁻ a, g (f₁ a) (f₂ a)) = (∫⁻ a, g (f₁' a) (f₂' a)) :=
lintegral_congr_ae $ h₁.mp $ h₂.mono $ λ _ h₂ h₁, by rw [h₁, h₂]

lemma simple_func.lintegral_map (f : α →ₛ β) (g : β → ennreal) :
  (∫⁻ a, (f.map g) a) = ∫⁻ a, g (f a) :=
by simp only [map_apply]

/-- Chebyshev's inequality -/
lemma mul_volume_ge_le_lintegral {f : α → ennreal} (hf : measurable f) (ε : ennreal) :
  ε * volume {x | ε ≤ f x} ≤ ∫⁻ a, f a :=
begin
  have : is_measurable {a : α | ε ≤ f a }, from hf.preimage is_measurable_Ici,
  rw [← simple_func.restrict_const_integral _ _ this, ← simple_func.lintegral_eq_integral],
  refine lintegral_mono (λ a, _),
  simp only [restrict_apply _ this],
  split_ifs; [assumption, exact zero_le _]
end

lemma volume_ge_le_lintegral_div {f : α → ennreal} (hf : measurable f) {ε : ennreal}
  (hε : ε ≠ 0) (hε' : ε ≠ ⊤) :
  volume {x | ε ≤ f x} ≤ (∫⁻ a, f a) / ε :=
(ennreal.le_div_iff_mul_le (or.inl hε) (or.inl hε')).2 $
by { rw [mul_comm], exact mul_volume_ge_le_lintegral hf ε }

lemma lintegral_eq_zero_iff {f : α → ennreal} (hf : measurable f) :
  lintegral f = 0 ↔ (∀ₘ a, f a = 0) :=
begin
  refine iff.intro (assume h, _) (assume h, _),
  { have : ∀n:ℕ, ∀ₘ a, f a < n⁻¹,
    { assume n,
      rw [ae_iff, ← le_zero_iff_eq, ← @ennreal.zero_div n⁻¹,
        ennreal.le_div_iff_mul_le, mul_comm],
      simp only [not_lt],
      -- TODO: why `rw ← h` fails with "not an equality or an iff"?
      exacts [h ▸ mul_volume_ge_le_lintegral hf n⁻¹,
        or.inl (ennreal.inv_ne_zero.2 ennreal.coe_nat_ne_top),
        or.inr ennreal.zero_ne_top] },
    refine (ae_all_iff.2 this).mono (λ a ha, _),
    by_contradiction h,
    rcases ennreal.exists_inv_nat_lt h with ⟨n, hn⟩,
    exact (lt_irrefl _ $ lt_trans hn $ ha n).elim },
  { calc lintegral f = lintegral (λa:α, 0) : lintegral_congr_ae h
      ... = 0 : lintegral_zero }
end

/-- Weaker version of the monotone convergence theorem-/
lemma lintegral_supr_ae {f : ℕ → α → ennreal} (hf : ∀n, measurable (f n))
  (h_mono : ∀n, ∀ₘ a, f n a ≤ f n.succ a) :
  (∫⁻ a, ⨆n, f n a) = (⨆n, ∫⁻ a, f n a) :=
let ⟨s, hs⟩ := exists_is_measurable_superset_of_measure_eq_zero
                       (ae_iff.1 (ae_all_iff.2 h_mono)) in
let g := λ n a, if a ∈ s then 0 else f n a in
have g_eq_f : ∀ₘ a, ∀n, g n a = f n a,
  begin
    have := hs.2.2, rw [← compl_compl s] at this,
    filter_upwards [(mem_ae_iff sᶜ).2 this] assume a ha n, if_neg ha
  end,
calc
  (∫⁻ a, ⨆n, f n a) = (∫⁻ a, ⨆n, g n a) :
  lintegral_congr_ae
    begin
      filter_upwards [g_eq_f], assume a ha, congr, funext, exact (ha n).symm
    end
  ... = ⨆n, (∫⁻ a, g n a) :
  lintegral_supr
    (assume n, measurable.if hs.2.1 measurable_const (hf n))
    (monotone_of_monotone_nat $ assume n a,  classical.by_cases
      (assume h : a ∈ s, by simp [g, if_pos h])
      (assume h : a ∉ s,
      begin
        simp only [g, if_neg h], have := hs.1, rw subset_def at this, have := mt (this a) h,
        simp only [not_not, mem_set_of_eq] at this, exact this n
      end))
  ... = ⨆n, (∫⁻ a, f n a) :
  begin
    congr, funext, apply lintegral_congr_ae, filter_upwards [g_eq_f] assume a ha, ha n
  end

lemma lintegral_sub {f g : α → ennreal} (hf : measurable f) (hg : measurable g)
  (hg_fin : lintegral g < ⊤) (h_le : ∀ₘ a, g a ≤ f a) :
  (∫⁻ a, f a - g a) = (∫⁻ a, f a) - (∫⁻ a, g a) :=
begin
  rw [← ennreal.add_left_inj hg_fin,
        ennreal.sub_add_cancel_of_le (lintegral_le_lintegral_ae h_le),
      ← lintegral_add (hf.ennreal_sub hg) hg],
  show  (∫⁻ (a : α), f a - g a + g a) = ∫⁻ (a : α), f a,
  apply lintegral_congr_ae, filter_upwards [h_le], simp only [add_comm, mem_set_of_eq],
  assume a ha, exact ennreal.add_sub_cancel_of_le ha
end

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
lemma lintegral_infi_ae
  {f : ℕ → α → ennreal} (h_meas : ∀n, measurable (f n))
  (h_mono : ∀n:ℕ, ∀ₘ a, f n.succ a ≤ f n a) (h_fin : lintegral (f 0) < ⊤) :
  (∫⁻ a, ⨅n, f n a) = (⨅n, ∫⁻ a, f n a) :=
have fn_le_f0 : (∫⁻ a, ⨅n, f n a) ≤ lintegral (f 0), from
  lintegral_mono (assume a, infi_le_of_le 0 (le_refl _)),
have fn_le_f0' : (⨅n, ∫⁻ a, f n a) ≤ lintegral (f 0), from infi_le_of_le 0 (le_refl _),
(ennreal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1 $
show lintegral (f 0) - (∫⁻ a, ⨅n, f n a) = lintegral (f 0) - (⨅n, ∫⁻ a, f n a), from
calc
  lintegral (f 0) - (∫⁻ a, ⨅n, f n a) = ∫⁻ a, f 0 a - ⨅n, f n a :
    (lintegral_sub (h_meas 0) (measurable_infi h_meas)
    (calc
      (∫⁻ a, ⨅n, f n a)  ≤ lintegral (f 0) : lintegral_mono (assume a, infi_le _ _)
          ... < ⊤ : h_fin  )
    (ae_of_all _ $ assume a, infi_le _ _)).symm
  ... = ∫⁻ a, ⨆n, f 0 a - f n a : congr rfl (funext (assume a, ennreal.sub_infi))
  ... = ⨆n, ∫⁻ a, f 0 a - f n a :
    lintegral_supr_ae
      (assume n, (h_meas 0).ennreal_sub (h_meas n))
      (assume n, by
        filter_upwards [h_mono n] assume a ha, ennreal.sub_le_sub (le_refl _) ha)
  ... = ⨆n, lintegral (f 0) - ∫⁻ a, f n a :
    have h_mono : ∀ₘ a, ∀n:ℕ, f n.succ a ≤ f n a := ae_all_iff.2 h_mono,
    have h_mono : ∀n, ∀ₘa, f n a ≤ f 0 a := assume n,
    begin
      filter_upwards [h_mono], simp only [mem_set_of_eq], assume a, assume h, induction n with n ih,
      {exact le_refl _}, {exact le_trans (h n) ih}
    end,
    congr rfl (funext $ assume n, lintegral_sub (h_meas _) (h_meas _)
      (calc
        (∫⁻ a, f n a) ≤ ∫⁻ a, f 0 a : lintegral_le_lintegral_ae $ h_mono n
        ... < ⊤ : h_fin)
        (h_mono n))
  ... = lintegral (f 0) - (⨅n, ∫⁻ a, f n a) : ennreal.sub_infi.symm

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
lemma lintegral_infi
  {f : ℕ → α → ennreal} (h_meas : ∀n, measurable (f n))
  (h_mono : ∀ ⦃m n⦄, m ≤ n → f n ≤ f m) (h_fin : lintegral (f 0) < ⊤) :
  (∫⁻ a, ⨅n, f n a) = (⨅n, ∫⁻ a, f n a) :=
lintegral_infi_ae h_meas (λ n, ae_of_all _ $ h_mono $ le_of_lt n.lt_succ_self) h_fin

section priority
-- for some reason the next proof fails without changing the priority of this instance
local attribute [instance, priority 1000] classical.prop_decidable
/-- Known as Fatou's lemma -/
lemma lintegral_liminf_le {f : ℕ → α → ennreal} (h_meas : ∀n, measurable (f n)) :
  (∫⁻ a, liminf at_top (λ n, f n a)) ≤ liminf at_top (λ n, lintegral (f n)) :=
calc
  (∫⁻ a, liminf at_top (λ n, f n a)) = ∫⁻ a, ⨆n:ℕ, ⨅i≥n, f i a :
     by simp only [liminf_eq_supr_infi_of_nat]
  ... = ⨆n:ℕ, ∫⁻ a, ⨅i≥n, f i a :
    lintegral_supr
      (assume n, measurable_binfi _ h_meas)
      (assume n m hnm a, infi_le_infi_of_subset $ λ i hi, le_trans hnm hi)
  ... ≤ ⨆n:ℕ, ⨅i≥n, lintegral (f i) :
    supr_le_supr $ λ n, le_infi2_lintegral _
  ... = liminf at_top (λ n, lintegral (f n)) : liminf_eq_supr_infi_of_nat.symm
end priority

lemma limsup_lintegral_le {f : ℕ → α → ennreal} {g : α → ennreal}
  (hf_meas : ∀ n, measurable (f n)) (h_bound : ∀n, ∀ₘa, f n a ≤ g a) (h_fin : lintegral g < ⊤) :
  limsup at_top (λn, lintegral (f n)) ≤ ∫⁻ a, limsup at_top (λn, f n a) :=
calc
  limsup at_top (λn, lintegral (f n)) = ⨅n:ℕ, ⨆i≥n, lintegral (f i) :
    limsup_eq_infi_supr_of_nat
  ... ≤ ⨅n:ℕ, ∫⁻ a, ⨆i≥n, f i a :
    infi_le_infi $ assume n, supr2_lintegral_le _
  ... = ∫⁻ a, ⨅n:ℕ, ⨆i≥n, f i a :
    begin
      refine (lintegral_infi _ _ _).symm,
      { assume n, exact measurable_bsupr _ hf_meas },
      { assume n m hnm a, exact (supr_le_supr_of_subset $ λ i hi, le_trans hnm hi) },
      { refine lt_of_le_of_lt (lintegral_le_lintegral_ae _) h_fin,
        refine (ae_all_iff.2 h_bound).mono (λ n hn, _),
        exact supr_le (λ i, supr_le $ λ hi, hn i) }
    end
  ... = ∫⁻ a, limsup at_top (λn, f n a) :
    by simp only [limsup_eq_infi_supr_of_nat]

/-- Dominated convergence theorem for nonnegative functions -/
lemma tendsto_lintegral_of_dominated_convergence
  {F : ℕ → α → ennreal} {f : α → ennreal} (bound : α → ennreal)
  (hF_meas : ∀n, measurable (F n)) (h_bound : ∀n, ∀ₘ a, F n a ≤ bound a)
  (h_fin : lintegral bound < ⊤)
  (h_lim : ∀ₘ a, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, lintegral (F n)) at_top (𝓝 (lintegral f)) :=
begin
  have limsup_le_lintegral :=
  calc
    limsup at_top (λ (n : ℕ), lintegral (F n)) ≤ ∫⁻ (a : α), limsup at_top (λn, F n a) :
      limsup_lintegral_le hF_meas h_bound h_fin
    ... = lintegral f :
      lintegral_congr_ae $
          by filter_upwards [h_lim] assume a h, limsup_eq_of_tendsto at_top_ne_bot h,
  have lintegral_le_liminf :=
  calc
    lintegral f = ∫⁻ (a : α), liminf at_top (λ (n : ℕ), F n a) :
      lintegral_congr_ae $
      by filter_upwards [h_lim] assume a h, (liminf_eq_of_tendsto at_top_ne_bot h).symm
    ... ≤ liminf at_top (λ n, lintegral (F n)) :
      lintegral_liminf_le hF_meas,
  have liminf_eq_limsup :=
    le_antisymm
      (liminf_le_limsup (map_ne_bot at_top_ne_bot))
      (le_trans limsup_le_lintegral lintegral_le_liminf),
  have liminf_eq_lintegral : liminf at_top (λ n, lintegral (F n)) = lintegral f :=
    le_antisymm (by convert limsup_le_lintegral) lintegral_le_liminf,
  have limsup_eq_lintegral : limsup at_top (λ n, lintegral (F n)) = lintegral f :=
    le_antisymm
      limsup_le_lintegral
      begin convert lintegral_le_liminf, exact liminf_eq_limsup.symm end,
  exact tendsto_of_liminf_eq_limsup ⟨liminf_eq_lintegral, limsup_eq_lintegral⟩
end

/-- Dominated convergence theorem for filters with a countable basis -/
lemma tendsto_lintegral_filter_of_dominated_convergence {ι} {l : filter ι}
  {F : ι → α → ennreal} {f : α → ennreal} (bound : α → ennreal)
  (hl_cb : l.is_countably_generated)
  (hF_meas : ∀ᶠ n in l, measurable (F n))
  (h_bound : ∀ᶠ n in l, ∀ₘ a, F n a ≤ bound a)
  (h_fin : lintegral bound < ⊤)
  (h_lim : ∀ₘ a, tendsto (λ n, F n a) l (nhds (f a))) :
  tendsto (λn, lintegral (F n)) l (nhds (lintegral f)) :=
begin
  rw hl_cb.tendsto_iff_seq_tendsto,
  { intros x xl,
    have hxl, { rw tendsto_at_top' at xl, exact xl },
    have h := inter_mem_sets hF_meas h_bound,
    replace h := hxl _ h,
    rcases h with ⟨k, h⟩,
    rw ← tendsto_add_at_top_iff_nat k,
    refine tendsto_lintegral_of_dominated_convergence _ _ _ _ _,
    { exact bound },
    { intro, refine (h _ _).1, exact nat.le_add_left _ _ },
    { intro, refine (h _ _).2, exact nat.le_add_left _ _ },
    { assumption },
    { filter_upwards [h_lim],
      simp only [mem_set_of_eq],
      assume a h_lim,
      apply @tendsto.comp _ _ _ (λn, x (n + k)) (λn, F n a),
      { assumption },
      rw tendsto_add_at_top_iff_nat,
      assumption } },
end

section
open encodable

/-- Monotone convergence for a suprema over a directed family and indexed by an encodable type -/
theorem lintegral_supr_directed [encodable β] {f : β → α → ennreal}
  (hf : ∀b, measurable (f b)) (h_directed : directed (≤) f) :
  (∫⁻ a, ⨆b, f b a) = (⨆b, ∫⁻ a, f b a) :=
begin
  by_cases hβ : ¬ nonempty β,
  { have : ∀f : β → ennreal, (⨆(b : β), f b) = 0 :=
      assume f, supr_eq_bot.2 (assume b, (hβ ⟨b⟩).elim),
    simp [this] },
  cases of_not_not hβ with b,
  haveI iβ : inhabited β := ⟨b⟩, clear hβ b,
  have : ∀a, (⨆ b, f b a) = (⨆ n, f (h_directed.sequence f n) a),
  { assume a,
    refine le_antisymm (supr_le $ assume b, _) (supr_le $ assume n, le_supr (λn, f n a) _),
    exact le_supr_of_le (encode b + 1) (h_directed.le_sequence b a) },
  calc (∫⁻ a, ⨆ b, f b a) = (∫⁻ a, ⨆ n, f (h_directed.sequence f n) a) :
      by simp only [this]
    ... = (⨆ n, ∫⁻ a, f (h_directed.sequence f n) a) :
      lintegral_supr (assume n, hf _) h_directed.sequence_mono
    ... = (⨆ b, ∫⁻ a, f b a) :
    begin
      refine le_antisymm (supr_le $ assume n, _) (supr_le $ assume b, _),
      { exact le_supr (λb, lintegral (f b)) _ },
      { exact le_supr_of_le (encode b + 1)
          (lintegral_mono $ h_directed.le_sequence b) }
    end
end

end

lemma lintegral_tsum [encodable β] {f : β → α → ennreal} (hf : ∀i, measurable (f i)) :
  (∫⁻ a, ∑' i, f i a) = (∑' i, ∫⁻ a, f i a) :=
begin
  simp only [ennreal.tsum_eq_supr_sum],
  rw [lintegral_supr_directed],
  { simp [lintegral_finset_sum _ hf] },
  { assume b, exact finset.measurable_sum _ hf },
  { assume s t,
    use [s ∪ t],
    split,
    exact assume a, finset.sum_le_sum_of_subset (finset.subset_union_left _ _),
    exact assume a, finset.sum_le_sum_of_subset (finset.subset_union_right _ _) }
end

end lintegral

namespace measure

def integral [measurable_space α] (m : measure α) (f : α → ennreal) : ennreal :=
@lintegral α { volume := m } f

variables [measurable_space α] {m : measure α}

@[simp] lemma integral_zero : m.integral (λa, 0) = 0 := @lintegral_zero α { volume := m }

lemma integral_map [measurable_space β] {f : β → ennreal} {g : α → β}
  (hf : measurable f) (hg : measurable g) : (map g m).integral f = m.integral (f ∘ g) :=
begin
  rw [integral, integral, lintegral_eq_supr_eapprox_integral, lintegral_eq_supr_eapprox_integral],
  { congr, funext n, symmetry,
    apply simple_func.integral_map,
    { assume a, exact congr_fun (simple_func.eapprox_comp hf hg) a },
    { assume s hs, exact map_apply hg hs } },
  exact hf.comp hg,
  assumption
end

lemma integral_dirac (a : α) {f : α → ennreal} (hf : measurable f) : (dirac a).integral f = f a :=
have ∀f:α →ₛ ennreal, @simple_func.integral α {volume := dirac a} f = f a,
begin
  assume f,
  have : ∀r, @volume α { volume := dirac a } (⇑f ⁻¹' {r}) = ⨆ h : f a = r, 1,
  { assume r,
    transitivity,
    apply dirac_apply,
    apply simple_func.measurable_sn,
    refine supr_congr_Prop _ _; simp },
  transitivity,
  apply finset.sum_eq_single (f a),
  { assume b hb h, simp [this, ne.symm h], },
  { assume h, simp at h, exact (h a rfl).elim },
  { rw [this], simp }
end,
begin
  rw [integral, lintegral_eq_supr_eapprox_integral],
  { simp [this, simple_func.supr_eapprox_apply f hf] },
  assumption
end

def with_density (m : measure α) (f : α → ennreal) : measure α :=
if hf : measurable f then
  measure.of_measurable (λs hs, m.integral (λa, ⨆(h : a ∈ s), f a))
    (by simp)
    begin
      assume s hs hd,
      have : ∀a, (⨆ (h : a ∈ ⋃i, s i), f a) = (∑'i, (⨆ (h : a ∈ s i), f a)),
      { assume a,
        by_cases ha : ∃j, a ∈ s j,
        { rcases ha with ⟨j, haj⟩,
          have : ∀i, a ∈ s i ↔ j = i := assume i,
            iff.intro
              (assume hai, by_contradiction $ assume hij, hd j i hij ⟨haj, hai⟩)
              (by rintros rfl; assumption),
          simp [this, ennreal.tsum_supr_eq] },
        { have : ∀i, ¬ a ∈ s i, { simpa using ha },
          simp [this] } },
      simp only [this],
      apply lintegral_tsum,
      { assume i,
        simp [supr_eq_if],
        exact measurable.if (hs i) hf measurable_const }
    end
else 0

lemma with_density_apply {m : measure α} {f : α → ennreal} {s : set α}
  (hf : measurable f) (hs : is_measurable s) :
  m.with_density f s = m.integral (λa, ⨆(h : a ∈ s), f a) :=
by rw [with_density, dif_pos hf]; exact measure.of_measurable_apply s hs

end measure

end measure_theory
