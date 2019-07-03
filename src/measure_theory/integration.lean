/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl

Lebesgue integral on `ennreal`.

We define simple functions and show that each Borel measurable function on `ennreal` can be
approximated by a sequence of simple functions.
-/
import
  algebra.pi_instances
  measure_theory.measure_space
  measure_theory.borel_space
noncomputable theory
open lattice set filter
local attribute [instance] classical.prop_decidable

section sequence_of_directed
variables {α : Type*} {β : Type*} [encodable α] [inhabited α]
open encodable

noncomputable def sequence_of_directed (r : β → β → Prop) (f : α → β) (hf : directed r f) : ℕ → α
| 0       := default α
| (n + 1) :=
  let p := sequence_of_directed n in
  match decode α n with
  | none     := p
  | (some a) := classical.some (hf p a)
  end

lemma monotone_sequence_of_directed [partial_order β] (f : α → β) (hf : directed (≤) f) :
  monotone (f ∘ sequence_of_directed (≤) f hf) :=
monotone_of_monotone_nat $ assume n,
  begin
    dsimp [sequence_of_directed],
    generalize eq : sequence_of_directed (≤) f hf n = p,
    cases h : decode α n with a,
    { refl },
    { exact (classical.some_spec (hf p a)).1 }
  end

lemma le_sequence_of_directed [partial_order β] (f : α → β) (hf : directed (≤) f) (a : α) :
  f a ≤ f (sequence_of_directed (≤) f hf (encode a + 1)) :=
begin
  simp [sequence_of_directed, -add_comm, encodek],
  exact (classical.some_spec (hf _ a)).2
end

end sequence_of_directed

namespace measure_theory

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

structure {u v} simple_func (α : Type u) [measurable_space α] (β : Type v) :=
(to_fun : α → β)
(measurable_sn : ∀ x, is_measurable (to_fun ⁻¹' {x}))
(finite : (set.range to_fun).finite)

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

section measurable
variables [measurable_space α]
instance has_coe_to_fun : has_coe_to_fun (α →ₛ β) := ⟨_, to_fun⟩

@[extensionality] theorem ext {f g : α →ₛ β} (H : ∀ a, f a = g a) : f = g :=
by cases f; cases g; congr; exact funext H

protected def range (f : α →ₛ β) := f.finite.to_finset

@[simp] theorem mem_range {f : α →ₛ β} {b} : b ∈ f.range ↔ ∃ a, f a = b :=
finite.mem_to_finset

def const (α) {β} [measurable_space α] (b : β) : α →ₛ β :=
⟨λ a, b, λ x, is_measurable.const _,
  finite_subset (set.finite_singleton b) $ by rintro _ ⟨a, rfl⟩; simp⟩

@[simp] theorem const_apply (a : α) (b : β) : (const α b) a = b := rfl

lemma range_const (α) [measurable_space α] [ne : nonempty α] (b : β) :
  (const α b).range = {b} :=
begin
  ext b',
  simp [mem_range],
  exact ⟨assume ⟨_, h⟩, h.symm, assume h, ne.elim $ λa, ⟨a, h.symm⟩⟩
end

lemma is_measurable_cut (p : α → β → Prop) (f : α →ₛ β)
  (h : ∀b, is_measurable {a | p a b}) : is_measurable {a | p a (f a)} :=
begin
  rw (_ : {a | p a (f a)} = ⋃ b ∈ set.range f, {a | p a b} ∩ f ⁻¹' {b}),
  { exact is_measurable.bUnion (countable_finite f.finite)
      (λ b _, is_measurable.inter (h b) (f.measurable_sn _)) },
  ext a, simp,
  exact ⟨λ h, ⟨_, ⟨a, rfl⟩, h, rfl⟩, λ ⟨_, ⟨a', rfl⟩, h', e⟩, e.symm ▸ h'⟩
end

theorem preimage_measurable (f : α →ₛ β) (s) : is_measurable (f ⁻¹' s) :=
is_measurable_cut (λ _ b, b ∈ s) f (λ b, by simp [is_measurable.const])

theorem measurable [measurable_space β] (f : α →ₛ β) : measurable f :=
λ s _, preimage_measurable f s

def ite {s : set α} (hs : is_measurable s) (f g : α →ₛ β) : α →ₛ β :=
⟨λ a, if a ∈ s then f a else g a,
 λ x, by letI : measurable_space β := ⊤; exact
   measurable.if hs f.measurable g.measurable _ trivial,
 finite_subset (finite_union f.finite g.finite) begin
   rintro _ ⟨a, rfl⟩,
   by_cases a ∈ s; simp [h],
   exacts [or.inl ⟨_, rfl⟩, or.inr ⟨_, rfl⟩]
 end⟩

@[simp] theorem ite_apply {s : set α} (hs : is_measurable s)
  (f g : α →ₛ β) (a) : ite hs f g a = if a ∈ s then f a else g a := rfl

def bind (f : α →ₛ β) (g : β → α →ₛ γ) : α →ₛ γ :=
⟨λa, g (f a) a,
 λ c, is_measurable_cut (λa b, g b a ∈ ({c} : set γ)) f (λ b, (g b).measurable_sn c),
 finite_subset (finite_bUnion f.finite (λ b, (g b).finite)) $
 by rintro _ ⟨a, rfl⟩; simp; exact ⟨_, ⟨a, rfl⟩, _, rfl⟩⟩

@[simp] theorem bind_apply (f : α →ₛ β) (g : β → α →ₛ γ) (a) :
  f.bind g a = g (f a) a := rfl

def restrict [has_zero β] (f : α →ₛ β) (s : set α) : α →ₛ β :=
if hs : is_measurable s then ite hs f (const α 0) else const α 0

@[simp] theorem restrict_apply [has_zero β]
  (f : α →ₛ β) {s : set α} (hs : is_measurable s) (a) :
  restrict f s a = if a ∈ s then f a else 0 :=
by unfold_coes; simp [restrict, hs]; apply ite_apply hs

theorem restrict_preimage [has_zero β]
  (f : α →ₛ β) {s : set α} (hs : is_measurable s)
  {t : set β} (ht : (0:β) ∉ t) : restrict f s ⁻¹' t = s ∩ f ⁻¹' t :=
by ext a; dsimp; rw [restrict_apply]; by_cases a ∈ s; simp [h, hs, ht]

def map (g : β → γ) (f : α →ₛ β) : α →ₛ γ := bind f (const α ∘ g)

@[simp] theorem map_apply (g : β → γ) (f : α →ₛ β) (a) : f.map g a = g (f a) := rfl

theorem map_map (g : β → γ) (h: γ → δ) (f : α →ₛ β) : (f.map g).map h = f.map (h ∘ g) := rfl

theorem coe_map (g : β → γ) (f : α →ₛ β) : (f.map g : α → γ) = g ∘ f := rfl

@[simp] theorem range_map (g : β → γ) (f : α →ₛ β) : (f.map g).range = f.range.image g :=
begin
  ext c,
  simp [mem_range],
  split,
  { rintros ⟨a, rfl⟩, exact ⟨f a, ⟨_, rfl⟩, rfl⟩ },
  { rintros ⟨_, ⟨a, rfl⟩, rfl⟩, exact ⟨_, rfl⟩ }
end

def seq (f : α →ₛ (β → γ)) (g : α →ₛ β) : α →ₛ γ := f.bind (λf, g.map f)

def pair (f : α →ₛ β) (g : α →ₛ γ) : α →ₛ (β × γ) := (f.map prod.mk).seq g

@[simp] lemma pair_apply (f : α →ₛ β) (g : α →ₛ γ) (a) : pair f g a = (f a, g a) := rfl

theorem bind_const (f : α →ₛ β) : f.bind (const α) = f := by ext; simp

instance [has_zero β] : has_zero (α →ₛ β) := ⟨const α 0⟩
instance [has_add β] : has_add (α →ₛ β) := ⟨λf g, (f.map (+)).seq g⟩
instance [has_mul β] : has_mul (α →ₛ β) := ⟨λf g, (f.map (*)).seq g⟩
instance [has_sup β] : has_sup (α →ₛ β) := ⟨λf g, (f.map (⊔)).seq g⟩
instance [has_inf β] : has_inf (α →ₛ β) := ⟨λf g, (f.map (⊓)).seq g⟩
instance [has_le β] : has_le (α →ₛ β) := ⟨λf g, ∀a, f a ≤ g a⟩

@[simp] lemma sup_apply [has_sup β] (f g : α →ₛ β) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl
@[simp] lemma mul_apply [has_mul β] (f g : α →ₛ β) (a : α) : (f * g) a = f a * g a := rfl
lemma add_apply [has_add β] (f g : α →ₛ β) (a : α) : (f + g) a = f a + g a := rfl

lemma add_eq_map₂ [has_add β] (f g : α →ₛ β) : f + g = (pair f g).map (λp:β×β, p.1 + p.2) :=
rfl

lemma sup_eq_map₂ [has_sup β] (f g : α →ₛ β) : f ⊔ g = (pair f g).map (λp:β×β, p.1 ⊔ p.2) :=
rfl

lemma const_mul_eq_map [has_mul β] (f : α →ₛ β) (b : β) : const α b * f = f.map (λa, b * a) := rfl

instance [add_monoid β] : add_monoid (α →ₛ β) :=
{ add       := (+), zero := 0,
  add_assoc := assume f g h, ext (assume a, add_assoc _ _ _),
  zero_add  := assume f, ext (assume a, zero_add _),
  add_zero  := assume f, ext (assume a, add_zero _) }

instance [semiring β] [add_monoid β] : has_scalar β (α →ₛ β) := ⟨λb f, f.map (λa, b * a)⟩

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
{ top := const α⊤, le_top := λf a, le_top, .. simple_func.partial_order }

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
{ .. simple_func.lattice.semilattice_sup,.. simple_func.lattice.order_bot }

instance [lattice β] : lattice (α →ₛ β) :=
{ .. simple_func.lattice.semilattice_sup,.. simple_func.lattice.semilattice_inf }

instance [bounded_lattice β] : bounded_lattice (α →ₛ β) :=
{ .. simple_func.lattice.lattice, .. simple_func.lattice.order_bot, .. simple_func.lattice.order_top }

lemma finset_sup_apply [semilattice_sup_bot β] {f : γ → α →ₛ β} (s : finset γ) (a : α) :
  s.sup f a = s.sup (λc, f c a) :=
begin
  refine finset.induction_on s rfl _,
  assume a s hs ih,
  rw [finset.sup_insert, finset.sup_insert, sup_apply, ih]
end

section approx

section
variables [topological_space β] [semilattice_sup_bot β] [has_zero β]

def approx (i : ℕ → β) (f : α → β) (n : ℕ) : α →ₛ β :=
(finset.range n).sup (λk, restrict (const α (i k)) {a:α | i k ≤ f a})

lemma approx_apply [ordered_topology β] {i : ℕ → β} {f : α → β} {n : ℕ} (a : α)
  (hf : _root_.measurable f) :
  (approx i f n : α →ₛ β) a = (finset.range n).sup (λk, if i k ≤ f a then i k else 0) :=
begin
  dsimp only [approx],
  rw [finset_sup_apply],
  congr,
  funext k,
  rw [restrict_apply],
  refl,
  exact (hf.preimage $ is_measurable_of_is_closed $ is_closed_ge' _)
end

lemma monotone_approx (i : ℕ → β) (f : α → β) : monotone (approx i f) :=
assume n m h, finset.sup_mono $ finset.range_subset.2 h

lemma approx_comp [ordered_topology β] [measurable_space γ]
  {i : ℕ → β} {f : γ → β} {g : α → γ} {n : ℕ} (a : α)
  (hf : _root_.measurable f) (hg : _root_.measurable g) :
  (approx i (f ∘ g) n : α →ₛ β) a = (approx i f n : γ →ₛ β) (g a) :=
by rw [approx_apply _ hf, approx_apply _ (hf.comp hg)]

end

lemma supr_approx_apply [topological_space β] [complete_lattice β] [ordered_topology β] [has_zero β]
  (i : ℕ → β) (f : α → β) (a : α) (hf : _root_.measurable f) (h_zero : (0 : β) = ⊥) :
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

def ennreal_rat_embed (n : ℕ) : ennreal :=
nnreal.of_real ((encodable.decode ℚ n).get_or_else (0 : ℚ))

lemma ennreal_rat_embed_encode (q : ℚ) (hq : 0 ≤ q) :
  ennreal_rat_embed (encodable.encode q) = nnreal.of_real q :=
by rw [ennreal_rat_embed, encodable.encodek]; refl

def eapprox : (α → ennreal) → ℕ → α →ₛ ennreal :=
approx ennreal_rat_embed

lemma monotone_eapprox (f : α → ennreal) : monotone (eapprox f) :=
monotone_approx _ f

lemma supr_eapprox_apply (f : α → ennreal) (hf : _root_.measurable f) (a : α) :
  (⨆n, (eapprox f n : α →ₛ ennreal) a) = f a :=
begin
  rw [eapprox, supr_approx_apply ennreal_rat_embed f a hf rfl],
  refine le_antisymm (supr_le $ assume i, supr_le $ assume hi, hi) (le_of_not_gt _),
  assume h,
  rcases ennreal.lt_iff_exists_rat_btwn.1 h with ⟨q, hq, lt_q, q_lt⟩,
  have : (nnreal.of_real q : ennreal) ≤
      (⨆ (k : ℕ) (h : ennreal_rat_embed k ≤ f a), ennreal_rat_embed k),
  { refine le_supr_of_le (encodable.encode q) _,
    rw [ennreal_rat_embed_encode q hq],
    refine le_supr_of_le (le_of_lt q_lt) _,
    exact le_refl _ },
  exact lt_irrefl _ (lt_of_le_of_lt this lt_q)
end

lemma eapprox_comp [measurable_space γ] {f : γ → ennreal} {g : α → γ} {n : ℕ}
  (hf : _root_.measurable f) (hg : _root_.measurable g) :
  (eapprox (f ∘ g) n : α → ennreal) = (eapprox f n : γ →ₛ ennreal) ∘ g :=
funext $ assume a, approx_comp a hf hg

end eapprox

end measurable

section measure
variables [measure_space α]

def integral (f : α →ₛ ennreal) : ennreal :=
f.range.sum (λ x, x * volume (f ⁻¹' {x}))

-- TODO: slow simp proofs
lemma map_integral (g : β → ennreal) (f : α →ₛ β) :
  (f.map g).integral = f.range.sum (λ x, g x * volume (f ⁻¹' {x})) :=
begin
  simp only [integral, coe_map, range_map],
  refine finset.sum_image' _ (assume b hb, _),
  rcases mem_range.1 hb with ⟨a, rfl⟩,
  let s' := f.range.filter (λb, g b = g (f a)),
  have : g ∘ ⇑f ⁻¹' {g (f a)} = (⋃b∈s', ⇑f ⁻¹' {b}),
  { ext a',
    simp,
    split,
    { assume eq, exact ⟨⟨_, rfl⟩, eq⟩ },
    { rintros ⟨_, eq⟩, exact eq } },
  calc g (f a) * volume (g ∘ ⇑f ⁻¹' {g (f a)}) = g (f a) * volume (⋃b∈s', ⇑f ⁻¹' {b}) : by rw [this]
    ... = g (f a) * s'.sum (λb, volume (f ⁻¹' {b})) :
    begin
      rw [volume_bUnion_finset],
      { simp [pairwise_on, (on)],
        rintros b a₀ rfl eq₀ b a₁ rfl eq₁ ne a ⟨h₁, h₂⟩,
        simp at h₁ h₂,
        rw [← h₁, h₂] at ne,
        exact ne rfl },
      exact assume a ha, preimage_measurable _ _
    end
    ... = s'.sum (λb,  g (f a) * volume (f ⁻¹' {b})) : by rw [finset.mul_sum]
    ... = s'.sum  (λb, g b * volume (f ⁻¹' {b})) : finset.sum_congr rfl $ by simp {contextual := tt}
end

lemma zero_integral : (0 : α →ₛ ennreal).integral = 0 :=
begin
  refine (finset.sum_eq_zero_iff_of_nonneg $ assume _ _, zero_le _).2 _,
  assume r hr, rcases mem_range.1 hr with ⟨a, rfl⟩,
  exact zero_mul _
end

lemma add_integral (f g : α →ₛ ennreal) : (f + g).integral = f.integral + g.integral :=
calc (f + g).integral =
      (pair f g).range.sum (λx, x.1 * volume (pair f g ⁻¹' {x}) + x.2  * volume (pair f g ⁻¹' {x})) :
    by rw [add_eq_map₂, map_integral]; exact finset.sum_congr rfl (assume a ha, add_mul _ _ _)
  ... = (pair f g).range.sum (λx, x.1 * volume (pair f g ⁻¹' {x})) +
      (pair f g).range.sum (λx, x.2 * volume (pair f g ⁻¹' {x})) : by rw [finset.sum_add_distrib]
  ... = ((pair f g).map prod.fst).integral + ((pair f g).map prod.snd).integral :
    by rw [map_integral, map_integral]
  ... = integral f + integral g : rfl

lemma const_mul_integral (f : α →ₛ ennreal) (x : ennreal) :
  (const α x * f).integral = x * f.integral :=
calc (f.map (λa, x * a)).integral = f.range.sum (λr, x * r * volume (f ⁻¹' {r})) :
    by rw [map_integral]
  ... = f.range.sum (λr, x * (r * volume (f ⁻¹' {r}))) :
    finset.sum_congr rfl (assume a ha, mul_assoc _ _ _)
  ... = x * f.integral :
    finset.mul_sum.symm

lemma mem_restrict_range [has_zero β] {r : β} {s : set α} {f : α →ₛ β} (hs : is_measurable s) :
  r ∈ (restrict f s).range ↔ (r = 0 ∧ s ≠ univ) ∨ (∃a∈s, f a = r) :=
begin
  simp only [mem_range, restrict_apply, hs],
  split,
  { rintros ⟨a, ha⟩,
    split_ifs at ha,
    { exact or.inr ⟨a, h, ha⟩ },
    { exact or.inl ⟨ha.symm, assume eq, h $ eq.symm ▸ trivial⟩ } },
  { rintros (⟨rfl, h⟩ | ⟨a, ha, rfl⟩),
    { have : ¬ ∀a, a ∈ s := assume this, h $ eq_univ_of_forall this,
      rcases not_forall.1 this with ⟨a, ha⟩,
      refine ⟨a, _⟩,
      rw [if_neg ha] },
    { refine ⟨a, _⟩,
      rw [if_pos ha] } }
end

lemma restrict_preimage' {r : ennreal} {s : set α}
  (f : α →ₛ ennreal) (hs : is_measurable s) (hr : r ≠ 0) :
  (restrict f s) ⁻¹' {r} = (f ⁻¹' {r} ∩ s) :=
begin
  ext a,
  by_cases a ∈ s; simp [hs, h, hr.symm]
end

lemma restrict_integral (f : α →ₛ ennreal) (s : set α) (hs : is_measurable s) :
  (restrict f s).integral = f.range.sum (λr, r * volume (f ⁻¹' {r} ∩ s)) :=
begin
  refine finset.sum_bij_ne_zero (λr _ _, r) _ _ _ _,
  { assume r hr,
    rcases (mem_restrict_range hs).1 hr with ⟨rfl, h⟩ | ⟨a, ha, rfl⟩,
    { simp },
    { assume _, exact mem_range.2 ⟨a, rfl⟩ } },
  { assume a b _ _ _ _ h, exact h },
  { assume r hr,
    by_cases r0 : r = 0, { simp [r0] },
    assume h0,
    rcases mem_range.1 hr with ⟨a, rfl⟩,
    have : f ⁻¹' {f a} ∩ s ≠ ∅,
    { assume h, simpa [h] using h0 },
    rcases ne_empty_iff_exists_mem.1 this with ⟨a', eq', ha'⟩,
    refine ⟨_, (mem_restrict_range hs).2 (or.inr ⟨a', ha', _⟩), _, rfl⟩,
    { simpa using eq' },
    { rwa [restrict_preimage' _ hs r0] } },
  { assume r hr ne,
    by_cases r = 0, { simp [h] },
    rw [restrict_preimage' _ hs h] }
end

lemma restrict_const_integral (c : ennreal) (s : set α) (hs : is_measurable s) :
  (restrict (const α c) s).integral = c * volume s :=
have (@const α ennreal _ c) ⁻¹' {c} = univ,
begin
  refine eq_univ_of_forall (assume a, _),
  simp,
end,
calc (restrict (const α c) s).integral = c * volume ((const α c) ⁻¹' {c} ∩ s) :
  begin
    rw [restrict_integral (const α c) s hs],
    refine finset.sum_eq_single c _ _,
    { assume r hr, rcases mem_range.1 hr with ⟨a, rfl⟩, contradiction },
    { by_cases nonempty α,
      { assume ne,
        rcases h with ⟨a⟩,
        exfalso,
        exact ne (mem_range.2 ⟨a, rfl⟩) },
      { assume empty,
        have : (@const α ennreal _ c) ⁻¹' {c} ∩ s = ∅,
        { ext a, exfalso, exact h ⟨a⟩ },
        simp only [this, volume_empty, mul_zero] } }
  end
  ... = c * volume s : by rw [this, univ_inter]

lemma integral_sup_le (f g : α →ₛ ennreal) : f.integral ⊔ g.integral ≤ (f ⊔ g).integral :=
calc f.integral ⊔ g.integral =
      ((pair f g).map prod.fst).integral ⊔ ((pair f g).map prod.snd).integral : rfl
  ... ≤ (pair f g).range.sum (λx, (x.1 ⊔ x.2) * volume (pair f g ⁻¹' {x})) :
  begin
    rw [map_integral, map_integral],
    refine sup_le _ _;
      refine finset.sum_le_sum' (λ a _, canonically_ordered_semiring.mul_le_mul _ (le_refl _)),
    exact le_sup_left,
    exact le_sup_right
  end
  ... = (f ⊔ g).integral : by rw [sup_eq_map₂, map_integral]

lemma integral_le_integral (f g : α →ₛ ennreal) (h : f ≤ g) : f.integral ≤ g.integral :=
calc f.integral ≤ f.integral ⊔ g.integral : le_sup_left
  ... ≤ (f ⊔ g).integral : integral_sup_le _ _
  ... = g.integral : by rw [sup_of_le_right h]

lemma integral_congr (f g : α →ₛ ennreal) (h : {a | f a = g a} ∈ (@measure_space.μ α _).a_e) :
  f.integral = g.integral :=
show ((pair f g).map prod.fst).integral = ((pair f g).map prod.snd).integral, from
begin
  rw [map_integral, map_integral],
  refine finset.sum_congr rfl (assume p hp, _),
  rcases mem_range.1 hp with ⟨a, rfl⟩,
  by_cases eq : f a = g a,
  { dsimp only [pair_apply], rw eq },
  { have : volume ((pair f g) ⁻¹' {(f a, g a)}) = 0,
    { refine volume_mono_null (assume a' ha', _) h,
      simp at ha',
      show f a' ≠ g a',
      rwa [ha'.1, ha'.2] },
    simp [this] }
end

lemma integral_map {β} [measure_space β] (f : α →ₛ ennreal) (g : β →ₛ ennreal)
  (m : α → β) (hm : _root_.measurable m) (eq : ∀a:α, f a = g (m a))
  (h : ∀s:set β, is_measurable s → volume s = volume (m ⁻¹' s)) :
  f.integral = g.integral :=
have f_eq : (f : α → ennreal) = g ∘ m := funext eq,
have vol_f : ∀r, volume (f ⁻¹' {r}) = volume (g ⁻¹' {r}),
  by { assume r, rw [h, f_eq, preimage_comp], exact measurable_sn _ _ },
begin
  simp [integral, vol_f],
  refine finset.sum_subset _ _,
  { simp [finset.subset_iff, f_eq],
    rintros r a rfl, exact ⟨_, rfl⟩ },
  { assume r hrg hrf,
    rw [simple_func.mem_range, not_exists] at hrf,
    have : f ⁻¹' {r} = ∅ := set.eq_empty_of_subset_empty (assume a, by simpa using hrf a),
    simp [(vol_f _).symm, this] }
end

end measure

end simple_func

section lintegral
open simple_func
variable [measure_space α]

/-- The lower Lebesgue integral -/
def lintegral (f : α → ennreal) : ennreal :=
⨆ (s : α →ₛ ennreal) (hf : f ≥ s), s.integral

notation `∫⁻` binders `, ` r:(scoped f, lintegral f) := r

theorem simple_func.lintegral_eq_integral (f : α →ₛ ennreal) : (∫⁻ a, f a) = f.integral :=
le_antisymm
  (supr_le $ assume s, supr_le $ assume hs, integral_le_integral _ _ hs)
  (le_supr_of_le f $ le_supr_of_le (le_refl f) $ le_refl _)

lemma lintegral_le_lintegral (f g : α → ennreal) (h : f ≤ g) : (∫⁻ a, f a) ≤ (∫⁻ a, g a) :=
supr_le_supr $ assume s, supr_le $ assume hs, le_supr_of_le (le_trans hs h) (le_refl _)

lemma lintegral_eq_nnreal (f : α → ennreal) :
  (∫⁻ a, f a) =
    (⨆ (s : α →ₛ nnreal) (hf : f ≥ s.map (coe : nnreal → ennreal)), (s.map (coe : nnreal → ennreal)).integral) :=
begin
  let c : nnreal → ennreal := coe,
  refine le_antisymm
    (supr_le $ assume s, supr_le $ assume hs, _)
    (supr_le $ assume s, supr_le $ assume hs, le_supr_of_le (s.map c) $ le_supr _ hs),
  by_cases {a | s a ≠ ⊤} ∈ (@measure_space.μ α _).a_e,
  { have : f ≥ (s.map ennreal.to_nnreal).map c :=
      le_trans (assume a, ennreal.coe_to_nnreal_le_self) hs,
    refine le_supr_of_le (s.map ennreal.to_nnreal) (le_supr_of_le this (le_of_eq $ integral_congr _ _ _)),
    exact filter.mem_sets_of_superset h (assume a ha, (ennreal.coe_to_nnreal ha).symm) },
  { have h_vol_s : volume {a : α | s a = ⊤} ≠ 0,
    { simp [measure.a_e, set.compl_set_of] at h, assumption },
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
      have : {a : α | s a = ⊤} = s ⁻¹' {⊤}, { ext a, simp },
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

/-- Monotone convergence theorem -- somtimes called Beppo-Levi convergence.

See `lintegral_supr_directed` for a more general form. -/
theorem lintegral_supr
  {f : ℕ → α → ennreal} (hf : ∀n, measurable (f n)) (h_mono : monotone f) :
  (∫⁻ a, ⨆n, f n a) = (⨆n, ∫⁻ a, f n a) :=
let c : nnreal → ennreal := coe in
let F (a:α) := ⨆n, f n a in
have hF : measurable F := measurable.supr hf,
show (∫⁻ a, F a) = (⨆n, ∫⁻ a, f n a),
begin
  refine le_antisymm _ _,
  { rw [lintegral_eq_nnreal],
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
      assume n, measurable_le (simple_func.measurable _) (hf n),
    calc (r:ennreal) * integral (s.map c) = (rs.map c).range.sum (λr, r * volume ((rs.map c) ⁻¹' {r})) :
        by rw [← const_mul_integral, integral, eq_rs]
      ... ≤ (rs.map c).range.sum (λr, r * volume (⋃n, (rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a})) :
        le_of_eq (finset.sum_congr rfl $ assume x hx, by rw ← eq)
      ... ≤ (rs.map c).range.sum (λr, (⨆n, r * volume ((rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}))) :
        le_of_eq (finset.sum_congr rfl $ assume x hx,
          begin
            rw [volume, measure_Union_eq_supr_nat _ (mono x), ennreal.mul_supr],
            { assume i,
              refine is_measurable.inter ((rs.map c).preimage_measurable _) _,
              refine (hf i).preimage _,
              exact is_measurable_of_is_closed (is_closed_ge' _) }
          end)
      ... ≤ ⨆n, (rs.map c).range.sum (λr, r * volume ((rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a})) :
        begin
          refine le_of_eq _,
          rw [ennreal.finset_sum_supr_nat],
          assume p i j h,
          exact canonically_ordered_semiring.mul_le_mul (le_refl _) (volume_mono $ mono p h)
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
        refine lintegral_le_lintegral _ _ (assume a, _),
        dsimp,
        rw [restrict_apply],
        split_ifs; simp, simpa using h,
        exact h_meas n
      end },
  { exact supr_le (assume n, lintegral_le_lintegral _ _ $ assume a, le_supr _ n) }
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
    { assume n, exact measurable_add (eapprox f n).measurable (eapprox g n).measurable },
    { assume i j h a, exact add_le_add' (monotone_eapprox _ h _) (monotone_eapprox _ h _) }
  end
  ... = (⨆n, (eapprox f n).integral) + (⨆n, (eapprox g n).integral) :
  by refine (ennreal.supr_add_supr_of_monotone _ _).symm;
     { assume i j h, exact simple_func.integral_le_integral _ _ (monotone_eapprox _ h) }
  ... = (∫⁻ a, f a) + (∫⁻ a, g a) :
    by rw [lintegral_eq_supr_eapprox_integral hf, lintegral_eq_supr_eapprox_integral hg]

@[simp] lemma lintegral_zero : (∫⁻ a:α, 0) = 0 :=
show (∫⁻ a:α, (0 : α →ₛ ennreal) a) = 0, by rw [simple_func.lintegral_eq_integral, zero_integral]

lemma lintegral_finset_sum (s : finset β) {f : β → α → ennreal} (hf : ∀b, measurable (f b)) :
  (∫⁻ a, s.sum (λb, f b a)) = s.sum (λb, ∫⁻ a, f b a) :=
begin
  refine finset.induction_on s _ _,
  { simp },
  { assume a s has ih,
    simp [has],
    rw [lintegral_add (hf _) (measurable_finset_sum s hf), ih] }
end

lemma lintegral_const_mul (r : ennreal) {f : α → ennreal} (hf : measurable f) :
  (∫⁻ a, r * f a) = r * (∫⁻ a, f a) :=
calc (∫⁻ a, r * f a) = (∫⁻ a, (⨆n, (const α r * eapprox f n) a)) :
    by congr; funext a; rw [← supr_eapprox_apply f hf, ennreal.mul_supr]; refl
  ... = (⨆n, r * (eapprox f n).integral) :
  begin
    rw [lintegral_supr],
    { congr, funext n, rw [← simple_func.const_mul_integral, ← simple_func.lintegral_eq_integral] },
    { assume n, exact simple_func.measurable _ },
    { assume i j h a, exact canonically_ordered_semiring.mul_le_mul (le_refl _)
        (monotone_eapprox _ h _) }
  end
  ... = r * (∫⁻ a, f a) : by rw [← ennreal.mul_supr, lintegral_eq_supr_eapprox_integral hf]

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
  have : - t ∈ (@measure_space.μ α _).a_e,
  { rw [measure.mem_a_e_iff, lattice.neg_neg, ht0] },
  refine (supr_le $ assume s, supr_le $ assume hfs,
    le_supr_of_le (s.restrict (- t)) $ le_supr_of_le _ _),
  { assume a,
    by_cases a ∈ t;
      simp [h, simple_func.restrict_apply, ht.compl],
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
  (lintegral_le_lintegral_ae $ by filter_upwards [h] assume a h, le_of_eq h)
  (lintegral_le_lintegral_ae $ by filter_upwards [h] assume a h, le_of_eq h.symm)

lemma lintegral_eq_zero_iff {f : α → ennreal} (hf : measurable f) :
  lintegral f = 0 ↔ (∀ₘ a, f a = 0) :=
begin
  refine iff.intro (assume h, _) (assume h, _),
  { have : ∀n:ℕ, ∀ₘ a, f a < n⁻¹,
    { assume n,
      have : is_measurable {a : α | f a ≥ n⁻¹ },
      { exact hf _ (is_measurable_of_is_closed $ is_closed_ge' _) },
      have : (n : ennreal)⁻¹ * volume {a | f a ≥ n⁻¹ } = 0,
      { rw [← simple_func.restrict_const_integral _ _ this, ← le_zero_iff_eq,
          ← simple_func.lintegral_eq_integral],
        refine le_trans (lintegral_le_lintegral _ _ _) (le_of_eq h),
        assume a, by_cases h : (n : ennreal)⁻¹ ≤ f a; simp [h, (≥), this] },
      rw [ennreal.mul_eq_zero, ennreal.inv_eq_zero] at this,
      simpa [ennreal.nat_ne_top, all_ae_iff] using this },
    filter_upwards [all_ae_all_iff.2 this],
    dsimp,
    assume a ha,
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
                       (all_ae_iff.1 (all_ae_all_iff.2 h_mono)) in
let g := λ n a, if a ∈ s then 0 else f n a in
have g_eq_f : ∀ₘ a, ∀n, g n a = f n a,
  begin
    have := hs.2.2, rw [← compl_compl s] at this,
    filter_upwards [(measure.mem_a_e_iff (-s)).2 this] assume a ha n, if_neg ha
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
  rw [← ennreal.add_right_inj hg_fin,
        ennreal.sub_add_cancel_of_le (lintegral_le_lintegral_ae h_le),
      ← lintegral_add (ennreal.measurable_sub hf hg) hg],
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
  lintegral_le_lintegral _ _ (assume a, infi_le_of_le 0 (le_refl _)),
have fn_le_f0' : (⨅n, ∫⁻ a, f n a) ≤ lintegral (f 0), from infi_le_of_le 0 (le_refl _),
(ennreal.sub_left_inj h_fin fn_le_f0 fn_le_f0').1 $
show lintegral (f 0) - (∫⁻ a, ⨅n, f n a) = lintegral (f 0) - (⨅n, ∫⁻ a, f n a), from
calc
  lintegral (f 0) - (∫⁻ a, ⨅n, f n a) = ∫⁻ a, f 0 a - ⨅n, f n a :
    (lintegral_sub (h_meas 0) (measurable.infi h_meas)
    (calc
      (∫⁻ a, ⨅n, f n a)  ≤ lintegral (f 0) : lintegral_le_lintegral _ _
                                             (assume a, infi_le _ _)
          ... < ⊤ : h_fin  )
    (all_ae_of_all $ assume a, infi_le _ _)).symm
  ... = ∫⁻ a, ⨆n, f 0 a - f n a : congr rfl (funext (assume a, ennreal.sub_infi))
  ... = ⨆n, ∫⁻ a, f 0 a - f n a :
    lintegral_supr_ae
      (assume n, ennreal.measurable_sub (h_meas 0) (h_meas n))
      (assume n, by
        filter_upwards [h_mono n] assume a ha, ennreal.sub_le_sub (le_refl _) ha)
  ... = ⨆n, lintegral (f 0) - ∫⁻ a, f n a :
    have h_mono : ∀ₘ a, ∀n:ℕ, f n.succ a ≤ f n a := all_ae_all_iff.2 h_mono,
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

/-- Known as Fatou's lemma -/
lemma lintegral_liminf_le {f : ℕ → α → ennreal} (h_meas : ∀n, measurable (f n)) :
  (∫⁻ a, liminf at_top (λ n, f n a)) ≤ liminf at_top (λ n, lintegral (f n)) :=
calc
  (∫⁻ a, liminf at_top (λ n, f n a)) = ∫⁻ a, ⨆n:ℕ, ⨅i≥n, f i a :
     congr rfl (funext (assume a, liminf_eq_supr_infi_of_nat))
  ... = ⨆n:ℕ, ∫⁻ a, ⨅i≥n, f i a :
    lintegral_supr
    begin
      assume n, apply measurable.infi, assume i, by_cases h : i ≥ n,
      {convert h_meas i, simp [h]},
      {convert measurable_const, simp [h]}
    end
    begin
      assume n m hnm a, simp only [le_infi_iff], assume i hi,
      refine infi_le_of_le i (infi_le_of_le (le_trans hnm hi) (le_refl _))
    end
  ... ≤ ⨆n:ℕ, ⨅i≥n, lintegral (f i) :
    supr_le_supr $ assume n, le_infi $
      assume i, le_infi $ assume hi, lintegral_le_lintegral _ _
      $ assume a, infi_le_of_le i $ infi_le_of_le hi $ le_refl _
  ... = liminf at_top (λ n, lintegral (f n)) : liminf_eq_supr_infi_of_nat.symm

lemma limsup_lintegral_le {f : ℕ → α → ennreal} {g : α → ennreal}
  (hf_meas : ∀ n, measurable (f n)) (hg_meas : measurable g)
  (h_bound : ∀n, ∀ₘa, f n a ≤ g a) (h_fin : lintegral g < ⊤) :
  limsup at_top (λn, lintegral (f n)) ≤ ∫⁻ a, limsup at_top (λn, f n a) :=
calc
  limsup at_top (λn, lintegral (f n)) = ⨅n:ℕ, ⨆i≥n, lintegral (f i) :
    limsup_eq_infi_supr_of_nat
  ... ≤ ⨅n:ℕ, ∫⁻ a, ⨆i≥n, f i a :
    infi_le_infi $ assume n, supr_le $ assume i, supr_le $ assume hi,
    lintegral_le_lintegral _ _ $ assume a, le_supr_of_le i $ le_supr_of_le hi (le_refl _)
  ... = ∫⁻ a, ⨅n:ℕ, ⨆i≥n, f i a :
    (lintegral_infi_ae
      (assume n,
           @measurable.supr _ _ _ _ _ _ _ _ _ (λ i a, supr (λ (h : i ≥ n), f i a))
      (assume i, measurable.supr_Prop (hf_meas i)))
      (assume n, all_ae_of_all $ assume a,
       begin
         simp only [supr_le_iff], assume i hi, refine le_supr_of_le i _,
         rw [supr_pos _], exact le_refl _, exact nat.le_of_succ_le hi
       end )
      (lt_of_le_of_lt
        (lintegral_le_lintegral_ae
        begin
          filter_upwards [all_ae_all_iff.2 h_bound],
          simp only [supr_le_iff, mem_set_of_eq],
          assume a ha i hi, exact ha i
        end )
        h_fin)).symm
  ... = ∫⁻ a, limsup at_top (λn, f n a) :
    lintegral_congr_ae $ all_ae_of_all $ assume a, limsup_eq_infi_supr_of_nat.symm

/-- Dominated convergence theorem for nonnegative functions -/
lemma dominated_convergence_nn
  {F : ℕ → α → ennreal} {f : α → ennreal} {g : α → ennreal}
  (hF_meas : ∀n, measurable (F n)) (hf_meas : measurable f) (hg_meas : measurable g)
  (h_bound : ∀n, ∀ₘ a, F n a ≤ g a)
  (h_fin : lintegral g < ⊤)
  (h_lim : ∀ₘ a, tendsto (λ n, F n a) at_top (nhds (f a))) :
  tendsto (λn, lintegral (F n)) at_top (nhds (lintegral f)) :=
begin
  have limsup_le_lintegral :=
  calc
    limsup at_top (λ (n : ℕ), lintegral (F n)) ≤ ∫⁻ (a : α), limsup at_top (λn, F n a) :
      limsup_lintegral_le hF_meas hg_meas h_bound h_fin
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
  have : ∀a, (⨆ b, f b a) = (⨆ n, f (sequence_of_directed (≤) f h_directed n) a),
  { assume a,
    refine le_antisymm (supr_le $ assume b, _) (supr_le $ assume n, le_supr (λn, f n a) _),
    exact le_supr_of_le (encode b + 1) (le_sequence_of_directed f h_directed b a) },
  calc (∫⁻ a, ⨆ b, f b a) = (∫⁻ a, ⨆ n, f (sequence_of_directed (≤) f h_directed n) a) :
      by simp only [this]
    ... = (⨆ n, ∫⁻ a, f (sequence_of_directed (≤) f h_directed n) a) :
      lintegral_supr (assume n, hf _) (monotone_sequence_of_directed f h_directed)
    ... = (⨆ b, ∫⁻ a, f b a) :
    begin
      refine le_antisymm (supr_le $ assume n, _) (supr_le $ assume b, _),
      { exact le_supr (λb, lintegral (f b)) _ },
      { exact le_supr_of_le (encode b + 1)
          (lintegral_le_lintegral _ _ $ le_sequence_of_directed f h_directed b) }
    end
end

end

lemma lintegral_tsum [encodable β] {f : β → α → ennreal} (hf : ∀i, measurable (f i)) :
  (∫⁻ a, ∑ i, f i a) = (∑ i, ∫⁻ a, f i a) :=
begin
  simp only [ennreal.tsum_eq_supr_sum],
  rw [lintegral_supr_directed],
  { simp [lintegral_finset_sum _ hf] },
  { assume b, exact measurable_finset_sum _ hf },
  { assume s t,
    use [s ∪ t],
    split,
    exact assume a, finset.sum_le_sum_of_subset (finset.subset_union_left _ _),
    exact assume a, finset.sum_le_sum_of_subset (finset.subset_union_right _ _) }
end

end lintegral

namespace measure

def integral [measurable_space α] (m : measure α) (f : α → ennreal) : ennreal :=
@lintegral α { μ := m } f

variables [measurable_space α] {m : measure α}

@[simp] lemma integral_zero : m.integral (λa, 0) = 0 := @lintegral_zero α { μ := m }

lemma integral_map [measurable_space β] {f : β → ennreal} {g : α → β}
  (hf : measurable f) (hg : measurable g) : (map g m).integral f = m.integral (f ∘ g) :=
begin
  rw [integral, integral, lintegral_eq_supr_eapprox_integral, lintegral_eq_supr_eapprox_integral],
  { congr, funext n, symmetry,
    apply simple_func.integral_map,
    { exact hg },
    { assume a, exact congr_fun (simple_func.eapprox_comp hf hg) a },
    { assume s hs, exact map_apply hg hs } },
  exact hf.comp hg,
  assumption
end

lemma integral_dirac (a : α) {f : α → ennreal} (hf : measurable f) : (dirac a).integral f = f a :=
have ∀f:α →ₛ ennreal, @simple_func.integral α {μ := dirac a} f = f a,
begin
  assume f,
  have : ∀r, @volume α { μ := dirac a } (⇑f ⁻¹' {r}) = ⨆ h : f a = r, 1,
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
      have : ∀a, (⨆ (h : a ∈ ⋃i, s i), f a) = (∑i, (⨆ (h : a ∈ s i), f a)),
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
