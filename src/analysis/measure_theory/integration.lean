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
  analysis.measure_theory.measure_space
  analysis.measure_theory.borel_space
noncomputable theory
open lattice set filter
local attribute [instance] classical.prop_decidable

lemma supr_eq_of_tendsto {α} [topological_space α] [complete_linear_order α] [orderable_topology α]
  {f : ℕ → α} {a : α} (hf : monotone f) (h : tendsto f at_top (nhds a)) : supr f = a :=
le_antisymm
  (supr_le $ assume i, le_of_not_gt $ assume hi,
    have {n | i ≤ n} ∈ (at_top : filter ℕ).sets, from mem_at_top _,
    let ⟨n, h₁, h₂⟩ := inhabited_of_mem_sets at_top_ne_bot
      (inter_mem_sets this ((tendsto_orderable.1 h).2 _ hi)) in
    not_lt_of_ge (hf h₁) h₂)
  (le_of_not_gt $ assume ha,
    let ⟨n, hn⟩ := inhabited_of_mem_sets at_top_ne_bot ((tendsto_orderable.1 h).1 _ ha) in
    not_lt_of_ge (le_supr _ _) hn)

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

lemma range_const (α) [measure_space α] [ne : nonempty α] (b : β) :
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
(finset.range n).sup (λk, restrict (const α(i k)) {a:α | i k ≤ f a})

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

end

lemma supr_approx_apply [topological_space β] [complete_lattice β] [ordered_topology β] [has_zero β]
  (i : ℕ → β) (f : α → β) (a : α) (hf : _root_.measurable f) (h_zero : (0 : β) = ⊥):
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
  (f : α →ₛ ennreal) (hs : is_measurable s) (hr : r ≠ 0):
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

lemma integral_congr (f g : α →ₛ ennreal) (h : {a | f a = g a} ∈ (@measure_space.μ α _).a_e.sets) :
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
  by_cases {a | s a ≠ ⊤} ∈ ((@measure_space.μ α _).a_e).sets,
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

/-- Monotone convergence theorem -- somtimes called Beppo-Levi convergence -/
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
      rw [← inter_Union_left, ← inter_univ ((map c rs) ⁻¹' {p})] {occs := occurrences.pos [1]},
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
  congr; ext a; by_cases a ∈ s; simp [h, hs],
end

end lintegral

/-
namespace measure

def integral [measurable_space α] (m : measure α) (f : α → ennreal) : ennreal :=
@lintegral α { μ := m } f

def measure.with_density
  [measurable_space α] (m : measure α) (f : α → ennreal) : measure α :=
if measurable f then
  measure.of_measurable (λs hs, m.integral (λa, ⨆(h : a ∈ s), f a))
    _
    _
else m

end measure
-/
end measure_theory