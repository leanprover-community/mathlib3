/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov
-/
import topology.algebra.ordered.basic

/-!
# Bounded monotone sequences converge

In this file we prove a few theorems of the form “if the range of a monotone function `f : ι → α`
admits a least upper bound `a`, then `f x` tends to `a` as `x → ∞`”, as well as version of this
statement for (conditionally) complete lattices that use `⨆ x, f x` instead of `is_lub`.

These theorems work for linear orders with order topologies as well as their products (both in terms
of `prod` and in terms of function types). In order to reduce code duplication, we introduce two
typeclasses (one for the property formulated above and one for the dual property), prove theorems
assuming one of these typeclasses, and provide instances for linear orders and their products.

We also prove some "inverse" results: if `f n` is a monotone sequence and `a` is its limit,
then `f n ≤ a` for all `n`.

## Tags

monotone convergence
-/

open filter set function
open_locale filter topological_space classical

variables {α β : Type*}

/-- We say that `α` is a `Sup_convergence_class` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a least upper bound of `set.range f`. Then `f x` tends to `𝓝 a` as
`x → ∞` (formally, at the filter `filter.at_top`). We require this for `ι = (s : set α)`, `f = coe`
in the definition, then prove it for any `f` in `tendsto_at_top_is_lub`.

This property holds for linear orders with order topology as well as their products. -/
class Sup_convergence_class (α : Type*) [preorder α] [topological_space α] : Prop :=
(tendsto_coe_at_top_is_lub : ∀ (a : α) (s : set α), is_lub s a → tendsto (coe : s → α) at_top (𝓝 a))

/-- We say that `α` is an `Inf_convergence_class` if the following holds. Let `f : ι → α` be a
monotone function, let `a : α` be a greatest lower bound of `set.range f`. Then `f x` tends to `𝓝 a`
as `x → -∞` (formally, at the filter `filter.at_bot`). We require this for `ι = (s : set α)`,
`f = coe` in the definition, then prove it for any `f` in `tendsto_at_bot_is_glb`.

This property holds for linear orders with order topology as well as their products. -/
class Inf_convergence_class (α : Type*) [preorder α] [topological_space α] : Prop :=
(tendsto_coe_at_bot_is_glb : ∀ (a : α) (s : set α), is_glb s a → tendsto (coe : s → α) at_bot (𝓝 a))

instance order_dual.Sup_convergence_class [preorder α] [topological_space α]
  [Inf_convergence_class α] : Sup_convergence_class (order_dual α) :=
⟨‹Inf_convergence_class α›.1⟩

instance order_dual.Inf_convergence_class [preorder α] [topological_space α]
  [Sup_convergence_class α] : Inf_convergence_class (order_dual α) :=
⟨‹Sup_convergence_class α›.1⟩

@[priority 100] -- see Note [lower instance priority]
instance linear_order.Sup_convergence_class [topological_space α] [linear_order α]
  [order_topology α] : Sup_convergence_class α :=
begin
  refine ⟨λ a s ha, tendsto_order.2 ⟨λ b hb, _, λ b hb, _⟩⟩,
  { rcases ha.exists_between hb with ⟨c, hcs, bc, bca⟩,
    lift c to s using hcs,
    refine (eventually_ge_at_top c).mono (λ x hx, bc.trans_le hx) },
  { exact eventually_of_forall (λ x, (ha.1 x.2).trans_lt hb) }
end

@[priority 100] -- see Note [lower instance priority]
instance linear_order.Inf_convergence_class [topological_space α] [linear_order α]
  [order_topology α] : Inf_convergence_class α :=
show Inf_convergence_class (order_dual $ order_dual α), from order_dual.Inf_convergence_class

section

variables {ι : Type*} [preorder ι] [topological_space α]

section is_lub

variables [preorder α] [Sup_convergence_class α] {f : ι → α} {a : α}

lemma tendsto_at_top_is_lub (h_mono : monotone f) (ha : is_lub (set.range f) a) :
  tendsto f at_top (𝓝 a) :=
begin
  suffices : tendsto (range_factorization f) at_top at_top,
    from (Sup_convergence_class.tendsto_coe_at_top_is_lub _ _ ha).comp this,
  exact h_mono.range_factorization.tendsto_at_top_at_top (λ b, b.2.imp $ λ a ha, ha.ge)
end

lemma tendsto_at_bot_is_lub (h_anti : antitone f)
  (ha : is_lub (set.range f) a) : tendsto f at_bot (𝓝 a) :=
@tendsto_at_top_is_lub α (order_dual ι) _ _ _ _ f a h_anti.dual ha

end is_lub

section is_glb

variables [preorder α] [Inf_convergence_class α] {f : ι → α} {a : α}

lemma tendsto_at_bot_is_glb (h_mono : monotone f) (ha : is_glb (set.range f) a) :
  tendsto f at_bot (𝓝 a) :=
@tendsto_at_top_is_lub (order_dual α) (order_dual ι) _ _ _ _ f a h_mono.dual ha

lemma tendsto_at_top_is_glb (h_anti : antitone f)
  (ha : is_glb (set.range f) a) :
  tendsto f at_top (𝓝 a) :=
@tendsto_at_top_is_lub (order_dual α) ι _ _ _ _ f a h_anti ha

end is_glb

section csupr

variables [conditionally_complete_lattice α] [Sup_convergence_class α] {f : ι → α} {a : α}

lemma tendsto_at_top_csupr (h_mono : monotone f) (hbdd : bdd_above $ range f) :
  tendsto f at_top (𝓝 (⨆i, f i)) :=
begin
  casesI is_empty_or_nonempty ι,
  exacts [tendsto_of_is_empty, tendsto_at_top_is_lub h_mono (is_lub_csupr hbdd)]
end

lemma tendsto_at_bot_csupr (h_anti : antitone f)
  (hbdd : bdd_above $ range f) :
  tendsto f at_bot (𝓝 (⨆i, f i)) :=
@tendsto_at_top_csupr α (order_dual ι) _ _ _ _ _ h_anti.dual hbdd

end csupr

section cinfi

variables [conditionally_complete_lattice α] [Inf_convergence_class α] {f : ι → α} {a : α}

lemma tendsto_at_bot_cinfi (h_mono : monotone f) (hbdd : bdd_below $ range f) :
  tendsto f at_bot (𝓝 (⨅i, f i)) :=
@tendsto_at_top_csupr (order_dual α) (order_dual ι) _ _ _ _ _ h_mono.dual hbdd

lemma tendsto_at_top_cinfi (h_anti : antitone f)
  (hbdd : bdd_below $ range f) :
  tendsto f at_top (𝓝 (⨅i, f i)) :=
@tendsto_at_top_csupr (order_dual α) ι _ _ _ _ _ h_anti hbdd

end cinfi

section supr

variables [complete_lattice α] [Sup_convergence_class α] {f : ι → α} {a : α}

lemma tendsto_at_top_supr (h_mono : monotone f) : tendsto f at_top (𝓝 (⨆i, f i)) :=
tendsto_at_top_csupr h_mono (order_top.bdd_above _)

lemma tendsto_at_bot_supr (h_anti : antitone f) :
  tendsto f at_bot (𝓝 (⨆i, f i)) :=
tendsto_at_bot_csupr h_anti (order_top.bdd_above _)

end supr

section infi

variables [complete_lattice α] [Inf_convergence_class α] {f : ι → α} {a : α}

lemma tendsto_at_bot_infi (h_mono : monotone f) : tendsto f at_bot (𝓝 (⨅i, f i)) :=
tendsto_at_bot_cinfi h_mono (order_bot.bdd_below _)

lemma tendsto_at_top_infi (h_anti : antitone f) :
  tendsto f at_top (𝓝 (⨅i, f i)) :=
tendsto_at_top_cinfi h_anti (order_bot.bdd_below _)

end infi

end

instance [preorder α] [preorder β] [topological_space α] [topological_space β]
  [Sup_convergence_class α] [Sup_convergence_class β] : Sup_convergence_class (α × β) :=
begin
  constructor,
  rintro ⟨a, b⟩ s h,
  rw [is_lub_prod, ← range_restrict, ← range_restrict] at h,
  have A : tendsto (λ x : s, (x : α × β).1) at_top (𝓝 a),
    from tendsto_at_top_is_lub (monotone_fst.restrict s) h.1,
  have B : tendsto (λ x : s, (x : α × β).2) at_top (𝓝 b),
    from tendsto_at_top_is_lub (monotone_snd.restrict s) h.2,
  convert A.prod_mk_nhds B,
  ext1 ⟨⟨x, y⟩, h⟩, refl
end

instance [preorder α] [preorder β] [topological_space α] [topological_space β]
  [Inf_convergence_class α] [Inf_convergence_class β] : Inf_convergence_class (α × β) :=
show Inf_convergence_class (order_dual $ (order_dual α × order_dual β)),
  from order_dual.Inf_convergence_class

instance {ι : Type*} {α : ι → Type*} [Π i, preorder (α i)] [Π i, topological_space (α i)]
  [Π i, Sup_convergence_class (α i)] : Sup_convergence_class (Π i, α i) :=
begin
  refine ⟨λ f s h, _⟩,
  simp only [is_lub_pi, ← range_restrict] at h,
  exact tendsto_pi_nhds.2 (λ i, tendsto_at_top_is_lub ((monotone_eval _).restrict _) (h i))
end

instance {ι : Type*} {α : ι → Type*} [Π i, preorder (α i)] [Π i, topological_space (α i)]
  [Π i, Inf_convergence_class (α i)] : Inf_convergence_class (Π i, α i) :=
show Inf_convergence_class (order_dual $ Π i, order_dual (α i)),
  from order_dual.Inf_convergence_class

instance pi.Sup_convergence_class' {ι : Type*} [preorder α] [topological_space α]
  [Sup_convergence_class α] : Sup_convergence_class (ι → α) :=
pi.Sup_convergence_class

instance pi.Inf_convergence_class' {ι : Type*} [preorder α] [topological_space α]
  [Inf_convergence_class α] : Inf_convergence_class (ι → α) :=
pi.Inf_convergence_class

lemma tendsto_of_monotone {ι α : Type*} [preorder ι] [topological_space α]
  [conditionally_complete_linear_order α] [order_topology α] {f : ι → α} (h_mono : monotone f) :
  tendsto f at_top at_top ∨ (∃ l, tendsto f at_top (𝓝 l)) :=
if H : bdd_above (range f) then or.inr ⟨_, tendsto_at_top_csupr h_mono H⟩
else or.inl $ tendsto_at_top_at_top_of_monotone' h_mono H

lemma tendsto_iff_tendsto_subseq_of_monotone {ι₁ ι₂ α : Type*} [semilattice_sup ι₁] [preorder ι₂]
  [nonempty ι₁] [topological_space α] [conditionally_complete_linear_order α] [order_topology α]
  [no_top_order α] {f : ι₂ → α} {φ : ι₁ → ι₂} {l : α} (hf : monotone f)
  (hg : tendsto φ at_top at_top) :
  tendsto f at_top (𝓝 l) ↔ tendsto (f ∘ φ) at_top (𝓝 l) :=
begin
  split; intro h,
  { exact h.comp hg },
  { rcases tendsto_of_monotone hf with h' | ⟨l', hl'⟩,
    { exact (not_tendsto_at_top_of_tendsto_nhds h (h'.comp hg)).elim },
    { rwa tendsto_nhds_unique h (hl'.comp hg) } }
end

/-! The next family of results, such as `is_lub_of_tendsto_at_top` and `supr_eq_of_tendsto`, are
converses to the standard fact that bounded monotone functions converge. They state, that if a
monotone function `f` tends to `a` along `filter.at_top`, then that value `a` is a least upper bound
for the range of `f`.

Related theorems above (`is_lub.is_lub_of_tendsto`, `is_glb.is_glb_of_tendsto` etc) cover the case
when `f x` tends to `a` as `x` tends to some point `b` in the domain. -/

lemma monotone.ge_of_tendsto [topological_space α] [preorder α] [order_closed_topology α]
  [semilattice_sup β] {f : β → α} {a : α} (hf : monotone f)
  (ha : tendsto f at_top (𝓝 a)) (b : β) :
  f b ≤ a :=
begin
  haveI : nonempty β := nonempty.intro b,
  exact ge_of_tendsto ha ((eventually_ge_at_top b).mono (λ _ hxy, hf hxy))
end

lemma monotone.le_of_tendsto [topological_space α] [preorder α] [order_closed_topology α]
  [semilattice_inf β] {f : β → α} {a : α} (hf : monotone f)
  (ha : tendsto f at_bot (𝓝 a)) (b : β) :
  a ≤ f b :=
@monotone.ge_of_tendsto (order_dual α) (order_dual β) _ _ _ _ f _ hf.dual ha b

lemma is_lub_of_tendsto_at_top [topological_space α] [preorder α] [order_closed_topology α]
  [nonempty β] [semilattice_sup β] {f : β → α} {a : α} (hf : monotone f)
  (ha : tendsto f at_top (𝓝 a)) :
  is_lub (set.range f) a :=
begin
  split,
  { rintros _ ⟨b, rfl⟩,
    exact hf.ge_of_tendsto ha b },
  { exact λ _ hb, le_of_tendsto' ha (λ x, hb (set.mem_range_self x)) }
end

lemma is_glb_of_tendsto_at_bot [topological_space α] [preorder α] [order_closed_topology α]
  [nonempty β] [semilattice_inf β] {f : β → α} {a : α} (hf : monotone f)
  (ha : tendsto f at_bot (𝓝 a)) :
  is_glb (set.range f) a :=
@is_lub_of_tendsto_at_top (order_dual α) (order_dual β) _ _ _ _ _ _ _ hf.dual ha

lemma is_lub_of_tendsto_at_bot [topological_space α] [preorder α] [order_closed_topology α]
  [nonempty β] [semilattice_inf β] {f : β → α} {a : α} (hf : antitone f)
  (ha : tendsto f at_bot (𝓝 a)) :
  is_lub (set.range f) a :=
@is_lub_of_tendsto_at_top α (order_dual β)  _ _ _ _ _ _ _ hf.dual_left ha

lemma is_glb_of_tendsto_at_top [topological_space α] [preorder α] [order_closed_topology α]
  [nonempty β] [semilattice_sup β] {f : β → α} {a : α} (hf : antitone f)
  (ha : tendsto f at_top (𝓝 a)) :
  is_glb (set.range f) a :=
@is_glb_of_tendsto_at_bot α (order_dual β)  _ _ _ _ _ _ _ hf.dual_left ha

lemma supr_eq_of_tendsto {α β} [topological_space α] [complete_linear_order α] [order_topology α]
  [nonempty β] [semilattice_sup β] {f : β → α} {a : α} (hf : monotone f) :
  tendsto f at_top (𝓝 a) → supr f = a :=
tendsto_nhds_unique (tendsto_at_top_supr hf)

lemma infi_eq_of_tendsto {α} [topological_space α] [complete_linear_order α] [order_topology α]
  [nonempty β] [semilattice_sup β] {f : β → α} {a : α} (hf : antitone f) :
  tendsto f at_top (𝓝 a) → infi f = a :=
tendsto_nhds_unique (tendsto_at_top_infi hf)

lemma supr_eq_supr_subseq_of_monotone {ι₁ ι₂ α : Type*} [preorder ι₂] [complete_lattice α]
  {l : filter ι₁} [l.ne_bot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : monotone f)
  (hφ : tendsto φ l at_top) :
  (⨆ i, f i) = (⨆ i, f (φ i)) :=
le_antisymm
  (supr_le_supr2 $ λ i, exists_imp_exists (λ j (hj : i ≤ φ j), hf hj)
    (hφ.eventually $ eventually_ge_at_top i).exists)
  (supr_le_supr2 $ λ i, ⟨φ i, le_refl _⟩)

lemma infi_eq_infi_subseq_of_monotone {ι₁ ι₂ α : Type*} [preorder ι₂] [complete_lattice α]
  {l : filter ι₁} [l.ne_bot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : monotone f)
  (hφ : tendsto φ l at_bot) :
  (⨅ i, f i) = (⨅ i, f (φ i)) :=
supr_eq_supr_subseq_of_monotone hf.dual hφ
