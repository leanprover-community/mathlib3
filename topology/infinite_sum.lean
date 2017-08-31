/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Infinite sum over a topological monoid
-/
import data.finset topology.topological_structures algebra.big_operators
noncomputable theory
open set lattice finset filter function

variables {α : Type*} {β : Type*} {γ : Type*}

section logic

theorem forall_and_distrib' {α : Sort*} (p q : α → Prop) :
  (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
  (assume h, ⟨(assume x, (h x).left), (assume x, (h x).right)⟩)
  (assume h x, ⟨h.left x, h.right x⟩)

end logic

open classical
local attribute [instance] decidable_inhabited prop_decidable

namespace filter

lemma mem_infi_sets_finset {s : finset α} {f : α → filter β} :
  ∀t, t ∈ (⨅a∈s, f a).sets ↔ (∃p:α → set β, (∀a∈s, p a ∈ (f a).sets) ∧ (⋂a∈s, p a) ⊆ t) :=
show ∀t,  t ∈ (⨅a∈s, f a).sets ↔ (∃p:α → set β, (∀a∈s, p a ∈ (f a).sets) ∧ (⨅a∈s, p a) ≤ t),
  from s.induction_on (by simp; exact assume t, iff.refl _) $
    by simp [infi_or, mem_inf_sets, infi_inf_eq] {contextual := tt};
    from assume a s has ih t, iff.intro
      (assume ⟨t₁, ht₁, t₂, ht, p, hp, ht₂⟩,
        ⟨λa', if a' = a then t₁ else p a',
          assume a' ha', by by_cases a' = a; simp * at *,
          have ∀a', (⨅ (h : a' ∈ s), ite (a' = a) t₁ (p a')) ≤ ⨅ (H : a' ∈ s), p a',
            from assume a', infi_le_infi $ assume has',
              have a' ≠ a, from assume h, has $ h ▸ has',
              le_of_eq $ by simp [this],
          le_trans (inf_le_inf (by simp; exact le_refl t₁) (le_trans (infi_le_infi this) ht₂)) ht⟩)
      (assume ⟨p, hp, ht⟩, ⟨p a, hp _ (by simp), ⨅ (x : α) (h : x ∈ s), p x, ht, p,
        assume a ha, hp _ (or.inr ha), le_refl _⟩)

end filter

section topological_space

variables [topological_space α]

lemma mem_closure_of_tendsto {f : β → α} {x : filter β} {a : α} {s : set α}
  (hf : tendsto f x (nhds a)) (hs : is_closed s) (h : x ⊓ principal (f ⁻¹' s) ≠ ⊥) : a ∈ s :=
is_closed_iff_nhds.mp hs _ $ neq_bot_of_le_neq_bot (@map_ne_bot _ _ _ f h) $
  le_inf (le_trans (map_mono $ inf_le_left) hf) $
    le_trans (map_mono $ inf_le_right_of_le $ by simp; exact subset.refl _) (@map_vmap_le _ _ _ f)

end topological_space

section uniform_space

lemma cauchy_iff [uniform_space α] {f : filter α} :
  cauchy f ↔ (f ≠ ⊥ ∧ (∀s∈(@uniformity α _).sets, ∃t∈f.sets, set.prod t t ⊆ s)) :=
and_congr (iff.refl _) $ forall_congr $ assume s, forall_congr $ assume hs, mem_prod_same_iff

end uniform_space

section at_top

@[simp] lemma at_top_ne_bot [inhabited α] [semilattice_sup α] : (at_top : filter α) ≠ ⊥ :=
infi_neq_bot_of_directed (by apply_instance)
  (assume a b, ⟨a ⊔ b, by simp {contextual := tt}⟩)
  (assume a, by simp [principal_eq_bot_iff]; exact ne_empty_of_mem (le_refl a))

lemma mem_at_top_iff [inhabited α] [semilattice_sup α] {s : set α} :
  s ∈ (at_top : filter α).sets ↔ (∃a:α, ∀b≥a, b ∈ s) :=
iff.intro
  (assume h, infi_sets_induct h ⟨default α, by simp⟩
    (assume a s₁ s₂ ha ⟨b, hb⟩, ⟨a ⊔ b,
      assume c hc, ⟨ha $ le_trans le_sup_left hc, hb _ $ le_trans le_sup_right hc⟩⟩)
    (assume s₁ s₂ h ⟨a, ha⟩, ⟨a, assume b hb, h $ ha _ hb⟩))
  (assume ⟨a, h⟩, mem_infi_sets a $ assume x, h x)

lemma map_at_top_eq [inhabited α] [semilattice_sup α] {f : α → β} :
  at_top.map f = (⨅a, principal $ f '' {a' | a ≤ a'}) :=
calc map f (⨅a, principal {a' | a ≤ a'}) = (⨅a, map f $ principal {a' | a ≤ a'}) :
    map_infi_eq (assume a b, ⟨a ⊔ b, by simp {contextual := tt}⟩) ⟨default α⟩
  ... = (⨅a, principal $ f '' {a' | a ≤ a'}) : by simp

lemma tendsto_finset_image_at_top_at_top {i : β → γ} {j : γ → β} (h : ∀x, j (i x) = x) :
  tendsto (λs:finset γ, s.image j) at_top at_top :=
tendsto_infi $ assume s, tendsto_infi' (s.image i) $ tendsto_principal_principal $
  assume t (ht : s.image i ⊆ t),
  calc s = (s.image i).image j : by simp [image_image, (∘), h]; exact finset.image_id.symm
    ... ⊆  t.image j : image_subset_image ht

end at_top

section is_sum
variables [add_comm_monoid α] [topological_space α] [topological_add_monoid α]

/-- Infinite sum on a topological monoid
The `at_top` filter on `finset α` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is still invariant under reordering, and a absolute
sum operator.

This is based on Mario Carneiro's infinite sum in Metamath.
-/
def is_sum (f : β → α) (a : α) : Prop := tendsto (λs:finset β, s.sum f) at_top (nhds a)

variables {f g : β → α} {a b : α} {s : finset β}

lemma is_sum_zero : is_sum (λb, 0 : β → α) 0 :=
by simp [is_sum, tendsto_const_nhds]

lemma is_sum_add (hf : is_sum f a) (hg : is_sum g b) : is_sum (λb, f b + g b) (a + b) :=
by simp [is_sum, sum_add_distrib]; exact tendsto_add hf hg

lemma is_sum_sum {f : γ → β → α} {a : γ → α} {s : finset γ} :
  (∀i∈s, is_sum (f i) (a i)) → is_sum (λb, s.sum $ λi, f i b) (s.sum a) :=
s.induction_on (by simp [is_sum_zero]) (by simp [is_sum_add] {contextual := tt})

lemma is_sum_sum_of_ne_zero (hf : ∀b∉s, f b = 0) : is_sum f (s.sum f) :=
tendsto_infi' s $ tendsto_cong tendsto_const_nhds $
  assume t (ht : s ⊆ t), show s.sum f = t.sum f, from sum_subset ht $ assume x _, hf _

lemma is_sum_of_iso {j : γ → β} {i : β → γ}
  (hf : is_sum f a) (h₁ : ∀x, i (j x) = x) (h₂ : ∀x, j (i x) = x) : is_sum (f ∘ j) a :=
have ∀x y, j x = j y → x = y,
  from assume x y h,
  have i (j x) = i (j y), by rw [h],
  by rwa [h₁, h₁] at this,
have (λs:finset γ, s.sum (f ∘ j)) = (λs:finset β, s.sum f) ∘ (λs:finset γ, s.image j),
  from funext $ assume s, (sum_image $ assume x _ y _, this x y).symm,
show tendsto (λs:finset γ, s.sum (f ∘ j)) at_top (nhds a),
   by rw [this]; apply tendsto_compose (tendsto_finset_image_at_top_at_top h₂) hf

lemma is_sum_hom {g : α → γ} [add_comm_monoid γ] [topological_space γ] [topological_add_monoid γ]
  (hf : is_sum f a) (h₁ : g 0 = 0) (h₂ : ∀x y, g (x + y) = g x + g y) (h₃ : continuous g) :
  is_sum (g ∘ f) (g a) :=
have (λs:finset β, s.sum (g ∘ f)) = g ∘ (λs:finset β, s.sum f),
  from funext $ assume s, sum_hom g h₁ h₂,
show tendsto (λs:finset β, s.sum (g ∘ f)) at_top (nhds (g a)),
  by rw [this]; exact tendsto_compose hf (continuous_iff_tendsto.mp h₃ a)

end is_sum

section is_sum_iff_is_sum_of_iso_ne_zero
variables [add_comm_monoid α] [topological_space α] [topological_add_monoid α]
variables {f : β → α} {g : γ → α} {i : γ → β} {j : β → γ} {a : α}

lemma is_sum_of_is_sum
  (h_eq : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ u'.sum g = v'.sum f)
  (hf : is_sum g a) : is_sum f a :=
suffices at_top.map (λs:finset β, s.sum f) ≤ at_top.map (λs:finset γ, s.sum g),
  from le_trans this hf,
by rw [map_at_top_eq, map_at_top_eq];
from (le_infi $ assume b, let ⟨v, hv⟩ := h_eq b in infi_le_of_le v $
  by simp [image_subset_iff_subset_preimage]; exact hv)

lemma is_sum_iff_is_sum
  (h₁ : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ u'.sum g = v'.sum f)
  (h₂ : ∀v:finset β, ∃u:finset γ, ∀u', u ⊆ u' → ∃v', v ⊆ v' ∧ v'.sum f = u'.sum g) :
  is_sum f a ↔ is_sum g a :=
⟨is_sum_of_is_sum h₂, is_sum_of_is_sum h₁⟩

variables
  (h₁ : ∀c, g c ≠ 0 → j (i c) = c) (h₂ : ∀b, f b ≠ 0 → i (j b) = b)
  (h₃ : ∀c, g c ≠ 0 → g c = f (i c)) (h₄ : ∀b, f b ≠ 0 → f b = g (j b))
include h₁ h₂ h₃ h₄

lemma is_sum_of_is_sum_ne_zero : is_sum g a → is_sum f a :=
have j_inj : ∀x y, f x ≠ 0 → f y ≠ 0 → (j x = j y ↔ x = y),
  from assume x y hx hy,
  ⟨assume h,
    have i (j x) = i (j y), from congr_arg i h,
    by rwa [h₂, h₂] at this; assumption,
  congr_arg j⟩,
is_sum_of_is_sum $ assume u, exists.intro ((u.filter $ λc, g c ≠ 0).image i) $
  assume v hv,
  let u' := (v.filter $ λb, f b ≠ 0).image j in
  exists.intro (u ∪ u') $ and.intro subset_union_left $
  have ∀c:γ, c ∈ u ∪ u' → c ∉ u' → g c = 0,
    from assume c hc hnc, classical.by_contradiction $ assume h : g c ≠ 0,
    have c ∈ u,
      from (mem_or_mem_of_mem_union hc).resolve_right hnc,
    have i c ∈ v,
      from mem_of_subset_of_mem hv $ mem_image_iff.mpr ⟨_, mem_filter_iff.mpr ⟨this, h⟩, rfl⟩,
    have j (i c) ∈ u',
      from mem_image_iff.mpr ⟨_, mem_filter_iff.mpr ⟨this, h₃ _ h ▸ h⟩, rfl⟩,
    by rw [h₁ c h] at this; exact hnc this,
  calc (u ∪ u').sum g = u'.sum g :
     (sum_subset subset_union_right this).symm
    ... = (v.filter $ λb, f b ≠ 0).sum (g ∘ j) :
      sum_image $ by simp [j_inj] {contextual := tt}
    ... = (v.filter $ λb, f b ≠ 0).sum f :
      sum_congr $ assume b hx, (h₄ b $ (mem_filter_iff.mp hx).right).symm
    ... = v.sum f :
      sum_subset filter_subset $ by simp [not_not] {contextual := tt}

lemma is_sum_iff_is_sum_of_ne_zero : is_sum f a ↔ is_sum g a :=
iff.intro (is_sum_of_is_sum_ne_zero h₂ h₁ h₄ h₃) (is_sum_of_is_sum_ne_zero h₁ h₂ h₃ h₄)

end is_sum_iff_is_sum_of_iso_ne_zero

lemma is_sum_sigma
  [add_comm_monoid α] [topological_space α] [topological_add_monoid α] [regular_space α]
  {γ : β → Type*} {f : (Σ b:β, γ b) → α} {g : β → α} {a : α}
  (hf : ∀b, is_sum (λc, f ⟨b, c⟩) (g b)) (ha : is_sum f a) : is_sum g a :=
assume s' hs',
let
  ⟨s, hs, hss', hsc⟩ := nhds_is_closed hs',
  ⟨u, hu⟩ := mem_at_top_iff.mp $ ha $ hs,
  fsts := u.image sigma.fst,
  snds := λb, u.bind (λp, (if h : p.1 = b then {cast (congr_arg γ h) p.2} else ∅ : finset (γ b)))
in
have sig_inj : ∀b, ∀c₁ c₂ : γ b, sigma.mk b c₁ = sigma.mk b c₂ ↔ c₁ = c₂,
  from assume b c₁ c₂, ⟨assume h, by cases h; refl, assume h, by simp *⟩,
have sig_image_inj : ∀b₁ b₂, ∀s₁ : finset (γ b₁), ∀s₂ : finset (γ b₂), b₁ ≠ b₂ →
    s₁.image (sigma.mk b₁) ∩ s₂.image (sigma.mk b₂) = ∅,
  from assume b₁ b₂ s₁ s₂ h, ext $ assume ⟨b₃, c₃⟩,
    by simp [mem_image_iff];
    from assume c₁ h₁ eq₁ c₂ h₂ eq₂,
      have h₁ : b₁ = b₃, from congr_arg sigma.fst eq₁,
      have h₂ : b₂ = b₃, from congr_arg sigma.fst eq₂,
      h $ by simp [h₁, h₂],
mem_at_top_iff.mpr $ exists.intro fsts $ assume bs (hbs : fsts ⊆ bs),
  have h : ∀cs:(Πb, b ∈ bs → finset (γ b)),
      (⋂b (hb : b ∈ bs), (λp:Πb, finset (γ b), p b) ⁻¹' {cs' | cs b hb ⊆ cs' }) ∩
      (λp, bs.sum (λb, (p b).sum (λc, f ⟨b, c⟩))) ⁻¹' s ≠ ∅,
    from assume cs,
    let cs' := λb, (if h : b ∈ bs then cs b h else ∅) ∪ snds b in
    let sig : finset (sigma γ) := bs.bind (λb, (cs' b).image (λc, ⟨b, c⟩)) in
    have sum_eq : bs.sum (λb, (cs' b).sum (λc, f ⟨b, c⟩)) = sig.sum f,
      from calc bs.sum (λb, (cs' b).sum (λc, f ⟨b, c⟩)) =
            bs.sum (λb, ((cs' b).image (@sigma.mk β γ b)).sum f) :
          by simp [sum_image, sig_inj]
        ... = sig.sum f :
          (sum_bind $ assume b₁ hb b₂ hb₂ h, sig_image_inj b₁ b₂ (cs' b₁) (cs' b₂) h).symm,
    have sig.sum f ∈ s,
      from hu _ $ subset_iff.mpr $ show ∀x:sigma γ, x ∈ u → x ∈ sig,
        from assume ⟨b, c⟩ hbc,
        have hb : b ∈ fsts, from mem_image_iff.mpr ⟨_, hbc, rfl⟩,
        have hb' : b ∈ bs, from mem_of_subset_of_mem hbs hb,
        have hc : c ∈ snds b, from mem_bind_iff.mpr ⟨_, hbc, by simp; refl⟩,
        have hc' : c ∈ cs' b, by simp [hb', hc],
        by simp [sig, mem_bind_iff];
        from ⟨b, hb', mem_image_iff.mpr ⟨c, hc', rfl⟩⟩,
    ne_empty_iff_exists_mem.mpr $ exists.intro cs' $
    by simp [sum_eq, this]; { intros b hb, simp [cs', hb, finset.subset_union_right] },
  have tendsto (λp:(Πb:β, finset (γ b)), bs.sum (λb, (p b).sum (λc, f ⟨b, c⟩)))
      (⨅b (h : b ∈ bs), at_top.vmap (λp, p b)) (nhds (bs.sum g)),
    from tendsto_sum $
      assume c hc, tendsto_infi' c $ tendsto_infi' hc $ tendsto_compose tendsto_vmap (hf c),
  have bs.sum g ∈ s,
    from mem_closure_of_tendsto this hsc $ forall_sets_neq_empty_iff_neq_bot.mp $
      by simp [mem_inf_sets, exists_imp_distrib, and_imp, forall_and_distrib',
               filter.mem_infi_sets_finset, mem_vmap, skolem, mem_at_top_iff];
      from
        assume s₁ s₂ s₃ hs₁ hs₃ p hs₂ p' hp cs hp',
        have (⋂b (h : b ∈ bs), (λp:(Πb, finset (γ b)), p b) ⁻¹' {cs' | cs b h ⊆ cs' }) ≤ (⨅b∈bs, p b),
          from infi_le_infi $ assume b, infi_le_infi $ assume hb,
            le_trans (preimage_mono $ hp' b hb) (hp b hb),
        neq_bot_of_le_neq_bot (h _) (le_trans (inter_subset_inter (le_trans this hs₂) hs₃) hs₁),
  hss' this

section topological_group
variables [add_comm_group α] [uniform_space α] [complete_space α] [uniform_add_group α]
variables {f g : β → α} {a a₁ a₂ : α}

/- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a` -/
lemma exists_is_sum_of_is_sum {f' : β → α} (hf : is_sum f a) (h : ∀b, f' b = 0 ∨ f' b = f b) :
  ∃a, is_sum f' a :=
suffices cauchy (at_top.map (λs:finset β, s.sum f')),
  from complete_space.complete this,
⟨map_ne_bot at_top_ne_bot,
  assume s' hs',
  have ∃t∈(@uniformity α _).sets, ∀{a₁ a₂ a₃ a₄}, (a₁, a₂) ∈ t → (a₃, a₄) ∈ t → (a₁ - a₃, a₂ - a₄) ∈ s',
  begin
    have h : {p:(α×α)×(α×α)| (p.1.1 - p.1.2, p.2.1 - p.2.2) ∈ s'} ∈ (@uniformity (α × α) _).sets,
      from uniform_continuous_sub' hs',
    rw [uniformity_prod_eq_prod, mem_map, mem_prod_same_iff] at h,
    cases h with t ht, cases ht with ht h,
    exact ⟨t, ht, assume a₁ a₂ a₃ a₄ h₁ h₂, @h ((a₁, a₂), (a₃, a₄)) ⟨h₁, h₂⟩⟩
  end,
  let ⟨s, hs, hss'⟩ := this in
  have cauchy (at_top.map (λs:finset β, s.sum f)),
    from cauchy_downwards cauchy_nhds (map_ne_bot at_top_ne_bot) hf,
  have ∃t, ∀u₁ u₂:finset β, t ⊆ u₁ → t ⊆ u₂ → (u₁.sum f, u₂.sum f) ∈ s,
    by simp [cauchy_iff, mem_at_top_iff] at this;
    from let ⟨t, ht, u, hu⟩ := this s hs in
      ⟨u, assume u₁ u₂ h₁ h₂, ht $ prod_mk_mem_set_prod_eq.mpr ⟨hu _ h₁, hu _ h₂⟩⟩,
  let ⟨t, ht⟩ := this in
  let d := (t.filter (λb, f' b = 0)).sum f in
  have eq : ∀{u}, t ⊆ u → (t ∪ u.filter (λb, f' b ≠ 0)).sum f - d = u.sum f',
    from assume u hu,
    have t ∪ u.filter (λb, f' b ≠ 0) = t.filter (λb, f' b = 0) ∪ u.filter (λb, f' b ≠ 0),
      from ext $ assume b, by by_cases f' b = 0;
        simp [h, subset_iff.mp hu, iff_def, or_imp_distrib] {contextual := tt},
    calc (t ∪ u.filter (λb, f' b ≠ 0)).sum f - d =
        (t.filter (λb, f' b = 0) ∪ u.filter (λb, f' b ≠ 0)).sum f - d : by rw [this]
      ... = (d + (u.filter (λb, f' b ≠ 0)).sum f) - d :
        by rw [sum_union]; exact (ext $ assume b, by simp)
      ... = (u.filter (λb, f' b ≠ 0)).sum f :
        by simp
      ... = (u.filter (λb, f' b ≠ 0)).sum f' :
        sum_congr $ assume b, by have h := h b; cases h with h h; simp [*]
      ... = u.sum f' :
        by apply sum_subset; by simp [subset_iff, not_not] {contextual := tt},
  have ∀{u₁ u₂}, t ⊆ u₁ → t ⊆ u₂ → (u₁.sum f', u₂.sum f') ∈ s',
    from assume u₁ u₂ h₁ h₂,
    have ((t ∪ u₁.filter (λb, f' b ≠ 0)).sum f, (t ∪ u₂.filter (λb, f' b ≠ 0)).sum f) ∈ s,
      from ht _ _ subset_union_left subset_union_left,
    have ((t ∪ u₁.filter (λb, f' b ≠ 0)).sum f - d, (t ∪ u₂.filter (λb, f' b ≠ 0)).sum f - d) ∈ s',
      from hss' this $ refl_mem_uniformity hs,
    by rwa [eq h₁, eq h₂] at this,
  mem_prod_same_iff.mpr ⟨(λu:finset β, u.sum f') '' {u | t ⊆ u},
    image_mem_map $ mem_infi_sets t $ mem_principal_sets.mpr $ subset.refl _,
    assume ⟨a₁, a₂⟩ ⟨⟨t₁, h₁, eq₁⟩, ⟨t₂, h₂, eq₂⟩⟩, by simp at eq₁ eq₂; rw [←eq₁, ←eq₂]; exact this h₁ h₂⟩⟩

end topological_group
