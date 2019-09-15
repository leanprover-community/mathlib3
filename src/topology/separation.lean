/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Separation properties of topological spaces.
-/

import topology.order

open set filter lattice
local attribute [instance] classical.prop_decidable -- TODO: use "open_locale classical"

universes u v
variables {α : Type u} {β : Type v} [topological_space α]

section separation

/-- A T₀ space, also known as a Kolmogorov space, is a topological space
  where for every pair `x ≠ y`, there is an open set containing one but not the other. -/
class t0_space (α : Type u) [topological_space α] : Prop :=
(t0 : ∀ x y, x ≠ y → ∃ U:set α, is_open U ∧ (xor (x ∈ U) (y ∈ U)))

theorem exists_open_singleton_of_fintype [t0_space α]
  [f : fintype α] [decidable_eq α] [ha : nonempty α] :
  ∃ x:α, is_open ({x}:set α) :=
have H : ∀ (T : finset α), T ≠ ∅ → ∃ x ∈ T, ∃ u, is_open u ∧ {x} = {y | y ∈ T} ∩ u :=
begin
  intro T,
  apply finset.case_strong_induction_on T,
  { intro h, exact (h rfl).elim },
  { intros x S hxS ih h,
    by_cases hs : S = ∅,
    { existsi [x, finset.mem_insert_self x S, univ, is_open_univ],
      rw [hs, inter_univ], refl },
    { rcases ih S (finset.subset.refl S) hs with ⟨y, hy, V, hv1, hv2⟩,
      by_cases hxV : x ∈ V,
      { cases t0_space.t0 x y (λ hxy, hxS $ by rwa hxy) with U hu,
        rcases hu with ⟨hu1, ⟨hu2, hu3⟩ | ⟨hu2, hu3⟩⟩,
        { existsi [x, finset.mem_insert_self x S, U ∩ V, is_open_inter hu1 hv1],
          apply set.ext,
          intro z,
          split,
          { intro hzx,
            rw set.mem_singleton_iff at hzx,
            rw hzx,
            exact ⟨finset.mem_insert_self x S, ⟨hu2, hxV⟩⟩ },
          { intro hz,
            rw set.mem_singleton_iff,
            rcases hz with ⟨hz1, hz2, hz3⟩,
            cases finset.mem_insert.1 hz1 with hz4 hz4,
            { exact hz4 },
            { have h1 : z ∈ {y : α | y ∈ S} ∩ V,
              { exact ⟨hz4, hz3⟩ },
              rw ← hv2 at h1,
              rw set.mem_singleton_iff at h1,
              rw h1 at hz2,
              exact (hu3 hz2).elim } } },
        { existsi [y, finset.mem_insert_of_mem hy, U ∩ V, is_open_inter hu1 hv1],
          apply set.ext,
          intro z,
          split,
          { intro hz,
            rw set.mem_singleton_iff at hz,
            rw hz,
            refine ⟨finset.mem_insert_of_mem hy, hu2, _⟩,
            have h1 : y ∈ {y} := set.mem_singleton y,
            rw hv2 at h1,
            exact h1.2 },
          { intro hz,
            rw set.mem_singleton_iff,
            cases hz with hz1 hz2,
            cases finset.mem_insert.1 hz1 with hz3 hz3,
            { rw hz3 at hz2,
              exact (hu3 hz2.1).elim },
            { have h1 : z ∈ {y : α | y ∈ S} ∩ V := ⟨hz3, hz2.2⟩,
              rw ← hv2 at h1,
              rw set.mem_singleton_iff at h1,
              exact h1 } } } },
      { existsi [y, finset.mem_insert_of_mem hy, V, hv1],
        apply set.ext,
        intro z,
        split,
        { intro hz,
          rw set.mem_singleton_iff at hz,
          rw hz,
          split,
          { exact finset.mem_insert_of_mem hy },
          { have h1 : y ∈ {y} := set.mem_singleton y,
            rw hv2 at h1,
            exact h1.2 } },
        { intro hz,
          rw hv2,
          cases hz with hz1 hz2,
          cases finset.mem_insert.1 hz1 with hz3 hz3,
          { rw hz3 at hz2,
            exact (hxV hz2).elim },
          { exact ⟨hz3, hz2⟩ } } } } }
end,
begin
  apply nonempty.elim ha, intro x,
  specialize H finset.univ (finset.ne_empty_of_mem $ finset.mem_univ x),
  rcases H with ⟨y, hyf, U, hu1, hu2⟩,
  existsi y,
  have h1 : {y : α | y ∈ finset.univ} = (univ : set α),
  { exact set.eq_univ_of_forall (λ x : α,
      by rw mem_set_of_eq; exact finset.mem_univ x) },
  rw h1 at hu2,
  rw set.univ_inter at hu2,
  rw hu2,
  exact hu1
end

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`. -/
class t1_space (α : Type u) [topological_space α] : Prop :=
(t1 : ∀x, is_closed ({x} : set α))

lemma is_closed_singleton [t1_space α] {x : α} : is_closed ({x} : set α) :=
t1_space.t1 x

instance t1_space.t0_space [t1_space α] : t0_space α :=
⟨λ x y h, ⟨-{x}, is_open_compl_iff.2 is_closed_singleton,
  or.inr ⟨λ hyx, or.cases_on hyx h.symm id, λ hx, hx $ or.inl rfl⟩⟩⟩

lemma compl_singleton_mem_nhds [t1_space α] {x y : α} (h : y ≠ x) : - {x} ∈ nhds y :=
mem_nhds_sets is_closed_singleton $ by rwa [mem_compl_eq, mem_singleton_iff]

@[simp] lemma closure_singleton [t1_space α] {a : α} :
  closure ({a} : set α) = {a} :=
closure_eq_of_is_closed is_closed_singleton

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
class t2_space (α : Type u) [topological_space α] : Prop :=
(t2 : ∀x y, x ≠ y → ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅)

lemma t2_separation [t2_space α] {x y : α} (h : x ≠ y) :
  ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
t2_space.t2 x y h

instance t2_space.t1_space [t2_space α] : t1_space α :=
⟨λ x, is_open_iff_forall_mem_open.2 $ λ y hxy,
let ⟨u, v, hu, hv, hyu, hxv, huv⟩ := t2_separation (mt mem_singleton_of_eq hxy) in
⟨u, λ z hz1 hz2, ((ext_iff _ _).1 huv x).1 ⟨mem_singleton_iff.1 hz2 ▸ hz1, hxv⟩, hu, hyu⟩⟩

lemma eq_of_nhds_neq_bot [ht : t2_space α] {x y : α} (h : nhds x ⊓ nhds y ≠ ⊥) : x = y :=
classical.by_contradiction $ assume : x ≠ y,
let ⟨u, v, hu, hv, hx, hy, huv⟩ := t2_space.t2 x y this in
have u ∩ v ∈ nhds x ⊓ nhds y,
  from inter_mem_inf_sets (mem_nhds_sets hu hx) (mem_nhds_sets hv hy),
h $ empty_in_sets_eq_bot.mp $ huv ▸ this

lemma t2_iff_nhds : t2_space α ↔ ∀ {x y : α}, nhds x ⊓ nhds y ≠ ⊥ → x = y :=
⟨assume h, by exactI λ x y, eq_of_nhds_neq_bot,
 assume h, ⟨assume x y xy,
   have nhds x ⊓ nhds y = ⊥ := classical.by_contradiction (mt h xy),
   let ⟨u', hu', v', hv', u'v'⟩ := empty_in_sets_eq_bot.mpr this,
       ⟨u, uu', uo, hu⟩ := mem_nhds_sets_iff.mp hu',
       ⟨v, vv', vo, hv⟩ := mem_nhds_sets_iff.mp hv' in
   ⟨u, v, uo, vo, hu, hv, disjoint.eq_bot $ disjoint_mono uu' vv' u'v'⟩⟩⟩

lemma t2_iff_ultrafilter :
  t2_space α ↔ ∀ f {x y : α}, is_ultrafilter f → f ≤ nhds x → f ≤ nhds y → x = y :=
t2_iff_nhds.trans
  ⟨assume h f x y u fx fy, h $ neq_bot_of_le_neq_bot u.1 (le_inf fx fy),
   assume h x y xy,
     let ⟨f, hf, uf⟩ := exists_ultrafilter xy in
     h f uf (le_trans hf lattice.inf_le_left) (le_trans hf lattice.inf_le_right)⟩

@[simp] lemma nhds_eq_nhds_iff {a b : α} [t2_space α] : nhds a = nhds b ↔ a = b :=
⟨assume h, eq_of_nhds_neq_bot $ by rw [h, inf_idem]; exact nhds_neq_bot, assume h, h ▸ rfl⟩

@[simp] lemma nhds_le_nhds_iff {a b : α} [t2_space α] : nhds a ≤ nhds b ↔ a = b :=
⟨assume h, eq_of_nhds_neq_bot $ by rw [inf_of_le_left h]; exact nhds_neq_bot, assume h, h ▸ le_refl _⟩

lemma tendsto_nhds_unique [t2_space α] {f : β → α} {l : filter β} {a b : α}
  (hl : l ≠ ⊥) (ha : tendsto f l (nhds a)) (hb : tendsto f l (nhds b)) : a = b :=
eq_of_nhds_neq_bot $ neq_bot_of_le_neq_bot (map_ne_bot hl) $ le_inf ha hb

section lim
variables [inhabited α] [t2_space α] {f : filter α}

lemma lim_eq {a : α} (hf : f ≠ ⊥) (h : f ≤ nhds a) : lim f = a :=
eq_of_nhds_neq_bot $ neq_bot_of_le_neq_bot hf $ le_inf (lim_spec ⟨_, h⟩) h

@[simp] lemma lim_nhds_eq {a : α} : lim (nhds a) = a :=
lim_eq nhds_neq_bot (le_refl _)

@[simp] lemma lim_nhds_eq_of_closure {a : α} {s : set α} (h : a ∈ closure s) :
  lim (nhds a ⊓ principal s) = a :=
lim_eq begin rw [closure_eq_nhds] at h, exact h end inf_le_left
end lim

instance t2_space_discrete {α : Type*} [topological_space α] [discrete_topology α] : t2_space α :=
{ t2 := assume x y hxy, ⟨{x}, {y}, is_open_discrete _, is_open_discrete _, mem_insert _ _, mem_insert _ _,
  eq_empty_iff_forall_not_mem.2 $ by intros z hz;
    cases eq_of_mem_singleton hz.1; cases eq_of_mem_singleton hz.2; cc⟩ }

private lemma separated_by_f {α : Type*} {β : Type*}
  [tα : topological_space α] [tβ : topological_space β] [t2_space β]
  (f : α → β) (hf : tα ≤ tβ.induced f) {x y : α} (h : f x ≠ f y) :
  ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h in
⟨f ⁻¹' u, f ⁻¹' v, hf _ ⟨u, uo, rfl⟩, hf _ ⟨v, vo, rfl⟩, xu, yv,
  by rw [←preimage_inter, uv, preimage_empty]⟩

instance {α : Type*} {p : α → Prop} [t : topological_space α] [t2_space α] : t2_space (subtype p) :=
⟨assume x y h,
  separated_by_f subtype.val (le_refl _) (mt subtype.eq h)⟩

instance {α : Type*} {β : Type*} [t₁ : topological_space α] [t2_space α]
  [t₂ : topological_space β] [t2_space β] : t2_space (α × β) :=
⟨assume ⟨x₁,x₂⟩ ⟨y₁,y₂⟩ h,
  or.elim (not_and_distrib.mp (mt prod.ext_iff.mpr h))
    (λ h₁, separated_by_f prod.fst inf_le_left h₁)
    (λ h₂, separated_by_f prod.snd inf_le_right h₂)⟩

instance Pi.t2_space {α : Type*} {β : α → Type v} [t₂ : Πa, topological_space (β a)] [Πa, t2_space (β a)] :
  t2_space (Πa, β a) :=
⟨assume x y h,
  let ⟨i, hi⟩ := not_forall.mp (mt funext h) in
  separated_by_f (λz, z i) (infi_le _ i) hi⟩

end separation

section regularity

/-- A T₃ space, also known as a regular space (although this condition sometimes
  omits T₂), is one in which for every closed `C` and `x ∉ C`, there exist
  disjoint open sets containing `x` and `C` respectively. -/
class regular_space (α : Type u) [topological_space α] extends t1_space α : Prop :=
(regular : ∀{s:set α} {a}, is_closed s → a ∉ s → ∃t, is_open t ∧ s ⊆ t ∧ nhds a ⊓ principal t = ⊥)

lemma nhds_is_closed [regular_space α] {a : α} {s : set α} (h : s ∈ nhds a) :
  ∃t∈(nhds a), t ⊆ s ∧ is_closed t :=
let ⟨s', h₁, h₂, h₃⟩ := mem_nhds_sets_iff.mp h in
have ∃t, is_open t ∧ -s' ⊆ t ∧ nhds a ⊓ principal t = ⊥,
  from regular_space.regular (is_closed_compl_iff.mpr h₂) (not_not_intro h₃),
let ⟨t, ht₁, ht₂, ht₃⟩ := this in
⟨-t,
  mem_sets_of_neq_bot $ by rwa [lattice.neg_neg],
  subset.trans (compl_subset_comm.1 ht₂) h₁,
  is_closed_compl_iff.mpr ht₁⟩

variable (α)
instance regular_space.t2_space [regular_space α] : t2_space α :=
⟨λ x y hxy,
let ⟨s, hs, hys, hxs⟩ := regular_space.regular is_closed_singleton
    (mt mem_singleton_iff.1 hxy),
  ⟨t, hxt, u, hsu, htu⟩ := empty_in_sets_eq_bot.2 hxs,
  ⟨v, hvt, hv, hxv⟩ := mem_nhds_sets_iff.1 hxt in
⟨v, s, hv, hs, hxv, singleton_subset_iff.1 hys,
eq_empty_of_subset_empty $ λ z ⟨hzv, hzs⟩, htu ⟨hvt hzv, hsu hzs⟩⟩⟩

end regularity

section normality

/-- A T₄ space, also known as a normal space (although this condition sometimes
  omits T₂), is one in which for every pair of disjoint closed sets `C` and `D`,
  there exist disjoint open sets containing `C` and `D` respectively. -/
class normal_space (α : Type u) [topological_space α] extends t1_space α : Prop :=
(normal : ∀ s t : set α, is_closed s → is_closed t → disjoint s t →
  ∃ u v, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v)

theorem normal_separation [normal_space α] (s t : set α)
  (H1 : is_closed s) (H2 : is_closed t) (H3 : disjoint s t) :
  ∃ u v, is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ disjoint u v :=
normal_space.normal s t H1 H2 H3

variable (α)
instance normal_space.regular_space [normal_space α] : regular_space α :=
{ regular := λ s x hs hxs, let ⟨u, v, hu, hv, hsu, hxv, huv⟩ := normal_separation s {x} hs is_closed_singleton
      (λ _ ⟨hx, hy⟩, hxs $ set.mem_of_eq_of_mem (set.eq_of_mem_singleton hy).symm hx) in
    ⟨u, hu, hsu, filter.empty_in_sets_eq_bot.1 $ filter.mem_inf_sets.2
      ⟨v, mem_nhds_sets hv (set.singleton_subset_iff.1 hxv), u, filter.mem_principal_self u, set.inter_comm u v ▸ huv⟩⟩ }

end normality
