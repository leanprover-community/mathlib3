/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
import order.filter.cofinite

/-!
# Ultrafilters

An ultrafilter is a minimal (maximal in the set order) proper filter.
In this file we define

* `is_ultrafilter`: a predicate stating that a given filter is an ultrafiler;
* `ultrafilter_of`: an ultrafilter that is less than or equal to a given filter;
* `ultrafilter`: subtype of ultrafilters;
* `ultrafilter.pure`: `pure x` as an `ultrafiler`;
* `ultrafilter.map`, `ultrafilter.bind` : operations on ultrafilters;
* `hyperfilter`: the ultra-filter extending the cofinite filter.
-/

universes u v
variables {α : Type u} {β : Type v}

namespace filter

open set zorn
open_locale classical

variables {f g : filter α}

/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
def is_ultrafilter (f : filter α) := f ≠ ⊥ ∧ ∀g, g ≠ ⊥ → g ≤ f → f ≤ g

lemma ultrafilter_unique (hg : is_ultrafilter g) (hf : f ≠ ⊥) (h : f ≤ g) : f = g :=
le_antisymm h (hg.right _ hf h)

lemma le_of_ultrafilter {g : filter α} (hf : is_ultrafilter f) (h : f ⊓ g ≠ ⊥) :
  f ≤ g :=
le_of_inf_eq $ ultrafilter_unique hf h inf_le_left

/-- Equivalent characterization of ultrafilters:
  A filter f is an ultrafilter if and only if for each set s,
  -s belongs to f if and only if s does not belong to f. -/
lemma ultrafilter_iff_compl_mem_iff_not_mem :
  is_ultrafilter f ↔ (∀ s, -s ∈ f ↔ s ∉ f) :=
⟨assume hf s,
   ⟨assume hns hs,
      hf.1 $ empty_in_sets_eq_bot.mp $ by convert f.inter_sets hs hns; rw [inter_compl_self],
    assume hs,
      have f ≤ principal (-s), from
        le_of_ultrafilter hf $ assume h, hs $ mem_sets_of_eq_bot $
          by simp only [h, eq_self_iff_true, compl_compl],
      by simp only [le_principal_iff] at this; assumption⟩,
 assume hf,
   ⟨mt empty_in_sets_eq_bot.mpr ((hf ∅).mp (by convert f.univ_sets; rw [compl_empty])),
    assume g hg g_le s hs, classical.by_contradiction $ mt (hf s).mpr $
      assume : - s ∈ f,
        have s ∩ -s ∈ g, from inter_mem_sets hs (g_le this),
        by simp only [empty_in_sets_eq_bot, hg, inter_compl_self] at this; contradiction⟩⟩

lemma mem_or_compl_mem_of_ultrafilter (hf : is_ultrafilter f) (s : set α) :
  s ∈ f ∨ - s ∈ f :=
classical.or_iff_not_imp_left.2 (ultrafilter_iff_compl_mem_iff_not_mem.mp hf s).mpr

lemma mem_or_mem_of_ultrafilter {s t : set α} (hf : is_ultrafilter f) (h : s ∪ t ∈ f) :
  s ∈ f ∨ t ∈ f :=
(mem_or_compl_mem_of_ultrafilter hf s).imp_right
  (assume : -s ∈ f, by filter_upwards [this, h] assume x hnx hx, hx.resolve_left hnx)

lemma mem_of_finite_sUnion_ultrafilter {s : set (set α)} (hf : is_ultrafilter f) (hs : finite s)
  : ⋃₀ s ∈ f → ∃t∈s, t ∈ f :=
finite.induction_on hs (by simp only [empty_in_sets_eq_bot, hf.left, mem_empty_eq, sUnion_empty,
  forall_prop_of_false, exists_false, not_false_iff, exists_prop_of_false]) $
λ t s' ht' hs' ih, by simp only [exists_prop, mem_insert_iff, set.sUnion_insert]; exact
assume h, (mem_or_mem_of_ultrafilter hf h).elim
  (assume : t ∈ f, ⟨t, or.inl rfl, this⟩)
  (assume h, let ⟨t, hts', ht⟩ := ih h in ⟨t, or.inr hts', ht⟩)

lemma mem_of_finite_Union_ultrafilter {is : set β} {s : β → set α}
  (hf : is_ultrafilter f) (his : finite is) (h : (⋃i∈is, s i) ∈ f) : ∃i∈is, s i ∈ f :=
have his : finite (image s is), from finite_image s his,
have h : (⋃₀ image s is) ∈ f, from by simp only [sUnion_image, set.sUnion_image]; assumption,
let ⟨t, ⟨i, hi, h_eq⟩, (ht : t ∈ f)⟩ := mem_of_finite_sUnion_ultrafilter hf his h in
⟨i, hi, h_eq.symm ▸ ht⟩

lemma ultrafilter_map {f : filter α} {m : α → β} (h : is_ultrafilter f) :
  is_ultrafilter (map m f) :=
by rw ultrafilter_iff_compl_mem_iff_not_mem at ⊢ h; exact assume s, h (m ⁻¹' s)

lemma ultrafilter_pure {a : α} : is_ultrafilter (pure a) :=
begin
  rw ultrafilter_iff_compl_mem_iff_not_mem, intro s,
  rw [mem_pure_sets, mem_pure_sets], exact iff.rfl
end

lemma ultrafilter_bind {f : filter α} (hf : is_ultrafilter f) {m : α → filter β}
  (hm : ∀ a, is_ultrafilter (m a)) : is_ultrafilter (f.bind m) :=
begin
  simp only [ultrafilter_iff_compl_mem_iff_not_mem] at ⊢ hf hm, intro s,
  dsimp [bind, join, map, preimage],
  simp only [hm], apply hf
end

/-- The ultrafilter lemma: Any proper filter is contained in an ultrafilter. -/
lemma exists_ultrafilter (h : f ≠ ⊥) : ∃u, u ≤ f ∧ is_ultrafilter u :=
let
  τ                := {f' // f' ≠ ⊥ ∧ f' ≤ f},
  r : τ → τ → Prop := λt₁ t₂, t₂.val ≤ t₁.val,
  ⟨a, ha⟩          := nonempty_of_mem_sets h univ_mem_sets,
  top : τ          := ⟨f, h, le_refl f⟩,
  sup : Π(c:set τ), chain r c → τ :=
    λc hc, ⟨⨅a:{a:τ // a ∈ insert top c}, a.val.val,
      infi_ne_bot_of_directed ⟨a⟩
        (directed_of_chain $ chain_insert hc $ assume ⟨b, _, hb⟩ _ _, or.inl hb)
        (assume ⟨⟨a, ha, _⟩, _⟩, ha),
      infi_le_of_le ⟨top, mem_insert _ _⟩ (le_refl _)⟩
in
have ∀c (hc: chain r c) a (ha : a ∈ c), r a (sup c hc),
  from assume c hc a ha, infi_le_of_le ⟨a, mem_insert_of_mem _ ha⟩ (le_refl _),
have (∃ (u : τ), ∀ (a : τ), r u a → r a u),
  from exists_maximal_of_chains_bounded (assume c hc, ⟨sup c hc, this c hc⟩)
    (assume f₁ f₂ f₃ h₁ h₂, le_trans h₂ h₁),
let ⟨uτ, hmin⟩ := this in
⟨uτ.val, uτ.property.right, uτ.property.left, assume g hg₁ hg₂,
  hmin ⟨g, hg₁, le_trans hg₂ uτ.property.right⟩ hg₂⟩

/-- Construct an ultrafilter extending a given filter.
  The ultrafilter lemma is the assertion that such a filter exists;
  we use the axiom of choice to pick one. -/
noncomputable def ultrafilter_of (f : filter α) : filter α :=
if h : f = ⊥ then ⊥ else classical.epsilon (λu, u ≤ f ∧ is_ultrafilter u)

lemma ultrafilter_of_spec (h : f ≠ ⊥) : ultrafilter_of f ≤ f ∧ is_ultrafilter (ultrafilter_of f) :=
begin
  have h' := classical.epsilon_spec (exists_ultrafilter h),
  simp only [ultrafilter_of, dif_neg, h, dif_neg, not_false_iff],
  simp only at h',
  assumption
end

lemma ultrafilter_of_le : ultrafilter_of f ≤ f :=
if h : f = ⊥ then by simp only [ultrafilter_of, h, dif_pos, le_bot_iff]
  else (ultrafilter_of_spec h).left

lemma ultrafilter_ultrafilter_of (h : f ≠ ⊥) : is_ultrafilter (ultrafilter_of f) :=
(ultrafilter_of_spec h).right

lemma ultrafilter_of_ultrafilter (h : is_ultrafilter f) : ultrafilter_of f = f :=
ultrafilter_unique h (ultrafilter_ultrafilter_of h.left).left ultrafilter_of_le

/-- A filter equals the intersection of all the ultrafilters which contain it. -/
lemma sup_of_ultrafilters (f : filter α) : f = ⨆ (g) (u : is_ultrafilter g) (H : g ≤ f), g :=
begin
  refine le_antisymm _ (supr_le $ λ g, supr_le $ λ u, supr_le $ λ H, H),
  intros s hs,
  -- If s ∉ f.sets, we'll apply the ultrafilter lemma to the restriction of f to -s.
  by_contradiction hs',
  let j : (-s) → α := subtype.val,
  have j_inv_s : j ⁻¹' s = ∅, by
    erw [←preimage_inter_range, subtype.val_range, inter_compl_self, preimage_empty],
  let f' := comap j f,
  have : f' ≠ ⊥,
  { apply mt empty_in_sets_eq_bot.mpr,
    rintro ⟨t, htf, ht⟩,
    suffices : t ⊆ s, from absurd (f.sets_of_superset htf this) hs',
    rw [subset_empty_iff] at ht,
    have : j '' (j ⁻¹' t) = ∅, by rw [ht, image_empty],
    erw [image_preimage_eq_inter_range, subtype.val_range, ←subset_compl_iff_disjoint,
      set.compl_compl] at this,
    exact this },
  rcases exists_ultrafilter this with ⟨g', g'f', u'⟩,
  simp only [supr_sets_eq, mem_Inter] at hs,
  have := hs (g'.map subtype.val) (ultrafilter_map u') (map_le_iff_le_comap.mpr g'f'),
  rw [←le_principal_iff, map_le_iff_le_comap, comap_principal, j_inv_s, principal_empty,
    le_bot_iff] at this,
  exact absurd this u'.1
end

/-- The `tendsto` relation can be checked on ultrafilters. -/
lemma tendsto_iff_ultrafilter (f : α → β) (l₁ : filter α) (l₂ : filter β) :
  tendsto f l₁ l₂ ↔ ∀ g, is_ultrafilter g → g ≤ l₁ → g.map f ≤ l₂ :=
⟨assume h g u gx, le_trans (map_mono gx) h,
 assume h, by rw [sup_of_ultrafilters l₁]; simpa only [tendsto, map_supr, supr_le_iff]⟩

/-- The ultrafilter monad. The monad structure on ultrafilters is the
  restriction of the one on filters. -/
def ultrafilter (α : Type u) : Type u := {f : filter α // is_ultrafilter f}

/-- Push-forward for ultra-filters. -/
def ultrafilter.map (m : α → β) (u : ultrafilter α) : ultrafilter β :=
⟨u.val.map m, ultrafilter_map u.property⟩

/-- The principal ultra-filter associated to a point `x`. -/
def ultrafilter.pure (x : α) : ultrafilter α := ⟨pure x, ultrafilter_pure⟩

/-- Monadic bind for ultra-filters, coming from the one on filters
defined in terms of map and join.-/
def ultrafilter.bind (u : ultrafilter α) (m : α → ultrafilter β) : ultrafilter β :=
⟨u.val.bind (λ a, (m a).val), ultrafilter_bind u.property (λ a, (m a).property)⟩

instance ultrafilter.has_pure : has_pure ultrafilter := ⟨@ultrafilter.pure⟩
instance ultrafilter.has_bind : has_bind ultrafilter := ⟨@ultrafilter.bind⟩
instance ultrafilter.functor : functor ultrafilter := { map := @ultrafilter.map }
instance ultrafilter.monad : monad ultrafilter := { map := @ultrafilter.map }

instance ultrafilter.inhabited [inhabited α] : inhabited (ultrafilter α) := ⟨pure (default _)⟩

/-- The ultra-filter extending the cofinite filter. -/
noncomputable def hyperfilter : filter α := ultrafilter_of cofinite

lemma hyperfilter_le_cofinite : @hyperfilter α ≤ cofinite :=
ultrafilter_of_le

lemma is_ultrafilter_hyperfilter [infinite α] : is_ultrafilter (@hyperfilter α) :=
(ultrafilter_of_spec cofinite_ne_bot).2

theorem nmem_hyperfilter_of_finite [infinite α] {s : set α} (hf : s.finite) :
  s ∉ @hyperfilter α :=
λ hy,
have hx : -s ∉ hyperfilter :=
  λ hs, (ultrafilter_iff_compl_mem_iff_not_mem.mp is_ultrafilter_hyperfilter s).mp hs hy,
have ht : -s ∈ cofinite.sets := by show -s ∈ {s | _}; rwa [set.mem_set_of_eq, compl_compl],
hx $ hyperfilter_le_cofinite ht

theorem compl_mem_hyperfilter_of_finite [infinite α] {s : set α} (hf : set.finite s) :
  -s ∈ @hyperfilter α :=
(ultrafilter_iff_compl_mem_iff_not_mem.mp is_ultrafilter_hyperfilter s).mpr $
nmem_hyperfilter_of_finite hf

theorem mem_hyperfilter_of_finite_compl [infinite α] {s : set α} (hf : set.finite (-s)) :
  s ∈ @hyperfilter α :=
s.compl_compl ▸ compl_mem_hyperfilter_of_finite hf

section

local attribute [instance] filter.monad filter.is_lawful_monad

instance ultrafilter.is_lawful_monad : is_lawful_monad ultrafilter :=
{ id_map := assume α f, subtype.eq (id_map f.val),
  pure_bind := assume α β a f, subtype.eq (pure_bind a (subtype.val ∘ f)),
  bind_assoc := assume α β γ f m₁ m₂, subtype.eq (filter_eq rfl),
  bind_pure_comp_eq_map := assume α β f x, subtype.eq (bind_pure_comp_eq_map f x.val) }

end

lemma ultrafilter.eq_iff_val_le_val {u v : ultrafilter α} : u = v ↔ u.val ≤ v.val :=
⟨assume h, by rw h; exact le_refl _,
 assume h, by rw subtype.ext; apply ultrafilter_unique v.property u.property.1 h⟩

lemma exists_ultrafilter_iff (f : filter α) : (∃ (u : ultrafilter α), u.val ≤ f) ↔ f ≠ ⊥ :=
⟨assume ⟨u, uf⟩, ne_bot_of_le_ne_bot u.property.1 uf,
 assume h, let ⟨u, uf, hu⟩ := exists_ultrafilter h in ⟨⟨u, hu⟩, uf⟩⟩

end filter
