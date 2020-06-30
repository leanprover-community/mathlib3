/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.constructions

/-!
# Neighborhoods and continuity relative to a subset

This file defines relative versions

`nhds_within`           of `nhds`
`continuous_on`         of `continuous`
`continuous_within_at`  of `continuous_at`

and proves their basic properties, including the relationships between
these restricted notions and the corresponding notions for the subtype
equipped with the subspace topology.

-/

open set filter
open_locale topological_space filter

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables [topological_space α]

/-- The "neighborhood within" filter. Elements of `nhds_within a s` are sets containing the
intersection of `s` and a neighborhood of `a`. -/
def nhds_within (a : α) (s : set α) : filter α := 𝓝 a ⊓ 𝓟 s

theorem nhds_within_eq (a : α) (s : set α) :
  nhds_within a s = ⨅ t ∈ {t : set α | a ∈ t ∧ is_open t}, 𝓟 (t ∩ s) :=
have set.univ ∈ {s : set α | a ∈ s ∧ is_open s}, from ⟨set.mem_univ _, is_open_univ⟩,
begin
  rw [nhds_within, nhds, binfi_inf]; try { exact this },
  simp only [inf_principal]
end

theorem nhds_within_univ (a : α) : nhds_within a set.univ = 𝓝 a :=
by rw [nhds_within, principal_univ, inf_top_eq]

lemma nhds_within_has_basis {p : β → Prop} {s : β → set α} {a : α} (h : (𝓝 a).has_basis p s)
  (t : set α) :
  (nhds_within a t).has_basis p (λ i, s i ∩ t) :=
h.inf_principal t

lemma nhds_within_basis_open (a : α) (t : set α) :
  (nhds_within a t).has_basis (λ u, a ∈ u ∧ is_open u) (λ u, u ∩ t) :=
nhds_within_has_basis (nhds_basis_opens a) t

theorem mem_nhds_within {t : set α} {a : α} {s : set α} :
  t ∈ nhds_within a s ↔ ∃ u, is_open u ∧ a ∈ u ∧ u ∩ s ⊆ t  :=
by simpa only [exists_prop, and_assoc, and_comm] using (nhds_within_basis_open a s).mem_iff

lemma mem_nhds_within_iff_exists_mem_nhds_inter {t : set α} {a : α} {s : set α} :
  t ∈ nhds_within a s ↔ ∃ u ∈ 𝓝 a, u ∩ s ⊆ t :=
(nhds_within_has_basis (𝓝 a).basis_sets s).mem_iff

lemma nhds_of_nhds_within_of_nhds
  {s t : set α} {a : α} (h1 : s ∈ 𝓝 a) (h2 : t ∈ nhds_within a s) : (t ∈ 𝓝 a) :=
begin
  rcases mem_nhds_within_iff_exists_mem_nhds_inter.mp h2 with ⟨_, Hw, hw⟩,
  exact (nhds a).sets_of_superset ((nhds a).inter_sets Hw h1) hw,
end

lemma mem_nhds_within_of_mem_nhds {s t : set α} {a : α} (h : s ∈ 𝓝 a) :
  s ∈ nhds_within a t :=
mem_inf_sets_of_left h

theorem self_mem_nhds_within {a : α} {s : set α} : s ∈ nhds_within a s :=
mem_inf_sets_of_right (mem_principal_self s)

theorem inter_mem_nhds_within (s : set α) {t : set α} {a : α} (h : t ∈ 𝓝 a) :
  s ∩ t ∈ nhds_within a s :=
inter_mem_sets (mem_inf_sets_of_right (mem_principal_self s)) (mem_inf_sets_of_left h)

theorem nhds_within_mono (a : α) {s t : set α} (h : s ⊆ t) : nhds_within a s ≤ nhds_within a t :=
inf_le_inf_left _ (principal_mono.mpr h)

lemma mem_of_mem_nhds_within {a : α} {s t : set α} (ha : a ∈ s) (ht : t ∈ nhds_within a s) :
  a ∈ t :=
let ⟨u, hu, H⟩ := mem_nhds_within.1 ht in H.2 ⟨H.1, ha⟩

lemma filter.eventually.self_of_nhds_within {p : α → Prop} {s : set α} {x : α}
  (h : ∀ᶠ y in nhds_within x s, p y) (hx : x ∈ s) : p x :=
mem_of_mem_nhds_within hx h

theorem nhds_within_restrict'' {a : α} (s : set α) {t : set α} (h : t ∈ nhds_within a s) :
  nhds_within a s = nhds_within a (s ∩ t) :=
le_antisymm
  (le_inf inf_le_left (le_principal_iff.mpr (inter_mem_sets self_mem_nhds_within h)))
  (inf_le_inf_left _ (principal_mono.mpr (set.inter_subset_left _ _)))

theorem nhds_within_restrict' {a : α} (s : set α) {t : set α} (h : t ∈ 𝓝 a) :
  nhds_within a s = nhds_within a (s ∩ t) :=
nhds_within_restrict'' s $ mem_inf_sets_of_left h

theorem nhds_within_restrict {a : α} (s : set α) {t : set α} (h₀ : a ∈ t) (h₁ : is_open t) :
  nhds_within a s = nhds_within a (s ∩ t) :=
nhds_within_restrict' s (mem_nhds_sets h₁ h₀)

theorem nhds_within_le_of_mem {a : α} {s t : set α} (h : s ∈ nhds_within a t) :
  nhds_within a t ≤ nhds_within a s :=
begin
  rcases mem_nhds_within.1 h with ⟨u, u_open, au, uts⟩,
  have : nhds_within a t = nhds_within a (t ∩ u) := nhds_within_restrict _ au u_open,
  rw [this, inter_comm],
  exact nhds_within_mono _ uts
end

theorem nhds_within_eq_nhds_within {a : α} {s t u : set α}
    (h₀ : a ∈ s) (h₁ : is_open s) (h₂ : t ∩ s = u ∩ s) :
  nhds_within a t = nhds_within a u :=
by rw [nhds_within_restrict t h₀ h₁, nhds_within_restrict u h₀ h₁, h₂]

theorem nhds_within_eq_of_open {a : α} {s : set α} (h₀ : a ∈ s) (h₁ : is_open s) :
  nhds_within a s = 𝓝 a :=
by rw [←nhds_within_univ]; apply nhds_within_eq_nhds_within h₀ h₁;
     rw [set.univ_inter, set.inter_self]

@[simp] theorem nhds_within_empty (a : α) : nhds_within a {} = ⊥ :=
by rw [nhds_within, principal_empty, inf_bot_eq]

theorem nhds_within_union (a : α) (s t : set α) :
  nhds_within a (s ∪ t) = nhds_within a s ⊔ nhds_within a t :=
by unfold nhds_within; rw [←inf_sup_left, sup_principal]

theorem nhds_within_inter (a : α) (s t : set α) :
  nhds_within a (s ∩ t) = nhds_within a s ⊓ nhds_within a t :=
by unfold nhds_within; rw [inf_left_comm, inf_assoc, inf_principal,
                             ←inf_assoc, inf_idem]

theorem nhds_within_inter' (a : α) (s t : set α) :
  nhds_within a (s ∩ t) = (nhds_within a s) ⊓ 𝓟 t :=
by { unfold nhds_within, rw [←inf_principal, inf_assoc] }

lemma nhds_within_prod_eq {α : Type*} [topological_space α] {β : Type*} [topological_space β]
  (a : α) (b : β) (s : set α) (t : set β) :
  nhds_within (a, b) (s.prod t) = (nhds_within a s).prod (nhds_within b t) :=
by { unfold nhds_within, rw [nhds_prod_eq, ←filter.prod_inf_prod, filter.prod_principal_principal] }

theorem tendsto_if_nhds_within {f g : α → β} {p : α → Prop} [decidable_pred p]
    {a : α} {s : set α} {l : filter β}
    (h₀ : tendsto f (nhds_within a (s ∩ p)) l)
    (h₁ : tendsto g (nhds_within a (s ∩ {x | ¬ p x})) l) :
  tendsto (λ x, if p x then f x else g x) (nhds_within a s) l :=
by apply tendsto_if; rw [←nhds_within_inter']; assumption

lemma map_nhds_within (f : α → β) (a : α) (s : set α) :
  map f (nhds_within a s) =
    ⨅ t ∈ {t : set α | a ∈ t ∧ is_open t}, 𝓟 (set.image f (t ∩ s)) :=
((nhds_within_basis_open a s).map f).eq_binfi

theorem tendsto_nhds_within_mono_left {f : α → β} {a : α}
    {s t : set α} {l : filter β} (hst : s ⊆ t) (h : tendsto f (nhds_within a t) l) :
  tendsto f (nhds_within a s) l :=
tendsto_le_left (nhds_within_mono a hst) h

theorem tendsto_nhds_within_mono_right {f : β → α} {l : filter β}
    {a : α} {s t : set α} (hst : s ⊆ t) (h : tendsto f l (nhds_within a s)) :
  tendsto f l (nhds_within a t) :=
tendsto_le_right (nhds_within_mono a hst) h

theorem tendsto_nhds_within_of_tendsto_nhds {f : α → β} {a : α}
    {s : set α} {l : filter β} (h : tendsto f (𝓝 a) l) :
  tendsto f (nhds_within a s) l :=
by rw [←nhds_within_univ] at h; exact tendsto_nhds_within_mono_left (set.subset_univ _) h

theorem principal_subtype {α : Type*} (s : set α) (t : set {x // x ∈ s}) :
  𝓟 t = comap coe (𝓟 ((coe : s → α) '' t)) :=
by rw comap_principal; rw set.preimage_image_eq; apply subtype.coe_injective

lemma mem_closure_iff_nhds_within_ne_bot {s : set α} {x : α} :
  x ∈ closure s ↔ nhds_within x s ≠ ⊥ :=
mem_closure_iff_nhds.trans (nhds_within_has_basis (𝓝 x).basis_sets s).forall_nonempty_iff_ne_bot

lemma nhds_within_ne_bot_of_mem {s : set α} {x : α} (hx : x ∈ s) :
  nhds_within x s ≠ ⊥ :=
mem_closure_iff_nhds_within_ne_bot.1 $ subset_closure hx

lemma is_closed.mem_of_nhds_within_ne_bot {s : set α} (hs : is_closed s)
  {x : α} (hx : nhds_within x s ≠ ⊥) : x ∈ s :=
by simpa only [hs.closure_eq] using mem_closure_iff_nhds_within_ne_bot.2 hx

/-
nhds_within and subtypes
-/

theorem mem_nhds_within_subtype (s : set α) (a : {x // x ∈ s}) (t u : set {x // x ∈ s}) :
  t ∈ nhds_within a u ↔
    t ∈ comap (coe : s → α) (nhds_within a (coe '' u)) :=
by rw [nhds_within, nhds_subtype, principal_subtype, ←comap_inf, ←nhds_within]

theorem nhds_within_subtype (s : set α) (a : {x // x ∈ s}) (t : set {x // x ∈ s}) :
  nhds_within a t = comap (coe : s → α) (nhds_within a (coe '' t)) :=
filter_eq $ by ext u; rw mem_nhds_within_subtype

theorem nhds_within_eq_map_subtype_coe {s : set α} {a : α} (h : a ∈ s) :
  nhds_within a s = map (coe : s → α) (𝓝 ⟨a, h⟩) :=
have h₀ : s ∈ nhds_within a s,
  by { rw [mem_nhds_within], existsi set.univ, simp [set.diff_eq] },
have h₁ : ∀ y ∈ s, ∃ x : s, ↑x = y,
  from λ y h, ⟨⟨y, h⟩, rfl⟩,
begin
  rw [←nhds_within_univ, nhds_within_subtype, subtype.coe_image_univ],
  exact (map_comap_of_surjective' h₀ h₁).symm,
end

theorem tendsto_nhds_within_iff_subtype {s : set α} {a : α} (h : a ∈ s) (f : α → β) (l : filter β) :
  tendsto f (nhds_within a s) l ↔ tendsto (s.restrict f) (𝓝 ⟨a, h⟩) l :=
by { simp only [tendsto, nhds_within_eq_map_subtype_coe h, filter.map_map], refl }

variables [topological_space β] [topological_space γ] [topological_space δ]

/-- A function between topological spaces is continuous at a point `x₀` within a subset `s`
if `f x` tends to `f x₀` when `x` tends to `x₀` while staying within `s`. -/
def continuous_within_at (f : α → β) (s : set α) (x : α) : Prop :=
tendsto f (nhds_within x s) (𝓝 (f x))

/-- If a function is continuous within `s` at `x`, then it tends to `f x` within `s` by definition.
We register this fact for use with the dot notation, especially to use `tendsto.comp` as
`continuous_within_at.comp` will have a different meaning. -/
lemma continuous_within_at.tendsto {f : α → β} {s : set α} {x : α} (h : continuous_within_at f s x) :
  tendsto f (nhds_within x s) (𝓝 (f x)) := h

/-- A function between topological spaces is continuous on a subset `s`
when it's continuous at every point of `s` within `s`. -/
def continuous_on (f : α → β) (s : set α) : Prop := ∀ x ∈ s, continuous_within_at f s x

lemma continuous_on.continuous_within_at {f : α → β} {s : set α} {x : α} (hf : continuous_on f s)
  (hx : x ∈ s) : continuous_within_at f s x :=
hf x hx

theorem continuous_within_at_univ (f : α → β) (x : α) :
  continuous_within_at f set.univ x ↔ continuous_at f x :=
by rw [continuous_at, continuous_within_at, nhds_within_univ]

theorem continuous_within_at_iff_continuous_at_restrict (f : α → β) {x : α} {s : set α} (h : x ∈ s) :
  continuous_within_at f s x ↔ continuous_at (s.restrict f) ⟨x, h⟩ :=
tendsto_nhds_within_iff_subtype h f _

theorem continuous_within_at.tendsto_nhds_within_image {f : α → β} {x : α} {s : set α}
  (h : continuous_within_at f s x) :
  tendsto f (nhds_within x s) (nhds_within (f x) (f '' s)) :=
tendsto_inf.2 ⟨h, tendsto_principal.2 $
  mem_inf_sets_of_right $ mem_principal_sets.2 $
  λ x, mem_image_of_mem _⟩

lemma continuous_within_at.prod_map {f : α → γ} {g : β → δ} {s : set α} {t : set β}
  {x : α} {y : β}
  (hf : continuous_within_at f s x) (hg : continuous_within_at g t y) :
  continuous_within_at (prod.map f g) (s.prod t) (x, y) :=
begin
  unfold continuous_within_at at *,
  rw [nhds_within_prod_eq, prod.map, nhds_prod_eq],
  exact hf.prod_map hg,
end

theorem continuous_on_iff {f : α → β} {s : set α} :
  continuous_on f s ↔ ∀ x ∈ s, ∀ t : set β, is_open t → f x ∈ t → ∃ u, is_open u ∧ x ∈ u ∧
    u ∩ s ⊆ f ⁻¹' t :=
by simp only [continuous_on, continuous_within_at, tendsto_nhds, mem_nhds_within]

theorem continuous_on_iff_continuous_restrict {f : α → β} {s : set α} :
  continuous_on f s ↔ continuous (s.restrict f) :=
begin
  rw [continuous_on, continuous_iff_continuous_at], split,
  { rintros h ⟨x, xs⟩,
    exact (continuous_within_at_iff_continuous_at_restrict f xs).mp (h x xs) },
  intros h x xs,
  exact (continuous_within_at_iff_continuous_at_restrict f xs).mpr (h ⟨x, xs⟩)
end

theorem continuous_on_iff' {f : α → β} {s : set α} :
  continuous_on f s ↔ ∀ t : set β, is_open t → ∃ u, is_open u ∧ f ⁻¹' t ∩ s = u ∩ s :=
have ∀ t, is_open (s.restrict f ⁻¹' t) ↔ ∃ (u : set α), is_open u ∧ f ⁻¹' t ∩ s = u ∩ s,
  begin
    intro t,
    rw [is_open_induced_iff, set.restrict_eq, set.preimage_comp],
    simp only [subtype.preimage_coe_eq_preimage_coe_iff],
    split; { rintros ⟨u, ou, useq⟩, exact ⟨u, ou, useq.symm⟩ }
  end,
by rw [continuous_on_iff_continuous_restrict, continuous]; simp only [this]

theorem continuous_on_iff_is_closed {f : α → β} {s : set α} :
  continuous_on f s ↔ ∀ t : set β, is_closed t → ∃ u, is_closed u ∧ f ⁻¹' t ∩ s = u ∩ s :=
have ∀ t, is_closed (s.restrict f ⁻¹' t) ↔ ∃ (u : set α), is_closed u ∧ f ⁻¹' t ∩ s = u ∩ s,
  begin
    intro t,
    rw [is_closed_induced_iff, set.restrict_eq, set.preimage_comp],
    simp only [subtype.preimage_coe_eq_preimage_coe_iff]
  end,
by rw [continuous_on_iff_continuous_restrict, continuous_iff_is_closed]; simp only [this]

lemma continuous_on.prod_map {f : α → γ} {g : β → δ} {s : set α} {t : set β}
  (hf : continuous_on f s) (hg : continuous_on g t) :
  continuous_on (prod.map f g) (s.prod t) :=
λ ⟨x, y⟩ ⟨hx, hy⟩, continuous_within_at.prod_map (hf x hx) (hg y hy)

lemma continuous_on_empty (f : α → β) : continuous_on f ∅ :=
λ x, false.elim

theorem nhds_within_le_comap {x : α} {s : set α} {f : α → β} (ctsf : continuous_within_at f s x) :
  nhds_within x s ≤ comap f (nhds_within (f x) (f '' s)) :=
map_le_iff_le_comap.1 ctsf.tendsto_nhds_within_image

theorem continuous_within_at_iff_ptendsto_res (f : α → β) {x : α} {s : set α} :
  continuous_within_at f s x ↔ ptendsto (pfun.res f s) (𝓝 x) (𝓝 (f x)) :=
tendsto_iff_ptendsto _ _ _ _

lemma continuous_iff_continuous_on_univ {f : α → β} : continuous f ↔ continuous_on f univ :=
by simp [continuous_iff_continuous_at, continuous_on, continuous_at, continuous_within_at,
         nhds_within_univ]

lemma continuous_within_at.mono {f : α → β} {s t : set α} {x : α} (h : continuous_within_at f t x)
  (hs : s ⊆ t) : continuous_within_at f s x :=
tendsto_le_left (nhds_within_mono x hs) h

lemma continuous_within_at_inter' {f : α → β} {s t : set α} {x : α} (h : t ∈ nhds_within x s) :
  continuous_within_at f (s ∩ t) x ↔ continuous_within_at f s x :=
by simp [continuous_within_at, nhds_within_restrict'' s h]

lemma continuous_within_at_inter {f : α → β} {s t : set α} {x : α} (h : t ∈ 𝓝 x) :
  continuous_within_at f (s ∩ t) x ↔ continuous_within_at f s x :=
by simp [continuous_within_at, nhds_within_restrict' s h]

lemma continuous_within_at.union {f : α → β} {s t : set α} {x : α}
  (hs : continuous_within_at f s x) (ht : continuous_within_at f t x) :
  continuous_within_at f (s ∪ t) x :=
by simp only [continuous_within_at, nhds_within_union, tendsto, map_sup, sup_le_iff.2 ⟨hs, ht⟩]

lemma continuous_within_at.mem_closure_image  {f : α → β} {s : set α} {x : α}
  (h : continuous_within_at f s x) (hx : x ∈ closure s) : f x ∈ closure (f '' s) :=
mem_closure_of_tendsto (mem_closure_iff_nhds_within_ne_bot.1 hx) h $
mem_sets_of_superset self_mem_nhds_within (subset_preimage_image f s)

lemma continuous_within_at.mem_closure {f : α → β} {s : set α} {x : α} {A : set β}
  (h : continuous_within_at f s x) (hx : x ∈ closure s) (hA : s ⊆ f⁻¹' A) : f x ∈ closure A :=
closure_mono (image_subset_iff.2 hA) (h.mem_closure_image hx)

lemma continuous_within_at.image_closure {f : α → β} {s : set α}
  (hf : ∀ x ∈ closure s, continuous_within_at f s x) :
  f '' (closure s) ⊆ closure (f '' s) :=
begin
  rintros _ ⟨x, hx, rfl⟩,
  exact (hf x hx).mem_closure_image hx
end

theorem is_open_map.continuous_on_image_of_left_inv_on {f : α → β} {s : set α}
  (h : is_open_map (s.restrict f)) {finv : β → α} (hleft : left_inv_on finv f s) :
  continuous_on finv (f '' s) :=
begin
  rintros _ ⟨x, xs, rfl⟩ t ht,
  rw [hleft xs] at ht,
  replace h := h.nhds_le ⟨x, xs⟩,
  apply mem_nhds_within_of_mem_nhds,
  apply h,
  erw [map_compose.symm, function.comp, mem_map, ← nhds_within_eq_map_subtype_coe],
  apply mem_sets_of_superset (inter_mem_nhds_within _ ht),
  assume y hy,
  rw [mem_set_of_eq, mem_preimage, hleft hy.1],
  exact hy.2
end

theorem is_open_map.continuous_on_range_of_left_inverse {f : α → β} (hf : is_open_map f)
  {finv : β → α} (hleft : function.left_inverse finv f) :
  continuous_on finv (range f) :=
begin
  rw [← image_univ],
  exact (hf.restrict is_open_univ).continuous_on_image_of_left_inv_on (λ x _, hleft x)
end

lemma continuous_on.congr_mono {f g : α → β} {s s₁ : set α} (h : continuous_on f s)
  (h' : eq_on g f s₁) (h₁ : s₁ ⊆ s) : continuous_on g s₁ :=
begin
  assume x hx,
  unfold continuous_within_at,
  have A := (h x (h₁ hx)).mono h₁,
  unfold continuous_within_at at A,
  rw ← h' hx at A,
  have : (g =ᶠ[nhds_within x s₁] f) := mem_inf_sets_of_right h',
  exact A.congr' this.symm
end

lemma continuous_on.congr {f g : α → β} {s : set α} (h : continuous_on f s) (h' : eq_on g f s) :
  continuous_on g s :=
h.congr_mono h' (subset.refl _)

lemma continuous_on_congr {f g : α → β} {s : set α} (h' : eq_on g f s) :
  continuous_on g s ↔ continuous_on f s :=
⟨λ h, continuous_on.congr h h'.symm, λ h, h.congr h'⟩

lemma continuous_at.continuous_within_at {f : α → β} {s : set α} {x : α} (h : continuous_at f x) :
  continuous_within_at f s x :=
continuous_within_at.mono ((continuous_within_at_univ f x).2 h) (subset_univ _)

lemma continuous_within_at.continuous_at {f : α → β} {s : set α} {x : α}
  (h : continuous_within_at f s x) (hs : s ∈ 𝓝 x) : continuous_at f x :=
begin
  have : s = univ ∩ s, by rw univ_inter,
  rwa [this, continuous_within_at_inter hs, continuous_within_at_univ] at h
end

lemma continuous_on.continuous_at {f : α → β} {s : set α} {x : α}
  (h : continuous_on f s) (hx : s ∈ 𝓝 x) : continuous_at f x :=
(h x (mem_of_nhds hx)).continuous_at hx

lemma continuous_within_at.comp {g : β → γ} {f : α → β} {s : set α} {t : set β} {x : α}
  (hg : continuous_within_at g t (f x)) (hf : continuous_within_at f s x) (h : s ⊆ f ⁻¹' t) :
  continuous_within_at (g ∘ f) s x :=
begin
  have : tendsto f (𝓟 s) (𝓟 t),
    by { rw tendsto_principal_principal, exact λx hx, h hx },
  have : tendsto f (nhds_within x s) (𝓟 t) :=
    tendsto_le_left inf_le_right this,
  have : tendsto f (nhds_within x s) (nhds_within (f x) t) :=
    tendsto_inf.2 ⟨hf, this⟩,
  exact tendsto.comp hg this
end

lemma continuous_on.comp {g : β → γ} {f : α → β} {s : set α} {t : set β}
  (hg : continuous_on g t) (hf : continuous_on f s) (h : s ⊆ f ⁻¹' t) :
  continuous_on (g ∘ f) s :=
λx hx, continuous_within_at.comp (hg _ (h hx)) (hf x hx) h

lemma continuous_on.mono {f : α → β} {s t : set α} (hf : continuous_on f s) (h : t ⊆ s)  :
  continuous_on f t :=
λx hx, tendsto_le_left (nhds_within_mono _ h) (hf x (h hx))

lemma continuous.continuous_on {f : α → β} {s : set α} (h : continuous f) :
  continuous_on f s :=
begin
  rw continuous_iff_continuous_on_univ at h,
  exact h.mono (subset_univ _)
end

lemma continuous.continuous_within_at {f : α → β} {s : set α} {x : α} (h : continuous f) :
  continuous_within_at f s x :=
tendsto_le_left inf_le_left (h.tendsto x)

lemma continuous.comp_continuous_on {g : β → γ} {f : α → β} {s : set α}
  (hg : continuous g) (hf : continuous_on f s) :
  continuous_on (g ∘ f) s :=
hg.continuous_on.comp hf subset_preimage_univ

lemma continuous_within_at.preimage_mem_nhds_within {f : α → β} {x : α} {s : set α} {t : set β}
  (h : continuous_within_at f s x) (ht : t ∈ 𝓝 (f x)) : f ⁻¹' t ∈ nhds_within x s :=
h ht

lemma continuous_within_at.preimage_mem_nhds_within' {f : α → β} {x : α} {s : set α} {t : set β}
  (h : continuous_within_at f s x) (ht : t ∈ nhds_within (f x) (f '' s)) :
  f ⁻¹' t ∈ nhds_within x s :=
begin
  rw mem_nhds_within at ht,
  rcases ht with ⟨u, u_open, fxu, hu⟩,
  have : f ⁻¹' u ∩ s ∈ nhds_within x s :=
    filter.inter_mem_sets (h (mem_nhds_sets u_open fxu)) self_mem_nhds_within,
  apply mem_sets_of_superset this,
  calc f ⁻¹' u ∩ s
    ⊆ f ⁻¹' u ∩ f ⁻¹' (f '' s) : inter_subset_inter_right _ (subset_preimage_image f s)
    ... = f ⁻¹' (u ∩ f '' s) : rfl
    ... ⊆ f ⁻¹' t : preimage_mono hu
end

lemma continuous_within_at.congr_of_mem_nhds_within {f f₁ : α → β} {s : set α} {x : α}
  (h : continuous_within_at f s x) (h₁ : f₁ =ᶠ[nhds_within x s] f) (hx : f₁ x = f x) :
  continuous_within_at f₁ s x :=
by rwa [continuous_within_at, filter.tendsto, hx, filter.map_congr h₁]

lemma continuous_within_at.congr {f f₁ : α → β} {s : set α} {x : α}
  (h : continuous_within_at f s x) (h₁ : ∀y∈s, f₁ y = f y) (hx : f₁ x = f x) :
  continuous_within_at f₁ s x :=
h.congr_of_mem_nhds_within (mem_sets_of_superset self_mem_nhds_within h₁) hx

lemma continuous_on_const {s : set α} {c : β} : continuous_on (λx, c) s :=
continuous_const.continuous_on

lemma continuous_within_at_const {b : β} {s : set α} {x : α} :
  continuous_within_at (λ _:α, b) s x :=
continuous_const.continuous_within_at

lemma continuous_on_id {s : set α} : continuous_on id s :=
continuous_id.continuous_on

lemma continuous_within_at_id {s : set α} {x : α} : continuous_within_at id s x :=
continuous_id.continuous_within_at

lemma continuous_on_open_iff {f : α → β} {s : set α} (hs : is_open s) :
  continuous_on f s ↔ (∀t, is_open t → is_open (s ∩ f⁻¹' t)) :=
begin
  rw continuous_on_iff',
  split,
  { assume h t ht,
    rcases h t ht with ⟨u, u_open, hu⟩,
    rw [inter_comm, hu],
    apply is_open_inter u_open hs },
  { assume h t ht,
    refine ⟨s ∩ f ⁻¹' t, h t ht, _⟩,
    rw [@inter_comm _ s (f ⁻¹' t), inter_assoc, inter_self] }
end

lemma continuous_on.preimage_open_of_open {f : α → β} {s : set α} {t : set β}
  (hf : continuous_on f s) (hs : is_open s) (ht : is_open t) : is_open (s ∩ f⁻¹' t) :=
(continuous_on_open_iff hs).1 hf t ht

lemma continuous_on.preimage_closed_of_closed {f : α → β} {s : set α} {t : set β}
  (hf : continuous_on f s) (hs : is_closed s) (ht : is_closed t) : is_closed (s ∩ f⁻¹' t) :=
begin
  rcases continuous_on_iff_is_closed.1 hf t ht with ⟨u, hu⟩,
  rw [inter_comm, hu.2],
  apply is_closed_inter hu.1 hs
end

lemma continuous_on.preimage_interior_subset_interior_preimage {f : α → β} {s : set α} {t : set β}
  (hf : continuous_on f s) (hs : is_open s) : s ∩ f⁻¹' (interior t) ⊆ s ∩ interior (f⁻¹' t) :=
calc s ∩ f ⁻¹' (interior t) ⊆ interior (s ∩ f ⁻¹' t) :
  interior_maximal (inter_subset_inter (subset.refl _) (preimage_mono interior_subset))
    (hf.preimage_open_of_open hs is_open_interior)
... = s ∩ interior (f ⁻¹' t) : by rw [interior_inter, interior_eq_of_open hs]

lemma continuous_on_of_locally_continuous_on {f : α → β} {s : set α}
  (h : ∀x∈s, ∃t, is_open t ∧ x ∈ t ∧ continuous_on f (s ∩ t)) : continuous_on f s :=
begin
  assume x xs,
  rcases h x xs with ⟨t, open_t, xt, ct⟩,
  have := ct x ⟨xs, xt⟩,
  rwa [continuous_within_at, ← nhds_within_restrict _ xt open_t] at this
end

lemma continuous_on_open_of_generate_from {β : Type*} {s : set α} {T : set (set β)} {f : α → β}
  (hs : is_open s) (h : ∀t ∈ T, is_open (s ∩ f⁻¹' t)) :
  @continuous_on α β _ (topological_space.generate_from T) f s :=
begin
  rw continuous_on_open_iff,
  assume t ht,
  induction ht with u hu u v Tu Tv hu hv U hU hU',
  { exact h u hu },
  { simp only [preimage_univ, inter_univ], exact hs },
  { have : s ∩ f ⁻¹' (u ∩ v) = (s ∩ f ⁻¹' u) ∩ (s ∩ f ⁻¹' v),
      by { ext x, simp, split, finish, finish },
    rw this,
    exact is_open_inter hu hv },
  { rw [preimage_sUnion, inter_bUnion],
    exact is_open_bUnion hU' },
  { exact hs }
end

lemma continuous_within_at.prod {f : α → β} {g : α → γ} {s : set α} {x : α}
  (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) :
  continuous_within_at (λx, (f x, g x)) s x :=
hf.prod_mk_nhds hg

lemma continuous_on.prod {f : α → β} {g : α → γ} {s : set α}
  (hf : continuous_on f s) (hg : continuous_on g s) : continuous_on (λx, (f x, g x)) s :=
λx hx, continuous_within_at.prod (hf x hx) (hg x hx)
