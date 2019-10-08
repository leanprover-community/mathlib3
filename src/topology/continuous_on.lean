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

variables {α : Type*} {β : Type*} {γ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]

/-- The "neighborhood within" filter. Elements of `nhds_within a s` are sets containing the
intersection of `s` and a neighborhood of `a`. -/
def nhds_within (a : α) (s : set α) : filter α := nhds a ⊓ principal s

theorem nhds_within_eq (a : α) (s : set α) :
  nhds_within a s = ⨅ t ∈ {t : set α | a ∈ t ∧ is_open t}, principal (t ∩ s) :=
have set.univ ∈ {s : set α | a ∈ s ∧ is_open s}, from ⟨set.mem_univ _, is_open_univ⟩,
begin
  rw [nhds_within, nhds, lattice.binfi_inf]; try { exact this },
  simp only [inf_principal]
end

theorem nhds_within_univ (a : α) : nhds_within a set.univ = nhds a :=
by rw [nhds_within, principal_univ, lattice.inf_top_eq]

theorem mem_nhds_within (t : set α) (a : α) (s : set α) :
  t ∈ nhds_within a s ↔ ∃ u, is_open u ∧ a ∈ u ∧ u ∩ s ⊆ t  :=
begin
  rw [nhds_within, mem_inf_principal, mem_nhds_sets_iff], split,
  { rintros ⟨u, hu, openu, au⟩,
    exact ⟨u, openu, au, λ x ⟨xu, xs⟩, hu xu xs⟩ },
  rintros ⟨u, openu, au, hu⟩,
  exact ⟨u, λ x xu xs, hu ⟨xu, xs⟩, openu, au⟩
end

theorem self_mem_nhds_within {a : α} {s : set α} : s ∈ nhds_within a s :=
begin
  rw [nhds_within, mem_inf_principal],
  simp only [imp_self],
  exact univ_mem_sets
end

theorem inter_mem_nhds_within (s : set α) {t : set α} {a : α} (h : t ∈ nhds a) :
  s ∩ t ∈ nhds_within a s :=
inter_mem_sets (mem_inf_sets_of_right (mem_principal_self s)) (mem_inf_sets_of_left h)

theorem nhds_within_mono (a : α) {s t : set α} (h : s ⊆ t) : nhds_within a s ≤ nhds_within a t :=
lattice.inf_le_inf (le_refl _) (principal_mono.mpr h)

theorem nhds_within_restrict'' {a : α} (s : set α) {t : set α} (h : t ∈ nhds_within a s) :
  nhds_within a s = nhds_within a (s ∩ t) :=
le_antisymm
  (lattice.le_inf lattice.inf_le_left (le_principal_iff.mpr (inter_mem_sets self_mem_nhds_within h)))
  (lattice.inf_le_inf (le_refl _) (principal_mono.mpr (set.inter_subset_left _ _)))

theorem nhds_within_restrict' {a : α} (s : set α) {t : set α} (h : t ∈ nhds a) :
  nhds_within a s = nhds_within a (s ∩ t) :=
nhds_within_restrict'' s $ mem_inf_sets_of_left h

theorem nhds_within_restrict {a : α} (s : set α) {t : set α} (h₀ : a ∈ t) (h₁ : is_open t) :
  nhds_within a s = nhds_within a (s ∩ t) :=
nhds_within_restrict' s (mem_nhds_sets h₁ h₀)

theorem nhds_within_le_of_mem {a : α} {s t : set α} (h : s ∈ nhds_within a t) :
  nhds_within a t ≤ nhds_within a s :=
begin
  rcases (mem_nhds_within _ _ _).1 h with ⟨u, u_open, au, uts⟩,
  have : nhds_within a t = nhds_within a (t ∩ u) := nhds_within_restrict _ au u_open,
  rw [this, inter_comm],
  exact nhds_within_mono _ uts
end

theorem nhds_within_eq_nhds_within {a : α} {s t u : set α}
    (h₀ : a ∈ s) (h₁ : is_open s) (h₂ : t ∩ s = u ∩ s) :
  nhds_within a t = nhds_within a u :=
by rw [nhds_within_restrict t h₀ h₁, nhds_within_restrict u h₀ h₁, h₂]

theorem nhds_within_eq_of_open {a : α} {s : set α} (h₀ : a ∈ s) (h₁ : is_open s) :
  nhds_within a s = nhds a :=
by rw [←nhds_within_univ]; apply nhds_within_eq_nhds_within h₀ h₁;
     rw [set.univ_inter, set.inter_self]

@[simp] theorem nhds_within_empty (a : α) : nhds_within a {} = ⊥ :=
by rw [nhds_within, principal_empty, lattice.inf_bot_eq]

theorem nhds_within_union (a : α) (s t : set α) :
  nhds_within a (s ∪ t) = nhds_within a s ⊔ nhds_within a t :=
by unfold nhds_within; rw [←lattice.inf_sup_left, sup_principal]

theorem nhds_within_inter (a : α) (s t : set α) :
  nhds_within a (s ∩ t) = nhds_within a s ⊓ nhds_within a t :=
by unfold nhds_within; rw [lattice.inf_left_comm, lattice.inf_assoc, inf_principal,
                             ←lattice.inf_assoc, lattice.inf_idem]

theorem nhds_within_inter' (a : α) (s t : set α) :
  nhds_within a (s ∩ t) = (nhds_within a s) ⊓ principal t :=
by { unfold nhds_within, rw [←inf_principal, lattice.inf_assoc] }

theorem tendsto_if_nhds_within {f g : α → β} {p : α → Prop} [decidable_pred p]
    {a : α} {s : set α} {l : filter β}
    (h₀ : tendsto f (nhds_within a (s ∩ p)) l)
    (h₁ : tendsto g (nhds_within a (s ∩ {x | ¬ p x})) l) :
  tendsto (λ x, if p x then f x else g x) (nhds_within a s) l :=
by apply tendsto_if; rw [←nhds_within_inter']; assumption

lemma map_nhds_within (f : α → β) (a : α) (s : set α) :
  map f (nhds_within a s) =
    ⨅ t ∈ {t : set α | a ∈ t ∧ is_open t}, principal (set.image f (t ∩ s)) :=
have h₀ : directed_on ((λ (i : set α), principal (i ∩ s)) ⁻¹'o ge)
        {x : set α | x ∈ {t : set α | a ∈ t ∧ is_open t}}, from
  assume x ⟨ax, openx⟩ y ⟨ay, openy⟩,
  ⟨x ∩ y, ⟨⟨ax, ay⟩, is_open_inter openx openy⟩,
    le_principal_iff.mpr (set.inter_subset_inter_left _ (set.inter_subset_left _ _)),
    le_principal_iff.mpr (set.inter_subset_inter_left _ (set.inter_subset_right _ _))⟩,
have h₁ : ∃ (i : set α), i ∈ {t : set α | a ∈ t ∧ is_open t},
  from ⟨set.univ, set.mem_univ _, is_open_univ⟩,
by { rw [nhds_within_eq, map_binfi_eq h₀ h₁], simp only [map_principal] }

theorem tendsto_nhds_within_mono_left {f : α → β} {a : α}
    {s t : set α} {l : filter β} (hst : s ⊆ t) (h : tendsto f (nhds_within a t) l) :
  tendsto f (nhds_within a s) l :=
tendsto_le_left (nhds_within_mono a hst) h

theorem tendsto_nhds_within_mono_right {f : β → α} {l : filter β}
    {a : α} {s t : set α} (hst : s ⊆ t) (h : tendsto f l (nhds_within a s)) :
  tendsto f l (nhds_within a t) :=
tendsto_le_right (nhds_within_mono a hst) h

theorem tendsto_nhds_within_of_tendsto_nhds {f : α → β} {a : α}
    {s : set α} {l : filter β} (h : tendsto f (nhds a) l) :
  tendsto f (nhds_within a s) l :=
by rw [←nhds_within_univ] at h; exact tendsto_nhds_within_mono_left (set.subset_univ _) h

theorem principal_subtype {α : Type*} (s : set α) (t : set {x // x ∈ s}) :
  principal t = comap subtype.val (principal (subtype.val '' t)) :=
by rw comap_principal; rw set.preimage_image_eq; apply subtype.val_injective

/-
nhds_within and subtypes
-/

theorem mem_nhds_within_subtype (s : set α) (a : {x // x ∈ s}) (t u : set {x // x ∈ s}) :
  t ∈ nhds_within a u ↔
    t ∈ comap (@subtype.val _ s) (nhds_within a.val (subtype.val '' u)) :=
by rw [nhds_within, nhds_subtype, principal_subtype, ←comap_inf, ←nhds_within]

theorem nhds_within_subtype (s : set α) (a : {x // x ∈ s}) (t : set {x // x ∈ s}) :
  nhds_within a t = comap (@subtype.val _ s) (nhds_within a.val (subtype.val '' t)) :=
filter_eq $ by ext u; rw mem_nhds_within_subtype

theorem nhds_within_eq_map_subtype_val {s : set α} {a : α} (h : a ∈ s) :
  nhds_within a s = map subtype.val (nhds ⟨a, h⟩) :=
have h₀ : s ∈ nhds_within a s,
  by { rw [mem_nhds_within], existsi set.univ, simp [set.diff_eq] },
have h₁ : ∀ y ∈ s, ∃ x, @subtype.val _ s x = y,
  from λ y h, ⟨⟨y, h⟩, rfl⟩,
begin
  rw [←nhds_within_univ, nhds_within_subtype, subtype.val_image_univ],
  exact (map_comap_of_surjective' h₀ h₁).symm,
end

theorem tendsto_nhds_within_iff_subtype {s : set α} {a : α} (h : a ∈ s) (f : α → β) (l : filter β) :
  tendsto f (nhds_within a s) l ↔ tendsto (function.restrict f s) (nhds ⟨a, h⟩) l :=
by rw [tendsto, tendsto, function.restrict, nhds_within_eq_map_subtype_val h,
    ←(@filter.map_map _ _ _ _ subtype.val)]

/-- A function between topological spaces is continuous at a point `x₀` within a subset `s`
if `f x` tends to `f x₀` when `x` tends to `x₀` while staying within `s`. -/
def continuous_within_at (f : α → β) (s : set α) (x : α) : Prop :=
tendsto f (nhds_within x s) (nhds (f x))

/-- A function between topological spaces is continuous on a subset `s`
when it's continuous at every point of `s` within `s`. -/
def continuous_on (f : α → β) (s : set α) : Prop := ∀ x ∈ s, continuous_within_at f s x

theorem continuous_within_at_univ (f : α → β) (x : α) :
  continuous_within_at f set.univ x ↔ continuous_at f x :=
by rw [continuous_at, continuous_within_at, nhds_within_univ]

theorem continuous_within_at_iff_continuous_at_restrict (f : α → β) {x : α} {s : set α} (h : x ∈ s) :
  continuous_within_at f s x ↔ continuous_at (function.restrict f s) ⟨x, h⟩ :=
tendsto_nhds_within_iff_subtype h f _

theorem continuous_within_at.tendsto_nhds_within_image {f : α → β} {x : α} {s : set α}
  (h : continuous_within_at f s x) :
  tendsto f (nhds_within x s) (nhds_within (f x) (f '' s)) :=
tendsto_inf.2 ⟨h, tendsto_principal.2 $
  mem_inf_sets_of_right $ mem_principal_sets.2 $
  λ x, mem_image_of_mem _⟩

theorem continuous_on_iff {f : α → β} {s : set α} :
  continuous_on f s ↔ ∀ x ∈ s, ∀ t : set β, is_open t → f x ∈ t → ∃ u, is_open u ∧ x ∈ u ∧
    u ∩ s ⊆ f ⁻¹' t :=
by simp only [continuous_on, continuous_within_at, tendsto_nhds, mem_nhds_within]

theorem continuous_on_iff_continuous_restrict {f : α → β} {s : set α} :
  continuous_on f s ↔ continuous (function.restrict f s) :=
begin
  rw [continuous_on, continuous_iff_continuous_at], split,
  { rintros h ⟨x, xs⟩,
    exact (continuous_within_at_iff_continuous_at_restrict f xs).mp (h x xs) },
  intros h x xs,
  exact (continuous_within_at_iff_continuous_at_restrict f xs).mpr (h ⟨x, xs⟩)
end

theorem continuous_on_iff' {f : α → β} {s : set α} :
  continuous_on f s ↔ ∀ t : set β, is_open t → ∃ u, is_open u ∧ f ⁻¹' t ∩ s = u ∩ s :=
have ∀ t, is_open (function.restrict f s ⁻¹' t) ↔ ∃ (u : set α), is_open u ∧ f ⁻¹' t ∩ s = u ∩ s,
  begin
    intro t,
    rw [is_open_induced_iff, function.restrict_eq, set.preimage_comp],
    simp only [subtype.preimage_val_eq_preimage_val_iff],
    split; { rintros ⟨u, ou, useq⟩, exact ⟨u, ou, useq.symm⟩ }
  end,
by rw [continuous_on_iff_continuous_restrict, continuous]; simp only [this]

theorem continuous_on_iff_is_closed  {f : α → β} {s : set α} :
  continuous_on f s ↔ ∀ t : set β, is_closed t → ∃ u, is_closed u ∧ f ⁻¹' t ∩ s = u ∩ s :=
have ∀ t, is_closed (function.restrict f s ⁻¹' t) ↔ ∃ (u : set α), is_closed u ∧ f ⁻¹' t ∩ s = u ∩ s,
  begin
    intro t,
    rw [is_closed_induced_iff, function.restrict_eq, set.preimage_comp],
    simp only [subtype.preimage_val_eq_preimage_val_iff]
  end,
by rw [continuous_on_iff_continuous_restrict, continuous_iff_is_closed]; simp only [this]

theorem nhds_within_le_comap {x : α} {s : set α} {f : α → β} (ctsf : continuous_within_at f s x) :
  nhds_within x s ≤ comap f (nhds_within (f x) (f '' s)) :=
map_le_iff_le_comap.1 ctsf.tendsto_nhds_within_image

theorem continuous_within_at_iff_ptendsto_res (f : α → β) {x : α} {s : set α} :
  continuous_within_at f s x ↔ ptendsto (pfun.res f s) (nhds x) (nhds (f x)) :=
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

lemma continuous_within_at_inter {f : α → β} {s t : set α} {x : α} (h : t ∈ nhds x) :
  continuous_within_at f (s ∩ t) x ↔ continuous_within_at f s x :=
by simp [continuous_within_at, nhds_within_restrict' s h]

lemma continuous_on.congr_mono {f g : α → β} {s s₁ : set α} (h : continuous_on f s)
  (h' : ∀x ∈ s₁, g x = f x) (h₁ : s₁ ⊆ s) : continuous_on g s₁ :=
begin
  assume x hx,
  unfold continuous_within_at,
  have A := (h x (h₁ hx)).mono h₁,
  unfold continuous_within_at at A,
  rw ← h' x hx at A,
  have : {x : α | g x = f x} ∈ nhds_within x s₁ := mem_inf_sets_of_right h',
  apply tendsto.congr' _ A,
  convert this,
  ext,
  finish
end

lemma continuous_at.continuous_within_at {f : α → β} {s : set α} {x : α} (h : continuous_at f x) :
  continuous_within_at f s x :=
continuous_within_at.mono ((continuous_within_at_univ f x).2 h) (subset_univ _)

lemma continuous_within_at.continuous_at {f : α → β} {s : set α} {x : α}
  (h : continuous_within_at f s x) (hs : s ∈ nhds x) : continuous_at f x :=
begin
  have : s = univ ∩ s, by rw univ_inter,
  rwa [this, continuous_within_at_inter hs, continuous_within_at_univ] at h
end

lemma continuous_within_at.comp {g : β → γ} {f : α → β} {s : set α} {t : set β} {x : α}
  (hg : continuous_within_at g t (f x)) (hf : continuous_within_at f s x) (h : f '' s ⊆ t) :
  continuous_within_at (g ∘ f) s x :=
begin
  have : tendsto f (principal s) (principal t),
    by { rw tendsto_principal_principal, exact λx hx, h (mem_image_of_mem _ hx) },
  have : tendsto f (nhds_within x s) (principal t) :=
    tendsto_le_left lattice.inf_le_right this,
  have : tendsto f (nhds_within x s) (nhds_within (f x) t) :=
    tendsto_inf.2 ⟨hf, this⟩,
  exact tendsto.comp hg this
end

lemma continuous_on.comp {g : β → γ} {f : α → β} {s : set α} {t : set β}
  (hg : continuous_on g t) (hf : continuous_on f s) (h : f '' s ⊆ t) :
  continuous_on (g ∘ f) s :=
λx hx, continuous_within_at.comp (hg _ (h (mem_image_of_mem _ hx))) (hf x hx) h

lemma continuous_on.mono {f : α → β} {s t : set α} (hf : continuous_on f s) (h : t ⊆ s)  :
  continuous_on f t :=
λx hx, tendsto_le_left (nhds_within_mono _ h) (hf x (h hx))

lemma continuous.continuous_on {f : α → β} {s : set α} (h : continuous f) :
  continuous_on f s :=
begin
  rw continuous_iff_continuous_on_univ at h,
  exact h.mono (subset_univ _)
end

lemma continuous.comp_continuous_on {g : β → γ} {f : α → β} {s : set α}
  (hg : continuous g) (hf : continuous_on f s) :
  continuous_on (g ∘ f) s :=
hg.continuous_on.comp hf (subset_univ _)

lemma continuous_within_at.preimage_mem_nhds_within {f : α → β} {x : α} {s : set α} {t : set β}
  (h : continuous_within_at f s x) (ht : t ∈ nhds (f x)) : f ⁻¹' t ∈ nhds_within x s :=
h ht

lemma continuous_within_at.congr_of_mem_nhds_within {f f₁ : α → β} {s : set α} {x : α}
  (h : continuous_within_at f s x) (h₁ : {y | f₁ y = f y} ∈ nhds_within x s) (hx : f₁ x = f x) :
  continuous_within_at f₁ s x :=
by rwa [continuous_within_at, filter.tendsto, hx, filter.map_cong h₁]

lemma continuous_on_const {s : set α} {c : β} : continuous_on (λx, c) s :=
continuous_const.continuous_on

lemma continuous_on_open_iff {f : α → β} {s : set α} (hs : is_open s) :
  continuous_on f s ↔ (∀t, _root_.is_open t → is_open (s ∩ f⁻¹' t)) :=
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
calc s ∩ f ⁻¹' (interior t)
     = interior (s ∩ f ⁻¹' (interior t)) :
       (interior_eq_of_open (hf.preimage_open_of_open hs is_open_interior)).symm
    ... ⊆ interior (s ∩ f ⁻¹' t) :
        interior_mono (inter_subset_inter (subset.refl _) (preimage_mono interior_subset))
    ... = s ∩ interior (f ⁻¹' t) :
      by rw [interior_inter, interior_eq_of_open hs]

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
tendsto_prod_mk_nhds hf hg

lemma continuous_on.prod {f : α → β} {g : α → γ} {s : set α}
  (hf : continuous_on f s) (hg : continuous_on g s) : continuous_on (λx, (f x, g x)) s :=
λx hx, continuous_within_at.prod (hf x hx) (hg x hx)
