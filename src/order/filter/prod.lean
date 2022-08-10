/-
Copyright (c) 2022 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johanes Hölzl, Patrick Massot, Yury Kudryashov, Kevin Wilson, Heather Macbeth
-/
import order.filter.basic

/-!
# Product and coproduct filters

In this file we define `filter.prod f g` (notation: `f ×ᶠ g`) and `filter.coprod f g`. The product
of two filters is the largest filter `l` such that `filter.tendsto prod.fst l f` and
`filter.tendsto prod.snd l g`.

## Implementation details

The product filter cannot be defined using the monad structure on filters. For example:

```lean
F := do {x ← seq, y ← top, return (x, y)}
G := do {y ← top, x ← seq, return (x, y)}
```
hence:
```lean
s ∈ F  ↔  ∃ n, [n..∞] × univ ⊆ s
s ∈ G  ↔  ∀ i:ℕ, ∃ n, [n..∞] × {i} ⊆ s
```
Now `⋃ i, [i..∞] × {i}` is in `G` but not in `F`.
As product filter we want to have `F` as result.

## Notations

* `f ×ᶠ g` : `filter.prod f g`, localized in `filter`.

-/

open set
open_locale filter

namespace filter

variables {α β γ δ : Type*} {ι : Sort*}

section prod
variables {s : set α} {t : set β} {f : filter α} {g : filter β}

/-- Product of filters. This is the filter generated by cartesian products
of elements of the component filters. -/
protected def prod (f : filter α) (g : filter β) : filter (α × β) :=
f.comap prod.fst ⊓ g.comap prod.snd

localized "infix ` ×ᶠ `:60 := filter.prod" in filter

lemma prod_mem_prod {s : set α} {t : set β} {f : filter α} {g : filter β}
  (hs : s ∈ f) (ht : t ∈ g) : s ×ˢ t ∈ f ×ᶠ g :=
inter_mem_inf (preimage_mem_comap hs) (preimage_mem_comap ht)

lemma mem_prod_iff {s : set (α×β)} {f : filter α} {g : filter β} :
  s ∈ f ×ᶠ g ↔ (∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ×ˢ t₂ ⊆ s) :=
begin
  simp only [filter.prod],
  split,
  { rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩,
    exact  ⟨s₁, hs₁, s₂, hs₂, λ p ⟨h, h'⟩, ⟨hts₁ h, hts₂ h'⟩⟩ },
  { rintro ⟨t₁, ht₁, t₂, ht₂, h⟩,
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h }
end

@[simp] lemma prod_mem_prod_iff {s : set α} {t : set β} {f : filter α} {g : filter β}
  [f.ne_bot] [g.ne_bot] :
  s ×ˢ t ∈ f ×ᶠ g ↔ s ∈ f ∧ t ∈ g :=
⟨λ h, let ⟨s', hs', t', ht', H⟩ := mem_prod_iff.1 h in (prod_subset_prod_iff.1 H).elim
  (λ ⟨hs's, ht't⟩, ⟨mem_of_superset hs' hs's, mem_of_superset ht' ht't⟩)
  (λ h, h.elim
    (λ hs'e, absurd hs'e (nonempty_of_mem hs').ne_empty)
    (λ ht'e, absurd ht'e (nonempty_of_mem ht').ne_empty)),
  λ h, prod_mem_prod h.1 h.2⟩

lemma mem_prod_principal {f : filter α} {s : set (α × β)} {t : set β}:
  s ∈ f ×ᶠ 𝓟 t ↔ {a | ∀ b ∈ t, (a, b) ∈ s} ∈ f :=
begin
  rw [← @exists_mem_subset_iff _ f, mem_prod_iff],
  refine exists₂_congr (λ u u_in, ⟨_, λ h, ⟨t, mem_principal_self t, _⟩⟩),
  { rintros ⟨v, v_in, hv⟩ a a_in b b_in,
    exact hv (mk_mem_prod a_in $ v_in b_in) },
  { rintro ⟨x, y⟩ ⟨hx, hy⟩,
    exact h hx y hy }
end

lemma mem_prod_top {f : filter α} {s : set (α × β)} :
  s ∈ f ×ᶠ (⊤ : filter β) ↔ {a | ∀ b, (a, b) ∈ s} ∈ f :=
begin
  rw [← principal_univ, mem_prod_principal],
  simp only [mem_univ, forall_true_left]
end

lemma comap_prod (f : α → β × γ) (b : filter β) (c : filter γ) :
  comap f (b ×ᶠ c) = (comap (prod.fst ∘ f) b) ⊓ (comap (prod.snd ∘ f) c) :=
by erw [comap_inf, filter.comap_comap, filter.comap_comap]

lemma prod_top {f : filter α} : f ×ᶠ (⊤ : filter β) = f.comap prod.fst :=
by rw [filter.prod, comap_top, inf_top_eq]

lemma sup_prod (f₁ f₂ : filter α) (g : filter β) : (f₁ ⊔ f₂) ×ᶠ g = (f₁ ×ᶠ g) ⊔ (f₂ ×ᶠ g) :=
by rw [filter.prod, comap_sup, inf_sup_right, ← filter.prod, ← filter.prod]

lemma prod_sup (f : filter α) (g₁ g₂ : filter β) : f ×ᶠ (g₁ ⊔ g₂) = (f ×ᶠ g₁) ⊔ (f ×ᶠ g₂) :=
by rw [filter.prod, comap_sup, inf_sup_left, ← filter.prod, ← filter.prod]

lemma eventually_prod_iff {p : α × β → Prop} {f : filter α} {g : filter β} :
  (∀ᶠ x in f ×ᶠ g, p x) ↔ ∃ (pa : α → Prop) (ha : ∀ᶠ x in f, pa x)
    (pb : β → Prop) (hb : ∀ᶠ y in g, pb y), ∀ {x}, pa x → ∀ {y}, pb y → p (x, y) :=
by simpa only [set.prod_subset_iff] using @mem_prod_iff α β p f g

lemma tendsto_fst {f : filter α} {g : filter β} : tendsto prod.fst (f ×ᶠ g) f :=
tendsto_inf_left tendsto_comap

lemma tendsto_snd {f : filter α} {g : filter β} : tendsto prod.snd (f ×ᶠ g) g :=
tendsto_inf_right tendsto_comap

lemma tendsto.prod_mk {f : filter α} {g : filter β} {h : filter γ} {m₁ : α → β} {m₂ : α → γ}
  (h₁ : tendsto m₁ f g) (h₂ : tendsto m₂ f h) : tendsto (λ x, (m₁ x, m₂ x)) f (g ×ᶠ h) :=
tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

lemma tendsto_prod_swap {α1 α2 : Type*} {a1 : filter α1} {a2 : filter α2} :
  tendsto (prod.swap : α1 × α2 → α2 × α1) (a1 ×ᶠ a2) (a2 ×ᶠ a1) :=
tendsto_snd.prod_mk tendsto_fst

lemma eventually.prod_inl {la : filter α} {p : α → Prop} (h : ∀ᶠ x in la, p x) (lb : filter β) :
  ∀ᶠ x in la ×ᶠ lb, p (x : α × β).1 :=
tendsto_fst.eventually h

lemma eventually.prod_inr {lb : filter β} {p : β → Prop} (h : ∀ᶠ x in lb, p x) (la : filter α) :
  ∀ᶠ x in la ×ᶠ lb, p (x : α × β).2 :=
tendsto_snd.eventually h

lemma eventually.prod_mk {la : filter α} {pa : α → Prop} (ha : ∀ᶠ x in la, pa x)
  {lb : filter β} {pb : β → Prop} (hb : ∀ᶠ y in lb, pb y) :
  ∀ᶠ p in la ×ᶠ lb, pa (p : α × β).1 ∧ pb p.2 :=
(ha.prod_inl lb).and (hb.prod_inr la)

lemma eventually_eq.prod_map {δ} {la : filter α} {fa ga : α → γ} (ha : fa =ᶠ[la] ga)
  {lb : filter β} {fb gb : β → δ} (hb : fb =ᶠ[lb] gb) :
  prod.map fa fb =ᶠ[la ×ᶠ lb] prod.map ga gb :=
(eventually.prod_mk ha hb).mono $ λ x h, prod.ext h.1 h.2

lemma eventually_le.prod_map {δ} [has_le γ] [has_le δ] {la : filter α} {fa ga : α → γ}
  (ha : fa ≤ᶠ[la] ga) {lb : filter β} {fb gb : β → δ} (hb : fb ≤ᶠ[lb] gb) :
  prod.map fa fb ≤ᶠ[la ×ᶠ lb] prod.map ga gb :=
eventually.prod_mk ha hb

lemma eventually.curry {la : filter α} {lb : filter β} {p : α × β → Prop}
  (h : ∀ᶠ x in la ×ᶠ lb, p x) :
  ∀ᶠ x in la, ∀ᶠ y in lb, p (x, y) :=
begin
  rcases eventually_prod_iff.1 h with ⟨pa, ha, pb, hb, h⟩,
  exact ha.mono (λ a ha, hb.mono $ λ b hb, h ha hb)
end

/-- A fact that is eventually true about all pairs `l ×ᶠ l` is eventually true about
all diagonal pairs `(i, i)` -/
lemma eventually.diag_of_prod {f : filter α} {p : α × α → Prop}
  (h : ∀ᶠ i in f ×ᶠ f, p i) : (∀ᶠ i in f, p (i, i)) :=
begin
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h,
  apply (ht.and hs).mono (λ x hx, hst hx.1 hx.2),
end

lemma tendsto_diag : tendsto (λ i, (i, i)) f (f ×ᶠ f) :=
tendsto_iff_eventually.mpr (λ _ hpr, hpr.diag_of_prod)

lemma prod_infi_left [nonempty ι] {f : ι → filter α} {g : filter β}:
  (⨅ i, f i) ×ᶠ g = (⨅ i, (f i) ×ᶠ g) :=
by { rw [filter.prod, comap_infi, infi_inf], simp only [filter.prod, eq_self_iff_true] }

lemma prod_infi_right [nonempty ι] {f : filter α} {g : ι → filter β} :
  f ×ᶠ (⨅ i, g i) = (⨅ i, f ×ᶠ (g i)) :=
by { rw [filter.prod, comap_infi, inf_infi], simp only [filter.prod, eq_self_iff_true] }

@[mono] lemma prod_mono {f₁ f₂ : filter α} {g₁ g₂ : filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  f₁ ×ᶠ g₁ ≤ f₂ ×ᶠ g₂ :=
inf_le_inf (comap_mono hf) (comap_mono hg)

lemma {u v w x} prod_comap_comap_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} :
  (comap m₁ f₁) ×ᶠ (comap m₂ f₂) = comap (λ p : β₁×β₂, (m₁ p.1, m₂ p.2)) (f₁ ×ᶠ f₂) :=
by simp only [filter.prod, comap_comap, eq_self_iff_true, comap_inf]

lemma prod_comm' : f ×ᶠ g = comap (prod.swap) (g ×ᶠ f) :=
by simp only [filter.prod, comap_comap, (∘), inf_comm, prod.fst_swap,
  eq_self_iff_true, prod.snd_swap, comap_inf]

lemma prod_comm : f ×ᶠ g = map (λ p : β×α, (p.2, p.1)) (g ×ᶠ f) :=
by { rw [prod_comm', ← map_swap_eq_comap_swap], refl }

lemma prod_assoc (f : filter α) (g : filter β) (h : filter γ) :
  map (equiv.prod_assoc α β γ) ((f ×ᶠ g) ×ᶠ h) = f ×ᶠ (g ×ᶠ h) :=
by simp_rw [← comap_equiv_symm, filter.prod, comap_inf, comap_comap, inf_assoc, function.comp,
  equiv.prod_assoc_symm_apply]

theorem prod_assoc_symm (f : filter α) (g : filter β) (h : filter γ) :
map (equiv.prod_assoc α β γ).symm (f ×ᶠ (g ×ᶠ h)) = (f ×ᶠ g) ×ᶠ h :=
by simp_rw [map_equiv_symm, filter.prod, comap_inf, comap_comap, inf_assoc, function.comp,
  equiv.prod_assoc_apply]

lemma tendsto_prod_assoc {f : filter α} {g : filter β} {h : filter γ} :
  tendsto (equiv.prod_assoc α β γ) (f ×ᶠ g ×ᶠ h) (f ×ᶠ (g ×ᶠ h)) :=
(prod_assoc f g h).le

lemma tendsto_prod_assoc_symm {f : filter α} {g : filter β} {h : filter γ} :
  tendsto (equiv.prod_assoc α β γ).symm (f ×ᶠ (g ×ᶠ h)) (f ×ᶠ g ×ᶠ h) :=
(prod_assoc_symm f g h).le

/-- A useful lemma when dealing with uniformities. -/
lemma map_swap4_prod {f : filter α} {g : filter β} {h : filter γ} {k : filter δ} :
  map (λ p : (α × β) × (γ × δ), ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f ×ᶠ g) ×ᶠ (h ×ᶠ k)) =
  (f ×ᶠ h) ×ᶠ (g ×ᶠ k) :=
by simp_rw [map_swap4_eq_comap, filter.prod, comap_inf, comap_comap, inf_assoc, inf_left_comm]

lemma tendsto_swap4_prod {f : filter α} {g : filter β} {h : filter γ} {k : filter δ} :
  tendsto (λ p : (α × β) × (γ × δ), ((p.1.1, p.2.1), (p.1.2, p.2.2)))
    ((f ×ᶠ g) ×ᶠ (h ×ᶠ k)) ((f ×ᶠ h) ×ᶠ (g ×ᶠ k)) :=
map_swap4_prod.le

lemma {u v w x} prod_map_map_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  (map m₁ f₁) ×ᶠ (map m₂ f₂) = map (λ p : α₁×α₂, (m₁ p.1, m₂ p.2)) (f₁ ×ᶠ f₂) :=
le_antisymm
  (λ s hs,
    let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs in
    filter.sets_of_superset _ (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂)) $
      calc (m₁ '' s₁) ×ˢ (m₂ '' s₂) = (λ p : α₁×α₂, (m₁ p.1, m₂ p.2)) '' s₁ ×ˢ s₂ :
          set.prod_image_image_eq
        ... ⊆ _ : by rwa [image_subset_iff])
  ((tendsto.comp le_rfl tendsto_fst).prod_mk (tendsto.comp le_rfl tendsto_snd))

lemma prod_map_map_eq' {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}
  (f : α₁ → α₂) (g : β₁ → β₂) (F : filter α₁) (G : filter β₁) :
  (map f F) ×ᶠ (map g G) = map (prod.map f g) (F ×ᶠ G) :=
prod_map_map_eq

lemma le_prod_map_fst_snd {f : filter (α × β)} : f ≤ map prod.fst f ×ᶠ map prod.snd f :=
le_inf le_comap_map le_comap_map

lemma tendsto.prod_map {δ : Type*} {f : α → γ} {g : β → δ} {a : filter α} {b : filter β}
  {c : filter γ} {d : filter δ} (hf : tendsto f a c) (hg : tendsto g b d) :
  tendsto (prod.map f g) (a ×ᶠ b) (c ×ᶠ d) :=
begin
  erw [tendsto, ← prod_map_map_eq],
  exact filter.prod_mono hf hg,
end

protected lemma map_prod (m : α × β → γ) (f : filter α) (g : filter β) :
  map m (f ×ᶠ g) = (f.map (λ a b, m (a, b))).seq g :=
begin
  simp [filter.ext_iff, mem_prod_iff, mem_map_seq_iff],
  intro s,
  split,
  exact λ ⟨t, ht, s, hs, h⟩, ⟨s, hs, t, ht, λ x hx y hy, @h ⟨x, y⟩ ⟨hx, hy⟩⟩,
  exact λ ⟨s, hs, t, ht, h⟩, ⟨t, ht, s, hs, λ ⟨x, y⟩ ⟨hx, hy⟩, h x hx y hy⟩
end

lemma prod_eq {f : filter α} {g : filter β} : f ×ᶠ g = (f.map prod.mk).seq g  :=
have h : _ := f.map_prod id g, by rwa [map_id] at h

lemma prod_inf_prod {f₁ f₂ : filter α} {g₁ g₂ : filter β} :
  (f₁ ×ᶠ g₁) ⊓ (f₂ ×ᶠ g₂) = (f₁ ⊓ f₂) ×ᶠ (g₁ ⊓ g₂) :=
by simp only [filter.prod, comap_inf, inf_comm, inf_assoc, inf_left_comm]

@[simp] lemma prod_bot {f : filter α} : f ×ᶠ (⊥ : filter β) = ⊥ := by simp [filter.prod]
@[simp] lemma bot_prod {g : filter β} : (⊥ : filter α) ×ᶠ g = ⊥ := by simp [filter.prod]

@[simp] lemma prod_principal_principal {s : set α} {t : set β} :
  (𝓟 s) ×ᶠ (𝓟 t) = 𝓟 (s ×ˢ t) :=
by simp only [filter.prod, comap_principal, principal_eq_iff_eq, comap_principal, inf_principal];
  refl

@[simp] lemma pure_prod {a : α} {f : filter β} : pure a ×ᶠ f = map (prod.mk a) f :=
by rw [prod_eq, map_pure, pure_seq_eq_map]

lemma map_pure_prod (f : α → β → γ) (a : α) (B : filter β) :
  filter.map (function.uncurry f) (pure a ×ᶠ B) = filter.map (f a) B :=
by { rw filter.pure_prod, refl }

@[simp] lemma prod_pure {f : filter α} {b : β} : f ×ᶠ pure b = map (λ a, (a, b)) f :=
by rw [prod_eq, seq_pure, map_map]

lemma prod_pure_pure {a : α} {b : β} : (pure a) ×ᶠ (pure b) = pure (a, b) :=
by simp

lemma prod_eq_bot {f : filter α} {g : filter β} : f ×ᶠ g = ⊥ ↔ (f = ⊥ ∨ g = ⊥) :=
begin
  split,
  { intro h,
    rcases mem_prod_iff.1 (empty_mem_iff_bot.2 h) with ⟨s, hs, t, ht, hst⟩,
    rw [subset_empty_iff, set.prod_eq_empty_iff] at hst,
    cases hst with s_eq t_eq,
    { left, exact empty_mem_iff_bot.1 (s_eq ▸ hs) },
    { right, exact empty_mem_iff_bot.1 (t_eq ▸ ht) } },
  { rintro (rfl | rfl),
    exact bot_prod,
    exact prod_bot }
end

lemma prod_ne_bot {f : filter α} {g : filter β} : ne_bot (f ×ᶠ g) ↔ (ne_bot f ∧ ne_bot g) :=
by simp only [ne_bot_iff, ne, prod_eq_bot, not_or_distrib]

lemma ne_bot.prod {f : filter α} {g : filter β} (hf : ne_bot f) (hg : ne_bot g) :
  ne_bot (f ×ᶠ g) :=
prod_ne_bot.2 ⟨hf, hg⟩

instance prod_ne_bot' {f : filter α} {g : filter β} [hf : ne_bot f] [hg : ne_bot g] :
  ne_bot (f ×ᶠ g) :=
hf.prod hg

lemma tendsto_prod_iff {f : α × β → γ} {x : filter α} {y : filter β} {z : filter γ} :
  filter.tendsto f (x ×ᶠ y) z ↔
  ∀ W ∈ z, ∃ U ∈ x,  ∃ V ∈ y, ∀ x y, x ∈ U → y ∈ V → f (x, y) ∈ W :=
by simp only [tendsto_def, mem_prod_iff, prod_sub_preimage_iff, exists_prop, iff_self]

lemma tendsto_prod_iff' {f : filter α} {g : filter β} {g' : filter γ}
  {s : α → β × γ} :
  tendsto s f (g ×ᶠ g') ↔ tendsto (λ n, (s n).1) f g ∧ tendsto (λ n, (s n).2) f g' :=
by { unfold filter.prod, simp only [tendsto_inf, tendsto_comap_iff, iff_self] }

end prod

/-! ### Coproducts of filters -/

section coprod
variables {f : filter α} {g : filter β}

/-- Coproduct of filters. -/
protected def coprod (f : filter α) (g : filter β) : filter (α × β) :=
f.comap prod.fst ⊔ g.comap prod.snd

lemma mem_coprod_iff {s : set (α×β)} {f : filter α} {g : filter β} :
  s ∈ f.coprod g ↔ ((∃ t₁ ∈ f, prod.fst ⁻¹' t₁ ⊆ s) ∧ (∃ t₂ ∈ g, prod.snd ⁻¹' t₂ ⊆ s)) :=
by simp [filter.coprod]

@[simp] lemma bot_coprod (l : filter β) : (⊥ : filter α).coprod l = comap prod.snd l :=
by simp [filter.coprod]

@[simp] lemma coprod_bot (l : filter α) : l.coprod (⊥ : filter β) = comap prod.fst l :=
by simp [filter.coprod]

lemma bot_coprod_bot : (⊥ : filter α).coprod (⊥ : filter β) = ⊥ := by simp

lemma compl_mem_coprod {s : set (α × β)} {la : filter α} {lb : filter β} :
  sᶜ ∈ la.coprod lb ↔ (prod.fst '' s)ᶜ ∈ la ∧ (prod.snd '' s)ᶜ ∈ lb :=
by simp only [filter.coprod, mem_sup, compl_mem_comap]

@[mono] lemma coprod_mono {f₁ f₂ : filter α} {g₁ g₂ : filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  f₁.coprod g₁ ≤ f₂.coprod g₂ :=
sup_le_sup (comap_mono hf) (comap_mono hg)

lemma coprod_ne_bot_iff : (f.coprod g).ne_bot ↔ f.ne_bot ∧ nonempty β ∨ nonempty α ∧ g.ne_bot :=
by simp [filter.coprod]

@[instance] lemma coprod_ne_bot_left [ne_bot f] [nonempty β] : (f.coprod g).ne_bot :=
coprod_ne_bot_iff.2 (or.inl ⟨‹_›, ‹_›⟩)

@[instance] lemma coprod_ne_bot_right [ne_bot g] [nonempty α] : (f.coprod g).ne_bot :=
coprod_ne_bot_iff.2 (or.inr ⟨‹_›, ‹_›⟩)

lemma principal_coprod_principal (s : set α) (t : set β) :
  (𝓟 s).coprod (𝓟 t) = 𝓟 (sᶜ ×ˢ tᶜ)ᶜ :=
by rw [filter.coprod, comap_principal, comap_principal, sup_principal, set.prod_eq, compl_inter,
  preimage_compl, preimage_compl, compl_compl, compl_compl]

-- this inequality can be strict; see `map_const_principal_coprod_map_id_principal` and
-- `map_prod_map_const_id_principal_coprod_principal` below.
lemma {u v w x} map_prod_map_coprod_le {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  map (prod.map m₁ m₂) (f₁.coprod f₂) ≤ (map m₁ f₁).coprod (map m₂ f₂) :=
begin
  intros s,
  simp only [mem_map, mem_coprod_iff],
  rintro ⟨⟨u₁, hu₁, h₁⟩, u₂, hu₂, h₂⟩,
  refine ⟨⟨m₁ ⁻¹' u₁, hu₁, λ _ hx, h₁ _⟩, ⟨m₂ ⁻¹' u₂, hu₂, λ _ hx, h₂ _⟩⟩; convert hx
end

/-- Characterization of the coproduct of the `filter.map`s of two principal filters `𝓟 {a}` and
`𝓟 {i}`, the first under the constant function `λ a, b` and the second under the identity function.
Together with the next lemma, `map_prod_map_const_id_principal_coprod_principal`, this provides an
example showing that the inequality in the lemma `map_prod_map_coprod_le` can be strict. -/
lemma map_const_principal_coprod_map_id_principal {α β ι : Type*} (a : α) (b : β) (i : ι) :
  (map (λ _ : α, b) (𝓟 {a})).coprod (map id (𝓟 {i}))
  = 𝓟 (({b} : set β) ×ˢ (univ : set ι) ∪ (univ : set β) ×ˢ ({i} : set ι)) :=
by simp only [map_principal, filter.coprod, comap_principal, sup_principal, image_singleton,
  image_id, prod_univ, univ_prod]

/-- Characterization of the `filter.map` of the coproduct of two principal filters `𝓟 {a}` and
`𝓟 {i}`, under the `prod.map` of two functions, respectively the constant function `λ a, b` and the
identity function.  Together with the previous lemma,
`map_const_principal_coprod_map_id_principal`, this provides an example showing that the inequality
in the lemma `map_prod_map_coprod_le` can be strict. -/
lemma map_prod_map_const_id_principal_coprod_principal {α β ι : Type*} (a : α) (b : β) (i : ι) :
  map (prod.map (λ _ : α, b) id) ((𝓟 {a}).coprod (𝓟 {i}))
  = 𝓟 (({b} : set β) ×ˢ (univ : set ι)) :=
begin
  rw [principal_coprod_principal, map_principal],
  congr,
  ext ⟨b', i'⟩,
  split,
  { rintro ⟨⟨a'', i''⟩, h₁, h₂, h₃⟩,
    simp },
  { rintro ⟨h₁, h₂⟩,
    use (a, i'),
    simpa using h₁.symm }
end

lemma tendsto.prod_map_coprod {δ : Type*} {f : α → γ} {g : β → δ} {a : filter α} {b : filter β}
  {c : filter γ} {d : filter δ} (hf : tendsto f a c) (hg : tendsto g b d) :
  tendsto (prod.map f g) (a.coprod b) (c.coprod d) :=
map_prod_map_coprod_le.trans (coprod_mono hf hg)

end coprod

end filter
