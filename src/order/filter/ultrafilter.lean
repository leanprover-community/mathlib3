/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
import order.filter.cofinite
import order.zorn

/-!
# Ultrafilters

An ultrafilter is a minimal (maximal in the set order) proper filter.
In this file we define

* `ultrafilter.of`: an ultrafilter that is less than or equal to a given filter;
* `ultrafilter`: subtype of ultrafilters;
* `ultrafilter.pure`: `pure x` as an `ultrafiler`;
* `ultrafilter.map`, `ultrafilter.bind`, `ultrafilter.comap` : operations on ultrafilters;
* `hyperfilter`: the ultrafilter extending the cofinite filter.
-/

universes u v
variables {α : Type u} {β : Type v}

open set zorn filter function
open_locale classical filter

/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
@[protect_proj]
structure ultrafilter (α : Type*) extends filter α :=
(ne_bot' : ne_bot to_filter)
(le_of_le : ∀ g, filter.ne_bot g → g ≤ to_filter → to_filter ≤ g)

namespace ultrafilter

variables {f g : ultrafilter α} {s t : set α} {p q : α → Prop}

instance : has_coe_t (ultrafilter α) (filter α) := ⟨ultrafilter.to_filter⟩

instance : has_mem (set α) (ultrafilter α) := ⟨λ s f, s ∈ (f : filter α)⟩

lemma unique (f : ultrafilter α) {g : filter α} (h : g ≤ f)
  (hne : ne_bot g . tactic.apply_instance) : g = f :=
le_antisymm h $ f.le_of_le g hne h

instance ne_bot (f : ultrafilter α) : ne_bot (f : filter α) := f.ne_bot'

@[simp, norm_cast] lemma mem_coe : s ∈ (f : filter α) ↔ s ∈ f := iff.rfl

lemma coe_injective : injective (coe : ultrafilter α → filter α)
| ⟨f, h₁, h₂⟩ ⟨g, h₃, h₄⟩ rfl := by congr

@[simp, norm_cast] lemma coe_le_coe {f g : ultrafilter α} : (f : filter α) ≤ g ↔ f = g :=
⟨λ h, coe_injective $ g.unique h, λ h, h ▸ le_rfl⟩

@[simp, norm_cast] lemma coe_inj : (f : filter α) = g ↔ f = g := coe_injective.eq_iff

@[ext] lemma ext ⦃f g : ultrafilter α⦄ (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g :=
coe_injective $ filter.ext h

lemma le_of_inf_ne_bot (f : ultrafilter α) {g : filter α} (hg : ne_bot (↑f ⊓ g)) : ↑f ≤ g :=
le_of_inf_eq (f.unique inf_le_left hg)

lemma le_of_inf_ne_bot' (f : ultrafilter α) {g : filter α} (hg : ne_bot (g ⊓ f)) : ↑f ≤ g :=
f.le_of_inf_ne_bot $ by rwa inf_comm

@[simp] lemma compl_not_mem_iff : sᶜ ∉ f ↔ s ∈ f :=
⟨λ hsc, le_principal_iff.1 $ f.le_of_inf_ne_bot
  ⟨λ h, hsc $ mem_of_eq_bot$ by rwa compl_compl⟩, compl_not_mem⟩

@[simp] lemma frequently_iff_eventually : (∃ᶠ x in f, p x) ↔ ∀ᶠ x in f, p x :=
compl_not_mem_iff

alias frequently_iff_eventually ↔ filter.frequently.eventually _

lemma compl_mem_iff_not_mem : sᶜ ∈ f ↔ s ∉ f := by rw [← compl_not_mem_iff, compl_compl]

lemma diff_mem_iff (f : ultrafilter α) : s \ t ∈ f ↔ s ∈ f ∧ t ∉ f :=
inter_mem_iff.trans $ and_congr iff.rfl compl_mem_iff_not_mem

/-- If `sᶜ ∉ f ↔ s ∈ f`, then `f` is an ultrafilter. The other implication is given by
`ultrafilter.compl_not_mem_iff`.  -/
def of_compl_not_mem_iff (f : filter α) (h : ∀ s, sᶜ ∉ f ↔ s ∈ f) : ultrafilter α :=
{ to_filter := f,
  ne_bot' := ⟨λ hf, by simpa [hf] using h⟩,
  le_of_le := λ g hg hgf s hs, (h s).1 $ λ hsc, by exactI compl_not_mem hs (hgf hsc) }

lemma nonempty_of_mem (hs : s ∈ f) : s.nonempty := nonempty_of_mem hs
lemma ne_empty_of_mem (hs : s ∈ f) : s ≠ ∅ := (nonempty_of_mem hs).ne_empty
@[simp] lemma empty_not_mem : ∅ ∉ f := empty_not_mem f

lemma mem_or_compl_mem (f : ultrafilter α) (s : set α) : s ∈ f ∨ sᶜ ∈ f :=
or_iff_not_imp_left.2 compl_mem_iff_not_mem.2

protected lemma em (f : ultrafilter α) (p : α → Prop) :
  (∀ᶠ x in f, p x) ∨ ∀ᶠ x in f, ¬p x :=
f.mem_or_compl_mem {x | p x}

lemma eventually_or : (∀ᶠ x in f, p x ∨ q x) ↔ (∀ᶠ x in f, p x) ∨ ∀ᶠ x in f, q x :=
⟨λ H, (f.em p).imp_right $ λ hp, (H.and hp).mono $ λ x ⟨hx, hnx⟩, hx.resolve_left hnx,
  λ H, H.elim (λ hp, hp.mono $ λ x, or.inl) (λ hp, hp.mono $ λ x, or.inr)⟩

lemma union_mem_iff : s ∪ t ∈ f ↔ s ∈ f ∨ t ∈ f := eventually_or

lemma eventually_not : (∀ᶠ x in f, ¬p x) ↔ ¬∀ᶠ x in f, p x := compl_mem_iff_not_mem

lemma eventually_imp : (∀ᶠ x in f, p x → q x) ↔ (∀ᶠ x in f, p x) → ∀ᶠ x in f, q x :=
by simp only [imp_iff_not_or, eventually_or, eventually_not]

lemma finite_sUnion_mem_iff {s : set (set α)} (hs : finite s) : ⋃₀ s ∈ f ↔ ∃t∈s, t ∈ f :=
finite.induction_on hs (by simp) $ λ a s ha hs his,
  by simp [union_mem_iff, his, or_and_distrib_right, exists_or_distrib]

lemma finite_bUnion_mem_iff {is : set β} {s : β → set α} (his : finite is) :
  (⋃i∈is, s i) ∈ f ↔ ∃i∈is, s i ∈ f :=
by simp only [← sUnion_image, finite_sUnion_mem_iff (his.image s), bex_image_iff]

/-- Pushforward for ultrafilters. -/
def map (m : α → β) (f : ultrafilter α) : ultrafilter β :=
of_compl_not_mem_iff (map m f) $ λ s, @compl_not_mem_iff _ f (m ⁻¹' s)

@[simp, norm_cast] lemma coe_map (m : α → β) (f : ultrafilter α) :
  (map m f : filter β) = filter.map m ↑f := rfl

@[simp] lemma mem_map {m : α → β} {f : ultrafilter α} {s : set β} :
  s ∈ map m f ↔ m ⁻¹' s ∈ f := iff.rfl

/-- The pullback of an ultrafilter along an injection whose range is large with respect to the given
ultrafilter. -/
def comap {m : α → β} (u : ultrafilter β) (inj : injective m)
  (large : set.range m ∈ u) : ultrafilter α :=
{ to_filter := comap m u,
  ne_bot' := u.ne_bot'.comap_of_range_mem large,
  le_of_le := λ g hg hgu, by { resetI,
    simp only [← u.unique (map_le_iff_le_comap.2 hgu), comap_map inj, le_rfl] } }

@[simp] lemma mem_comap {m : α → β} (u : ultrafilter β) (inj : injective m)
  (large : set.range m ∈ u) {s : set α} :
  s ∈ u.comap inj large ↔ m '' s ∈ u :=
mem_comap_iff inj large

@[simp] lemma coe_comap {m : α → β} (u : ultrafilter β) (inj : injective m)
  (large : set.range m ∈ u) : (u.comap inj large : filter α) = filter.comap m u := rfl

/-- The principal ultrafilter associated to a point `x`. -/
instance : has_pure ultrafilter :=
⟨λ α a, of_compl_not_mem_iff (pure a) $ λ s, by simp⟩

@[simp] lemma mem_pure {a : α} {s : set α} : s ∈ (pure a : ultrafilter α) ↔ a ∈ s := iff.rfl

instance [inhabited α] : inhabited (ultrafilter α) := ⟨pure (default _)⟩
instance [nonempty α] : nonempty (ultrafilter α) := nonempty.map pure infer_instance

lemma eq_principal_of_finite_mem {f : ultrafilter α} {s : set α} (h : s.finite) (h' : s ∈ f) :
  ∃ x ∈ s, (f : filter α) = pure x :=
begin
  rw ← bUnion_of_singleton s at h',
  rcases (ultrafilter.finite_bUnion_mem_iff h).mp h' with ⟨a, has, haf⟩,
  use [a, has],
  change (f : filter α) = (pure a : ultrafilter α),
  rw [ultrafilter.coe_inj, ← ultrafilter.coe_le_coe],
  change (f : filter α) ≤ pure a,
  rwa [← principal_singleton, le_principal_iff]
end

/-- Monadic bind for ultrafilters, coming from the one on filters
defined in terms of map and join.-/
def bind (f : ultrafilter α) (m : α → ultrafilter β) : ultrafilter β :=
of_compl_not_mem_iff (bind ↑f (λ x, ↑(m x))) $ λ s,
  by simp only [mem_bind', mem_coe, ← compl_mem_iff_not_mem, compl_set_of, compl_compl]

instance has_bind : has_bind ultrafilter := ⟨@ultrafilter.bind⟩
instance functor : functor ultrafilter := { map := @ultrafilter.map }
instance monad : monad ultrafilter := { map := @ultrafilter.map }

section

local attribute [instance] filter.monad filter.is_lawful_monad

instance is_lawful_monad : is_lawful_monad ultrafilter :=
{ id_map := assume α f, coe_injective (id_map f.1),
  pure_bind := assume α β a f, coe_injective (pure_bind a (coe ∘ f)),
  bind_assoc := assume α β γ f m₁ m₂, coe_injective (filter_eq rfl),
  bind_pure_comp_eq_map := assume α β f x, coe_injective (bind_pure_comp_eq_map f x.1) }

end

/-- The ultrafilter lemma: Any proper filter is contained in an ultrafilter. -/
lemma exists_le (f : filter α) [h : ne_bot f] : ∃u : ultrafilter α, ↑u ≤ f :=
begin
  let τ                := {f' // ne_bot f' ∧ f' ≤ f},
  let r : τ → τ → Prop := λt₁ t₂, t₂.val ≤ t₁.val,
  haveI                := nonempty_of_ne_bot f,
  let top : τ          := ⟨f, h, le_refl f⟩,
  let sup : Π(c:set τ), chain r c → τ :=
    λc hc, ⟨⨅a:{a:τ // a ∈ insert top c}, a.1,
      infi_ne_bot_of_directed
        (directed_of_chain $ chain_insert hc $ λ ⟨b, _, hb⟩ _ _, or.inl hb)
        (assume ⟨⟨a, ha, _⟩, _⟩, ha),
      infi_le_of_le ⟨top, mem_insert _ _⟩ (le_refl _)⟩,
  have : ∀c (hc: chain r c) a (ha : a ∈ c), r a (sup c hc),
    from assume c hc a ha, infi_le_of_le ⟨a, mem_insert_of_mem _ ha⟩ (le_refl _),
  have : (∃ (u : τ), ∀ (a : τ), r u a → r a u),
    from exists_maximal_of_chains_bounded (assume c hc, ⟨sup c hc, this c hc⟩)
      (assume f₁ f₂ f₃ h₁ h₂, le_trans h₂ h₁),
  cases this with uτ hmin,
  exact ⟨⟨uτ.val, uτ.property.left, assume g hg₁ hg₂,
    hmin ⟨g, hg₁, le_trans hg₂ uτ.property.right⟩ hg₂⟩, uτ.property.right⟩
end

alias exists_le ← filter.exists_ultrafilter_le

/-- Construct an ultrafilter extending a given filter.
  The ultrafilter lemma is the assertion that such a filter exists;
  we use the axiom of choice to pick one. -/
noncomputable def of (f : filter α) [ne_bot f] : ultrafilter α :=
classical.some (exists_le f)

lemma of_le (f : filter α) [ne_bot f] : ↑(of f) ≤ f := classical.some_spec (exists_le f)

lemma of_coe (f : ultrafilter α) : of ↑f = f :=
coe_inj.1 $ f.unique (of_le f)

lemma exists_ultrafilter_of_finite_inter_nonempty (S : set (set α))
  (cond : ∀ T : finset (set α), (↑T : set (set α)) ⊆ S → (⋂₀ (↑T : set (set α))).nonempty) :
  ∃ F : ultrafilter α, S ⊆ F.sets :=
begin
  suffices : ∃ F : filter α, ne_bot F ∧ S ⊆ F.sets,
  { rcases this with ⟨F, cond, hF⟩,
    resetI,
    obtain ⟨G : ultrafilter α, h1 : ↑G ≤ F⟩ := exists_le F,
    exact ⟨G, λ T hT, h1 (hF hT)⟩ },
  use filter.generate S,
  refine ⟨_, λ T hT, filter.generate_sets.basic hT⟩,
  rw ← forall_mem_nonempty_iff_ne_bot,
  intros T hT,
  rcases mem_generate_iff.mp hT with ⟨A, h1, h2, h3⟩,
  let B := set.finite.to_finset h2,
  rw (show A = ↑B, by simp) at *,
  rcases cond B h1 with ⟨x, hx⟩,
  exact ⟨x, h3 hx⟩,
end

end ultrafilter

namespace filter

open ultrafilter

lemma mem_iff_ultrafilter {s : set α} {f : filter α} :
  s ∈ f ↔ ∀ g : ultrafilter α, ↑g ≤ f → s ∈ g :=
begin
  refine ⟨λ hf g hg, hg hf, λ H, by_contra $ λ hf, _⟩,
  set g : filter ↥sᶜ := comap coe f,
  haveI : ne_bot g := comap_ne_bot_iff_compl_range.2 (by simpa [compl_set_of]),
  simpa using H ((of g).map coe) (map_le_iff_le_comap.mpr (of_le g))
end

lemma le_iff_ultrafilter {f₁ f₂ : filter α} : f₁ ≤ f₂ ↔ ∀ g : ultrafilter α, ↑g ≤ f₁ → ↑g ≤ f₂ :=
⟨λ h g h₁, h₁.trans h, λ h s hs, mem_iff_ultrafilter.2 $ λ g hg, h g hg hs⟩

/-- A filter equals the intersection of all the ultrafilters which contain it. -/
lemma supr_ultrafilter_le_eq (f : filter α) :
  (⨆ (g : ultrafilter α) (hg : ↑g ≤ f), (g : filter α)) = f :=
eq_of_forall_ge_iff $ λ f', by simp only [supr_le_iff, ← le_iff_ultrafilter]

/-- The `tendsto` relation can be checked on ultrafilters. -/
lemma tendsto_iff_ultrafilter (f : α → β) (l₁ : filter α) (l₂ : filter β) :
  tendsto f l₁ l₂ ↔ ∀ g : ultrafilter α, ↑g ≤ l₁ → tendsto f g l₂ :=
by simpa only [tendsto_iff_comap] using le_iff_ultrafilter

lemma exists_ultrafilter_iff {f : filter α} : (∃ (u : ultrafilter α), ↑u ≤ f) ↔ ne_bot f :=
⟨λ ⟨u, uf⟩, ne_bot_of_le uf, λ h, @exists_ultrafilter_le _ _ h⟩

lemma forall_ne_bot_le_iff {g : filter α} {p : filter α → Prop} (hp : monotone p) :
  (∀ f : filter α, ne_bot f → f ≤ g → p f) ↔ ∀ f : ultrafilter α, ↑f ≤ g → p f :=
begin
  refine ⟨λ H f hf, H f f.ne_bot hf, _⟩,
  introsI H f hf hfg,
  exact hp (of_le f) (H _ ((of_le f).trans hfg))
end

section hyperfilter

variables (α) [infinite α]

/-- The ultrafilter extending the cofinite filter. -/
noncomputable def hyperfilter : ultrafilter α := ultrafilter.of cofinite

variable {α}

lemma hyperfilter_le_cofinite : ↑(hyperfilter α) ≤ @cofinite α :=
ultrafilter.of_le cofinite

@[simp] lemma bot_ne_hyperfilter : (⊥ : filter α) ≠ hyperfilter α :=
(by apply_instance : ne_bot ↑(hyperfilter α)).1.symm

theorem nmem_hyperfilter_of_finite {s : set α} (hf : s.finite) : s ∉ hyperfilter α :=
λ hy, compl_not_mem hy $ hyperfilter_le_cofinite hf.compl_mem_cofinite

alias nmem_hyperfilter_of_finite ← set.finite.nmem_hyperfilter

theorem compl_mem_hyperfilter_of_finite {s : set α} (hf : set.finite s) :
  sᶜ ∈ hyperfilter α :=
compl_mem_iff_not_mem.2 hf.nmem_hyperfilter

alias compl_mem_hyperfilter_of_finite ← set.finite.compl_mem_hyperfilter

theorem mem_hyperfilter_of_finite_compl {s : set α} (hf : set.finite sᶜ) :
  s ∈ hyperfilter α :=
compl_compl s ▸ hf.compl_mem_hyperfilter

end hyperfilter

end filter
