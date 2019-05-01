/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Order on topological structures. Lattice structure, Galois connection, and applications.
-/
import topology.basic

open set filter lattice classical
local attribute [instance] prop_decidable

universes u v w

namespace topological_space
variables {α : Type u}

/-- The least topology containing a collection of basic sets. -/
inductive generate_open (g : set (set α)) : set α → Prop
| basic  : ∀s∈g, generate_open s
| univ   : generate_open univ
| inter  : ∀s t, generate_open s → generate_open t → generate_open (s ∩ t)
| sUnion : ∀k, (∀s∈k, generate_open s) → generate_open (⋃₀ k)

/-- The smallest topological space containing the collection `g` of basic sets -/
def generate_from (g : set (set α)) : topological_space α :=
{ is_open        := generate_open g,
  is_open_univ   := generate_open.univ g,
  is_open_inter  := generate_open.inter,
  is_open_sUnion := generate_open.sUnion  }

lemma nhds_generate_from {g : set (set α)} {a : α} :
  @nhds α (generate_from g) a = (⨅s∈{s | a ∈ s ∧ s ∈ g}, principal s) :=
le_antisymm
  (infi_le_infi $ assume s, infi_le_infi_const $ assume ⟨as, sg⟩, ⟨as, generate_open.basic _ sg⟩)
  (le_infi $ assume s, le_infi $ assume ⟨as, hs⟩,
    have ∀s, generate_open g s → a ∈ s → (⨅s∈{s | a ∈ s ∧ s ∈ g}, principal s) ≤ principal s,
    begin
      intros s hs,
      induction hs,
      case generate_open.basic : s hs
      { exact assume as, infi_le_of_le s $ infi_le _ ⟨as, hs⟩ },
      case generate_open.univ
      { rw [principal_univ],
        exact assume _, le_top },
      case generate_open.inter : s t hs' ht' hs ht
      { exact assume ⟨has, hat⟩, calc _ ≤ principal s ⊓ principal t : le_inf (hs has) (ht hat)
          ... = _ : inf_principal },
      case generate_open.sUnion : k hk' hk
      { exact λ ⟨t, htk, hat⟩, calc _ ≤ principal t : hk t htk hat
          ... ≤ _ : le_principal_iff.2 $ subset_sUnion_of_mem htk }
    end,
    this s hs as)

lemma tendsto_nhds_generate_from {β : Type*} {m : α → β} {f : filter α} {g : set (set β)} {b : β}
  (h : ∀s∈g, b ∈ s → m ⁻¹' s ∈ f) : tendsto m f (@nhds β (generate_from g) b) :=
by rw [nhds_generate_from]; exact
  (tendsto_infi.2 $ assume s, tendsto_infi.2 $ assume ⟨hbs, hsg⟩, tendsto_principal.2 $ h s hsg hbs)

protected def mk_of_nhds (n : α → filter α) : topological_space α :=
{ is_open        := λs, ∀a∈s, s ∈ n a,
  is_open_univ   := assume x h, univ_mem_sets,
  is_open_inter  := assume s t hs ht x ⟨hxs, hxt⟩, inter_mem_sets (hs x hxs) (ht x hxt),
  is_open_sUnion := assume s hs a ⟨x, hx, hxa⟩, mem_sets_of_superset (hs x hx _ hxa) (set.subset_sUnion_of_mem hx) }

lemma nhds_mk_of_nhds (n : α → filter α) (a : α)
  (h₀ : pure ≤ n) (h₁ : ∀{a s}, s ∈ n a → ∃ t ∈ n a, t ⊆ s ∧ ∀a' ∈ t, s ∈ n a') :
  @nhds α (topological_space.mk_of_nhds n) a = n a :=
begin
  letI := topological_space.mk_of_nhds n,
  refine le_antisymm (assume s hs, _) (assume s hs, _),
  { have h₀ : {b | s ∈ n b} ⊆ s := assume b hb, mem_pure_sets.1 $ h₀ b hb,
    have h₁ : {b | s ∈ n b} ∈ nhds a,
    { refine mem_nhds_sets (assume b (hb : s ∈ n b), _) hs,
      rcases h₁ hb with ⟨t, ht, hts, h⟩,
      exact mem_sets_of_superset ht h },
    exact mem_sets_of_superset h₁ h₀ },
  { rcases (@mem_nhds_sets_iff α (topological_space.mk_of_nhds n) _ _).1 hs with ⟨t, hts, ht, hat⟩,
    exact (n a).sets_of_superset (ht _ hat) hts },
end

end topological_space

section lattice

variables {α : Type u} {β : Type v}

instance : partial_order (topological_space α) :=
{ le          := λt s, t.is_open ≤ s.is_open,
  le_antisymm := assume t s h₁ h₂, topological_space_eq $ le_antisymm h₁ h₂,
  le_refl     := assume t, le_refl t.is_open,
  le_trans    := assume a b c h₁ h₂, @le_trans _ _ a.is_open b.is_open c.is_open h₁ h₂ }

lemma generate_from_le_iff_subset_is_open {g : set (set α)} {t : topological_space α} :
  topological_space.generate_from g ≤ t ↔ g ⊆ {s | t.is_open s} :=
iff.intro
  (assume ht s hs, ht _ $ topological_space.generate_open.basic s hs)
  (assume hg s hs, hs.rec_on (assume v hv, hg hv)
    t.is_open_univ (assume u v _ _, t.is_open_inter u v) (assume k _, t.is_open_sUnion k))

protected def mk_of_closure (s : set (set α))
  (hs : {u | (topological_space.generate_from s).is_open u} = s) : topological_space α :=
{ is_open        := λu, u ∈ s,
  is_open_univ   := hs ▸ topological_space.generate_open.univ _,
  is_open_inter  := hs ▸ topological_space.generate_open.inter,
  is_open_sUnion := hs ▸ topological_space.generate_open.sUnion }

lemma mk_of_closure_sets {s : set (set α)}
  {hs : {u | (topological_space.generate_from s).is_open u} = s} :
  mk_of_closure s hs = topological_space.generate_from s :=
topological_space_eq hs.symm

def gi_generate_from (α : Type*) :
  galois_insertion topological_space.generate_from (λt:topological_space α, {s | t.is_open s}) :=
{ gc        := assume g t, generate_from_le_iff_subset_is_open,
  le_l_u    := assume ts s hs, topological_space.generate_open.basic s hs,
  choice    := λg hg, mk_of_closure g
    (subset.antisymm hg $ generate_from_le_iff_subset_is_open.1 $ le_refl _),
  choice_eq := assume s hs, mk_of_closure_sets }

lemma generate_from_mono {α} {g₁ g₂ : set (set α)} (h : g₁ ⊆ g₂) :
  topological_space.generate_from g₁ ≤ topological_space.generate_from g₂ :=
(gi_generate_from _).gc.monotone_l h

instance {α : Type u} : complete_lattice (topological_space α) :=
(gi_generate_from α).lift_complete_lattice

class discrete_topology (α : Type*) [t : topological_space α] : Prop :=
(eq_top : t = ⊤)

@[simp] lemma is_open_discrete [topological_space α] [discrete_topology α] (s : set α) :
  is_open s :=
(discrete_topology.eq_top α).symm ▸ trivial

lemma continuous_of_discrete_topology [topological_space α] [discrete_topology α] [topological_space β] {f : α → β} : continuous f :=
λs hs, is_open_discrete _

lemma nhds_top (α : Type*) : (@nhds α ⊤) = pure :=
begin
  ext a s,
  rw [mem_nhds_sets_iff, mem_pure_iff],
  split,
  { exact assume ⟨t, ht, _, hta⟩, ht hta },
  { exact assume h, ⟨{a}, set.singleton_subset_iff.2 h, trivial, set.mem_singleton a⟩ }
end

lemma nhds_discrete (α : Type*) [topological_space α] [discrete_topology α] : (@nhds α _) = pure :=
(discrete_topology.eq_top α).symm ▸ nhds_top α

lemma le_of_nhds_le_nhds {t₁ t₂ : topological_space α} (h : ∀x, @nhds α t₂ x ≤ @nhds α t₁ x) :
  t₁ ≤ t₂ :=
assume s, show @is_open α t₁ s → @is_open α t₂ s,
  begin simp only [is_open_iff_nhds, le_principal_iff];
    exact assume hs a ha, h _ $ hs _ ha end

lemma eq_of_nhds_eq_nhds {t₁ t₂ : topological_space α} (h : ∀x, @nhds α t₂ x = @nhds α t₁ x) :
  t₁ = t₂ :=
le_antisymm
  (le_of_nhds_le_nhds $ assume x, le_of_eq $ h x)
  (le_of_nhds_le_nhds $ assume x, le_of_eq $ (h x).symm)

lemma eq_top_of_singletons_open {t : topological_space α} (h : ∀ x, t.is_open {x}) : t = ⊤ :=
top_unique $ le_of_nhds_le_nhds $ assume x,
  have nhds x ≤ pure x, from infi_le_of_le {x} (infi_le _ (by simpa using h x)),
  le_trans this (@pure_le_nhds _ ⊤ x)

end lattice

section galois_connection
variables {α : Type*} {β : Type*} {γ : Type*}

/-- Given `f : α → β` and a topology on `β`, the induced topology on `α` is the collection of
  sets that are preimages of some open set in `β`. This is the coarsest topology that
  makes `f` continuous. -/
def topological_space.induced {α : Type u} {β : Type v} (f : α → β) (t : topological_space β) :
  topological_space α :=
{ is_open        := λs, ∃s', t.is_open s' ∧ f ⁻¹' s' = s,
  is_open_univ   := ⟨univ, t.is_open_univ, preimage_univ⟩,
  is_open_inter  := by rintro s₁ s₂ ⟨s'₁, hs₁, rfl⟩ ⟨s'₂, hs₂, rfl⟩;
    exact ⟨s'₁ ∩ s'₂, t.is_open_inter _ _ hs₁ hs₂, preimage_inter⟩,
  is_open_sUnion := assume s h,
  begin
    simp only [classical.skolem] at h,
    cases h with f hf,
    apply exists.intro (⋃(x : set α) (h : x ∈ s), f x h),
    simp only [sUnion_eq_bUnion, preimage_Union, (λx h, (hf x h).right)], refine ⟨_, rfl⟩,
    exact (@is_open_Union β _ t _ $ assume i,
      show is_open (⋃h, f i h), from @is_open_Union β _ t _ $ assume h, (hf i h).left)
  end }

lemma is_open_induced_iff [t : topological_space β] {s : set α} {f : α → β} :
  @is_open α (t.induced f) s ↔ (∃t, is_open t ∧ f ⁻¹' t = s) :=
iff.refl _

lemma is_closed_induced_iff [t : topological_space β] {s : set α} {f : α → β} :
  @is_closed α (t.induced f) s ↔ (∃t, is_closed t ∧ s = f ⁻¹' t) :=
⟨assume ⟨t, ht, heq⟩, ⟨-t, is_closed_compl_iff.2 ht,
    by simp only [preimage_compl, heq, lattice.neg_neg]⟩,
  assume ⟨t, ht, heq⟩, ⟨-t, ht, by simp only [preimage_compl, heq.symm]⟩⟩

/-- Given `f : α → β` and a topology on `α`, the coinduced topology on `β` is defined
  such that `s:set β` is open if the preimage of `s` is open. This is the finest topology that
  makes `f` continuous. -/
def topological_space.coinduced {α : Type u} {β : Type v} (f : α → β) (t : topological_space α) :
  topological_space β :=
{ is_open        := λs, t.is_open (f ⁻¹' s),
  is_open_univ   := by rw preimage_univ; exact t.is_open_univ,
  is_open_inter  := assume s₁ s₂ h₁ h₂, by rw preimage_inter; exact t.is_open_inter _ _ h₁ h₂,
  is_open_sUnion := assume s h, by rw [preimage_sUnion]; exact (@is_open_Union _ _ t _ $ assume i,
    show is_open (⋃ (H : i ∈ s), f ⁻¹' i), from
      @is_open_Union _ _ t _ $ assume hi, h i hi) }

lemma is_open_coinduced {t : topological_space α} {s : set β} {f : α → β} :
  @is_open β (topological_space.coinduced f t) s ↔ is_open (f ⁻¹' s) :=
iff.refl _

variables {t t₁ t₂ : topological_space α} {t' : topological_space β} {f : α → β} {g : β → α}

lemma induced_le_iff_le_coinduced {f : α → β } {tα : topological_space α} {tβ : topological_space β} :
  tβ.induced f ≤ tα ↔ tβ ≤ tα.coinduced f :=
iff.intro
  (assume h s hs, show tα.is_open (f ⁻¹' s), from h _ ⟨s, hs, rfl⟩)
  (assume h s ⟨t, ht, hst⟩, hst ▸ h _ ht)

lemma gc_induced_coinduced (f : α → β) :
  galois_connection (topological_space.induced f) (topological_space.coinduced f) :=
assume f g, induced_le_iff_le_coinduced

lemma induced_mono (h : t₁ ≤ t₂) : t₁.induced g ≤ t₂.induced g :=
(gc_induced_coinduced g).monotone_l h

lemma coinduced_mono (h : t₁ ≤ t₂) : t₁.coinduced f ≤ t₂.coinduced f :=
(gc_induced_coinduced f).monotone_u h

@[simp] lemma induced_bot : (⊥ : topological_space α).induced g = ⊥ :=
(gc_induced_coinduced g).l_bot

@[simp] lemma induced_sup : (t₁ ⊔ t₂).induced g = t₁.induced g ⊔ t₂.induced g :=
(gc_induced_coinduced g).l_sup

@[simp] lemma induced_supr {ι : Sort w} {t : ι → topological_space α} :
  (⨆i, t i).induced g = (⨆i, (t i).induced g) :=
(gc_induced_coinduced g).l_supr

@[simp] lemma coinduced_top : (⊤ : topological_space α).coinduced f = ⊤ :=
(gc_induced_coinduced f).u_top

@[simp] lemma coinduced_inf : (t₁ ⊓ t₂).coinduced f = t₁.coinduced f ⊓ t₂.coinduced f :=
(gc_induced_coinduced f).u_inf

@[simp] lemma coinduced_infi {ι : Sort w} {t : ι → topological_space α} :
  (⨅i, t i).coinduced f = (⨅i, (t i).coinduced f) :=
(gc_induced_coinduced f).u_infi

lemma induced_id [t : topological_space α] : t.induced id = t :=
topological_space_eq $ funext $ assume s, propext $
  ⟨assume ⟨s', hs, h⟩, h ▸ hs, assume hs, ⟨s, hs, rfl⟩⟩

lemma induced_compose [tβ : topological_space β] [tγ : topological_space γ]
  {f : α → β} {g : β → γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f) :=
topological_space_eq $ funext $ assume s, propext $
  ⟨assume ⟨s', ⟨s, hs, h₂⟩, h₁⟩, h₁ ▸ h₂ ▸ ⟨s, hs, rfl⟩,
    assume ⟨s, hs, h⟩, ⟨preimage g s, ⟨s, hs, rfl⟩, h ▸ rfl⟩⟩

lemma coinduced_id [t : topological_space α] : t.coinduced id = t :=
topological_space_eq rfl

lemma coinduced_compose [tα : topological_space α]
  {f : α → β} {g : β → γ} : (tα.coinduced f).coinduced g = tα.coinduced (g ∘ f) :=
topological_space_eq rfl

end galois_connection

/- constructions using the complete lattice structure -/
section constructions
open topological_space

variables {α : Type u} {β : Type v}

instance inhabited_topological_space {α : Type u} : inhabited (topological_space α) :=
⟨⊤⟩

instance : topological_space empty := ⊤
instance : discrete_topology empty := ⟨rfl⟩
instance : topological_space unit := ⊤
instance : discrete_topology unit := ⟨rfl⟩
instance : topological_space bool := ⊤
instance : discrete_topology bool := ⟨rfl⟩
instance : topological_space ℕ := ⊤
instance : discrete_topology ℕ := ⟨rfl⟩
instance : topological_space ℤ := ⊤
instance : discrete_topology ℤ := ⟨rfl⟩

instance sierpinski_space : topological_space Prop :=
generate_from {{true}}

instance {p : α → Prop} [t : topological_space α] : topological_space (subtype p) :=
induced subtype.val t

instance {r : α → α → Prop} [t : topological_space α] : topological_space (quot r) :=
coinduced (quot.mk r) t

instance {s : setoid α} [t : topological_space α] : topological_space (quotient s) :=
coinduced quotient.mk t

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α × β) :=
induced prod.fst t₁ ⊔ induced prod.snd t₂

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α ⊕ β) :=
coinduced sum.inl t₁ ⊓ coinduced sum.inr t₂

instance {β : α → Type v} [t₂ : Πa, topological_space (β a)] : topological_space (sigma β) :=
⨅a, coinduced (sigma.mk a) (t₂ a)

instance Pi.topological_space {β : α → Type v} [t₂ : Πa, topological_space (β a)] :
  topological_space (Πa, β a) :=
⨆a, induced (λf, f a) (t₂ a)

instance [topological_space α] : topological_space (list α) :=
topological_space.mk_of_nhds (traverse nhds)

lemma nhds_list [topological_space α] (as : list α) : nhds as = traverse nhds as :=
begin
  refine nhds_mk_of_nhds _ _ _ _,
  { assume l, induction l,
    case list.nil { exact le_refl _ },
    case list.cons : a l ih {
      suffices : list.cons <$> pure a <*> pure l ≤ list.cons <$> nhds a <*> traverse nhds l,
      { simpa only [-filter.pure_def] with functor_norm using this },
      exact filter.seq_mono (filter.map_mono $ pure_le_nhds a) ih } },
  { assume l s hs,
    rcases (mem_traverse_sets_iff _ _).1 hs with ⟨u, hu, hus⟩, clear as hs,
    have : ∃v:list (set α), l.forall₂ (λa s, is_open s ∧ a ∈ s) v ∧ sequence v ⊆ s,
    { induction hu generalizing s,
      case list.forall₂.nil : hs this { existsi [], simpa only [list.forall₂_nil_left_iff, exists_eq_left] },
      case list.forall₂.cons : a s as ss ht h ih t hts {
        rcases mem_nhds_sets_iff.1 ht with ⟨u, hut, hu⟩,
        rcases ih (subset.refl _) with ⟨v, hv, hvss⟩,
        exact ⟨u::v, list.forall₂.cons hu hv,
          subset.trans (set.seq_mono (set.image_subset _ hut) hvss) hts⟩ } },
    rcases this with ⟨v, hv, hvs⟩,
    refine ⟨sequence v, mem_traverse_sets _ _ _, hvs, _⟩,
    { exact hv.imp (assume a s ⟨hs, ha⟩, mem_nhds_sets hs ha) },
    { assume u hu,
      have hu := (list.mem_traverse _ _).1 hu,
      have : list.forall₂ (λa s, is_open s ∧ a ∈ s) u v,
      { refine list.forall₂.flip _,
        replace hv := hv.flip,
        simp only [list.forall₂_and_left, flip] at ⊢ hv,
        exact ⟨hv.1, hu.flip⟩ },
      refine mem_sets_of_superset _ hvs,
      exact mem_traverse_sets _ _ (this.imp $ assume a s ⟨hs, ha⟩, mem_nhds_sets hs ha) } }
end

lemma nhds_nil [topological_space α] : nhds ([] : list α) = pure [] :=
by rw [nhds_list, list.traverse_nil _]; apply_instance

lemma nhds_cons [topological_space α] (a : α) (l : list α) :
  nhds (a :: l) = list.cons <$> nhds a <*> nhds l  :=
by rw [nhds_list, list.traverse_cons _, ← nhds_list]; apply_instance

lemma quotient_dense_of_dense [setoid α] [topological_space α] {s : set α} (H : ∀ x, x ∈ closure s) :
  closure (quotient.mk '' s) = univ :=
eq_univ_of_forall $ λ x, begin
  rw mem_closure_iff,
  intros U U_op x_in_U,
  let V := quotient.mk ⁻¹' U,
  cases quotient.exists_rep x with y y_x,
  have y_in_V : y ∈ V, by simp only [mem_preimage_eq, y_x, x_in_U],
  have V_op : is_open V := U_op,
  have : V ∩ s ≠ ∅ := mem_closure_iff.1 (H y) V V_op y_in_V,
  rcases exists_mem_of_ne_empty this with ⟨w, w_in_V, w_in_range⟩,
  exact ne_empty_of_mem ⟨w_in_V, mem_image_of_mem quotient.mk w_in_range⟩
end

lemma generate_from_le {t : topological_space α} { g : set (set α) } (h : ∀s∈g, is_open s) :
  generate_from g ≤ t :=
generate_from_le_iff_subset_is_open.2 h

lemma induced_generate_from_eq {α β} {b : set (set β)} {f : α → β} :
  (generate_from b).induced f = topological_space.generate_from (preimage f '' b) :=
le_antisymm
  (induced_le_iff_le_coinduced.2 $ generate_from_le $ assume s hs,
    generate_open.basic _ $ mem_image_of_mem _ hs)
  (generate_from_le $ ball_image_iff.2 $ assume s hs, ⟨s, generate_open.basic _ hs, rfl⟩)

protected def topological_space.nhds_adjoint (a : α) (f : filter α) : topological_space α :=
{ is_open        := λs, a ∈ s → s ∈ f,
  is_open_univ   := assume s, univ_mem_sets,
  is_open_inter  := assume s t hs ht ⟨has, hat⟩, inter_mem_sets (hs has) (ht hat),
  is_open_sUnion := assume k hk ⟨u, hu, hau⟩, mem_sets_of_superset (hk u hu hau) (subset_sUnion_of_mem hu) }

lemma gc_nhds (a : α) :
  @galois_connection _ (order_dual (filter α)) _ _ (λt, @nhds α t a) (topological_space.nhds_adjoint a) :=
assume t (f : filter α), show f ≤ @nhds α t a ↔ _, from iff.intro
  (assume h s hs has, h $ @mem_nhds_sets α t a s hs has)
  (assume h, le_infi $ assume u, le_infi $ assume ⟨hau, hu⟩, le_principal_iff.2 $ h _ hu hau)

lemma nhds_mono {t₁ t₂ : topological_space α} {a : α} (h : t₁ ≤ t₂) :
  @nhds α t₂ a ≤ @nhds α t₁ a := (gc_nhds a).monotone_l h

lemma nhds_supr {ι : Sort*} {t : ι → topological_space α} {a : α} :
  @nhds α (supr t) a = (⨅i, @nhds α (t i) a) := (gc_nhds a).l_supr

lemma nhds_Sup {s : set (topological_space α)} {a : α} :
  @nhds α (Sup s) a = (⨅t∈s, @nhds α t a) := (gc_nhds a).l_Sup

lemma nhds_sup {t₁ t₂ : topological_space α} {a : α} :
  @nhds α (t₁ ⊔ t₂) a = @nhds α t₁ a ⊓ @nhds α t₂ a := (gc_nhds a).l_sup

lemma nhds_bot {a : α} : @nhds α ⊥ a = ⊤ := (gc_nhds a).l_bot

instance {p : α → Prop} [topological_space α] [discrete_topology α] :
  discrete_topology (subtype p) :=
⟨top_unique $ assume s hs,
  ⟨subtype.val '' s, is_open_discrete _, (set.preimage_image_eq _ subtype.val_injective)⟩⟩

instance sum.discrete_topology [topological_space α] [topological_space β]
  [hα : discrete_topology α] [hβ : discrete_topology β] : discrete_topology (α ⊕ β) :=
⟨by unfold sum.topological_space; simp [hα.eq_top, hβ.eq_top]⟩

instance sigma.discrete_topology {β : α → Type v} [Πa, topological_space (β a)]
  [h : Πa, discrete_topology (β a)] : discrete_topology (sigma β) :=
⟨by unfold sigma.topological_space; simp [λ a, (h a).eq_top]⟩

local notation `cont` := @continuous _ _
local notation `tspace` := topological_space
open topological_space

variables {γ : Type*} {f : α → β} {ι : Sort*}

lemma continuous_iff_le_coinduced {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ t₂ ≤ coinduced f t₁ := iff.rfl

lemma continuous_iff_induced_le {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ induced f t₂ ≤ t₁ :=
iff.trans continuous_iff_le_coinduced (gc_induced_coinduced f _ _).symm

theorem continuous_generated_from {t : tspace α} {b : set (set β)}
  (h : ∀s∈b, is_open (f ⁻¹' s)) : cont t (generate_from b) f :=
continuous_iff_le_coinduced.2 $ generate_from_le h

lemma continuous_induced_dom {t : tspace β} : cont (induced f t) t f :=
assume s h, ⟨_, h, rfl⟩

lemma continuous_induced_rng {g : γ → α} {t₂ : tspace β} {t₁ : tspace γ}
  (h : cont t₁ t₂ (f ∘ g)) : cont t₁ (induced f t₂) g :=
assume s ⟨t, ht, s_eq⟩, s_eq ▸ h t ht

lemma continuous_coinduced_rng {t : tspace α} : cont t (coinduced f t) f :=
assume s h, h

lemma continuous_coinduced_dom {g : β → γ} {t₁ : tspace α} {t₂ : tspace γ}
  (h : cont t₁ t₂ (g ∘ f)) : cont (coinduced f t₁) t₂ g :=
assume s hs, h s hs

lemma continuous_le_dom {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h₁ : t₁ ≤ t₂) (h₂ : cont t₁ t₃ f) : cont t₂ t₃ f :=
assume s h, h₁ _ (h₂ s h)

lemma continuous_le_rng {t₁ : tspace α} {t₂ t₃ : tspace β}
  (h₁ : t₃ ≤ t₂) (h₂ : cont t₁ t₂ f) : cont t₁ t₃ f :=
assume s h, h₂ s (h₁ s h)

lemma continuous_inf_dom {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h₁ : cont t₁ t₃ f) (h₂ : cont t₂ t₃ f) : cont (t₁ ⊓ t₂) t₃ f :=
assume s h, ⟨h₁ s h, h₂ s h⟩

lemma continuous_inf_rng_left {t₁ : tspace α} {t₃ t₂ : tspace β} :
  cont t₁ t₂ f → cont t₁ (t₂ ⊓ t₃) f :=
continuous_le_rng inf_le_left

lemma continuous_inf_rng_right {t₁ : tspace α} {t₃ t₂ : tspace β} :
  cont t₁ t₃ f → cont t₁ (t₂ ⊓ t₃) f :=
continuous_le_rng inf_le_right

lemma continuous_Inf_dom {t₁ : set (tspace α)} {t₂ : tspace β}
  (h : ∀t∈t₁, cont t t₂ f) : cont (Inf t₁) t₂ f :=
continuous_iff_induced_le.2 $ le_Inf $ assume t ht, continuous_iff_induced_le.1 $ h t ht

lemma continuous_Inf_rng {t₁ : tspace α} {t₂ : set (tspace β)} {t : tspace β}
  (h₁ : t ∈ t₂) (hf : cont t₁ t f) : cont t₁ (Inf t₂) f :=
continuous_iff_le_coinduced.2 $ Inf_le_of_le h₁ $ continuous_iff_le_coinduced.1 hf

lemma continuous_infi_dom {t₁ : ι → tspace α} {t₂ : tspace β}
  (h : ∀i, cont (t₁ i) t₂ f) : cont (infi t₁) t₂ f :=
continuous_Inf_dom $ assume t ⟨i, (t_eq : t₁ i = t)⟩, t_eq ▸ h i

lemma continuous_infi_rng {t₁ : tspace α} {t₂ : ι → tspace β} {i : ι}
  (h : cont t₁ (t₂ i) f) : cont t₁ (infi t₂) f :=
continuous_Inf_rng ⟨i, rfl⟩ h

lemma continuous_sup_rng {t₁ : tspace α} {t₂ t₃ : tspace β}
  (h₁ : cont t₁ t₂ f) (h₂ : cont t₁ t₃ f) : cont t₁ (t₂ ⊔ t₃) f :=
continuous_iff_le_coinduced.2 $ sup_le
  (continuous_iff_le_coinduced.1 h₁)
  (continuous_iff_le_coinduced.1 h₂)

lemma continuous_sup_dom_left {t₁ t₂ : tspace α} {t₃ : tspace β} :
  cont t₁ t₃ f → cont (t₁ ⊔ t₂) t₃ f :=
continuous_le_dom le_sup_left

lemma continuous_sup_dom_right {t₁ t₂ : tspace α} {t₃ : tspace β} :
  cont t₂ t₃ f → cont (t₁ ⊔ t₂) t₃ f :=
continuous_le_dom le_sup_right

lemma continuous_Sup_dom {t₁ : set (tspace α)} {t₂ : tspace β} {t : tspace α} (h₁ : t ∈ t₁) :
  cont t t₂ f → cont (Sup t₁) t₂ f :=
continuous_le_dom $ le_Sup h₁

lemma continuous_Sup_rng {t₁ : tspace α} {t₂ : set (tspace β)}
  (h : ∀t∈t₂, cont t₁ t f) : cont t₁ (Sup t₂) f :=
continuous_iff_le_coinduced.2 $ Sup_le $ assume b hb, continuous_iff_le_coinduced.1 $ h b hb

lemma continuous_supr_dom {t₁ : ι → tspace α} {t₂ : tspace β} {i : ι} :
  cont (t₁ i) t₂ f → cont (supr t₁) t₂ f :=
continuous_le_dom $ le_supr _ _

lemma continuous_supr_rng {t₁ : tspace α} {t₂ : ι → tspace β}
  (h : ∀i, cont t₁ (t₂ i) f) : cont t₁ (supr t₂) f :=
continuous_iff_le_coinduced.2 $ supr_le $ assume i, continuous_iff_le_coinduced.1 $ h i

lemma continuous_top {t : tspace β} : cont ⊤ t f :=
continuous_iff_induced_le.2 $ le_top

lemma continuous_bot {t : tspace α} : cont t ⊥ f :=
continuous_iff_le_coinduced.2 $ bot_le
/- nhds in the induced topology -/

theorem mem_nhds_induced [T : topological_space α] (f : β → α) (a : β) (s : set β) :
  s ∈ @nhds β (topological_space.induced f T) a ↔ ∃ u ∈ nhds (f a), f ⁻¹' u ⊆ s :=
begin
  simp only [nhds_sets, is_open_induced_iff, exists_prop, set.mem_set_of_eq],
  split,
  { rintros ⟨u, usub, ⟨v, openv, ueq⟩, au⟩,
    exact ⟨v, ⟨v, set.subset.refl v, openv, by rwa ←ueq at au⟩, by rw ueq; exact usub⟩ },
  rintros ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩,
  exact ⟨f ⁻¹' v, set.subset.trans (set.preimage_mono vsubu) finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩
end

theorem nhds_induced [T : topological_space α] (f : β → α) (a : β) :
  @nhds β (topological_space.induced f T) a = comap f (nhds (f a)) :=
filter_eq $ by ext s; rw mem_nhds_induced; rw mem_comap_sets

theorem map_nhds_induced_of_surjective [T : topological_space α]
    {f : β → α} (hf : function.surjective f) (a : β) (s : set α) :
  map f (@nhds β (topological_space.induced f T) a) = nhds (f a) :=
by rw [nhds_induced, map_comap_of_surjective hf]

section topα

variable [topological_space α]

/-
The nhds filter and the subspace topology.
-/

theorem mem_nhds_subtype (s : set α) (a : {x // x ∈ s}) (t : set {x // x ∈ s}) :
  t ∈ nhds a ↔ ∃ u ∈ nhds a.val, (@subtype.val α s) ⁻¹' u ⊆ t :=
by rw mem_nhds_induced

theorem nhds_subtype (s : set α) (a : {x // x ∈ s}) :
  nhds a = comap subtype.val (nhds a.val) :=
by rw nhds_induced

theorem principal_subtype (s : set α) (t : set {x // x ∈ s}) :
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

variables [tspace β] [tspace γ]

theorem continuous_at_within_univ (f : α → β) (x : α) :
   continuous_at_within f x set.univ ↔ continuous_at f x :=
by rw [continuous_at, continuous_at_within, nhds_within_univ]

theorem continuous_at_within_iff_continuous_at_restrict (f : α → β) {x : α} {s : set α} (h : x ∈ s) :
  continuous_at_within f x s ↔ continuous_at (function.restrict f s) ⟨x, h⟩ :=
tendsto_nhds_within_iff_subtype h f _

theorem continuous_at_within.tendsto_nhds_within_image {f : α → β} {x : α} {s : set α}
  (h : continuous_at_within f x s) :
  tendsto f (nhds_within x s) (nhds_within (f x) (f '' s)) :=
tendsto_inf.2 ⟨h, tendsto_principal.2 $
  mem_inf_sets_of_right $ mem_principal_sets.2 $
  λ x, mem_image_of_mem _⟩

theorem continuous_on_iff {f : α → β} {s : set α} :
  continuous_on f s ↔ ∀ x ∈ s, ∀ t : set β, is_open t → f x ∈ t → ∃ u, is_open u ∧ x ∈ u ∧
    u ∩ s ⊆ f ⁻¹' t :=
by simp only [continuous_on, continuous_at_within, tendsto_nhds, mem_nhds_within]

theorem continuous_on_iff_continuous_restrict {f : α → β} {s : set α} :
  continuous_on f s ↔ continuous (function.restrict f s) :=
begin
  rw [continuous_on, continuous_iff_continuous_at], split,
  { rintros h ⟨x, xs⟩,
    exact (continuous_at_within_iff_continuous_at_restrict f xs).mp (h x xs) },
  intros h x xs,
  exact (continuous_at_within_iff_continuous_at_restrict f xs).mpr (h ⟨x, xs⟩)
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

theorem nhds_within_le_comap {x : α} {s : set α} {f : α → β} (ctsf : continuous_at_within f x s) :
  nhds_within x s ≤ comap f (nhds_within (f x) (f '' s)) :=
map_le_iff_le_comap.1 ctsf.tendsto_nhds_within_image

theorem continuous_at_within_iff_ptendsto_res (f : α → β) {x : α} {s : set α} (xs : x ∈ s) :
  continuous_at_within f x s ↔ ptendsto (pfun.res f s) (nhds x) (nhds (f x)) :=
tendsto_iff_ptendsto _ _ _ _

def continuous_iff_continuous_on_univ {f : α → β} : continuous f ↔ continuous_on f univ :=
by simp [continuous_iff_continuous_at, continuous_on, continuous_at, continuous_at_within,
         nhds_within_univ]

lemma continuous_at_within.mono {f : α → β} {s t : set α} {x : α} (h : continuous_at_within f x t)
  (hs : s ⊆ t) : continuous_at_within f x s :=
tendsto_le_left (nhds_within_mono x hs) h

lemma continuous_on.congr_mono {f g : α → β} {s s₁ : set α} (h : continuous_on f s)
  (h' : ∀x ∈ s₁, g x = f x) (h₁ : s₁ ⊆ s) : continuous_on g s₁ :=
begin
  assume x hx,
  unfold continuous_at_within,
  have A := (h x (h₁ hx)).mono h₁,
  unfold continuous_at_within at A,
  rw ← h' x hx at A,
  have : {x : α | g x = f x} ∈ nhds_within x s₁ := mem_inf_sets_of_right h',
  apply tendsto.congr' _ A,
  convert this,
  ext,
  finish
end

lemma continuous_at.continuous_at_within {f : α → β} {s : set α} {x : α} (h : continuous_at f x) :
  continuous_at_within f x s :=
continuous_at_within.mono ((continuous_at_within_univ f x).2 h) (subset_univ _)

lemma continuous_on.comp {f : α → β} {g : β → γ} {s : set α} {t : set β}
  (hf : continuous_on f s) (hg : continuous_on g t) (h : f '' s ⊆ t) :
  continuous_on (g ∘ f) s :=
begin
  assume x hx,
  have : tendsto f (principal s) (principal t),
    by { rw tendsto_principal_principal, exact λx hx, h (mem_image_of_mem _ hx) },
  have : tendsto f (nhds_within x s) (principal t) :=
    tendsto_le_left lattice.inf_le_right this,
  have : tendsto f (nhds_within x s) (nhds_within (f x) t) :=
    tendsto_inf.2 ⟨hf x hx, this⟩,
  exact tendsto.comp this (hg _ (h (mem_image_of_mem _ hx)))
end

lemma continuous_on.mono {f : α → β} {s t : set α} (hf : continuous_on f s) (h : t ⊆ s)  :
  continuous_on f t :=
λx hx, tendsto_le_left (nhds_within_mono _ h) (hf x (h hx))

lemma continuous.continuous_on {f : α → β} {s : set α} (h : continuous f) :
  continuous_on f s :=
begin
  rw continuous_iff_continuous_on_univ at h,
  exact h.mono (subset_univ _)
end

lemma continuous_on_const {s : set α} {c : β} : continuous_on (λx, c) s :=
begin
  apply continuous_on.mono _ (subset_univ _),
  rw ← continuous_iff_continuous_on_univ,
  exact continuous_const,
end

lemma continuous_on.preimage_open_of_open {f : α → β} {s : set α} {t : set β}
  (hf : continuous_on f s) (hs : is_open s) (ht : is_open t) : is_open (s ∩ f⁻¹' t) :=
begin
  rcases continuous_on_iff'.1 hf t ht with ⟨u, hu⟩,
  rw [inter_comm, hu.2],
  apply is_open_inter hu.1 hs
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
  rwa [continuous_at_within, ← nhds_within_restrict _ xt open_t] at this
end

end topα

end constructions

section induced
open topological_space
variables {α : Type*} {β : Type*}
variables [t : topological_space β] {f : α → β}

theorem is_open_induced_eq {s : set α} :
  @_root_.is_open _ (induced f t) s ↔ s ∈ preimage f '' {s | is_open s} :=
iff.refl _

theorem is_open_induced {s : set β} (h : is_open s) : (induced f t).is_open (f ⁻¹' s) :=
⟨s, h, rfl⟩

lemma nhds_induced_eq_comap {a : α} : @nhds α (induced f t) a = comap f (nhds (f a)) :=
calc @nhds α (induced f t) a = (⨅ s (x : s ∈ preimage f '' set_of is_open ∧ a ∈ s), principal s) :
    by simp [nhds, is_open_induced_eq, -mem_image, and_comm]
  ... = (⨅ s (x : is_open s ∧ f a ∈ s), principal (f ⁻¹' s)) :
    by simp only [infi_and, infi_image]; refl
  ... = _ : by simp [nhds, comap_infi, and_comm]

lemma map_nhds_induced_eq {a : α} (h : range f ∈ nhds (f a)) :
  map f (@nhds α (induced f t) a) = nhds (f a) :=
by rw [nhds_induced_eq_comap, filter.map_comap h]

lemma closure_induced [t : topological_space β] {f : α → β} {a : α} {s : set α}
  (hf : ∀x y, f x = f y → x = y) :
  a ∈ @closure α (topological_space.induced f t) s ↔ f a ∈ closure (f '' s) :=
have comap f (nhds (f a) ⊓ principal (f '' s)) ≠ ⊥ ↔ nhds (f a) ⊓ principal (f '' s) ≠ ⊥,
  from ⟨assume h₁ h₂, h₁ $ h₂.symm ▸ comap_bot,
    assume h,
    forall_sets_neq_empty_iff_neq_bot.mp $
      assume s₁ ⟨s₂, hs₂, (hs : f ⁻¹' s₂ ⊆ s₁)⟩,
      have f '' s ∈ nhds (f a) ⊓ principal (f '' s),
        from mem_inf_sets_of_right $ by simp [subset.refl],
      have s₂ ∩ f '' s ∈ nhds (f a) ⊓ principal (f '' s),
        from inter_mem_sets hs₂ this,
      let ⟨b, hb₁, ⟨a, ha, ha₂⟩⟩ := inhabited_of_mem_sets h this in
      ne_empty_of_mem $ hs $ by rwa [←ha₂] at hb₁⟩,
calc a ∈ @closure α (topological_space.induced f t) s
    ↔ (@nhds α (topological_space.induced f t) a) ⊓ principal s ≠ ⊥ : by rw [closure_eq_nhds]; refl
  ... ↔ comap f (nhds (f a)) ⊓ principal (f ⁻¹' (f '' s)) ≠ ⊥ : by rw [nhds_induced_eq_comap, preimage_image_eq _ hf]
  ... ↔ comap f (nhds (f a) ⊓ principal (f '' s)) ≠ ⊥ : by rw [comap_inf, ←comap_principal]
  ... ↔ _ : by rwa [closure_eq_nhds]

end induced
