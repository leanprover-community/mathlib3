/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Continuous functions.
-/
import topology.topological_space
open set filter lattice

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

theorem classical.cases {p : Prop → Prop} (h1 : p true) (h2 : p false) : ∀a, p a :=
assume a, classical.cases_on a h1 h2

lemma univ_eq_true_false : univ = ({true, false} : set Prop) :=
eq.symm $ top_unique $ classical.cases (by simp) (by simp)

@[simp]
lemma false_neq_true : false ≠ true :=
begin intro h, rw [h], trivial end

lemma subtype.val_image {p : α → Prop} {s : set (subtype p)} :
  subtype.val '' s = {x | ∃h : p x, (⟨x, h⟩ : subtype p) ∈ s} :=
set.ext $ assume a,
⟨assume ⟨⟨a', ha'⟩, in_s, (h_eq : a' = a)⟩, h_eq ▸ ⟨ha', in_s⟩,
  assume ⟨ha, in_s⟩, ⟨⟨a, ha⟩, in_s, rfl⟩⟩

section
variables [topological_space α] [topological_space β] [topological_space γ]

def continuous (f : α → β) := ∀s, open' s → open' (vimage f s)

lemma continuous_id : continuous (id : α → α) :=
assume s h, h

lemma continuous_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g):
  continuous (g ∘ f) :=
assume s h, hf _ (hg s h)

lemma continuous_iff_towards {f : α → β} :
  continuous f ↔ (∀x, towards f (nhds x) (nhds (f x))) :=
⟨assume hf : continuous f, assume x s,
  show s ∈ (nhds (f x))^.sets → s ∈ (map f (nhds x))^.sets,
    by simp [nhds_sets];
      exact assume ⟨t, t_open, t_subset, fx_in_t⟩,
        ⟨vimage f t, hf t t_open, fx_in_t, vimage_mono t_subset⟩,
  assume hf : ∀x, towards f (nhds x) (nhds (f x)),
  assume s, assume hs : open' s,
  have ∀a, f a ∈ s → s ∈ (nhds (f a))^.sets,
    by simp [nhds_sets]; exact assume a ha, ⟨s, hs, subset.refl s, ha⟩,
  show open' (vimage f s),
    by simp [open_iff_nhds]; exact assume a ha, hf a (this a ha)⟩

end

section constructions
local notation `cont` := @continuous _ _
local notation `tspace` := topological_space
open topological_space

variable {f : α → β}

lemma continuous_iff_induced_le {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f ↔ (induced f t₂ ≤ t₁) :=
⟨assume hc s ⟨t, ht, s_eq⟩, s_eq^.symm ▸ hc t ht,
  assume hle s h, hle _ ⟨_, h, rfl⟩⟩

lemma continuous_eq_le_coinduced {t₁ : tspace α} {t₂ : tspace β} :
  cont t₁ t₂ f = (t₂ ≤ coinduced f t₁) :=
rfl

lemma continuous_generated_from {t : tspace α} {b : set (set β)}
  (h : ∀s∈b, open' (vimage f s)) : cont t (generate_from b) f :=
assume s hs, generate_open.rec_on hs h
  open_univ
  (assume s t _ _, open_inter)
  (assume t _ h, by rw [vimage_sUnion]; exact (open_Union $ assume s, open_Union $ assume hs, h s hs))

lemma continuous_induced_dom {t : tspace β} : cont (induced f t) t f :=
assume s h, ⟨_, h, rfl⟩

lemma continuous_induced_rng {g : γ → α} {t₂ : tspace β} {t₁ : tspace γ}
  (h : cont t₁ t₂ (f ∘ g)) : cont t₁ (induced f t₂) g :=
assume s ⟨t, ht, s_eq⟩, s_eq^.symm ▸ h t ht

lemma continuous_coinduced_rng {t : tspace α} : cont t (coinduced f t) f :=
assume s h, h

lemma continuous_coinduced_dom {g : β → γ} {t₁ : tspace α} {t₂ : tspace γ}
  (h : cont t₁ t₂ (g ∘ f)) : cont (coinduced f t₁) t₂ g :=
assume s hs, h s hs

lemma continuous_inf_dom {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h₁ : cont t₁ t₃ f) (h₂ : cont t₂ t₃ f) : cont (t₁ ⊓ t₂) t₃ f :=
assume s h, ⟨h₁ s h, h₂ s h⟩

lemma continuous_inf_rng_left {t₁ : tspace α} {t₃ t₂ : tspace β}
  (h : cont t₁ t₂ f) : cont t₁ (t₂ ⊓ t₃) f :=
assume s hs, h s hs^.left

lemma continuous_inf_rng_right {t₁ : tspace α} {t₃ t₂ : tspace β}
  (h : cont t₁ t₃ f) : cont t₁ (t₂ ⊓ t₃) f :=
assume s hs, h s hs^.right

lemma continuous_Inf_dom {t₁ : set (tspace α)} {t₂ : tspace β}
  (h : ∀t∈t₁, cont t t₂ f) : cont (Inf t₁) t₂ f :=
assume s hs t ht, h t ht s hs

lemma continuous_Inf_rng {t₁ : tspace α} {t₂ : set (tspace β)}
  {t : tspace β} (h₁ : t ∈ t₂) (hf : cont t₁ t f) : cont t₁ (Inf t₂) f :=
assume s hs, hf s $ hs t h₁

lemma continuous_infi_dom {t₁ : ι → tspace α} {t₂ : tspace β}
  (h : ∀i, cont (t₁ i) t₂ f) : cont (infi t₁) t₂ f :=
continuous_Inf_dom $ assume t ⟨i, (t_eq : t = t₁ i)⟩, t_eq^.symm ▸ h i

lemma continuous_infi_rng {t₁ : tspace α} {t₂ : ι → tspace β}
  {i : ι} (h : cont t₁ (t₂ i) f) : cont t₁ (infi t₂) f :=
continuous_Inf_rng ⟨i, rfl⟩ h

lemma continuous_top {t : tspace β} : cont ⊤ t f :=
assume s h, trivial

lemma continuous_bot {t : tspace α} : cont t ⊥ f :=
continuous_Inf_rng (mem_univ $ coinduced f t) continuous_coinduced_rng

lemma continuous_sup_rng {t₁ : tspace α} {t₂ t₃ : tspace β}
  (h₁ : cont t₁ t₂ f) (h₂ : cont t₁ t₃ f) : cont t₁ (t₂ ⊔ t₃) f :=
continuous_Inf_rng
  (show t₂ ≤ coinduced f t₁ ∧ t₃ ≤ coinduced f t₁, from ⟨h₁, h₂⟩)
  continuous_coinduced_rng

lemma continuous_sup_dom_left {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h : cont t₁ t₃ f) : cont (t₁ ⊔ t₂) t₃ f :=
continuous_Inf_dom $ assume t ⟨h₁, h₂⟩ s hs, h₁ _ $ h s hs

lemma continuous_sup_dom_right {t₁ t₂ : tspace α} {t₃ : tspace β}
  (h : cont t₂ t₃ f) : cont (t₁ ⊔ t₂) t₃ f :=
continuous_Inf_dom $ assume t ⟨h₁, h₂⟩ s hs, h₂ _ $ h s hs

end constructions

section sierpinski
variables [topological_space α]

@[simp]
lemma open_singleton_true : open' ({true} : set Prop) :=
topological_space.generate_open.basic _ (by simp)

lemma continuous_Prop {p : α → Prop} : continuous p ↔ open' {x | p x} :=
⟨assume h : continuous p,
  have open' (vimage p {true}),
    from h _ open_singleton_true,
  by simp [vimage, eq_true] at this; assumption,
  assume h : open' {x | p x},
  continuous_generated_from $ assume s (hs : s ∈ {{true}}),
    by simp at hs; simp [hs, vimage, eq_true, h]⟩

end sierpinski

section induced
open topological_space
variables [t : topological_space β] {f : α → β}

lemma open_induced {s : set β} (h : open' s) : (induced f t).open' (vimage f s) :=
⟨s, h, rfl⟩

lemma nhds_induced_eq_vmap {a : α} : @nhds α (induced f t) a = vmap f (nhds (f a)) :=
le_antisymm
  (assume s ⟨s', hs', (h_s : vimage f s' ⊆ s)⟩,
    have ∃t':set β, open' t' ∧ t' ⊆ s' ∧ f a ∈ t',
      by simp [mem_nhds_sets_iff] at hs'; assumption,
    let ⟨t', ht', hsub, hin⟩ := this in
    (@nhds α (induced f t) a).upwards_sets
      begin
        simp [mem_nhds_sets_iff],
        exact ⟨vimage f t', open_induced ht', hin, vimage_mono hsub⟩
      end
      h_s)
  (le_infi $ assume s, le_infi $ assume ⟨as, ⟨s', open_s', s_eq⟩⟩,
    begin
      simp [vmap, mem_nhds_sets_iff, s_eq],
      exact ⟨s', subset.refl _, s', open_s', subset.refl _, by rw [s_eq] at as; assumption⟩
    end)

lemma map_nhds_induced_eq {a : α} (h : image f univ ∈ (nhds (f a))^.sets) :
  map f (@nhds α (induced f t) a) = nhds (f a) :=
le_antisymm
  ((@continuous_iff_towards α β (induced f t) _ _)^.mp continuous_induced_dom a)
  (assume s, assume hs : vimage f s ∈ (@nhds α (induced f t) a)^.sets,
    let ⟨t', t_subset, open_t, a_in_t⟩ := mem_nhds_sets_iff^.mp h in
    let ⟨s', s'_subset, ⟨s'', open_s'', s'_eq⟩, a_in_s'⟩ := (@mem_nhds_sets_iff _ (induced f t) _ _)^.mp hs in
    by subst s'_eq; exact (mem_nhds_sets_iff^.mpr $
      ⟨t' ∩ s'',
        assume x ⟨h₁, h₂⟩, match x, h₂, t_subset h₁ with
        | x, h₂, ⟨y, _, y_eq⟩ := begin subst y_eq, exact s'_subset h₂ end
        end,
        open_inter open_t open_s'',
        ⟨a_in_t, a_in_s'⟩⟩))

end induced

section prod
open topological_space
variables [topological_space α] [topological_space β] [topological_space γ]

lemma continuous_fst : continuous (@prod.fst α β) :=
continuous_sup_dom_left continuous_induced_dom

lemma continuous_snd : continuous (@prod.snd α β) :=
continuous_sup_dom_right continuous_induced_dom

lemma continuous_prod_mk {f : γ → α} {g : γ → β}
  (hf : continuous f) (hg : continuous g) : continuous (λx, prod.mk (f x) (g x)) :=
continuous_sup_rng (continuous_induced_rng hf) (continuous_induced_rng hg)

lemma open_set_prod {s : set α} {t : set β} (hs : open' s) (ht: open' t) :
  open' (set.prod s t) :=
open_inter (continuous_fst s hs) (continuous_snd t ht)

lemma prod_eq_generate_from [tα : topological_space α] [tβ : topological_space β] :
  prod.topological_space =
  generate_from {g | ∃(s:set α) (t:set β), open' s ∧ open' t ∧ g = set.prod s t} :=
le_antisymm
  (sup_le
    (assume s ⟨t, ht, s_eq⟩,
      have set.prod t univ = s, by simp [s_eq, vimage, set.prod],
      this ▸ (generate_open.basic _ ⟨t, univ, ht, open_univ, rfl⟩))
    (assume s ⟨t, ht, s_eq⟩,
      have set.prod univ t = s, by simp [s_eq, vimage, set.prod],
      this ▸ (generate_open.basic _ ⟨univ, t, open_univ, ht, rfl⟩)))
  (generate_from_le $ assume g ⟨s, t, hs, ht, g_eq⟩, g_eq.symm ▸ open_set_prod hs ht)

lemma nhds_prod_eq {a : α} {b : β} : nhds (a, b) = filter.prod (nhds a) (nhds b) :=
by rw [prod_eq_generate_from, nhds_generate_from];
  exact le_antisymm
    (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
      begin
        simp [mem_nhds_sets_iff] at hs, simp [mem_nhds_sets_iff] at ht,
        revert hs ht,
        exact (assume ⟨s', hs', hs_sub, as'⟩ ⟨t', ht', ht_sub, at'⟩,
          infi_le_of_le (set.prod s' t') $
          infi_le_of_le ⟨⟨as', at'⟩, s', t', hs', ht', rfl⟩ $
          principal_mono.mpr $ set.prod_mono hs_sub ht_sub)
      end)
    (le_infi $ assume s, le_infi $ assume ⟨hab, s', t', hs', ht', s_eq⟩,
      begin
        revert hab,
        simp [s_eq],
        exact assume ⟨ha, hb⟩, @prod_mem_prod α β s' t' (nhds a) (nhds b)
          (mem_nhds_sets_iff.mpr ⟨s', subset.refl s', hs', ha⟩)
          (mem_nhds_sets_iff.mpr ⟨t', subset.refl t', ht', hb⟩)
      end)

lemma closure_prod_eq {s : set α} {t : set β} :
  closure (set.prod s t) = set.prod (closure s) (closure t) :=
set.ext $ assume ⟨a, b⟩,
have filter.prod (nhds a) (nhds b) ⊓ principal (set.prod s t) =
  filter.prod (nhds a ⊓ principal s) (nhds b ⊓ principal t),
  by rw [←prod_inf_prod, prod_principal_principal],
by simp [closure_eq_nhds, nhds_prod_eq, this]; exact prod_neq_bot

end prod

section sum
variables [topological_space α] [topological_space β] [topological_space γ]

lemma continuous_inl : continuous (@sum.inl α β) :=
continuous_inf_rng_left continuous_coinduced_rng

lemma continuous_inr : continuous (@sum.inr α β) :=
continuous_inf_rng_right continuous_coinduced_rng

lemma continuous_sum_rec {f : α → γ} {g : β → γ}
  (hf : continuous f) (hg : continuous g) : @continuous (α ⊕ β) γ _ _ (@sum.rec α β (λ_, γ) f g) :=
continuous_inf_dom hf hg

end sum

section subtype
variables [topological_space α] [topological_space β] {p : α → Prop}

lemma continuous_subtype_val : continuous (@subtype.val α p) :=
continuous_induced_dom

lemma continuous_subtype_mk {f : β → α}
  (hp : ∀x, p (f x)) (h : continuous f) : continuous (λx, (⟨f x, hp x⟩ : subtype p)) :=
continuous_induced_rng h

lemma map_nhds_subtype_val_eq {a : α} {ha : p a} (h : {a | p a} ∈ (nhds a)^.sets) :
  map (@subtype.val α p) (nhds ⟨a, ha⟩) = nhds a :=
map_nhds_induced_eq (by simp [subtype.val_image, h])

lemma continuous_subtype_nhds_cover {f : α → β} {c : ι → α → Prop}
  (c_cover : ∀x, ∃i, c i x ∧ {x | c i x} ∈ (nhds x)^.sets)
  (f_cont  : ∀i, continuous (λ(x : subtype (c i)), f x.val)) :
  continuous f :=
continuous_iff_towards^.mpr $ assume x,
  let ⟨i, (hi : c i x), (c_sets : {x | c i x} ∈ (nhds x)^.sets)⟩ := c_cover x in
  calc map f (nhds x) = map f (map (@subtype.val α (c i)) (nhds ⟨x, hi⟩)) :
      congr_arg (map f) (map_nhds_subtype_val_eq $ c_sets)^.symm
    ... = map (λ(x : subtype (c i)), f x.val) (nhds ⟨x, hi⟩) : rfl
    ... ≤ (nhds (f x)) : continuous_iff_towards^.mp (f_cont i) ⟨x, hi⟩

end subtype

section pi

lemma nhds_pi {ι : Type u} {α : ι → Type v} [t : ∀i, topological_space (α i)] {a : Πi, α i} :
  nhds a = (⨅i, vmap (λx, x i) (nhds (a i))) :=
calc nhds a = (⨅i, @nhds _ (@topological_space.induced _ _ (λx:Πi, α i, x i) (t i)) a) : nhds_supr
  ... = (⨅i, vmap (λx, x i) (nhds (a i))) : by simp [nhds_induced_eq_vmap]

/-- Tychonoff's theorem -/
lemma compact_pi_infinite {ι : Type v} {α : ι → Type u} [∀i:ι, topological_space (α i)]
  {s : Πi:ι, set (α i)} : (∀i, compact (s i)) → compact {x : Πi:ι, α i | ∀i, x i ∈ s i} :=
begin
  simp [compact_iff_ultrafilter_le_nhds, nhds_pi],
  exact assume h f hf hfs,
    let p : Πi:ι, filter (α i) := λi, map (λx:Πi:ι, α i, x i) f in
    have ∀i:ι, ∃a, a∈s i ∧ p i ≤ nhds a,
      from assume i, h i (p i) (ultrafilter_map hf) $
      show vimage (λx:Πi:ι, α i, x i) (s i) ∈ f.sets,
        from f.upwards_sets hfs $ assume x (hx : ∀i, x i ∈ s i), hx i,
    let ⟨a, ha⟩ := classical.axiom_of_choice this in
    ⟨a, assume i, (ha i).left, le_infi $ assume i, le_vmap_iff_map_le.mpr $ (ha i).right⟩
end

end pi
