/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot

Hausdorff properties of uniform spaces. Separation quotient.
-/
import topology.uniform_space.basic


open filter topological_space lattice set classical
local attribute [instance, priority 0] prop_decidable
noncomputable theory
set_option eqn_compiler.zeta true

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
variables [uniform_space α] [uniform_space β] [uniform_space γ]


/- separated uniformity -/

/-- The separation relation is the intersection of all entourages.
  Two points which are related by the separation relation are "indistinguishable"
  according to the uniform structure. -/
protected def separation_rel (α : Type u) [u : uniform_space α] :=
⋂₀ (@uniformity α _).sets

lemma separated_equiv : equivalence (λx y, (x, y) ∈ separation_rel α) :=
⟨assume x, assume s, refl_mem_uniformity,
  assume x y, assume h (s : set (α×α)) hs,
    have preimage prod.swap s ∈ (@uniformity α _).sets,
      from symm_le_uniformity hs,
    h _ this,
  assume x y z (hxy : (x, y) ∈ separation_rel α) (hyz : (y, z) ∈ separation_rel α)
      s (hs : s ∈ (@uniformity α _).sets),
    let ⟨t, ht, (h_ts : comp_rel t t ⊆ s)⟩ := comp_mem_uniformity_sets hs in
    h_ts $ show (x, z) ∈ comp_rel t t,
      from ⟨y, hxy t ht, hyz t ht⟩⟩

@[class] def separated (α : Type u) [uniform_space α] :=
separation_rel α = id_rel

theorem separated_def {α : Type u} [uniform_space α] :
  separated α ↔ ∀ x y, (∀ r ∈ (@uniformity α _).sets, (x, y) ∈ r) → x = y :=
by simp [separated, id_rel_subset.2 separated_equiv.1, subset.antisymm_iff];
   simp [subset_def, separation_rel]

theorem separated_def' {α : Type u} [uniform_space α] :
  separated α ↔ ∀ x y, x ≠ y → ∃ r ∈ (@uniformity α _).sets, (x, y) ∉ r :=
separated_def.trans $ forall_congr $ λ x, forall_congr $ λ y,
by rw ← not_imp_not; simp [classical.not_forall]

instance separated_t2 [s : separated α] : t2_space α :=
⟨assume x y, assume h : x ≠ y,
let ⟨d, hd, (hxy : (x, y) ∉ d)⟩ := separated_def'.1 s x y h in
let ⟨d', hd', (hd'd' : comp_rel d' d' ⊆ d)⟩ := comp_mem_uniformity_sets hd in
have {y | (x, y) ∈ d'} ∈ (nhds x).sets,
  from mem_nhds_left x hd',
let ⟨u, hu₁, hu₂, hu₃⟩ := mem_nhds_sets_iff.mp this in
have {x | (x, y) ∈ d'} ∈ (nhds y).sets,
  from mem_nhds_right y hd',
let ⟨v, hv₁, hv₂, hv₃⟩ := mem_nhds_sets_iff.mp this in
have u ∩ v = ∅, from
  eq_empty_of_subset_empty $
  assume z ⟨(h₁ : z ∈ u), (h₂ : z ∈ v)⟩,
  have (x, y) ∈ comp_rel d' d', from ⟨z, hu₁ h₁, hv₁ h₂⟩,
  hxy $ hd'd' this,
⟨u, v, hu₂, hv₂, hu₃, hv₃, this⟩⟩

instance separated_regular [separated α] : regular_space α :=
{ regular := λs a hs ha,
    have -s ∈ (nhds a).sets,
      from mem_nhds_sets hs ha,
    have {p : α × α | p.1 = a → p.2 ∈ -s} ∈ uniformity.sets,
      from mem_nhds_uniformity_iff.mp this,
    let ⟨d, hd, h⟩ := comp_mem_uniformity_sets this in
    let e := {y:α| (a, y) ∈ d} in
    have hae : a ∈ closure e, from subset_closure $ refl_mem_uniformity hd,
    have set.prod (closure e) (closure e) ⊆ comp_rel d (comp_rel (set.prod e e) d),
    begin
      rw [←closure_prod_eq, closure_eq_inter_uniformity],
      change (⨅d' ∈ uniformity.sets, _) ≤ comp_rel d (comp_rel _ d),
      exact (infi_le_of_le d $ infi_le_of_le hd $ le_refl _)
    end,
    have e_subset : closure e ⊆ -s,
      from assume a' ha',
        let ⟨x, (hx : (a, x) ∈ d), y, ⟨hx₁, hx₂⟩, (hy : (y, _) ∈ d)⟩ := @this ⟨a, a'⟩ ⟨hae, ha'⟩ in
        have (a, a') ∈ comp_rel d d, from ⟨y, hx₂, hy⟩,
        h this rfl,
    have closure e ∈ (nhds a).sets, from (nhds a).sets_of_superset (mem_nhds_left a hd) subset_closure,
    have nhds a ⊓ principal (-closure e) = ⊥,
      from (@inf_eq_bot_iff_le_compl _ _ _ (principal (- closure e)) (principal (closure e))
        (by simp [principal_univ, union_comm]) (by simp)).mpr (by simp [this]),
    ⟨- closure e, is_closed_closure, assume x h₁ h₂, @e_subset x h₂ h₁, this⟩,
  ..separated_t2 }

/- separation space -/
namespace uniform_space
def separation_setoid (α : Type u) [uniform_space α] : setoid α :=
⟨λx y, (x, y) ∈ separation_rel α, separated_equiv⟩

local attribute [instance] separation_setoid

instance {α : Type u} [u : uniform_space α] : uniform_space (quotient (separation_setoid α)) :=
{ to_topological_space := u.to_topological_space.coinduced (λx, ⟦x⟧),
  uniformity := map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) uniformity,
  refl := le_trans (by simp [quotient.exists_rep]) (filter.map_mono refl_le_uniformity),
  symm := tendsto_map' $
    by simp [prod.swap, (∘)]; exact tendsto_swap_uniformity.comp tendsto_map,
  comp := calc (map (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) uniformity).lift' (λs, comp_rel s s) =
          uniformity.lift' ((λs, comp_rel s s) ∘ image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧))) :
      map_lift'_eq2 $ monotone_comp_rel monotone_id monotone_id
    ... ≤ uniformity.lift' (image (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ∘ (λs:set (α×α), comp_rel s (comp_rel s s))) :
      lift'_mono' $ assume s hs ⟨a, b⟩ ⟨c, ⟨⟨a₁, a₂⟩, ha, a_eq⟩, ⟨⟨b₁, b₂⟩, hb, b_eq⟩⟩,
      begin
        simp at a_eq,
        simp at b_eq,
        have h : ⟦a₂⟧ = ⟦b₁⟧, { rw [a_eq.right, b_eq.left] },
        have h : (a₂, b₁) ∈ separation_rel α := quotient.exact h,
        simp [function.comp, set.image, comp_rel, and.comm, and.left_comm, and.assoc],
        exact ⟨a₁, a_eq.left, b₂, b_eq.right, a₂, ha, b₁, h s hs, hb⟩
      end
    ... = map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) (uniformity.lift' (λs:set (α×α), comp_rel s (comp_rel s s))) :
      by rw [map_lift'_eq];
        exact monotone_comp_rel monotone_id (monotone_comp_rel monotone_id monotone_id)
    ... ≤ map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) uniformity :
      map_mono comp_le_uniformity3,
  is_open_uniformity := assume s,
    have ∀a, ⟦a⟧ ∈ s →
        ({p:α×α | p.1 = a → ⟦p.2⟧ ∈ s} ∈ (@uniformity α _).sets ↔
          {p:α×α | p.1 ≈ a → ⟦p.2⟧ ∈ s} ∈ (@uniformity α _).sets),
      from assume a ha,
      ⟨assume h,
        let ⟨t, ht, hts⟩ := comp_mem_uniformity_sets h in
        have hts : ∀{a₁ a₂}, (a, a₁) ∈ t → (a₁, a₂) ∈ t → ⟦a₂⟧ ∈ s,
          from assume a₁ a₂ ha₁ ha₂, @hts (a, a₂) ⟨a₁, ha₁, ha₂⟩ rfl,
        have ht' : ∀{a₁ a₂}, a₁ ≈ a₂ → (a₁, a₂) ∈ t,
          from assume a₁ a₂ h, sInter_subset_of_mem ht h,
        uniformity.sets_of_superset ht $ assume ⟨a₁, a₂⟩ h₁ h₂, hts (ht' $ setoid.symm h₂) h₁,
        assume h, uniformity.sets_of_superset h $ by simp {contextual := tt}⟩,
    begin
      simp [topological_space.coinduced, u.is_open_uniformity, uniformity, forall_quotient_iff],
      exact ⟨λh a ha, (this a ha).mp $ h a ha, λh a ha, (this a ha).mpr $ h a ha⟩
    end }

lemma uniformity_quotient :
  @uniformity (quotient (separation_setoid α)) _ = uniformity.map (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧)) :=
rfl

lemma uniform_continuous_quotient_mk :
  uniform_continuous (quotient.mk : α → quotient (separation_setoid α)) :=
le_refl _

lemma uniform_continuous_quotient {f : quotient (separation_setoid α) → β}
  (hf : uniform_continuous (λx, f ⟦x⟧)) : uniform_continuous f :=
hf

lemma uniform_continuous_quotient_lift
  {f : α → β} {h : ∀a b, (a, b) ∈ separation_rel α → f a = f b}
  (hf : uniform_continuous f) : uniform_continuous (λa, quotient.lift f h a) :=
uniform_continuous_quotient hf

lemma uniform_continuous_quotient_lift₂ [uniform_space γ]
  {f : α → β → γ} {h : ∀a c b d, (a, b) ∈ separation_rel α → (c, d) ∈ separation_rel β → f a c = f b d}
  (hf : uniform_continuous (λp:α×β, f p.1 p.2)) :
  uniform_continuous (λp:_×_, quotient.lift₂ f h p.1 p.2) :=
begin
  rw [uniform_continuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient,
    filter.prod_map_map_eq, filter.tendsto_map'_iff, filter.tendsto_map'_iff],
  rwa [uniform_continuous, uniformity_prod_eq_prod, filter.tendsto_map'_iff] at hf
end

lemma comap_quotient_le_uniformity :
  uniformity.comap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) ≤ uniformity :=
assume t' ht',
let ⟨t, ht, tt_t'⟩ := comp_mem_uniformity_sets ht' in
let ⟨s, hs, ss_t⟩ := comp_mem_uniformity_sets ht in
⟨(λp:α×α, (⟦p.1⟧, ⟦p.2⟧)) '' s,
  (@uniformity α _).sets_of_superset hs $ assume x hx, ⟨x, hx, rfl⟩,
  assume ⟨a₁, a₂⟩ ⟨⟨b₁, b₂⟩, hb, ab_eq⟩,
  have ⟦b₁⟧ = ⟦a₁⟧ ∧ ⟦b₂⟧ = ⟦a₂⟧, from prod.mk.inj ab_eq,
  have b₁ ≈ a₁ ∧ b₂ ≈ a₂, from and.imp quotient.exact quotient.exact this,
  have ab₁ : (a₁, b₁) ∈ t, from (setoid.symm this.left) t ht,
  have ba₂ : (b₂, a₂) ∈ s, from this.right s hs,
  tt_t' ⟨b₁, show ((a₁, a₂).1, b₁) ∈ t, from ab₁,
    ss_t ⟨b₂, show ((b₁, a₂).1, b₂) ∈ s, from hb, ba₂⟩⟩⟩

lemma comap_quotient_eq_uniformity :
  uniformity.comap (λ (p : α × α), (⟦p.fst⟧, ⟦p.snd⟧)) = uniformity :=
le_antisymm comap_quotient_le_uniformity le_comap_map


instance separated_separation : separated (quotient (separation_setoid α)) :=
set.ext $ assume ⟨a, b⟩, quotient.induction_on₂ a b $ assume a b,
  ⟨assume h,
    have a ≈ b, from assume s hs,
      have s ∈ (uniformity.comap (λp:(α×α), (⟦p.1⟧, ⟦p.2⟧))).sets,
        from comap_quotient_le_uniformity hs,
      let ⟨t, ht, hts⟩ := this in
      hts begin dsimp, exact h t ht end,
    show ⟦a⟧ = ⟦b⟧, from quotient.sound this,

  assume heq : ⟦a⟧ = ⟦b⟧, assume h hs,
  heq ▸ refl_mem_uniformity hs⟩

lemma separated_of_uniform_continuous {f : α → β} {x y : α}
  (H : uniform_continuous f) (h : x ≈ y) : f x ≈ f y :=
assume _ h', h _ (H h')

lemma eq_of_separated_of_uniform_continuous [separated β] {f : α → β} {x y : α}
  (H : uniform_continuous f) (h : x ≈ y) : f x = f y :=
separated_def.1 (by apply_instance) _ _ $ separated_of_uniform_continuous H h

def separation_quotient (α : Type*) [uniform_space α] := quotient (separation_setoid α)

namespace separation_quotient
instance : uniform_space (separation_quotient α) := by dunfold separation_quotient ; apply_instance
instance : separated (separation_quotient α) := by dunfold separation_quotient ; apply_instance

def lift [separated β] (f : α → β) : (separation_quotient α → β) :=
if h : uniform_continuous f then
  quotient.lift f (λ x y, eq_of_separated_of_uniform_continuous h)
else
  λ x, f (classical.inhabited_of_nonempty $ (nonempty_quotient_iff $ separation_setoid α).1 ⟨x⟩).default

lemma lift_mk [separated β] {f : α → β} (h : uniform_continuous f) (a : α) : lift f ⟦a⟧ = f a :=
by rw [lift, dif_pos h]; refl

lemma uniform_continuous_lift [separated β] (f : α → β) : uniform_continuous (lift f) :=
begin
  by_cases hf : uniform_continuous f,
  { rw [lift, dif_pos hf], exact uniform_continuous_quotient_lift hf },
  { rw [lift, dif_neg hf], exact uniform_continuous_of_const (assume a b, rfl) }
end

def map (f : α → β) : separation_quotient α → separation_quotient β :=
lift (quotient.mk ∘ f)

lemma map_mk {f : α → β} (h : uniform_continuous f) (a : α) : map f ⟦a⟧ = ⟦f a⟧ :=
by rw [map, lift_mk (h.comp uniform_continuous_quotient_mk)]

lemma uniform_continuous_map (f : α → β): uniform_continuous (map f) :=
uniform_continuous_lift (quotient.mk ∘ f)

lemma map_unique {f : α → β} (hf : uniform_continuous f)
  {g : separation_quotient α → separation_quotient β}
  (comm : quotient.mk ∘ f = g ∘ quotient.mk) : map f = g :=
by ext ⟨a⟩;
calc map f ⟦a⟧ = ⟦f a⟧ : map_mk hf a
  ... = g ⟦a⟧ : congr_fun comm a

lemma map_id : map (@id α) = id :=
map_unique uniform_continuous_id rfl

lemma map_comp {f : α → β} {g : β → γ} (hf : uniform_continuous f) (hg : uniform_continuous g) :
  map g ∘ map f = map (g ∘ f) :=
(map_unique (hf.comp hg) $ by simp only [(∘), map_mk, hf, hg]).symm

end separation_quotient

lemma separation_prod {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ :=
begin
  split,
  { assume h,
    exact ⟨separated_of_uniform_continuous uniform_continuous_fst h,
           separated_of_uniform_continuous uniform_continuous_snd h⟩ },
  { rintros ⟨eqv_α, eqv_β⟩ r r_in,
    rw uniformity_prod at r_in,
    rcases r_in with ⟨t_α, ⟨r_α, r_α_in, h_α⟩, t_β, ⟨r_β, r_β_in, h_β⟩, H⟩,

    let p_α := λ(p : (α × β) × (α × β)), (p.1.1, p.2.1),
    let p_β := λ(p : (α × β) × (α × β)), (p.1.2, p.2.2),
    have key_α : p_α ((a₁, b₁), (a₂, b₂)) ∈ r_α, { simp [p_α, eqv_α r_α r_α_in] },
    have key_β : p_β ((a₁, b₁), (a₂, b₂)) ∈ r_β, { simp [p_β, eqv_β r_β r_β_in] },
    exact H ⟨h_α key_α, h_β key_β⟩ },
end

instance separated.prod [separated α] [separated β] : separated (α × β) :=
separated_def.2 $ assume x y H, prod.ext
  (eq_of_separated_of_uniform_continuous uniform_continuous_fst H)
  (eq_of_separated_of_uniform_continuous uniform_continuous_snd H)
end uniform_space
