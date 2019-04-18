/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Linear structures on function with finite support `α →₀ β`.
-/
import data.finsupp linear_algebra.basic
noncomputable theory

local attribute [instance, priority 0] classical.prop_decidable

open lattice set linear_map submodule

namespace finsupp

variables {α : Type*} {β : Type*} {γ : Type*}
variables [decidable_eq α] [decidable_eq β] [ring γ] [add_comm_group β] [module γ β]

local attribute [instance] finsupp.to_module

def lsingle (a : α) : β →ₗ[γ] (α →₀ β) :=
⟨single a, assume a b, single_add, assume c b, (smul_single _ _ _).symm⟩

def lapply (a : α) : (α →₀ β) →ₗ[γ] β := ⟨λg, g a, assume a b, rfl, assume a b, rfl⟩

section lsubtype_domain
variables (s : set α) [decidable_pred (λx, x ∈ s)]

def lsubtype_domain : (α →₀ β) →ₗ[γ] (s →₀ β) :=
⟨subtype_domain (λx, x ∈ s), assume a b, subtype_domain_add, assume c a, ext $ assume a, rfl⟩

lemma lsubtype_domain_apply (f : α →₀ β) :
  (lsubtype_domain s : (α →₀ β) →ₗ[γ] (s →₀ β)) f = subtype_domain (λx, x ∈ s) f := rfl

end lsubtype_domain

@[simp] lemma lsingle_apply (a : α) (b : β) : (lsingle a : β →ₗ[γ] (α →₀ β)) b = single a b  :=
rfl

@[simp] lemma lapply_apply (a : α) (f : α →₀ β) : (lapply a : (α →₀ β) →ₗ[γ] β) f = f a  :=
rfl

@[simp] lemma ker_lsingle (a : α) : (lsingle a : β →ₗ[γ] (α →₀ β)).ker = ⊥ :=
ker_eq_bot.2 (injective_single a)

lemma lsingle_range_le_ker_lapply (s t : set α) (h : disjoint s t) :
  (⨆a∈s, (lsingle a : β →ₗ[γ] (α →₀ β)).range) ≤ (⨅a∈t, ker (lapply a)) :=
begin
  refine supr_le (assume a₁, supr_le $ assume h₁, range_le_iff_comap.2 _),
  simp only [(ker_comp _ _).symm, eq_top_iff, le_def', mem_ker, comap_infi, mem_infi],
  assume b hb a₂ h₂,
  have : a₁ ≠ a₂ := assume eq, h ⟨h₁, eq.symm ▸ h₂⟩,
  exact single_eq_of_ne this
end

lemma infi_ker_lapply_le_bot : (⨅a, ker (lapply a : (α →₀ β) →ₗ[γ] β)) ≤ ⊥ :=
begin
  simp only [le_def', mem_infi, mem_ker, mem_bot, lapply_apply],
  exact assume a h, finsupp.ext h
end

lemma supr_lsingle_range : (⨆a, (lsingle a : β →ₗ[γ] (α →₀ β)).range) = ⊤ :=
begin
  refine (eq_top_iff.2 $ le_def'.2 $ assume f _, _),
  rw [← sum_single f],
  refine sum_mem _ (assume a ha, submodule.mem_supr_of_mem _ a $ set.mem_image_of_mem _ trivial)
end

lemma disjoint_lsingle_lsingle (s t : set α) (hs : disjoint s t) :
  disjoint (⨆a∈s, (lsingle a : β →ₗ[γ] (α →₀ β)).range) (⨆a∈t, (lsingle a).range) :=
begin
  refine disjoint_mono
    (lsingle_range_le_ker_lapply _ _ $ disjoint_compl s)
    (lsingle_range_le_ker_lapply _ _ $ disjoint_compl t)
    (le_trans (le_infi $ assume i, _) infi_ker_lapply_le_bot),
  classical,
  by_cases his : i ∈ s,
  { by_cases hit : i ∈ t,
    { exact (hs ⟨his, hit⟩).elim },
    exact inf_le_right_of_le (infi_le_of_le i $ infi_le _ hit) },
  exact inf_le_left_of_le (infi_le_of_le i $ infi_le _ his)
end

lemma span_single_image (s : set β) (a : α) :
  submodule.span γ (single a '' s) = (submodule.span γ s).map (lsingle a) :=
by rw ← span_image; refl

variables (β γ)

def supported (s : set α) : submodule γ (α →₀ β) :=
begin
  refine ⟨ {p | ↑p.support ⊆ s }, _, _, _ ⟩,
  { simp only [subset_def, finset.mem_coe, set.mem_set_of_eq, mem_support_iff, zero_apply],
    assume h ha, exact (ha rfl).elim },
  { assume p q hp hq,
    refine subset.trans
      (subset.trans (finset.coe_subset.2 support_add) _) (union_subset hp hq),
    rw [finset.coe_union] },
  { assume a p hp,
    refine subset.trans (finset.coe_subset.2 support_smul) hp }
end

variables {β}

lemma mem_supported {s : set α} (p : α →₀ β) : p ∈ (supported β γ s) ↔ ↑p.support ⊆ s :=
iff.rfl

lemma mem_supported' {s : set α} (p : α →₀ β) :
  p ∈ supported β γ s ↔ ∀ x ∉ s, p x = 0 :=
by simp [mem_supported, set.subset_def, not_imp_comm]

lemma single_mem_supported {s : set α} {a : α} (b : β) (h : a ∈ s) :
  single a b ∈ supported β γ s :=
set.subset.trans support_single_subset (set.singleton_subset_iff.2 h)

lemma supported_eq_span_single [has_one β] (s : set α) :
  supported γ γ s = span γ ((λ i, single i 1) '' s) :=
begin
  refine (span_eq_of_le _ _ (le_def'.2 $ λ l hl, _)).symm,
  { rintro _ ⟨_, hp, rfl ⟩ , exact single_mem_supported γ 1 hp },
  { rw ← l.sum_single,
    refine sum_mem _ (λ i il, _),
    convert @smul_mem γ (α →₀ γ) _ _ _ _ (single i 1) (l i) _,
    { simp },
    apply subset_span,
    apply set.mem_image_of_mem _ (hl il) }
end

variables (β γ)

def restrict_dom (s : set α) : α →₀ β →ₗ supported β γ s :=
linear_map.cod_restrict _
  { to_fun := filter (∈ s),
    add := λ l₁ l₂, filter_add,
    smul := λ a l, filter_smul }
  (λ l, (mem_supported' _ _).2 $ λ x, filter_apply_neg (∈ s) l)

variables {β γ}

set_option class.instance_max_depth 50
@[simp] theorem restrict_dom_apply (s : set α) (l : α →₀ β) :
  ↑((restrict_dom β γ s : α →₀ β →ₗ supported β γ s) l) = finsupp.filter (∈ s) l := rfl
set_option class.instance_max_depth 32

theorem restrict_dom_comp_subtype (s : set α) :
  (restrict_dom β γ s).comp (submodule.subtype _) = linear_map.id :=
by ext l; apply subtype.coe_ext.2; simp; ext a;
   by_cases a ∈ s; simp [h]; exact ((mem_supported' γ l.1).1 l.2 a h).symm

theorem range_restrict_dom (s : set α) : (restrict_dom β γ s).range = ⊤ :=
begin
  have := linear_map.range_comp (submodule.subtype _) (restrict_dom β γ s),
  rw [restrict_dom_comp_subtype, linear_map.range_id] at this,
  exact eq_top_mono (submodule.map_mono le_top) this.symm
end

theorem supported_mono {s t : set α} (st : s ⊆ t) :
  supported β γ s ≤ supported β γ t :=
λ l h, set.subset.trans h st

@[simp] theorem supported_empty : supported β γ (∅ : set α) = ⊥ :=
eq_bot_iff.2 $ λ l h, (submodule.mem_bot γ).2 $
by ext; simp [*, mem_supported'] at *

@[simp] theorem supported_univ : supported β γ (set.univ : set α) = ⊤ :=
eq_top_iff.2 $ λ l _, set.subset_univ _

theorem supported_Union {δ : Type*} (s : δ → set α) :
  supported β γ (⋃ i, s i) = ⨆ i, supported β γ (s i) :=
begin
  refine le_antisymm _ (supr_le $ λ i, supported_mono $ set.subset_Union _ _),
  suffices : ((submodule.subtype _).comp (restrict_dom β γ (⋃ i, s i))).range ≤ ⨆ i, supported β γ (s i),
  { rwa [linear_map.range_comp, range_restrict_dom, map_top, range_subtype] at this },
  rw [range_le_iff_comap, eq_top_iff],
  rintro l ⟨⟩, rw mem_coe,
  apply finsupp.induction l, {exact zero_mem _},
  refine λ x a l hl a0, add_mem _ _,
  by_cases (∃ i, x ∈ s i); simp [h],
  cases h with i hi,
  exact le_supr (λ i, supported β γ (s i)) i (single_mem_supported γ _ hi)
end

theorem supported_union (s t : set α) :
  supported β γ (s ∪ t) = supported β γ s ⊔ supported β γ t :=
by erw [set.union_eq_Union, supported_Union, supr_bool_eq]; refl

theorem supported_Inter {ι : Type*} (s : ι → set α) :
  supported β γ (⋂ i, s i) = ⨅ i, supported β γ (s i) :=
begin
  refine le_antisymm (le_infi $ λ i, supported_mono $ set.Inter_subset _ _) _,
  simp [le_def, infi_coe, set.subset_def],
  exact λ l, set.subset_Inter
end

set_option class.instance_max_depth 37
def supported_equiv_finsupp (s : set α) [decidable_pred (λ (x : α), x ∈ s)] :
  (supported β γ s) ≃ₗ[γ] (s →₀ β) :=
(restrict_support_equiv s).to_linear_equiv
begin
  show is_linear_map γ ((lsubtype_domain s : (α →₀ β) →ₗ[γ] (s →₀ β)).comp
      (submodule.subtype (supported β γ s))),
  exact linear_map.is_linear _
end
set_option class.instance_max_depth 32

def lsum (f : α → γ →ₗ[γ] β) : α →₀ γ →ₗ[γ] β :=
⟨λ d, d.sum (λ i, f i),
  assume d₁ d₂, by simp [sum_add_index],
  assume a d, by simp [sum_smul_index, smul_sum, -smul_eq_mul, smul_eq_mul.symm]⟩

@[simp] theorem lsum_apply (f : α → γ →ₗ[γ] β) (l : α →₀ γ) :
  (finsupp.lsum f : α →₀ γ →ₗ β) l = l.sum (λ b, f b) := rfl

section lmap_domain
variables {α' : Type*} [decidable_eq α'] {α'' : Type*} [decidable_eq α''] (β γ)

def lmap_domain (f : α → α') : (α →₀ β) →ₗ[γ] (α' →₀ β) :=
⟨map_domain f, assume a b, map_domain_add, map_domain_smul⟩

@[simp] theorem map_apply (f : α → α') (l : α →₀ β) :
  (lmap_domain β γ f : (α →₀ β) →ₗ[γ] (α' →₀ β)) l = map_domain f l := rfl

@[simp] theorem map_id : (lmap_domain β γ id : α →₀ β →ₗ[γ] α →₀ β) = linear_map.id :=
linear_map.ext $ λ l, map_domain_id

theorem map_comp (f : α → α') (g : α' → α'') :
  lmap_domain β γ (g ∘ f) = (lmap_domain β γ g).comp (lmap_domain β γ f) :=
linear_map.ext $ λ l, map_domain_comp

theorem supported_comap_map (f : α → α') (s : set α') :
  supported β γ (f ⁻¹' s) ≤ (supported β γ s).comap (lmap_domain β γ f) :=
λ l (hl : ↑l.support ⊆ f ⁻¹' s),
show ↑(map_domain f l).support ⊆ s, begin
  rw [← set.image_subset_iff, ← finset.coe_image] at hl,
  exact set.subset.trans map_domain_support hl
end

theorem map_supported [inhabited α] (f : α → α') (s : set α) :
  (supported β γ s).map (lmap_domain β γ f) = supported β γ (f '' s) :=
begin
  refine le_antisymm (map_le_iff_le_comap.2 $
    le_trans (supported_mono $ set.subset_preimage_image _ _)
       (supported_comap_map _ _ _ _)) _,
  intros l hl,
  refine ⟨(lmap_domain β γ (function.inv_fun_on f s) : α' →₀ β →ₗ α →₀ β) l, λ x hx, _, _⟩,
  { rcases finset.mem_image.1 (map_domain_support hx) with ⟨c, hc, rfl⟩,
    exact function.inv_fun_on_mem (by simpa using hl hc) },
  { rw [← linear_map.comp_apply, ← map_comp],
    refine (map_domain_congr $ λ c hc, _).trans map_domain_id,
    exact function.inv_fun_on_eq (by simpa using hl hc) }
end

theorem map_disjoint_ker (f : α → α') {s : set α}
  (H : ∀ a b ∈ s, f a = f b → a = b) :
  disjoint (supported β γ s) (lmap_domain β γ f).ker :=
begin
  rintro l ⟨h₁, h₂⟩,
  rw [mem_coe, mem_ker, map_apply, map_domain] at h₂,
  simp, ext x,
  by_cases xs : x ∈ s,
  { have : finsupp.sum l (λ a, finsupp.single (f a)) (f x) = 0, {rw h₂, refl},
    rw [finsupp.sum_apply, finsupp.sum, finset.sum_eq_single x] at this,
    { simpa [finsupp.single_apply] },
    { intros y hy xy, simp [mt (H _ _ (h₁ hy) xs) xy] },
    { simp {contextual := tt} } },
  { by_contra h, exact xs (h₁ $ finsupp.mem_support_iff.2 h) }
end

end lmap_domain

section total
variables (α) {α' : Type*} (β) {β' : Type*} (γ)
          [decidable_eq α'] [decidable_eq β'] [add_comm_group β'] [module γ β']
          (v : α → β) {v' : α' → β'}

/-- Interprets (l : α →₀ γ) as linear combination of the elements in the family (v : α → β) and
    evaluates this linear combination. -/
protected def total : α →₀ γ →ₗ β := finsupp.lsum (λ i, linear_map.id.smul_right (v i))

variables {α β v}

theorem total_apply (l : α →₀ γ) :
  finsupp.total α β γ v l = l.sum (λ i a, a • v i) := rfl

@[simp] theorem total_single (c : γ) (a : α) :
  finsupp.total α β γ v (single a c) = c • (v a) :=
by simp [total_apply, sum_single_index]

theorem total_range (h : function.surjective v) : (finsupp.total α β γ v).range = ⊤ :=
begin
  apply range_eq_top.2,
  intros x,
  apply exists.elim (h x),
  exact λ i hi, ⟨single i 1, by simp [hi]⟩
end

theorem map_total (f : α → α') (g : β →ₗ[γ] β') (h : ∀ i, g (v i) = v' (f i)) :
  (finsupp.total α' β' γ v').comp (lmap_domain γ γ f) = g.comp (finsupp.total α β γ v) :=
by ext l; simp [total_apply, finsupp.sum_map_domain_index, add_smul, h]

theorem span_eq_map_total (s : set α):
  span γ (v '' s) = submodule.map (finsupp.total α β γ v) (supported γ γ s) :=
begin
  apply span_eq_of_le,
  { intros x hx,
    rw set.mem_image at hx,
    apply exists.elim hx,
    intros i hi,
    exact ⟨_, finsupp.single_mem_supported γ 1 hi.1, by simp [hi.2]⟩ },
  { refine map_le_iff_le_comap.2 (λ z hz, _),
    have : ∀i, z i • v i ∈ span γ (v '' s),
    { intro c, by_cases c ∈ s,
      { exact smul_mem _ _ (subset_span (set.mem_image_of_mem _ h)) },
      { simp [(finsupp.mem_supported' γ _).1 hz _ h] } },
    refine sum_mem _ _, simp [this] }
end

theorem mem_span_iff_total {s : set α} {x : β}:
  x ∈ span γ (v '' s) ↔ ∃ l ∈ supported γ γ s, finsupp.total α β γ v l = x :=
by rw span_eq_map_total; simp

variables (α) (β) (v)
protected def total_on (s : set α) : supported γ γ s →ₗ[γ] span γ (v '' s) :=
linear_map.cod_restrict _ ((finsupp.total _ _ _ v).comp (submodule.subtype (supported γ γ s))) $
  λ ⟨l, hl⟩, (mem_span_iff_total _).2 ⟨l, hl, rfl⟩
variables {α} {β} {v}

theorem total_on_range (s : set α) : (finsupp.total_on α β γ v s).range = ⊤ :=
by rw [finsupp.total_on, linear_map.range, linear_map.map_cod_restrict, ← linear_map.range_le_iff_comap,
  range_subtype, map_top, linear_map.range_comp, range_subtype]; exact le_of_eq (span_eq_map_total _ _)

end total

protected def dom_lcongr
  {α₁ : Type*} {α₂ : Type*} [decidable_eq α₁] [decidable_eq α₂] (e : α₁ ≃ α₂) :
  (α₁ →₀ β) ≃ₗ[γ] (α₂ →₀ β) :=
(finsupp.dom_congr e).to_linear_equiv
begin
  change is_linear_map γ (lmap_domain β γ e : (α₁ →₀ β) →ₗ[γ] (α₂ →₀ β)),
  exact linear_map.is_linear _
end

noncomputable def congr {α' : Type*} (s : set α) (t : set α') (e : s ≃ t) :
  supported β γ s ≃ₗ[γ] supported β γ t :=
begin
  refine linear_equiv.trans (finsupp.supported_equiv_finsupp s)
      (linear_equiv.trans _ (finsupp.supported_equiv_finsupp t).symm),
  exact finsupp.dom_lcongr e
end

end finsupp
