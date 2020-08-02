import data.set.intervals.ord_connected
import order.filter.lift
import order.filter.at_top_bot

variables {α β : Type*}

open_locale classical filter

open set function

namespace filter

variables [preorder α]

class is_interval_generated (f : filter α) : Prop :=
(exists_ord_connected_mem : ∀ ⦃s⦄, s ∈ f → ∃ t ∈ f, ord_connected t ∧ t ⊆ s)

export is_interval_generated (exists_ord_connected_mem)

lemma has_basis.is_interval_generated {f : filter α} {ι} {p : ι → Prop} {s} (h : f.has_basis p s)
  (hs : ∀ i, p i → ord_connected (s i)) :
  is_interval_generated f :=
begin
  refine ⟨λ t ht, _⟩,
  rcases h.mem_iff.1 ht with ⟨i, hi, hsi⟩,
  exact ⟨s i, h.mem_of_mem hi, hs i hi, hsi⟩,
end

lemma has_ord_connected_basis (f : filter α) [is_interval_generated f] :
  f.has_basis (λ s : set α, s ∈ f ∧ ord_connected s) id :=
f.basis_sets.restrict $ λ s hs,
  by simpa only [exists_prop, and_assoc] using exists_ord_connected_mem hs

lemma is_interval_generated_principal_iff {s : set α} :
  is_interval_generated (𝓟 s) ↔ ord_connected s :=
begin
  refine ⟨_, λ h, (has_basis_principal _).is_interval_generated (λ _ _, h)⟩,
  introI h,
  rcases exists_ord_connected_mem (mem_principal_self s) with ⟨t, hst, ht, hts⟩,
  rwa [subset.antisymm hst hts]
end

alias is_interval_generated_principal_iff ↔ _ set.ord_connected.is_interval_generated_principal

instance is_interval_generated_inf {f g : filter α} [is_interval_generated f]
  [is_interval_generated g] :
  is_interval_generated (f ⊓ g) :=
begin
  apply ((has_ord_connected_basis f).inf (has_ord_connected_basis g)).is_interval_generated,
  rintros ⟨s, t⟩ ⟨⟨hsf, hsc⟩, htg, htc⟩,
  exact hsc.inter htc
end

instance is_interval_generated_at_top : is_interval_generated (at_top : filter α) :=
(has_basis_infi_principal_finite _).is_interval_generated $ λ t ht, ord_connected_bInter $
  λ i hi, ord_connected_Ici

instance is_interval_generated_at_bot : is_interval_generated (at_bot : filter α) :=
(has_basis_infi_principal_finite _).is_interval_generated $ λ t ht, ord_connected_bInter $
  λ i hi, ord_connected_Iic

lemma tendsto_Ixx_same_filter {Ixx : α → α → set α} (hI : ∀ x y, Ixx x y ⊆ Icc x y)
  (l : filter α) [is_interval_generated l] :
  tendsto (uncurry Ixx) (l ×ᶠ l) (l.lift' powerset) :=
begin
  rw [l.basis_sets.prod_self.tendsto_iff (l.basis_sets.lift' (λ _ _, powerset_mono.2))],
  intros s hs,
  rcases exists_ord_connected_mem hs with ⟨t, htl, htc, hts⟩,
  exact ⟨t, htl, λ x hx, subset.trans (hI _ _) (subset.trans (htc hx.1 hx.2) hts)⟩
end

lemma tendsto.Ixx {la : filter α} [is_interval_generated la]
  {Ixx : α → α → set α} (hI : ∀ x y, Ixx x y ⊆ Icc x y)
  {lb : filter β} {f g : β → α} (hf : tendsto f lb la) (hg : tendsto g lb la) :
  tendsto (λ x, Ixx (f x) (g x)) lb (la.lift' powerset) :=
(tendsto_Ixx_same_filter hI _).comp (hf.prod_mk hg)

lemma tendsto.Icc {lb : filter β} {la : filter α} [is_interval_generated la]
  {f g : β → α} (hf : tendsto f lb la) (hg : tendsto g lb la) :
  tendsto (λ x, Icc (f x) (g x)) lb (la.lift' powerset) :=
hf.Ixx (λ _ _, subset.refl _) hg

lemma tendsto.Ico {lb : filter β} {la : filter α} [is_interval_generated la]
  {f g : β → α} (hf : tendsto f lb la) (hg : tendsto g lb la) :
  tendsto (λ x, Ico (f x) (g x)) lb (la.lift' powerset) :=
hf.Ixx (λ _ _, Ico_subset_Icc_self) hg

lemma tendsto.Ioc {lb : filter β} {la : filter α} [is_interval_generated la]
  {f g : β → α} (hf : tendsto f lb la) (hg : tendsto g lb la) :
  tendsto (λ x, Ioc (f x) (g x)) lb (la.lift' powerset) :=
hf.Ixx (λ _ _, Ioc_subset_Icc_self) hg

lemma tendsto.Ioo {lb : filter β} {la : filter α} [is_interval_generated la]
  {f g : β → α} (hf : tendsto f lb la) (hg : tendsto g lb la) :
  tendsto (λ x, Ioo (f x) (g x)) lb (la.lift' powerset) :=
hf.Ixx (λ _ _, Ioo_subset_Icc_self) hg

end filter

open set filter

lemma set.ord_connected.is_interval_generated_inf_principal [preorder α]
  {f : filter α} [is_interval_generated f] {s : set α} (hs : ord_connected s) :
  is_interval_generated (f ⊓ 𝓟 s) :=
by haveI := hs.is_interval_generated_principal; apply_instance
