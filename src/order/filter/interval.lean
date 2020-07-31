import order.filter.lift
import order.filter.at_top_bot

variables {α β : Type*}

open_locale classical filter

namespace set

variables [preorder α]

def ord_connected (s : set α) : Prop := ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), Icc x y ⊆ s

lemma ord_connected.inter {s t : set α} (hs : ord_connected s) (ht : ord_connected t) :
  ord_connected (s ∩ t) :=
λ x hx y hy, subset_inter (hs hx.1 hy.1) (ht hx.2 hy.2)

lemma ord_connected.dual {s : set α} (hs : ord_connected s) : @ord_connected (order_dual α) _ s :=
λ x hx y hy z hz, hs hy hx ⟨hz.2, hz.1⟩

lemma ord_connected_dual {s : set α} : @ord_connected (order_dual α) _ s ↔ ord_connected s :=
⟨λ h, h.dual, λ h, h.dual⟩

lemma ord_connected_sInter {S : set (set α)} (hS : ∀ s ∈ S, ord_connected s) :
  ord_connected (⋂₀ S) :=
λ x hx y hy, subset_sInter $ λ s hs, hS s hs (hx s hs) (hy s hs)

lemma ord_connected_Inter {ι : Sort*} {s : ι → set α} (hs : ∀ i, ord_connected (s i)) :
  ord_connected (⋂ i, s i) :=
ord_connected_sInter $ forall_range_iff.2 hs

lemma ord_connected_bInter {ι : Sort*} {p : ι → Prop} {s : Π (i : ι) (hi : p i), set α}
  (hs : ∀ i hi, ord_connected (s i hi)) :
  ord_connected (⋂ i hi, s i hi) :=
ord_connected_Inter $ λ i, ord_connected_Inter $ hs i

lemma ord_connected_Ici {a : α} : ord_connected (Ici a) := λ x hx y hy z hz, le_trans hx hz.1
lemma ord_connected_Iic {a : α} : ord_connected (Iic a) := λ x hx y hy z hz, le_trans hz.2 hy
lemma ord_connected_Ioi {a : α} : ord_connected (Ioi a) := λ x hx y hy z hz, lt_of_lt_of_le hx hz.1
lemma ord_connected_Iio {a : α} : ord_connected (Iio a) := λ x hx y hy z hz, lt_of_le_of_lt hz.2 hy

lemma ord_connected_Icc {a b : α} : ord_connected (Icc a b) :=
ord_connected_Ici.inter ord_connected_Iic

lemma ord_connected_Ico {a b : α} : ord_connected (Ico a b) :=
ord_connected_Ici.inter ord_connected_Iio

lemma ord_connected_Ioc {a b : α} : ord_connected (Ioc a b) :=
ord_connected_Ioi.inter ord_connected_Iic

lemma ord_connected_Ioo {a b : α} : ord_connected (Ioo a b) :=
ord_connected_Ioi.inter ord_connected_Iio

end set

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
  refine ⟨_, λ h, has_basis_principal.is_interval_generated (λ _ _, h)⟩,
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
