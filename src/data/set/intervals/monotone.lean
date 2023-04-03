/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.set.intervals.disjoint
import order.succ_pred.basic

/-!
# Monotonicity on intervals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that `set.Ici` etc are monotone/antitone functions. We also prove some lemmas
about functions monotone on intervals in `succ_order`s.
-/

open set

section Ixx

variables {α β : Type*} [preorder α] [preorder β] {f g : α → β} {s : set α}

lemma antitone_Ici : antitone (Ici : α → set α) := λ _ _, Ici_subset_Ici.2

lemma monotone_Iic : monotone (Iic : α → set α) := λ _ _, Iic_subset_Iic.2

lemma antitone_Ioi : antitone (Ioi : α → set α) := λ _ _, Ioi_subset_Ioi

lemma monotone_Iio : monotone (Iio : α → set α) := λ _ _, Iio_subset_Iio

protected lemma monotone.Ici (hf : monotone f) : antitone (λ x, Ici (f x)) :=
antitone_Ici.comp_monotone hf

protected lemma monotone_on.Ici (hf : monotone_on f s) : antitone_on (λ x, Ici (f x)) s :=
antitone_Ici.comp_monotone_on hf

protected lemma antitone.Ici (hf : antitone f) : monotone (λ x, Ici (f x)) :=
antitone_Ici.comp hf

protected lemma antitone_on.Ici (hf : antitone_on f s) : monotone_on (λ x, Ici (f x)) s :=
antitone_Ici.comp_antitone_on hf

protected lemma monotone.Iic (hf : monotone f) : monotone (λ x, Iic (f x)) :=
monotone_Iic.comp hf

protected lemma monotone_on.Iic (hf : monotone_on f s) : monotone_on (λ x, Iic (f x)) s :=
monotone_Iic.comp_monotone_on hf

protected lemma antitone.Iic (hf : antitone f) : antitone (λ x, Iic (f x)) :=
monotone_Iic.comp_antitone hf

protected lemma antitone_on.Iic (hf : antitone_on f s) : antitone_on (λ x, Iic (f x)) s :=
monotone_Iic.comp_antitone_on hf

protected lemma monotone.Ioi (hf : monotone f) : antitone (λ x, Ioi (f x)) :=
antitone_Ioi.comp_monotone hf

protected lemma monotone_on.Ioi (hf : monotone_on f s) : antitone_on (λ x, Ioi (f x)) s :=
antitone_Ioi.comp_monotone_on hf

protected lemma antitone.Ioi (hf : antitone f) : monotone (λ x, Ioi (f x)) :=
antitone_Ioi.comp hf

protected lemma antitone_on.Ioi (hf : antitone_on f s) : monotone_on (λ x, Ioi (f x)) s :=
antitone_Ioi.comp_antitone_on hf

protected lemma monotone.Iio (hf : monotone f) : monotone (λ x, Iio (f x)) :=
monotone_Iio.comp hf

protected lemma monotone_on.Iio (hf : monotone_on f s) : monotone_on (λ x, Iio (f x)) s :=
monotone_Iio.comp_monotone_on hf

protected lemma antitone.Iio (hf : antitone f) : antitone (λ x, Iio (f x)) :=
monotone_Iio.comp_antitone hf

protected lemma antitone_on.Iio (hf : antitone_on f s) : antitone_on (λ x, Iio (f x)) s :=
monotone_Iio.comp_antitone_on hf

protected lemma monotone.Icc (hf : monotone f) (hg : antitone g) :
  antitone (λ x, Icc (f x) (g x)) :=
hf.Ici.inter hg.Iic

protected lemma monotone_on.Icc (hf : monotone_on f s) (hg : antitone_on g s) :
  antitone_on (λ x, Icc (f x) (g x)) s :=
hf.Ici.inter hg.Iic

protected lemma antitone.Icc (hf : antitone f) (hg : monotone g) :
  monotone (λ x, Icc (f x) (g x)) :=
hf.Ici.inter hg.Iic

protected lemma antitone_on.Icc (hf : antitone_on f s) (hg : monotone_on g s) :
  monotone_on (λ x, Icc (f x) (g x)) s :=
hf.Ici.inter hg.Iic

protected lemma monotone.Ico (hf : monotone f) (hg : antitone g) :
  antitone (λ x, Ico (f x) (g x)) :=
hf.Ici.inter hg.Iio

protected lemma monotone_on.Ico (hf : monotone_on f s) (hg : antitone_on g s) :
  antitone_on (λ x, Ico (f x) (g x)) s :=
hf.Ici.inter hg.Iio

protected lemma antitone.Ico (hf : antitone f) (hg : monotone g) :
  monotone (λ x, Ico (f x) (g x)) :=
hf.Ici.inter hg.Iio

protected lemma antitone_on.Ico (hf : antitone_on f s) (hg : monotone_on g s) :
  monotone_on (λ x, Ico (f x) (g x)) s :=
hf.Ici.inter hg.Iio

protected lemma monotone.Ioc (hf : monotone f) (hg : antitone g) :
  antitone (λ x, Ioc (f x) (g x)) :=
hf.Ioi.inter hg.Iic

protected lemma monotone_on.Ioc (hf : monotone_on f s) (hg : antitone_on g s) :
  antitone_on (λ x, Ioc (f x) (g x)) s :=
hf.Ioi.inter hg.Iic

protected lemma antitone.Ioc (hf : antitone f) (hg : monotone g) :
  monotone (λ x, Ioc (f x) (g x)) :=
hf.Ioi.inter hg.Iic

protected lemma antitone_on.Ioc (hf : antitone_on f s) (hg : monotone_on g s) :
  monotone_on (λ x, Ioc (f x) (g x)) s :=
hf.Ioi.inter hg.Iic

protected lemma monotone.Ioo (hf : monotone f) (hg : antitone g) :
  antitone (λ x, Ioo (f x) (g x)) :=
hf.Ioi.inter hg.Iio

protected lemma monotone_on.Ioo (hf : monotone_on f s) (hg : antitone_on g s) :
  antitone_on (λ x, Ioo (f x) (g x)) s :=
hf.Ioi.inter hg.Iio

protected lemma antitone.Ioo (hf : antitone f) (hg : monotone g) :
  monotone (λ x, Ioo (f x) (g x)) :=
hf.Ioi.inter hg.Iio

protected lemma antitone_on.Ioo (hf : antitone_on f s) (hg : monotone_on g s) :
  monotone_on (λ x, Ioo (f x) (g x)) s :=
hf.Ioi.inter hg.Iio

end Ixx

section Union

variables {α β : Type*} [semilattice_sup α] [linear_order β] {f g : α → β} {a b : β}

lemma Union_Ioo_of_mono_of_is_glb_of_is_lub (hf : antitone f) (hg : monotone g)
  (ha : is_glb (range f) a) (hb : is_lub (range g) b) :
  (⋃ x, Ioo (f x) (g x)) = Ioo a b :=
calc (⋃ x, Ioo (f x) (g x)) = (⋃ x, Ioi (f x)) ∩ ⋃ x, Iio (g x) :
  Union_inter_of_monotone hf.Ioi hg.Iio
... = Ioi a ∩ Iio b : congr_arg2 (∩) ha.Union_Ioi_eq hb.Union_Iio_eq

end Union

section succ_order

open order

variables {α β : Type*} [partial_order α]

lemma strict_mono_on.Iic_id_le [succ_order α] [is_succ_archimedean α] [order_bot α]
  {n : α} {φ : α → α} (hφ : strict_mono_on φ (set.Iic n)) :
  ∀ m ≤ n, m ≤ φ m :=
begin
  revert hφ,
  refine succ.rec_bot (λ n, strict_mono_on φ (set.Iic n) → ∀ m ≤ n, m ≤ φ m)
    (λ _ _ hm, hm.trans bot_le) _ _,
  rintro k ih hφ m hm,
  by_cases hk : is_max k,
  { rw succ_eq_iff_is_max.2 hk at hm,
    exact ih (hφ.mono $ Iic_subset_Iic.2 (le_succ _)) _ hm },
  obtain (rfl | h) := le_succ_iff_eq_or_le.1 hm,
  { specialize ih (strict_mono_on.mono hφ (λ x hx, le_trans hx (le_succ _))) k le_rfl,
    refine le_trans (succ_mono ih) (succ_le_of_lt (hφ (le_succ _) le_rfl _)),
    rw lt_succ_iff_eq_or_lt_of_not_is_max hk,
    exact or.inl rfl },
  { exact ih (strict_mono_on.mono hφ (λ x hx, le_trans hx (le_succ _))) _ h }
end

lemma strict_mono_on.Iic_le_id [pred_order α] [is_pred_archimedean α] [order_top α]
  {n : α} {φ : α → α} (hφ : strict_mono_on φ (set.Ici n)) :
  ∀ m, n ≤ m → φ m ≤ m :=
@strict_mono_on.Iic_id_le αᵒᵈ _ _ _ _ _ _ (λ i hi j hj hij, hφ hj hi hij)

variables [preorder β] {ψ : α → β}

/-- A function `ψ` on a `succ_order` is strictly monotone before some `n` if for all `m` such that
`m < n`, we have `ψ m < ψ (succ m)`. -/
lemma strict_mono_on_Iic_of_lt_succ [succ_order α] [is_succ_archimedean α]
  {n : α} (hψ : ∀ m, m < n → ψ m < ψ (succ m)) :
  strict_mono_on ψ (set.Iic n) :=
begin
  intros x hx y hy hxy,
  obtain ⟨i, rfl⟩ := hxy.le.exists_succ_iterate,
  induction i with k ih,
  { simpa using hxy },
  cases k,
  { exact hψ _ (lt_of_lt_of_le hxy hy) },
  rw set.mem_Iic at *,
  simp only [function.iterate_succ', function.comp_apply] at ih hxy hy ⊢,
  by_cases hmax : is_max (succ^[k] x),
  { rw succ_eq_iff_is_max.2 hmax at hxy ⊢,
    exact ih (le_trans (le_succ _) hy) hxy },
  by_cases hmax' : is_max (succ (succ^[k] x)),
  { rw succ_eq_iff_is_max.2 hmax' at hxy ⊢,
    exact ih (le_trans (le_succ _) hy) hxy },
  refine lt_trans (ih (le_trans (le_succ _) hy)
    (lt_of_le_of_lt (le_succ_iterate k _) (lt_succ_iff_not_is_max.2 hmax))) _,
  rw [← function.comp_apply succ, ← function.iterate_succ'],
  refine hψ _ (lt_of_lt_of_le _ hy),
  rwa [function.iterate_succ', function.comp_apply, lt_succ_iff_not_is_max],
end

lemma strict_anti_on_Iic_of_succ_lt [succ_order α] [is_succ_archimedean α]
  {n : α} (hψ : ∀ m, m < n → ψ (succ m) < ψ m) :
  strict_anti_on ψ (set.Iic n) :=
λ i hi j hj hij, @strict_mono_on_Iic_of_lt_succ α βᵒᵈ _ _ ψ _ _ n hψ i hi j hj hij

lemma strict_mono_on_Iic_of_pred_lt [pred_order α] [is_pred_archimedean α]
  {n : α} (hψ : ∀ m, n < m → ψ (pred m) < ψ m) :
  strict_mono_on ψ (set.Ici n) :=
λ i hi j hj hij, @strict_mono_on_Iic_of_lt_succ αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij

lemma strict_anti_on_Iic_of_lt_pred [pred_order α] [is_pred_archimedean α]
  {n : α} (hψ : ∀ m, n < m → ψ m < ψ (pred m)) :
  strict_anti_on ψ (set.Ici n) :=
λ i hi j hj hij, @strict_anti_on_Iic_of_succ_lt αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij

end succ_order
