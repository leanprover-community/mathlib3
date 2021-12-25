/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Gabriel Ebner, Yury Kudryashov
-/
import data.nat.enat
import order.conditionally_complete_lattice

/-!
# Conditionally complete linear order structure on `ℕ`

In this file we

* define a `conditionally_complete_linear_order_bot` structure on `ℕ`;
* define a `complete_linear_order` structure on `enat`;
* prove a few lemmas about `supr`/`infi`/`set.Union`/`set.Inter` and natural numbers.
-/

open set

namespace nat

open_locale classical

noncomputable instance : has_Inf ℕ :=
⟨λs, if h : ∃n, n ∈ s then @nat.find (λn, n ∈ s) _ h else 0⟩

noncomputable instance : has_Sup ℕ :=
⟨λs, if h : ∃n, ∀a∈s, a ≤ n then @nat.find (λn, ∀a∈s, a ≤ n) _ h else 0⟩

lemma Inf_def {s : set ℕ} (h : s.nonempty) : Inf s = @nat.find (λn, n ∈ s) _ h :=
dif_pos _

lemma Sup_def {s : set ℕ} (h : ∃n, ∀a∈s, a ≤ n) :
  Sup s = @nat.find (λn, ∀a∈s, a ≤ n) _ h :=
dif_pos _

lemma _root_.set.infinite.nat.Sup_eq_zero {s : set ℕ} (h : s.infinite) : Sup s = 0 :=
dif_neg $ λ ⟨n, hn⟩, let ⟨k, hks, hk⟩ := h.exists_nat_lt n in (hn k hks).not_lt hk

@[simp] lemma Inf_eq_zero {s : set ℕ} : Inf s = 0 ↔ 0 ∈ s ∨ s = ∅ :=
begin
  cases eq_empty_or_nonempty s,
  { subst h, simp only [or_true, eq_self_iff_true, iff_true, Inf, has_Inf.Inf,
      mem_empty_eq, exists_false, dif_neg, not_false_iff] },
  { have := ne_empty_iff_nonempty.mpr h,
    simp only [this, or_false, nat.Inf_def, h, nat.find_eq_zero] }
end

@[simp] lemma Inf_empty : Inf ∅ = 0 :=
by { rw Inf_eq_zero, right, refl }

lemma Inf_mem {s : set ℕ} (h : s.nonempty) : Inf s ∈ s :=
by { rw [nat.Inf_def h], exact nat.find_spec h }

lemma not_mem_of_lt_Inf {s : set ℕ} {m : ℕ} (hm : m < Inf s) : m ∉ s :=
begin
  cases eq_empty_or_nonempty s,
  { subst h, apply not_mem_empty },
  { rw [nat.Inf_def h] at hm, exact nat.find_min h hm }
end

protected lemma Inf_le {s : set ℕ} {m : ℕ} (hm : m ∈ s) : Inf s ≤ m :=
by { rw [nat.Inf_def ⟨m, hm⟩], exact nat.find_min' ⟨m, hm⟩ hm }

lemma nonempty_of_pos_Inf {s : set ℕ} (h : 0 < Inf s) : s.nonempty :=
begin
  by_contradiction contra, rw set.not_nonempty_iff_eq_empty at contra,
  have h' : Inf s ≠ 0, { exact ne_of_gt h, }, apply h',
  rw nat.Inf_eq_zero, right, assumption,
end

lemma nonempty_of_Inf_eq_succ {s : set ℕ} {k : ℕ} (h : Inf s = k + 1) : s.nonempty :=
nonempty_of_pos_Inf (h.symm ▸ (succ_pos k) : Inf s > 0)

lemma eq_Ici_of_nonempty_of_upward_closed {s : set ℕ} (hs : s.nonempty)
  (hs' : ∀ (k₁ k₂ : ℕ), k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) : s = Ici (Inf s) :=
ext (λ n, ⟨λ H, nat.Inf_le H, λ H, hs' (Inf s) n H (Inf_mem hs)⟩)

lemma Inf_upward_closed_eq_succ_iff {s : set ℕ}
  (hs : ∀ (k₁ k₂ : ℕ), k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) (k : ℕ) :
  Inf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s :=
begin
  split,
  { intro H,
    rw [eq_Ici_of_nonempty_of_upward_closed (nonempty_of_Inf_eq_succ H) hs, H, mem_Ici, mem_Ici],
    exact ⟨le_refl _, k.not_succ_le_self⟩, },
  { rintro ⟨H, H'⟩,
    rw [Inf_def (⟨_, H⟩ : s.nonempty), find_eq_iff],
    exact ⟨H, λ n hnk hns, H' $ hs n k (lt_succ_iff.mp hnk) hns⟩, },
end

/-- This instance is necessary, otherwise the lattice operations would be derived via
conditionally_complete_linear_order_bot and marked as noncomputable. -/
instance : lattice ℕ := lattice_of_linear_order

noncomputable instance : conditionally_complete_linear_order_bot ℕ :=
{ Sup := Sup, Inf := Inf,
  le_cSup    := assume s a hb ha, by rw [Sup_def hb]; revert a ha; exact @nat.find_spec _ _ hb,
  cSup_le    := assume s a hs ha, by rw [Sup_def ⟨a, ha⟩]; exact nat.find_min' _ ha,
  le_cInf    := assume s a hs hb,
    by rw [Inf_def hs]; exact hb (@nat.find_spec (λn, n ∈ s) _ _),
  cInf_le    := assume s a hb ha, by rw [Inf_def ⟨a, ha⟩]; exact nat.find_min' _ ha,
  cSup_empty :=
  begin
    simp only [Sup_def, set.mem_empty_eq, forall_const, forall_prop_of_false, not_false_iff,
      exists_const],
    apply bot_unique (nat.find_min' _ _),
    trivial
  end,
  .. (infer_instance : order_bot ℕ), .. (lattice_of_linear_order : lattice ℕ),
  .. (infer_instance : linear_order ℕ) }

lemma Inf_add {n : ℕ} {p : ℕ → Prop} (hn : n ≤ Inf {m | p m}) :
  Inf {m | p (m + n)} + n = Inf {m | p m} :=
begin
  obtain h | ⟨m, hm⟩ := {m | p (m + n)}.eq_empty_or_nonempty,
  { rw [h, nat.Inf_empty, zero_add],
    obtain hnp | hnp := hn.eq_or_lt,
    { exact hnp },
    suffices hp : p (Inf {m | p m} - n + n),
    { exact (h.subset hp).elim },
    rw tsub_add_cancel_of_le hn,
    exact Inf_mem (nonempty_of_pos_Inf $ n.zero_le.trans_lt hnp) },
  { have hp : ∃ n, n ∈ {m | p m} := ⟨_, hm⟩,
    rw [nat.Inf_def ⟨m, hm⟩, nat.Inf_def hp],
    rw [nat.Inf_def hp] at hn,
    exact find_add hn }
end

lemma Inf_add' {n : ℕ} {p : ℕ → Prop} (h : 0 < Inf {m | p m}) :
  Inf {m | p m} + n = Inf {m | p (m - n)} :=
begin
  convert Inf_add _,
  { simp_rw add_tsub_cancel_right },
  obtain ⟨m, hm⟩ := nonempty_of_pos_Inf h,
  refine le_cInf ⟨m + n, _⟩ (λ b hb, le_of_not_lt $ λ hbn,
    ne_of_mem_of_not_mem _ (not_mem_of_lt_Inf h) (tsub_eq_zero_of_le hbn.le)),
  { dsimp,
    rwa add_tsub_cancel_right },
  { exact hb }
end

section

variables {α : Type*} [complete_lattice α]

lemma supr_lt_succ (u : ℕ → α) (n : ℕ) : (⨆ k < n + 1, u k) = (⨆ k < n, u k) ⊔ u n :=
by simp [nat.lt_succ_iff_lt_or_eq, supr_or, supr_sup_eq]

lemma supr_lt_succ' (u : ℕ → α) (n : ℕ) : (⨆ k < n + 1, u k) = u 0 ⊔ (⨆ k < n, u (k + 1)) :=
by { rw ← sup_supr_nat_succ, simp }

lemma infi_lt_succ (u : ℕ → α) (n : ℕ) : (⨅ k < n + 1, u k) = (⨅ k < n, u k) ⊓ u n :=
@supr_lt_succ (order_dual α) _ _ _

lemma infi_lt_succ' (u : ℕ → α) (n : ℕ) : (⨅ k < n + 1, u k) = u 0 ⊓ (⨅ k < n, u (k + 1)) :=
@supr_lt_succ' (order_dual α) _ _ _

end

end nat

namespace set

variable {α : Type*}

lemma bUnion_lt_succ (u : ℕ → set α) (n : ℕ) : (⋃ k < n + 1, u k) = (⋃ k < n, u k) ∪ u n :=
nat.supr_lt_succ u n

lemma bUnion_lt_succ' (u : ℕ → set α) (n : ℕ) : (⋃ k < n + 1, u k) = u 0 ∪ (⋃ k < n, u (k + 1)) :=
nat.supr_lt_succ' u n

lemma bInter_lt_succ (u : ℕ → set α) (n : ℕ) : (⋂ k < n + 1, u k) = (⋂ k < n, u k) ∩ u n :=
nat.infi_lt_succ u n

lemma bInter_lt_succ' (u : ℕ → set α) (n : ℕ) : (⋂ k < n + 1, u k) = u 0 ∩ (⋂ k < n, u (k + 1)) :=
nat.infi_lt_succ' u n

end set

namespace enat
open_locale classical

noncomputable instance : complete_linear_order enat :=
{ .. enat.linear_order,
  .. with_top_order_iso.symm.to_galois_insertion.lift_complete_lattice }

end enat
