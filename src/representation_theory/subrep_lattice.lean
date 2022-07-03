/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.subrep
import representation_theory.rep_equiv

variables {k k' G V : Type*}

section add_comm_monoid

variables
  [comm_semiring k] [comm_semiring k'] [monoid G]
  [add_comm_monoid V] [module k V] [module k' V]
  [has_smul k' k] [is_scalar_tower k' k V]
  {ρ : representation k G V} {p q : subrep ρ}

namespace subrep

/-- The set `{0}` is the bottom element of the lattice of subreps. -/
instance : has_bot (subrep ρ) :=
⟨{ carrier := {0}, smulG_mem' := by simp { contextual := tt }, .. (⊥ : submodule k V)}⟩

instance inhabited' : inhabited (subrep ρ) := ⟨⊥⟩

@[simp] lemma bot_coe : ((⊥ : subrep ρ) : set V) = {0} := rfl
@[simp] lemma bot_to_submodule : (⊥ : subrep ρ).to_submodule = ⊥ := rfl

-- restrict_scalars_bot

@[simp] lemma mem_bot {x : V} : x ∈ (⊥ : subrep ρ) ↔ x = 0 := set.mem_singleton_iff

-- restrict_scalars_eq_bot_iff

instance unique_bot : unique (⊥ : subrep ρ) :=
⟨infer_instance, λ x, subtype.ext x.mem⟩

instance : order_bot (subrep ρ) :=
{ bot := ⊥,
  bot_le := λ p x, by simp [zero_mem] {contextual := tt} }

protected lemma eq_bot_iff (p : subrep ρ) : p = ⊥ ↔ ∀ x ∈ p, x = (0 : V) :=
⟨ λ h, h.symm ▸ λ x hx, hx,
  λ h, eq_bot_iff.mpr (λ x hx, h x hx) ⟩

@[ext] protected lemma bot_ext (x y : (⊥ : subrep ρ)) : x = y :=
begin
  rcases x with ⟨x, xm⟩, rcases y with ⟨y, ym⟩, congr,
  rw (subrep.eq_bot_iff _).mp rfl x xm,
  rw (subrep.eq_bot_iff _).mp rfl y ym
end

protected lemma ne_bot_iff (p : subrep ρ) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : V) :=
by { haveI := classical.prop_decidable, simp_rw [ne.def, p.eq_bot_iff, not_forall] }

lemma nonzero_mem_of_bot_lt {p : subrep ρ} (bot_lt : ⊥ < p) : ∃ a : p, a ≠ 0 :=
let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp bot_lt.ne' in ⟨⟨b, hb₁⟩, hb₂ ∘ (congr_arg coe)⟩

lemma exists_mem_ne_zero_of_ne_bot {p : subrep ρ} (h : p ≠ ⊥) : ∃ b : V, b ∈ p ∧ b ≠ 0 :=
let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp h in ⟨b, hb₁, hb₂⟩

-- bot_equiv_punit

lemma eq_bot_of_subsingleton (p : subrep ρ) [subsingleton p] : p = ⊥ :=
begin
  rw eq_bot_iff,
  intros v hv,
  exact congr_arg coe (subsingleton.elim (⟨v, hv⟩ : p) 0)
end

/-- The universal set is the top element of the lattice of subrepresentations. -/
instance : has_top (subrep ρ) :=
⟨{ carrier := set.univ, smulG_mem' := λ _ _ _, trivial, .. (⊤ : submodule k V)}⟩

@[simp] lemma top_coe : ((⊤ : subrep ρ) : set V) = set.univ := rfl

@[simp] lemma top_to_add_submonoid : (⊤ : subrep ρ).to_submodule = ⊤ := rfl

@[simp] lemma mem_top {x : V} : x ∈ (⊤ : subrep ρ) := trivial

-- restrict_scalars_top

instance : order_top (subrep ρ) :=
{ top := ⊤,
  le_top := λ p x _, trivial }

lemma eq_top_iff' {p : subrep ρ} : p = ⊤ ↔ ∀ x, x ∈ p :=
eq_top_iff.trans ⟨λ h x, h trivial, λ h x _, h x⟩

/-- The top subrep is linearly equivalent to the representation. -/
@[simps] def top_equiv : (⊤ : subrep ρ).representation' ≃ᵣ ρ  :=
{ to_fun := λ x, x,
  inv_fun := λ x, ⟨x, by simp⟩,
  map_add' := by { intros, refl },
  map_smul' := by { intros, refl },
  map_smulG' := by { intros, refl },
  left_inv := by { intro x, ext, refl },
  right_inv := by { intro x, refl }, }

instance : has_Inf (subrep ρ) :=
⟨λ S,
{ carrier    := ⋂ s ∈ S, (s : set V),
  zero_mem'  := by simp [zero_mem],
  add_mem'   := by simp [add_mem] {contextual := tt},
  smul_mem'  := by simp [smul_mem] {contextual := tt},
  smulG_mem' := by simp [smulG_mem] {contextual := tt} }⟩

private lemma Inf_le' {S : set (subrep ρ)} {p} : p ∈ S → Inf S ≤ p :=
set.bInter_subset_of_mem

private lemma le_Inf' {S : set (subrep ρ)} {p} : (∀q ∈ S, p ≤ q) → p ≤ Inf S :=
set.subset_Inter₂

instance : has_inf (subrep ρ) :=
⟨λ p q,
{ carrier    := p ∩ q,
  zero_mem'  := by simp [zero_mem],
  add_mem'   := by simp [add_mem] {contextual := tt},
  smul_mem'  := by simp [smul_mem] {contextual := tt},
  smulG_mem' := by simp [smulG_mem] {contextual := tt} }⟩

instance : complete_lattice (subrep ρ) :=
{ sup          := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left  := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, ha,
  le_sup_right := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, hb,
  sup_le       := λ a b c h₁ h₂, Inf_le' ⟨h₁, h₂⟩,
  inf          := (⊓),
  le_inf       := λ a b c, set.subset_inter,
  inf_le_left  := λ a b, set.inter_subset_left _ _,
  inf_le_right := λ a b, set.inter_subset_right _ _,
  Sup          := λtt, Inf {t | ∀t'∈tt, t' ≤ t},
  le_Sup       := λ s p hs, le_Inf' $ λ q hq, hq _ hs,
  Sup_le       := λ s p hs, Inf_le' hs,
  Inf          := Inf,
  le_Inf       := λ s a, le_Inf',
  Inf_le       := λ s a, Inf_le',
  ..subrep.order_top,
  ..subrep.order_bot,
  ..set_like.partial_order }

@[simp] theorem inf_coe : ↑(p ⊓ q) = (p ∩ q : set V) := rfl

@[simp] theorem mem_inf {p q : subrep ρ} {x : V} :
  x ∈ p ⊓ q ↔ x ∈ p ∧ x ∈ q := iff.rfl

@[simp] theorem Inf_coe (P : set (subrep ρ)) : (↑(Inf P) : set V) = ⋂ p ∈ P, ↑p := rfl

@[simp] theorem finset_inf_coe {ι} (s : finset ι) (p : ι → subrep ρ) :
  (↑(s.inf p) : set V) = ⋂ i ∈ s, ↑(p i) :=
begin
  letI := classical.dec_eq ι,
  refine s.induction_on _ (λ i s hi ih, _),
  { simp },
  { rw [finset.inf_insert, inf_coe, ih],
    simp },
end

@[simp] theorem infi_coe {ι} (p : ι → subrep ρ) :
  (↑⨅ i, p i : set V) = ⋂ i, ↑(p i) :=
by rw [infi, Inf_coe]; ext a; simp; exact
⟨λ h i, h _ i rfl, λ h i x e, e ▸ h _⟩

@[simp] lemma mem_Inf {S : set (subrep ρ)} {x : V} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
set.mem_Inter₂

@[simp] theorem mem_infi {ι} (p : ι → subrep ρ) {x} :
  x ∈ (⨅ i, p i) ↔ ∀ i, x ∈ p i :=
by rw [← set_like.mem_coe, infi_coe, set.mem_Inter]; refl

@[simp] theorem mem_finset_inf {ι} {s : finset ι} {p : ι → subrep ρ} {x : V} :
  x ∈ s.inf p ↔ ∀ i ∈ s, x ∈ p i :=
by simp only [← set_like.mem_coe, finset_inf_coe, set.mem_Inter]

lemma mem_sup_left {S T : subrep ρ} : ∀ {x : V}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

lemma mem_sup_right {S T : subrep ρ} : ∀ {x : V}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

lemma add_mem_sup {S T : subrep ρ} {s t : V} (hs : s ∈ S) (ht : t ∈ T) : s + t ∈ S ⊔ T :=
add_mem (mem_sup_left hs) (mem_sup_right ht)

lemma mem_supr_of_mem {ι : Sort*} {b : V} {p : ι → subrep ρ} (i : ι) (h : b ∈ p i) :
  b ∈ (⨆i, p i) :=
have p i ≤ (⨆i, p i) := le_supr p i,
@this b h

open_locale big_operators

lemma sum_mem_supr {ι : Type*} [fintype ι] {f : ι → V} {p : ι → subrep ρ}
  (h : ∀ i, f i ∈ p i) :
  ∑ i, f i ∈ ⨆ i, p i :=
sum_mem $ λ i hi, mem_supr_of_mem i (h i)

lemma sum_mem_bsupr {ι : Type*} {s : finset ι} {f : ι → V} {p : ι → subrep ρ}
  (h : ∀ i ∈ s, f i ∈ p i) :
  ∑ i in s, f i ∈ ⨆ i ∈ s, p i :=
sum_mem $ λ i hi, mem_supr_of_mem i $ mem_supr_of_mem hi (h i hi)

lemma mem_Sup_of_mem {S : set (subrep ρ)} {s : subrep ρ}
  (hs : s ∈ S) : ∀ {x : V}, x ∈ s → x ∈ Sup S :=
show s ≤ Sup S, from le_Sup hs

theorem disjoint_def {p p' : subrep ρ} :
  disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = (0 : V) :=
show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : set V)) ↔ _, by simp

theorem disjoint_def' {p p' : subrep ρ} :
  disjoint p p' ↔ ∀ (x ∈ p) (y ∈ p'), x = y → x = (0 : V) :=
disjoint_def.trans ⟨λ h x hx y hy hxy, h x hx $ hxy.symm ▸ hy,
  λ h x hx hx', h _ hx x hx' rfl⟩

lemma eq_zero_of_coe_mem_of_disjoint (hpq : disjoint p q) {a : p} (ha : (a : V) ∈ q) :
  a = 0 :=
by exact_mod_cast disjoint_def.mp hpq a (coe_mem a) ha

end subrep

-- nat_submodule

end add_comm_monoid
