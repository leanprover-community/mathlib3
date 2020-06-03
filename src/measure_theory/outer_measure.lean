/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Outer measures -- overapproximations of measures
-/
import analysis.specific_limits
import measure_theory.measurable_space

noncomputable theory

open set finset function filter encodable
open_locale classical

namespace measure_theory

structure outer_measure (α : Type*) :=
(measure_of : set α → ennreal)
(empty : measure_of ∅ = 0)
(mono : ∀{s₁ s₂}, s₁ ⊆ s₂ → measure_of s₁ ≤ measure_of s₂)
(Union_nat : ∀(s:ℕ → set α), measure_of (⋃i, s i) ≤ (∑'i, measure_of (s i)))

namespace outer_measure

instance {α} : has_coe_to_fun (outer_measure α) := ⟨_, λ m, m.measure_of⟩

section basic
variables {α : Type*} {ms : set (outer_measure α)} {m : outer_measure α}

@[simp] theorem empty' (m : outer_measure α) : m ∅ = 0 := m.empty

theorem mono' (m : outer_measure α) {s₁ s₂}
  (h : s₁ ⊆ s₂) : m s₁ ≤ m s₂ := m.mono h

theorem Union_aux (m : set α → ennreal) (m0 : m ∅ = 0)
  {β} [encodable β] (s : β → set α) :
  (∑' b, m (s b)) = ∑' i, m (⋃ b ∈ decode2 β i, s b) :=
begin
  have H : ∀ n, m (⋃ b ∈ decode2 β n, s b) ≠ 0 → (decode2 β n).is_some,
  { intros n h,
    cases decode2 β n with b,
    { exact (h (by simp [m0])).elim },
    { exact rfl } },
  refine tsum_eq_tsum_of_ne_zero_bij (λ n h, option.get (H n h)) _ _ _,
  { intros m n hm hn e,
    have := mem_decode2.1 (option.get_mem (H n hn)),
    rwa [← e, mem_decode2.1 (option.get_mem (H m hm))] at this },
  { intros b h,
    refine ⟨encode b, _, _⟩,
    { convert h, simp [ext_iff, encodek2] },
    { exact option.get_of_mem _ (encodek2 _) } },
  { intros n h,
    transitivity, swap,
    rw [show decode2 β n = _, from option.get_mem (H n h)],
    congr, simp [ext_iff, -option.some_get] }
end

protected theorem Union (m : outer_measure α)
  {β} [encodable β] (s : β → set α) :
  m (⋃i, s i) ≤ (∑'i, m (s i)) :=
by rw [Union_decode2, Union_aux _ m.empty' s]; exact m.Union_nat _

lemma Union_null (m : outer_measure α)
  {β} [encodable β] {s : β → set α} (h : ∀ i, m (s i) = 0) : m (⋃i, s i) = 0 :=
by simpa [h] using m.Union s

protected lemma union (m : outer_measure α) (s₁ s₂ : set α) :
  m (s₁ ∪ s₂) ≤ m s₁ + m s₂ :=
begin
  convert m.Union (λ b, cond b s₁ s₂),
  { simp [union_eq_Union] },
  { rw tsum_fintype, change _ = _ + _, simp }
end

lemma union_null (m : outer_measure α) {s₁ s₂ : set α}
  (h₁ : m s₁ = 0) (h₂ : m s₂ = 0) : m (s₁ ∪ s₂) = 0 :=
by simpa [h₁, h₂] using m.union s₁ s₂

@[ext] lemma ext : ∀{μ₁ μ₂ : outer_measure α},
  (∀s, μ₁ s = μ₂ s) → μ₁ = μ₂
| ⟨m₁, e₁, _, u₁⟩ ⟨m₂, e₂, _, u₂⟩ h := by congr; exact funext h

instance : has_zero (outer_measure α) :=
⟨{ measure_of := λ_, 0,
   empty      := rfl,
   mono       := assume _ _ _, le_refl 0,
   Union_nat  := assume s, zero_le _ }⟩

@[simp] theorem zero_apply (s : set α) : (0 : outer_measure α) s = 0 := rfl

instance : inhabited (outer_measure α) := ⟨0⟩

instance : has_add (outer_measure α) :=
⟨λm₁ m₂,
  { measure_of := λs, m₁ s + m₂ s,
    empty      := show m₁ ∅ + m₂ ∅ = 0, by simp [outer_measure.empty],
    mono       := assume s₁ s₂ h, add_le_add' (m₁.mono h) (m₂.mono h),
    Union_nat  := assume s,
      calc m₁ (⋃i, s i) + m₂ (⋃i, s i) ≤
          (∑'i, m₁ (s i)) + (∑'i, m₂ (s i)) :
          add_le_add' (m₁.Union_nat s) (m₂.Union_nat s)
        ... = _ : ennreal.tsum_add.symm}⟩

@[simp] theorem add_apply (m₁ m₂ : outer_measure α) (s : set α) :
  (m₁ + m₂) s = m₁ s + m₂ s := rfl

instance add_comm_monoid : add_comm_monoid (outer_measure α) :=
{ zero      := 0,
  add       := (+),
  add_comm  := assume a b, ext $ assume s, add_comm _ _,
  add_assoc := assume a b c, ext $ assume s, add_assoc _ _ _,
  add_zero  := assume a, ext $ assume s, add_zero _,
  zero_add  := assume a, ext $ assume s, by simp }

instance : has_bot (outer_measure α) := ⟨0⟩

instance outer_measure.order_bot : order_bot (outer_measure α) :=
{ le          := λm₁ m₂, ∀s, m₁ s ≤ m₂ s,
  bot         := 0,
  le_refl     := assume a s, le_refl _,
  le_trans    := assume a b c hab hbc s, le_trans (hab s) (hbc s),
  le_antisymm := assume a b hab hba, ext $ assume s, le_antisymm (hab s) (hba s),
  bot_le      := assume a s, zero_le _ }

section supremum

instance : has_Sup (outer_measure α) :=
⟨λms, {
  measure_of := λs, ⨆m:ms, m.val s,
  empty      := le_zero_iff_eq.1 $ supr_le $ λ ⟨m, h⟩, le_of_eq m.empty,
  mono       := assume s₁ s₂ hs, supr_le_supr $ assume ⟨m, hm⟩, m.mono hs,
  Union_nat  := assume f, supr_le $ assume m,
    calc m.val (⋃i, f i) ≤ (∑' (i : ℕ), m.val (f i)) : m.val.Union_nat _
      ... ≤ (∑'i, ⨆m:ms, m.val (f i)) :
        ennreal.tsum_le_tsum $ assume i, le_supr (λm:ms, m.val (f i)) m }⟩

protected lemma le_Sup (hm : m ∈ ms) : m ≤ Sup ms :=
λ s, le_supr (λm:ms, m.val s) ⟨m, hm⟩

protected lemma Sup_le (hm : ∀m' ∈ ms, m' ≤ m) : Sup ms ≤ m :=
λ s, (supr_le $ assume ⟨m', h'⟩, (hm m' h') s)

instance : has_Inf (outer_measure α) := ⟨λs, Sup {m | ∀m'∈s, m ≤ m'}⟩
protected lemma Inf_le (hm : m ∈ ms) : Inf ms ≤ m := outer_measure.Sup_le $ assume m' h', h' _ hm
protected lemma le_Inf (hm : ∀m' ∈ ms, m ≤ m') : m ≤ Inf ms := outer_measure.le_Sup hm

instance : complete_lattice (outer_measure α) :=
{ top          := Sup univ,
  le_top       := assume a, outer_measure.le_Sup (mem_univ a),
  Sup          := Sup,
  Sup_le       := assume s m, outer_measure.Sup_le,
  le_Sup       := assume s m, outer_measure.le_Sup,
  Inf          := Inf,
  Inf_le       := assume s m, outer_measure.Inf_le,
  le_Inf       := assume s m, outer_measure.le_Inf,
  sup          := λa b, Sup {a, b},
  le_sup_left  := assume a b, outer_measure.le_Sup $ by simp,
  le_sup_right := assume a b, outer_measure.le_Sup $ by simp,
  sup_le       := assume a b c ha hb, outer_measure.Sup_le $
    by simp [or_imp_distrib, ha, hb] {contextual:=tt},
  inf          := λa b, Inf {a, b},
  inf_le_left  := assume a b, outer_measure.Inf_le $ by simp,
  inf_le_right := assume a b, outer_measure.Inf_le $ by simp,
  le_inf       := assume a b c ha hb, outer_measure.le_Inf $
    by simp [or_imp_distrib, ha, hb] {contextual:=tt},
  .. outer_measure.order_bot }

@[simp] theorem Sup_apply (ms : set (outer_measure α)) (s : set α) :
  (Sup ms) s = ⨆ m : ms, m s := rfl

@[simp] theorem supr_apply {ι} (f : ι → outer_measure α) (s : set α) :
  (⨆ i : ι, f i) s = ⨆ i, f i s :=
le_antisymm
  (supr_le $ λ ⟨_, i, rfl⟩, le_supr _ i)
  (supr_le $ λ i, le_supr
    (λ (m : {a : outer_measure α // ∃ i, f i = a}), m.1 s)
    ⟨f i, i, rfl⟩)

@[simp] theorem sup_apply (m₁ m₂ : outer_measure α) (s : set α) :
  (m₁ ⊔ m₂) s = m₁ s ⊔ m₂ s :=
by have := supr_apply (λ b, cond b m₁ m₂) s;
  rwa [supr_bool_eq, supr_bool_eq] at this

end supremum

def map {β} (f : α → β) (m : outer_measure α) : outer_measure β :=
{ measure_of := λs, m (f ⁻¹' s),
  empty := m.empty,
  mono := λ s t h, m.mono (preimage_mono h),
  Union_nat := λ s, by rw [preimage_Union]; exact
    m.Union_nat (λ i, f ⁻¹' s i) }

@[simp] theorem map_apply {β} (f : α → β)
  (m : outer_measure α) (s : set β) : map f m s = m (f ⁻¹' s) := rfl

@[simp] theorem map_id (m : outer_measure α) : map id m = m :=
ext $ λ s, rfl

@[simp] theorem map_map {β γ} (f : α → β) (g : β → γ)
  (m : outer_measure α) : map g (map f m) = map (g ∘ f) m :=
ext $ λ s, rfl

instance : functor outer_measure := {map := λ α β, map}

instance : is_lawful_functor outer_measure :=
{ id_map := λ α, map_id,
  comp_map := λ α β γ f g m, (map_map f g m).symm }

/-- The dirac outer measure. -/
def dirac (a : α) : outer_measure α :=
{ measure_of := λs, ⨆ h : a ∈ s, 1,
  empty := by simp,
  mono := λ s t h, supr_le_supr2 (λ h', ⟨h h', le_refl _⟩),
  Union_nat := λ s, supr_le $ λ h,
    let ⟨i, h⟩ := mem_Union.1 h in
    le_trans (by exact le_supr _ h) (ennreal.le_tsum i) }

@[simp] theorem dirac_apply (a : α) (s : set α) :
  dirac a s = ⨆ h : a ∈ s, 1 := rfl

def sum {ι} (f : ι → outer_measure α) : outer_measure α :=
{ measure_of := λs, ∑' i, f i s,
  empty := by simp,
  mono := λ s t h, ennreal.tsum_le_tsum (λ i, (f i).mono' h),
  Union_nat := λ s, by rw ennreal.tsum_comm; exact
    ennreal.tsum_le_tsum (λ i, (f i).Union_nat _) }

@[simp] theorem sum_apply {ι} (f : ι → outer_measure α) (s : set α) :
  sum f s = ∑' i, f i s := rfl

instance : has_scalar ennreal (outer_measure α) :=
⟨λ a m, {
  measure_of := λs, a * m s,
  empty := by simp,
  mono := λ s t h, canonically_ordered_semiring.mul_le_mul (le_refl _) (m.mono' h),
  Union_nat := λ s, by rw ennreal.tsum_mul_left; exact
    canonically_ordered_semiring.mul_le_mul (le_refl _) (m.Union_nat _) }⟩

@[simp] theorem smul_apply (a : ennreal) (m : outer_measure α) (s : set α) :
  (a • m) s = a * m s := rfl

instance : semimodule ennreal (outer_measure α) :=
{ smul_add := λ a m₁ m₂, ext $ λ s, mul_add _ _ _,
  add_smul := λ a b m, ext $ λ s, add_mul _ _ _,
  mul_smul := λ a b m, ext $ λ s, mul_assoc _ _ _,
  one_smul := λ m, ext $ λ s, one_mul _,
  zero_smul := λ m, ext $ λ s, zero_mul _,
  smul_zero := λ a, ext $ λ s, mul_zero _,
  ..outer_measure.has_scalar }

theorem smul_dirac_apply (a : ennreal) (b : α) (s : set α) :
  (a • dirac b) s = ⨆ h : b ∈ s, a :=
by by_cases b ∈ s; simp [h]

theorem top_apply {s : set α} (h : s.nonempty) : (⊤ : outer_measure α) s = ⊤ :=
let ⟨a, as⟩ := h in
top_unique $ le_supr_of_le ⟨(⊤ : ennreal) • dirac a, trivial⟩ $
by simp [smul_dirac_apply, as]

end basic

section of_function
set_option eqn_compiler.zeta true

/-- Given any function `m` assigning measures to sets satisying `m ∅ = 0`, there is
  a unique maximal outer measure `μ` satisfying `μ s ≤ m s` for all `s : set α`. -/
protected def of_function {α : Type*} (m : set α → ennreal) (m_empty : m ∅ = 0) :
  outer_measure α :=
let μ := λs, ⨅{f : ℕ → set α} (h : s ⊆ ⋃i, f i), ∑'i, m (f i) in
{ measure_of := μ,
  empty      := le_antisymm
    (infi_le_of_le (λ_, ∅) $ infi_le_of_le (empty_subset _) $ by simp [m_empty])
    (zero_le _),
  mono       := assume s₁ s₂ hs, infi_le_infi $ assume f,
    infi_le_infi2 $ assume hb, ⟨subset.trans hs hb, le_refl _⟩,
  Union_nat := assume s, ennreal.le_of_forall_epsilon_le $ begin
    assume ε hε (hb : (∑'i, μ (s i)) < ⊤),
    rcases ennreal.exists_pos_sum_of_encodable (ennreal.coe_lt_coe.2 hε) ℕ with ⟨ε', hε', hl⟩,
    refine le_trans _ (add_le_add_left' (le_of_lt hl)),
    rw ← ennreal.tsum_add,
    choose f hf using show
      ∀i, ∃f:ℕ → set α, s i ⊆ (⋃i, f i) ∧ (∑'i, m (f i)) < μ (s i) + ε' i,
    { intro,
      have : μ (s i) < μ (s i) + ε' i :=
        ennreal.lt_add_right
          (lt_of_le_of_lt (by apply ennreal.le_tsum) hb)
          (by simpa using hε' i),
      simpa [μ, infi_lt_iff] },
    refine le_trans _ (ennreal.tsum_le_tsum $ λ i, le_of_lt (hf i).2),
    rw [← ennreal.tsum_prod, ← tsum_equiv equiv.nat_prod_nat_equiv_nat.symm],
    swap, {apply_instance},
    refine infi_le_of_le _ (infi_le _ _),
    exact Union_subset (λ i, subset.trans (hf i).1 $
      Union_subset $ λ j, subset.trans (by simp) $
      subset_Union _ $ equiv.nat_prod_nat_equiv_nat (i, j)),
  end }

theorem of_function_le {α : Type*} (m : set α → ennreal) (m_empty s) :
  outer_measure.of_function m m_empty s ≤ m s :=
let f : ℕ → set α := λi, nat.rec_on i s (λn s, ∅) in
infi_le_of_le f $ infi_le_of_le (subset_Union f 0) $ le_of_eq $
calc (∑'i, m (f i)) = ({0} : finset ℕ).sum (λi, m (f i)) :
    tsum_eq_sum $ by intro i; cases i; simp [m_empty]
  ... = m s : by simp; refl

theorem le_of_function {α : Type*} {m m_empty} {μ : outer_measure α} :
  μ ≤ outer_measure.of_function m m_empty ↔ ∀ s, μ s ≤ m s :=
⟨λ H s, le_trans (H _) (of_function_le _ _ _),
 λ H s, le_infi $ λ f, le_infi $ λ hs,
  le_trans (μ.mono hs) $ le_trans (μ.Union f) $
  ennreal.tsum_le_tsum $ λ i, H _⟩

end of_function

section caratheodory_measurable
universe u
parameters {α : Type u} (m : outer_measure α)
include m

local attribute [simp] set.inter_comm set.inter_left_comm set.inter_assoc

variables {s s₁ s₂ : set α}

private def C (s : set α) := ∀t, m t = m (t ∩ s) + m (t \ s)

private lemma C_iff_le {s : set α} : C s ↔ ∀t, m (t ∩ s) + m (t \ s) ≤ m t :=
forall_congr $ λ t, le_antisymm_iff.trans $ and_iff_right $
by convert m.union _ _; rw inter_union_diff t s

@[simp] private lemma C_empty : C ∅ := by simp [C, m.empty, diff_empty]

private lemma C_compl : C s₁ → C (- s₁) := by simp [C, diff_eq, add_comm]

@[simp] private lemma C_compl_iff : C (- s) ↔ C s :=
⟨λ h, by simpa using C_compl m h, C_compl⟩

private lemma C_union (h₁ : C s₁) (h₂ : C s₂) : C (s₁ ∪ s₂) :=
λ t, begin
  rw [h₁ t, h₂ (t ∩ s₁), h₂ (t \ s₁), h₁ (t ∩ (s₁ ∪ s₂)),
    inter_diff_assoc _ _ s₁, set.inter_assoc _ _ s₁,
    inter_eq_self_of_subset_right (set.subset_union_left _ _),
    union_diff_left, h₂ (t ∩ s₁)],
  simp [diff_eq, add_assoc]
end

private lemma measure_inter_union (h : s₁ ∩ s₂ ⊆ ∅) (h₁ : C s₁) {t : set α} :
  m (t ∩ (s₁ ∪ s₂)) = m (t ∩ s₁) + m (t ∩ s₂) :=
by rw [h₁, set.inter_assoc, set.union_inter_cancel_left,
  inter_diff_assoc, union_diff_cancel_left h]

private lemma C_Union_lt {s : ℕ → set α} : ∀{n:ℕ}, (∀i<n, C (s i)) → C (⋃i<n, s i)
| 0       h := by simp [nat.not_lt_zero]
| (n + 1) h := by rw Union_lt_succ; exact C_union m
  (h n (le_refl (n + 1)))
      (C_Union_lt $ assume i hi, h i $ lt_of_lt_of_le hi $ nat.le_succ _)

private lemma C_inter (h₁ : C s₁) (h₂ : C s₂) : C (s₁ ∩ s₂) :=
by rw [← C_compl_iff, compl_inter]; from C_union _ (C_compl _ h₁) (C_compl _ h₂)

private lemma C_sum {s : ℕ → set α} (h : ∀i, C (s i)) (hd : pairwise (disjoint on s)) {t : set α} :
  ∀ {n}, (finset.range n).sum (λi, m (t ∩ s i)) = m (t ∩ ⋃i<n, s i)
| 0            := by simp [nat.not_lt_zero, m.empty]
| (nat.succ n) := begin
  simp [Union_lt_succ, range_succ],
  rw [measure_inter_union m _ (h n), C_sum],
  intro a, simpa [range_succ] using λ h₁ i hi h₂, hd _ _ (ne_of_gt hi) ⟨h₁, h₂⟩
end

private lemma C_Union_nat {s : ℕ → set α} (h : ∀i, C (s i))
  (hd : pairwise (disjoint on s)) : C (⋃i, s i) :=
C_iff_le.2 $ λ t, begin
  have hp : m (t ∩ ⋃i, s i) ≤ (⨆n, m (t ∩ ⋃i<n, s i)),
  { convert m.Union (λ i, t ∩ s i),
    { rw inter_Union },
    { simp [ennreal.tsum_eq_supr_nat, C_sum m h hd] } },
  refine le_trans (add_le_add_right' hp) _,
  rw ennreal.supr_add,
  refine supr_le (λ n, le_trans (add_le_add_left' _)
    (ge_of_eq (C_Union_lt m (λ i _, h i) _))),
  refine m.mono (diff_subset_diff_right _),
  exact bUnion_subset (λ i _, subset_Union _ i),
end

private lemma f_Union {s : ℕ → set α} (h : ∀i, C (s i))
  (hd : pairwise (disjoint on s)) : m (⋃i, s i) = ∑'i, m (s i) :=
begin
  refine le_antisymm (m.Union_nat s) _,
  rw ennreal.tsum_eq_supr_nat,
  refine supr_le (λ n, _),
  have := @C_sum _ m _ h hd univ n,
  simp at this, simp [this],
  exact m.mono (bUnion_subset (λ i _, subset_Union _ i)),
end

private def caratheodory_dynkin : measurable_space.dynkin_system α :=
{ has := C,
  has_empty := C_empty,
  has_compl := assume s, C_compl,
  has_Union_nat := assume f hf hn, C_Union_nat hn hf }

/-- Given an outer measure `μ`, the Caratheodory measurable space is
  defined such that `s` is measurable if `∀t, μ t = μ (t ∩ s) + μ (t \ s)`. -/
protected def caratheodory : measurable_space α :=
caratheodory_dynkin.to_measurable_space $ assume s₁ s₂, C_inter

lemma is_caratheodory {s : set α} :
  caratheodory.is_measurable s ↔ ∀t, m t = m (t ∩ s) + m (t \ s) :=
iff.rfl

lemma is_caratheodory_le {s : set α} :
  caratheodory.is_measurable s ↔ ∀t, m (t ∩ s) + m (t \ s) ≤ m t :=
C_iff_le

protected lemma Union_eq_of_caratheodory {s : ℕ → set α}
  (h : ∀i, caratheodory.is_measurable (s i)) (hd : pairwise (disjoint on s)) :
  m (⋃i, s i) = ∑'i, m (s i) :=
f_Union h hd

end caratheodory_measurable

variables {α : Type*}

lemma caratheodory_is_measurable {m : set α → ennreal} {s : set α}
  {h₀ : m ∅ = 0} (hs : ∀t, m (t ∩ s) + m (t \ s) ≤ m t) :
  (outer_measure.of_function m h₀).caratheodory.is_measurable s :=
let o := (outer_measure.of_function m h₀) in
(is_caratheodory_le o).2 $ λ t,
le_infi $ λ f, le_infi $ λ hf, begin
  refine le_trans (add_le_add'
    (infi_le_of_le (λi, f i ∩ s) $ infi_le _ _)
    (infi_le_of_le (λi, f i \ s) $ infi_le _ _)) _,
  { rw ← Union_inter,
    exact inter_subset_inter_left _ hf },
  { rw ← Union_diff,
    exact diff_subset_diff_left hf },
  { rw ← ennreal.tsum_add,
    exact ennreal.tsum_le_tsum (λ i, hs _) }
end

@[simp] theorem zero_caratheodory : (0 : outer_measure α).caratheodory = ⊤ :=
top_unique $ λ s _ t, (add_zero _).symm

theorem top_caratheodory : (⊤ : outer_measure α).caratheodory = ⊤ :=
top_unique $ assume s hs, (is_caratheodory_le _).2 $ assume t,
  t.eq_empty_or_nonempty.elim (λ ht, by simp [ht])
    (λ ht, by simp only [ht, top_apply, le_top])

theorem le_add_caratheodory (m₁ m₂ : outer_measure α) :
  m₁.caratheodory ⊓ m₂.caratheodory ≤ (m₁ + m₂ : outer_measure α).caratheodory :=
λ s ⟨hs₁, hs₂⟩ t, by simp [hs₁ t, hs₂ t, add_left_comm, add_assoc]

theorem le_sum_caratheodory {ι} (m : ι → outer_measure α) :
  (⨅ i, (m i).caratheodory) ≤ (sum m).caratheodory :=
λ s h t, by simp [λ i,
  measurable_space.is_measurable_infi.1 h i t, ennreal.tsum_add]

theorem le_smul_caratheodory (a : ennreal) (m : outer_measure α) :
  m.caratheodory ≤ (a • m).caratheodory :=
λ s h t, by simp [h t, mul_add]

@[simp] theorem dirac_caratheodory (a : α) : (dirac a).caratheodory = ⊤ :=
top_unique $ λ s _ t, begin
  by_cases a ∈ t; simp [h],
  by_cases a ∈ s; simp [h]
end

section Inf_gen

def Inf_gen (m : set (outer_measure α)) (s : set α) : ennreal :=
⨆(h : s.nonempty), ⨅ (μ : outer_measure α) (h : μ ∈ m), μ s

@[simp] lemma Inf_gen_empty (m : set (outer_measure α)) : Inf_gen m ∅ = 0 :=
by simp [Inf_gen, empty_not_nonempty]

lemma Inf_gen_nonempty1 (m : set (outer_measure α)) (t : set α) (h : t.nonempty) :
  Inf_gen m t = (⨅ (μ : outer_measure α) (h : μ ∈ m), μ t) :=
by rw [Inf_gen, supr_pos h]

lemma Inf_gen_nonempty2 (m : set (outer_measure α)) (μ) (h : μ ∈ m) (t) :
  Inf_gen m t = (⨅ (μ : outer_measure α) (h : μ ∈ m), μ t) :=
begin
  cases t.eq_empty_or_nonempty with ht ht,
  { simp [ht],
    refine (bot_unique $ infi_le_of_le μ $ _).symm,
    refine infi_le_of_le h (le_refl ⊥) },
  { exact Inf_gen_nonempty1 m t ht }
end

lemma Inf_eq_of_function_Inf_gen (m : set (outer_measure α)) :
  Inf m = outer_measure.of_function (Inf_gen m) (Inf_gen_empty m) :=
begin
  refine le_antisymm
    (assume t', le_of_function.2 (assume t, _) _)
    (_root_.le_Inf $ assume μ hμ t, le_trans (outer_measure.of_function_le _ _ _) _);
    cases t.eq_empty_or_nonempty with ht ht; simp [ht, Inf_gen_nonempty1],
  { assume μ hμ, exact (show Inf m ≤ μ, from _root_.Inf_le hμ) t },
  { exact infi_le_of_le μ (infi_le _ hμ) }
end

end Inf_gen

end outer_measure

end measure_theory
