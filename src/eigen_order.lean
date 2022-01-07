import order.well_founded_set data.nat.nth
import order.filter.cofinite topology.basic
import topology.uniform_space.compact_convergence
import topology.metric_space.basic
import data.stream.flatten


section

variables {α : Type*} [linear_order α]

noncomputable def set.is_wf.succ {s : set α} (h_wf : s.is_wf) : s → s :=
well_founded.succ h_wf

lemma set.is_wf.lt_succ {s : set α} (h_wf : s.is_wf) {x : s} (hex : ∃ y : s, x < y) :
  x < h_wf.succ x :=
well_founded.lt_succ _ hex

lemma set.is_wf.well_ordered {s : set α} (h_wf : s.is_wf) : is_well_order _ ((<) : s → s → Prop) :=
⟨h_wf⟩

lemma set.is_wf.lt_succ_iff {s : set α} (h_wf : s.is_wf) {x : s} (h : ∃ y, x < y)
  (y : s) : y < h_wf.succ x ↔ y < x ∨ y = x :=
@well_founded.lt_succ_iff _ _ h_wf.well_ordered _ h _


lemma set.is_wf.le_succ {s : set α} (h_wf : s.is_wf) {x z : s} (h_lt : x < z) :
  h_wf.succ x ≤ z :=
begin
  apply le_of_not_lt,
  intro hlt,
  rw h_wf.lt_succ_iff ⟨_, h_lt⟩ at hlt,
  rcases hlt with hzx | rfl,
  { exact lt_irrefl _ (h_lt.trans hzx) },
  { exact lt_irrefl _ h_lt }
end

variables {s : set α} (h_wf : s.is_wf) (h_inf : s.infinite)

noncomputable def enum : ℕ → s
| 0 := ⟨h_wf.min h_inf.nonempty, h_wf.min_mem _⟩
| (k+1) := h_wf.succ (enum k)

lemma infinite_ge (n) : set.infinite {x | enum h_wf h_inf n ≤ x} :=
begin
  induction n with k ih,
  { intro hf, apply h_inf,
    have he : {x : s | x < enum h_wf h_inf 0} = {},
    { ext y,
      simp only [enum, set.mem_empty_eq, not_lt, set.mem_set_of_eq, iff_false],
      apply h_wf.min_le _ y.property },
    have : {x : s | x < enum h_wf h_inf 0} ∪ {x : s | enum h_wf h_inf 0 ≤ x} = set.univ,
    { ext y,
      simp only [lt_or_ge, set.mem_univ, set.mem_union_eq, set.mem_set_of_eq], },
    rw [he, set.empty_union] at this,
    rw this at hf,
    have : s = (set.univ : set s).image subtype.val := by simp,
    rw this,
    exact set.finite.image _ hf },
  { cases ih.nonempty with w hw,
    dsimp at hw,
    have : ∃ x, enum h_wf h_inf k < x,
    { by_contradiction h,
      apply ih,
      convert set.finite_singleton (enum h_wf h_inf k),
      push_neg at h,
      ext y, rw set.mem_singleton_iff, split,
      { intro hy, exact le_antisymm (h _) hy },
      { rintro rfl, apply le_refl } },
    convert set.infinite.diff ih (set.finite_singleton (enum h_wf h_inf k)),
    ext x, show _ ≤ x ↔ _ ≤  _ ∧ ¬ _,
    have := h_wf.lt_succ_iff this x,
    simp only [enum, set.mem_singleton_iff],
    apply not_iff_not.mp, push_neg,
    rw ← not_lt, tauto }
end

lemma infinite_gt (n) : set.infinite {x | enum h_wf h_inf n < x} :=
begin
  intro h,
  apply infinite_ge h_wf h_inf n,
  convert set.finite.union h (set.finite_singleton (enum h_wf h_inf n)),
  ext y, simp only [set.mem_insert_iff, set.mem_set_of_eq, set.union_singleton],
  show _ ≤ y ↔ _,
  convert le_iff_eq_or_lt using 2,
  simp only [eq_iff_iff], tauto
end

lemma exists_greater (n) : ∃ y, enum h_wf h_inf n < y :=
(infinite_gt h_wf h_inf n).nonempty

lemma enum_lt (n) : enum h_wf h_inf n < enum h_wf h_inf (n + 1) :=
begin
  dsimp [enum],
  apply h_wf.lt_succ (exists_greater _ _ _),
end

lemma enum_mono {m n : ℕ} (h : m < n) : enum h_wf h_inf m < enum h_wf h_inf n :=
strict_mono_nat_of_lt_succ (enum_lt _ _) h

lemma nothing_between {n} {z : s} (h_lt : enum h_wf h_inf n < z) :
  enum h_wf h_inf (n+1) ≤ z :=
begin
  dsimp [enum],
  exact h_wf.le_succ h_lt
end


lemma exists_of_le {b : s} {nc : ℕ} (hc : b ≤ enum h_wf h_inf nc) :
  ∃ nb : ℕ, enum h_wf h_inf nb = b :=
begin
  have hex : ∃ n, b ≤ enum h_wf h_inf n := ⟨nc, hc⟩,
  have hle : b ≤ enum h_wf h_inf (nat.find hex) := nat.find_spec hex,
  use nat.find hex,
  apply le_antisymm _ hle,
  cases hcas : nat.find hex with k,
  { simp only [enum, hcas],
    exact h_wf.min_le _ b.property },
  { refine nothing_between _ _ (lt_of_not_ge' (nat.find_min hex _)),
    simp [hcas, nat.lt_succ_self] }
end

noncomputable def enum' : ℕ → α := λ a, enum h_wf h_inf a

lemma enum'_mem (n) : enum' h_wf h_inf n ∈ s := (enum h_wf h_inf n).property

end

section discr
open filter

open_locale topological_space


variables {α : Type*} [conditionally_complete_linear_order α] [topological_space α] [order_topology α]

variables {s : set α} (h_wf : s.is_wf) (h_inf : s.infinite) (h_cpct : is_compact s) {r : α} -- (hr : r ∈ s)

def iso_set (s : set α) (r : α) : Prop := ∀ x ∈ s, x ≠ r → ∃ nhd ∈ 𝓝 x, nhd ∩ s = {x}

variable h_cf : iso_set s r
-- variable (h_cf : ∀ n, tendsto (enum' h_wf h_inf) (cofinite : filter ℕ) (𝓝 (enum' h_wf h_inf n)) → enum' h_wf h_inf n = r)
include h_wf h_inf h_cpct --hr
 h_cf


lemma exists_enum_gt {x : α} (hxs : x ∈ s) (hxr : x < r) (hlt : ∀ y ∈ s, y ≤ r) :
  ∃ n, x < enum' h_wf h_inf n :=
begin
  by_contradiction hn,
  push_neg at hn,
  let t := set.range (λ n, (enum h_wf h_inf n : α)),
  have sup_lt_r : Sup t < r,
  { apply lt_of_not_ge,
    intro hge,
    apply lt_irrefl x,
    refine lt_of_lt_of_le (lt_of_lt_of_le hxr hge) (cSup_le ⟨_, set.mem_range_self 0⟩ _),
    rintros b ⟨n, rfl⟩,
    apply hn },
  have ht : t ⊆ s,
  { intros x hx,
    rcases hx with ⟨i, rfl⟩,
    apply (enum _ _ _).property },
  have t_bdd : bdd_above t := bdd_above.mono ht h_cpct.bdd_above,
  have ht_sup : Sup t ∈ s,
  { apply is_closed.closure_subset h_cpct.is_closed,
    apply closure_mono ht,
    apply cSup_mem_closure ⟨_, set.mem_range_self 0⟩ t_bdd, },
  have h_sup_gt : ∀ n, (enum h_wf h_inf n).val < Sup t,
  { intro n,
    apply lt_of_not_ge,
    intro hge,
    exact lt_irrefl _ (lt_of_le_of_lt
      (le_cSup t_bdd (set.mem_range_self (n+1)))
      (lt_of_le_of_lt hge (enum_lt h_wf h_inf _))) },
  rcases h_cf _ ht_sup (ne_of_lt sup_lt_r) with ⟨nhd, nhd_mem, nhd_inter⟩,
  rcases exists_Ioc_subset_of_mem_nhds nhd_mem ⟨_, h_sup_gt 0⟩ with ⟨v, v_lt, vsub⟩,
  apply not_le_of_lt v_lt,
  apply cSup_le ⟨_, set.mem_range_self 0⟩,
  intros b bmem,
  rw set.mem_range at bmem,
  rcases bmem with ⟨y, rfl⟩,
  apply le_of_not_lt,
  intro hvt,
  have bsup : ↑(enum h_wf h_inf y) < Sup t := h_sup_gt _,
  have bnhd : ↑(enum h_wf h_inf y) ∈ nhd,
  { apply vsub,
    rw set.mem_Ioc,
    exact ⟨hvt, le_of_lt bsup⟩ },
  have beq : ↑(enum h_wf h_inf y) = Sup t,
  { apply set.mem_singleton_iff.mp,
    rw ← nhd_inter,
    exact ⟨bnhd, (enum _ _ _).property⟩ },
  rw beq at bsup,
  exact lt_irrefl _ bsup
end

lemma enum_surj {x : α} (hxs : x ∈ s) (hxr : x < r) (hlt : ∀ y ∈ s, y ≤ r) :
  ∃ n, enum' h_wf h_inf n = x :=
begin
  cases exists_enum_gt h_wf h_inf h_cpct h_cf hxs hxr hlt with w hw,
  have : (⟨x, hxs⟩ : s) < enum _ _ _ := hw,
  rcases exists_of_le h_wf h_inf (le_of_lt this) with ⟨k, hk⟩,
  use k, exact subtype.ext_iff.1 hk
end


end discr

section discr
open filter

def list.head_of_ne_nil {α} : Π {ls : list α}, ls ≠ [] → α
| [] h        := (h rfl).elim
| (a :: ls) _ := a


lemma list.head_of_ne_nil_mem {α} {ls : list α} (h : ls ≠ []) : list.head_of_ne_nil h ∈ ls :=
begin
  cases ls,
  { contradiction },
  { apply list.mem_cons_self }
end

open_locale topological_space

lemma finset.to_list_ne_nil {α} {s : finset α} : s.to_list ≠ [] ↔ s.nonempty :=
begin
  split,
  { intros h,
    use list.head_of_ne_nil h,
    rw ← finset.mem_to_list,
    apply list.head_of_ne_nil_mem },
  { rintro ⟨k, hk⟩ hsl,
    have : k ∈ s.to_list := (finset.mem_to_list _).mpr hk,
    apply list.not_mem_nil k,
    rwa hsl at this }
end

section
variables {α : Type*} -- α is the type of eigenvals
[conditionally_complete_linear_order α] [topological_space α] [order_topology α]
[has_abs α] [add_group α] [covariant_class α α has_add.add has_le.le]


variables {ι : Type*} -- the type of eigenvectors
          {f : ι → α} -- maps an eigenvector to the abs val of its eigenvalue
          (h_pre : ∀ a : α, (f ⁻¹' {a}).finite)
          {z : α}     -- the accumulation point of the image of f (ie zero)
          (h_wf : (set.range f).is_wf)
          (h_inf : (set.range f).infinite)
          (h_cpct : is_compact (set.range f))
          (h_cf : ∀ n, tendsto (enum' h_wf h_inf)
                        (cofinite : filter ℕ)
                        (𝓝 (enum' h_wf h_inf n)) →
                          enum' h_wf h_inf n = z)


noncomputable def enum_dom : ℕ → ι :=
let val := enum h_wf h_inf,
    map' := λ n : ℕ, (h_pre (val n)).to_finset.to_list in
have ∀ n, (map' n) ≠ [],
begin
  intro n,
  cases set.mem_range.mp (enum h_wf h_inf n).property with i hi,
  simp only [map', finset.to_list_ne_nil],
  use i,
  simp [map', val, hi],
end,
stream.flatten map' this

lemma enum_dom_le (n : ℕ) :
  f (enum_dom h_pre h_wf h_inf n) ≤ f (enum_dom h_pre h_wf h_inf (n+1)) :=
begin
  dsimp [enum_dom],
  apply stream.flatten_le,
  { intros n i j hi hj,
    simp only [set.mem_preimage, set.finite.mem_to_finset, set.mem_singleton_iff, finset.mem_to_list] at hi hj,
    rw [hi, hj] },
  { intros n i hi j hj,
    simp only [set.mem_preimage, set.finite.mem_to_finset, set.mem_singleton_iff, finset.mem_to_list] at hi hj,
    rw [hi, hj],
    apply_mod_cast enum_lt }
end

end

end discr
