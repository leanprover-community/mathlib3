/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.set.finite
import data.fintype.basic
import order.well_founded
import order.order_iso_nat

/-!
# Well-founded sets

A well-founded subset of an ordered type is one on which the relation `<` is well-founded.

## Main Definitions
 * `set.well_founded_on s r` indicates that the relation `r` is
  well-founded when restricted to the set `s`.
 * `set.is_wf s` indicates that `<` is well-founded when restricted to `s`.notation

## Main Results
 * `set.well_founded_on_iff` relates `well_founded_on` to the well-foundedness of a relation on the
 original type, to avoid dealing with subtypes.
 * `set.is_wf.mono` shows that a subset of a well-founded subset is well-founded.
 * `set.is_wf.union` shows that the union of two well-founded subsets is well-founded.
 * `finset.is_wf` shows that all `finset`s are well-founded.

-/

variables {α : Type*}

namespace set

/-- `s.well_founded_on r` indicates that the relation `r` is well-founded when restricted to `s`. -/
def well_founded_on (s : set α) (r : α → α → Prop) : Prop :=
well_founded (λ (a : s) (b : s), r a b)

lemma well_founded_on_iff {s : set α} {r : α → α → Prop} :
  s.well_founded_on r ↔ well_founded (λ (a b : α), r a b ∧ a ∈ s ∧ b ∈ s) :=
begin
  have f : rel_embedding (λ (a : s) (b : s), r a b) (λ (a b : α), r a b ∧ a ∈ s ∧ b ∈ s) :=
    ⟨⟨coe, subtype.coe_injective⟩, λ a b, by simp⟩,
  refine ⟨λ h, _, f.well_founded⟩,
  rw well_founded.well_founded_iff_has_min,
  intros t ht,
  by_cases hst : (s ∩ t).nonempty,
  { rw ← subtype.preimage_coe_nonempty at hst,
    rcases well_founded.well_founded_iff_has_min.1 h (coe ⁻¹' t) hst with ⟨⟨m, ms⟩, mt, hm⟩,
    exact ⟨m, mt, λ x xt ⟨xm, xs, ms⟩, hm ⟨x, xs⟩ xt xm⟩ },
  { rcases ht with ⟨m, mt⟩,
    exact ⟨m, mt, λ x xt ⟨xm, xs, ms⟩, hst ⟨m, ⟨ms, mt⟩⟩⟩ }
end

section has_lt
variables [has_lt α]

/-- `s.is_wf` indicates that `<` is well-founded when restricted to `s`. -/
def is_wf (s : set α) : Prop := well_founded_on s (<)

variables {s t : set α}

theorem is_wf.mono (h : is_wf t) (st : s ⊆ t) : is_wf s :=
begin
  rw [is_wf, well_founded_on_iff] at *,
  refine subrelation.wf (λ x y xy, _) h,
  exact ⟨xy.1, st xy.2.1, st xy.2.2⟩,
end
end has_lt

section partial_order
variables [partial_order α] {s t : set α} {a : α}

theorem is_wf_iff_no_descending_seq :
  is_wf s ↔ ∀ (f : (order_dual ℕ) ↪o α), ¬ (range f) ⊆ s :=
begin
  haveI : is_strict_order α (λ (a b : α), a < b ∧ a ∈ s ∧ b ∈ s) := {
    to_is_irrefl := ⟨λ x con, lt_irrefl x con.1⟩,
    to_is_trans := ⟨λ a b c ab bc, ⟨lt_trans ab.1 bc.1, ab.2.1, bc.2.2⟩⟩,
  },
  rw [is_wf, well_founded_on_iff, rel_embedding.well_founded_iff_no_descending_seq],
  refine ⟨λ h f con, h begin
    use f,
      { exact f.injective },
      { intros a b,
        simp only [con (mem_range_self a), con (mem_range_self b), and_true, gt_iff_lt,
          function.embedding.coe_fn_mk, order_embedding.lt_iff_lt],
        refl } end, λ h con, _⟩,
  rcases con with ⟨f, hf⟩,
  have hfs' : ∀ n : ℕ, f n ∈ s := λ n, (hf.2 n.lt_succ_self).2.2,
  refine h ⟨f, λ a b, _⟩ (λ n hn, _),
  { split; intro hle,
    { cases lt_or_eq_of_le hle with hlt heq,
      { exact le_of_lt (hf.1 ⟨hlt, hfs' _, hfs' _⟩) },
      { rw [f.injective heq] } },
    { cases lt_or_eq_of_le hle with hlt heq,
      { exact le_of_lt (hf.2 hlt).1, },
      { rw [heq] } } },
  { rcases set.mem_range.1 hn with ⟨m, hm⟩,
    rw ← hm,
    apply hfs' }
end

theorem is_wf.union (hs : is_wf s) (ht : is_wf t) : is_wf (s ∪ t) :=
begin
  classical,
  rw [is_wf_iff_no_descending_seq] at *,
  rintros f fst,
  have h : infinite (f ⁻¹' s) ∨ infinite (f ⁻¹' t),
  { have h : infinite (univ : set ℕ) := infinite_univ,
    have hpre : f ⁻¹' (s ∪ t) = set.univ,
    { rw [← image_univ, image_subset_iff, univ_subset_iff] at fst,
      exact fst },
    rw preimage_union at hpre,
    rw ← hpre at h,
    rw [infinite, infinite],
    rw infinite at h,
    contrapose! h,
    exact finite.union h.1 h.2, },
  rw [← infinite_coe_iff, ← infinite_coe_iff] at h,
  cases h with inf inf; haveI := inf,
  { apply hs ((nat.order_embedding_of_set (f ⁻¹' s)).dual.trans f),
    change range (function.comp f (nat.order_embedding_of_set (f ⁻¹' s))) ⊆ s,
    rw [range_comp, image_subset_iff],
      simp },
  { apply ht ((nat.order_embedding_of_set (f ⁻¹' t)).dual.trans f),
    change range (function.comp f (nat.order_embedding_of_set (f ⁻¹' t))) ⊆ t,
    rw [range_comp, image_subset_iff],
      simp }
end
end partial_order

end set

@[simp]
theorem finset.is_wf [partial_order α] {f : finset α} : set.is_wf (↑f : set α) :=
fintype.preorder.well_founded

namespace set
variables [partial_order α] {s : set α} {a : α}

@[simp]
theorem is_wf_singleton : is_wf ({a} : set α) :=
by simp [← finset.coe_singleton]

theorem is_wf.insert (hs : is_wf s) : is_wf (insert a s) :=
by { rw ← union_singleton, exact hs.union is_wf_singleton }

end set

lemma set.infinite.nonempty {s : set α} (h : s.infinite) : s.nonempty :=
begin
  haveI := set.infinite_coe_iff.2 h,
  exact set.nonempty_of_nonempty_subtype
end

lemma not_well_founded_swap_of_infinite_of_well_order_aux
  {r : α → α → Prop} [is_well_order α r] {a : α} (h_inf : ({x : α | r a x}).infinite) :
  {x : α | r ((is_well_order.wf : well_founded r).succ a) x}.infinite :=
begin
  have h_nonempty : ∃ x, r a x := h_inf.nonempty,
  intro con,
  apply h_inf,
  convert con.insert ((is_well_order.wf : well_founded r).succ a),
  ext x,
  simp only [set.mem_insert_iff, set.mem_set_of_eq],
  split; intro h,
  { rcases is_trichotomous.trichotomous x ((is_well_order.wf : well_founded r).succ a) with c1 | c,
    { exfalso,
      cases (well_founded.lt_succ_iff h_nonempty x).1 c1 with hlt heq,
      { exact is_asymm.asymm _ _ hlt h },
      { rw heq at h,
        have h_irr : is_irrefl α r := infer_instance,
        have h_irr' := h_irr.irrefl,
        exact h_irr' a h, } },
    { exact c },
    { apply_instance }, },
  { rcases h with rfl | h,
    { exact (is_well_order.wf : well_founded r).lt_succ h_nonempty },
    { exact is_trans.trans _ _ _ ((is_well_order.wf : well_founded r).lt_succ h_nonempty) h } }
end

theorem not_well_founded_swap_of_infinite_of_well_order
  [infinite α] {r : α → α → Prop} [is_well_order α r] :
  ¬ well_founded (function.swap r) :=
begin
  haveI : is_strict_order α (function.swap r) := is_strict_order.swap _,
  let m := (is_well_order.wf : well_founded r).min set.univ (set.univ_nonempty),
  have hm : { x | r m x }.infinite,
  { intro con,
    have h : (set.univ : set α).infinite := set.infinite_univ,
      apply h,
      convert con.insert m,
      ext x,
      simp only [set.mem_insert_iff, true_iff, set.mem_univ, set.mem_set_of_eq],
      rcases is_trichotomous.trichotomous x m with c1 | c,
      { exfalso,
        exact well_founded.not_lt_min _ set.univ _ (set.mem_univ x) c1 },
      { exact c },
      { apply_instance } },
  rw [rel_embedding.well_founded_iff_no_descending_seq, not_not],
  let f : ℕ → { a : α | ({x : α | r a x}).infinite },
  { apply nat.rec,
    { exact ⟨m, hm⟩ },
    { exact λ _ x, ⟨_, not_well_founded_swap_of_infinite_of_well_order_aux x.2⟩ } },
  refine ⟨rel_embedding.swap (rel_embedding.nat_lt (function.comp coe f) _)⟩,
  intro n,
  simp only [nat.rec_add_one, function.comp_app, subtype.coe_mk, subtype.val_eq_coe],
  exact well_founded.lt_succ _ (set.infinite.nonempty (subtype.coe_prop (f n))),
end

namespace set

variables [add_cancel_comm_monoid α] (s t : set α) (a : α)

/-- `set.add_antidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
  that add to `a`. -/
def add_antidiagonal : set (α × α) := { x | x.1 + x.2 = a ∧ x.1 ∈ s ∧ x.2 ∈ t }

namespace add_antidiagonal

variables {s} {t} {a}

lemma fst_eq_fst_iff_snd_eq_snd {x y : (add_antidiagonal s t a)} :
  (x : α × α).fst = (y : α × α).fst ↔ (x : α × α).snd = (y : α × α).snd :=
⟨λ h, begin
  have hx := x.2.1,
  rw [subtype.val_eq_coe, h] at hx,
  apply add_left_cancel (hx.trans y.2.1.symm),
end, λ h, begin
  have hx := x.2.1,
  rw [subtype.val_eq_coe, h] at hx,
  apply add_right_cancel (hx.trans y.2.1.symm),
end⟩

lemma eq_of_fst_eq_fst {x y : (add_antidiagonal s t a)}
  (h : (x : α × α).fst = (y : α × α).fst) : x = y :=
subtype.ext (prod.ext h (add_antidiagonal.fst_eq_fst_iff_snd_eq_snd.1 h))

lemma eq_of_snd_eq_snd {x y : (add_antidiagonal s t a)}
  (h : (x : α × α).snd = (y : α × α).snd) : x = y :=
subtype.ext (prod.ext (add_antidiagonal.fst_eq_fst_iff_snd_eq_snd.2 h) h)

end add_antidiagonal
end set

namespace set
namespace add_antidiagonal

variables [linear_ordered_cancel_add_comm_monoid α] (s t : set α) (a : α)

/-- The relation on `set.add_antidagonal s t a` given by `<` on the first coordinate. -/
def lt_left (x y : add_antidiagonal s t a) : Prop := (x : α × α).1 < (y : α × α).1

/-- `set.add_antidiagonal s t a` ordered by `lt_left` embeds into `s` -/
def fst_rel_embedding : (lt_left s t a) ↪r ((<) : s → s → Prop) :=
⟨⟨λ x, ⟨(↑x : α × α).1, x.2.2.1⟩, λ x y hxy,
    add_antidiagonal.eq_of_fst_eq_fst (subtype.mk_eq_mk.1 hxy)⟩, λ x y, iff.refl _⟩

/-- `set.add_antidiagonal s t a` ordered by `lt_left` embeds into the dual of `t` -/
def snd_rel_embedding : (lt_left s t a) ↪r ((>) : t → t → Prop) :=
⟨⟨λ x, ⟨(↑x : α × α).2, x.2.2.2⟩, λ x y hxy,
    add_antidiagonal.eq_of_snd_eq_snd (subtype.mk_eq_mk.1 hxy)⟩, λ x y, begin
  simp only [lt_left, subtype.mk_lt_mk, gt_iff_lt, function.embedding.coe_fn_mk],
  split; intro h,
  { by_contra hle,
    rw not_lt at hle,
    have h := add_lt_add_of_le_of_lt hle h,
    rw [← subtype.val_eq_coe, ← subtype.val_eq_coe, x.2.1, y.2.1] at h,
    exact lt_irrefl a h },
  { by_contra hle,
    rw not_lt at hle,
    have h := add_lt_add_of_le_of_lt hle h,
    rw [← subtype.val_eq_coe, ← subtype.val_eq_coe, add_comm, x.2.1, add_comm, y.2.1] at h,
    exact lt_irrefl a h }
end⟩

variables {s} {t}

theorem finite_of_is_wf (hs : s.is_wf) (ht : t.is_wf) (a) :
  (add_antidiagonal s t a).finite :=
begin
  by_contra h,
  rw [← set.infinite, ← infinite_coe_iff] at h,
  haveI := h,
  haveI : is_well_order s (<) := {
    wf := hs,
    .. (infer_instance : is_strict_total_order _ _),
  },
  haveI : is_well_order (add_antidiagonal s t a) (lt_left s t a) :=
    (add_antidiagonal.fst_rel_embedding s t a).is_well_order,
  have hwf : well_founded
    (function.swap (lt_left s t a)) :=
    (add_antidiagonal.snd_rel_embedding s t a).swap.well_founded ht,
  exact not_well_founded_swap_of_infinite_of_well_order (hwf),
end

end add_antidiagonal
end set

/-- `finset.add_antidiagonal_of_is_wf hs ht a` is the set of all pairs of an element in
  `s` and an element in `t` that add to `a`, but its construction requires proofs `hs` and `ht` that
  `s` and `t` are well-ordered. -/
noncomputable def finset.add_antidiagonal_of_is_wf [linear_ordered_cancel_add_comm_monoid α]
  {s t : set α} (hs : s.is_wf) (ht : t.is_wf) (a : α) :
  finset (α × α) :=
(set.add_antidiagonal.finite_of_is_wf hs ht a).to_finset
