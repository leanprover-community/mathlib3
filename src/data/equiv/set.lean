/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import data.equiv.basic
import data.set.function

/-!
# Equivalences and sets

In this file we provide lemmas linking equivalences to sets.

Some notable definitions are:

* `equiv.of_injective`: an injective function is (noncomputably) equivalent to its range.
* `equiv.set_congr`: two equal sets are equivalent as types.
* `equiv.set.union`: a disjoint union of sets is equivalent to their `sum`.

This file is separate from `equiv/basic` such that we do not require the full lattice structure
on sets before defining what an equivalence is.
-/

open function

universes u v w z
variables {α : Sort u} {β : Sort v} {γ : Sort w}

namespace equiv

@[simp] lemma range_eq_univ {α : Type*} {β : Type*} (e : α ≃ β) : set.range e = set.univ :=
set.eq_univ_of_forall e.surjective

protected lemma image_eq_preimage {α β} (e : α ≃ β) (s : set α) : e '' s = e.symm ⁻¹' s :=
set.ext $ assume x, set.mem_image_iff_of_inverse e.left_inv e.right_inv

lemma _root_.set.mem_image_equiv {α β} {S : set α} {f : α ≃ β} {x : β} :
  x ∈ f '' S ↔ f.symm x ∈ S :=
set.ext_iff.mp (f.image_eq_preimage S) x

/-- Alias for `equiv.image_eq_preimage` -/
lemma _root_.set.image_equiv_eq_preimage_symm {α β} (S : set α) (f : α ≃ β) :
  f '' S = f.symm ⁻¹' S :=
f.image_eq_preimage S

/-- Alias for `equiv.image_eq_preimage` -/
lemma _root_.set.preimage_equiv_eq_image_symm {α β} (S : set α) (f : β ≃ α) :
  f ⁻¹' S = f.symm '' S :=
(f.symm.image_eq_preimage S).symm

@[simp] protected lemma subset_image {α β} (e : α ≃ β) (s : set α) (t : set β) :
  e.symm '' t ⊆ s ↔ t ⊆ e '' s :=
by rw [set.image_subset_iff, e.image_eq_preimage]

@[simp] protected lemma subset_image' {α β} (e : α ≃ β) (s : set α) (t : set β) :
  s ⊆ e.symm '' t ↔ e '' s ⊆ t :=
calc s ⊆ e.symm '' t ↔ e.symm.symm '' s ⊆ t : by rw e.symm.subset_image
                 ... ↔ e '' s ⊆ t : by rw e.symm_symm

@[simp] lemma symm_image_image {α β} (e : α ≃ β) (s : set α) : e.symm '' (e '' s) = s :=
e.left_inverse_symm.image_image s

lemma eq_image_iff_symm_image_eq {α β} (e : α ≃ β) (s : set α) (t : set β) :
  t = e '' s ↔ e.symm '' t = s :=
(e.symm.injective.image_injective.eq_iff' (e.symm_image_image s)).symm

@[simp] lemma image_symm_image {α β} (e : α ≃ β) (s : set β) : e '' (e.symm '' s) = s :=
e.symm.symm_image_image s

@[simp] lemma image_preimage {α β} (e : α ≃ β) (s : set β) : e '' (e ⁻¹' s) = s :=
e.surjective.image_preimage s

@[simp] lemma preimage_image {α β} (e : α ≃ β) (s : set α) : e ⁻¹' (e '' s) = s :=
e.injective.preimage_image s

protected lemma image_compl {α β} (f : equiv α β) (s : set α) :
  f '' sᶜ = (f '' s)ᶜ :=
set.image_compl_eq f.bijective

@[simp] lemma symm_preimage_preimage {α β} (e : α ≃ β) (s : set β) :
  e.symm ⁻¹' (e ⁻¹' s) = s :=
e.right_inverse_symm.preimage_preimage s

@[simp] lemma preimage_symm_preimage {α β} (e : α ≃ β) (s : set α) :
  e ⁻¹' (e.symm ⁻¹' s) = s :=
e.left_inverse_symm.preimage_preimage s

@[simp] lemma preimage_subset {α β} (e : α ≃ β) (s t : set β) : e ⁻¹' s ⊆ e ⁻¹' t ↔ s ⊆ t :=
e.surjective.preimage_subset_preimage_iff

@[simp] lemma image_subset {α β} (e : α ≃ β) (s t : set α) : e '' s ⊆ e '' t ↔ s ⊆ t :=
set.image_subset_image_iff e.injective

@[simp] lemma image_eq_iff_eq {α β} (e : α ≃ β) (s t : set α) : e '' s = e '' t ↔ s = t :=
set.image_eq_image e.injective

lemma preimage_eq_iff_eq_image {α β} (e : α ≃ β) (s t) : e ⁻¹' s = t ↔ s = e '' t :=
set.preimage_eq_iff_eq_image e.bijective

lemma eq_preimage_iff_image_eq {α β} (e : α ≃ β) (s t) : s = e ⁻¹' t ↔ e '' s = t :=
set.eq_preimage_iff_image_eq e.bijective

lemma prod_assoc_preimage {α β γ} {s : set α} {t : set β} {u : set γ} :
  equiv.prod_assoc α β γ ⁻¹' s.prod (t.prod u) = (s.prod t).prod u :=
by { ext, simp [and_assoc] }

/-- A set `s` in `α × β` is equivalent to the sigma-type `Σ x, {y | (x, y) ∈ s}`. -/
def set_prod_equiv_sigma {α β : Type*} (s : set (α × β)) :
  s ≃ Σ x : α, {y | (x, y) ∈ s} :=
{ to_fun := λ x, ⟨x.1.1, x.1.2, by simp⟩,
  inv_fun := λ x, ⟨(x.1, x.2.1), x.2.2⟩,
  left_inv := λ ⟨⟨x, y⟩, h⟩, rfl,
  right_inv := λ ⟨x, y, h⟩, rfl }

/-- The subtypes corresponding to equal sets are equivalent. -/
@[simps apply]
def set_congr {α : Type*} {s t : set α} (h : s = t) : s ≃ t :=
subtype_equiv_prop h

/--
A set is equivalent to its image under an equivalence.
-/
-- We could construct this using `equiv.set.image e s e.injective`,
-- but this definition provides an explicit inverse.
@[simps]
def image {α β : Type*} (e : α ≃ β) (s : set α) : s ≃ e '' s :=
{ to_fun := λ x, ⟨e x.1, by simp⟩,
  inv_fun := λ y, ⟨e.symm y.1, by { rcases y with ⟨-, ⟨a, ⟨m, rfl⟩⟩⟩, simpa using m, }⟩,
  left_inv := λ x, by simp,
  right_inv := λ y, by simp, }.

open set

namespace set

/-- `univ α` is equivalent to `α`. -/
@[simps apply symm_apply]
protected def univ (α) : @univ α ≃ α :=
⟨coe, λ a, ⟨a, trivial⟩, λ ⟨a, _⟩, rfl, λ a, rfl⟩

/-- An empty set is equivalent to the `empty` type. -/
protected def empty (α) : (∅ : set α) ≃ empty :=
equiv_empty _

/-- An empty set is equivalent to a `pempty` type. -/
protected def pempty (α) : (∅ : set α) ≃ pempty :=
equiv_pempty _

/-- If sets `s` and `t` are separated by a decidable predicate, then `s ∪ t` is equivalent to
`s ⊕ t`. -/
protected def union' {α} {s t : set α}
  (p : α → Prop) [decidable_pred p]
  (hs : ∀ x ∈ s, p x)
  (ht : ∀ x ∈ t, ¬ p x) : (s ∪ t : set α) ≃ s ⊕ t :=
{ to_fun := λ x, if hp : p x
    then sum.inl ⟨_, x.2.resolve_right (λ xt, ht _ xt hp)⟩
    else sum.inr ⟨_, x.2.resolve_left (λ xs, hp (hs _ xs))⟩,
  inv_fun := λ o, match o with
    | (sum.inl x) := ⟨x, or.inl x.2⟩
    | (sum.inr x) := ⟨x, or.inr x.2⟩
  end,
  left_inv := λ ⟨x, h'⟩, by by_cases p x; simp [union'._match_1, h]; congr,
  right_inv := λ o, begin
    rcases o with ⟨x, h⟩ | ⟨x, h⟩;
    dsimp [union'._match_1];
    [simp [hs _ h], simp [ht _ h]]
  end }

/-- If sets `s` and `t` are disjoint, then `s ∪ t` is equivalent to `s ⊕ t`. -/
protected def union {α} {s t : set α} [decidable_pred (λ x, x ∈ s)] (H : s ∩ t ⊆ ∅) :
  (s ∪ t : set α) ≃ s ⊕ t :=
set.union' (λ x, x ∈ s) (λ _, id) (λ x xt xs, H ⟨xs, xt⟩)

lemma union_apply_left {α} {s t : set α} [decidable_pred (λ x, x ∈ s)] (H : s ∩ t ⊆ ∅)
  {a : (s ∪ t : set α)} (ha : ↑a ∈ s) : equiv.set.union H a = sum.inl ⟨a, ha⟩ :=
dif_pos ha

lemma union_apply_right {α} {s t : set α} [decidable_pred (λ x, x ∈ s)] (H : s ∩ t ⊆ ∅)
  {a : (s ∪ t : set α)} (ha : ↑a ∈ t) : equiv.set.union H a = sum.inr ⟨a, ha⟩ :=
dif_neg $ λ h, H ⟨h, ha⟩

@[simp] lemma union_symm_apply_left {α} {s t : set α} [decidable_pred (λ x, x ∈ s)] (H : s ∩ t ⊆ ∅)
  (a : s) : (equiv.set.union H).symm (sum.inl a) = ⟨a, subset_union_left _ _ a.2⟩ :=
rfl

@[simp] lemma union_symm_apply_right {α} {s t : set α} [decidable_pred (λ x, x ∈ s)] (H : s ∩ t ⊆ ∅)
  (a : t) : (equiv.set.union H).symm (sum.inr a) = ⟨a, subset_union_right _ _ a.2⟩ :=
rfl

/-- A singleton set is equivalent to a `punit` type. -/
protected def singleton {α} (a : α) : ({a} : set α) ≃ punit.{u} :=
⟨λ _, punit.star, λ _, ⟨a, mem_singleton _⟩,
 λ ⟨x, h⟩, by { simp at h, subst x },
 λ ⟨⟩, rfl⟩

/-- Equal sets are equivalent. -/
@[simps apply symm_apply]
protected def of_eq {α : Type u} {s t : set α} (h : s = t) : s ≃ t :=
{ to_fun := λ x, ⟨x, h ▸ x.2⟩,
  inv_fun := λ x, ⟨x, h.symm ▸ x.2⟩,
  left_inv := λ _, subtype.eq rfl,
  right_inv := λ _, subtype.eq rfl }

/-- If `a ∉ s`, then `insert a s` is equivalent to `s ⊕ punit`. -/
protected def insert {α} {s : set.{u} α} [decidable_pred (∈ s)] {a : α} (H : a ∉ s) :
  (insert a s : set α) ≃ s ⊕ punit.{u+1} :=
calc (insert a s : set α) ≃ ↥(s ∪ {a}) : equiv.set.of_eq (by simp)
... ≃ s ⊕ ({a} : set α) : equiv.set.union (by finish [set.subset_def])
... ≃ s ⊕ punit.{u+1} : sum_congr (equiv.refl _) (equiv.set.singleton _)

@[simp] lemma insert_symm_apply_inl {α} {s : set.{u} α} [decidable_pred (∈ s)] {a : α} (H : a ∉ s)
  (b : s) : (equiv.set.insert H).symm (sum.inl b) = ⟨b, or.inr b.2⟩ :=
rfl

@[simp] lemma insert_symm_apply_inr {α} {s : set.{u} α} [decidable_pred (∈ s)] {a : α} (H : a ∉ s)
  (b : punit.{u+1}) : (equiv.set.insert H).symm (sum.inr b) = ⟨a, or.inl rfl⟩ :=
rfl

@[simp] lemma insert_apply_left {α} {s : set.{u} α} [decidable_pred (∈ s)] {a : α} (H : a ∉ s) :
  equiv.set.insert H ⟨a, or.inl rfl⟩ = sum.inr punit.star :=
(equiv.set.insert H).apply_eq_iff_eq_symm_apply.2 rfl

@[simp] lemma insert_apply_right {α} {s : set.{u} α} [decidable_pred (∈ s)] {a : α} (H : a ∉ s)
  (b : s) : equiv.set.insert H ⟨b, or.inr b.2⟩ = sum.inl b :=
(equiv.set.insert H).apply_eq_iff_eq_symm_apply.2 rfl

/-- If `s : set α` is a set with decidable membership, then `s ⊕ sᶜ` is equivalent to `α`. -/
protected def sum_compl {α} (s : set α) [decidable_pred (∈ s)] : s ⊕ (sᶜ : set α) ≃ α :=
calc s ⊕ (sᶜ : set α) ≃ ↥(s ∪ sᶜ) : (equiv.set.union (by simp [set.ext_iff])).symm
... ≃ @univ α : equiv.set.of_eq (by simp)
... ≃ α : equiv.set.univ _

@[simp] lemma sum_compl_apply_inl {α : Type u} (s : set α) [decidable_pred (∈ s)] (x : s) :
  equiv.set.sum_compl s (sum.inl x) = x := rfl

@[simp] lemma sum_compl_apply_inr {α : Type u} (s : set α) [decidable_pred (∈ s)] (x : sᶜ) :
  equiv.set.sum_compl s (sum.inr x) = x := rfl

lemma sum_compl_symm_apply_of_mem {α : Type u} {s : set α} [decidable_pred (∈ s)] {x : α}
  (hx : x ∈ s) : (equiv.set.sum_compl s).symm x = sum.inl ⟨x, hx⟩ :=
have ↑(⟨x, or.inl hx⟩ : (s ∪ sᶜ : set α)) ∈ s, from hx,
by { rw [equiv.set.sum_compl], simpa using set.union_apply_left _ this }

lemma sum_compl_symm_apply_of_not_mem {α : Type u} {s : set α} [decidable_pred (∈ s)] {x : α}
  (hx : x ∉ s) : (equiv.set.sum_compl s).symm x = sum.inr ⟨x, hx⟩ :=
have ↑(⟨x, or.inr hx⟩ : (s ∪ sᶜ : set α)) ∈ sᶜ, from hx,
by { rw [equiv.set.sum_compl], simpa using set.union_apply_right _ this }

@[simp] lemma sum_compl_symm_apply {α : Type*} {s : set α} [decidable_pred (∈ s)] {x : s} :
  (equiv.set.sum_compl s).symm x = sum.inl x :=
by cases x with x hx; exact set.sum_compl_symm_apply_of_mem hx

@[simp] lemma sum_compl_symm_apply_compl {α : Type*} {s : set α}
  [decidable_pred (∈ s)] {x : sᶜ} : (equiv.set.sum_compl s).symm x = sum.inr x :=
by cases x with x hx; exact set.sum_compl_symm_apply_of_not_mem hx

/-- `sum_diff_subset s t` is the natural equivalence between
`s ⊕ (t \ s)` and `t`, where `s` and `t` are two sets. -/
protected def sum_diff_subset {α} {s t : set α} (h : s ⊆ t) [decidable_pred (∈ s)] :
  s ⊕ (t \ s : set α) ≃ t :=
calc s ⊕ (t \ s : set α) ≃ (s ∪ (t \ s) : set α) :
  (equiv.set.union (by simp [inter_diff_self])).symm
... ≃ t : equiv.set.of_eq (by { simp [union_diff_self, union_eq_self_of_subset_left h] })

@[simp] lemma sum_diff_subset_apply_inl
  {α} {s t : set α} (h : s ⊆ t) [decidable_pred (∈ s)] (x : s) :
  equiv.set.sum_diff_subset h (sum.inl x) = inclusion h x := rfl

@[simp] lemma sum_diff_subset_apply_inr
  {α} {s t : set α} (h : s ⊆ t) [decidable_pred (∈ s)] (x : t \ s) :
  equiv.set.sum_diff_subset h (sum.inr x) = inclusion (diff_subset t s) x := rfl

lemma sum_diff_subset_symm_apply_of_mem
  {α} {s t : set α} (h : s ⊆ t) [decidable_pred (∈ s)] {x : t} (hx : x.1 ∈ s) :
  (equiv.set.sum_diff_subset h).symm x = sum.inl ⟨x, hx⟩ :=
begin
  apply (equiv.set.sum_diff_subset h).injective,
  simp only [apply_symm_apply, sum_diff_subset_apply_inl],
  exact subtype.eq rfl,
end

lemma sum_diff_subset_symm_apply_of_not_mem
  {α} {s t : set α} (h : s ⊆ t) [decidable_pred (∈ s)] {x : t} (hx : x.1 ∉ s) :
  (equiv.set.sum_diff_subset h).symm x = sum.inr ⟨x, ⟨x.2, hx⟩⟩  :=
begin
  apply (equiv.set.sum_diff_subset h).injective,
  simp only [apply_symm_apply, sum_diff_subset_apply_inr],
  exact subtype.eq rfl,
end

/-- If `s` is a set with decidable membership, then the sum of `s ∪ t` and `s ∩ t` is equivalent
to `s ⊕ t`. -/
protected def union_sum_inter {α : Type u} (s t : set α) [decidable_pred (∈ s)] :
  (s ∪ t : set α) ⊕ (s ∩ t : set α) ≃ s ⊕ t :=
calc  (s ∪ t : set α) ⊕ (s ∩ t : set α)
    ≃ (s ∪ t \ s : set α) ⊕ (s ∩ t : set α) : by rw [union_diff_self]
... ≃ (s ⊕ (t \ s : set α)) ⊕ (s ∩ t : set α) :
  sum_congr (set.union $ subset_empty_iff.2 (inter_diff_self _ _)) (equiv.refl _)
... ≃ s ⊕ (t \ s : set α) ⊕ (s ∩ t : set α) : sum_assoc _ _ _
... ≃ s ⊕ (t \ s ∪ s ∩ t : set α) : sum_congr (equiv.refl _) begin
    refine (set.union' (∉ s) _ _).symm,
    exacts [λ x hx, hx.2, λ x hx, not_not_intro hx.1]
  end
... ≃ s ⊕ t : by { rw (_ : t \ s ∪ s ∩ t = t), rw [union_comm, inter_comm, inter_union_diff] }

/-- Given an equivalence `e₀` between sets `s : set α` and `t : set β`, the set of equivalences
`e : α ≃ β` such that `e ↑x = ↑(e₀ x)` for each `x : s` is equivalent to the set of equivalences
between `sᶜ` and `tᶜ`. -/
protected def compl {α : Type u} {β : Type v} {s : set α} {t : set β} [decidable_pred (∈ s)]
  [decidable_pred (∈ t)] (e₀ : s ≃ t) :
  {e : α ≃ β // ∀ x : s, e x = e₀ x} ≃ ((sᶜ : set α) ≃ (tᶜ : set β)) :=
{ to_fun := λ e, subtype_equiv e
    (λ a, not_congr $ iff.symm $ maps_to.mem_iff
      (maps_to_iff_exists_map_subtype.2 ⟨e₀, e.2⟩)
      (surj_on.maps_to_compl (surj_on_iff_exists_map_subtype.2
        ⟨t, e₀, subset.refl t, e₀.surjective, e.2⟩) e.1.injective)),
  inv_fun := λ e₁,
    subtype.mk
      (calc α ≃ s ⊕ (sᶜ : set α) : (set.sum_compl s).symm
          ... ≃ t ⊕ (tᶜ : set β) : e₀.sum_congr e₁
          ... ≃ β : set.sum_compl t)
      (λ x, by simp only [sum.map_inl, trans_apply, sum_congr_apply,
        set.sum_compl_apply_inl, set.sum_compl_symm_apply]),
  left_inv := λ e,
    begin
      ext x,
      by_cases hx : x ∈ s,
      { simp only [set.sum_compl_symm_apply_of_mem hx, ←e.prop ⟨x, hx⟩,
          sum.map_inl, sum_congr_apply, trans_apply,
          subtype.coe_mk, set.sum_compl_apply_inl] },
      { simp only [set.sum_compl_symm_apply_of_not_mem hx, sum.map_inr,
          subtype_equiv_apply, set.sum_compl_apply_inr, trans_apply,
          sum_congr_apply, subtype.coe_mk] },
    end,
  right_inv := λ e, equiv.ext $ λ x, by simp only [sum.map_inr, subtype_equiv_apply,
    set.sum_compl_apply_inr, function.comp_app, sum_congr_apply, equiv.coe_trans,
    subtype.coe_eta, subtype.coe_mk, set.sum_compl_symm_apply_compl] }

/-- The set product of two sets is equivalent to the type product of their coercions to types. -/
protected def prod {α β} (s : set α) (t : set β) :
  s.prod t ≃ s × t :=
@subtype_prod_equiv_prod α β s t

/-- If a function `f` is injective on a set `s`, then `s` is equivalent to `f '' s`. -/
protected noncomputable def image_of_inj_on {α β} (f : α → β) (s : set α) (H : inj_on f s) :
  s ≃ (f '' s) :=
⟨λ p, ⟨f p, mem_image_of_mem f p.2⟩,
 λ p, ⟨classical.some p.2, (classical.some_spec p.2).1⟩,
 λ ⟨x, h⟩, subtype.eq (H (classical.some_spec (mem_image_of_mem f h)).1 h
   (classical.some_spec (mem_image_of_mem f h)).2),
 λ ⟨y, h⟩, subtype.eq (classical.some_spec h).2⟩

/-- If `f` is an injective function, then `s` is equivalent to `f '' s`. -/
@[simps apply]
protected noncomputable def image {α β} (f : α → β) (s : set α) (H : injective f) : s ≃ (f '' s) :=
equiv.set.image_of_inj_on f s (H.inj_on s)

@[simp] protected lemma image_symm_apply {α β} (f : α → β) (s : set α) (H : injective f)
  (x : α) (h : x ∈ s) :
  (set.image f s H).symm ⟨f x, ⟨x, ⟨h, rfl⟩⟩⟩ = ⟨x, h⟩ :=
begin
  apply (set.image f s H).injective,
  simp [(set.image f s H).apply_symm_apply],
end

lemma image_symm_preimage {α β} {f : α → β} (hf : injective f) (u s : set α) :
  (λ x, (set.image f s hf).symm x : f '' s → α) ⁻¹' u = coe ⁻¹' (f '' u) :=
begin
  ext ⟨b, a, has, rfl⟩,
  have : ∀(h : ∃a', a' ∈ s ∧ a' = a), classical.some h = a := λ h, (classical.some_spec h).2,
  simp [equiv.set.image, equiv.set.image_of_inj_on, hf.eq_iff, this],
end

/-- If `α` is equivalent to `β`, then `set α` is equivalent to `set β`. -/
@[simps]
protected def congr {α β : Type*} (e : α ≃ β) : set α ≃ set β :=
⟨λ s, e '' s, λ t, e.symm '' t, symm_image_image e, symm_image_image e.symm⟩

/-- The set `{x ∈ s | t x}` is equivalent to the set of `x : s` such that `t x`. -/
protected def sep {α : Type u} (s : set α) (t : α → Prop) :
  ({ x ∈ s | t x } : set α) ≃ { x : s | t x } :=
(equiv.subtype_subtype_equiv_subtype_inter s t).symm

/-- The set `𝒫 S := {x | x ⊆ S}` is equivalent to the type `set S`. -/
protected def powerset {α} (S : set α) : 𝒫 S ≃ set S :=
{ to_fun := λ x : 𝒫 S, coe ⁻¹' (x : set α),
  inv_fun := λ x : set S, ⟨coe '' x, by rintro _ ⟨a : S, _, rfl⟩; exact a.2⟩,
  left_inv := λ x, by ext y; exact ⟨λ ⟨⟨_, _⟩, h, rfl⟩, h, λ h, ⟨⟨_, x.2 h⟩, h, rfl⟩⟩,
  right_inv := λ x, by ext; simp }

/--
If `s` is a set in `range f`,
then its image under `range_splitting f` is in bijection (via `f`) with `s`.
-/
@[simps]
noncomputable def range_splitting_image_equiv {α β : Type*} (f : α → β) (s : set (range f)) :
  range_splitting f '' s ≃ s :=
{ to_fun := λ x, ⟨⟨f x, by simp⟩,
    (by { rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩, simpa [apply_range_splitting f] using m, })⟩,
  inv_fun := λ x, ⟨range_splitting f x, ⟨x, ⟨x.2, rfl⟩⟩⟩,
  left_inv := λ x, by { rcases x with ⟨x, ⟨y, ⟨m, rfl⟩⟩⟩, simp [apply_range_splitting f] },
  right_inv := λ x, by simp [apply_range_splitting f], }

end set


/-- If `f : α → β` has a left-inverse when `α` is nonempty, then `α` is computably equivalent to the
range of `f`.

While awkward, the `nonempty α` hypothesis on `f_inv` and `hf` allows this to be used when `α` is
empty too. This hypothesis is absent on analogous definitions on stronger `equiv`s like
`linear_equiv.of_left_inverse` and `ring_equiv.of_left_inverse` as their typeclass assumptions
are already sufficient to ensure non-emptiness. -/
@[simps]
def of_left_inverse {α β : Sort*}
  (f : α → β) (f_inv : nonempty α → β → α) (hf : Π h : nonempty α, left_inverse (f_inv h) f) :
  α ≃ set.range f :=
{ to_fun := λ a, ⟨f a, a, rfl⟩,
  inv_fun := λ b, f_inv (nonempty_of_exists b.2) b,
  left_inv := λ a, hf ⟨a⟩ a,
  right_inv := λ ⟨b, a, ha⟩, subtype.eq $ show f (f_inv ⟨a⟩ b) = b,
    from eq.trans (congr_arg f $ by exact ha ▸ (hf _ a)) ha }

/-- If `f : α → β` has a left-inverse, then `α` is computably equivalent to the range of `f`.

Note that if `α` is empty, no such `f_inv` exists and so this definition can't be used, unlike
the stronger but less convenient `of_left_inverse`. -/
abbreviation of_left_inverse' {α β : Sort*}
  (f : α → β) (f_inv : β → α) (hf : left_inverse f_inv f) :
  α ≃ set.range f :=
of_left_inverse f (λ _, f_inv) (λ _, hf)

/-- If `f : α → β` is an injective function, then domain `α` is equivalent to the range of `f`. -/
@[simps apply]
noncomputable def of_injective {α β} (f : α → β) (hf : injective f) : α ≃ set.range f :=
equiv.of_left_inverse f
  (λ h, by exactI function.inv_fun f) (λ h, by exactI function.left_inverse_inv_fun hf)

theorem apply_of_injective_symm {α β} (f : α → β) (hf : injective f) (b : set.range f) :
  f ((of_injective f hf).symm b) = b :=
subtype.ext_iff.1 $ (of_injective f hf).apply_symm_apply b

@[simp] theorem of_injective_symm_apply {α β} (f : α → β) (hf : injective f) (a : α) :
  (of_injective f hf).symm ⟨f a, ⟨a, rfl⟩⟩ = a :=
begin
  apply (of_injective f hf).injective,
  simp [apply_of_injective_symm f hf],
end

@[simp] lemma self_comp_of_injective_symm {α β} (f : α → β) (hf : injective f) :
  f ∘ ((of_injective f hf).symm) = coe :=
funext (λ x, apply_of_injective_symm f hf x)

lemma of_left_inverse_eq_of_injective {α β : Type*}
  (f : α → β) (f_inv : nonempty α → β → α) (hf : Π h : nonempty α, left_inverse (f_inv h) f) :
  of_left_inverse f f_inv hf = of_injective f
    ((em (nonempty α)).elim (λ h, (hf h).injective) (λ h _ _ _, by {
      haveI : subsingleton α := subsingleton_of_not_nonempty h, simp })) :=
by { ext, simp }

lemma of_left_inverse'_eq_of_injective {α β : Type*}
  (f : α → β) (f_inv : β → α) (hf : left_inverse f_inv f) :
  of_left_inverse' f f_inv hf = of_injective f hf.injective :=
by { ext, simp }

protected lemma set_forall_iff {α β} (e : α ≃ β) {p : set α → Prop} :
  (∀ a, p a) ↔ (∀ a, p (e ⁻¹' a)) :=
by simpa [equiv.image_eq_preimage] using (equiv.set.congr e).forall_congr_left'

protected lemma preimage_sUnion {α β} (f : α ≃ β) {s : set (set β)} :
  f ⁻¹' (⋃₀ s) = ⋃₀ (_root_.set.image f ⁻¹' s) :=
by { ext x, simp [(equiv.set.congr f).symm.exists_congr_left] }

end equiv

/-- If a function is a bijection between two sets `s` and `t`, then it induces an
equivalence between the types `↥s` and ``↥t`. -/
noncomputable def set.bij_on.equiv {α : Type*} {β : Type*} {s : set α} {t : set β} (f : α → β)
  (h : set.bij_on f s t) : s ≃ t :=
equiv.of_bijective _ h.bijective

/-- The composition of an updated function with an equiv on a subset can be expressed as an
updated function. -/
lemma dite_comp_equiv_update {α : Type*} {β : Sort*} {γ : Sort*} {s : set α} (e : β ≃ s)
  (v : β → γ) (w : α → γ) (j : β) (x : γ) [decidable_eq β] [decidable_eq α]
  [∀ j, decidable (j ∈ s)] :
  (λ (i : α), if h : i ∈ s then (function.update v j x) (e.symm ⟨i, h⟩) else w i) =
  function.update (λ (i : α), if h : i ∈ s then v (e.symm ⟨i, h⟩) else w i) (e j) x :=
begin
  ext i,
  by_cases h : i ∈ s,
  { rw [dif_pos h,
        function.update_apply_equiv_apply, equiv.symm_symm, function.comp,
        function.update_apply, function.update_apply,
        dif_pos h],
    have h_coe : (⟨i, h⟩ : s) = e j ↔ i = e j := subtype.ext_iff.trans (by rw subtype.coe_mk),
    simp_rw h_coe,
    congr, },
  { have : i ≠ e j,
      by { contrapose! h, have : (e j : α) ∈ s := (e j).2, rwa ← h at this },
    simp [h, this] }
end
