/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Patrick Massot
-/
import data.set.basic

/-!
# Sets in product and pi types

This file defines the product of sets in `α × β` and in `Π i, α i` along with the diagonal of a
type.

## Main declarations

* `set.prod`: Binary product of sets. For `s : set α`, `t : set β`, we have
  `s.prod t : set (α × β)`.
* `set.diagonal`: Diagonal of a type. `set.diagonal α = {(x, x) | x : α}`.
* `set.pi`: Arbitrary product of sets.
-/

open function

/-- Notation class for product of subobjects (sets, submonoids, subgroups, etc). -/
class has_set_prod (α β : Type*) (γ : out_param Type*) :=
(prod : α → β → γ)

/- This notation binds more strongly than (pre)images, unions and intersections. -/
infixr ` ×ˢ `:82 := has_set_prod.prod

namespace set

/-! ### Cartesian binary product of sets -/

section prod
variables {α β γ δ : Type*} {s s₁ s₂ : set α} {t t₁ t₂ : set β} {a : α} {b : β}

/-- The cartesian product `prod s t` is the set of `(a, b)`
  such that `a ∈ s` and `b ∈ t`. -/
instance : has_set_prod (set α) (set β) (set (α × β)) :=
⟨λ s t, {p | p.1 ∈ s ∧ p.2 ∈ t}⟩

lemma prod_eq (s : set α) (t : set β) : s ×ˢ t = prod.fst ⁻¹' s ∩ prod.snd ⁻¹' t := rfl

lemma mem_prod_eq {p : α × β} : p ∈ s ×ˢ t = (p.1 ∈ s ∧ p.2 ∈ t) := rfl

@[simp] lemma mem_prod {p : α × β} : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

@[simp] lemma prod_mk_mem_set_prod_eq : (a, b) ∈ s ×ˢ t = (a ∈ s ∧ b ∈ t) := rfl

lemma mk_mem_prod (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t := ⟨ha, hb⟩

lemma prod_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ×ˢ t₁ ⊆ s₂ ×ˢ t₂ :=
λ x ⟨h₁, h₂⟩, ⟨hs h₁, ht h₂⟩

@[simp] lemma prod_self_subset_prod_self : s₁ ×ˢ s₁ ⊆ s₂ ×ˢ s₂ ↔ s₁ ⊆ s₂ :=
⟨λ h x hx, (h (mk_mem_prod hx hx)).1, λ h x hx, ⟨h hx.1, h hx.2⟩⟩

@[simp] lemma prod_self_ssubset_prod_self : s₁ ×ˢ s₁ ⊂ s₂ ×ˢ s₂ ↔ s₁ ⊂ s₂ :=
and_congr prod_self_subset_prod_self $ not_congr prod_self_subset_prod_self

lemma prod_subset_iff {P : set (α × β)} : s ×ˢ t ⊆ P ↔ ∀ (x ∈ s) (y ∈ t), (x, y) ∈ P :=
⟨λ h _ hx _ hy, h (mk_mem_prod hx hy), λ h ⟨_, _⟩ hp, h _ hp.1 _ hp.2⟩

lemma forall_prod_set {p : α × β → Prop} : (∀ x ∈ s ×ˢ t, p x) ↔ ∀ (x ∈ s) (y ∈ t), p (x, y) :=
prod_subset_iff

lemma exists_prod_set {p : α × β → Prop} : (∃ x ∈ s ×ˢ t, p x) ↔ ∃ (x ∈ s) (y ∈ t), p (x, y) :=
by simp [and_assoc]

@[simp] lemma prod_empty : s ×ˢ (∅ : set β) = ∅ := by { ext, exact and_false _ }

@[simp] lemma empty_prod : (∅ : set α) ×ˢ t = ∅ := by { ext, exact false_and _ }

@[simp] lemma univ_prod_univ : @univ α ×ˢ @univ β = univ := by { ext, exact true_and _ }

lemma univ_prod {t : set β} : (univ : set α) ×ˢ t = prod.snd ⁻¹' t := by simp [prod_eq]

lemma prod_univ {s : set α} : s ×ˢ (univ : set β) = prod.fst ⁻¹' s := by simp [prod_eq]

@[simp] lemma singleton_prod : ({a} : set α) ×ˢ t = prod.mk a '' t :=
by { ext ⟨x, y⟩, simp [and.left_comm, eq_comm] }

@[simp] lemma prod_singleton : s ×ˢ ({b} : set β) = (λ a, (a, b)) '' s :=
by { ext ⟨x, y⟩, simp [and.left_comm, eq_comm] }

lemma singleton_prod_singleton : ({a} : set α) ×ˢ ({b} : set β) = {(a, b)} :=by simp

@[simp] lemma union_prod : (s₁ ∪ s₂) ×ˢ t = s₁ ×ˢ t ∪ s₂ ×ˢ t :=
by { ext ⟨x, y⟩, simp [or_and_distrib_right] }

@[simp] lemma prod_union : s ×ˢ (t₁ ∪ t₂) = s ×ˢ t₁ ∪ s ×ˢ t₂ :=
by { ext ⟨x, y⟩, simp [and_or_distrib_left] }

lemma prod_inter_prod : s₁ ×ˢ t₁ ∩ s₂ ×ˢ t₂ = (s₁ ∩ s₂) ×ˢ (t₁ ∩ t₂) :=
by { ext ⟨x, y⟩, simp [and_assoc, and.left_comm] }

lemma insert_prod : insert a s ×ˢ t = (prod.mk a '' t) ∪ s ×ˢ t :=
by { ext ⟨x, y⟩, simp [image, iff_def, or_imp_distrib, imp.swap] {contextual := tt} }

lemma prod_insert : s ×ˢ (insert b t) = ((λa, (a, b)) '' s) ∪ s ×ˢ t :=
by { ext ⟨x, y⟩, simp [image, iff_def, or_imp_distrib, imp.swap] {contextual := tt} }

lemma prod_preimage_eq {f : γ → α} {g : δ → β} :
  (f ⁻¹' s) ×ˢ (g ⁻¹' t) = (λ p : γ × δ, (f p.1, g p.2)) ⁻¹' s ×ˢ t := rfl

lemma prod_preimage_left {f : γ → α} :
  (f ⁻¹' s) ×ˢ t = (λ p : γ × β, (f p.1, p.2)) ⁻¹' s ×ˢ t := rfl

lemma prod_preimage_right {g : δ → β} :
  s ×ˢ (g ⁻¹' t) = (λ p : α × δ, (p.1, g p.2)) ⁻¹' s ×ˢ t := rfl

lemma preimage_prod_map_prod (f : α → β) (g : γ → δ) (s : set β) (t : set δ) :
  prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t) :=
rfl

lemma mk_preimage_prod (f : γ → α) (g : γ → β) :
  (λ x, (f x, g x)) ⁻¹' s ×ˢ t = f ⁻¹' s ∩ g ⁻¹' t := rfl

@[simp] lemma mk_preimage_prod_left (hb : b ∈ t) : (λ a, (a, b)) ⁻¹' s ×ˢ t = s :=
by { ext a, simp [hb] }

@[simp] lemma mk_preimage_prod_right (ha : a ∈ s) : prod.mk a ⁻¹' s ×ˢ t = t :=
by { ext b, simp [ha] }

@[simp] lemma mk_preimage_prod_left_eq_empty (hb : b ∉ t) : (λ a, (a, b)) ⁻¹' s ×ˢ t = ∅ :=
by { ext a, simp [hb] }

@[simp] lemma mk_preimage_prod_right_eq_empty (ha : a ∉ s) : prod.mk a ⁻¹' s ×ˢ t = ∅ :=
by { ext b, simp [ha] }

lemma mk_preimage_prod_left_eq_if [decidable_pred (∈ t)] :
  (λ a, (a, b)) ⁻¹' s ×ˢ t = if b ∈ t then s else ∅ :=
by split_ifs; simp [h]

lemma mk_preimage_prod_right_eq_if [decidable_pred (∈ s)] :
  prod.mk a ⁻¹' s ×ˢ t = if a ∈ s then t else ∅ :=
by split_ifs; simp [h]

lemma mk_preimage_prod_left_fn_eq_if [decidable_pred (∈ t)] (f : γ → α) :
  (λ a, (f a, b)) ⁻¹' s ×ˢ t = if b ∈ t then f ⁻¹' s else ∅ :=
by rw [← mk_preimage_prod_left_eq_if, prod_preimage_left, preimage_preimage]

lemma mk_preimage_prod_right_fn_eq_if [decidable_pred (∈ s)] (g : δ → β) :
  (λ b, (a, g b)) ⁻¹' s ×ˢ t = if a ∈ s then g ⁻¹' t else ∅ :=
by rw [← mk_preimage_prod_right_eq_if, prod_preimage_right, preimage_preimage]

lemma preimage_swap_prod {s : set α} {t : set β} : prod.swap ⁻¹' t ×ˢ s = s ×ˢ t :=
by { ext ⟨x, y⟩, simp [and_comm] }

lemma image_swap_prod : prod.swap '' t ×ˢ s = s ×ˢ t :=
by rw [image_swap_eq_preimage_swap, preimage_swap_prod]

lemma prod_image_image_eq {m₁ : α → γ} {m₂ : β → δ} :
  (m₁ '' s) ×ˢ (m₂ '' t) = (λ p : α × β, (m₁ p.1, m₂ p.2)) '' s ×ˢ t :=
ext $ by simp [-exists_and_distrib_right, exists_and_distrib_right.symm, and.left_comm,
  and.assoc, and.comm]

lemma prod_range_range_eq {m₁ : α → γ} {m₂ : β → δ} :
  (range m₁) ×ˢ (range m₂) = range (λ p : α × β, (m₁ p.1, m₂ p.2)) :=
ext $ by simp [range]

@[simp] lemma range_prod_map {m₁ : α → γ} {m₂ : β → δ} :
  range (prod.map m₁ m₂) = (range m₁) ×ˢ (range m₂) :=
prod_range_range_eq.symm

lemma prod_range_univ_eq {m₁ : α → γ} :
  (range m₁) ×ˢ (univ : set β) = range (λ p : α × β, (m₁ p.1, p.2)) :=
ext $ by simp [range]

lemma prod_univ_range_eq {m₂ : β → δ} :
  (univ : set α) ×ˢ (range m₂) = range (λ p : α × β, (p.1, m₂ p.2)) :=
ext $ by simp [range]

lemma range_pair_subset (f : α → β) (g : α → γ) :
  range (λ x, (f x, g x)) ⊆ (range f) ×ˢ (range g) :=
have (λ x, (f x, g x)) = prod.map f g ∘ (λ x, (x, x)), from funext (λ x, rfl),
by { rw [this, ← range_prod_map], apply range_comp_subset_range }

lemma nonempty.prod : s.nonempty → t.nonempty → (s ×ˢ t : set _).nonempty :=
λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨(x, y), ⟨hx, hy⟩⟩

lemma nonempty.fst : (s ×ˢ t : set _).nonempty → s.nonempty := λ ⟨x, hx⟩, ⟨x.1, hx.1⟩
lemma nonempty.snd : (s ×ˢ t : set _).nonempty → t.nonempty := λ ⟨x, hx⟩, ⟨x.2, hx.2⟩

lemma prod_nonempty_iff : (s ×ˢ t : set _).nonempty ↔ s.nonempty ∧ t.nonempty :=
⟨λ h, ⟨h.fst, h.snd⟩, λ h, h.1.prod h.2⟩

lemma prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
by simp only [not_nonempty_iff_eq_empty.symm, prod_nonempty_iff, not_and_distrib]

lemma prod_sub_preimage_iff {W : set γ} {f : α × β → γ} :
  s ×ˢ t ⊆ f ⁻¹' W ↔ ∀ a b, a ∈ s → b ∈ t → f (a, b) ∈ W :=
by simp [subset_def]

lemma image_prod_mk_subset_prod_left (hb : b ∈ t) : (λ a, (a, b)) '' s ⊆ s ×ˢ t :=
by { rintro _ ⟨a, ha, rfl⟩, exact ⟨ha, hb⟩ }

lemma image_prod_mk_subset_prod_right (ha : a ∈ s) : prod.mk a '' t ⊆ s ×ˢ t :=
by { rintro _ ⟨b, hb, rfl⟩, exact ⟨ha, hb⟩ }

lemma prod_subset_preimage_fst (s : set α) (t : set β) : s ×ˢ t ⊆ prod.fst ⁻¹' s :=
inter_subset_left _ _

lemma fst_image_prod_subset (s : set α) (t : set β) : prod.fst '' s ×ˢ t ⊆ s :=
image_subset_iff.2 $ prod_subset_preimage_fst s t

lemma fst_image_prod (s : set β) {t : set α} (ht : t.nonempty) : prod.fst '' s ×ˢ t = s :=
(fst_image_prod_subset _ _).antisymm $ λ y hy, let ⟨x, hx⟩ := ht in ⟨(y, x), ⟨hy, hx⟩, rfl⟩

lemma prod_subset_preimage_snd (s : set α) (t : set β) : s ×ˢ t ⊆ prod.snd ⁻¹' t :=
inter_subset_right _ _

lemma snd_image_prod_subset (s : set α) (t : set β) : prod.snd '' s ×ˢ t ⊆ t :=
image_subset_iff.2 $ prod_subset_preimage_snd s t

lemma snd_image_prod {s : set α} (hs : s.nonempty) (t : set β) : prod.snd '' s ×ˢ t = t :=
(snd_image_prod_subset _ _).antisymm $ λ y y_in, let ⟨x, x_in⟩ := hs in ⟨(x, y), ⟨x_in, y_in⟩, rfl⟩

lemma prod_diff_prod : s ×ˢ t \ s₁ ×ˢ t₁ = s ×ˢ (t \ t₁) ∪ (s \ s₁) ×ˢ t :=
by { ext x, by_cases h₁ : x.1 ∈ s₁; by_cases h₂ : x.2 ∈ t₁; simp * }

/-- A product set is included in a product set if and only factors are included, or a factor of the
first set is empty. -/
lemma prod_subset_prod_iff : s ×ˢ t ⊆ s₁ ×ˢ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ :=
begin
  cases (s ×ˢ t : set _).eq_empty_or_nonempty with h h,
  { simp [h, prod_eq_empty_iff.1 h] },
  have st : s.nonempty ∧ t.nonempty, by rwa [prod_nonempty_iff] at h,
  refine ⟨λ H, or.inl ⟨_, _⟩, _⟩,
  { have := image_subset (prod.fst : α × β → α) H,
    rwa [fst_image_prod _ st.2, fst_image_prod _ (h.mono H).snd] at this },
  { have := image_subset (prod.snd : α × β → β) H,
    rwa [snd_image_prod st.1, snd_image_prod (h.mono H).fst] at this },
  { intro H,
    simp only [st.1.ne_empty, st.2.ne_empty, or_false] at H,
    exact prod_mono H.1 H.2 }
end

@[simp] lemma prod_eq_iff_eq (ht : t.nonempty) : s ×ˢ t = s₁ ×ˢ t ↔ s = s₁ :=
begin
  obtain ⟨b, hb⟩ := ht,
  split,
  { simp only [set.ext_iff],
    intros h a,
    simpa [hb, set.mem_prod] using h (a, b) },
  { rintros rfl,
    refl },
end

@[simp] lemma image_prod (f : α → β → γ) : (λ x : α × β, f x.1 x.2) '' s ×ˢ t = image2 f s t :=
set.ext $ λ a,
⟨ by { rintro ⟨_, _, rfl⟩, exact ⟨_, _, (mem_prod.mp ‹_›).1, (mem_prod.mp ‹_›).2, rfl⟩ },
  by { rintro ⟨_, _, _, _, rfl⟩, exact ⟨(_, _), mem_prod.mpr ⟨‹_›, ‹_›⟩, rfl⟩ }⟩

end prod

/-! ### Diagonal -/

section diagonal
variables {α : Type*}

/-- `diagonal α` is the set of `α × α` consisting of all pairs of the form `(a, a)`. -/
def diagonal (α : Type*) : set (α × α) := {p | p.1 = p.2}

@[simp] lemma mem_diagonal (x : α) : (x, x) ∈ diagonal α := by simp [diagonal]

lemma preimage_coe_coe_diagonal (s : set α) : (prod.map coe coe) ⁻¹' (diagonal α) = diagonal s :=
by { ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩, simp [set.diagonal] }

lemma diagonal_eq_range : diagonal α = range (λ x, (x, x)) :=
by { ext ⟨x, y⟩, simp [diagonal, eq_comm] }

end diagonal

/-! ### Cartesian set-indexed product of sets -/

section pi
variables {ι : Type*} {α β : ι → Type*} {s s₁ s₂ : set ι} {t t₁ t₂ : Π i, set (α i)} {i : ι}

/-- Given an index set `ι` and a family of sets `t : Π i, set (α i)`, `pi s t`
is the set of dependent functions `f : Πa, π a` such that `f a` belongs to `t a`
whenever `a ∈ s`. -/
def pi (s : set ι) (t : Π i, set (α i)) : set (Π i, α i) := {f | ∀ i ∈ s, f i ∈ t i}

@[simp] lemma mem_pi {f : Π i, α i} : f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i := iff.rfl

@[simp] lemma mem_univ_pi {f : Π i, α i} : f ∈ pi univ t ↔ ∀ i, f i ∈ t i := by simp

@[simp] lemma empty_pi (s : Π i, set (α i)) : pi ∅ s = univ := by { ext, simp [pi] }

@[simp] lemma pi_univ (s : set ι) : pi s (λ i, (univ : set (α i))) = univ :=
eq_univ_of_forall $ λ f i hi, mem_univ _

lemma pi_mono (h : ∀ i ∈ s, t₁ i ⊆ t₂ i) : pi s t₁ ⊆ pi s t₂ :=
λ x hx i hi, (h i hi $ hx i hi)

lemma pi_inter_distrib : s.pi (λ i, t i ∩ t₁ i) = s.pi t ∩ s.pi t₁ :=
ext $ λ x, by simp only [forall_and_distrib, mem_pi, mem_inter_eq]

lemma pi_congr (h : s₁ = s₂) (h' : ∀ i ∈ s₁, t₁ i = t₂ i) : s₁.pi t₁ = s₂.pi t₂ :=
h ▸ (ext $ λ x, forall₂_congr $ λ i hi, h' i hi ▸ iff.rfl)

lemma pi_eq_empty (hs : i ∈ s) (ht : t i = ∅) : s.pi t = ∅ :=
by { ext f, simp only [mem_empty_eq, not_forall, iff_false, mem_pi, not_imp],
     exact ⟨i, hs, by simp [ht]⟩ }

lemma univ_pi_eq_empty (ht : t i = ∅) : pi univ t = ∅ := pi_eq_empty (mem_univ i) ht

lemma pi_nonempty_iff : (s.pi t).nonempty ↔ ∀ i, ∃ x, i ∈ s → x ∈ t i :=
by simp [classical.skolem, set.nonempty]

lemma univ_pi_nonempty_iff : (pi univ t).nonempty ↔ ∀ i, (t i).nonempty :=
by simp [classical.skolem, set.nonempty]

lemma pi_eq_empty_iff : s.pi t = ∅ ↔ ∃ i, is_empty (α i) ∨ i ∈ s ∧ t i = ∅ :=
begin
  rw [← not_nonempty_iff_eq_empty, pi_nonempty_iff],
  push_neg,
  refine exists_congr (λ i, ⟨λ h, (is_empty_or_nonempty (α i)).imp_right _, _⟩),
  { rintro ⟨x⟩,
    exact ⟨(h x).1, by simp [eq_empty_iff_forall_not_mem, h]⟩ },
  { rintro (h | h) x,
    { exact h.elim' x },
    { simp [h] } }
end

lemma univ_pi_eq_empty_iff : pi univ t = ∅ ↔ ∃ i, t i = ∅ :=
by simp [← not_nonempty_iff_eq_empty, univ_pi_nonempty_iff]

@[simp] lemma univ_pi_empty [h : nonempty ι] : pi univ (λ i, ∅ : Π i, set (α i)) = ∅ :=
univ_pi_eq_empty_iff.2 $ h.elim $ λ x, ⟨x, rfl⟩

@[simp] lemma range_dcomp (f : Π i, α i → β i) :
  range (λ (g : Π i, α i), (λ i, f i (g i))) = pi univ (λ i, range (f i)) :=
begin
  apply subset.antisymm _ (λ x hx, _),
  { rintro _ ⟨x, rfl⟩ i -,
    exact ⟨x i, rfl⟩ },
  { choose y hy using hx,
    exact ⟨λ i, y i trivial, funext $ λ i, hy i trivial⟩ }
end

@[simp] lemma insert_pi (i : ι) (s : set ι) (t : Π i, set (α i)) :
  pi (insert i s) t = (eval i ⁻¹' t i) ∩ pi s t :=
by { ext, simp [pi, or_imp_distrib, forall_and_distrib] }

@[simp] lemma singleton_pi (i : ι) (t : Π i, set (α i)) : pi {i} t = (eval i ⁻¹' t i) :=
by { ext, simp [pi] }

lemma singleton_pi' (i : ι) (t : Π i, set (α i)) : pi {i} t = {x | x i ∈ t i} := singleton_pi i t

lemma pi_if {p : ι → Prop} [h : decidable_pred p] (s : set ι) (t₁ t₂ : Π i, set (α i)) :
  pi s (λ i, if p i then t₁ i else t₂ i) = pi {i ∈ s | p i} t₁ ∩ pi {i ∈ s | ¬ p i} t₂ :=
begin
  ext f,
  refine ⟨λ h, _, _⟩,
  { split; { rintro i ⟨his, hpi⟩, simpa [*] using h i } },
  { rintro ⟨ht₁, ht₂⟩ i his,
    by_cases p i; simp * at * }
end

lemma union_pi : (s₁ ∪ s₂).pi t = s₁.pi t ∩ s₂.pi t :=
by simp [pi, or_imp_distrib, forall_and_distrib, set_of_and]

@[simp] lemma pi_inter_compl (s : set ι) : pi s t ∩ pi sᶜ t = pi univ t :=
by rw [← union_pi, union_compl_self]

lemma pi_update_of_not_mem [decidable_eq ι] (hi : i ∉ s) (f : Π j, α j) (a : α i)
  (t : Π j, α j → set (β j)) :
  s.pi (λ j, t j (update f i a j)) = s.pi (λ j, t j (f j)) :=
pi_congr rfl $ λ j hj, by { rw update_noteq, exact λ h, hi (h ▸ hj) }

lemma pi_update_of_mem [decidable_eq ι] (hi : i ∈ s) (f : Π j, α j) (a : α i)
  (t : Π j, α j → set (β j)) :
  s.pi (λ j, t j (update f i a j)) = {x | x i ∈ t i a} ∩ (s \ {i}).pi (λ j, t j (f j)) :=
calc s.pi (λ j, t j (update f i a j)) = ({i} ∪ s \ {i}).pi (λ j, t j (update f i a j)) :
  by rw [union_diff_self, union_eq_self_of_subset_left (singleton_subset_iff.2 hi)]
... = {x | x i ∈ t i a} ∩ (s \ {i}).pi (λ j, t j (f j)) :
  by { rw [union_pi, singleton_pi', update_same, pi_update_of_not_mem], simp }

lemma univ_pi_update [decidable_eq ι] {β : Π i, Type*} (i : ι) (f : Π j, α j) (a : α i)
  (t : Π j, α j → set (β j)) :
  pi univ (λ j, t j (update f i a j)) = {x | x i ∈ t i a} ∩ pi {i}ᶜ (λ j, t j (f j)) :=
by rw [compl_eq_univ_diff, ← pi_update_of_mem (mem_univ _)]

lemma univ_pi_update_univ [decidable_eq ι] (i : ι) (s : set (α i)) :
  pi univ (update (λ j : ι, (univ : set (α j))) i s) = eval i ⁻¹' s :=
by rw [univ_pi_update i (λ j, (univ : set (α j))) s (λ j t, t), pi_univ, inter_univ, preimage]

lemma eval_image_pi_subset (hs : i ∈ s) : eval i '' s.pi t ⊆ t i :=
image_subset_iff.2 $ λ f hf, hf i hs

lemma eval_image_univ_pi_subset : eval i '' pi univ t ⊆ t i :=
eval_image_pi_subset (mem_univ i)

lemma eval_image_pi (hs : i ∈ s) (ht : (s.pi t).nonempty) : eval i '' s.pi t = t i :=
begin
  refine (eval_image_pi_subset hs).antisymm _,
  classical,
  obtain ⟨f, hf⟩ := ht,
  refine λ y hy, ⟨update f i y, λ j hj, _, update_same _ _ _⟩,
  obtain rfl | hji := eq_or_ne j i; simp [*, hf _ hj]
end

@[simp] lemma eval_image_univ_pi (ht : (pi univ t).nonempty) :
  (λ f : Π i, α i, f i) '' pi univ t = t i :=
eval_image_pi (mem_univ i) ht

lemma eval_preimage [decidable_eq ι] {s : set (α i)} :
  eval i ⁻¹' s = pi univ (update (λ i, univ) i s) :=
by { ext x, simp [@forall_update_iff _ (λ i, set (α i)) _ _ _ _ (λ i' y, x i' ∈ y)] }

lemma eval_preimage' [decidable_eq ι] {s : set (α i)} :
  eval i ⁻¹' s = pi {i} (update (λ i, univ) i s) :=
by { ext, simp }

lemma update_preimage_pi [decidable_eq ι] {f : Π i, α i} (hi : i ∈ s)
  (hf : ∀ j ∈ s, j ≠ i → f j ∈ t j) :
  (update f i) ⁻¹' s.pi t = t i :=
begin
  ext x,
  refine ⟨λ h, _, λ hx j hj, _⟩,
  { convert h i hi,
    simp },
  { obtain rfl | h := eq_or_ne j i,
    { simpa },
    { rw update_noteq h,
      exact hf j hj h } }
end

lemma update_preimage_univ_pi [decidable_eq ι] {f : Π i, α i} (hf : ∀ j ≠ i, f j ∈ t j) :
  (update f i) ⁻¹' pi univ t = t i :=
update_preimage_pi (mem_univ i) (λ j _, hf j)

lemma subset_pi_eval_image (s : set ι) (u : set (Π i, α i)) : u ⊆ pi s (λ i, eval i '' u) :=
λ f hf i hi, ⟨f, hf, rfl⟩

lemma univ_pi_ite (s : set ι) [decidable_pred (∈ s)] (t : Π i, set (α i)) :
  pi univ (λ i, if i ∈ s then t i else univ) = s.pi t :=
by { ext, simp_rw [mem_univ_pi], refine forall_congr (λ i, _), split_ifs; simp [h] }

end pi
end set
