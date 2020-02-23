/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

(Least / Greatest) upper / lower bounds
-/
import algebra.order_functions data.set.intervals.basic
open set lattice

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {a a₁ a₂ : α} {b b₁ b₂ : β} {s t : set α}

section preorder

variables [preorder α] [preorder β] {f : α → β}

/-- The set of upper bounds of a set. -/
def upper_bounds (s : set α) : set α := { x | ∀ ⦃a⦄, a ∈ s →  a ≤ x }
/-- The set of lower bounds of a set. -/
def lower_bounds (s : set α) : set α := { x | ∀ ⦃a⦄, a ∈ s → x ≤ a }
/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
def is_least (s : set α) (a : α) : Prop := a ∈ s ∧ a ∈ lower_bounds s
/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists -/
def is_greatest (s : set α) (a : α) : Prop := a ∈ s ∧ a ∈ upper_bounds s
/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
def is_lub (s : set α) : α → Prop := is_least (upper_bounds s)
/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/
def is_glb (s : set α) : α → Prop := is_greatest (lower_bounds s)

lemma upper_bounds_mono (h₁ : a₁ ≤ a₂) (h₂ : a₁ ∈ upper_bounds s) : a₂ ∈ upper_bounds s :=
λ a h, le_trans (h₂ h) h₁

lemma lower_bounds_mono (h₁ : a₂ ≤ a₁) (h₂ : a₁ ∈ lower_bounds s) : a₂ ∈ lower_bounds s :=
λ a h, le_trans h₁ (h₂ h)

lemma mem_upper_bounds_image (Hf : monotone f) (Ha : a ∈ upper_bounds s) :
  f a ∈ upper_bounds (f '' s) :=
ball_image_of_ball (assume x H, Hf (Ha ‹x ∈ s›))

lemma mem_lower_bounds_image (Hf : monotone f) (Ha : a ∈ lower_bounds s) :
  f a ∈ lower_bounds (f '' s) :=
ball_image_of_ball (assume x H, Hf (Ha ‹x ∈ s›))

lemma is_lub_singleton {a : α} : is_lub {a} a :=
by simp [is_lub, is_least, upper_bounds, lower_bounds] {contextual := tt}

lemma is_glb_singleton {a : α} : is_glb {a} a :=
by simp [is_glb, is_greatest, upper_bounds, lower_bounds] {contextual := tt}

lemma is_glb_Ici : is_glb (Ici a) a :=
⟨λx hx, hx, λy hy, hy left_mem_Ici⟩

lemma is_glb_Icc (h : a₁ ≤ a₂) : is_glb (Icc a₁ a₂) a₁ :=
⟨λx hx, hx.1, λy hy, hy (left_mem_Icc.mpr h)⟩

lemma is_glb_Ico (h : a₁ < a₂) : is_glb (Ico a₁ a₂) a₁ :=
⟨λx hx, hx.1, λy hy, hy (left_mem_Ico.mpr h)⟩

lemma is_lub_Iic : is_lub (Iic a) a :=
⟨λx hx, hx, λy hy, hy right_mem_Iic⟩

lemma is_lub_Icc (h : a₁ ≤ a₂) : is_lub (Icc a₁ a₂) a₂ :=
⟨λx hx, hx.2, λy hy, hy (right_mem_Icc.mpr h)⟩

lemma is_lub_Ioc (h : a₁ < a₂) : is_lub (Ioc a₁ a₂) a₂ :=
⟨λx hx, hx.2, λy hy, hy (right_mem_Ioc.mpr h)⟩

end preorder

section partial_order
variables [partial_order α]

lemma eq_of_is_least_of_is_least (Ha : is_least s a₁) (Hb : is_least s a₂) : a₁ = a₂ :=
le_antisymm (Ha.right Hb.left) (Hb.right Ha.left)

lemma is_least_iff_eq_of_is_least (Ha : is_least s a₁) : is_least s a₂ ↔ a₁ = a₂ :=
iff.intro (eq_of_is_least_of_is_least Ha) (assume h, h ▸ Ha)

lemma eq_of_is_greatest_of_is_greatest (Ha : is_greatest s a₁) (Hb : is_greatest s a₂) : a₁ = a₂ :=
le_antisymm (Hb.right Ha.left) (Ha.right Hb.left)

lemma is_greatest_iff_eq_of_is_greatest (Ha : is_greatest s a₁) : is_greatest s a₂ ↔ a₁ = a₂ :=
iff.intro (eq_of_is_greatest_of_is_greatest Ha) (assume h, h ▸ Ha)

lemma eq_of_is_lub_of_is_lub : is_lub s a₁ → is_lub s a₂ → a₁ = a₂ :=
eq_of_is_least_of_is_least

lemma is_lub_iff_eq_of_is_lub : is_lub s a₁ → (is_lub s a₂ ↔ a₁ = a₂) :=
is_least_iff_eq_of_is_least

lemma is_lub_le_iff (h : is_lub s a₁) : a₁ ≤ a₂ ↔ a₂ ∈ upper_bounds s :=
⟨λ hl, upper_bounds_mono hl h.1, λ hr, h.2 hr⟩

lemma le_is_glb_iff (h : is_glb s a₁) : a₂ ≤ a₁ ↔ a₂ ∈ lower_bounds s :=
⟨λ hl, lower_bounds_mono hl h.1, λ hr, h.2 hr⟩

lemma eq_of_is_glb_of_is_glb : is_glb s a₁ → is_glb s a₂ → a₁ = a₂ :=
eq_of_is_greatest_of_is_greatest

lemma is_glb_iff_eq_of_is_glb : is_glb s a₁ → (is_glb s a₂ ↔ a₁ = a₂) :=
is_greatest_iff_eq_of_is_greatest

lemma nonempty_of_is_lub [no_bot_order α] (hs : is_lub s a) : s.nonempty :=
let ⟨a', ha'⟩ := no_bot a in
ne_empty_iff_nonempty.1 $ assume h,
have a ≤ a', from hs.right (by simp [upper_bounds, h]),
lt_irrefl a $ lt_of_le_of_lt this ha'

lemma nonempty_of_is_glb [no_top_order α] (hs : is_glb s a) : s.nonempty :=
let ⟨a', ha'⟩ := no_top a in
ne_empty_iff_nonempty.1 $ assume h,
have a' ≤ a, from hs.right (by simp [lower_bounds, h]),
lt_irrefl a $ lt_of_lt_of_le ha' this

end partial_order

section lattice

lemma is_glb_empty [order_top α] : is_glb ∅ (⊤:α) :=
by simp [is_glb, is_greatest, lower_bounds, upper_bounds]

lemma is_lub_empty [order_bot α] : is_lub ∅ (⊥:α) :=
by simp [is_lub, is_least, lower_bounds, upper_bounds]

lemma is_lub_union_sup [semilattice_sup α] (hs : is_lub s a₁) (ht : is_lub t a₂) :
  is_lub (s ∪ t) (a₁ ⊔ a₂) :=
⟨assume c h, h.cases_on (λ h, le_sup_left_of_le $ hs.left h) (λ h, le_sup_right_of_le $ ht.left h),
  assume c hc, sup_le
    (hs.right $ assume d hd, hc $ or.inl hd) (ht.right $ assume d hd, hc $ or.inr hd)⟩

lemma is_glb_union_inf [semilattice_inf α] (hs : is_glb s a₁) (ht : is_glb t a₂) :
  is_glb (s ∪ t) (a₁ ⊓ a₂) :=
⟨assume c h, h.cases_on (λ h, inf_le_left_of_le $ hs.left h) (λ h, inf_le_right_of_le $ ht.left h),
  assume c hc, le_inf
    (hs.right $ assume d hd, hc $ or.inl hd) (ht.right $ assume d hd, hc $ or.inr hd)⟩

lemma is_lub_insert_sup [semilattice_sup α] (h : is_lub s a₁) : is_lub (insert a₂ s) (a₂ ⊔ a₁) :=
by rw [insert_eq]; exact is_lub_union_sup is_lub_singleton h

lemma is_lub_iff_sup_eq [semilattice_sup α] : is_lub {a₁, a₂} a ↔ a₂ ⊔ a₁ = a :=
is_lub_iff_eq_of_is_lub $ is_lub_insert_sup $ is_lub_singleton

lemma is_glb_insert_inf [semilattice_inf α] (h : is_glb s a₁) : is_glb (insert a₂ s) (a₂ ⊓ a₁) :=
by rw [insert_eq]; exact is_glb_union_inf is_glb_singleton h

lemma is_glb_iff_inf_eq [semilattice_inf α] : is_glb {a₁, a₂} a ↔ a₂ ⊓ a₁ = a :=
is_glb_iff_eq_of_is_glb $ is_glb_insert_inf $ is_glb_singleton

end lattice

section linear_order
variables [linear_order α]

lemma lt_is_lub_iff (h : is_lub s a₁) : a₂ < a₁ ↔ ∃ a ∈ s, a₂ < a :=
by haveI := classical.dec;
   simpa [upper_bounds, not_ball] using
   not_congr (@is_lub_le_iff _ _ a₂ _ _ h)

lemma is_glb_lt_iff (h : is_glb s a₁) : a₁ < a₂ ↔ ∃ a ∈ s, a < a₂ :=
by haveI := classical.dec;
   simpa [lower_bounds, not_ball] using
   not_congr (@le_is_glb_iff _ _ a₂ _ _ h)

variables [densely_ordered α]

lemma is_glb_Ioi : is_glb (Ioi a) a :=
begin
  refine ⟨λx hx, le_of_lt hx, λy hy, _⟩,
  cases le_or_lt y a with h h, { exact h },
  rcases dense h with ⟨z, az, zy⟩,
  exact absurd zy (not_lt_of_le (hy az))
end

lemma is_lub_Iio : is_lub (Iio a) a :=
begin
  refine ⟨λx hx, le_of_lt hx, λy hy, _⟩,
  classical; by_contradiction h,
  rcases dense (not_le.1 h) with ⟨z, az, zy⟩,
  exact lt_irrefl _ (lt_of_lt_of_le az (hy zy)),
end

local attribute [instance] classical.DLO

lemma is_glb_Ioo (hab : a₁ < a₂) : is_glb (Ioo a₁ a₂) a₁ :=
begin
  refine ⟨λx hx, le_of_lt hx.1, λy hy, le_of_not_lt $ λ h, _⟩,
  have : a₁ < min a₂ y, by { rw lt_min_iff, exact ⟨hab, h⟩ },
  rcases dense this with ⟨z, az, zy⟩,
  rw lt_min_iff at zy,
  exact lt_irrefl _ (lt_of_le_of_lt (hy ⟨az, zy.1⟩) zy.2)
end

lemma is_glb_Ioc (hab : a₁ < a₂) : is_glb (Ioc a₁ a₂) a₁ :=
begin
  refine ⟨λx hx, le_of_lt hx.1, λy hy, le_of_not_lt $ λ h, _⟩,
  have : a₁ < min a₂ y, by { rw lt_min_iff, exact ⟨hab, h⟩ },
  rcases dense this with ⟨z, az, zy⟩,
  rw lt_min_iff at zy,
  exact lt_irrefl _ (lt_of_le_of_lt (hy ⟨az, le_of_lt zy.1⟩) zy.2)
end

lemma is_lub_Ioo (hab : a₁ < a₂) : is_lub (Ioo a₁ a₂) a₂ :=
begin
  refine ⟨λx hx, le_of_lt hx.2, λy hy, le_of_not_lt $ λ h, _⟩,
  have : max a₁ y < a₂, by { rw max_lt_iff, exact ⟨hab, h⟩ },
  rcases dense this with ⟨z, az, zy⟩,
  rw max_lt_iff at az,
  exact lt_irrefl _ (lt_of_lt_of_le az.2 (hy ⟨az.1, zy⟩))
end

lemma is_lub_Ico (hab : a₁ < a₂) : is_lub (Ico a₁ a₂) a₂ :=
begin
  refine ⟨λx hx, le_of_lt hx.2, λy hy, le_of_not_lt $ λ h, _⟩,
  have : max a₁ y < a₂, by { rw max_lt_iff, exact ⟨hab, h⟩ },
  rcases dense this with ⟨z, az, zy⟩,
  rw max_lt_iff at az,
  exact lt_irrefl _ (lt_of_lt_of_le az.2 (hy ⟨le_of_lt az.1, zy⟩))
end

end linear_order

section preorder
variables [preorder α] [preorder β]

/-- A set is bounded above if there exists an upper bound. -/
def bdd_above (s : set α) := ∃x, x ∈ upper_bounds s

/-- A set is bounded below if there exists a lower bound. -/
def bdd_below (s : set α) := ∃x, x ∈ lower_bounds s

/-Introduction rules for boundedness above and below.
Most of the time, it is more efficient to use ⟨w, P⟩ where P is a proof
that all elements of the set are bounded by w. However, they are sometimes handy.-/
lemma bdd_above.mk (a : α) (H : a ∈ upper_bounds s) : bdd_above s := ⟨a, H⟩
lemma bdd_below.mk (a : α) (H : a ∈ lower_bounds s) : bdd_below s := ⟨a, H⟩

/-Empty sets and singletons are trivially bounded. For finite sets, we need
a notion of maximum and minimum, i.e., a lattice structure, see later on.-/
@[simp] lemma bdd_above_empty : ∀ [nonempty α], bdd_above (∅ : set α)
| ⟨x⟩ := ⟨x, by simp [upper_bounds]⟩

@[simp] lemma bdd_below_empty : ∀ [nonempty α], bdd_below (∅ : set α)
| ⟨x⟩ := ⟨x, by simp [lower_bounds]⟩

@[simp] lemma bdd_above_singleton : bdd_above ({a} : set α) :=
⟨a, by simp only [upper_bounds, set.mem_set_of_eq, set.mem_singleton_iff, forall_eq]⟩

@[simp] lemma bdd_below_singleton : bdd_below ({a} : set α) :=
⟨a, by simp only [lower_bounds, set.mem_set_of_eq, set.mem_singleton_iff, forall_eq]⟩

/-If a set is included in another one, boundedness of the second implies boundedness
of the first-/
lemma bdd_above_subset (st : s ⊆ t) : bdd_above t → bdd_above s
| ⟨w, hw⟩ := ⟨w, λ y ys, hw (st ys)⟩

lemma bdd_below_subset (st : s ⊆ t) : bdd_below t → bdd_below s
| ⟨w, hw⟩ := ⟨w, λ y ys, hw (st ys)⟩

/- Boundedness of intersections of sets, in different guises, deduced from the
monotonicity of boundedness.-/
lemma bdd_above_inter_left : bdd_above s → bdd_above (s ∩ t) :=
bdd_above_subset (set.inter_subset_left _ _)

lemma bdd_above_inter_right : bdd_above t → bdd_above (s ∩ t) :=
bdd_above_subset (set.inter_subset_right _ _)

lemma bdd_below_inter_left : bdd_below s → bdd_below (s ∩ t) :=
bdd_below_subset (set.inter_subset_left _ _)

lemma bdd_below_inter_right : bdd_below t → bdd_below (s ∩ t) :=
bdd_below_subset (set.inter_subset_right _ _)

/--The image under a monotone function of a set which is bounded above is bounded above-/
lemma bdd_above_of_bdd_above_of_monotone {f : α → β} (hf : monotone f) : bdd_above s → bdd_above (f '' s)
| ⟨C, hC⟩ := ⟨f C, by rintro y ⟨x, x_bnd, rfl⟩; exact hf (hC x_bnd)⟩

/--The image under a monotone function of a set which is bounded below is bounded below-/
lemma bdd_below_of_bdd_below_of_monotone {f : α → β} (hf : monotone f) : bdd_below s → bdd_below (f '' s)
| ⟨C, hC⟩ := ⟨f C, by rintro y ⟨x, x_bnd, rfl⟩; exact hf (hC x_bnd)⟩

lemma bdd_below_iff_subset_Ici (s : set α) : bdd_below s ↔ ∃ a, s ⊆ Ici a := iff.rfl

lemma bdd_above_iff_subset_Iic (s : set α) : bdd_above s ↔ ∃ a, s ⊆ Iic a := iff.rfl

lemma bdd_below_bdd_above_iff_subset_Icc (s : set α) :
  bdd_below s ∧ bdd_above s ↔ ∃ a b, s ⊆ Icc a b :=
by simp [Ici_inter_Iic.symm, subset_inter_iff, bdd_below_iff_subset_Ici, bdd_above_iff_subset_Iic]

end preorder

/--When there is a global maximum, every set is bounded above.-/
@[simp] lemma bdd_above_top [order_top α] (s : set α) : bdd_above s :=
⟨⊤, assume a ha, order_top.le_top a⟩

/--When there is a global minimum, every set is bounded below.-/
@[simp] lemma bdd_below_bot [order_bot α] (s : set α) : bdd_below s :=
⟨⊥, assume a ha, order_bot.bot_le a⟩

/-When there is a max (i.e., in the class semilattice_sup), then the union of
two bounded sets is bounded, by the maximum of the bounds for the two sets.
With this, we deduce that finite sets are bounded by induction, and that a finite
union of bounded sets is bounded.-/
section semilattice_sup
variables [semilattice_sup α]

/--The union of two sets is bounded above if and only if each of the sets is.-/
@[simp] lemma bdd_above_union : bdd_above (s ∪ t) ↔ bdd_above s ∧ bdd_above t :=
⟨show bdd_above (s ∪ t) → (bdd_above s ∧ bdd_above t), from
  assume : bdd_above (s ∪ t),
  have S : bdd_above s, by apply bdd_above_subset _ ‹bdd_above (s ∪ t)›; simp only [set.subset_union_left],
  have T : bdd_above t, by apply bdd_above_subset _ ‹bdd_above (s ∪ t)›; simp only [set.subset_union_right],
  and.intro S T,
show (bdd_above s ∧ bdd_above t) → bdd_above (s ∪ t), from
  assume H : bdd_above s ∧ bdd_above t,
  let ⟨⟨ws, hs⟩, ⟨wt, ht⟩⟩ := H in
    /-hs : ∀ (y : α), y ∈ s → y ≤ ws      ht : ∀ (y : α), y ∈ s → y ≤ wt-/
  have Bs : ∀b∈s, b ≤ ws ⊔ wt,
    by intros; apply le_trans (hs ‹b ∈ s›) _; simp only [lattice.le_sup_left],
  have Bt : ∀b∈t, b ≤ ws ⊔ wt,
    by intros; apply le_trans (ht ‹b ∈ t›) _; simp only [lattice.le_sup_right],
  show bdd_above (s ∪ t),
    begin
    apply bdd_above.mk (ws ⊔ wt),
    intros b H_1,
    cases H_1,
    apply Bs _ ‹b ∈ s›,
    apply Bt _ ‹b ∈ t›,
    end⟩

/--Adding a point to a set preserves its boundedness above.-/
@[simp] lemma bdd_above_insert : bdd_above (insert a s) ↔ bdd_above s :=
⟨bdd_above_subset (by simp only [set.subset_insert]),
 λ h, by rw [insert_eq, bdd_above_union]; exact ⟨bdd_above_singleton, h⟩⟩

end semilattice_sup


/-When there is a min (i.e., in the class semilattice_inf), then the union of
two sets which are bounded from below is bounded from below, by the minimum of
the bounds for the two sets. With this, we deduce that finite sets are
bounded below by induction, and that a finite union of sets which are bounded below
is still bounded below.-/

section semilattice_inf
variables [semilattice_inf α]

/--The union of two sets is bounded below if and only if each of the sets is.-/
@[simp] lemma bdd_below_union : bdd_below (s ∪ t) ↔ bdd_below s ∧ bdd_below t :=
⟨show bdd_below (s ∪ t) → (bdd_below s ∧ bdd_below t), from
  assume : bdd_below (s ∪ t),
  have S : bdd_below s, by apply bdd_below_subset _ ‹bdd_below (s ∪ t)›; simp only [set.subset_union_left],
  have T : bdd_below t, by apply bdd_below_subset _ ‹bdd_below (s ∪ t)›; simp only [set.subset_union_right],
  and.intro S T,
show (bdd_below s ∧ bdd_below t) → bdd_below (s ∪ t), from
  assume H : bdd_below s ∧ bdd_below t,
  let ⟨⟨ws, hs⟩, ⟨wt, ht⟩⟩ := H in
    /-hs : ∀ (y : α), y ∈ s → ws ≤ y      ht : ∀ (y : α), y ∈ s → wt ≤ y-/
  have Bs : ∀b∈s, ws ⊓ wt ≤ b,
    by intros; apply le_trans _ (hs ‹b ∈ s›); simp only [lattice.inf_le_left],
  have Bt : ∀b∈t, ws ⊓ wt ≤ b,
    by intros; apply le_trans _ (ht ‹b ∈ t›); simp only [lattice.inf_le_right],
  show bdd_below (s ∪ t),
    begin
    apply bdd_below.mk (ws ⊓ wt),
    intros b H_1,
    cases H_1,
    apply Bs _ ‹b ∈ s›,
    apply Bt _ ‹b ∈ t›,
    end⟩

/--Adding a point to a set preserves its boundedness below.-/
@[simp] lemma bdd_below_insert : bdd_below (insert a s) ↔ bdd_below s :=
⟨show bdd_below (insert a s) → bdd_below s, from bdd_below_subset (by simp only [set.subset_insert]),
 show bdd_below s → bdd_below (insert a s),
   by rw[insert_eq]; simp only [bdd_below_singleton, bdd_below_union, and_self, forall_true_iff] {contextual := tt}⟩

end semilattice_inf
