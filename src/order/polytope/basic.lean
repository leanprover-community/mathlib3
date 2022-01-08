-- Current progress on polytopes. Currently very broken.

/-
import combinatorics.simple_graph.connectivity
import .graded

variables {α β : Type*}

-- Proper elements are those that are neither maximal nor minimal.
--def is_proper [has_lt α] (b : α) : Prop := ∃ a, a < b ∧ ∃ c, b < c

section partial_order
variables [partial_order α]

section bounded_order
variables [bounded_order α]

variables [grade_order α]


/-- An element is proper iff it has a grade between the bottom and top element. -/
lemma proper_iff_grade_iio (a : α) : is_proper a ↔ grade a ∈ set.Ioo 0 (grade (⊤ : α)) :=
begin
  rw proper_iff_ne_bot_top,
  split,
  { intro ha,
    cases ha with hal har,
    cases eq_or_lt_of_le (zero_le (grade a)) with h hl,
    { replace h := eq.symm h,
      rw grade_eq_zero_iff at h,
      exact (hal h).elim },
    cases eq_or_lt_of_le (grade_le_grade_top a) with h hr,
    { rw eq_grade_top_iff_eq_top at h,
      exact (har h).elim },
    exact ⟨hl, hr⟩ },
  rintro ⟨hl, hr⟩,
  split,
  { intro ha,
    rw ←grade_eq_zero_iff at ha,
    exact hl.ne' ha },
  intro ha,
  rw ←eq_grade_top_iff_eq_top at ha,
  exact hr.ne ha
end

/-- A `graded` with top grade 1 or less has no proper elements. -/
lemma proper.empty : grade (⊤ : α) ≤ 1 → is_empty (polytope.proper α) :=
begin
  intro h,
  split,
  rintro ⟨a, ha⟩,
  rw proper_iff_grade_iio at ha,
  refine (not_le_of_lt (lt_of_le_of_lt _ ha.right)) h,
  exact ha.left
end

/-- A `graded` with top grade 2 or more has some proper element. -/
lemma proper.nonempty (h : 2 ≤ grade (⊤ : α)) : nonempty (polytope.proper α) :=
begin
  have hbt : ¬ ⊥ ⋖ ⊤ := begin
    intro hbt,
    have := hbt.grade,
    rw grade_bot at this,
    rw this at h,
    exact nat.lt_asymm h h,
  end,

  have hbt' : (⊥ : α) < ⊤ := begin
    rw bot_lt_iff_ne_bot,
    intro hbt',
    rw [hbt', grade_bot] at h,
    exact (not_le_of_lt zero_lt_two) h,
  end,

  obtain ⟨z, hz⟩ := exists_lt_lt_of_not_covers hbt hbt',
  exact ⟨⟨z, ⊥, ⊤, hz⟩⟩,
end

end bounded_order
end partial_order

/-- Proper elements are connected when they're related by a sequence of pairwise incident proper
elements. -/
def polytope.proper_connected [preorder α] [bounded_order α] {a b : α} : Prop :=
∃ l, list.chain (λ x y, x ≤ y ∨ y ≤ x) a (l ++ [b]) ∧ ¬ l.mem ⊥ ∧ ¬ l.mem ⊤

open polytope

namespace graded

/-- A `graded` is totally connected' when any two proper elements are connected. Note that this
definition requires nothing more than a preorder. -/
def total_connected' (α : Type*) [preorder α] : Prop :=
∀ a b : proper α, connected a b

/-- A `graded` is totally connected when it's of grade 2, or any two proper elements are connected.

Here we deviate from standard nomenclature: mathematicians would just call this connectedness.
However, by doing this, it makes it unambiguous when we're talking about two elements being
connected, and when we're talking about a polytope being totally connected. -/
def total_connected (α : Type*) [preorder α] [bounded_order α] [grade_order α] : Prop :=
grade (⊤ : α) = 2 ∨ total_connected' α

/-- Order isomorphisms preserve proper elements. -/
private lemma proper_order_iso_of_proper [partial_order α] [bounded_order α] [grade_order α]
  [partial_order β] [bounded_order β] [grade_order β] (oiso : α ≃o β) (x : proper α) :
  is_proper (oiso x) :=
begin
  rw proper_iff_ne_bot_top (oiso x),
  have := x.prop,
  split, {
    intro h,
    apply @not_proper_bot α,
    rw ←oiso.map_bot at h,
    rwa oiso.injective h at this },
  intro h,
  apply @not_proper_top α,
  rw ←oiso.map_top at h,
  rwa oiso.injective h at this,
end

/-- Order isomorphisms preserve proper elements. -/
lemma proper_order_iso_iff_proper [partial_order α] [bounded_order α] [grade_order α]
  [partial_order β] [bounded_order β] [grade_order β] (oiso : α ≃o β) (x : α) :
  is_proper x ↔ is_proper (oiso x) :=
begin
  refine ⟨λ hx, proper_order_iso_of_proper oiso ⟨x, hx⟩, λ hx, _⟩,
  have := proper_order_iso_of_proper oiso.symm ⟨oiso x, hx⟩,
  simp at this,
  exact this,
end

end graded

namespace order_iso

variables [partial_order α] [partial_order β] (oiso : α ≃o β)

/-- Order isomorphisms preserve covering. -/
private lemma covers' (a b : α) : a ⋖ b → oiso a ⋖ oiso b :=
begin
  refine λ h, ⟨oiso.strict_mono h.left, λ c ha hb, h.2 (_ : a < oiso.symm c) _⟩,
  { have := oiso.symm.strict_mono ha,
    simp at this,
    exact this },
  { have := oiso.symm.strict_mono hb,
    simp at this,
    exact this }
end

/-- Order isomorphisms preserve covering. -/
protected lemma covers (x y : α) : x ⋖ y ↔ oiso x ⋖ oiso y :=
begin
  use covers' oiso x y,
  have := covers' oiso.symm (oiso x) (oiso y),
  simp at this,
  exact this,
end

/-- An isomorphism between posets, one of which is graded, is enough to give a grade function for
the other. -/
protected def grade_order [order_bot α] [order_bot β] [grade_order β] : grade_order α :=
{ grade := λ a, @grade β _ _ _ (oiso a),
  grade_bot := begin
    rw oiso.map_bot,
    exact grade_bot,
  end,
  strict_mono := λ _ _ hab, grade_strict_mono (oiso.strict_mono hab),
  grade_of_covers := begin
    intros x y hxy,
    apply covers.grade,
    rwa ←oiso.covers x y,
  end }

/-- An isomorphism between graded posets extends to an isomorphism between sections. -/
protected def Icc (x y : α) : set.Icc x y ≃o set.Icc (oiso x) (oiso y) :=
{ to_fun := λ a, ⟨oiso.to_fun a.1, (le_iff_le oiso).2 a.prop.left, (le_iff_le oiso).2 a.prop.right⟩,
  inv_fun := λ a, ⟨oiso.inv_fun a, begin
    split,
    { have H : oiso.inv_fun (oiso.to_fun x) ≤ oiso.inv_fun a,
      { change oiso.inv_fun with oiso.symm,
        rw le_iff_le oiso.symm,
        exact a.prop.left },
      simp at H,
      exact H },
    have H : oiso.inv_fun a ≤ oiso.inv_fun (oiso.to_fun y),
    { change oiso.inv_fun with oiso.symm,
      rw le_iff_le oiso.symm,
      exact a.prop.right },
    simp at H,
    exact H,
  end⟩,
  left_inv := λ _, subtype.eq (by simp),
  right_inv := λ _, subtype.eq (by simp),
  map_rel_iff' := by simp }

variables [bounded_order α] [grade_order α] [bounded_order β] [grade_order β]

/-- The map from proper elements to proper elements given by an order isomorphism. -/
private def proper_aux : proper α → proper β :=
λ x, ⟨oiso x, (graded.proper_order_iso_iff_proper oiso x).1 x.prop⟩

/-- An isomorphism between graded posets extends to an isomorphism between proper elements. -/
def proper : proper α ≃o proper β :=
{ to_fun := proper_aux oiso,
  inv_fun := proper_aux oiso.symm,
  left_inv := λ x, subtype.eq (oiso.symm_apply_apply x),
  right_inv := λ x, subtype.eq (oiso.apply_symm_apply x),
  map_rel_iff' := λ _ _, le_iff_le oiso }

end order_iso

namespace graded

/-- If two elements are connected, so are their maps under an isomorphism. -/
private lemma con_order_iso_of_con [partial_order α] [bounded_order α] [grade_order α]
  [partial_order β] [bounded_order β] [grade_order β] (oiso : α ≃o β) (x y : proper α) :
  connected x y → connected (oiso.proper x) (oiso.proper y) :=
begin
  intro hxy,
  induction hxy with _ x y z hxy hyz hxy',
    { exact path.refl },
  apply path.append_right hxy',
  intro hne,
  cases hyz (λ h, hne (congr_arg oiso h : oiso y = oiso z)) with hyz hyz,
    { exact or.inl (oiso.lt_iff_lt.2 hyz) },
  exact or.inr (oiso.lt_iff_lt.2 hyz),
end

/-- Two elements are connected iff their maps under an isomorphism are. -/
lemma con_order_iso_iff_con [partial_order α] [bounded_order α] [grade_order α]
  [partial_order β] [bounded_order β] [grade_order β] (oiso : α ≃o β) (x y : proper α) :
  connected x y ↔ connected (oiso.proper x) (oiso.proper y) :=
begin
  refine ⟨con_order_iso_of_con oiso x y, _⟩,
  have := con_order_iso_of_con oiso.symm (oiso.proper x) (oiso.proper y),
  rwa [(subtype.eq (oiso.left_inv _) : (oiso.symm.proper (oiso.proper x)) = x),
       (subtype.eq (oiso.left_inv _) : (oiso.symm.proper (oiso.proper y)) = y)] at this
end

/-- Any `graded` of top grade less or equal to 2 is connected. -/
lemma tcon_of_grade_le_two (α : Type*) [partial_order α] [bounded_order α] [grade_order α] :
  grade (⊤ : α) ≤ 2 → total_connected α :=
begin
  intro h,
  cases eq_or_lt_of_le h with ha ha, { exact or.inl ha },
  exact or.inr (λ a, (((proper.empty (nat.le_of_lt_succ ha)).false : proper α → false) a).elim)
end

/-- Asserts that a section of a graded poset is connected'. -/
def section_connected' [preorder α] (x y : α) : Prop :=
total_connected' (set.Icc x y)

/-- Asserts that a section of a graded poset is connected. -/
def section_connected [partial_order α] [order_bot α] [grade_order α] {x y : α} (hxy : x ≤ y) :
  Prop :=
@total_connected _ _ (set.Icc.bounded_order hxy) (set.Icc.graded hxy)

/-- A graded poset is strongly connected when all sections are connected. -/
def strong_connected (α : Type*) [partial_order α] [order_bot α] [grade_order α] : Prop :=
∀ {x y : α} (hxy : x ≤ y), section_connected hxy

/-- Any `graded` of top grade less or equal to 2 is strongly connected. -/
lemma scon_of_grade_le_two [partial_order α] [bounded_order α] [grade_order α]
  (h : grade (⊤ : α) ≤ 2) :
  strong_connected α :=
begin
  intros a b hab,
  apply tcon_of_grade_le_two,
  exact (le_trans tsub_le_self (le_trans (grade_le_grade_top b) h)),
end

end graded

-/
