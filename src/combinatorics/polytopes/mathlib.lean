import order.atoms

variables {α : Type*}

section order_dual
open order_dual
variables [has_lt α]

lemma has_lt.lt.of_dual {a b : order_dual α} (h : a < b) : of_dual b < of_dual a := h

end order_dual

namespace nat

/-- A point subdivides an interval into three. -/
private lemma ioo_tricho {a b c : ℕ} (hc : c ∈ set.Ioo a b) (d : ℕ) :
  c = d ∨ c ∈ set.Ioo a d ∨ c ∈ set.Ioo d b :=
begin
  cases eq_or_ne c d with hcd hcd,
    { exact or.inl hcd },
  cases ne.lt_or_lt hcd with ha hb,
    { exact or.inr (or.inl ⟨and.left hc, ha⟩) },
    { exact or.inr (or.inr ⟨hb, and.right hc⟩) }
end

/-- A set of nats without gaps is an interval. The sizes of the gaps and intervals we consider are
bounded by `n`, so that we may induct on it. -/
private lemma all_ioo_of_ex_ioo {P : ℕ → Prop} (n : ℕ)
  (hP : ∀ a b, b ≤ a + n → P a → P b → nonempty (set.Ioo a b) → ∃ c ∈ set.Ioo a b, P c) (a b : ℕ) :
  b ≤ a + n → P a → P b → ∀ c ∈ set.Ioo a b, P c :=
begin
  revert a b,
  induction n with n hP',
    { exact λ _ _ hba _ _ _ hci, ((not_lt_of_ge hba) (lt_trans hci.left hci.right)).elim },
  intros a b hba ha hb _ hci,
  rcases hP a b hba ha hb (nonempty.intro ⟨_, hci⟩) with ⟨d, ⟨hdil, hdir⟩, hd⟩,
  cases ioo_tricho hci d with hcd hdb, { rwa ←hcd at hd },
  have hxy : ∃ x y, P x ∧ P y ∧ c ∈ set.Ioo x y ∧ y ≤ x + n := begin
    cases hdb with hcad hcdb,
      { refine ⟨a, d, ha, hd, hcad, _⟩,
        have := lt_of_lt_of_le hdir hba,
        rw nat.add_succ at this,
        exact nat.le_of_lt_succ this },
      { refine ⟨d, b, hd, hb, hcdb, _⟩,
        have := nat.add_le_add hdil rfl.le,
        rw nat.succ_add a n at this,
        exact le_trans hba this }
  end,
  rcases hxy with ⟨x, y, hx, hy, hxy, hyx⟩,
  exact hP' (λ _ _ hba, hP _ _ (hba.trans (nat.le_succ _))) x y hyx hx hy c hxy,
end

/-- A set of nats without gaps is an interval. -/
lemma all_icc_of_ex_ioo {P : ℕ → Prop}
  (hP : ∀ a b, P a → P b → (nonempty (set.Ioo a b)) → ∃ c ∈ set.Ioo a b, P c) (a b : ℕ) (ha : P a)
  (hb : P b) :
  ∀ c ∈ set.Icc a b, P c :=
begin
  rintro c ⟨hac, hcb⟩,
  cases eq_or_lt_of_le hac with hac hac,
    { rwa ←hac },
  cases eq_or_lt_of_le hcb with hcb hcb,
    { rwa  hcb },
  exact all_ioo_of_ex_ioo b (λ c d _, hP c d) _ _ le_add_self ha hb _ ⟨hac, hcb⟩
end

end nat

/-- A preorder is isomorphic to the section from bottom to top. -/
def set.Icc.self_order_iso_bot_top (α : Type*) [preorder α] [order_bot α] [order_top α] :
  α ≃o set.Icc ⊥ (⊤ : α) :=
{ to_fun := λ x, ⟨x, bot_le, le_top⟩,
  inv_fun := subtype.val,
  left_inv := λ _, rfl,
  right_inv := λ _, subtype.eq rfl,
  map_rel_iff' := by simp }

lemma ne_bot_of_lt {α : Type*} [preorder α] [order_bot α] {a b : α} (h : a < b) : b ≠ ⊥ :=
begin
  rintro rfl,
  exact not_lt_bot h,
end

lemma ne_top_of_gt {α : Type*} [preorder α] [order_top α] {a b : α} (h : a < b) : a ≠ ⊤ :=
begin
  rintro rfl,
  exact not_top_lt h,
end

lemma is_simple_order.eq_bot_of_lt {α : Type*} [preorder α] [bounded_order α] [is_simple_order α]
  {a b : α} (h : a < b) :
  a = ⊥ :=
(is_simple_order.eq_bot_or_eq_top _).resolve_right $ ne_top_of_gt h

lemma is_simple_order.eq_top_of_lt {α : Type*} [preorder α] [bounded_order α] [is_simple_order α]
  {a b : α} (h : a < b) :
  b = ⊤ :=
(is_simple_order.eq_bot_or_eq_top _).resolve_left $ ne_bot_of_lt h

lemma bot_lt_top {α : Type*} [partial_order α] [bounded_order α] [nontrivial α] : (⊥ : α) < ⊤ :=
lt_top_iff_ne_top.2 bot_ne_top
