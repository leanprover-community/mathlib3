import analysis.real
noncomputable theory



definition nnreal := {r : ℝ // 0 ≤ r}
local notation ` ℝ≥0 ` := nnreal

namespace nnreal

section projections

end projections

instance : has_zero ℝ≥0  := ⟨⟨0,le_refl 0⟩⟩
instance : has_one ℝ≥0   := ⟨⟨1,zero_le_one⟩⟩
instance : inhabited ℝ≥0 := ⟨0⟩

@[simp] lemma val_zero : (0 : ℝ≥0).val = 0 := rfl
@[simp] lemma val_one  : (1 : ℝ≥0).val = 1 := rfl

variables {r s: ℝ}

section semiring

instance : has_add ℝ≥0 := ⟨λa b, ⟨a.1 + b.1, add_nonneg a.2 b.2⟩⟩
instance : has_mul ℝ≥0 := ⟨λa b, ⟨a.1 * b.1, mul_nonneg a.2 b.2⟩⟩

@[simp] lemma add_val (r₁ r₂ : ℝ≥0) : (r₁ + r₂).val = r₁.val + r₂.val := rfl
@[simp] lemma mul_val (r₁ r₂ : ℝ≥0) : (r₁ * r₂).val = r₁.val * r₂.val := rfl

instance : add_comm_monoid ℝ≥0 :=
by refine { zero := 0, add := (+), .. }; { intros; apply subtype.eq; simp }

instance : comm_semiring ℝ≥0 :=
by refine
{ one := 1,
  mul := (*),
  mul_zero := λ r, begin apply subtype.eq; simp, show r.val * 0 = 0, simp, end,
  ..nnreal.add_comm_monoid,
  ..};
  { intros; apply subtype.eq;
    simp [mul_comm, mul_assoc, add_comm_monoid.add, left_distrib, right_distrib,
          add_comm_monoid.zero] }

end semiring

section order

instance : has_le ℝ≥0 := ⟨λ r s, r.val ≤ s.val⟩

instance : decidable_linear_order ℝ≥0 :=
{ le           := (≤),
  le_refl      := begin intro r, show r.val ≤ r.val, apply le_refl end,
  le_trans     :=
  begin
    intros r s t,
    show r.val ≤ s.val → s.val ≤ t.val → r.val ≤ t.val,
    apply le_trans
  end,
  le_antisymm  :=
  begin
    intros r s,
    show r.val ≤ s.val → s.val ≤ r.val → r = s,
    intros h1 h2,
    apply subtype.eq,
    apply le_antisymm h1 h2
  end,
  le_total     := begin intros r s, show r.val ≤ s.val ∨ s.val ≤ r.val, apply le_total end,
  decidable_le :=
  begin
    unfold decidable_rel,
    intros r s,
    show decidable (preorder.le r.val s.val),
    apply_instance,
  end}

@[simp] lemma le_zero_iff_eq {r : ℝ≥0} : r ≤ 0 ↔ r = 0 :=
⟨assume h, le_antisymm h r.property, assume h, h ▸ le_refl r⟩

instance : ordered_comm_monoid ℝ≥0 :=
{ add_le_add_left       :=
  λ r s h t,
  begin
    show t.val + r.val ≤ t.val + s.val,
    apply add_le_add_left,
    exact h,
  end,
  lt_of_add_lt_add_left :=
  λ r s t h,
  have H : r.val + s.val < r.val + t.val :=
  begin apply lt_of_not_ge, show ¬ r + s ≥ r + t, simp, exact h end,
  begin
    apply lt_of_not_ge,
    show ¬s.val ≥ t.val,
    simp,
    apply lt_of_add_lt_add_left H,
  end,
  ..nnreal.add_comm_monoid,
  ..nnreal.decidable_linear_order}

end order

section topology

instance : topological_space ℝ≥0 := subtype.topological_space

instance : topological_monoid ℝ≥0 :=
{ continuous_mul :=
by apply continuous_subtype_mk _
        (continuous_mul (continuous.comp continuous_fst continuous_induced_dom)
                        (continuous.comp continuous_snd continuous_induced_dom));
apply_instance}

instance : topological_semiring ℝ≥0 :=
{ continuous_add :=
by apply continuous_subtype_mk _
        (continuous_add (continuous.comp continuous_fst continuous_induced_dom)
                        (continuous.comp continuous_snd continuous_induced_dom));
apply_instance}

end topology

end nnreal