import order.bounds algebra.ordered_group analysis.real analysis.topology.infinite_sum analysis.topology.topological_space
noncomputable theory



definition nnreal := {r : ℝ // 0 ≤ r}
notation ` ℝ≥0 ` := nnreal

namespace nnreal

section projections

end projections

instance : has_zero ℝ≥0  := {zero := ⟨0,le_refl 0⟩}
instance : has_one ℝ≥0   := {one := ⟨1,zero_le_one⟩}
instance : inhabited ℝ≥0 := ⟨0⟩

@[simp] lemma val_zero : (0 : ℝ≥0).val = 0 := rfl
@[simp] lemma val_one  : (1 : ℝ≥0).val = 1 := rfl

variables {r s: ℝ}

-- instance : zero_ne_one_class ℝ≥0 :=
-- { zero := 0, one := 1, zero_ne_one := begin simp, congr_arg subtype.val, end }

section semiring

protected def add : ℝ≥0 → ℝ≥0 → ℝ≥0 :=
λ r s, ⟨r.val + s.val,have h : (r.val ≤ r.val + s.val) :=
                      by rw le_add_iff_nonneg_right; exact s.property,
        le_trans r.property h⟩

protected def mul : ℝ≥0 → ℝ≥0 → ℝ≥0 :=
λ r s, ⟨r.val * s.val,begin
                      have h := mul_le_mul_of_nonneg_right r.2 s.2,
                      simp at h,
                      exact h
                      end⟩

instance : has_add ℝ≥0 := ⟨nnreal.add⟩
instance : has_mul ℝ≥0 := ⟨nnreal.mul⟩

@[simp] lemma add_val (r₁ r₂ : ℝ≥0) : (r₁ + r₂).val = r₁.val + r₂.val := rfl
@[simp] lemma mul_val (r₁ r₂ : ℝ≥0) : (r₁ * r₂).val = r₁.val * r₂.val := rfl

instance : add_comm_monoid ℝ≥0 :=
{ zero      := 0,
  add       := (+),
  add_zero  := λ _, by apply subtype.eq; simp,
  zero_add  := λ _, by apply subtype.eq; simp,
  add_comm  := λ _ _, by apply subtype.eq; simp,
  add_assoc := λ _ _ _, by apply subtype.eq; simp
}

instance : comm_semiring ℝ≥0 :=
{ one := 1,
  mul := (*),
  mul_zero  := λ r, begin apply subtype.eq; simp, show r.val * 0 = 0, simp, end,
  zero_mul  := λ r, begin apply subtype.eq; simp, show 0 * r.val = 0, simp, end,
  one_mul   := λ _, by apply subtype.eq; simp,
  mul_one   := λ _, by apply subtype.eq; simp,
  mul_comm  := λ _ _, by apply subtype.eq; simp; rw mul_comm,
  mul_assoc := λ _ _ _, by apply subtype.eq; simp; rw mul_assoc,
  left_distrib :=
  λ r s t,
  begin
    apply subtype.eq,
    show r.val * (s+t).val = (r*s + r*t).val,
    simp,
    rw left_distrib,
  end,
  right_distrib :=
  λ r s t,
  begin
    apply subtype.eq,
    show (r+s).val * t.val = (r*t + s*t).val,
    simp,
    rw right_distrib,
  end,
  ..nnreal.add_comm_monoid
}

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

definition real_topology : topological_space ℝ := by apply_instance
instance : topological_space ℝ≥0 := topological_space.induced subtype.val real_topology

lemma prod_subtype {α : Type*} {p : α → Prop} [t : topological_space α] :
continuous (λ x : (subtype p) × (subtype p), (x.fst.val, x.snd.val)) :=
continuous.prod_mk (continuous.comp continuous_fst continuous_induced_dom)
                   (continuous.comp continuous_snd continuous_induced_dom)

lemma continuous_add : continuous (λ (p : ℝ≥0 × ℝ≥0), p.fst + p.snd) :=
begin
rw continuous_iff_induced_le,
unfold nnreal.topological_space,
have triv : topological_space.induced (λ (p : ℝ≥0 × ℝ≥0), p.fst + p.snd)
              (topological_space.induced subtype.val real_topology) = 
            ((topological_space.induced (λ (p : ℝ≥0 × ℝ≥0), p.fst + p.snd)) ∘
              (topological_space.induced subtype.val)) real_topology :=
by unfold function.comp,
rw triv,
rw ←induced_comp,
unfold function.comp,
simp,
rw ←continuous_iff_induced_le,
have comp : (λ (x : ℝ≥0 × ℝ≥0), (x.fst).val + (x.snd).val) =
              (λ (x : ℝ × ℝ), x.fst + x.snd) ∘ (λ (x : ℝ≥0 × ℝ≥0), (x.fst.val, x.snd.val)) :=
begin
  apply funext,
  intro x,
  unfold function.comp
end,
rw comp,
apply continuous.comp prod_subtype _,
have helpme : topological_add_monoid ℝ := by apply_instance,
exact helpme.continuous_add
end

instance : topological_add_monoid ℝ≥0 := {continuous_add := continuous_add}

end topology

end nnreal