/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Nonnegative real numbers.
-/
import analysis.real analysis.topology.infinite_sum

noncomputable theory
open lattice filter
variables {α : Type*}

definition nnreal := {r : ℝ // 0 ≤ r}
local notation ` ℝ≥0 ` := nnreal

namespace nnreal

instance : has_coe ℝ≥0 ℝ := ⟨subtype.val⟩

protected lemma eq {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) → n = m := subtype.eq
protected lemma eq_iff {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) ↔ n = m :=
iff.intro nnreal.eq (congr_arg coe)

instance : has_zero ℝ≥0  := ⟨⟨0, le_refl 0⟩⟩
instance : has_one ℝ≥0   := ⟨⟨1, zero_le_one⟩⟩
instance : has_add ℝ≥0   := ⟨λa b, ⟨a + b, add_nonneg a.2 b.2⟩⟩
instance : has_mul ℝ≥0   := ⟨λa b, ⟨a * b, mul_nonneg a.2 b.2⟩⟩
instance : has_div ℝ≥0   := ⟨λa b, ⟨a.1 / b.1, div_nonneg' a.2 b.2⟩⟩
instance : has_le ℝ≥0    := ⟨λ r s, (r:ℝ) ≤ s⟩
instance : has_bot ℝ≥0   := ⟨0⟩
instance : inhabited ℝ≥0 := ⟨0⟩

@[simp] protected lemma coe_zero : ((0 : ℝ≥0) : ℝ) = 0 := rfl
@[simp] protected lemma coe_one  : ((1 : ℝ≥0) : ℝ) = 1 := rfl
@[simp] protected lemma coe_add (r₁ r₂ : ℝ≥0) : ((r₁ + r₂ : ℝ≥0) : ℝ) = r₁ + r₂ := rfl
@[simp] protected lemma coe_mul (r₁ r₂ : ℝ≥0) : ((r₁ * r₂ : ℝ≥0) : ℝ) = r₁ * r₂ := rfl
@[simp] protected lemma coe_div (r₁ r₂ : ℝ≥0) : ((r₁ / r₂ : ℝ≥0) : ℝ) = r₁ / r₂ := rfl

-- TODO: setup semifield!
@[simp] protected lemma zero_div (r : nnreal) : 0 / r = 0 :=
nnreal.eq (zero_div _)

instance : comm_semiring ℝ≥0 :=
begin
  refine { zero := 0, add := (+), one := 1, mul := (*), ..};
  { intros;
    apply nnreal.eq;
    simp [mul_comm, mul_assoc, add_comm_monoid.add, left_distrib, right_distrib,
          add_comm_monoid.zero],  }
end

@[simp] protected lemma coe_nat_cast : ∀(n : ℕ), (↑(↑n : ℝ≥0) : ℝ) = n
| 0       := rfl
| (n + 1) := by simp [coe_nat_cast n]

instance : decidable_linear_order ℝ≥0 :=
{ le               := (≤),
  lt               := λa b, (a : ℝ) < b,
  lt_iff_le_not_le := assume a b, @lt_iff_le_not_le ℝ _ a b,
  le_refl          := assume a, le_refl (a : ℝ),
  le_trans         := assume a b c, @le_trans ℝ _ a b c,
  le_antisymm      := assume a b hab hba, nnreal.eq $ le_antisymm hab hba,
  le_total         := assume a b, le_total (a : ℝ) b,
  decidable_le     := λa b, by apply_instance }

instance : canonically_ordered_monoid ℝ≥0 :=
{ add_le_add_left       := assume a b h c, @add_le_add_left ℝ _ a b h c,
  lt_of_add_lt_add_left := assume a b c, @lt_of_add_lt_add_left ℝ _ a b c,
  le_iff_exists_add     := assume ⟨a, ha⟩ ⟨b, hb⟩,
    iff.intro
      (assume h : a ≤ b,
        ⟨⟨b - a, le_sub_iff_add_le.2 $ by simp [h]⟩,
          nnreal.eq $ show b = a + (b - a), by rw [add_sub_cancel'_right]⟩)
      (assume ⟨⟨c, hc⟩, eq⟩, eq.symm ▸ show a ≤ a + c, from (le_add_iff_nonneg_right a).2 hc),
  ..nnreal.comm_semiring,
  ..nnreal.decidable_linear_order}

instance : order_bot ℝ≥0 :=
{ bot := ⊥, bot_le := zero_le, .. nnreal.decidable_linear_order }

instance : distrib_lattice ℝ≥0 := by apply_instance

instance : semilattice_inf_bot ℝ≥0 :=
{ .. nnreal.lattice.order_bot, .. nnreal.lattice.distrib_lattice }

instance : semilattice_sup_bot ℝ≥0 :=
{ .. nnreal.lattice.order_bot, .. nnreal.lattice.distrib_lattice }

instance : linear_ordered_semiring ℝ≥0 :=
{ add_left_cancel            := assume a b c h, nnreal.eq $ @add_left_cancel ℝ _ a b c (nnreal.eq_iff.2 h),
  add_right_cancel           := assume a b c h, nnreal.eq $ @add_right_cancel ℝ _ a b c (nnreal.eq_iff.2 h),
  le_of_add_le_add_left      := assume a b c, @le_of_add_le_add_left ℝ _ a b c,
  mul_le_mul_of_nonneg_left  := assume a b c, @mul_le_mul_of_nonneg_left ℝ _ a b c,
  mul_le_mul_of_nonneg_right := assume a b c, @mul_le_mul_of_nonneg_right ℝ _ a b c,
  mul_lt_mul_of_pos_left     := assume a b c, @mul_lt_mul_of_pos_left ℝ _ a b c,
  mul_lt_mul_of_pos_right    := assume a b c, @mul_lt_mul_of_pos_right ℝ _ a b c,
  zero_lt_one                := @zero_lt_one ℝ _,
  .. nnreal.decidable_linear_order,
  .. nnreal.canonically_ordered_monoid,
  .. nnreal.comm_semiring }

instance : topological_space ℝ≥0 := subtype.topological_space

instance : topological_semiring ℝ≥0 :=
{ continuous_mul :=
   continuous_subtype_mk _
        (continuous_mul (continuous.comp continuous_fst continuous_subtype_val)
                        (continuous.comp continuous_snd continuous_subtype_val)),
  continuous_add :=
    continuous_subtype_mk _
          (continuous_add (continuous.comp continuous_fst continuous_subtype_val)
                          (continuous.comp continuous_snd continuous_subtype_val)) }

instance : orderable_topology ℝ≥0 :=
⟨ le_antisymm
    begin
      apply induced_le_iff_le_coinduced.2,
      rw [orderable_topology.topology_eq_generate_intervals ℝ],
      apply generate_from_le,
      assume s hs,
      rcases hs with ⟨a, rfl | rfl⟩,
      { show topological_space.generate_open _ {b : ℝ≥0 | a < b },
        by_cases ha : 0 ≤ a,
        { exact topological_space.generate_open.basic _ ⟨⟨a, ha⟩, or.inl rfl⟩ },
        { have : a < 0, from lt_of_not_ge ha,
          have : {b : ℝ≥0 | a < b } = set.univ,
            from (set.eq_univ_iff_forall.2 $ assume b, lt_of_lt_of_le this b.2),
          rw [this],
          exact topological_space.generate_open.univ _ } },
      { show (topological_space.generate_from _).is_open {b : ℝ≥0 | a > b },
        by_cases ha : 0 ≤ a,
        { exact topological_space.generate_open.basic _ ⟨⟨a, ha⟩, or.inr rfl⟩ },
        { have : {b : ℝ≥0 | a > b } = ∅,
            from (set.eq_empty_iff_forall_not_mem.2 $ assume b hb, ha $
              show 0 ≤ a, from le_trans b.2 (le_of_lt hb)),
          rw [this],
          apply @is_open_empty } },
    end
    (generate_from_le $ assume s hs,
    match s, hs with
    | _, ⟨⟨a, ha⟩, or.inl rfl⟩ := ⟨{b : ℝ | a < b}, is_open_lt' a, rfl⟩
    | _, ⟨⟨a, ha⟩, or.inr rfl⟩ := ⟨{b : ℝ | b < a}, is_open_gt' a, set.ext $ assume b, iff.refl _⟩
    end) ⟩

lemma tendsto_coe {f : filter α} {m : α → nnreal} :
  ∀{x : nnreal}, tendsto (λa, (m a : ℝ)) f (nhds (x : ℝ)) ↔ tendsto m f (nhds x)
| ⟨r, hr⟩ := by rw [nhds_subtype_eq_vmap, tendsto_vmap_iff]; refl

lemma sum_coe {s : finset α} {f : α → nnreal} :
  s.sum (λa, (f a : ℝ)) = (s.sum f : nnreal)  :=
finset.sum_hom _ rfl (assume a b, rfl)

lemma is_sum_coe {f : α → nnreal} {r : nnreal} : is_sum (λa, (f a : ℝ)) (r : ℝ) ↔ is_sum f r :=
by simp [is_sum, sum_coe, tendsto_coe]

lemma has_sum_coe {f : α → nnreal} : has_sum (λa, (f a : ℝ)) ↔ has_sum f :=
begin
  simp [has_sum],
  split,
  exact assume ⟨a, ha⟩, ⟨⟨a, is_sum_le (λa, (f a).2) is_sum_zero ha⟩, is_sum_coe.1 ha⟩,
  exact assume ⟨a, ha⟩, ⟨a.1, is_sum_coe.2 ha⟩
end

end nnreal
