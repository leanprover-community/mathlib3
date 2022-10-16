import group_theory.free_group
import topology.metric_space.hausdorff_distance

/-!
# To move
-/

attribute [simp] free_group.to_word_inv

namespace free_group
variable {α : Type*}

open list

lemma mk_cons (a : α × bool) (l : list (α × bool)) : mk (a :: l) = mk [a] * mk l := rfl
lemma mk_append (l₁ l₂ : list (α × bool)) : mk (l₁ ++ l₂) = mk l₁ * mk l₂ := rfl

variable [decidable_eq α]

lemma to_word_mul_sublist (x y : free_group α) : (x * y).to_word <+ x.to_word ++ y.to_word :=
begin
  refine red.sublist _,
  have : x * y = free_group.mk (x.to_word ++ y.to_word),
  { rw [←free_group.mul_mk, free_group.mk_to_word, free_group.mk_to_word] },
  rw this,
  exact free_group.reduce.red,
end

end free_group

section
variables {α : Type*} [pseudo_emetric_space α] {s : set α} {ε : ℝ}

open emetric metric (hiding diam)
open_locale ennreal nnreal

lemma ediam_cthickening_le (ε : ℝ≥0) : diam (cthickening ε s) ≤ diam s + 2 * ε :=
begin
  refine diam_le (λ x hx y hy, ennreal.le_of_forall_pos_le_add $ λ δ hδ _, _),
  rw [mem_cthickening_iff, ennreal.of_real_coe_nnreal] at hx hy,
  have hε : (ε : ℝ≥0∞) < ε + ↑(δ / 2) :=
    ennreal.coe_lt_coe.2 (lt_add_of_pos_right _ $ half_pos hδ),
  rw [ennreal.coe_div two_ne_zero, ennreal.coe_two] at hε,
  replace hx := hx.trans_lt hε,
  replace hy := hy.trans_lt hε,
  rw inf_edist_lt_iff at hx hy,
  obtain ⟨x', hx', hxx'⟩ := hx,
  obtain ⟨y', hy', hyy'⟩ := hy,
  refine (edist_triangle_right _ _ _).trans ((add_le_add hxx'.le $ (edist_triangle _ _ _).trans $
    add_le_add hyy'.le $ edist_le_diam_of_mem hy' hx').trans_eq _),
  -- Now we're done, but `ring` won't do it :(
  rw [←add_assoc, ←two_mul, mul_add,
    ennreal.mul_div_cancel' ennreal.two_ne_zero ennreal.two_ne_top],
  abel,
end

lemma ediam_thickening_le (ε : ℝ≥0) : diam (thickening ε s) ≤ diam s + 2 * ε :=
(emetric.diam_mono $ thickening_subset_cthickening _ _).trans $ ediam_cthickening_le _

end

section
variables {α : Type*} [pseudo_metric_space α] {s : set α} {ε : ℝ}

open metric
open_locale ennreal nnreal

lemma diam_cthickening_le (hε : 0 ≤ ε) (hs : bounded s) : diam (cthickening ε s) ≤ diam s + 2 * ε :=
begin
  have : (2 : ℝ≥0∞) * @coe ℝ≥0 _ _ ⟨ε, hε⟩ ≠ ⊤ := by simp,
  refine (ennreal.to_real_mono (ennreal.add_ne_top.2 ⟨hs.ediam_ne_top, this⟩) $
    ediam_cthickening_le ⟨ε, hε⟩).trans_eq _,
  simp [ennreal.to_real_add hs.ediam_ne_top this, diam],
end

lemma diam_thickening_le (hε : 0 ≤ ε) (hs : bounded s) : diam (thickening ε s) ≤ diam s + 2 * ε :=
(diam_mono (thickening_subset_cthickening _ _) hs.cthickening).trans $ diam_cthickening_le hε hs

end

section
variables {E : Type*} [seminormed_comm_group E] {s t : set E}

open metric
open_locale pointwise

@[to_additive]
lemma diam_mul_le : diam (s * t) ≤ diam s + diam t :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp [diam_nonneg] },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { simp [diam_nonneg] },
  by_cases hs : bounded s,
  { by_cases ht : bounded t,
    { refine diam_le_of_forall_dist_le (by positivity) _,
      rintro _ ⟨x₁, y₁, hx₁, hy₁, rfl⟩ _ ⟨x₂, y₂, hx₂, hy₂, rfl⟩,
      exact dist_mul_mul_le_of_le (dist_le_diam_of_mem hs hx₁ hx₂)
        (dist_le_diam_of_mem ht hy₁ hy₂) },
    sorry },
  sorry
end

end

namespace nat
variables {α : Type*} [add_monoid_with_one α]

instance : add_action ℕ α := add_action.comp_hom _ $ nat.cast_add_monoid_hom α

@[simp] lemma vadd_def (n : ℕ) (a : α) : n +ᵥ a = ↑n + a := rfl

end nat

namespace int
variables {α : Type*} [add_group_with_one α]

instance : add_action ℤ α := add_action.comp_hom _ $ int.cast_add_hom α

@[simp] lemma vadd_def (n : ℤ) (a : α) : n +ᵥ a = ↑n + a := rfl

end int

namespace rat
variables {α : Type*} [division_ring α] [char_zero α]

instance : add_action ℚ α := add_action.comp_hom _ $ (rat.cast_hom α).to_add_monoid_hom

@[simp] lemma vadd_def (q : ℚ) (a : α) : q +ᵥ a = ↑q + a := rfl

end rat

example : nat.add_action = add_monoid.to_add_action _ := rfl
example : int.add_action = add_monoid.to_add_action _ := rfl
example : rat.add_action = add_monoid.to_add_action _ := rfl

section group
variables {α β : Type*} [group α] {f : β → α}

open function set

lemma closure_mul (g' : α) (K : set α) (hg : g' ∈ subgroup.closure K) (g : α) :
  (∃ k ∈ K, g'*k = g) → g ∈ subgroup.closure K :=
by { rintro ⟨k, hk, rfl⟩, exact mul_mem hg (subgroup.subset_closure hk) }

lemma free_group.range_lift (f : β → α) : range (free_group.lift f) = subgroup.closure (range f) :=
by rw [←free_group.lift.range_eq_closure, monoid_hom.coe_range]

lemma top_closure_to_surj_hom (hf : subgroup.closure (range f) = ⊤) :
  surjective (free_group.lift f) :=
by rw [←range_iff_surjective, free_group.range_lift, hf, subgroup.coe_top]

end group

lemma arch' {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) : ∃ n : ℕ, (n:ℝ)*x ≤ y ∧ y < (n+1 :ℝ)*x :=
begin
  refine ⟨⌊y / x⌋₊, _, _⟩,
  { rw ←le_div_iff hx,
    apply nat.floor_le,
    positivity },
  { rw ←div_lt_iff hx,
    apply nat.lt_floor_add_one }
end

lemma arch'' {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) : ∃ n : ℕ, (↑n - 1) * x ≤ y ∧ y < n * x :=
let ⟨n, hn⟩ := arch' hx hy in ⟨n + 1, by simp [hn]⟩

-- Currently false. To make this true, we need to change the definition of `seminormed_group`
lemma dist_eq_norm_inv_mul {E : Type*} [seminormed_group E] (a b : E) : dist a b = ∥a⁻¹ * b∥ :=
sorry
