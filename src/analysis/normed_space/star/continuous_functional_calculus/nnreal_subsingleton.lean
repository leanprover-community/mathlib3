import analysis.normed_space.star.continuous_functional_calculus.basic


open_locale nnreal

instance : star_ring ℝ≥0 :=
{ star := id,
  star_involutive := λ _, rfl,
  star_mul := mul_comm,
  star_add := λ _ _, rfl }

instance : has_trivial_star ℝ≥0 :=
{ star_trivial := λ _, rfl }

instance : has_continuous_star ℝ≥0 :=
{ continuous_star := continuous_id }

instance : star_module ℝ≥0 ℝ :=
{ star_smul := by simp only [star_trivial, eq_self_iff_true, forall_const] }

variables {X A : Type*} [topological_space X] [ring A] [star_ring A] [algebra ℝ A]
  (φ : C(X, ℝ≥0) →⋆ₐ[ℝ≥0] A)

noncomputable def continuous_map.pos_part (f : C(X, ℝ)) : C(X, ℝ≥0) :=
{ to_fun := λ x, ⟨(f ⊔ 0) x, le_sup_right⟩, }

@[simp]
lemma coe_comp_pos_part (f : C(X, ℝ)) : continuous_map.coe_nnreal_real.comp f.pos_part = f ⊔ 0 :=
continuous_map.ext (λ x, rfl)

noncomputable def continuous_map.neg_part (f : C(X, ℝ)) : C(X, ℝ≥0) :=
{ to_fun := λ x, ⟨-(f ⊓ 0) x, by simp only [le_refl,
 right.nonneg_neg_iff,
 continuous_map.inf_apply,
 continuous_map.zero_apply,
 min_le_iff,
 or_true]⟩, }

@[simp]
lemma coe_comp_neg_part (f : C(X, ℝ)) : continuous_map.coe_nnreal_real.comp f.neg_part = -(f ⊓ 0) :=
continuous_map.ext (λ x, rfl)

lemma neg_part_eq_of_pos (f : C(X, ℝ)) (hf : 0 ≤ f) : (f : C(X, ℝ)).neg_part = 0 :=
begin
  ext,
  rw continuous_map.neg_part,
  simp only [continuous_map.inf_apply, continuous_map.zero_apply, continuous_map.coe_mk, subtype.coe_mk, nonneg.coe_zero,
  neg_eq_zero, min_eq_right_iff],
  exact hf a,
end

lemma algebra_map_pos_part (r : ℝ) (hr : 0 ≤ r) :
  (algebra_map ℝ C(X, ℝ) r).pos_part = algebra_map ℝ≥0 C(X, ℝ≥0) ⟨r, hr⟩ :=
begin
  ext,
  rw continuous_map.pos_part,
  simpa only [continuous_map.sup_apply, algebra_map_apply, algebra.id.smul_eq_mul, mul_one, continuous_map.zero_apply,
  continuous_map.coe_mk, subtype.coe_mk, max_eq_left_iff] using hr,
end

lemma algebra_map_neg_part (r : ℝ) (hr : 0 ≤ r) :
  (algebra_map ℝ C(X, ℝ) r).neg_part = 0 :=
begin
  ext,
  rw continuous_map.neg_part,
  simpa only [continuous_map.inf_apply, algebra_map_apply, algebra.id.smul_eq_mul, mul_one, continuous_map.zero_apply,
  continuous_map.coe_mk, subtype.coe_mk, nonneg.coe_zero, neg_eq_zero, min_eq_right_iff] using hr,
end

lemma pos_part_one : (1 : C(X, ℝ)).pos_part = 1 :=
by { rw [←map_one (algebra_map ℝ C(X, ℝ)), algebra_map_pos_part 1 zero_le_one],
     ext,
     refl, }

lemma neg_part_one : (1 : C(X, ℝ)).neg_part = 0 :=
by rw [←map_one (algebra_map ℝ C(X, ℝ)), algebra_map_neg_part 1 zero_le_one]

lemma pos_part_mul (f g : C(X, ℝ)) :
  (f * g).pos_part = f.pos_part * g.pos_part + f.neg_part * g.neg_part :=
sorry

lemma neg_part_mul (f g : C(X, ℝ)) :
  (f * g).neg_part = f.pos_part * g.neg_part + f.neg_part * g.pos_part :=
sorry

lemma coe_nnreal_comp_injective :
  function.injective (continuous_map.coe_nnreal_real.comp : C(X, ℝ≥0) → C(X, ℝ)) :=
begin
  intros f g h,
  ext x,
  exact fun_like.congr_fun h x,
end

variable (X)
def foo : C(X, ℝ≥0) →⋆ₐ[ℝ≥0] C(X, ℝ) :=
continuous_map.comp_star_alg_hom X (star_alg_hom.of_id ℝ≥0 ℝ) continuous_induced_dom

@[simp]
lemma coe_foo : ⇑(foo X) = continuous_map.coe_nnreal_real.comp :=
by ext; refl

lemma foo_injective : function.injective (foo X) :=
begin
  intros f g h,
  ext x,
  exact fun_like.congr_fun h x,
end

variable {X}

instance {X Y : Type*} [topological_space X] [topological_space Y] [has_add Y]
  [has_continuous_add Y] [partial_order Y] [covariant_class Y Y (+) (≤)] :
  covariant_class C(X, Y) C(X, Y) (+) (≤) :=
{ elim := λ f g h h' x, add_le_add_left (h' x) _ }

lemma pos_part_add_neg_parts (f g : C(X, ℝ)) :
  (f + g).pos_part + f.neg_part + g.neg_part = (f + g).neg_part + f.pos_part + g.pos_part :=
begin
  apply foo_injective,
  simp only [map_add (foo X)],
  simp only [coe_foo, coe_comp_neg_part, coe_comp_pos_part],
  suffices : (f + g) ⊓ 0 + (f + g) ⊔ 0 = (f ⊓ 0 + f ⊔ 0) + (g ⊓ 0 + g ⊔ 0),
  linear_combination this,
  simp only [inf_add_sup, add_zero],
end


example : C(X, ℝ) →⋆ₐ[ℝ] A :=
{ to_fun := λ f, φ f.pos_part - φ f.neg_part,
  map_one' := by rw [pos_part_one, neg_part_one, map_one, map_zero, sub_zero],
  map_mul' := λ f g,
  begin
    simp only [pos_part_mul, neg_part_mul, map_add, map_mul, mul_sub, sub_mul],
    noncomm_ring,
  end,
  map_zero' := _,
  map_add' := λ f g,
  begin
    have := fun_like.congr_arg φ (pos_part_add_neg_parts f g),
    simp only [map_add, ←add_assoc] at this,
    rw [←sub_eq_zero] at ⊢ this,
    simp only [←sub_add, ←sub_sub] at ⊢ this,
    simp only [sub_eq_add_neg] at ⊢ this,
    calc _ = _ : by noncomm_ring
    ...    = _ : this,
  end,
  commutes' := _,
  map_star' := λ x, by simp only [star_trivial, star_sub, ←map_star] }

#exit


take `A := fin n → ℝ`. This is an `ℝ`-algebra. check.
Now take `a : fin n → ℝ`. Define a function `φ : C(spectrum ℝ a, ℝ) → (fin n → ℝ)`
By `φ f
