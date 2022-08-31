import analysis.convex.basic
import analysis.normed_space.add_torsor_bases
import analysis.normed_space.basic
import analysis.normed_space.linear_isometry
import data.real.basic
import data.set.pointwise
import linear_algebra.affine_space.pointwise

open_locale pointwise

def relint {V : Type} [add_comm_group V] [module ℝ V] [topological_space V]
  (A : set V) :=
(coe : affine_span ℝ A → V) '' interior ((coe : affine_span ℝ A → V) ⁻¹' A)

lemma relint_def {V : Type} [add_comm_group V] [module ℝ V] [topological_space V]
  (A : set V) :
relint A = (coe : affine_span ℝ A → V) '' interior ((coe : affine_span ℝ A → V) ⁻¹' A) := rfl

-- lemma relint_vadd {V : Type} [add_comm_group V] [has_continuous]

variables {V : Type} [normed_add_comm_group V] [normed_space ℝ V]
          {W : Type} [normed_add_comm_group W] [normed_space ℝ W]

/- lemma relint_isometry (A : set V) (φ : V →ₛₗᵢ[ℝ] W) :
relint (φ '' A) = φ '' (relint A) :=
begin

end -/

/- instance bla : has_vadd V (affine_subspace ℝ V) :=
{ vadd := λ x E,
  begin
    refine ⟨x +ᵥ ↑E, _⟩,
    rintro c - - - ⟨p₁, hp₁, rfl⟩ ⟨p₂, hp₂, rfl⟩ ⟨p₃, hp₃, rfl⟩,
    refine ⟨c • (p₁ - p₂) + p₃, _, _⟩,
    { apply E.smul_vsub_vadd_mem ; assumption },
    { simp only [vadd_eq_add, vsub_eq_sub, add_left_comm, add_sub_add_left_eq_sub] },
  end } -/

/- lemma affine_subspace.coe_vadd (E : affine_subspace ℝ V) (x : V) :
((x +ᵥ E) : set V) = x +ᵥ (E : set V) := rfl -/

lemma affine_subspace.le_neg_vadd (E F : affine_subspace ℝ V) (x : V) :
E ≤ (-x) +ᵥ F ↔ x +ᵥ E ≤ F :=
begin
  simp only [affine_subspace.le_def, affine_subspace.coe_pointwise_vadd],
  split,
  { rintro h - ⟨y, hy, rfl⟩,
    obtain ⟨z, hz, rfl⟩ := h hy,
    simp only [hz, vadd_eq_add, add_neg_cancel_left] },
  { rintro h y hy,
    refine ⟨x +ᵥ y, h ⟨y, hy, rfl⟩, _⟩,
    simp only [vadd_eq_add, neg_add_cancel_left] },
end

lemma neg_vadd_mem_affine_subspace_iff (E : affine_subspace ℝ V) (x y : V) :
(-x) +ᵥ y ∈ E ↔ y ∈ x +ᵥ E :=
begin
  split,
  {
    intro h,
    refine ⟨-x +ᵥ y, h, _⟩,
    simp only [vadd_eq_add, affine_equiv.coe_coe, affine_equiv.const_vadd_apply,
      add_neg_cancel_left],
  },
  {
    rintro ⟨z, hz, rfl⟩,
    simpa only [affine_equiv.coe_coe, affine_equiv.const_vadd_apply, vadd_eq_add,
      neg_add_cancel_left] using hz,
  },
end

lemma affine_span_vadd_le (A : set V) (x : V) :
affine_span ℝ (x +ᵥ A) ≤ x +ᵥ affine_span ℝ A :=
begin
  rw [affine_span_le],
  rintro - ⟨y, hy, rfl⟩,
  exact ⟨y, subset_affine_span ℝ _ hy, rfl⟩,
end

lemma affine_span_vadd (A : set V) (x : V) :
affine_span ℝ (x +ᵥ A) = x +ᵥ affine_span ℝ A :=
begin
  refine le_antisymm (by apply affine_span_vadd_le) _,
  have := affine_span_vadd_le (x +ᵥ A) (-x),
  simpa only [neg_vadd_vadd, affine_subspace.le_neg_vadd] using this,
end

--lemma relint_iso (A : set V) (f : V ≃ₜ W) (hf : )

lemma relint_vadd_subset (A : set V) (x : V) :
relint (x +ᵥ A) ⊆ x +ᵥ relint A :=
begin
  simp only [relint_def],
  rintro - ⟨y, hy, rfl⟩,
  refine ⟨y - x, _, _⟩, swap,
  { apply add_sub_cancel'_right },
  refine ⟨⟨y - x, _⟩, _, rfl⟩,
  { change ↑y - x ∈ affine_span ℝ A,
    rw [←affine_subspace.vadd_mem_pointwise_vadd_iff, affine_subspace.pointwise_vadd_span],
    swap, exact x,
    simp only [vadd_eq_add, add_sub_cancel'_right],
    exact y.property },
  obtain ⟨y, yprop⟩ := y,
  rw [←affine_subspace.pointwise_vadd_span] at yprop,
  simp only [mem_interior_iff_mem_nhds, mem_nhds_induced] at hy ⊢,
  simp only [mem_nhds_iff, subtype.coe_mk, exists_prop] at hy ⊢,
  obtain ⟨t, ⟨u, ut, uopen, yu⟩, ht⟩ := hy,
  refine ⟨(-x) +ᵥ u, ⟨(-x) +ᵥ u, subset_refl _, _, _⟩, _⟩,
  { apply uopen.vadd, apply_instance, },
  { refine ⟨y, yu, _⟩,
    rw [vadd_eq_add, ←sub_eq_neg_add], },

  rintro ⟨z, hz₁⟩ hz₂,
  simp only [set.mem_preimage, subtype.coe_mk] at hz₂ ⊢,
  obtain ⟨z, hz₂, rfl⟩ := hz₂,
  change (-x) +ᵥ z ∈ affine_span ℝ A at hz₁,
  rw [neg_vadd_mem_affine_subspace_iff, affine_subspace.pointwise_vadd_span] at hz₁,
  let w : affine_span ℝ (x +ᵥ A) := ⟨z, hz₁⟩,
  have hw: w ∈ (coe : affine_span ℝ (x +ᵥ A) → V) ⁻¹' t := ut hz₂,
  rw [←set.mem_vadd_set_iff_neg_vadd_mem],
  exact ht hw,
end

lemma relint_vadd (A : set V) (x : V) :
relint (x +ᵥ A) = x +ᵥ relint A :=
begin
  refine subset_antisymm (by apply relint_vadd_subset) _,
  suffices hs : relint ((-x) +ᵥ (x +ᵥ A)) ⊆ (-x) +ᵥ relint (x +ᵥ A),
  { simp only [neg_vadd_vadd] at hs,
    rintro - ⟨y, hy, rfl⟩,
    obtain ⟨z, hz, rfl⟩ := hs hy,
    simpa only [vadd_eq_add, add_neg_cancel_left] using hz },
  apply relint_vadd_subset,
end

lemma submodule.subtype_preimage_vsub {A : set V} {E : submodule ℝ V} (hAE : A ⊆ E) :
E.subtype ⁻¹' (A -ᵥ A) = (E.subtype ⁻¹' A) -ᵥ (E.subtype ⁻¹' A) :=
begin
  ext, split,
  { rintro ⟨x₁, x₂, hx₁, hx₂, h⟩,
    refine ⟨⟨x₁, hAE hx₁⟩, ⟨x₂, hAE hx₂⟩, hx₁, hx₂, _⟩,
    ext,
    exact h, },
  { rintro ⟨x₁, x₂, hx₁, hx₂, rfl⟩,
    refine ⟨↑x₁, ↑x₂, hx₁, hx₂, rfl⟩, },
end

lemma vadd_vsub_vadd_cancel_left' (x : V) (A B : set V) :
(x +ᵥ A) -ᵥ (x +ᵥ B) = A -ᵥ B :=
begin
  ext, split,
  { rintro ⟨-, -, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, rfl⟩,
    rw [vadd_vsub_vadd_cancel_left x],
    exact ⟨a, b, ha, hb, rfl⟩, },
  { rintro ⟨a, b, ha, hb, rfl⟩,
    rw [←vadd_vsub_vadd_cancel_left x],
    exact ⟨_, _, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, rfl⟩ },
end

lemma affine_span_eq_vector_span {A : set V} {x : V} (hxA : x ∈ A) :
(affine_span ℝ (-x +ᵥ A) : set V) = vector_span ℝ A :=
begin
  suffices hs : (affine_span ℝ (-x +ᵥ A)).direction = vector_span ℝ A,
  {
    rw [←affine_subspace.pointwise_vadd_span, ←direction_affine_span],
    ext y, split,
    { rintro ⟨y, hy, rfl⟩,
      simp only [affine_equiv.coe_coe, affine_equiv.const_vadd_apply, vadd_eq_add],
      rw [←sub_eq_neg_add, affine_subspace.coe_direction_eq_vsub_set_right],
      { refine ⟨y, hy, rfl⟩ },
      { apply subset_affine_span ; assumption } },
    { rintro h,
    refine ⟨y + x, _, _⟩,
    { rw [affine_subspace.mem_coe],
      refine affine_subspace.vadd_mem_of_mem_direction h _,
      { apply subset_affine_span ; assumption } },
    simp only [affine_equiv.coe_coe, affine_equiv.const_vadd_apply, vadd_eq_add,
      neg_add_cancel_comm_assoc], }
  },
  simp only [direction_affine_span, vector_span_def, vadd_vsub_vadd_cancel_left'],
end

lemma affine_subspace.coe_sort_coe (E : affine_subspace ℝ V) :
(E : Type) = (E : set V) := rfl

def affine_span_homeomorph_vector_span {A : set V} {x : V} (hxA : x ∈ A) :
affine_span ℝ (-x +ᵥ A) ≃ₜ vector_span ℝ A :=
begin
  refine ⟨_, _, _⟩,
  { rw [←set_like.coe_sort_coe, ←affine_span_eq_vector_span hxA],
    exact equiv.refl _ },
  admit { simp only [auto_param_eq],
    rw [←affine_subspace.coe_sort_coe], },
  admit,
end

lemma nonempty_relint_of_nonempty_of_convex [finite_dimensional ℝ V] {A : set V}
(Ane : A.nonempty) (Acv : convex ℝ A) :
(relint A).nonempty :=
begin
  obtain ⟨x, hx⟩ := Ane,
  rw [←vadd_neg_vadd x A, relint_vadd],
  apply set.nonempty.vadd_set,
  let A' := (vector_span ℝ A).subtype ⁻¹' ((-x) +ᵥ A),
  have Acv' : convex ℝ A' := (Acv.vadd _).linear_preimage _,
  obtain ⟨⟨y, hy₁⟩, hy₂⟩ : (interior A').nonempty,
  { rw [Acv'.interior_nonempty_iff_affine_span_eq_top,
        affine_subspace.affine_span_eq_top_iff_vector_span_eq_top_of_nonempty], swap,
    { refine ⟨0, _⟩,
      simp only [submodule.coe_subtype, set.mem_preimage, submodule.coe_zero],
      refine ⟨x, hx, _⟩,
      simp only [vadd_eq_add, add_left_neg] },
    { simp only [A', vector_span],
      refine eq.trans _ submodule.span_span_coe_preimage,
      rw [←submodule.subtype_preimage_vsub, vadd_vsub_vadd_cancel_left' (-x) A A],
      { refl },
      rintro - ⟨a, ha, rfl⟩,
      simp only [vadd_eq_add, set_like.mem_coe, ←sub_eq_neg_add],
      apply vsub_mem_vector_span ; assumption } },
  rw [relint_def, set.nonempty_image_iff],
  refine ⟨⟨y, _⟩, _⟩,
  { admit },
  rw [mem_interior] at hy₂ ⊢, -- want vector_span ℝ A = affine_span ℝ (-x +ᵥ A)
  admit, -- obtain ⟨t, ht, topen, yt⟩ := hy,
end
