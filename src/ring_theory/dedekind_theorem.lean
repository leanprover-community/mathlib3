/-- temporary
 variables {S : Type*} [cancel_comm_monoid_with_zero S] [decidable_rel (has_dvd.dvd : S → S → Prop)]
 (f : R →* S) (hf : function.surjective f)

lemma monoid_hom.image_dvd_image_of_dvd {α β : Type*} [comm_monoid α] [comm_monoid β] (f : α →* β)
 {a b : α} (H : a ∣ b) : f a ∣ (f b) :=
by { obtain ⟨c, rfl⟩ := H, simp only [map_mul, dvd_mul_right] }

lemma monoid_hom.image_dvd_image_iff_dvd_of_surjective {α β : Type*} [comm_monoid α] [comm_monoid β]
  (f : α ≃* β) {a b : α} : a ∣ b ↔ f a ∣ (f b) :=
begin
  refine ⟨λ h, monoid_hom.image_dvd_image_of_dvd (f : α →* β) h, λ h, _ ⟩,
  obtain ⟨c', hc'⟩ := h,
  sorry,
end

lemma multiplicity_eq_multiplicity_iff {p q : R} (hp : prime p) (hq : q ≠ 0) :
  multiplicity p q = multiplicity (f p) (f q) :=
begin
  by_cases hcases : finite p q,
  have temp := multiplicity.finite_def.1 hcases,
  apply le_antisymm,
  rw ← enat.le_iff_of_dom (multiplicity.finite_iff_dom.1 hcases),
  apply multiplicity.le_multiplicity_of_pow_dvd,

end

lemma multiplicity_eq_multiplicity_associates_mk
  [decidable_rel (has_dvd.dvd : associates R → associates R → Prop)] {p q : R} (hp : prime p) (hq : q ≠ 0) :
  multiplicity p q = multiplicity (associates.mk p) (associates.mk q) :=
begin
  by_cases hcases : finite p q,


  /-
  have finite₁ := multiplicity.finite_prime_left hp hq,
  have finite₂ := multiplicity.finite_prime_left ((associates.prime_mk p).2 hp)
    (associates.mk_ne_zero.2 hq),
  apply le_antisymm,
  { rw ← enat.le_iff_of_dom,
    apply multiplicity.le_multiplicity_of_pow_dvd,
    rw [← associates.mk_pow, associates.mk_dvd_mk],
    exact multiplicity.pow_multiplicity_dvd finite₁ },

  { rw ← enat.le_iff_of_dom,
    apply multiplicity.le_multiplicity_of_pow_dvd,
    rw [← associates.mk_dvd_mk, associates.mk_pow],
    exact multiplicity.pow_multiplicity_dvd finite₂ },-/
end


-/
