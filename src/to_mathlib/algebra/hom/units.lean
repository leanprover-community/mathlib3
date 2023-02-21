import algebra.hom.units

@[simp] lemma is_univ_inv_iff {γ : Type*} [division_monoid γ] {x : γ} :
  is_unit x⁻¹ ↔ is_unit x :=
begin
  split;
  intro h;
  simpa using h.inv
end
