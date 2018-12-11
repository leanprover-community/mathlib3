import algebra.euclidean_domain ring_theory.ideals ring_theory.associated
noncomputable theory
local attribute [instance] classical.dec
open euclidean_domain set ideal

def is_coprime {α} [comm_ring α] (x y : α) : Prop :=
span ({x, y} : set α) = ⊤

theorem mem_span_pair {α} [comm_ring α] {x y z : α} :
  z ∈ span (insert y {x} : set α) ↔ ∃ a b, a * x + b * y = z :=
begin
  simp only [mem_span_insert, mem_span_singleton', exists_prop],
  split,
  { rintros ⟨a, b, ⟨c, hc⟩, h⟩,
    exact ⟨c, a, by simp [h, hc]⟩ },
  { rintro ⟨b, c, e⟩, exact ⟨c, b * x, ⟨b, rfl⟩, by simp [e.symm]⟩ }
end

theorem is_coprime_def {α} [comm_ring α] {x y : α} :
  is_coprime x y ↔ ∀ z, ∃ a b, a * x + b * y = z :=
by simp [is_coprime, submodule.eq_top_iff', mem_span_pair]

theorem is_coprime_self {α} [comm_ring α] (x y : α) :
  is_coprime x x ↔ is_unit x :=
by rw [← span_singleton_eq_top]; simp [is_coprime]

theorem span_gcd {α} [euclidean_domain α] (x y : α) :
  span ({gcd x y} : set α) = span ({x, y} : set α) :=
begin
  apply le_antisymm; refine span_le.1 _,
  { simp [submodule.span_span, mem_span_pair, submodule.le_def', mem_span_singleton'],
    assume a b ha,
    exact ⟨b * gcd_a x y, b * gcd_b x y, by rw [← ha, gcd_eq_gcd_ab x y];
      simp [mul_add, mul_comm, mul_left_comm]⟩ },
  { assume z ,
    simp [mem_span_singleton, euclidean_domain.gcd_dvd_left, mem_span_pair,
      @eq_comm _ _ z] {contextual := tt},
    assume a b h,
    exact dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (gcd_dvd_right _ _) _) }
end

theorem gcd_is_unit_iff {α} [euclidean_domain α] {x y : α} :
  is_unit (gcd x y) ↔ is_coprime x y :=
by rw [← span_singleton_eq_top, span_gcd, is_coprime]

theorem is_coprime_of_dvd {α} [euclidean_domain α] {x y : α}
  (z : ¬ (x = 0 ∧ y = 0)) (H : ∀ z ∈ nonunits α, z ≠ 0 → z ∣ x → ¬ z ∣ y) :
  is_coprime x y :=
begin
  rw [← gcd_is_unit_iff],
  by_contra h,
  refine H _ h _ (gcd_dvd_left _ _) (gcd_dvd_right _ _),
  rwa [ne, euclidean_domain.gcd_eq_zero_iff]
end

theorem dvd_or_coprime {α} [euclidean_domain α] (x y : α)
  (h : irreducible x) : x ∣ y ∨ is_coprime x y :=
begin
  refine or_iff_not_imp_left.2 (λ h', _),
  unfreezeI, apply is_coprime_of_dvd,
  { rintro ⟨rfl, rfl⟩, simpa using h },
  { rintro z nu nz ⟨w, rfl⟩ dy,
    refine h' (dvd.trans _ dy),
    simpa using mul_dvd_mul_left z (is_unit_iff_dvd_one.1 $
      (of_irreducible_mul h).resolve_left nu) }
end

theorem is_maximal_of_irreducible {α} [euclidean_domain α] {x : α}
  (irr : irreducible x) : is_maximal (span ({x} : set α)) :=
{ left := by simp [span_singleton_eq_top]; exact irr.1,
  right := λ S ss,
    have hxS : x ∈ S, from ss.1 (by simp [mem_span_singleton]),
    begin
      simp [lt_iff_le_not_le, -not_le, submodule.le_def', not_forall, mem_span_singleton] at ss,
      rcases ss.2 with ⟨y, h₁, h₂⟩,
      apply submodule.eq_top_iff'.2,
      assume z,
      have : span ({x, y} : set α) ≤ S,
      { simp [span_le, subset_def, or_imp_distrib, *] {contextual := tt} },
      refine submodule.le_def.1 this _,
      rw (show _ = _, from (dvd_or_coprime x y irr).resolve_left h₂); simp
    end }
