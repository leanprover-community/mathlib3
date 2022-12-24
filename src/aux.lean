import algebra.hom.units

universes u v w

open function units

variables {α : Type*} {M : Type u} {N : Type v} {P : Type w} [monoid M] [monoid N] [monoid P]

lemma map_injective {f : M →* N} (hf : injective f) : injective (map f) :=
begin
  intros x y hxy,
  simp_rw [← units.eq_iff, units.coe_map] at hxy,
  exact units.ext (hf hxy),
end
