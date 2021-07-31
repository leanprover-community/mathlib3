import dynamics.circle.rotation_number.translation_number

open filter set function (hiding commute)
open_locale topological_space classical

namespace circle_deg1_lift

/-- Two `circle_deg1_lift` maps define the same self-map of the circle if they differ by an
integer translation. -/
def same_circle_map : con circle_deg1_lift :=
((units.coe_hom _).comp (translate.comp
  (subgroup.gpowers (multiplicative.of_add (1:ℝ))).subtype)).con_range_of_commute $
  by { rintro f ⟨_, ⟨m, rfl⟩⟩, by simp [f.commute_translate_int m] }

lemma same_circle_map_iff {f g : circle_deg1_lift} :
  same_circle_map f g ↔ ∃ m : ℤ, f = translate (multiplicative.of_add ↑m) * g :=
by simp [same_circle_map, monoid_hom.con_range_of_commute]

lemma same_circle_map_iff' {f g : circle_deg1_lift} :
  same_circle_map f g ↔ ∃ m : ℤ, ∀ x, f x = m + g x :=
same_circle_map_iff.trans $ exists_congr $ λ m, ext_iff

end circle_deg1_lift

def circle_deg1_map : Type := circle_deg1_lift.same_circle_map.quotient

instance : has_coe_t circle_deg1_lift circle_deg1_map := con.quotient.has_coe_t _

namespace circle_deg1_map



@[simp] lemma coe_translate_int (m : ℤ) :
  ((translate (multiplicative.of_add ↑m) : circle_deg1_lift) : same_circle_map.quotient) = 1 :=
same_circle_map.eq.2 $ same_circle_map_iff.2 ⟨m, rfl⟩

noncomputable def same_circle_units_equiv :
  (same_circle_map.comap coe units.coe_mul).quotient ≃* units same_circle_map.quotient :=
monoid_hom.con_range_of_commute_units_equiv _ _

@[simp] lemma coe_same_circle_units_equiv_coe (f : units circle_deg1_lift) :
  (same_circle_units_equiv f : same_circle_map.quotient) = (f : circle_deg1_lift) :=
rfl

noncomputable def euler_cocycle (f g : same_circle_map.quotient) : ℤ :=
con.lift_on₂ f g (λ f g, ⌊f (g 0)⌋ - ⌊f 0⌋ - ⌊g 0⌋) $ λ f₁ f₂ g₁ g₂ h₁ h₂,
  begin
    rcases ⟨same_circle_map_iff'.1 h₁, same_circle_map_iff'.1 h₂⟩ with ⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩⟩,
    simp only [hm₁, hm₂, floor_int_add, g₁.map_int_add],
    abel
  end

@[simp] lemma euler_cocycle_coe (f g : circle_deg1_lift) :
  euler_cocycle f g = ⌊f (g 0)⌋ - ⌊f 0⌋ - ⌊g 0⌋ := rfl

lemma euler_cocycle_nonneg (f g : same_circle_map.quotient) :
  0 ≤ euler_cocycle f g :=
begin
  rcases ⟨f, g⟩ with ⟨⟨f⟩, ⟨g⟩⟩,
  change 0 ≤ ⌊f (g 0)⌋ - ⌊f 0⌋ - ⌊g 0⌋,
  rw [sub_nonneg, le_sub_iff_add_le'],
  exact f.le_floor_map_map_zero g
end

lemma euler_cocycle_le_one (f g : same_circle_map.quotient) :
  euler_cocycle f g ≤ 1 :=
begin
  rcases ⟨f, g⟩ with ⟨⟨f⟩, ⟨g⟩⟩,
  change ⌊f (g 0)⌋ - ⌊f 0⌋ - ⌊g 0⌋ ≤ 1,
  rw [sub_le_iff_le_add', sub_le_iff_le_add'],
  refine (f.floor_map_map_zero_le g).trans (add_le_add_left _ _),
  exact ceil_le_floor_add_one (g 0)
end

lemma euler_cocycle_mem_zero_one (f g : same_circle_map.quotient) :
  euler_cocycle f g ∈ ({0, 1} : set ℤ) :=
(euler_cocycle_nonneg f g).eq_or_lt.imp eq.symm $
  le_antisymm (euler_cocycle_le_one f g)

noncomputable instance has_inv_circle : has_inv same_circle_map.quotient :=
⟨λ f, con.lift_on f (λ f, (↑(f⁻¹) : same_circle_map.quotient)) $ λ f g H,
  begin
    rcases same_circle_map_iff.1 H with ⟨n, rfl⟩,
    refine (con.eq _).2 (same_circle_map_iff.2 ⟨-n, _⟩),
    simpa using ((g⁻¹).commute_translate_int _).units_inv_right.eq
  end⟩


lemma semiconj_by_coe_iff {f g h : circle_deg1_lift} :
  semiconj_by (h : same_circle_map.quotient) f g ↔
    ∃ m : ℤ, semiconj_by h f (translate (multiplicative.of_add ↑m) * g) :=
begin
  split,
  { intro H, rcases same_circle_map_iff.1 ((con.eq _).1 H) with ⟨m, hm⟩,
    rw ← mul_assoc at hm,
    exact ⟨m, hm⟩ },
  { rintro ⟨m, hm⟩,
    simpa using hm.map same_circle_map.mk' }
end

lemma semiconj_by_inv_symm_circle {h : same_circle_map.quotient}
  {f g : units same_circle_map.quotient} (H : semiconj_by h f g) :
  semiconj_by h⁻¹ g f :=
begin
  rcases same_circle_units_equiv.surjective f with ⟨⟨f⟩, rfl⟩,
  rcases same_circle_units_equiv.surjective g with ⟨⟨g⟩, rfl⟩,
  rcases h with ⟨h⟩,
  dsimp at *,
  rcases semiconj_by_coe_iff.1 H with ⟨m, hm⟩,
end
