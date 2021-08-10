import number_theory.geometry_of_numbers
import number_theory.quadratic_reciprocity
open geometry_of_numbers
universe u
variables (ι : Type u)
noncomputable theory
section an_example
/- this can be generalized any range of a morphism is a subgroup -/
def L (ι : Type*) : add_subgroup (ι → ℝ) := add_monoid_hom.range { to_fun := λ (f : ι → ℤ), (↑f : ι → ℝ),
  map_zero' := rfl,
  map_add' := assume x y, begin ext, rw [pi.add_apply], exact int.cast_add (x x_1) (y x_1), end }

def cube_fund (ι : Type*) [fintype ι] : fundamental_domain (L ι) :=
{ F := (unit_cube ι).val,
  hF := begin sorry; simp [unit_cube] end,
  disjoint := begin
    rintros l ⟨hl, rfl⟩ hlnz x ⟨⟨y, ⟨hyl, hyu⟩, rfl⟩, ⟨hxl, hxu⟩⟩,
    sorry; simp at *,
  end,
  covers := begin
    intro x,
    refine ⟨-(coe ∘ floor ∘ x), ⟨-(floor ∘ x), _⟩, _⟩,
    { simp only [add_monoid_hom.coe_mk, add_monoid_hom.map_neg, neg_inj],
      refl, },
    { simp [unit_cube],
      split;
      rw pi.le_def;
      intro i;
      simp,
      { exact floor_le (x i), },
      { exact (lt_floor_add_one (x i)).le, }, },
  end }

lemma cube_fund_volume [fintype ι] : volume (cube_fund ι).F = 1 := volume_Icc _

/- Another proof of Fermat -/
lemma sq_add_sq (p : ℕ) [hp : _root_.fact p.prime] (hp1 : p % 4 = 1) :
  ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
begin
  obtain ⟨j, hj⟩ := (zmod.exists_sq_eq_neg_one_iff_mod_four_ne_three p).2 (
    by rw hp1; exact dec_trivial),
  let jj := j.val_min_abs,
  let L₁ := ![(0 : ℝ), p],
  let L₂ := ![(1 : ℝ), jj],
  let L : add_subgroup (fin (nat.succ 1) → ℝ) := add_subgroup.closure {L₁, L₂},
  -- haveI : encodable L := set.countable.to_encodable (set.countable_range (function.comp coe)),
  -- have := exists_nonzero_lattice_of_two_pow_card_le_volume L,
end

end an_example
