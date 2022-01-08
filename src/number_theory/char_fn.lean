import topology.continuous_function.compact
import topology.continuous_function.locally_constant

variables {X : Type*} [topological_space X] (R : Type*) [mul_zero_one_class R]

/-- Bundled version of `is_clopen` -/
def clopen_sets (H : Type*) [topological_space H] := {s : set H // is_clopen s}

variables {H : Type*} [topological_space H]
instance : inhabited (clopen_sets H) :=
{
  default := ⟨∅, is_clopen_empty⟩
}

/-- Characteristic functions are locally constant functions taking `x : X` to `1` if `x ∈ U`,
  where `U` is a clopen set, and `0` otherwise. -/
noncomputable def char_fn (U : clopen_sets X) : locally_constant X R :=
{
  to_fun := λ x, by classical; exact if (x ∈ U.val) then 1 else 0,
  is_locally_constant :=
    begin
      rw is_locally_constant.iff_exists_open, rintros x,
      by_cases x ∈ U.val,
      { refine ⟨U.val, ((U.prop).1), h, _⟩, rintros y hy, simp [h, hy], },
      { rw ←set.mem_compl_iff at h, refine ⟨(U.val)ᶜ, (is_clopen.compl U.prop).1, h, _⟩,
        rintros y hy, rw set.mem_compl_iff at h, rw set.mem_compl_iff at hy,
        simp [h, hy], },
    end,
}

lemma char_fn_one [nontrivial R] (x : X) (U : clopen_sets X) :
  x ∈ U.val ↔ char_fn R U x = (1 : R) :=
begin
  rw char_fn, simp only [locally_constant.coe_mk, ite_eq_left_iff],
  split, any_goals { intro h, },
  { intro h',
    exfalso, apply h', exact h, },
  { by_contra h', apply @one_ne_zero _ _ _,
    swap, exact R,
    any_goals { apply_instance, },
    { symmetry, apply h, apply h', }, },
end

lemma char_fn_zero [nontrivial R] (x : X) (U : clopen_sets X) :
  x ∈ U.val → false ↔ char_fn R U x = (0 : R) :=
begin
  rw char_fn,
  simp only [ite_eq_right_iff, one_ne_zero, locally_constant.coe_mk],
end

lemma char_fn_inj [nontrivial R] : function.injective (@char_fn X _ R _) :=
begin
  rintros U V h, ext,
  rw locally_constant.ext_iff at h, specialize h x,
  split,
  any_goals { intros h', apply (char_fn_one R _ _).2, rw (char_fn_one R _ _).1 h' at h, rw h, },
end
