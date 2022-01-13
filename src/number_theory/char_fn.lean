import topology.continuous_function.compact
import topology.continuous_function.locally_constant
import number_theory.padics.padic_integers

variables {X : Type*} [topological_space X] (R : Type*) [mul_zero_one_class R]

/-
/-- Bundled version of `is_clopen` -/
def clopens (H : Type*) [topological_space H] := {s : set H // is_clopen s}

variables {H : Type*} [topological_space H]
instance : inhabited (clopens H) :=
{
  default := ⟨∅, is_clopen_empty⟩
}

instance : order_bot (clopens X) :=

instance : semilattice_inf (clopens X) :=
begin
  constructor,
  swap 5, use ⟨∅, is_clopen_empty⟩,
  swap 5, rintros a b, refine (a.val ⊆ b.val),
  swap 8, rintros a b, refine ⟨a.val ∩ b.val, is_clopen.inter a.prop b.prop⟩,
  { rintros a, apply set.empty_subset, },
  { rintros a b, apply set.inter_subset_left, },
  { rintros a b, apply set.inter_subset_right, },
  { rintros a b c ab ac, apply set.subset_inter_iff.2 ⟨ab, ac⟩, },
  { rintros a, apply set.subset.refl, },
  { rintros a b c ab ac, apply set.subset.trans ab ac, },
  { rintros a b ab ba, apply subtype.eq, apply set.subset.antisymm ab ba, },
end

instance : lattice (clopens X) :=
begin
  refine subtype.lattice _ _,
  { rintros x y, apply is_clopen.union, },
  { rintros x y, apply is_clopen.inter, },
end
-/

/-- Characteristic functions are locally constant functions taking `x : X` to `1` if `x ∈ U`,
  where `U` is a clopen set, and `0` otherwise. -/
noncomputable def char_fn {U : set X} (hU : is_clopen U) : locally_constant X R :=
{
  to_fun := λ x, by classical; exact if (x ∈ U) then 1 else 0,
  is_locally_constant :=
    begin
      rw is_locally_constant.iff_exists_open, rintros x,
      by_cases x ∈ U,
      { refine ⟨U, hU.1, h, _⟩, rintros y hy, simp [h, hy], },
      { rw ←set.mem_compl_iff at h, refine ⟨Uᶜ, (is_clopen.compl hU).1, h, _⟩,
        rintros y hy, rw set.mem_compl_iff at h, rw set.mem_compl_iff at hy,
        simp [h, hy], },
    end,
}

lemma char_fn_one [nontrivial R] (x : X) {U : set X} (hU : is_clopen U) :
  x ∈ U ↔ char_fn R hU x = (1 : R) :=
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

lemma char_fn_zero [nontrivial R] (x : X) {U : set X} (hU : is_clopen U) :
  x ∈ U → false ↔ char_fn R hU x = (0 : R) :=
begin
  rw char_fn,
  simp only [ite_eq_right_iff, one_ne_zero, locally_constant.coe_mk],
end

lemma char_fn_inj [nontrivial R] {U V : set X} (hU : is_clopen U) (hV : is_clopen V)
  (h : char_fn R hU = char_fn R hV) : U = V :=
begin
  ext,
  rw locally_constant.ext_iff at h, specialize h x,
  split,
  { intros h', apply (char_fn_one R _ _).2,
    { rw (char_fn_one R _ _).1 h' at h, rw h.symm, }, },
  { intros h', apply (char_fn_one R _ _).2,
    { rw (char_fn_one R _ _).1 h' at h, rw h, }, },
end
