import topology.homotopy.basic

universes u v

variables (ι : Type u)

noncomputable theory

open_locale unit_interval classical
/-
(ι → I) → X : surface?
-/

def baz : C(ι → ℝ, ι → I) :=
{ to_fun := λ x i, continuous_map.id.Icc_extend (@zero_le_one ℝ _) (x i) }

lemma baz_apply_of_mem (x : ι → ℝ) (h : x ∈ (set.univ : set ι).pi (λ i, I)) :
  baz ι x = (λ i, ⟨x i, set.mem_univ_pi.1 h _⟩) :=
begin
  ext i,
  rw [baz, continuous_map.coe_mk, continuous_map.coe_Icc_extend, continuous_map.id_coe],
  apply congr_arg,
  rw set.Icc_extend_of_mem _ _ (set.mem_univ_pi.1 h _),
  refl,
end

structure foo {X : Type v} [topological_space X] (x : X) extends C(ι → I, X) :=
(boundary : ∀ p : ι → I, (∃ i, p i = 0 ∨ p i = 1) → to_fun p = x)

namespace foo

variable {ι}
variables {X : Type v} [topological_space X] {x₀ : X}

instance : has_coe_to_fun (foo ι x₀) (λ _, (ι → I) → X) := ⟨λ f, f.to_fun⟩

def extend (f : foo ι x₀) : C(ι → ℝ, X) := f.to_continuous_map.comp (baz ι)

lemma extend_apply_of_mem {f : foo ι x₀} {p : ι → ℝ} (h : p ∈ (set.univ : set ι).pi (λ i, I)) :
  f.extend p = f (λ i, ⟨p i, set.mem_univ_pi.1 h _⟩) :=
begin
  rw [extend, continuous_map.comp_apply, baz_apply_of_mem _ _ h],
  refl,
end

@[continuity]
lemma continuous (f : foo ι x₀) : continuous ⇑f := f.to_continuous_map.continuous

lemma apply_of_exists_eq_zero_or_eq_one {f : foo ι x₀} (p : ι → I) (hx : ∃ i, p i = 0 ∨ p i = 1) :
  f p = x₀ := f.boundary _ hx

def refl : foo ι x₀ :=
{ to_fun := λ i, x₀,
  boundary := λ p hp, rfl }

def symm (f : foo ι x₀) (i : ι) : foo ι x₀ :=
{ to_fun := λ t, f (λ j, if i = j then σ (t j) else t j),
  continuous_to_fun := begin
    apply f.continuous.comp,
    rw continuous_pi_iff,
    intro j,
    split_ifs;
    continuity
  end,
  boundary := begin
    rintros p ⟨j, hj⟩,
    dsimp only,
    apply apply_of_exists_eq_zero_or_eq_one,
    use j,
    rcases hj with (hj | hj); rw hj; finish
  end }

def trans (f g : foo ι x₀) (i : ι) : foo ι x₀ :=
{ to_fun := λ t,
  if (t i : ℝ) ≤ 1/2 then
    f.extend (λ j, if i = j then 2 * t j else t j)
  else
    g.extend (λ j, if i = j then 2 * t j - 1 else t j),
  continuous_to_fun := begin
    apply continuous_if_le,
    { continuity },
    { continuity },
    { apply continuous.continuous_on,
      apply continuous.comp,
      { continuity },
      { rw continuous_pi_iff,
        intro j,
        split_ifs;
        continuity } },
    { apply continuous.continuous_on,
      apply continuous.comp,
      { continuity },
      { rw continuous_pi_iff,
        intro j,
        split_ifs;
        continuity } },
    { intros x hx,
      rw [extend_apply_of_mem, extend_apply_of_mem],
      { rw [apply_of_exists_eq_zero_or_eq_one, apply_of_exists_eq_zero_or_eq_one];
        { use i,
          norm_num [hx] } },
      { rw set.mem_pi,
        intros j hj,
        split_ifs,
        { rw [←h, hx],
          norm_num },
        { exact subtype.mem (x j) } },
      { rw set.mem_pi,
        intros j hj,
        split_ifs,
        { rw [←h, hx],
          norm_num },
        { exact subtype.mem (x j) } } }
  end,
  boundary := begin
    rintros p ⟨j, hj⟩,
    dsimp only,
    split_ifs,
    { rw [extend_apply_of_mem, apply_of_exists_eq_zero_or_eq_one],
      { use j,
        cases hj,
        { left,
          norm_num [hj] },
        { right,
          apply subtype.ext,
          rw [subtype.coe_mk, if_neg, hj],
          intro hij,
          norm_num [hij, hj] at h } },
      { rw set.mem_pi,
        intros k hk,
        split_ifs with hik hik,
        { rw [unit_interval.mul_pos_mem_iff zero_lt_two, ←hik],
          exact ⟨unit_interval.nonneg _, h⟩ },
        { exact subtype.mem _ } } },
    {  rw [extend_apply_of_mem, apply_of_exists_eq_zero_or_eq_one],
      { use j,
        cases hj,
        { left,
          apply subtype.ext,
          rw [subtype.coe_mk, if_neg, hj],
          intro hij,
          norm_num [hij, hj] at h },
        { right,
          norm_num [hj] } },
      { rw set.mem_pi,
        intros k hk,
        split_ifs with hik hik,
        { rw [unit_interval.two_mul_sub_one_mem_iff, ←hik],
          exact ⟨le_of_not_le h, unit_interval.le_one _⟩, },
        { exact subtype.mem _ } } }
  end } .

abbreviation homotopy (f g : foo ι x₀) :=
continuous_map.homotopy_rel f.to_continuous_map g.to_continuous_map {p | ∃ i, p i = 0 ∨ p i = 1}

namespace homotopy

def refl (f : foo ι x₀) : homotopy f f :=
{ to_fun := λ t, f t.2,
  to_fun_zero := λ _, rfl,
  to_fun_one := λ _, rfl,
  prop' := λ t x hx, ⟨rfl, rfl⟩ }

def symm {f g : foo ι x₀} (h : homotopy f g) : homotopy g f :=
{ to_fun := λ t, h (σ t.1, t.2),
  to_fun_zero := sorry,
  to_fun_one := sorry,
  prop' := sorry }

end homotopy

end foo
