import measure_theory.measure.lebesgue
import analysis.calculus.monotone
import data.set.function
import analysis.bounded_variation
import tactic.swap_var

open_locale big_operators nnreal ennreal
open set measure_theory

variables {α β : Type*} [linear_order α] [linear_order β]
{E F : Type*} [pseudo_emetric_space E] [pseudo_emetric_space F]

def is_linearly_parameterized_on_by (f : ℝ → E) (s : set ℝ) (l : ℝ) :=
∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), evariation_on f (s ∩ Icc x y) = ennreal.of_real (l * (y - x))

-- Could do without `hl` but it means we have to check whether `s` is subsingleton
-- and if not deduce that `hl` necessarily holds…
lemma is_linearly_parameterized_on_by.iff_ordered (f : ℝ → E) (s : set ℝ) {l : ℝ} (hl : 0 ≤ l):
  is_linearly_parameterized_on_by f s l ↔
  ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), (x ≤ y) →
    evariation_on f (s ∩ Icc x y) = ennreal.of_real (l * (y - x)) :=
begin
  refine ⟨λ h x xs y ys xy, h xs ys, λ h x xs y ys, _⟩,
  rcases le_total x y with xy|yx,
  { exact h xs ys xy, },
  { rw [evariation_on.subsingleton, ennreal.of_real_of_nonpos],
    { exact mul_nonpos_of_nonneg_of_nonpos hl (sub_nonpos_of_le yx), },
    { rintro z ⟨zs,xz,zy⟩ w ⟨ws,xw,wy⟩,
      cases le_antisymm (zy.trans yx) xz,
      cases le_antisymm (wy.trans yx) xw,
      refl, }, },
end

def is_naturally_parameterized_on (f : ℝ → E) (s : set ℝ) := is_linearly_parameterized_on_by f s 1

lemma is_linearly_parameterized_on_by_zero_iff (f : ℝ → E) (s : set ℝ) :
  is_linearly_parameterized_on_by f s 0 ↔ ∀ x y ∈ s, edist (f x) (f y) = 0 :=
begin
  dsimp [is_linearly_parameterized_on_by],
  simp only [zero_mul, ennreal.of_real_zero, ←evariation_on.eq_zero_iff],
  split,
  { by_contra',
    obtain ⟨h,hfs⟩ := this,
    simp_rw evariation_on.eq_zero_iff at hfs h,
    push_neg at hfs,
    obtain ⟨x,xs,y,ys,hxy⟩ := hfs,
    rcases le_total x y with xy|yx,
    { exact hxy (h xs ys x ⟨xs,le_rfl,xy⟩ y ⟨ys,xy,le_rfl⟩), },
    { rw edist_comm at hxy,
      exact hxy (h ys xs y ⟨ys,le_rfl,yx⟩ x ⟨xs,yx,le_rfl⟩), }, },
  { rintro h x xs y ys,
    refine le_antisymm _ (zero_le'),
    rw ←h,
    exact evariation_on.mono f (inter_subset_left s (Icc x y)), },
end

lemma test {f : ℝ → E} {s t : set ℝ} {φ : ℝ → ℝ}
  (φm : monotone_on φ s) (φst : s.maps_to φ t) (φst' : s.surj_on φ t)
  {l l' : ℝ} (hl : 0 ≤ l) (hl' : 0 < l')
  (hf : is_linearly_parameterized_on_by (f ∘ φ) s l)
  (hfφ : is_linearly_parameterized_on_by f t l')
  ⦃x : ℝ⦄ (xs : x ∈ s) : s.eq_on φ (λ y, (l / l') * (y - x) + (φ x)) :=
begin
  rintro y ys,
  rw [←sub_eq_iff_eq_add, mul_comm, ←mul_div_assoc, eq_div_iff hl'.ne.symm],
  rcases le_total x y with h|h,
  work_on_goal 2
  { swap_var [x y, xs ↔ ys],
    have : (x - y) * l = - ((y - x) * l), by rw [←neg_mul, neg_sub], rw this,
    have : (φ x - φ y) * l' = - ((φ y - φ x) * l'), by rw [←neg_mul, neg_sub], rw this,
    simp only [neg_inj], },
  all_goals
  { rw ←ennreal.of_real_eq_of_real_iff (mul_nonneg (sub_nonneg_of_le (φm xs ys h)) hl'.le)
                                       (mul_nonneg (sub_nonneg_of_le h) hl),
    symmetry,
    calc ennreal.of_real ((y - x) * l)
       = ennreal.of_real (l * (y - x)) : by rw mul_comm
    ...= evariation_on (f ∘ φ) (s ∩ Icc x y) : (hf xs ys).symm
    ...= evariation_on f (t ∩ Icc (φ x) (φ y)) : by
    begin
      apply evariation_on.comp_eq_of_monotone_on,
      apply φm.mono (inter_subset_left _ _),
      { rintro u ⟨us,ux,uy⟩, exact ⟨φst us, φm xs us ux, φm us ys uy⟩, },
      { rintro v ⟨vt,vφx,vφy⟩,
        obtain ⟨u,us,rfl⟩ := φst' vt,
        rcases le_total x u with xu|ux,
        { rcases le_total u y with uy|yu,
          { exact ⟨u,⟨us,⟨xu,uy⟩⟩,rfl⟩, },
          { rw le_antisymm vφy (φm ys us yu),
            exact ⟨y,⟨ys,⟨h,le_rfl⟩⟩,rfl⟩, }, },
        { rw ←le_antisymm vφx (φm us xs ux),
            exact ⟨x,⟨xs,⟨le_rfl,h⟩⟩,rfl⟩, }, },
    end
    ...= ennreal.of_real (l' * (φ y - φ x)) : hfφ (φst xs) (φst ys)
    ...= ennreal.of_real ((φ y - φ x) * l') : by rw mul_comm, },
end
