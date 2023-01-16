import measure_theory.measure.lebesgue
import analysis.calculus.monotone
import data.set.function
import analysis.bounded_variation

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
    { apply hxy,
      apply h xs ys x ⟨xs,le_rfl,xy⟩ y ⟨ys,xy,le_rfl⟩, },
    { apply hxy, rw edist_comm,
      apply h ys xs y ⟨ys,le_rfl,yx⟩ x ⟨xs,yx,le_rfl⟩, }, },
  { rintro h x xs y ys,
    refine le_antisymm _ (zero_le'),
    rw ←h,
    exact evariation_on.mono f (inter_subset_left s (Icc x y)), },
end

lemma test {f : ℝ → E} {s t : set ℝ} {φ : ℝ → ℝ}
  (φm : monotone_on φ s) (φst : s.maps_to φ t) (φst' : s.surj_on φ t) {l l' : ℝ}
  (hf : is_linearly_parameterized_on_by (f ∘ φ) s l) (hfφ : is_linearly_parameterized_on_by f t l')
  ⦃x : ℝ⦄ (xs : x ∈ s) : s.eq_on φ (λ y, (l / l') * (y - x) + (φ x)) :=
begin
  rintro y ys,
end
