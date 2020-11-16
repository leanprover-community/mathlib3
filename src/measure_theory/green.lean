import measure_theory.prod
import analysis.normed_space.box_subadditive
import measure_theory.interval_integral

noncomputable theory

open fin set function
open_locale big_operators

section

/-- Given a point `x` in the plane, an index `i`, and a real number `a`, we introduce a definition
for the integral of a function along the segment obtained by varying the `i`-th coordinate of `x`
between its original variable and `a`. -/
def segment_parametrized_integral (f : (fin 2 → ℝ) → ℝ) (x : fin 2 → ℝ) (i : fin 2) (a : ℝ) : ℝ :=
∫ t in (x i)..a, f (update x i t)

variables {u : (fin 2 → ℝ) → ℝ} (hu : continuous u)

include hu

/-- Given a rectangle (defined by two points, the bottom-left corner `a` and the top-right corner
`b`), and a fixed continuous function `u` on the plane, and an index `i` in `fin 2`, the function
that sends a rectangle to the integral of `u` in opposite directions along the two sides parallel to
the `i`-axis. -/
def box_line_integral (i : fin 2) (a b : fin 2 → ℝ) : ℝ :=
(segment_parametrized_integral u a i (b i) - segment_parametrized_integral u b i (a i))

/-- The function `box_line_integral` is additive over rectangles. -/
lemma is_box_additive_line_integral (i : fin 2) : box_additive_on (box_line_integral hu i) univ :=
begin
  rw box_additive_on,
  intros,
  rw box_line_integral,
  rw box_line_integral,
  rw box_line_integral,
  rw segment_parametrized_integral,
  rw segment_parametrized_integral,
  rw segment_parametrized_integral,
  rw segment_parametrized_integral,
  rw segment_parametrized_integral,
  rw segment_parametrized_integral,

  sorry,
end
omit hu

end

section prod_eq_pi

/-! Lemmas relating `fin 2 → ℝ` and `ℝ × ℝ`. -/

lemma eq_one_of_ne_zero {i : fin 2} (hi : i ≠ 0) : i = 1 :=
begin
  suffices hi' : i.val = 1,
  { exact fin.eq_of_veq hi' },
  have : 1 ≤ i.val,
  { rw nat.succ_le_iff,
    apply nat.pos_of_ne_zero,
    exact fin.vne_of_ne hi },
  have : i.val ≤ 1 := nat.lt_succ_iff.mp i.2,
  linarith
end

def foo'' (α : Type) : equiv ((fin 2) → α) (α × α) :=
{ to_fun := λ f, ⟨f 0, f 1⟩,
  inv_fun := λ p i, if i = 0 then p.fst else p.snd,
  left_inv := begin
    intro f,
    ext i,
    simp only,
    split_ifs,
    { rw h },
    { rw eq_one_of_ne_zero h }
  end,
  right_inv := λ p, by { ext; simp } }

def foo' (𝕜 : Type) [ring 𝕜] (α : Type) [add_comm_group α] [module 𝕜 α] :
  linear_equiv 𝕜 ((fin 2) → α) (α × α) :=
(foo'' α).to_linear_equiv (begin
  split,
  { intros x y,
    simp [foo''] },
  { intros c x,
    simp [foo''] }
  end)

end prod_eq_pi

section box_partition

/-! A hyperplane divides a box in `fin n → ℝ` into smaller boxes. -/

lemma covers (n : ℕ) (s : set (fin n → ℝ)) ⦃I : s.subinterval⦄
  ⦃a : fin n → ℝ⦄ (i : fin n)
  (ha : a ∈ s) :
  Ioc I.left I.right =
    Ioc I.left (update I.right i (a i)) ∪
      Ioc (update I.left i (a i)) I.right :=
begin
  sorry
end

lemma is_disjoint (n : ℕ) (s : set (fin n → ℝ)) ⦃I : s.subinterval⦄
  ⦃a : fin n → ℝ⦄ (i : fin n)
  (ha : a ∈ s) :
  disjoint (Ioc I.left (update I.right i (a i)))
    (Ioc (update I.left i (a i)) I.right) :=
begin
  sorry
end

end box_partition

open measure_theory
variables (u : (fin 2 → ℝ) → ℝ)

def rectangle (a b : fin 2 → ℝ) : set (ℝ × ℝ) := (Ioc (a 0) (b 0)).prod (Ioc (a 1) (b 1))

lemma rectangle_eq (a b : fin 2 → ℝ)  :
  (foo' ℝ ℝ).symm ⁻¹' (Ioc a b) = rectangle a b :=
begin
  sorry
end

lemma is_measurable_rectangle (a b : fin 2 → ℝ) : is_measurable (rectangle a b) :=
begin
  change is_measurable (set.prod _ _),
  rw is_measurable_prod,
  left,
  split;
  exact is_measurable_Ioc,
end

lemma integrable_restrict (v : ℝ × ℝ → ℝ) (a b : fin 2 → ℝ)
  ⦃m : ℝ⦄ (i : fin 2)
  (hu : integrable v volume) :
  integrable_on v (rectangle a (update b i m)) volume :=
begin
  sorry
end

lemma integrable_restrict' (v : ℝ × ℝ → ℝ) (a b : fin 2 → ℝ)
  ⦃m : ℝ⦄ (i : fin 2)
  (hu : integrable v volume) :
  integrable_on v (rectangle (update a i m) b) volume :=
begin
  sorry
end

def box_integral (a b : fin 2 → ℝ) : ℝ :=
∫ x in rectangle a b, u ((foo' ℝ ℝ).symm x) ∂(volume.prod volume)

lemma is_box_additive_integral (hu : integrable (u ∘ (foo' ℝ ℝ).symm)) :
  box_additive_on (box_integral u) univ :=
begin
  intros I a ha i,
  symmetry,
  unfold box_integral,
  rw ← integral_union,
  { have : rectangle I.left I.right =
         (rectangle I.left (update I.right i (a i)) ∪
            rectangle (update I.left i (a i)) I.right),
    { rw [← rectangle_eq, ← rectangle_eq, ← rectangle_eq],
      rw ← preimage_union,
      congr,
      apply covers 2 univ,
      simp },
    rw this },
  { rw [← rectangle_eq, ← rectangle_eq],
    apply disjoint.preimage,
    apply is_disjoint,
    simp },
  { exact is_measurable_rectangle _ _ },
  { exact is_measurable_rectangle _ _ },
  { exact integrable_restrict _ _ _ _ hu },
  { exact integrable_restrict' _ _ _ _ hu }
end
