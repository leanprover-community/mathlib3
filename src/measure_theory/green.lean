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

variables (u : (fin 2 → ℝ) → ℝ)

/-- Given a rectangle (defined by two points, the bottom-left corner `a` and the top-right corner
`b`), and a fixed continuous function `u` on the plane, and an index `i` in `fin 2`, the function
that sends a rectangle to the integral of `u` in opposite directions along the two sides parallel to
the `i`-axis. -/
def box_line_integral  (i : fin 2) (a b : fin 2 → ℝ) : ℝ :=
(segment_parametrized_integral u a i (b i) + segment_parametrized_integral u b i (a i))
---- IS THIS DEF CORRECT???? OR OFF BY A SIGN??


lemma box_line_integral_const (cU : ℝ ) (i : fin 2) (a b : fin 2 → ℝ)
:
 box_line_integral (λ x, cU ) i a b  = 0
 :=
begin
  -- ALEX TO DO
  sorry,
end

def ex  (i : fin 2 ): (ℝ ):= if i = 0 then 1  else 0

def ey (i : fin 2 ): (ℝ ):= if i = 0 then 0  else 1

def oppI : fin 2 → fin 2 := λ i, if i=0 then 1 else 0

def oppE : fin 2 → (fin 2→ ℝ ) := λ i, if i=0 then ey else ex

lemma box_line_integral_linear (u: (fin 2→ ℝ ) →L[ℝ] ℝ ) (i : fin 2) (a b : fin 2 → ℝ)
:
 box_line_integral u i a b  = (b 0 - a 0)*(u (oppE i))*(b 1 - a 1)
 :=
begin
  rw box_line_integral,
  rw segment_parametrized_integral,
  rw segment_parametrized_integral,
  have :
  ∫ (t : ℝ) in b 0..a 0, u (update b 0 t)
  =
   - ∫ (t : ℝ) in a 0..b 0, u (update b 0 t),
  apply   interval_integral.integral_symm,
  rw this,
  ring,
  clear this,
  rw ←  interval_integral.integral_sub,
  {
    /-
    have : ∀ x,
    u (update a 0 x) - u (update b 0 x)
    =
    u (update a 0 x - (update b 0 x)),
    {
      simp,
    },
    -/
    have :
    (λ x, u (update a 0 x) - u (update b 0 x))
    =
    (λ x,     u (update a 0 x - (update b 0 x))),
    {
      simp,
    },
    rw this,
    clear this,
    have : (λ x,
    u (update a 0 x - update b 0 x))
    =
    (λ x ,
     (a 1 - b 1) * u ( ey ))
    ,
    {
      --- ALEX TO DO
      sorry,
    },
    rw this,
    clear this,
    --- ALEX
    sorry,
  },


  --- HEATHER

  sorry,

  sorry,
end

lemma box_integral_const (cU : ℝ )  (a b : fin 2 → ℝ)
:
 box_integral (λ x, cU ) a b  = 0
 :=
begin
  -- ALEX TO DO
  sorry,
end


variables {u}

/-- The function `box_line_integral` is additive over rectangles. -/
lemma is_box_additive_line_integral (i : fin 2) (hu : continuous u)
: box_additive_on (box_line_integral u i) univ :=
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
--  rw Ioc,
  ext,
--  simp,
  split,
  {
    intros h,
    rw Ioc at h,
    -- either x i < a i or a i <= x i
    by_cases ineq : x i <= a i,
    { -- case bottom half
      left,
      split,
      exact h.1,
      intros j,
      by_cases ji : j = i,
      { -- case j=i
        convert ineq,
        --rw update,
        convert dif_pos ji,
        simp,
      },
      { -- case j!= i
        convert h.2 j,
        convert dif_neg ji,
      },
    },
    { -- case top half
    --- ALEX
      sorry,
    },
  },
  {
    intros h,
    cases h,
    {
    --- ALEX
      sorry,
    },
    {
    --- ALEX
      sorry,
    },
  },
end

lemma is_disjoint (n : ℕ) (s : set (fin n → ℝ)) ⦃I : s.subinterval⦄
  ⦃a : fin n → ℝ⦄ (i : fin n)
  --(ha : a ∈ s) :
  (ha : I.left i < a i ∧ a i ≤ I.right i) :
  disjoint (Ioc I.left (update I.right i (a i)))
    (Ioc (update I.left i (a i)) I.right) :=
begin
  rw disjoint,
  intros x h,
  simp,
  have xiLai : x i ≤  a i,
  {
    convert h.1.2 i,
    simp,
  },
--  have xiGai : a i <  x i,
--  {
  --have h211i := h.2.1.1 i,
  --simp at h211i,
  have h2 := h.2,
  have h22 := h.2.2,
  have h21 := h.2.1,

  have h212 := h.2.1.2,
  have h211 := h.2.1.1,
  have claim : ∀ (i_1 : fin n), x i_1 ≤ update I.left i (a i) i_1 ,
  {
    intros j,
    rw update,
    split_ifs,
    simp [h_1,xiLai],
    have h1 := h.1.2 j,
    convert h1,
    simp [h_1],
--    refine h.2.1,
--ALEX
    --by_cases ji : j= i,

    sorry,
  },
  exact h212 claim,
--    have h212i := h212 i,
    --convert h.2.1.2 i,
    --simp,
   sorry,
--  },


end

end box_partition

section measure_stuff_foo

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
    --simp
    sorry,
    },
  { exact is_measurable_rectangle _ _ },
  { exact is_measurable_rectangle _ _ },
  { exact integrable_restrict _ _ _ _ hu },
  { exact integrable_restrict' _ _ _ _ hu }
end

end measure_stuff_foo

----------------------------------------------------------------

section Green

open measure_theory
variables (P Q  : (fin 2 → ℝ) →  ℝ) (hP : continuous P) (hQ : continuous Q)

--include hP


/-

∫_∂R P dx + Q dy

=

∫_R (P_y - Q_x ) dx dy

U=(P,Q)

-/

def ex  (i : fin 2 ): (ℝ ):= if i = 0 then 1  else 0

def ey (i : fin 2 ): (ℝ ):= if i = 0 then 0  else 1

def divergence : (fin 2 → ℝ ) → ℝ := fderiv ℝ P ex - fderiv ℝ Q ey

def div_diff (a b : fin 2 → ℝ ) : ℝ :=
box_integral (divergence P Q) a b
-
(
box_line_integral P 0 a b
+
box_line_integral Q 1 a b
)

lemma const_div_diff_cancels (a b : fin 2 → ℝ ) (cP cQ :ℝ )
:
div_diff (λ x, cP ) (λ x, cQ ) a b =0
:=
begin
  rw div_diff,

end

lemma linear_div_diff_cancels (a b : fin 2 → ℝ ) (P: (fin 2→ℝ ) →L[ℝ] (ℝ ) ) (Q: (fin 2→ℝ ) →L[ℝ] ℝ  )
:
div_diff P Q a b =0
:=
begin
  sorry,
end

open box_subadditive_on

lemma greens_thm
(I : subinterval (univ : set (fin 2 → ℝ )))
(hP : differentiable ℝ  P)
(hQ : differentiable ℝ  Q)
:
div_diff P Q I.left I.right = 0
--box_integral (divergence P Q) a b
--box_line_integral  (i : fin 2) (a b : fin 2 → ℝ)
--∫ x in rectangle a b, u ((foo' ℝ ℝ).symm x) ∂(volume.prod volume)
:=
begin
  refine eq_zero_of_forall_is_o_prod _ _ _ ,
  {

    sorry,
  },
  {
    intros,
--    rw asymptotics.is_o,
--    intros,
--
    have Pdiff := differentiable_at.has_fderiv_at (hP.differentiable_at ),

    have hpP := has_fderiv_at_iff_is_o_nhds_zero.1 Pdiff,


    /-

    b0 fixed , b near b0
      P(b) = P(b0) + P'(b0)(b-b0) +  o (b-b0)

need lemma: if f=o(m) then div_diff = o

    -/

    sorry,

  },

end


end Green

--- next steps: Lean definition of Divergence, prove additive by invoking these
-- prove that integral over perimeter - integral interior of divergence = o(volume)
