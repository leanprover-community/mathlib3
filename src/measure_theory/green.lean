import measure_theory.prod
import analysis.normed_space.box_subadditive
import measure_theory.interval_integral
import logic.basic

noncomputable theory

open fin set function
open_locale big_operators
open_locale topological_space

section misc_lemmas

variables {E : Type*} [measurable_space E] [normed_group E] [borel_space E]
variables {μ : measure_theory.measure ℝ} [measure_theory.locally_finite_measure μ]
/-! Miscellaneous lemmas, find homes elsewhere. -/

/-- A continuous function is `interval_integrable`. -/
lemma continuous.interval_integrable {u : ℝ → E} (hu : continuous u) (a b : ℝ) :
  interval_integrable u μ a b :=
begin
  split;
  { refine measure_theory.integrable_on.mono_set _ Ioc_subset_Icc_self,
    exact hu.integrable_on_compact compact_Icc },
end

/-- A variable in `fin 2` is either `0` or `1`. -/
lemma split_fin2 (i : fin 2) : i = 0 ∨ i = 1 :=
begin
  refine or.imp _ _ (em (i.val ≤ 0)),
  all_goals
  { intros hi,
    ext },
  { have : 0 ≤ i.val := zero_le i.val,
    have : i.val = 0 := by linarith,
    exact this },
  { have : i.val < 2 := i.2,
    have : i.val = 1 := by linarith,
    exact this },
end

/-- A nonzero variable in `fin 2` is `1`. -/
lemma eq_one_of_ne_zero {i : fin 2} (hi : i ≠ 0) : i = 1 :=
(split_fin2 i).elim (λ h, false.rec (i = 1) (hi h)) id

/-- A non-one variable in `fin 2` is `0`. -/
lemma eq_zero_of_ne_one {i : fin 2} (hi : i ≠ 1) : i = 0 :=
(split_fin2 i).elim id (λ h, false.rec (i = 0) (hi h))

/-- In `fin 2`, if `i ≠ j` and `i ≠ k` then `j = k`. -/
lemma eq_of_both_neq {i j k : fin 2} (hj : j ≠ i) (hk : k ≠ i) : j = k :=
begin
  cases split_fin2 i,
  { rw h at hj hk,
    transitivity (1 : fin 2),
    { exact eq_one_of_ne_zero hj },
    { symmetry,
      exact eq_one_of_ne_zero hk } },
  { rw h at hj hk,
    transitivity (0 : fin 2),
    { exact eq_zero_of_ne_one hj },
    { symmetry,
      exact eq_zero_of_ne_one hk } }
end

def opp_c {i : fin 2} : subtype ({i} : set (fin 2))ᶜ :=
⟨ if i = 0 then (1 : fin 2) else (0 : fin 2),
  begin
    have : ¬ (1 : fin 2) = 0 := sorry,
    cases split_fin2 i,
    { rw h,
      exact this },
    { rw h,
      simp [this],
      exact ne.symm this },
  end ⟩

def fill (i : fin 2) (t : ℝ) (c : ℝ) : fin 2 → ℝ :=
λ j, if j = i then t else c

lemma continuous_fill (i : fin 2) (t : ℝ) : continuous (fill i t) :=
begin
  refine continuous_pi _,
  intros j,
  by_cases h : j = i,
  { simp [fill, h],
    exact continuous_const },
  { convert continuous_id,
    ext s,
    simp [fill, h] },
end

end misc_lemmas

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

lemma box_line_integral_const (cU : ℝ ) (i : fin 2) (a b : fin 2 → ℝ) :
  box_line_integral (λ x, cU ) i a b  = 0 :=
begin
  -- ALEX TO DO
  rw box_line_integral,
  rw segment_parametrized_integral,
  rw segment_parametrized_integral,
  have :
  ∫ (t : ℝ) in b i..a i, cU
  =
  -∫ (t : ℝ) in a i..b i, cU,
  apply interval_integral.integral_symm,
  rw this,
  simp,
end

def ex  (i : fin 2 ): (ℝ ):= if i = 0 then 1  else 0

def ey (i : fin 2 ): (ℝ ):= if i = 0 then 0  else 1

def oppI : fin 2 → fin 2 := λ i, if i=0 then 1 else 0

def oppE : fin 2 → (fin 2→ ℝ ) := λ i, if i=0 then ey else ex

def exy : fin 2 → (fin 2→ ℝ ) := λ i, if i=0 then ex else ey

lemma ne_oppI (i : fin 2) : oppI i ≠ i :=
begin
  cases split_fin2 i;
  { rw h,
    simp [oppI] }
end

lemma eq_oppI_oppI (i : fin 2) : oppI (oppI i) = i :=
eq_of_both_neq (ne_oppI _) (ne_oppI _).symm

lemma iZeroOne (i: fin 2) : i=0 ∨ i=1:=
begin
  exact split_fin2 i,
  --simp,
--  sorry,
end

def box_volume (a b : fin 2 → ℝ) := ∏ (i : fin 2), (b i - a i)

def box_volume' : (fin 2 → ℝ) × (fin 2 → ℝ) → ℝ := uncurry box_volume



theorem set_mem_iff_prop (p : ℝ → Prop) (a : ℝ ) :
a ∈ {x : ℝ  | p x} ↔ p a
:=
begin
  rw  set.mem_def,
  rw  set.set_of_app_iff,
end


lemma box_volume_eq (a b : fin 2 → ℝ) :
  box_volume a b = (b 0 - a 0)*(b 1 - a 1)
:=
begin
  rw box_volume,

  -- HOW TO GET ∏ to know there are two terms???
  sorry,
end

lemma box_line_integral_linear (u: (fin 2→ ℝ ) →L[ℝ] ℝ ) (i : fin 2) (a b : fin 2 → ℝ) :
  box_line_integral u i a b  = (box_volume a b) * (u (oppE i))  :=
begin
  rw box_volume_eq,
  rw box_line_integral,
  rw segment_parametrized_integral,
  rw segment_parametrized_integral,
  have : ∫ (t : ℝ) in b i..a i, u (update b i t) = - ∫ (t : ℝ) in a i..b i, u (update b i t),
  { apply interval_integral.integral_symm },
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
    have uLinear : ∀ i,
    (λ x, u (update a i x) - u (update b i x))
    =
    (λ x,     u (update a i x - (update b i x))),
    {
      intros,
      simp,
    },
    rw uLinear,

    have : (λ x,
    u (update a i x - update b i x))
    =
    (λ x ,
     (a (oppI i) - b (oppI i)) * u ( oppE i ))
    ,
    {
      rw funext_iff,
      intros x,
      simp,
      have uLinPwise : ∀ i,
      ( u (update a i x) - u (update b i x))
      =
      (     u (update a i x - (update b i x))),
      {
        intros,
        simp,
      },
      rw uLinPwise,
      --clear this,
      have : i=0∨ i=1,
      {
        exact iZeroOne i,
      },
      cases this,
      {
        rw this,
        rw oppI,
        rw oppE,

        simp,

        rw uLinPwise 0,

        have rw1 : (update a 0 x - update b 0 x)
        =
        (a 1 - b 1) • ey,
        {
          rw funext_iff,
          intros i,
          have : i=0∨ i=1,
          {
            exact iZeroOne i,
          },
          cases this,
          {
            rw this_1,
            simp,
            right,
            rw ey,
            simp,
          },
          {
            rw this_1,
            simp,
            rw ey,
            simp,
          },
        },
        simp [rw1],
      },
      {
        rw this,
        rw oppI,
        rw oppE,

        simp,
        rw uLinPwise,

        have rw1 : (update a 1 x - update b 1 x)
        =
        (a 0 - b 0) • ex,
        {
          rw funext_iff,
          intros i,
          have : i=0∨ i=1,
          {
            exact iZeroOne i,
          },
          cases this,
          {
            rw this_1,
            simp,
            rw ex,
            simp,
          },
          {
            rw this_1,
            simp,
            rw ex,
            simp,
          },
        },
        simp [rw1],
      },
      --- ALEX TO DO
    },
    rw this,
    clear this,
    --- ALEX
    rw interval_integral.integral_const,
    have : i=0∨ i=1,
    {
      exact iZeroOne i,
    },
    cases this,
    {
      rw this,
      rw oppI,

      ring,
      have rw1 : (ite (0 = 0) 1 0) = 1,
      {
        simp,
      },
      -- rw rw1,
      have rw2:  a (ite (0 = 0) 1 0) = a 1,
      {
        simp [rw1],
      },
--      rw rw2,
      have rw3:  b (ite (0 = 0) 1 0) = b 1,
      {
        simp [rw1],
      },
--      rw rw3,
      have rw4:  a (ite (0 = 0) 1 0) -  b (ite (0 = 0) 1 0) = a 1 - b 1,
      {
        simp [rw2, rw3],
      },
--      rw rw4,
      have rw5 :
      (b 0 - a 0) • ((a (ite (0 = 0) 1 0) - b (ite (0 = 0) 1 0)) * u (oppE 0))
      =
      (b 0 - a 0) • ((a 1 - b 1) * u (oppE 0)),
      {
        simp [rw4],
      },
--      rw rw5,
      have rw6 :
      (b 0 - a 0) • ((a (ite (0 = 0) 1 0) - b (ite (0 = 0) 1 0)) * u (oppE 0))
      =
      (b 0 - a 0) * (a 1 - b 1)  * u (oppE 0),
      {
        simp [rw5],
        rw mul_assoc,
--        ring,
      },
      simp at rw6,
      simp,

--    UH OH!!! SOMETHING'S BROKEN HERE; have a wrong sign (come back later...)

--      refine rw6,
      sorry,
      --rw rw2,
--      refl,
--      rw ite_eq_iff refl,  --ite_eq_left_iff,
--      simp,
  --    ring,
    },
    {
      rw this,
      rw oppI,
      ring,
      have rw1 : (ite (1 = 0) 1 0) = 0,
      {
        simp,
      },
      -- rw rw1,
      have rw2:  a (ite (1 = 0) 1 0) = a 0,
      {
        simp [rw1],
      },
--      rw rw2,
      have rw3:  b (ite (1 = 0) 1 0) = b 0,
      {
        simp [rw1],
      },
--      rw rw3,
      have rw4:  a (ite (1 = 0) 1 0) -  b (ite (1 = 0) 1 0) = a 0 - b 0,
      {
        simp [rw2, rw3],
      },
--      rw rw4,
      have rw5 :
      (b 1 - a 1) • ((a (ite (1 = 0) 1 0) - b (ite (1 = 0) 1 0)) * u (oppE 1))
      =
      (b 1 - a 1) • ((a 0 - b 0) * u (oppE 1)),
      {
        simp [rw4],
      },
--      rw rw5,
      have rw6 :
      (b 1 - a 1) • ((a (ite (1 = 0) 1 0) - b (ite (1 = 0) 1 0)) * u (oppE 1))
      =
      (b 0 - a 0) * (a 1 - b 1) * u (oppE 1),
      {
        simp [rw5],
        rw ←  mul_assoc,
        have :
        (b 1 - a 1) * (a 0 - b 0)
        =
        (b 0 - a 0) * (a 1 - b 1),
        {
          ring,
        },
        rw this,
        --ring,
      },

      sorry,
      -- SOMETHING IS WRONG HERE TOO!!! Sign error somewhere

--      refine rw6,

    },
  },
  --- HEATHER
  { apply continuous.interval_integrable,
    exact (continuous_linear_map.continuous u).comp continuous_update },
  { apply continuous.interval_integrable,
    exact (continuous_linear_map.continuous u).comp continuous_update },
end

lemma junk (x y :ℝ ) (f: ℝ → ℝ ): x=y→ f x =  f y:=
begin
  exact congr_arg (λ (x : ℝ), f x),
--  library_search,
end


include u
def opp_diff_feeder (i : fin 2) (a : ℝ) (x : ({i} : set (fin 2))ᶜ → ℝ)
  (y : ({i} : set (fin 2))ᶜ → ℝ) : ℝ :=
∫ t in (x opp_c)..(y opp_c), u (fill i a t)

/-- Put `box_line_integral` into a general framework of functions constructed from functions one
dimension down. -/
lemma eq_opp_diff (i : fin 2) :
  box_line_integral u (oppI i) = opp_diff (opp_diff_feeder u i) :=
begin
  ext x y,
  simp [opp_diff, opp_diff_feeder, box_line_integral, segment_parametrized_integral, fill],
  congr' 1,
  { congr,
    ext t,
    congr,
    ext j,
    split_ifs,
    { rw h,
      exact update_noteq (ne_oppI i).symm _ _ },
    rw eq_of_both_neq h (ne_oppI i),
    simp },
  { rw ← interval_integral.integral_symm,
    congr,
    ext t,
    congr,
    ext j,
    split_ifs,
    { rw h,
      exact update_noteq (ne_oppI i).symm _ _ },
    rw eq_of_both_neq h (ne_oppI i),
    simp }
end

lemma eq_opp_diff' (i : fin 2) :
  box_line_integral u i = opp_diff (opp_diff_feeder u (oppI i)) :=
begin
  rw ← eq_opp_diff u (oppI i),
  congr,
  rwa eq_oppI_oppI
end

variables {u}

open measure_theory

/-- The function `box_line_integral` is additive over rectangles. -/
lemma is_box_additive_line_integral (i : fin 2) (hu : continuous u) :
  box_additive_on (box_line_integral u i) univ :=
begin
  rw eq_opp_diff',
  apply box_additive_on_opp_diff,
  intros a I m hm j,
  simp only [opp_diff_feeder],
  let f : ℝ → ℝ := λ t, u (fill (oppI i) a t),
  have : ∀ {r s}, interval_integrable f volume r s,
  { exact (hu.comp (continuous_fill (oppI i) a)).interval_integrable },
  rw ← @interval_integral.integral_add_adjacent_intervals _ _ _ _ _ _ _ _ _ _ (I.left opp_c) _ (I.right opp_c) f _ _ _ _ this this,
  apply congr_arg2,
  { congr },
  { congr' 1,
    have : opp_c = j := subtype.ext (eq_of_both_neq opp_c.2 j.2),
    rw this,
    simp }
end


end

section prod_eq_pi

/-! Lemmas relating `fin 2 → ℝ` and `ℝ × ℝ`. -/


def foo'' {α : Type} : equiv ((fin 2) → α) (α × α) :=
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
foo''.to_linear_equiv (begin
  split,
  { intros x y,
    simp [foo''] },
  { intros c x,
    simp [foo''] }
  end)

end prod_eq_pi

section box_partition

def rectangle' {n : ℕ} (a b : fin n → ℝ) : set (fin n → ℝ) := λ x, ∀ i, x i ∈ Ioc (a i) (b i)

/-! A hyperplane divides a box in `fin n → ℝ` into smaller boxes. -/

lemma covers (n : ℕ)  (i : fin n)
  (p q a : fin n → ℝ) : p i ≤ a i → a i ≤ q i →
  rectangle' p q =
    rectangle' p (update q i (a i)) ∪
      rectangle' (update p i (a i)) q :=
begin
  intros piai qiai,
--  rw Ioc,
  ext,
--  simp,
  split,
  {
    -- in big rect implies in both little rect's
    intros h,
    -- rw Ioc at h,
    -- either x i < a i or a i <= x i
    by_cases ineq : x i ≤ a i,
    { -- case bottom half
      left,
      simp only [rectangle'],
      intros j,
      split,
      { exact (h j).1 },
      -- intros j,
      by_cases ji : j = i,
      { -- case j=i
        convert ineq,
        --rw update,
        convert dif_pos ji,
        simp,
      },
      { -- case j!= i
        convert (h j).2,
        convert dif_neg ji,
      },
    },
    { -- case top half
    --- ALEX
      right,
      simp only [rectangle'],
      intros j,
      split,
      {
        by_cases ji : j = i,
        {
          rw ji,
          simp,
          linarith,
        },
        {
          convert (h j).1,
          convert dif_neg ji,
        },
      },
      {
        convert (h j).2,
      },
    },
  },
  {
    -- in one of the little rect's implies in big rect
    intros h,
    intros j,
    rw Ioc,
    rw set_mem_iff_prop,

    rw rectangle' at h,
    rw rectangle' at h,
    by_cases ji : j = i,
    {
      rw ji,

      cases h,
      {
        -- we're in the bottom rectangle
        have hj := h j,
        rw Ioc at hj,
        rw ji at hj,
        rw set_mem_iff_prop at hj,
        split,
        linarith,
        have hj2 := hj.2,
        simp at hj2,
        linarith,
      },
      {
        -- we're in the top rectangle
        have hj := h j,
        rw Ioc at hj,
        rw ji at hj,
        rw set_mem_iff_prop at hj,
        rw update at hj,
        simp at hj,
        split,
        linarith,
        linarith,
      },
    },
    {
      cases h,
      {
        have hj := h j,
        rw update at hj,
        simp [ji] at hj,
        exact hj,
      },
      {
        have hj := h j,
        rw update at hj,
        simp [ji] at hj,
        exact hj,
      },

    },


  },
end

lemma is_disjoint (n : ℕ) (i : fin n)
  (p q a : fin n → ℝ) :
  disjoint (rectangle' p (update q i (a i)))
    (rectangle' (update p i (a i)) q) :=
begin

  rw disjoint,
  intros x h,
  simp,
  have xiLai : x i ≤  a i,
  {
    have h := h.1,
    simpa using (h i).2,
  },
--  have xiGai : a i <  x i,
--  {
  --have h211i := h.2.1.1 i,
  --simp at h211i,
  have h2 := h.2,
  have h1 := h.1,

  rw rectangle' at h1,
  rw  set.mem_def at h1,
  have h1i := h1 i,
  rw Ioc at h1i,
  rw set_mem_iff_prop at h1i,
  have h1i2 := h1i.2,
  rw update at h1i2,
  simp at h1i2,

  rw rectangle' at h2,
  rw  set.mem_def at h2,
  have h2i := h2 i,
  rw Ioc at h2i,
  rw set_mem_iff_prop at h2i,
  have h2i2 := h2i.1,
  rw update at h2i2,
  simp at h2i2,

  linarith,
end

end box_partition

section measure_stuff_foo

open measure_theory
variables (u : (fin 2 → ℝ) → ℝ)

def rectangle (a b : fin 2 → ℝ) : set (ℝ × ℝ) := (Ioc (a 0) (b 0)).prod (Ioc (a 1) (b 1))

lemma rectangle_eq (a b : fin 2 → ℝ) :
  (foo' ℝ ℝ).symm ⁻¹' (rectangle' a b) = rectangle a b :=
begin
  ext,
  split,
  { intros h,
    exact ⟨h 0, h 1⟩ },
  intros h i,
  cases split_fin2 i with hi hi,
  { simpa [hi] using h.1 },
  { simpa [hi] using h.2 }
end

lemma is_measurable_rectangle (a b : fin 2 → ℝ) : is_measurable (rectangle a b) :=
begin
  change is_measurable (set.prod _ _),
  rw is_measurable_prod,
  left,
  split;
  exact is_measurable_Ioc,
end

def box_integral (a b : fin 2 → ℝ) : ℝ :=
∫ x in rectangle a b, u ((foo' ℝ ℝ).symm x) ∂(volume.prod volume)

def box_integral' (P : (fin 2 → ℝ) → ℝ) (p : (fin 2 → ℝ) × (fin 2 → ℝ))
: ℝ := uncurry (box_integral P) p
--ERROR!!!

lemma box_integral_const (cU : ℝ)  (a b : fin 2 → ℝ) :
  box_integral (λ x, cU ) a b  = cU * box_volume a b :=
begin

  -- ALEX TO DO
  -- TRIED AND FAILED!!!

  rw box_integral,
  rw rectangle,

--  rw measure_theory.integral_prod ,

--  refine interval_integral.integral_const_of_cdf,


--  rw interval_integral.integral_const_of_cdf,
  sorry,
end

lemma box_integral_ineq ( P Q : (fin 2 → ℝ ) →  ℝ)  (a b : fin 2 → ℝ) :
  (∀ x, (foo'' x) ∈ (rectangle a b) → P x ≤  Q x) → box_integral P a b ≤   box_integral Q a b  :=
begin
  intros,
  -- ALEX TO DO
  --- ???? Abstract measure inequality??
  rw box_integral,
  rw box_integral,

--  rw interval_integral.integral_const_of_cdf,
  sorry,
end

-- need Tonelli over sets !
/-
def mid_point (a b : fin 2 → ℝ) := (a + b)/2

lemma box_integral_linear (u : (fin 2 → ℝ) →L[ℝ] ℝ)  (a b : fin 2 → ℝ) :
  box_integral u a b  = * u (mid_point a b)
  :=
begin
  -- ALEX TO DO
  rw box_integral,
  rw rectangle,

--  rw lintegral_prod,
--  rw interval_integral.integral_const_of_cdf,
  sorry,
end
-/

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
      -- THIS IS NOW BROKEN - SORRY! -- need to give pi≤ ai≤ qi ...
      --rw covers
      sorry,
      },
    rw this },
  { rw [← rectangle_eq, ← rectangle_eq],
    apply disjoint.preimage,
    apply is_disjoint },
  { exact is_measurable_rectangle _ _ },
  { exact is_measurable_rectangle _ _ },
  { exact hu.integrable_on },
  { exact hu.integrable_on }
end

end measure_stuff_foo

----------------------------------------------------------------

section Green

open measure_theory
variables (P Q : (fin 2 → ℝ) → ℝ)

--include hP


/-

∫_∂R P dx + Q dy

=

∫_R (P_y - Q_x ) dx dy

U=(P,Q)

-/

def divergence : (fin 2 → ℝ) → ℝ := (λ x, fderiv ℝ P x ey - fderiv ℝ Q x ex)

def div_diff (a b : fin 2 → ℝ) : ℝ :=
box_integral (divergence P Q) a b
-
(
box_line_integral P 0 a b
-
box_line_integral Q 1 a b
)

lemma const_div_diff_cancels (a b : fin 2 → ℝ) (cP cQ : ℝ) :
  div_diff (λ x, cP) (λ x, cQ) a b = 0 :=
begin
  rw div_diff,
  rw divergence,
  simp [box_line_integral_const],
  rw box_integral,
  simp,
end

lemma linear_divergence (P Q : (fin 2 → ℝ) →L[ℝ] ℝ) :
divergence P Q = (λ x, P ey - Q ex)
:=
begin
  rw divergence,
  ext,
  rw continuous_linear_map.fderiv,
  rw continuous_linear_map.fderiv,
end

lemma linear_div_diff_cancels (a b : fin 2 → ℝ) (P Q : (fin 2 → ℝ) →L[ℝ] ℝ) :
  div_diff P Q a b = 0 :=
begin
  rw div_diff,

  rw linear_divergence,
  rw box_integral_const,

  simp [box_line_integral_linear, oppE],
  simp,
  ring,
end

variables {P Q} (hP : differentiable ℝ P) (hQ : differentiable ℝ Q)
variables (hdiv : integrable ((divergence P Q) ∘ (foo' ℝ ℝ).symm) volume)


-- lemma added to mathlib after the beginning of our branch
lemma nhds_basis_Ioo' {α : Type*} [topological_space α] [linear_order α] [order_topology α]
  {a : α} (hl : ∃ (l : α), l < a) (hu : ∃ (u : α), a < u) :
  (𝓝 a).has_basis (λ (b : α × α), b.fst < a ∧ a < b.snd) (λ (b : α × α), set.Ioo b.fst b.snd) :=
sorry

-- lemma added to mathlib after the beginning of our branch
lemma nhds_basis_Ioo {α : Type*} [topological_space α] [linear_order α] [order_topology α]
  [no_top_order α] [no_bot_order α] {a : α} :
  (𝓝 a).has_basis (λ (b : α × α), b.fst < a ∧ a < b.snd) (λ (b : α × α), set.Ioo b.fst b.snd) :=
sorry



-- add lemma that the average over smaller and smaller boxes is the value at a point
lemma averaging (P : (fin 2 → ℝ) → ℝ) (pcont: continuous P) (b : fin 2 → ℝ) :
  asymptotics.is_o (box_integral' P - (λ p, (box_volume' p) * P b)) box_volume'
    (nhds_within (b, b) ((Iic b).prod (Ici b))) :=
begin
  rw asymptotics.is_o,
  intros c cpos,
  rw asymptotics.is_O_with,
  --rw continuous at pcont,
  --have := pcont.continuous_at ,
  have := @continuous.continuous_at _ _ _ _ _ b pcont,
  rw continuous_at at this,
  rw  filter.tendsto_iff_eventually at this,




  let NeighPb : set ℝ := Ioo (P(b)-c) (P(b) + c),
  have sIsNeigh : NeighPb ∈ 𝓝 (P b),
  {
    refine Ioo_mem_nhds _ _,
    linarith,
    linarith,
  },

  have thiss := this sIsNeigh,

  -- have := filter.eventually.curry thiss,

  -- rw filter.has_basis.eventually_iff  nhds_basis_Ioo at thiss,
  -- obtain ⟨x, ⟨hx₁, hx₂⟩, hx'⟩ := thiss,

  -- obtain ⟨a, b⟩ := thiss,

  have foofoo := eventually_nhds_within_of_eventually_nhds thiss,
  -- have foofoo := eventually_nhds_within_of_eventually_nhds thiss,

  have foo''' :
  ∀ᶠ (x : (fin 2 → ℝ) × (fin 2 → ℝ)) in 𝓝[(Iic b).prod (Ici b)] (b, b),
  ∀ (y ∈ rectangle x.1 x.2), P (foo''.symm y) ∈ NeighPb,
  { -- HEATHER
    rw filter.eventually_iff_exists_mem,
    refine ⟨(Ioc x.1 b).prod (Ico b x.2), _, _⟩,
    { apply nhds_within_prod,
      have := hx₁,
      -- apply Ioc_mem_nhds_within_Iic,
      -- library_search,
    },
    sorry,
  },

  refine foo'''.mp _,


  refine eventually_nhds_with_of_forall _ ,

  rintros ⟨ x1, x2⟩  ⟨ H1,  H2⟩  H3,

  simp at H3,

  simp,

  rw box_volume',

  rw box_integral',

  rw uncurry,

  simp,

  refine abs_le.2 _,

  have x11LeB : x1 1 ≤ b 1 ,
  {
    refine H1 _,
  },
  have x12LeB : x1 0 ≤ b 0 ,
  {
    refine H1 _,
  },
  have x21geB : b 1 ≤ x2 1 ,
  {
    refine H2 _,
  },
  have x22geB : b 0 ≤ x2 0 ,
  {
    refine H2 _,
  },
  have x2igex1i : ∀ (i : fin 2), x1 i ≤ x2 i,
  {
    intros,
    cases split_fin2 i,
    rw h,
    linarith,
    rw h,
    linarith,
  },

  have boxVolAbs :
  ∥box_volume x1 x2∥
    =   box_volume x1 x2,
    {
      rw box_volume,
      have prodGe0 : 0 ≤
      ∏ (i : fin 2), (x2 i - x1 i),
      {
        refine finset.prod_nonneg _,
        simp [x2igex1i],
      },
      refine  abs_of_nonneg prodGe0 ,

    },

  split,

  {
--    rw mul_comm,
--    rw ← box_integral_const,
--    rw box_integral,

    calc
    -(c * ∥box_volume x1 x2∥)
    =    -(c * box_volume x1 x2) : _
    ... = box_volume x1 x2 * P b
    - box_volume x1 x2 * c
     - box_volume x1 x2 * P b : _
    ... = box_integral (λ x,  P b - c ) x1 x2
     - box_volume x1 x2 * P b : _
    ... ≤ box_integral P x1 x2 - box_volume x1 x2 * P b : _,

    {
      simp,
      left,
      exact boxVolAbs,
    },
    {
      ring,
    },
    {
      rw box_integral_const,
      ring,
    },
    {
      simp,

      have ineq1 : ∀ x, (foo'' x ∈ rectangle x1 x2) →  P b - c ≤ P x,
      {
        intros x hx,
        have h3hx := le_of_lt (H3 (x 0) (x 1) hx).1,
        have xIs : ((foo''.symm) (x 0, x 1)) = x,
        {
          ext,
          cases split_fin2 x_1,
          rw h,
          rw foo'',
          simp,
          rw h,
          rw foo'',
          simp,
        },
        rw xIs at h3hx,
        exact h3hx,
      },


      refine box_integral_ineq ((λ (x : fin 2 → ℝ), P b - c)) P  x1 x2 ineq1,
    },
  },

  {
    calc
    box_integral P x1 x2 - box_volume x1 x2 * P b
    ≤
    box_integral (λ x,  P b + c ) x1 x2 - box_volume x1 x2 * P b  : _
    ... =
    box_volume x1 x2 * P b
    + box_volume x1 x2 * c
     - box_volume x1 x2 * P b : _
    ... =    (c * box_volume x1 x2) : _
    ... =
         c * ∥box_volume x1 x2∥ : _,

    {
      simp,

      have ineq1 : ∀ x, (foo'' x ∈ rectangle x1 x2) →  P x ≤  P b + c ,
      {
        intros x hx,
        have h3hx := le_of_lt (H3 (x 0) (x 1) hx).2,
        have xIs : ((foo''.symm) (x 0, x 1)) = x,
        {
          ext,
          cases split_fin2 x_1,
          rw h,
          rw foo'',
          simp,
          rw h,
          rw foo'',
          simp,
        },
        rw xIs at h3hx,
        exact h3hx,
      },

      refine box_integral_ineq P ((λ (x : fin 2 → ℝ), P b + c))  x1 x2 ineq1,
    },

    {
      rw box_integral_const,
      ring,
    },
    {
      ring,
    },
    {
      simp,
      left,
      rw  boxVolAbs,
    },

  },


  -- ????
  sorry,
end

include hP hQ hdiv

/-- The `div_diff` function (difference between the LHS and RHS of Green's theorem) is
`box_additive`. -/
lemma box_additive_div_diff : box_additive_on (div_diff P Q) univ :=
begin
  apply (is_box_additive_integral _ hdiv).sub,
  apply (is_box_additive_line_integral 0 hP.continuous).sub,
  exact is_box_additive_line_integral 1 hQ.continuous
end

open box_additive_on
open box_subadditive_on





-- add hypothesis of continuity of divergence
lemma greens_thm (I : subinterval (univ : set (fin 2 → ℝ ))) :
--box_integral (divergence P Q) a b
--box_line_integral  (i : fin 2) (a b : fin 2 → ℝ)
--∫ x in rectangle a b, u ((foo' ℝ ℝ).symm x) ∂(volume.prod volume)
  div_diff P Q I.left I.right = 0 :=
begin
  refine eq_zero_of_forall_is_o_prod _ _ _ ,
  { exact norm_subadditive_on (box_additive_div_diff hP hQ hdiv) },
  {
    intros,
--    rw asymptotics.is_o,
--    intros,
--
    have Pdiff := differentiable_at.has_fderiv_at (hP.differentiable_at ),

    have hpP := has_fderiv_at_iff_is_o_nhds_zero.1 Pdiff,

    extract_goal,

    /-

    b0 fixed , b near b0
      P(b) = P(b0) + P'(b0)(b-b0) +  o (b-b0)

need lemma: if f=o(m) then div_diff = o

    -/

    repeat {sorry},

  },

end


end Green

--- next steps: Lean definition of Divergence, prove additive by invoking these
-- prove that integral over perimeter - integral interior of divergence = o(volume)
