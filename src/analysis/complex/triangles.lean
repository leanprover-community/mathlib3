import analysis.complex.basic
import data.zmod.basic
import measure_theory.interval_integral
import analysis.convex.products

noncomputable theory

open_locale classical
open_locale nnreal
open_locale big_operators
open_locale topological_space
open set function finset
open complex

/-- A triangle is a function from `ℤ/3ℤ` to `ℂ` (this definition allows for the description of
adjacent vertices as `i` and `i + 1`, cyclically). -/
def triangle := zmod 3 → ℂ

/-- Given a function `f : ℂ → ℂ`, the contour integral of `f` along the segment from `a` to `b` is
defined to be the (real) integral from `0` to `1` of the function
`λ t, f ((1 - t) * a + t * b) * (b - a)`. -/
def contour_integral_segment (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
∫ (t : ℝ) in 0..1, f ((1 - t) * a + t * b) * (b - a)

/-- The contour integral of a constant `c` along the segment from `a` to `b` is `c * (b - a)`. -/
lemma contour_integral_segment.integral_const (c : ℂ) (a b : ℂ) :
  contour_integral_segment (λ z, c) a b = c * (b - a) :=
by --show_term {
  simp [contour_integral_segment, interval_integral.integral_const] --}

/-- Given a function `f : ℂ → ℂ`, the contour integral of `f` around a triangle is defined to be the
sum of the contour integrals along the three segments forming its sides. -/
def contour_integral (f : ℂ → ℂ) (T : triangle) : ℂ :=
∑ i, contour_integral_segment f (T i) (T (i + 1))

/-- The contour integral of a constant `c` around a triangle is `0`. -/
lemma contour_integral.integral_const (c : ℂ) (T : triangle) : contour_integral (λ z, c) T = 0 :=
begin
  rw contour_integral,
  --rw contour_integral_segment.integral_const,
  simp only [contour_integral, contour_integral_segment.integral_const],
  calc ∑ i, c * (T (i + 1) - T i)
      =  ∑ i, (c * T (i + 1) - c * T i) : _ -- by { congr, ext; ring }
  ... = c * (∑ i, T (i + 1)) - c * (∑ i, T i) : _ -- by simp [mul_sum]
  ... = 0 : _,

  {
    congr,
    ext i,
    ring,
    ring,
  },

  {
    --squeeze_simp [mul_sum],
    simp [mul_sum],
  },


  rw sub_eq_zero,
  congr' 1,




  exact (equiv.add_left (1 : zmod 3)).sum_comp _

end



/-- The function partitioning a triangle into four smaller triangles, parametrized by `ℤ/3ℤ` (one
for each of the three corner triangles) and `none` (for the centre triangle). -/
def quadrisect (T : triangle) : option (zmod 3) → triangle
| none := λ j, ((∑ i, T i) - T j) / 2
| (some i) := λ j, (T i + T j) / 2

/-- Given a function `f : ℂ → ℂ`, the contour integral of `f` around a triangle equal to the sum of
the contour integrals of `f` around each triangle in its quadrisection. -/
lemma foo (f : ℂ → ℂ ) (T : triangle ) :
  contour_integral f T = ∑ i, contour_integral f (quadrisect T i)
  :=
begin
  simp [contour_integral],
  rw sum_comm,
  congr,
  ext1 j,
  let F : Π (a b : ℂ), ℂ := contour_integral_segment f,
  have h : ∀ (a b : ℂ), F a b = F a ((a + b) / 2) + F ((a + b) / 2) b,
  { intros a b,
    simp [F, contour_integral_segment],
    sorry, -- need change of variable
    },
  apply symm,
  calc ∑ x, contour_integral_segment f (quadrisect T x j) (quadrisect T x (j+1)) =
        F (quadrisect T none     j) (quadrisect T none     (j+1)) +
        (F (quadrisect T (some 0) j) (quadrisect T (some 0) (j+1)) +
        (F (quadrisect T (some 1) j) (quadrisect T (some 1) (j+1)) +
        (F (quadrisect T (some 2) j) (quadrisect T (some 2) (j+1)) + 0)))
    : rfl
  ... = F (quadrisect T none     j) (quadrisect T none     (j+1)) +
        F (quadrisect T (some 0) j) (quadrisect T (some 0) (j+1)) +
        F (quadrisect T (some 1) j) (quadrisect T (some 1) (j+1)) +
        F (quadrisect T (some 2) j) (quadrisect T (some 2) (j+1))
    : by simp [add_assoc]
  ... = F (((∑ i, T i) - T j) / 2)  (((∑ i, T i) - T (j+1)) / 2) +
        F ((T 0 + T j) / 2)         ((T 0 + T (j+1)) / 2) +
        F ((T 1 + T j) / 2)         ((T 1 + T (j+1)) / 2) +
        F ((T 2 + T j) / 2)         ((T 2 + T (j+1)) / 2)
    : rfl
  ... = F (((T 0 + (T 1 + (T 2 + 0))) - T j) / 2)  (((T 0 + (T 1 + (T 2 + 0))) - T (j+1)) / 2) +
        F ((T 0 + T j) / 2)         ((T 0 + T (j+1)) / 2) +
        F ((T 1 + T j) / 2)         ((T 1 + T (j+1)) / 2) +
        F ((T 2 + T j) / 2)         ((T 2 + T (j+1)) / 2)
    : rfl
  ... = F ((T 0 + T 1 + T 2 - T j) / 2)  ((T 0 + T 1 + T 2 - T (j+1)) / 2) +
        F ((T 0 + T j) / 2)         ((T 0 + T (j+1)) / 2) +
        F ((T 1 + T j) / 2)         ((T 1 + T (j+1)) / 2) +
        F ((T 2 + T j) / 2)         ((T 2 + T (j+1)) / 2)
    : by simp [add_assoc]
  ... = (∫ (t : ℝ) in 0..1, f ((1 - t) * ((T 0 + T 1 + T 2 - T j) / 2) + t * ((T 0 + T 1 + T 2 - T (j+1)) / 2)) * (((T 0 + T 1 + T 2 - T (j+1)) / 2) - ((T 0 + T 1 + T 2 - T j) / 2))) +
        (∫ (t : ℝ) in 0..1, f ((1 - t) * ((T 0 + T j) / 2) + t * ((T 0 + T (j+1)) / 2)) * (((T 0 + T (j+1)) / 2) - ((T 0 + T j) / 2))) +
        (∫ (t : ℝ) in 0..1, f ((1 - t) * ((T 1 + T j) / 2) + t * ((T 1 + T (j+1)) / 2)) * (((T 1 + T (j+1)) / 2) - ((T 1 + T j) / 2))) +
        (∫ (t : ℝ) in 0..1, f ((1 - t) * ((T 2 + T j) / 2) + t * ((T 2 + T (j+1)) / 2)) * (((T 2 + T (j+1)) / 2) - ((T 2 + T j) / 2)))
    : by simp [F, contour_integral_segment]
  ... = _ : sorry,
end

/-
lemma max_lemma (S : finset ℝ≥0 ) :
  S.sum ≤  S.cardinality * (Sup S) :=
begin
end

lemma max_lemma (S : finset ℝ) (hS: nonempty S) :
  (∑ s in S, s ) ≤ S.card * (S.max' hS) :=
begin
  sorry,
end

-/


/-
example {α : Type*} (S: fintype α) (f : α → ℕ) (g : α → ℕ) (h : ∀ a, f a ≤ g a) :
  ∑ (a : S), f a ≤ ∑ (a : S), g a :=
  begin
    exact  sum_le_sum (λ x _ , h x),
  end
-/

/-- The integral of a function over a triangle is bounded by the maximal of the four subdivided triangles
-/
lemma foo2 (f : ℂ → ℂ ) (T : triangle ) :
  abs (contour_integral f T) ≤
--  4 * Sup (set.range (λ i, abs ( contour_integral f (quadrisect T i)))) :=
  4 * supr ( (λ i, abs ( contour_integral f (quadrisect T i)))) :=
begin
  /- AK? -/
  rw foo,

  calc
 abs (∑ (i : option (zmod 3)), contour_integral f (quadrisect T i))
 ≤  ∑ (i : option (zmod 3)), abs( contour_integral f (quadrisect T i)) : _
 ... ≤ ∑ (i : option (zmod 3)),   supr ( (λ i, abs ( contour_integral f (quadrisect T i)))) : _
... = 4 * supr ( (λ i, abs ( contour_integral f (quadrisect T i)))) : _ ,


{
  let func : (option (zmod 3)) → ℂ   :=  λ i , contour_integral f (quadrisect T i),
  refine norm_sum_le _ func ,
},

{
  let funcabs  : (option (zmod 3)) → ℝ    :=  λ i , abs ( contour_integral f (quadrisect T i)),
  refine sum_le_sum _ ,
  intros,
  refine le_cSup _ _ ,
  {
  -- ASK ON ZULIP

  --    have : range (λ (i : option (zmod 3)), abs (contour_integral f (quadrisect T i)))
      --refine bdd_above _ ,
      sorry,
    },
    {
      use x,
    },
  --  congr,
  },

  {
    rw sum_const,
    simp,
    left,
    norm_cast,
  },
end


/--  ∫_γ  c = c (b-a)
-/
lemma foo3b (c: ℂ ) (a b :ℂ ) :
  contour_integral_segment (λ x, c) a b =
  c*(b-a) :=
begin
  rw contour_integral_segment,
  rw interval_integral.integral_const,
  simp,
end

def int_t := ∫ (t : ℝ) in 0..1, (t:ℂ )

#check interval_integral.integral_smul

lemma integral_smul_C  (c : ℂ) :
∫ (t : ℝ) in 0..1,  ((t:ℂ ) * c)
=
(∫ (t : ℝ) in 0..1, (t:ℂ )) * c
:=
begin

  --library_search,
  sorry,
end

lemma foo3bX (c: ℂ ) (a b :ℂ ) :
  contour_integral_segment (λ x, x) a b =
  int_t * (b-a)^2
  + a*(b-a)
   :=
begin
  rw contour_integral_segment,

  calc
  ∫ (t : ℝ) in 0..1, ((1 - ↑t) * a + ↑t * b) * (b - a)
  =  ∫ (t : ℝ) in 0..1, (a* (b - a)  + ↑t * ((b-a) * (b - a))) : _
  ... = (∫ (t : ℝ) in 0..1, (a* (b - a))) + ∫ (t : ℝ) in 0..1, (↑t * ((b-a) * (b - a))) : _
  ... =  (a* (b - a)) + ∫ (t : ℝ) in 0..1, (↑t * ((b-a) * (b - a))) : _
  ... = int_t * (b-a)^2 + a*(b-a) : _,

  {
    congr,
    rw funext_iff,
    intros,
    ring,
  },

  {
    refine  interval_integral.integral_add _ _ ,
    {

      have rw1 :
      measure_theory.integrable_on (λ (t : ℝ), a * (b - a)) (Icc 0 1) measure_theory.measure_space.volume
      ,
      {
        refine continuous.integrable_on_compact _ _,
        exact compact_Icc,
        exact continuous_const,
      },

      rw interval_integrable,
      split,

      {
        refine rw1.mono_set _ ,
        exact Ioc_subset_Icc_self,
      },

      have rw2: Ioc (1:ℝ) 0 = ∅ ,
      {
        have : (0:ℝ ) ≤ 1 := by linarith,
        exact Ioc_eq_empty this,
      },
      rw rw2,

      -- HM COMPLAIN ON ZULIP PLEASE *****
      simp,
--      refine measure_theory.integrable_on_empty _ ,
--      exact measurable_const,
    },
    {

      have rw3:=  complex.continuous_of_real.mul continuous_const,

    have rw1 :
      measure_theory.integrable_on (λ (t : ℝ), ↑t * ((b - a) * (b - a))) (Icc 0 1) measure_theory.measure_space.volume
      ,
      {
        refine continuous.integrable_on_compact _ _,
        exact compact_Icc,

      exact rw3,
        --refine continuous.mul  _ _ ,
        --exact complex.continuous_of_real.mul continuous_const,
--        refine complex.continuous_of_real ,
        --exact continuous_const,
      },

      rw interval_integrable,
      split,

      {
        refine rw1.mono_set _ ,
        exact Ioc_subset_Icc_self,
      },

      have rw2: Ioc (1:ℝ) 0 = ∅ ,
      {
        have : (0:ℝ ) ≤ 1 := by linarith,
        exact Ioc_eq_empty this,
      },
      rw rw2,
      refine measure_theory.integrable_on_empty _ ,
      refine continuous.measurable _,
      --refine continuous.mul  _ _ ,
      exact rw3,
    }
    },
  {
    rw interval_integral.integral_const,
    simp,
  },
  {
    rw (_ :
    ∫ (t : ℝ) in 0..1, ↑t * ((b - a) * (b - a))
    =
    (∫ (t : ℝ) in 0..1, ↑t) * ((b - a) * (b - a))),

    {
      rw int_t,
      ring,
    },

    {
      refine  integral_smul_C ((b - a) * (b - a)),
    },

  },

end


/-
lemma rw1 (f g : ℂ  → ℂ  ) :
( f = g ) ↔ (∀  x, f x = g x) :=
begin
  by library_search, -- funext_iff
end

lemma rw1 ( f g :ℂ → ℂ ) (S : finset ℂ  ) :
∑ s in S, (f s + g s)
=
∑ s in S, (f s )+
∑ s in S, ( g s)
:=
begin
  by library_search, --exact sum_add_distrib
end


lemma rw1 ( c :ℂ ) (f g :ℂ → ℂ ) :
f=g → ∀ x, c*(f x) = c*(g x ) :=
begin

  intros,

    by library_search,
    --exact congr_arg (has_mul.mul c) (congr_fun a x)
end

-/


/--  ∫_T c = 0
-/
lemma foo3bT (c: ℂ ) (T: triangle ) :
  contour_integral (λ x, c) T = 0 :=
begin
  /- AK -/
  rw contour_integral,

  calc
  ∑ (i : zmod 3), contour_integral_segment (λ (x : ℂ), c) (T i) (T (i + 1))
  =
  ∑ (i : zmod 3), c * (T (i+1) - (T i)) : _
  ... = 0 : _,

  congr,
  rw funext_iff,
  intros,
  rw foo3b,

  rw (_ :
  ∑ (i : zmod 3), c * (T (i + 1) - T i)
  =
  ∑ (i : zmod 3), c * (T (i + 1))
  - ∑ (i : zmod 3), c * ( T i)),

  rw (_ :
  ∑ (i : zmod 3), c * (T (i + 1))
  =
  ∑ (i : zmod 3), c * (T (i ))),

  ring,

  {
    rw (_ : ∑ (i : zmod 3), c * T (i + 1) =
     c * ∑ (i : zmod 3), T (i + 1) ),

    rw (_ : ∑ (i : zmod 3), c * T (i ) =
     c * ∑ (i : zmod 3), T (i ) ),

    refine congr_arg (has_mul.mul c) _, --exact congr_arg (has_mul.mul c) (congr_fun a x)

    exact (equiv.add_left (1 : zmod 3)).sum_comp _,

    rw ← mul_sum,
    rw ← mul_sum,
  },

  {
    rw ←  sum_sub_distrib,
    ring,
  },


/-
  let integs:  ℂ  := contour_integral_segment (λ (x : ℂ), c) (T 1) (T (1 + 1)),
  let integs1: ℂ :=
    ∫ (t : ℝ) in 0..1, (c * ((T(1+1)) - (T 1))),
  have : ∀ i, contour_integral_segment (λ (x : ℂ), c) (T i) (T (i + 1))
  =
  ∫ (t : ℝ) in 0..1, (c * ((T(i+1)) - (T i)))
  ,
  {
    intros,
    refl,
  },
  rw this,

  --rw (_ : te
  --= ∑ (i : zmod 3), contour_integral_segment (λ (x : ℂ), c) (T i) (T (i + 1))),
-/
end

lemma foo3bTX (c d: ℂ ) (T: triangle ) :
  contour_integral (λ x, c*x +d ) T = 0 :=
begin
  /- Alex  -/
  sorry,
end



def triangle_hull (T: triangle): set ℂ  := convex_hull (set.range T )


def sup_side_length : triangle → ℝ :=
--- HM
sorry
--supr (λ p, dist p.1 p.2 )

lemma foo7 (T:triangle ) (j : option (zmod 3)) :
  sup_side_length (quadrisect T j) =
  sup_side_length T / 2 :=
begin
  /- AK -/

  sorry,
end


/- NEXT TIME -/

theorem Goursat (f : ℂ →  ℂ ) (holc: differentiable ℂ f) (T₀ : triangle ) :
  contour_integral f T₀  = 0 :=
begin

  have : ∀ n , ∀ (T' :triangle ) , ∃ (T'' : triangle), ∃ j : option (zmod 3) ,
    T'' = quadrisect T' j ∧
    abs ( contour_integral f T') ≤ 4^n * abs (contour_integral f T''),
    {
      sorry,
    },
  choose! T   i h h' using this,
   --H using this,

  let X : ℕ → (triangle × ( option (zmod 3))) := λ n, nat.rec_on n ⟨T₀ ,none⟩
   (λ n p, ⟨ T n p.1, i n p.1⟩ ),
    --(λ n T, (T_seq n T) (H n T)),

  let T_seq : ℕ → triangle := λ n, (X n).1,
  let i_seq : ℕ → option (zmod 3) := λ n, (X n).2,

  have diameter : ∀ n m, ∀ i j,
    dist (T_seq n i) (T_seq m j) ≤ max_side_length T₀ / 2^(min n m),
    {

      sorry,
    },

  obtain ⟨ z, hz⟩  : ∃ z , filter.tendsto (λ n, T_seq n 0) filter.at_top (𝓝 z),
  {
    sorry,
  },


  have lim_pt : ∃ z:ℂ , ∀ n, z ∈ triangle_hull (T_seq n),
  {
    use z,
    intros,
    sorry,
  },

  have localize := (holc z).has_deriv_at ,
  rw has_deriv_at_iff_is_o_nhds_zero  at  localize,



  sorry,
  sorry,
end
