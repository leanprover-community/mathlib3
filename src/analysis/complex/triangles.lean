import analysis.complex.basic
import data.zmod.basic
import measure_theory.interval_integral

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

/-- The integral of a function over a triangle is the sum of the four subdivided triangles
-/
lemma foo (f : ℂ → ℂ ) (T : triangle ) :
  contour_integral f T = ∑ i, contour_integral f (quadrisect T i)
  :=
begin

  /- Adrian? -/
  sorry,
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
    exact  finset.sum_le_sum (λ x _ , h x),
  end
-/

/-- The integral of a function over a triangle is bounded by the maximal of the four subdivided triangles
-/
lemma foo2 (f : ℂ → ℂ ) (T : triangle ) :
  abs (contour_integral f T) ≤
  4 * Sup (set.range (λ i, abs ( contour_integral f (quadrisect T i)))) :=
begin
  /- AK? -/
  rw foo,

  calc
 abs (∑ (i : option (zmod 3)), contour_integral f (quadrisect T i))
 ≤  ∑ (i : option (zmod 3)), abs( contour_integral f (quadrisect T i)) : _
 ... ≤ ∑ (i : option (zmod 3)),   Sup (set.range (λ i, abs ( contour_integral f (quadrisect T i)))) : _
... = 4 * Sup (set.range (λ i, abs ( contour_integral f (quadrisect T i)))) : _ ,

{
  --refine finset.abs_sum_le_sum_abs,
  sorry,
},

{
--  congr,
  sorry,
},

{
  rw sum_const,
  simp,
  left,
  -- ???
  sorry,
},
end

/--  ∫_a^b F' = F(b)-F(a)
-/
lemma foo3 (F: ℂ → ℂ ) (holc: differentiable ℂ F) (a b :ℂ ) :
  contour_integral_segment (deriv F) a b =
  F b - F a :=
begin
  /- Adrian? NOPE ! -/
  sorry,
end


/--  ∫_T F' = 0
-/
lemma foo3a (F: ℂ → ℂ ) (holc: differentiable ℂ F) (T: triangle ) :
  contour_integral (deriv F) T = 0 :=
begin
  /- AK NOPE! -/
  sorry,
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

lemma integral_smul_C  (c : ℂ) :
∫ (t : ℝ) in 0..1,  ((t:ℂ ) * c)
=
(∫ (t : ℝ) in 0..1, (t:ℂ )) * c
:=
begin
  --by library_search,
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
    sorry,
    sorry,
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
  /- Adrian? -/
  sorry,
end





def triangle_hull (T: triangle): set ℂ  := convex_hull (set.range T )

def max_side_length (T: triangle ) : ℝ := Sup (set.range (λ i, abs (T (i+1) - T i)))

lemma foo5 (T:triangle )
  (z w : ℂ ) (hz: z ∈  triangle_hull T) (hw: w ∈  triangle_hull T) :
  dist z w ≤ max_side_length T :=
begin
  /- HM -/
  sorry,
end

lemma foo4 (T:triangle ) (i k : zmod 3) (j : option (zmod 3)) :
  dist (T i)   (quadrisect T j k) ≤ max_side_length T :=
begin
  /- AK -/
  have TiInT : T i ∈ (triangle_hull T),
  {
    apply subset_convex_hull,
    refine set.mem_range_self _,
    --simp,
    --apply set.mem_range.1,
    --rw set.range,
    ---???
  },
  have quadInT : (quadrisect T j k) ∈ (triangle_hull T),
  {
    have hs : finite (set.range T) := finite_range T,
    rw triangle_hull,
    simp [hs.convex_hull_eq],
    split,
    {
      split,
      {
        intros,
        sorry,
        -- try again?
      },

      split,
      {

       sorry,
      },
      {

        sorry,
      },

    },

    {
      sorry,
    },
  },
  exact foo5 T (T i) (quadrisect T j k) TiInT quadInT,
end


lemma foo6 (T:triangle ) (j : option (zmod 3)) :
  max_side_length (quadrisect T j) =
  max_side_length T / 2 :=
begin
  /- AK -/

  sorry,
end

/- NEXT TIME -/

theorem Goursat (f : ℂ →  ℂ ) (holc: differentiable ℂ f) (T₀ : triangle ) :
  contour_integral f T₀  = 0 :=
begin

/-

theorem Goursat (f : ℂ →  ℂ ) (holc: differentiable ℂ f) (T: triangle ) :
  contour_integral f T = 0 :=
begin

  have : ∀ n , ∀ (T' :triangle ) , ∃ (T'' : triangle), -- ∃ j : option (zmod 3) ,
--    T'' = quadrisect T' j ∧
    abs ( contour_integral f T') ≤ 4^n * abs (contour_integral f T'')
    ∧
    max_side_length T'' ≤ 1/4^n * max_side_length T'
    ∧
    convex_hull T'' ⊂ convex_hull T'
    ,
    {
      sorry,
    },
  choose! T_seq  -- i h h' using this,
   H using this,

  let X := λ n, nat.rec_on n T _  _,
    --(λ n T, (T_seq n T) (H n T)),

  sorry,
end
-/

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
end

/--
  |∫_γ f| ≤ ⊔ |f|
-/


/--

  in a neighborhood of z,
  f(w) = f(z) + f'(z) (w-z) + Err

-/
