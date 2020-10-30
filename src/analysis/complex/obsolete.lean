-- def max_side_length (T: triangle ) : ℝ := Sup (set.range (λ i, abs (T (i+1) - T i)))

-- /-- Our definition of `max_side_length` (given as the max of the three side lengths, cyclically
-- around the triangle) is the same as a variant definition (the max of the lengths of the 9 = 3 × 3
-- diff-pairs. -/
-- lemma max_side_length_eq (T : triangle) (i j : zmod 3) :
--   abs (T i - T j) ≤ Sup (range (λ (i : zmod 3), abs (T (i + 1) - T i))) :=
-- begin
--   sorry,
-- end


-- /--
--   Not needed?
-- -/
-- lemma foo4 (T:triangle ) (i k : zmod 3) (j : option (zmod 3)) :
--   dist (T i)   (quadrisect T j k) ≤ max_side_length T :=
-- begin
--   /- AK -/
--   have TiInT : T i ∈ (triangle_hull T),
--   {
--     apply subset_convex_hull,
--     refine set.mem_range_self _,
--     --simp,
--     --apply set.mem_range.1,
--     --rw set.range,
--     ---???
--   },
--   have quadInT : (quadrisect T j k) ∈ (triangle_hull T),
--   {
--     have hs : finite (set.range T) := finite_range T,
--     rw triangle_hull,
--     simp [hs.convex_hull_eq],
--     split,
--     {
--       split,
--       {
--         intros,
--         sorry,
--         -- try again?
--       },

--       split,
--       {

--        sorry,
--       },
--       {

--         sorry,
--       },

--     },

--     {
--       sorry,
--     },
--   },
--   exact foo5 T (T i) (quadrisect T j k) TiInT quadInT,
-- end

-- /--
--   Not needed?
-- -/
-- lemma foo6 (T:triangle ) (j : option (zmod 3)) :
--   max_side_length (quadrisect T j) =
--   max_side_length T / 2 :=
-- begin
--   /- AK -/

--   sorry,
-- end
