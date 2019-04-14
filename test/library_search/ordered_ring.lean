import algebra.ordered_ring

-- This works fine:
example {a b : ℕ} (h : 0 < b) (w : 1 ≤ a) : b ≤ a * b :=
(le_mul_iff_one_le_left h).mpr w

-- open tactic
-- meta def f : tactic unit :=
-- do d ← get_decl `le_mul_iff_one_le_left,
--    (e, t) ← library_search.decl_mk_const d,
--    trace t,
--    trace e,
--    mp ← iff_mpr_core e t,
--    trace mp,
--    apply mp,
--    skip

-- set_option pp.universes true

-- example {a b : ℕ} : b ≤ a * b :=
-- begin
--   f,
-- end

example {a b : ℕ} (h : b > 0) (w : a ≥ 1) : b ≤ a * b :=
by library_search -- exact (le_mul_iff_one_le_left h).mpr w
