/-
Copyright (c) 2019 Lucas Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Allen
-/
import tactic.converter.interactive

/-!
# Tests for the `conv` tactic inside the interactive `conv` monad
-/

example (a b c d : ℕ) (h₁ : b = c) (h₂ : a + c = a + d) : a + b = a + d :=
begin
conv {     --| a + b = a + d
  --Conv to the left hand side
  to_lhs,  -- | a + b
  --Zoom into the left hand side.
  conv {   -- | a + b
    congr, -- two goals: | a and | b
    skip,  -- | b
    rw h₁, -- | c
  },       -- | a + c
  --At this point, to get back to this position, without zoom, we would need to close
  --this conv block, and open a new one.
  rw h₂,   -- | a + d
},         -- goals accomplished
end

example : 1 + (5 * 8) - (3 * 14) + (4 * 99 - 45) - 350 = 1 :=
begin
  have h₁ : 5 * 8 = 40, from dec_trivial,
  have h₂ : 3 * 14 = 42, from dec_trivial,
  have h₃ : 4 * 99 - 45 = 351, from dec_trivial,
  conv {
    to_lhs,    -- conv to the left hand side
    conv {     -- zooming in to rewrite 4 * 99 - 45 to 351
      congr, congr, skip,
      rw h₃,
    },         -- returning to the left hand side, note we don't need to open a new conv block
    conv {     -- zooming in to rewrite 3 * 14 to 42
      congr, congr, congr, skip,
      rw h₂,
    },         -- returning to the left hand side
    conv {     -- zooming in to rewrite 5 * 8 to 40
      congr, congr, congr, congr, skip,
      rw h₁,
    },         -- returning to the left hand side
  },
end
