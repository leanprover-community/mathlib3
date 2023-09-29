/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import analysis.special_functions.log.base
import analysis.special_functions.log.deriv

/-!
# Stuff for analysis.special_functions.log.base
-/

namespace real

lemma has_deriv_at.logb {f : ℝ → ℝ} {x b f' : ℝ} (hf : has_deriv_at f f' x)
  (hx : f x ≠ 0) : has_deriv_at (λ y, logb b (f y)) (f' / (f x * log b)) x :=
by simpa [div_div] using (hf.log hx).div_const (log b)

-- TODO (BM): change to `⁻¹` rather than `1 /`
lemma has_deriv_at_logb {x b : ℝ} (hx : x ≠ 0) :
  has_deriv_at (logb b) (1 / (x * log b)) x :=
(has_deriv_at_id' _).logb hx

end real
