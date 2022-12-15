/-
Copyright (c) 2022 André Hernandez-Espiet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : André Hernandez-Espiet
-/

import data.real.basic
import data.set.finite
import data.matrix.basic
import data.real.sqrt

example (a b c : ℝ ) (h : real.sqrt a = 0  ) : a =0 :=
begin
  have := real.sqrt_eq_zero,
end
