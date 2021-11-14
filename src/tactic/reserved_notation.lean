/-
Copyright (c) 2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/

/-!
# Reserved notation

This file is imported by `logic.basic` and `logic.relator` to place it at the top of the
import graph.

We place all of `mathlib`'s reserved notation in this file so that users will know not to
use them as e.g. variable names without needing to import the specific file where they
are defined.

-/

-- used in `logic/relator.lean`
reserve infixr ` ⇒ `:40

-- used in `tactic/core.lean`
precedence `setup_tactic_parser`:0
reserve prefix `pformat! `:100
reserve prefix `fail! `:100
reserve prefix `trace! `:100

-- used in `tactic/localized.lean`
reserve notation `localized`

-- used in `tactic/lint/frontend.lean`
reserve notation `#lint`
reserve notation `#lint_mathlib`
reserve notation `#lint_all`
reserve notation `#list_linters`

-- used in `tactic/where.lean`
reserve prefix `#where`:max

-- used in `tactic/simps.lean`
reserve notation `initialize_simps_projections`
reserve notation `as_prefix`

-- used in `tactic/lift.lean`
reserve notation `to`

-- used in `tactic/rcases.lean`
precedence `?`:max

-- used in `order/lattice.lean`
reserve infixl ` ⊓ `:70
reserve infixl ` ⊔ `:65

-- used in `algebra/module/linear_map.lean`
reserve infix ` ≃ₗ `:25
