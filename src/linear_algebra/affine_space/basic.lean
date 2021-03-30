/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import algebra.add_torsor

/-!
# Affine space

In this file we introduce the following notation:

* `affine_space V P` is an alternative notation for `add_torsor V P` introduced at the end of this
  file.

We tried to use an `abbreviation` instead of a `notation` but this led to hard-to-debug elaboration
errors. So, we introduce a localized notation instead. When this notation is enabled with
`open_locale affine`, Lean will use `affine_space` instead of `add_torsor` both in input and in the
proof state.

Here is an incomplete list of notions related to affine spaces, all of them are defined in other
files:

* `affine_map`: a map between affine spaces that preserves the affine structure;
* `affine_equiv`: an equivalence between affine spaces that preserves the affine structure;
* `affine_subspace`: a subset of an affine space closed w.r.t. affine combinations of points;
* `affine_combination`: an affine combination of points;
* `affine_independent`: affine independent set of points.

## TODO

Some key definitions are not yet present.

* Affine frames.  An affine frame might perhaps be represented as an `affine_equiv` to a `finsupp`
  (in the general case) or function type (in the finite-dimensional case) that gives the
  coordinates, with appropriate proofs of existence when `k` is a field.

* Although results on affine combinations implicitly provide barycentric frames and coordinates,
  there is no explicit representation of the map from a point to its coordinates.
 -/

localized "notation `affine_space` := add_torsor" in affine
