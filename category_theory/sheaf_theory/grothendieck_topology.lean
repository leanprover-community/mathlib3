-- Copyright (c) 2019 Johan Commelin. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Johan Commelin

import category_theory.sheaf_theory.sieve

universes v v₁ v₂ u u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

local notation a `∈`:50 b:50 := b a

namespace category_theory
open category_theory

structure grothendieck_topology (X : Type u) [category.{v} X] :=
(sieves   : Π {{U : X}}, set (sieve U))
(pullback : ∀ {U V : X} (f : V ⟶ U) (S : sieve U), sieves S → sieves (S.pullback f))
(univ     : ∀ {U : X}, sieves (sieve.univ : sieve U))
(inter    : ∀ {U : X} (S₁ S₂ : sieve U), sieves S₁ → sieves S₂ → sieves (S₁ ∩ S₂))
(union    : ∀ {U} (R : sieve U) (S : sieve U), -- cook up a good name, instead of "union"
              sieves R → (Π {V} (f : V ⟶ U), f ∈ R.val → sieves (S.pullback f)) → sieves S)

namespace grothendieck_topology
variables {X : Type u} [𝒳 : category.{v} X]
include 𝒳

end grothendieck_topology

end category_theory