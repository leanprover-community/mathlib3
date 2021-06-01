/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import tactic.basic

namespace bundle
/- We provide a type synonym of `Σ x, E x` as `bundle.total_space E`, to be able to endow it with
a topology which is not the disjoint union topology. In general, the constructions of fiber bundles
we will make will be of this form. -/

variables {B : Type*} (E : B → Type*)

/--
`total_space E` is the total space of the bundle `Σ x, E x`. This type synonym is used to avoid
conflicts with general sigma types.
-/
def total_space := Σ x, E x

instance [inhabited B] [inhabited (E (default B))] :
  inhabited (total_space E) := ⟨⟨default B, default (E (default B))⟩⟩

/-- `bundle.proj E` is the canonical projection `total_space E → B` on the base space. -/
@[simp] def proj : total_space E → B :=
λ (y : total_space E), y.1

instance {x : B} : has_coe_t (E x) (total_space E) := ⟨λ y, (⟨x, y⟩ : total_space E)⟩

lemma to_total_space_coe {x : B} (v : E x) : (v : total_space E) = ⟨x, v⟩ := rfl

/-- `bundle.trivial B F` is the trivial bundle over `B` of fiber `F`. -/
@[nolint unused_arguments]
def trivial (B : Type*) (F : Type*) : B → Type* := λ x, F

instance {F : Type*} [inhabited F] {b : B} : inhabited (bundle.trivial B F b) :=
⟨(default F : F)⟩

/-- The trivial bundle, unlike other bundles, has a canonical projection on the fiber. -/
def trivial.proj_snd (B : Type*) (F : Type*) : (total_space (bundle.trivial B F)) → F := sigma.snd

end bundle
