/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.set.lattice
import order.directed
/-!
# Union lift
This file defines `set.Union_lift` to glue together functions defined on each of a collection of
sets to make a function on the Union of those sets.

## Main definitions

* `set.Union_lift` -  Given a Union of sets `Union S`, define a function on the Union by defining
it on each component, and proving that it agrees on the intersections.
* `set.lift_of_eq_Union` Version of `Union_lift` for a set that is propositionally equal to `Union S`.
  This is mainly motivated by the need to define functions on directed supremums of e.g. subgroups,
  where the supremum is propositionally, but not definitionally equal to the Union.

## Main statements

There are proofs of the obvious properties of `Union_lift`, i.e. what it does to elements of
each of the sets in the `Union`, stated in different ways.

There are also three lemmas about `Union_lift` and three lemmas about `lift_of_eq_Union` intended
to aid with proving that `Union_lift` of `lift_of_eq_Union` is a homomorphism when defined
on a Union of substructures. There is one lemma each to show that constants, unary functions,
or binary functions are preserved. These lemmas are:

*`set.Union_lift_const`
*`set.Union_lift_unary`
*`set.Union_lift_binary`
*`set.lift_of_eq_Union_const`
*`set.lift_of_eq_Union_unary`
*`set.lift_of_eq_Union_binary`

## Tags

directed union, directed supremum, glue, gluing
-/

variables {α ι β : Type*}

namespace set

/- The unused argument `hf` is left in the definition so that the `simp` lemmas
`Union_lift_inclusion` will work without the user having to provide `hf` explicitly to
simplify terms involving `Union_lift`. -/
/-- Given a Union of sets `Union S`, define a function on the Union by defining
it on each component, and proving that it agrees on the intersections. -/
@[nolint unused_arguments]
noncomputable def Union_lift (S : ι → set α)
  (f : Π i (x : S i), β)
  (hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
  (x : Union S) : β :=
let i := classical.indefinite_description _ (mem_Union.1 x.2) in
f i ⟨x, i.prop⟩

@[simp] lemma Union_lift_inclusion {S : ι → set α}
  {f : Π i (x : S i), β}
  {hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ }
  {i : ι} (x : S i) (h : S i ⊆ Union S := set.subset_Union S i) :
  Union_lift S f hf (set.inclusion h x) = f i x :=
let j := classical.indefinite_description _ (mem_Union.1 (h x.2)) in
by cases x with x hx; exact hf j i x j.2 hx

@[simp] lemma Union_lift_mk
  {S : ι → set α}
  {f : Π i (x : S i), β}
  {hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ }
  {i : ι} (x : S i) (hx : (x : α) ∈ Union S := set.subset_Union S i x.2) :
  Union_lift S f hf ⟨x, hx⟩ = f i x :=
Union_lift_inclusion x

lemma Union_lift_of_mem
  {S : ι → set α}
  {f : Π i (x : S i), β}
  {hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ }
  (x : Union S) {i : ι} (hx : (x : α) ∈ S i) :
  Union_lift S f hf x = f i ⟨x, hx⟩ :=
by cases x with x hx; exact hf _ _ _ _ _

/-- `Union_lift_const` is useful for proving that `Union_lift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of group homomorphisms on a union of subgroups preserves `1`. See also
  `lift_of_eq_Union_const` -/
lemma Union_lift_const
  {S : ι → set α}
  {f : Π i (x : S i), β}
  {hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
  (c : Union S)
  (ci : Π i, S i)
  (hci : ∀ i, (ci i : α) = c)
  (cβ : β)
  (h : ∀ i, f i (ci i) = cβ) :
  Union_lift S f hf c = cβ :=
let ⟨i, hi⟩ := set.mem_Union.1 c.prop in
have (ci i) = ⟨c, hi⟩, from subtype.ext (hci i),
by rw [Union_lift_of_mem _ hi, ← this, h]

/-- `Union_lift_unary` is useful for proving that `Union_lift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of linear_maps on a union of submodules preserves scalar multiplication. See also
  `lift_of_eq_Union_unary` -/
lemma Union_lift_unary
  {S : ι → set α}
  {f : Π i (x : S i), β}
  {hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
  (u : (Union S) → (Union S))
  (ui : Π i, S i → S i)
  (hui : ∀ i x, set.inclusion (set.subset_Union S i) (ui i x) =
    u (set.inclusion (set.subset_Union S i) x))
  (uβ : β → β)
  (h : ∀ i (x : S i), (f i (ui i x)) = uβ (f i x))
  (x : Union S) :
  Union_lift S f hf (u x) = uβ (Union_lift S f hf x) :=
begin
  cases set.mem_Union.1 x.prop with i hi,
  rw [Union_lift_of_mem x hi, ← h i],
  have : x = (set.inclusion (set.subset_Union S i) ⟨x, hi⟩), { cases x, refl },
  have hx' : (set.inclusion (set.subset_Union S i) (ui i ⟨x, hi⟩) : α) ∈ S i,
    from  (ui i ⟨x, hi⟩).prop,
  conv_lhs { rw [this, ← hui, Union_lift_of_mem _ hx'] },
  simp only [coe_inclusion, subtype.coe_eta]
end

/-- `Union_lift_binary` is useful for proving that `Union_lift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of group homomorphisms on a union of subgroups preserves `*`. See also
  `lift_of_eq_Union_binary` -/
lemma Union_lift_binary
  {S : ι → set α}
  {f : Π i (x : S i), β}
  {hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
  (dir: directed (≤) S)
  (op : (Union S) → (Union S) → (Union S))
  (opi : Π i, S i → S i → S i)
  (hopi : ∀ i x y, set.inclusion (set.subset_Union S i) (opi i x y) =
    op (set.inclusion (set.subset_Union S i) x)
       (set.inclusion (set.subset_Union S i) y))
  (opβ : β → β → β)
  (h : ∀ i (x y : S i), (f i (opi i x y)) = opβ (f i x) (f i y))
  (x y : Union S) :
  Union_lift S f hf (op x y) = opβ (Union_lift S f hf x) (Union_lift S f hf y) :=
begin
  cases set.mem_Union.1 x.prop with i hi,
  cases set.mem_Union.1 y.prop with j hj,
  rcases dir i j with ⟨k, hik, hjk⟩,
  rw [Union_lift_of_mem x (hik hi), Union_lift_of_mem y (hjk hj), ← h k],
  have hx : x = (set.inclusion (set.subset_Union S k) ⟨x, hik hi⟩), { cases x, refl },
  have hy : y = (set.inclusion (set.subset_Union S k) ⟨y, hjk hj⟩), { cases y, refl },
  have hxy : (set.inclusion (set.subset_Union S k) (opi k ⟨x, hik hi⟩ ⟨y, hjk hj⟩) : α) ∈ S k,
    from (opi k ⟨x, hik hi⟩ ⟨y, hjk hj⟩).prop,
  conv_lhs { rw [hx, hy, ← hopi, Union_lift_of_mem _ hxy] },
  simp only [coe_inclusion, subtype.coe_eta]
end

/-- Version of `Union_lift` for sets that are propositionally equal to the Union.
  Define a map on a set equal to the `Union` of sets by defining it on each of the sets
  in the `Union`. -/
noncomputable def lift_of_eq_Union
  (S : ι → set α)
  (f : Π i (x : S i), β)
  (hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
  (T : set α) (hT : T = ⋃ i, S i)
  (x : T) : β :=
by subst hT; exact Union_lift S f hf x

@[simp] lemma lift_of_eq_Union_inclusion {S : ι → set α}
  {f : Π i (x : S i), β}
  {hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ }
  {T : set α} {hT : T = Union S}
  {i : ι} (x : S i) (h : S i ⊆ T := hT.symm ▸ set.subset_Union S i) :
  lift_of_eq_Union S f hf T hT (set.inclusion h x) = f i x :=
begin
  subst hT,
  delta lift_of_eq_Union,
  exact Union_lift_inclusion x h
end

@[simp] lemma lift_of_eq_Union_mk
  {S : ι → set α}
  {f : Π i (x : S i), β}
  {hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ }
  {T : set α} {hT : T = Union S}
  {i : ι} (x : S i)
  (hx : (x : α) ∈ T := hT.symm ▸ set.subset_Union S i x.prop) :
  lift_of_eq_Union S f hf T hT ⟨x, hx⟩ = f i x :=
begin
  subst hT,
  delta lift_of_eq_Union,
  exact Union_lift_mk x hx
end

lemma lift_of_eq_Union_of_mem
  {S : ι → set α}
  {f : Π i (x : S i), β}
  {hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ }
  {T : set α} {hT : T = Union S}
  (x : T) {i : ι} (hx : (x : α) ∈ S i) :
  lift_of_eq_Union S f hf T hT x = f i ⟨x, hx⟩ :=
begin
  subst hT,
  delta lift_of_eq_Union,
  exact Union_lift_of_mem x hx
end

/-- Version of `Union_lift_const` for `lift_of_eq_Union`. -/
lemma lift_of_eq_Union_const
  {S : ι → set α}
  {f : Π i (x : S i), β}
  {hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
  {T : set α} {hT : T = Union S}
  (c : T)
  (ci : Π i, S i)
  (hci : ∀ i, (ci i : α) = c)
  (cβ : β)
  (h : ∀ i, f i (ci i) = cβ) :
  lift_of_eq_Union S f hf T hT c = cβ :=
begin
  subst T,
  delta lift_of_eq_Union,
  exact Union_lift_const c ci hci cβ h
end

/-- Version of `Union_lift_unary` for `lift_of_eq_Union`. -/
lemma lift_of_eq_Union_unary
  {S : ι → set α}
  {f : Π i (x : S i), β}
  {hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
  {T : set α} {hT : T = Union S}
  (u : T → T)
  (ui : Π i, S i → S i)
  (hui : ∀ i x, set.inclusion (show S i ⊆ T, from hT.symm ▸ set.subset_Union S i) (ui i x) =
    u (set.inclusion (show S i ⊆ T, from hT.symm ▸ set.subset_Union S i) x))
  (uβ : β → β)
  (h : ∀ i (x : S i), (f i (ui i x)) = uβ (f i x))
  (x : T) :
  lift_of_eq_Union S f hf T hT (u x) = uβ (lift_of_eq_Union S f hf T hT x) :=
begin
  subst T,
  delta lift_of_eq_Union,
  exact Union_lift_unary u ui hui uβ h x
end

/-- Version of `Union_lift_binary` for `lift_of_eq_Union`. -/
lemma lift_of_eq_Union_binary
  {S : ι → set α}
  {f : Π i (x : S i), β}
  {hf : ∀ i j (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
  {T : set α} {hT : T = ⋃ i, S i}
  (dir: directed (≤) S)
  (op : T → T → T)
  (opi : Π i, S i → S i → S i)
  (hopi : ∀ i x y, set.inclusion (show S i ⊆ T, from hT.symm ▸ set.subset_Union S i) (opi i x y) =
    op (set.inclusion (show S i ⊆ T, from hT.symm ▸ set.subset_Union S i) x)
       (set.inclusion (show S i ⊆ T, from hT.symm ▸ set.subset_Union S i) y))
  (opβ : β → β → β)
  (h : ∀ i (x y : S i), (f i (opi i x y)) = opβ (f i x) (f i y))
  (x y : T) :
  lift_of_eq_Union S f hf T hT (op x y) =
    opβ (lift_of_eq_Union S f hf T hT x)
      (lift_of_eq_Union S f hf T hT y) :=
begin
  subst T,
  delta lift_of_eq_Union,
  exact Union_lift_binary dir op opi hopi opβ h x y
end

attribute [irreducible] lift_of_eq_Union Union_lift

end set
