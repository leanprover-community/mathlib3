/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import data.list.nodup

/-!
# Finite products of Types

This file defines the product of types over a list. For `l : list ι` and `α : ι → Type*` we define
`tprod α l = l.foldr (λ i β, α i × β) punit`. It is used to transfer results from binary products to
finitary products, like for product measures.

## Main definitions

* We have the equivalence `tprod.pi_equiv_tprod : (Π i, α i) ≃ tprod α l`
  if `l` contains every element of `ι` exactly once.
* The product of sets is `set.tprod : (Π i, set (α i)) → set (tprod α l)`.
-/

open list function

variables {ι : Type*} (α : ι → Type*) {i j : ι} {l : list ι} {f : Π i, α i}

/-- The product of a family of types over a list. -/
@[nolint has_inhabited_instance] def tprod (l : list ι) : Type* :=
l.foldr (λ i β, α i × β) punit

variable {α}

namespace tprod

open list

/-- Turning a function `f : Π i, α i` into an element of the iterated product `tprod α l`. -/
protected def mk : ∀ (l : list ι) (f : Π i, α i), tprod α l
| []        := λ f, punit.star
| (i :: is) := λ f, (f i, mk is f)

@[simp] lemma fst_mk (i : ι) (l : list ι) (f : Π i, α i) : (tprod.mk (i::l) f).1 = f i := rfl

@[simp]
lemma snd_mk (i : ι) (l : list ι) (f : Π i, α i) : (tprod.mk (i::l) f).2 = tprod.mk l f := rfl

variables [decidable_eq ι]

/-- Given an element of the iterated product `l.prod α`, take a projection into direction `i`.
  If `i` appears multiple times in `l`, this chooses the first component in direction `i`. -/
protected def elim : ∀ {l : list ι} (v : tprod α l) {i : ι} (hi : i ∈ l), α i
| (i :: is) v j hj :=
  if hji : j = i then by { subst hji, exact v.1 } else elim v.2 (hj.resolve_left hji)

@[simp] lemma elim_self (v : tprod α (i :: l)) : v.elim (l.mem_cons_self i) = v.1 :=
by simp [tprod.elim]

@[simp] lemma elim_of_ne (hj : j ∈ i :: l) (hji : j ≠ i) (v : tprod α (i :: l)) :
  v.elim hj = tprod.elim v.2 (hj.resolve_left hji) :=
by simp [tprod.elim, hji]

@[simp] lemma elim_of_mem (hl : (i :: l).nodup) (hj : j ∈ l) (v : tprod α (i :: l)) :
  v.elim (mem_cons_of_mem _ hj) = tprod.elim v.2 hj :=
by { apply elim_of_ne, rintro rfl, exact not_mem_of_nodup_cons hl hj }

lemma elim_mk : ∀ (l : list ι) (f : Π i, α i) {i : ι} (hi : i ∈ l),
  (tprod.mk l f).elim hi = f i
| (i :: is) f j hj := begin
      by_cases hji : j = i,
      { subst hji, simp },
      { rw [elim_of_ne _ hji, snd_mk, elim_mk] }
  end

@[ext] lemma ext : ∀ {l : list ι} (hl : l.nodup) {v w : tprod α l}
  (hvw : ∀ i (hi : i ∈ l), v.elim hi = w.elim hi), v = w
| []        hl v w hvw := punit.ext
| (i :: is) hl v w hvw := begin
    ext, rw [← elim_self v, hvw, elim_self],
    refine ext (nodup_cons.mp hl).2 (λ j hj, _),
    rw [← elim_of_mem hl, hvw, elim_of_mem hl]
  end

/-- A version of `tprod.elim` when `l` contains all elements. In this case we get a function into
  `Π i, α i`. -/
@[simp] protected def elim' (h : ∀ i, i ∈ l) (v : tprod α l) (i : ι) : α i :=
v.elim (h i)

lemma mk_elim (hnd : l.nodup) (h : ∀ i, i ∈ l) (v : tprod α l) : tprod.mk l (v.elim' h) = v :=
tprod.ext hnd (λ i hi, by simp [elim_mk])

/-- Pi-types are equivalent to iterated products. -/
def pi_equiv_tprod (hnd : l.nodup) (h : ∀ i, i ∈ l) : (Π i, α i) ≃ tprod α l :=
⟨tprod.mk l, tprod.elim' h, λ f, funext $ λ i, elim_mk l f (h i), mk_elim hnd h⟩

end tprod

namespace set

open list
/-- A product of sets in `tprod α l`. -/
@[simp] protected def tprod : ∀ (l : list ι) (t : Π i, set (α i)), set (tprod α l)
| []        t := univ
| (i :: is) t := (t i).prod (tprod is t)

lemma mk_preimage_tprod : ∀ (l : list ι) (t : Π i, set (α i)),
  tprod.mk l ⁻¹' set.tprod l t = {i | i ∈ l}.pi t
| []        t := by simp [set.tprod]
| (i :: l) t := begin
  ext f,
  have : f ∈ tprod.mk l ⁻¹' set.tprod l t ↔ f ∈ {x | x ∈ l}.pi t, { rw [mk_preimage_tprod l t] },
  change tprod.mk l f ∈ set.tprod l t ↔ ∀ (i : ι), i ∈ l → f i ∈ t i at this,
  /- `simp [set.tprod, tprod.mk, this]` can close this goal but is slow. -/
  rw [set.tprod, tprod.mk, mem_preimage, mem_pi, prod_mk_mem_set_prod_eq],
  simp_rw [mem_set_of_eq, mem_cons_iff],
  rw [forall_eq_or_imp, and.congr_right_iff],
  exact λ _, this
end

lemma elim_preimage_pi [decidable_eq ι] {l : list ι} (hnd : l.nodup) (h : ∀ i, i ∈ l)
  (t : Π i, set (α i)) : tprod.elim' h ⁻¹' pi univ t = set.tprod l t :=
begin
  have : { i | i ∈ l} = univ, { ext i, simp [h] },
  rw [← this, ← mk_preimage_tprod, preimage_preimage],
  convert preimage_id, simp [tprod.mk_elim hnd h, id_def]
end

end set
