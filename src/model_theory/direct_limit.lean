/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.fintype.order
import algebra.direct_limit
import model_theory.quotients
import model_theory.finitely_generated

/-!
# Direct Limits of First-Order Structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file constructs the direct limit of a directed system of first-order embeddings.

## Main Definitions
* `first_order.language.direct_limit G f`  is the direct limit of the directed system `f` of
  first-order embeddings between the structures indexed by `G`.
-/

universes v w u₁ u₂

open_locale first_order
namespace first_order
namespace language
open Structure set

variables {L : language} {ι : Type v} [preorder ι]
variables {G : ι → Type w} [Π i, L.Structure (G i)]
variables (f : Π i j, i ≤ j → G i ↪[L] G j)

namespace directed_system

/-- A copy of `directed_system.map_self` specialized to `L`-embeddings, as otherwise the
`λ i j h, f i j h` can confuse the simplifier. -/
lemma map_self [directed_system G (λ i j h, f i j h)] (i x h) :
  f i i h x = x :=
directed_system.map_self (λ i j h, f i j h) i x h

/-- A copy of `directed_system.map_map` specialized to `L`-embeddings, as otherwise the
`λ i j h, f i j h` can confuse the simplifier. -/
lemma map_map [directed_system G (λ i j h, f i j h)] {i j k} (hij hjk x) :
  f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x :=
directed_system.map_map (λ i j h, f i j h) hij hjk x

variables {G' : ℕ → Type w} [Π i, L.Structure (G' i)] (f' : Π (n : ℕ), G' n ↪[L] G' (n + 1))

/-- Given a chain of embeddings of structures indexed by `ℕ`, defines a `directed_system` by
composing them. -/
def nat_le_rec (m n : ℕ) (h : m ≤ n) : G' m ↪[L] G' n :=
nat.le_rec_on h (λ k g, (f' k).comp g) (embedding.refl L _)

@[simp] lemma coe_nat_le_rec (m n : ℕ) (h : m ≤ n) :
  (nat_le_rec f' m n h : G' m → G' n) = nat.le_rec_on h (λ n, f' n) :=
begin
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le h,
  ext x,
  induction k with k ih,
  { rw [nat_le_rec, nat.le_rec_on_self, embedding.refl_apply, nat.le_rec_on_self] },
  { rw [nat.le_rec_on_succ le_self_add, nat_le_rec, nat.le_rec_on_succ le_self_add, ← nat_le_rec,
      embedding.comp_apply, ih] }
end

instance nat_le_rec.directed_system : directed_system G' (λ i j h, nat_le_rec f' i j h) :=
⟨λ i x h, congr (congr rfl (nat.le_rec_on_self _)) rfl,
  λ i j k ij jk, by simp [nat.le_rec_on_trans ij jk]⟩

end directed_system

namespace direct_limit

/-- Raises a family of elements in the `Σ`-type to the same level along the embeddings. -/
def unify {α : Type*} (x : α → (Σ i, G i)) (i : ι)
  (h : i ∈ upper_bounds (range (sigma.fst ∘ x))) (a : α) : G i :=
f (x a).1 i (h (mem_range_self a)) (x a).2

variable [directed_system G (λ i j h, f i j h)]

@[simp] lemma unify_sigma_mk_self {α : Type*} {i : ι}
  {x : α → G i} :
  unify f (sigma.mk i ∘ x) i (λ j ⟨a, hj⟩, trans (le_of_eq hj.symm) (refl _)) = x :=
begin
  ext a,
  simp only [unify, directed_system.map_self],
end

lemma comp_unify {α : Type*} {x : α → (Σ i, G i)} {i j : ι}
  (ij : i ≤ j) (h : i ∈ upper_bounds (range (sigma.fst ∘ x))) :
  (f i j ij) ∘ (unify f x i h) = unify f x j (λ k hk, trans (mem_upper_bounds.1 h k hk) ij) :=
begin
  ext a,
  simp [unify, directed_system.map_map],
end

end direct_limit

variables (G)

namespace direct_limit

/-- The directed limit glues together the structures along the embeddings. -/
def setoid [directed_system G (λ i j h, f i j h)] [is_directed ι (≤)] :
  setoid (Σ i, G i) :=
{ r := λ ⟨i, x⟩ ⟨j, y⟩, ∃ (k : ι) (ik : i ≤ k) (jk : j ≤ k), f i k ik x = f j k jk y,
  iseqv := ⟨λ ⟨i, x⟩, ⟨i, refl i, refl i, rfl⟩,
    λ ⟨i, x⟩ ⟨j, y⟩ ⟨k, ik, jk, h⟩, ⟨k, jk, ik, h.symm⟩,
    λ ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ ⟨ij, hiij, hjij, hij⟩ ⟨jk, hjjk, hkjk, hjk⟩,
      begin
        obtain ⟨ijk, hijijk, hjkijk⟩ := (directed_of (≤) ij jk),
        refine ⟨ijk, le_trans hiij hijijk, le_trans hkjk hjkijk, _⟩,
        rw [← directed_system.map_map, hij, directed_system.map_map],
        symmetry,
        rw [← directed_system.map_map, ← hjk, directed_system.map_map],
      end ⟩ }

/-- The structure on the `Σ`-type which becomes the structure on the direct limit after quotienting.
 -/
noncomputable def sigma_structure [is_directed ι (≤)] [nonempty ι] : L.Structure (Σ i, G i) :=
{ fun_map := λ n F x, ⟨_, fun_map F (unify f x
  (classical.some (fintype.bdd_above_range (λ a, (x a).1)))
  (classical.some_spec (fintype.bdd_above_range (λ a, (x a).1))))⟩,
                    rel_map := λ n R x, rel_map R (unify f x
  (classical.some (fintype.bdd_above_range (λ a, (x a).1)))
  (classical.some_spec (fintype.bdd_above_range (λ a, (x a).1)))) }

end direct_limit

/-- The direct limit of a directed system is the structures glued together along the embeddings. -/
def direct_limit [directed_system G (λ i j h, f i j h)] [is_directed ι (≤)] :=
quotient (direct_limit.setoid G f)

local attribute [instance] direct_limit.setoid

instance [directed_system G (λ i j h, f i j h)] [is_directed ι (≤)] [inhabited ι]
  [inhabited (G default)] : inhabited (direct_limit G f) :=
⟨⟦⟨default, default⟩⟧⟩

namespace direct_limit

variables [is_directed ι (≤)] [directed_system G (λ i j h, f i j h)]

lemma equiv_iff {x y : Σ i, G i} {i : ι} (hx : x.1 ≤ i) (hy : y.1 ≤ i) :
  x ≈ y ↔ (f x.1 i hx) x.2 = (f y.1 i hy) y.2 :=
begin
  cases x,
  cases y,
  refine ⟨λ xy, _, λ xy, ⟨i, hx, hy, xy⟩⟩,
  obtain ⟨j, _, _, h⟩ := xy,
  obtain ⟨k, ik, jk⟩ := directed_of (≤) i j,
  have h := congr_arg (f j k jk) h,
  apply (f i k ik).injective,
  rw [directed_system.map_map, directed_system.map_map] at *,
  exact h
end

lemma fun_map_unify_equiv {n : ℕ} (F : L.functions n) (x : (fin n) → (Σ i, G i)) (i j : ι)
  (hi : i ∈ upper_bounds (range (sigma.fst ∘ x))) (hj : j ∈ upper_bounds (range (sigma.fst ∘ x))) :
  (⟨i, fun_map F (unify f x i hi)⟩ : Σ i, G i) ≈ ⟨j, fun_map F (unify f x j hj)⟩ :=
begin
  obtain ⟨k, ik, jk⟩ := directed_of (≤) i j,
  refine ⟨k, ik, jk, _⟩,
  rw [(f i k ik).map_fun, (f j k jk).map_fun, comp_unify, comp_unify],
end

lemma rel_map_unify_equiv {n : ℕ} (R : L.relations n) (x : (fin n) → (Σ i, G i)) (i j : ι)
  (hi : i ∈ upper_bounds (range (sigma.fst ∘ x))) (hj : j ∈ upper_bounds (range (sigma.fst ∘ x)))  :
  rel_map R (unify f x i hi) = rel_map R (unify f x j hj) :=
begin
  obtain ⟨k, ik, jk⟩ := directed_of (≤) i j,
  rw [← (f i k ik).map_rel, comp_unify, ← (f j k jk).map_rel, comp_unify],
end

variable [nonempty ι]

lemma exists_unify_eq {α : Type*} [fintype α] {x y : α → (Σ i, G i)} (xy : x ≈ y) :
  ∃ (i : ι) (hx : i ∈ upper_bounds (range (sigma.fst ∘ x)))
    (hy : i ∈ upper_bounds (range (sigma.fst ∘ y))),
  unify f x i hx = unify f y i hy :=
begin
  obtain ⟨i, hi⟩ := fintype.bdd_above_range (sum.elim (λ a, (x a).1) (λ a, (y a).1)),
  rw [sum.elim_range, upper_bounds_union] at hi,
  simp_rw [← function.comp_apply sigma.fst _] at hi,
  exact ⟨i, hi.1, hi.2, funext (λ a, (equiv_iff G f _ _).1 (xy a))⟩,
end

lemma fun_map_equiv_unify {n : ℕ} (F : L.functions n) (x : (fin n) → (Σ i, G i)) (i : ι)
  (hi : i ∈ upper_bounds (range (sigma.fst ∘ x))) :
  @fun_map _ _ (sigma_structure G f) _ F x ≈ ⟨_, fun_map F (unify f x i hi)⟩ :=
fun_map_unify_equiv G f F x (classical.some (fintype.bdd_above_range (λ a, (x a).1))) i _ hi

lemma rel_map_equiv_unify {n : ℕ} (R : L.relations n) (x : (fin n) → (Σ i, G i)) (i : ι)
  (hi : i ∈ upper_bounds (range (sigma.fst ∘ x)))  :
  @rel_map _ _ (sigma_structure G f) _ R x = rel_map R (unify f x i hi) :=
rel_map_unify_equiv G f R x (classical.some (fintype.bdd_above_range (λ a, (x a).1))) i _ hi

/-- The direct limit `setoid` respects the structure `sigma_structure`, so quotienting by it
  gives rise to a valid structure. -/
noncomputable instance prestructure : L.prestructure (direct_limit.setoid G f) :=
{ to_structure := sigma_structure G f,
  fun_equiv := λ n F x y xy, begin
    obtain ⟨i, hx, hy, h⟩ := exists_unify_eq G f xy,
    refine setoid.trans (fun_map_equiv_unify G f F x i hx)
      (setoid.trans _ (setoid.symm (fun_map_equiv_unify G f F y i hy))),
    rw h,
  end,
  rel_equiv := λ n R x y xy, begin
    obtain ⟨i, hx, hy, h⟩ := exists_unify_eq G f xy,
    refine trans (rel_map_equiv_unify G f R x i hx)
      (trans _ (symm (rel_map_equiv_unify G f R y i hy))),
    rw h,
  end }

/-- The `L.Structure` on a direct limit of `L.Structure`s. -/
noncomputable instance Structure : L.Structure (direct_limit G f) := language.quotient_structure

@[simp] lemma fun_map_quotient_mk_sigma_mk {n : ℕ} {F : L.functions n} {i : ι} {x : fin n → G i} :
  fun_map F (λ a, (⟦⟨i, x a⟩⟧ : direct_limit G f)) = ⟦⟨i, fun_map F x⟩⟧ :=
begin
  simp only [function.comp_app, fun_map_quotient_mk, quotient.eq],
  obtain ⟨k, ik, jk⟩ := directed_of (≤) i (classical.some (fintype.bdd_above_range
    (λ (a : fin n), i))),
  refine ⟨k, jk, ik, _⟩,
  simp only [embedding.map_fun, comp_unify],
  refl
end

@[simp] lemma rel_map_quotient_mk_sigma_mk {n : ℕ} {R : L.relations n} {i : ι} {x : fin n → G i} :
  rel_map R (λ a, (⟦⟨i, x a⟩⟧ : direct_limit G f)) = rel_map R x :=
begin
  rw [rel_map_quotient_mk],
  obtain ⟨k, ik, jk⟩ := directed_of (≤) i (classical.some (fintype.bdd_above_range
    (λ (a : fin n), i))),
  rw [rel_map_equiv_unify G f R (λ a, ⟨i, x a⟩) i, unify_sigma_mk_self],
end

lemma exists_quotient_mk_sigma_mk_eq {α : Type*} [fintype α] (x : α → direct_limit G f) :
  ∃ (i : ι) (y : α → G i), x = quotient.mk ∘ (sigma.mk i) ∘ y :=
begin
  obtain ⟨i, hi⟩ := fintype.bdd_above_range (λ a, (x a).out.1),
  refine ⟨i, unify f (quotient.out ∘ x) i hi, _⟩,
  ext a,
  rw [quotient.eq_mk_iff_out, function.comp_app, unify, equiv_iff G f _],
  { simp only [directed_system.map_self] },
  { refl }
end

variables (L ι)

/-- The canonical map from a component to the direct limit. -/
def of (i : ι) : G i ↪[L] direct_limit G f :=
{ to_fun := quotient.mk ∘ sigma.mk i,
  inj' := λ x y h, begin
    simp only [quotient.eq] at h,
    obtain ⟨j, h1, h2, h3⟩ := h,
    exact (f i j h1).injective h3,
  end }

variables {L ι G f}

@[simp] lemma of_apply {i : ι} {x : G i} : of L ι G f i x = ⟦⟨i, x⟩⟧ := rfl

@[simp] lemma of_f {i j : ι} {hij : i ≤ j} {x : G i} :
  (of L ι G f j (f i j hij x)) = of L ι G f i x :=
begin
  simp only [of_apply, quotient.eq],
  refine setoid.symm ⟨j, hij, refl j, _⟩,
  simp only [directed_system.map_self],
end

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of (z : direct_limit G f) :
  ∃ i x, of L ι G f i x = z :=
⟨z.out.1, z.out.2, by simp⟩

@[elab_as_eliminator]
protected theorem induction_on {C : direct_limit G f → Prop}
  (z : direct_limit G f)
  (ih : ∀ i x, C (of L ι G f i x)) : C z :=
let ⟨i, x, h⟩ := exists_of z in h ▸ ih i x

variables {P : Type u₁} [L.Structure P] (g : Π i, G i ↪[L] P)
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
include Hg

variables (L ι G f)
/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : direct_limit G f ↪[L] P :=
{ to_fun := quotient.lift (λ (x : Σ i, G i), (g x.1) x.2) (λ x y xy, begin
    simp only,
    obtain ⟨i, hx, hy⟩ := directed_of (≤) x.1 y.1,
    rw [← Hg x.1 i hx, ← Hg y.1 i hy],
    exact congr_arg _ ((equiv_iff _ _ _ _).1 xy),
  end),
  inj' := λ x y xy, begin
    rw [← quotient.out_eq x, ← quotient.out_eq y, quotient.lift_mk, quotient.lift_mk] at xy,
    obtain ⟨i, hx, hy⟩ := directed_of (≤) x.out.1 y.out.1,
    rw [← Hg x.out.1 i hx, ← Hg y.out.1 i hy] at xy,
    rw [← quotient.out_eq x, ← quotient.out_eq y, quotient.eq, equiv_iff G f hx hy],
    exact (g i).injective xy,
  end,
  map_fun' := λ n F x, begin
    obtain ⟨i, y, rfl⟩ := exists_quotient_mk_sigma_mk_eq G f x,
    rw [fun_map_quotient_mk_sigma_mk, ← function.comp.assoc, quotient.lift_comp_mk],
    simp only [quotient.lift_mk, embedding.map_fun],
  end,
  map_rel' := λ n R x, begin
    obtain ⟨i, y, rfl⟩ := exists_quotient_mk_sigma_mk_eq G f x,
    rw [rel_map_quotient_mk_sigma_mk G f, ← (g i).map_rel R y,
      ← function.comp.assoc, quotient.lift_comp_mk],
  end }

variables {L ι G f}

omit Hg

@[simp] lemma lift_quotient_mk_sigma_mk {i} (x : G i) :
  lift L ι G f g Hg (⟦⟨i, x⟩⟧) = (g i) x :=
begin
  change (lift L ι G f g Hg).to_fun (⟦⟨i, x⟩⟧) = _,
  simp only [lift, quotient.lift_mk],
end

lemma lift_of {i} (x : G i) : lift L ι G f g Hg (of L ι G f i x) = g i x :=
by simp

theorem lift_unique (F : direct_limit G f ↪[L] P) (x) :
  F x = lift L ι G f (λ i, F.comp $ of L ι G f i)
    (λ i j hij x, by rw [F.comp_apply, F.comp_apply, of_f]) x :=
direct_limit.induction_on x $ λ i x, by rw lift_of; refl

/-- The direct limit of countably many countably generated structures is countably generated. -/
theorem cg {ι : Type*} [encodable ι] [preorder ι] [is_directed ι (≤)] [nonempty ι]
  {G : ι → Type w} [Π i, L.Structure (G i)]
  (f : Π i j, i ≤ j → G i ↪[L] G j) (h : ∀ i, Structure.cg L (G i))
  [directed_system G (λ i j h, f i j h)] :
  Structure.cg L (direct_limit G f) :=
begin
  refine ⟨⟨⋃ i, direct_limit.of L ι G f i '' (classical.some (h i).out), _, _⟩⟩,
  { exact set.countable_Union (λ i, set.countable.image (classical.some_spec (h i).out).1 _) },
  { rw [eq_top_iff, substructure.closure_Union],
    simp_rw [← embedding.coe_to_hom, substructure.closure_image],
    rw le_supr_iff,
    intros S hS x hx,
    let out := @quotient.out _ (direct_limit.setoid G f),
    refine hS (out x).1 ⟨(out x).2, _, _⟩,
    { rw [(classical.some_spec (h (out x).1).out).2],
      simp only [substructure.coe_top] },
    { simp only [embedding.coe_to_hom, direct_limit.of_apply, sigma.eta, quotient.out_eq] } }
end

instance cg' {ι : Type*} [encodable ι] [preorder ι] [is_directed ι (≤)] [nonempty ι]
  {G : ι → Type w} [Π i, L.Structure (G i)]
  (f : Π i j, i ≤ j → G i ↪[L] G j) [h : ∀ i, Structure.cg L (G i)]
  [directed_system G (λ i j h, f i j h)] :
  Structure.cg L (direct_limit G f) :=
cg f h

end direct_limit

end language
end first_order
