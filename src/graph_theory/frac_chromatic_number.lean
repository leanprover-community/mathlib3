/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/

import graph_theory.Kneser
import graph_theory.chromatic_number

/-!
# Fractional chromatic number of a graph
-/

universe variables v v₁ v₂ v₃ u u₁ u₂ u₃

namespace graph

variables {V : Type u} {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃} {W : Type*}
variables {G : graph V} {G₁ : graph V₁} {G₂ : graph V₂} {G₃ : graph V₃}

/-- A `multicolouring W k G` is a “k-fold colouring” of the graph `G`,
using colors from the type `W`.
In other words, an assignment of subsets of `W` of size `k` to the vertices of `G`,
in such a way that adjacent vertices are assigned disjoint sets.
These multicolourings are implemented as homomorphisms from `G` to the Kneser graph `Kneser W k`. -/
abbreviation multicolouring (W : Type*) [decidable_eq W] (k : ℕ+) (G : graph V) :=
hom G (Kneser W k)

/-- A `nat_multicolouring n k G` is a “n:k-fold colouring” of the graph `G`.
In other words, an assignment of sets of size `k` to the vertices of `G`,
in such a way that adjacent vertices are assigned disjoint sets. -/
abbreviation nat_multicolouring (n : ℕ) (k : ℕ+) (G : graph V) := multicolouring (fin n) k G

def multicolouring.extend {W₁ : Type u₁} {W₂ : Type u₂} [decidable_eq W₁] [decidable_eq W₂] {k : ℕ+}
  (c : multicolouring W₁ k G) (f : W₁ ↪ W₂) :
  multicolouring W₂ k G :=
(Kneser.map f k).comp c

@[simp]
lemma multicolouring.extend_id {W₁ : Type u₁} [decidable_eq W₁] {k : ℕ+} (c : multicolouring W₁ k G) :
  c.extend (function.embedding.refl _) = c :=
by { dsimp [multicolouring.extend], simp, }

@[simp]
lemma multicolouring.extend_trans
  {W₁ : Type u₁} {W₂ : Type u₂} {W₃ : Type u₃} [decidable_eq W₁] [decidable_eq W₂] [decidable_eq W₃]
  {k : ℕ+} (c : multicolouring W₁ k G) (f₁ : W₁ ↪ W₂) (f₂ : W₂ ↪ W₃) :
    c.extend (f₁.trans f₂) = (c.extend f₁).extend f₂:=
by { dsimp [multicolouring.extend], simp, }

def multicolouring.map_equiv
  {W₁ : Type u₁} {W₂ : Type u₂} [decidable_eq W₁] [decidable_eq W₂] {k : ℕ+} (e : W₁ ≃ W₂) :
    multicolouring W₁ k G ≃ multicolouring W₂ k G :=
{ to_fun := λ m, multicolouring.extend m e.to_embedding,
  inv_fun := λ m, multicolouring.extend m e.symm.to_embedding,
  left_inv := λ m, begin dsimp, rw ←multicolouring.extend_trans, simp, end,
  right_inv := λ m, begin dsimp, rw ←multicolouring.extend_trans, simp, end }

def complete_to_Kneser_one (W : Type*) [decidable_eq W] :
  hom (complete W) (Kneser W 1) :=
{ to_fun    := λ w, ⟨finset.singleton w, finset.card_singleton _⟩,
  map_edge' := assume x y e,
    by simpa only [finset.mem_singleton, subtype.coe_mk, finset.disjoint_singleton] using e.symm }

def colouring.to_multi [decidable_eq W] (c : colouring W G) :
  multicolouring W 1 G :=
(complete_to_Kneser_one W).comp c

def multicolouring.multiply {W' : Type*} [decidable_eq W] [decidable_eq W']
  {k : ℕ+} (c : multicolouring W k G) (m : ℕ+)
  (f : W → finset W') (hf : ∀ w, (f w).card = m) (hf' : ∀ w₁ w₂, w₁ ≠ w₂ → disjoint (f w₁) (f w₂)) :
  multicolouring W' (k * m) G :=
{ to_fun    := λ v, ⟨finset.sup (c v : finset W) f,
  begin
    rw [finset.card_sup],
    { have : finset.card (c v : finset W) = k := (c v).property,
      simp [hf, this] },
    { intros _ _ _ _ H, apply hf' _ _ H }
  end⟩,
  map_edge' := assume x y e, show disjoint (finset.sup ↑(c x) f) (finset.sup ↑(c y) f),
  begin
    rw finset.disjoint_sup_left, intros,
    rw finset.disjoint_sup_right, intros,
    apply hf',
    have : disjoint (c x : finset W) (c y) := c.map_edge e,
    rw finset.disjoint_iff_ne at this,
    solve_by_elim
  end }

def nat_multicolouring.multiply {n : ℕ} {k : ℕ+} (c : nat_multicolouring n k G) (m : ℕ+) :
  nat_multicolouring (n * m) (k * m) G :=
begin
  apply (multicolouring.map_equiv (@fin_prod_fin_equiv n m)).to_fun,
  fapply multicolouring.multiply c m,
  { exact fintype.fiber (λ p, p.1) },
  { intro a, simp, },
  { apply fintype.fibers_disjoint, }
end

def nat_colouring.multiply {n : ℕ} (c : nat_colouring n G) (m : ℕ+) :
  nat_multicolouring (n * m) m G :=
begin
  convert nat_multicolouring.multiply c.to_multi _,
  exact (one_mul m).symm,
end

structure is_multichromatic_number (G : graph V) (n : ℕ) (k : ℕ+) : Prop :=
(col_exists : nonempty (nat_multicolouring n k G))
(min        : ∀ {m}, nat_multicolouring m k G → n ≤ m)

section
open_locale classical

variable [fintype V]

lemma multichromatic_number_exists (G : graph V) (hG : G.is_loopless) (k : ℕ+) :
  ∃ n, nonempty (nat_multicolouring n k G) :=
⟨(chromatic_number G hG) * k, ⟨nat_colouring.multiply (minimal_colouring G hG) k⟩⟩

noncomputable def multichromatic_number (G : graph V) (hG : G.is_loopless) (k : ℕ+) : ℕ :=
nat.find (multichromatic_number_exists G hG k)

noncomputable def minimal_multicolouring [fintype V] (G : graph V) (hG : G.is_loopless)  (k : ℕ+) :
  nat_multicolouring (multichromatic_number G hG k) k G :=
nonempty.choose (nat.find_spec (multichromatic_number_exists G hG k))

lemma multichromatic_number_is_multichromatic_number (G : graph V) (hG : G.is_loopless) (k : ℕ+) :
  is_multichromatic_number G (multichromatic_number G hG k) k :=
begin
  refine ⟨nat.find_spec (multichromatic_number_exists G hG k), _⟩,
  intros m c,
  apply nat.find_min' (multichromatic_number_exists G hG k) ⟨c⟩,
end

end

structure frac_chromatic_number_at_least (G : graph V) (r : ℚ) : Prop :=
(min        : ∀ {n k}, nat_multicolouring n k G → r ≤ n/k)

structure is_frac_chromatic_number (G : graph V) (r : ℚ)
  extends frac_chromatic_number_at_least G r : Prop :=
(col_exists : ∃ (n : ℕ) (k : ℕ+), nonempty (nat_multicolouring n k G) ∧ r = n/k)

section
variable [fintype V]

lemma frac_chromatic_number_exists (G : graph V) (hG : G.is_loopless) :
  ∃ q, is_frac_chromatic_number G q :=
begin
  sorry
end

noncomputable def frac_chromatic_number (G : graph V) (hG : G.is_loopless) : ℚ :=
classical.some (frac_chromatic_number_exists G hG)

lemma frac_chromatic_number_is_frac_chromatic_number (G : graph V) (hG : G.is_loopless) :
  is_frac_chromatic_number G (frac_chromatic_number G hG) :=
classical.some_spec (frac_chromatic_number_exists G hG)

end

lemma frac_chromatic_number_at_least_le_has_chromatic_number
  (G : graph V) (q : ℚ) (n : ℕ)
  (hq : frac_chromatic_number_at_least G q) (hn : has_chromatic_number G n) :
  q ≤ n :=
begin
  obtain ⟨c⟩ := hn.col_exists,
  have := hq.min c.to_multi,
  simpa,
end

lemma frac_chromatic_number_le_chromatic_number [fintype V] (G : graph V) (hG : G.is_loopless) :
  frac_chromatic_number G hG ≤ chromatic_number G hG :=
frac_chromatic_number_at_least_le_has_chromatic_number G _ _
  (frac_chromatic_number_is_frac_chromatic_number G hG).to_frac_chromatic_number_at_least
  (has_chromatic_number_chromatic_number G hG)

lemma is_frac_chromatic_number.pos [nonempty V] {q : ℚ} (h : is_frac_chromatic_number G q) :
  0 < q :=
begin
  obtain ⟨n, k, ⟨c⟩, hc⟩ := h.col_exists,
  suffices hn : 0 < n,
  { rw hc, apply div_pos, assumption_mod_cast, simp, },
  unfreezeI, obtain ⟨x⟩ := ‹nonempty V›,
  obtain ⟨s, hs⟩ : {s : finset (fin n) // s.card = k} := c x,
  suffices : s.nonempty,
  { obtain ⟨i, hi⟩ : ∃ i, i ∈ s := this,
    exact lt_of_le_of_lt (zero_le _) i.is_lt },
  rw [← finset.card_pos, hs],
  simp,
end

lemma is_frac_chromatic_number.is_loopless {G : graph V} {q : ℚ}
  (hq : is_frac_chromatic_number G q) :
  G.is_loopless :=
begin
  obtain ⟨n, k, ⟨c⟩, hc⟩ := hq.col_exists,
  assume x e,
  have h := (Kneser.is_loopless_iff (fin n) k).2 (by simp),
  exact h (c.map_edge e)
end

end graph
