import algebra.big_operators.order
import data.equiv.fin
import data.fintype.fiber
import graph_theory.basic
import .to_mathlib

/-!
# The chromatic number of a graph
-/

universe variables v v₁ v₂ v₃ u u₁ u₂ u₃

namespace graph

variables {V : Type u} {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃} {W : Type*}
variables {G : graph V} {G₁ : graph V₁} {G₂ : graph V₂} {G₃ : graph V₃}

open_locale graph_theory

abbreviation colouring (W : Type*) (G : graph V) := hom G (complete W)

abbreviation nat_colouring (n : ℕ) (G : graph V) := colouring (fin n) G

def colouring_id (G : graph V) (h : G.is_loopless) : colouring V G :=
{ to_fun    := id,
  map_edge' := assume x y e, show x ≠ y, from ne_of_edge h e }

lemma colouring.is_loopless (c : colouring W G) :
  G.is_loopless :=
assume x e, c.map_edge e rfl

def colouring.extend {W₁ : Type u₁} {W₂ : Type u₂}
  (c : colouring W₁ G) (f : W₁ → W₂) (hf : function.injective f) :
  colouring W₂ G :=
{ to_fun    := f ∘ c,
  map_edge' := assume x y e, hf.ne $ c.map_edge e }

def universal_colouring (W : Type*) (G : graph V) :
  colouring W ((G.ihom (complete W)).prod G) :=
hom.uncurry $ hom.id _

structure chromatic_number_at_least (G : graph V) (n : ℕ) : Prop :=
(col_exists : nonempty (nat_colouring n G))

structure has_chromatic_number (G : graph V) (n : ℕ) extends chromatic_number_at_least G n :=
(min        : ∀ {k}, nat_colouring k G → n ≤ k)

lemma has_chromatic_number.elim {n₁ n₂ : ℕ}
  (h₁ : has_chromatic_number G n₁) (h₂ : has_chromatic_number G n₂) : n₁ = n₂ :=
begin
  obtain ⟨c₁⟩ := h₁.col_exists,
  obtain ⟨c₂⟩ := h₂.col_exists,
  exact le_antisymm (h₁.min c₂) (h₂.min c₁)
end

lemma has_chromatic_number.is_loopless {n} (h : has_chromatic_number G n) :
  G.is_loopless :=
begin
  rcases h.col_exists with ⟨c⟩,
  exact c.is_loopless
end

lemma has_chromatic_number_le_card_of_colouring {W : Type*} [fintype W] {n}
  (c : colouring W G) (hn : has_chromatic_number G n) :
  n ≤ fintype.card W :=
begin
  obtain ⟨k, ⟨f⟩⟩ : ∃ k, nonempty (W ≃ fin k) :=
    fintype.exists_equiv_fin W,
  obtain rfl : fintype.card W = k,
  { rw [fintype.card_congr f, fintype.card_fin] },
  apply hn.min,
  exact c.extend f f.injective
end

lemma has_chromatic_number_le_card [fintype V] {n}
  (hn : has_chromatic_number G n) :
  n ≤ fintype.card V :=
has_chromatic_number_le_card_of_colouring (colouring_id G hn.is_loopless) hn

section
open_locale classical

def trunc_nat_colouring [fintype V] [decidable_eq V] (G : graph V) (hG : G.is_loopless) :
  trunc (nat_colouring (fintype.card V) G) :=
(fintype.equiv_fin V).map (λ f, (colouring_id G hG).extend f f.injective)

lemma chromatic_number_exists [fintype V] (G : graph V) (hG : G.is_loopless) :
  ∃ n, nonempty (nat_colouring n G) :=
⟨fintype.card V, nonempty_of_trunc (trunc_nat_colouring G hG)⟩

noncomputable def chromatic_number [fintype V] (G : graph V) (hG : G.is_loopless) : ℕ :=
nat.find (chromatic_number_exists G hG)

noncomputable def minimal_colouring [fintype V] (G : graph V) (hG : G.is_loopless) :
  nat_colouring (chromatic_number G hG) G :=
nonempty.choose (nat.find_spec (chromatic_number_exists G hG))

noncomputable lemma has_chromatic_number_chromatic_number [fintype V] (G : graph V) (hG : G.is_loopless) :
  has_chromatic_number G (chromatic_number G hG) :=
{ col_exists := ⟨minimal_colouring G hG⟩,
  min        := λ k c, nat.find_min' (chromatic_number_exists G hG) ⟨c⟩ }

lemma has_chromatic_number.pos [nonempty V] {n : ℕ} (h : G.has_chromatic_number n) :
  0 < n :=
begin
  obtain ⟨c⟩ := h.col_exists,
  rw [← fintype.card_fin n, fintype.card_pos_iff],
  apply nonempty.map c,
  apply_assumption
end

lemma chromatic_number.pos [nonempty V] [fintype V] (G : graph V) (hG : G.is_loopless) :
  0 < chromatic_number G hG :=
(G.has_chromatic_number_chromatic_number hG).pos

end

section
variables {n₁ n₂ n : ℕ}
variables (h₁ : has_chromatic_number G₁ n₁)
variables (h₂ : has_chromatic_number G₂ n₂)
variables (h : has_chromatic_number (G₁.prod G₂) n)

include h₁ h₂ h

lemma has_chromatic_number_prod_le_min : n ≤ min n₁ n₂ :=
begin
  obtain ⟨c₁⟩ := h₁.col_exists,
  obtain ⟨c₂⟩ := h₂.col_exists,
  rw le_min_iff,
  split,
  { exact h.min (c₁.comp (prod.fst G₁ G₂)) },
  { exact h.min (c₂.comp (prod.snd G₁ G₂)) }
end

end

def is_independent_set (G : graph V) (s : finset V) : Prop :=
∀ (x ∈ s) (y ∈ s), ¬ (x ~[G] y)

structure independence_number_at_most (G : graph V) (n : ℕ) : Prop :=
(max : ∀ s, G.is_independent_set s → s.card ≤ n)

structure has_independence_number (G : graph V) (n : ℕ)
  extends independence_number_at_most G n : Prop :=
(set_exists : ∃ s, G.is_independent_set s ∧ s.card = n)

section
open_locale classical

noncomputable def independence_number [fintype V] (G : graph V) : ℕ :=
nat.find_greatest {n | ∃ s, G.is_independent_set s ∧ s.card = n} (fintype.card V)

lemma has_independence_number_indepencende_number [fintype V] (G : graph V) :
  G.has_independence_number (independence_number G) :=
{ max        :=
  begin
    assume s hs,
    apply (nat.find_greatest_spec_and_le _ _).2,
    { rw ← finset.card_univ,
      exact finset.card_le_of_subset s.subset_univ, },
    { use [s, hs], }
  end,
  set_exists :=
  begin
    suffices : ∃ n, n ≤ fintype.card V ∧ (∃ s, G.is_independent_set s ∧ s.card = n),
    { exact nat.find_greatest_spec this, },
    refine ⟨0, nat.zero_le _, ∅, _, finset.card_empty⟩,
    assume x hx, cases hx,
  end }

noncomputable def colouring.class [fintype V] (c : colouring W G) (w : W) : finset V :=
set.to_finset {v | c v = w}

@[simp]
lemma colouring.mem_class_iff [fintype V] (c : colouring W G) (w : W) (x : V) :
  x ∈ c.class w ↔ c x = w :=
set.mem_to_finset

lemma colouring.mem_class [fintype V] (c : colouring W G) (x : V) :
  x ∈ c.class (c x) :=
(c.mem_class_iff _ _).mpr rfl

lemma colouring.class_is_independent_set [fintype V] (c : colouring W G) (w : W) :
  G.is_independent_set (c.class w) :=
begin
  assume x hx y hy e,
  apply c.map_edge e,
  rw colouring.mem_class_iff at hx hy,
  rw [hx, hy],
end

lemma colouring.class_card_le [fintype V] (c : colouring W G) (w : W) :
  (c.class w).card ≤ independence_number G :=
G.has_independence_number_indepencende_number.max _ $ c.class_is_independent_set w

lemma card_le_chromatic_number_mul_independence_number [fintype V] (G : graph V) (hG : G.is_loopless) :
  fintype.card V ≤ chromatic_number G hG * independence_number G :=
begin
  let s := finset.univ.bind (minimal_colouring G hG).class,
  transitivity s.card,
  { rw ← finset.card_univ,
    apply finset.card_le_of_subset,
    assume x hx,
    rw finset.mem_bind,
    refine ⟨_, finset.mem_univ _, colouring.mem_class _ x⟩, },
  { apply le_trans finset.card_bind_le,
    apply le_trans (finset.sum_le _ _ _),
    swap 2, { exact independence_number G },
    { apply le_of_eq, rw add_monoid.smul_eq_mul, congr' 1,
      norm_cast, rw [finset.card_univ, fintype.card_fin], },
    { apply_instance },
    { assume i hi, apply colouring.class_card_le } }
end

end

end graph
