import graph_theory.basic
import data.equiv.fin
import data.fintype.fiber
import algebra.big_operators

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

structure is_chromatic_number (G : graph V) (n : ℕ) : Prop :=
(col_exists : nonempty (nat_colouring n G))
(min        : ∀ {k}, nat_colouring k G → n ≤ k)

lemma is_chromatic_number.elim {n₁ n₂ : ℕ}
  (h₁ : is_chromatic_number G n₁) (h₂ : is_chromatic_number G n₂) : n₁ = n₂ :=
begin
  obtain ⟨c₁⟩ := h₁.col_exists,
  obtain ⟨c₂⟩ := h₂.col_exists,
  exact le_antisymm (h₁.min c₂) (h₂.min c₁)
end

lemma is_chromatic_number.is_loopless {n} (h : is_chromatic_number G n) :
  G.is_loopless :=
begin
  rcases h.col_exists with ⟨c⟩,
  exact c.is_loopless
end

lemma is_chromatic_number_le_card_of_colouring {W : Type*} [fintype W] {n}
  (c : colouring W G) (hn : is_chromatic_number G n) :
  n ≤ fintype.card W :=
begin
  obtain ⟨k, ⟨f⟩⟩ : ∃ k, nonempty (W ≃ fin k) :=
    fintype.exists_equiv_fin W,
  obtain rfl : fintype.card W = k,
  { rw [fintype.card_congr f, fintype.card_fin] },
  apply hn.min,
  exact c.extend f f.injective
end

lemma is_chromatic_number_le_card [fintype V] {n}
  (hn : is_chromatic_number G n) :
  n ≤ fintype.card V :=
is_chromatic_number_le_card_of_colouring (colouring_id G hn.is_loopless) hn

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

lemma chromatic_number_is_chromatic_number [fintype V] (G : graph V) (hG : G.is_loopless) :
  is_chromatic_number G (chromatic_number G hG) :=
⟨⟨minimal_colouring G hG⟩, λ k c, nat.find_min' (chromatic_number_exists G hG) ⟨c⟩⟩

lemma chromatic_number.pos [nonempty V] [fintype V] (G : graph V) (hG : G.is_loopless) :
  0 < chromatic_number G hG :=
begin
  rw [← fintype.card_fin (chromatic_number G hG), fintype.card_pos_iff],
  apply nonempty.map (minimal_colouring G hG),
  apply_assumption
end

end

section
variables {n₁ n₂ n : ℕ}
variables (h₁ : is_chromatic_number G₁ n₁)
variables (h₂ : is_chromatic_number G₂ n₂)
variables (h : is_chromatic_number (G₁.prod G₂) n)

include h₁ h₂ h

lemma is_chromatic_number_prod_le_min : n ≤ min n₁ n₂ :=
begin
  obtain ⟨c₁⟩ := h₁.col_exists,
  obtain ⟨c₂⟩ := h₂.col_exists,
  rw le_min_iff,
  split,
  { exact h.min (c₁.comp (prod.fst G₁ G₂)) },
  { exact h.min (c₂.comp (prod.snd G₁ G₂)) }
end

end

end graph
