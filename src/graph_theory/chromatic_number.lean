import graph_theory.basic
import data.fin

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

structure chromatic_number (G : graph V) (n : ℕ) : Prop :=
(col_exists : nonempty (nat_colouring n G))
(min        : ∀ {k}, nat_colouring k G → n ≤ k)

lemma chromatic_number.is_loopless {n} (h : chromatic_number G n) :
  G.is_loopless :=
begin
  rcases h.col_exists with ⟨c⟩,
  exact c.is_loopless
end

lemma chromatic_number_le_card_of_colouring {W : Type*} [fintype W] {n m}
  (c : colouring W G) (hn : chromatic_number G n) (hm : m = fintype.card W) :
  n ≤ m :=
begin
  obtain ⟨k, ⟨f⟩⟩ : ∃ k, nonempty (W ≃ fin k) :=
    fintype.exists_equiv_fin W,
  obtain rfl : m = k,
  { rw [hm, fintype.card_congr f, fintype.card_fin] },
  apply hn.min,
  exact c.extend f f.injective
end

lemma chromatic_number_le_card [fintype V] {n m}
  (hn : chromatic_number G n) (hm : m = fintype.card V) :
  n ≤ m :=
chromatic_number_le_card_of_colouring (colouring_id G hn.is_loopless) hn hm

section
variables {n₁ n₂ n : ℕ}
variables (h₁ : chromatic_number G₁ n₁)
variables (h₂ : chromatic_number G₂ n₂)
variables (h : chromatic_number (G₁.prod G₂) n)

include h₁ h₂ h

lemma chromatic_number_prod_le_min : n ≤ min n₁ n₂ :=
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
