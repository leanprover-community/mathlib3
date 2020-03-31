import graph_theory.chromatic_number
import data.zmod.basic

/-!

Important source:

Yaroslav Shitov. COUNTEREXAMPLES TO HEDETNIEMI’S CONJECTURE.
 https://arxiv.org/pdf/1905.02167.pdf

-/

universe variables v v₁ v₂ v₃ u u₁ u₂ u₃

namespace graph

variables {V : Type u} {V₁ : Type u₁} {V₂ : Type u₂} {V₃ : Type u₃} {W : Type*}
variables {G : graph V} {G₁ : graph V₁} {G₂ : graph V₂} {G₃ : graph V₃}

open_locale graph_theory

def colouring.is_suited (c : colouring W (G.ihom (complete W))) : Prop :=
∀ w : W, c (λ x, w) = w

lemma colouring.mk_suited_aux' [fintype W] (c : colouring W (G.ihom (complete W))) :
  function.bijective (λ w, c (λ x, w) : W → W) :=
begin
  rw ← fintype.injective_iff_bijective,
  assume w₁ w₂ h,
  classical,
  contrapose! h,
  apply c.map_edge,
  assume x y e,
  exact h
end

noncomputable def colouring.mk_suited_aux [fintype W] (c : colouring W (G.ihom (complete W))) :
  W ≃ W :=
equiv.of_bijective $ c.mk_suited_aux'

noncomputable def colouring.mk_suited [fintype W] (c : colouring W (G.ihom (complete W))) :
  colouring W (G.ihom (complete W)) :=
c.extend (c.mk_suited_aux).symm $ equiv.injective _

lemma colouring.mk_suited_is_suited [fintype W] (c : colouring W (G.ihom (complete W))) :
  c.mk_suited.is_suited :=
begin
  assume w,
  apply (colouring.mk_suited_aux c).injective,
  apply equiv.apply_symm_apply
end

section hedetniemi
variables {n₁ n₂ n : ℕ}
variables (h₁ : chromatic_number G₁ n₁)
variables (h₂ : chromatic_number G₂ n₂)
variables (h : chromatic_number (G₁.prod G₂) n)

include h₁ h₂ h

/-- Hedetniemi's conjecture, which has been disproven in <https://arxiv.org/pdf/1905.02167.pdf>. -/
def hedetniemi : Prop :=
n = min n₁ n₂

omit h₁ h₂ h

variables {n' : ℕ} (h' : chromatic_number (G₂.ihom (K_ n)) n')
variables {nᵤ : ℕ} (hᵤ : chromatic_number ((G₂.ihom (K_ n)).prod G₂) nᵤ)

lemma min_le_of_universal_hedetniemi (H : hedetniemi h' h₂ hᵤ) :
  min n' n₂ ≤ n :=
calc min n' n₂ = nᵤ : H.symm
           ... ≤ n  : hᵤ.min (universal_colouring _ _)

lemma hedetniemi_of_universal (H : hedetniemi h' h₂ hᵤ) :
  hedetniemi h₁ h₂ h :=
begin
  apply le_antisymm (chromatic_number_prod_le_min h₁ h₂ h),
  obtain ⟨c⟩ : nonempty (nat_colouring n (G₁.prod G₂)) := h.col_exists,
  obtain ⟨c'⟩ : nonempty (nat_colouring n' (G₂.ihom (K_ n))) := h'.col_exists,
  let f : hom G₁ (G₂.ihom (K_ n)) := (adj G₁ G₂ (K_ n)) c,
  have n₁_le_n' : n₁ ≤ n' := h₁.min (c'.comp f),
  calc min n₁ n₂ ≤ min n' n₂ : inf_le_inf_left n₂ n₁_le_n'
             ... ≤ n         : min_le_of_universal_hedetniemi _ _ _ H
end

end hedetniemi

def induced_graph (G₂ : graph V₂) (f : V₁ → V₂) : graph V₁ :=
{ edge := assume x y, f x ~[G₂] f y,
  symm := assume x y e, G₂.symm e }

def closed_neighbourhood (G : graph V) (x : V) :=
{ y // y = x ∨ (y ~[G] x) }

def closed_neighbourhood.graph (G : graph V) (x : V) : graph (closed_neighbourhood G x) :=
induced_graph G subtype.val

/-- Observation 1. -/
lemma mem_range_of_is_suited {W : Type*} (G : graph V)
  (Φ : colouring W (G.ihom (complete W))) (h : Φ.is_suited) (φ : V → W) :
  Φ φ ∈ set.range φ :=
begin
  classical, by_contradiction H,
  let E := G.ihom (complete W),
  let w : W := Φ φ,
  have hΦw : Φ (λ x, w) = w := h w,
  suffices a : (φ ~[E] (λ x, w)),
  { exfalso, apply Φ.map_edge a, exact hΦw.symm },
  assume x y e, contrapose! H,
  rw set.mem_range,
  use x,
  exact classical.not_not.1 H
end

open_locale classical

noncomputable theory

section claim2

/-- This definition appears in Claim 2 of Shitov's article. -/
def is_robust {W : Type*} (G : graph V) (x : V) (w : W) (s : set (V → W)) : Prop :=
∀ φ ∈ s, ∃ y : closed_neighbourhood G x, w = (φ : V → W) y.val

def robust_classes {W : Type*} [fintype W] (G : graph V) (v : V)
  (Φ : colouring W (G.ihom (complete W))) :
  finset W :=
finset.univ.filter $ λ w, is_robust G v w (Φ ⁻¹' {w})

def I [fintype V] [fintype W] (Φ : colouring W (G.ihom (complete W)))
  (u : V) (b : W) :
  finset (V → W) :=
finset.univ.filter $ λ φ : V → W, φ u = b ∧ Φ φ = b

lemma hI [fintype V] [fintype W]
  (Φ : colouring W (G.ihom (complete W))) (hΦ : Φ.is_suited) (φ : V → W) :
  ∃ u b, φ ∈ I Φ u b :=
begin
  obtain ⟨u, hu⟩ := mem_range_of_is_suited G Φ hΦ φ,
  use [u, Φ φ],
  simp [I, finset.mem_filter, hu]
end

def is_large [fintype V] [fintype W] {n c : ℕ} (hn : n = fintype.card V) (hc : c = fintype.card W)
  (Φ : colouring W (G.ihom (complete W))) (hΦ : Φ.is_suited) (u : V) (b : W) : Prop :=
  n^2 * c^(n-2) < (I Φ u b).card

lemma is_robust_of_is_large [fintype V] [fintype W] {n c : ℕ} (hn : n = fintype.card V) (hc : c = fintype.card W)
  (Φ : colouring W (G.ihom (complete W))) (hΦ : Φ.is_suited) (u : V) (b : W)
  (hub : is_large hn hc Φ hΦ u b) :
  is_robust G u b (Φ ⁻¹' {b}) :=
begin
  assume φ,
  change _ < _ at hub,
  contrapose! hub,
  cases hub with hφ hub,
  have key : ∀ φ' : V → W, φ' ∈ I Φ u b → ∃ u' ≠ u, φ' u' ∈ finset.univ.image φ,
  { assume φ' hφ',
    replace hφ' := (finset.mem_filter.mp hφ').2,
    rw [set.mem_preimage, set.mem_singleton_iff] at hφ,
    have tmp : ¬ (φ ~[G.ihom (complete W)] φ'),
    { assume e, apply Φ.map_edge e, rw [hφ'.2, hφ] },
    have : ∃ (x y : V), (x ~[G] y) ∧ (φ x = φ' y),
    { contrapose! tmp, intros x y, rw imp_iff_not_or, exact tmp x y },
    sorry },
  sorry
end

/-- Claim 2 of Shitov's paper. -/
theorem claim2 {W : Type*} [fintype V] [fintype W] {n c k : ℕ} (G : graph V)
  (Φ : colouring W (G.ihom (complete W))) (hΦ : Φ.is_suited)
  (hn : n = fintype.card V) (hc : c = fintype.card W) (hk : k^n ≥ n^3 * c^(n-1)) :
  ∃ v, c ≤ (robust_classes G v Φ).card + k :=
begin
  let large_classes : V → finset W :=
    λ v, finset.univ.filter $ λ b, is_large hn hc Φ hΦ v b,
  by_cases h : ∃ v, c ≤ (large_classes v).card + k,
  { cases h with v hv,
    use v,
    apply le_trans hv,
    apply add_le_add_right,
    apply finset.card_le_of_subset,
    assume b hb,
    rw finset.mem_filter at hb,
    apply finset.mem_filter.mpr,
    refine ⟨finset.mem_univ _, _⟩,
    exact is_robust_of_is_large hn hc Φ hΦ v b hb.2 },
  { sorry }
end

end claim2

def strong_prod (G₁ : graph V₁) (G₂ : graph V₂) : graph (V₁ × V₂) :=
{ edge := assume p q,
    ((p.1 ~[G₁] q.1) ∧ (p.2 ~[G₂] q.2)) ∨
    ((p.1 = q.1) ∧ (p.2 ~[G₂] q.2)) ∨
    ((p.1 ~[G₁] q.1) ∧ (p.2 = q.2)),
  symm := assume p q, by
    -- TODO: Scott, diagnose why `solve_by_elim` can't do this
    repeat {apply or.imp <|> apply and.imp <|> apply edge.symm <|> apply eq.symm } }

def prod_hom_strong (G₁ : graph V₁) (G₂ : graph V₂) :
  hom (G₁.prod G₂) (G₁.strong_prod G₂) :=
{ to_fun := id,
  map_edge' := assume x y e, or.inl e }

def cyclic (n : ℕ+) : graph (zmod n) :=
{ edge := assume x y, x = y + 1 ∨ y = x + 1,
  symm := assume x y, or.symm }

structure cycle (n : ℕ+) (G : graph V) extends hom (cyclic n) G :=
(inj : function.injective to_fun)

structure girth (G : graph V) (n : ℕ+) : Prop :=
(cyc_exists : nonempty (cycle n G))
(min        : ∀ {m}, cycle m G → n ≤ m)

/-- Claim 3 of Shitov's paper. -/
-- Currently this statement is wrong, it's not what Shitov wrote.
lemma claim3 (G : graph V) {k : ℕ+} (g : girth G k) (hk : 6 ≤ k) :
  ∃ N : ℕ, ∀ q, N < q → ∀ c, chromatic_number (G.strong_prod (K_ q)) c → 3 * q < c :=
begin
  sorry
end

def statement_of_erdos (χ g : ℕ) :=
  ∃ {V : Type} [fintype V] (G : graph V) (k : ℕ) (n : ℕ+),
  chromatic_number G k ∧ χ < k ∧
  girth G n ∧ g < n

/-- Shitov's theorem -/
theorem hedetniemi_false :
  ∃ {V : Type} [fintype V] (G : graph V) (q n' n n'' : ℕ)
     (hn' : chromatic_number (G.ihom (K_ n)) n')
    (hn : chromatic_number G n)
    (hn'' : chromatic_number ((G.ihom (K_ n)).prod G) n''),
  ¬ hedetniemi hn' hn hn'' :=
begin
  sorry
  -- apply mt (min_le_of_universal_hedetniemi _ _ _)
end

end graph
