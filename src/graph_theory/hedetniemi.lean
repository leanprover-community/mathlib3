import data.rat.floor
import data.zmod.basic
import graph_theory.frac_chromatic_number
import graph_theory.girth
import graph_theory.strong_prod

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

lemma is_loopless.prod₁ (h : G₁.is_loopless) :
  (G₁.prod G₂).is_loopless :=
assume x e, h e.1

lemma is_loopless.prod₂ (h : G₂.is_loopless) :
  (G₁.prod G₂).is_loopless :=
assume x e, h e.2

section hedetniemi
variables {n₁ n₂ n : ℕ}
variables (h₁ : has_chromatic_number G₁ n₁)
variables (h₂ : has_chromatic_number G₂ n₂)
variables (h : has_chromatic_number (G₁.prod G₂) n)

variables (G₁ G₂)

/-- Hedetniemi's conjecture, which has been disproven in <https://arxiv.org/pdf/1905.02167.pdf>. -/
def hedetniemi [fintype V₁] [fintype V₂] (h₁ : G₁.is_loopless) (h₂ : G₂.is_loopless) : Prop :=
chromatic_number (G₁.prod G₂) h₁.prod₁ = min (chromatic_number G₁ h₁) (chromatic_number G₂ h₂)

variables {G₁ G₂}

include h₁ h₂ h

def hedetniemi' : Prop :=
n = min n₁ n₂

omit h₁ h₂ h

lemma hedetniemi_iff [fintype V₁] [fintype V₂] :
  hedetniemi G₁ G₂ h₁.is_loopless h₂.is_loopless ↔ hedetniemi' h₁ h₂ h :=
begin
  have H₁ : n₁ = chromatic_number G₁ h₁.is_loopless :=
    h₁.elim (has_chromatic_number_chromatic_number G₁ h₁.is_loopless),
  have H₂ : n₂ = chromatic_number G₂ h₂.is_loopless :=
    h₂.elim (has_chromatic_number_chromatic_number G₂ h₂.is_loopless),
  have H : n = chromatic_number (G₁.prod G₂) h.is_loopless :=
    h.elim (has_chromatic_number_chromatic_number (G₁.prod G₂) h.is_loopless),
  convert iff.rfl,
  all_goals { apply has_chromatic_number_chromatic_number }
end

variables {n' : ℕ} (h' : has_chromatic_number (G₂.ihom (K_ n)) n')
variables {nᵤ : ℕ} (hᵤ : has_chromatic_number ((G₂.ihom (K_ n)).prod G₂) nᵤ)

lemma min_le_of_universal_hedetniemi (H : hedetniemi' h' h₂ hᵤ) :
  min n' n₂ ≤ n :=
calc min n' n₂ = nᵤ : H.symm
           ... ≤ n  : hᵤ.min (universal_colouring _ _)

lemma hedetniemi_of_universal (H : hedetniemi' h' h₂ hᵤ) :
  hedetniemi' h₁ h₂ h :=
begin
  apply le_antisymm (has_chromatic_number_prod_le_min h₁ h₂ h),
  obtain ⟨c⟩ : nonempty (nat_colouring n (G₁.prod G₂)) := h.col_exists,
  obtain ⟨c'⟩ : nonempty (nat_colouring n' (G₂.ihom (K_ n))) := h'.col_exists,
  let f : hom G₁ (G₂.ihom (K_ n)) := (adj G₁ G₂ (K_ n)) c,
  have n₁_le_n' : n₁ ≤ n' := h₁.min (c'.comp f),
  calc min n₁ n₂ ≤ min n' n₂ : inf_le_inf_left n₂ n₁_le_n'
             ... ≤ n         : min_le_of_universal_hedetniemi _ _ _ H
end

end hedetniemi

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

section claim2

open_locale classical

noncomputable theory

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

lemma loop_of_hom (f : hom G₁ G₂) : f ~[G₁.ihom G₂] f :=
assume x y e, f.map_edge e

lemma is_loopless.ihom (h : hom G₁ G₂ → false) :
  (G₁.ihom G₂).is_loopless :=
assume f e, h ⟨f, e⟩


/-- Claim 3 of Shitov's paper. -/
lemma claim3 (G : graph V) (g : girth_at_least G 6) :
  ∃ N : ℕ+, ∀ q, N ≤ q → ∃ (c χ : ℕ)
    (h : has_chromatic_number ((G.strong_prod (K_ q)).ihom (K_ c)) χ),
    c < χ ∧ ⌈(3.1 * q : ℚ)⌉ = c :=
begin
  sorry
end

/--
The original paper is
https://doi.org/10.4153/CJM-1959-003-9
although this consequence is not mentioned directly.
-/
theorem erdos (χ : ℚ) (g : ℕ+) :
  ∃ {V : Type} [fintype V] (G : graph V),
  frac_chromatic_number_at_least G χ ∧ girth_at_least G g :=
sorry

lemma edge_strong_prod_complete (p q : V × W) (e : p.1 ~[G] q.1) :
  p ~[G.strong_prod (complete W)] q :=
begin
  classical,
  by_cases h : p.2 = q.2,
  { right, right, exact ⟨e, h⟩ },
  { left, exact ⟨e, h⟩ }
end

-- rename this
lemma colouring.foo {n : ℕ} (c : colouring W (G.strong_prod (K_ n))) (v : V) :
  function.injective (λ i : fin n, c (v, i)) :=
begin
  assume i j h,
  contrapose! h,
  apply c.map_edge,
  right, left,
  exact ⟨rfl, h⟩
end

def multicolouring_of_strong_prod_K_colouring [decidable_eq W] {n : ℕ+} (c : colouring W (G.strong_prod (K_ n))) :
  multicolouring W n G :=
{ to_fun := λ v, finset_with_card_of_injective_fn (λ i : fin n, c (v, i)) (c.foo v),
  map_edge' :=
  begin
    assume x y e, show disjoint (finset.map _ _) (finset.map _ _),
    rw finset.disjoint_iff_ne,
    assume w₁ hw₁ w₂ hw₂,
    rw finset.mem_map at hw₁ hw₂,
    rcases hw₁ with ⟨i, hi, rfl⟩,
    rcases hw₂ with ⟨j, hj, rfl⟩,
    show c (x,i) ≠ c (y,j),
    apply c.map_edge,
    exact edge_strong_prod_complete _ _ e
  end }

lemma frac_chromatic_number_mul_le_chromatic_number_strong_prod_K [fintype V] (G : graph V) (n : ℕ+) {k : ℕ} {χ : ℚ}
  (hk : has_chromatic_number (G.strong_prod (K_ n)) k) (hχ : frac_chromatic_number_at_least G χ) :
  χ * n ≤ k :=
begin
  obtain ⟨c⟩ := hk.col_exists,
  let mc := multicolouring_of_strong_prod_K_colouring c,
  have := hχ.min mc,
  rwa le_div_iff at this,
  simp,
end

lemma helpme' (α : ℚ) (q : ℕ+) : (⌈α * q⌉ : ℚ) < (α + 1) * q :=
calc (⌈α * q⌉ : ℚ) < α * q + 1 : ceil_lt_add_one _
               ... ≤ α * q + q : by { apply add_le_add_left, simp, sorry } -- how is that hard?
               ... = (α + 1) * q : by ring


lemma coe_monotone (a b : ℤ) (h : (a : ℚ) < (b : ℚ)) : a < b := by exact_mod_cast h

example (n : ℕ) : 0 ≤ (n : ℚ) := by exact nat.cast_nonneg n

/-- Shitov's theorem -/
theorem hedetniemi_false :
  ∃ {V₁ V₂ : Type} [fintype V₁] [fintype V₂]
    (G₁ : graph V₁) (G₂ : graph V₂) (h₁ : G₁.is_loopless) (h₂ : G₂.is_loopless),
  by exactI (¬ hedetniemi G₁ G₂ h₁ h₂) :=
begin
  classical,
  rcases erdos 4.1 6 with ⟨V, _inst, G, hχ, hg⟩,
  resetI,
  have hG : G.is_loopless := hg.is_loopless (by norm_num),
  rcases claim3 G hg with ⟨q, hq⟩,
  specialize hq q (le_refl q),
  rcases hq with ⟨c, χ', hχ', hcχ', hqc⟩,
  have hGKq : (G.strong_prod (K_ q)).is_loopless :=
    hG.strong_prod (complete_is_loopless _),
  refine ⟨_, _, infer_instance, infer_instance,
    (G.strong_prod (K_ q)).ihom (K_ c), G.strong_prod (K_ q),
    hχ'.is_loopless, hGKq, _⟩,
  apply ne_of_lt,
  refine lt_of_le_of_lt (show _ ≤ c, from _) _,
  { let uc := universal_colouring (fin c) (G.strong_prod (K_ q)),
    exact (has_chromatic_number_chromatic_number _ _).min uc },
  { rw lt_min_iff,
    split,
    { rwa (has_chromatic_number_chromatic_number _ _).elim hχ' },
    { rw [← int.coe_nat_lt, ← hqc],
      have t₂ := frac_chromatic_number_mul_le_chromatic_number_strong_prod_K G q
        (has_chromatic_number_chromatic_number _ _) hχ,
      apply coe_monotone,
      apply lt_of_lt_of_le,
      apply helpme' _ _,
      norm_num,
      exact t₂,
      } }
end

end graph
