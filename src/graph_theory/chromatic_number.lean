import graph_theory.basic
import data.equiv.fin

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

section move_this
variables {X : Type*} {Y : Type*} [decidable_eq X] [decidable_eq Y]

lemma finset.map_disjoint (f : X ↪ Y) (s t : finset X) :
  disjoint (s.map f) (t.map f) ↔ disjoint s t :=
begin
  simp only [finset.disjoint_iff_ne, finset.mem_map,
    exists_prop, exists_imp_distrib, and_imp],
  split,
  { rintros h x hxs _ hxt rfl, exact h _ x hxs rfl _ x hxt rfl rfl },
  { rintros h _ x₁ hxs rfl _ x₂ hxt rfl,
    apply f.inj'.ne, solve_by_elim }
end

end move_this

def Kneser (V : Type u) [decidable_eq V] (k : ℕ) :
  graph { s : finset V // s.card = k } :=
{ edge := assume s t, disjoint (s : finset V) (t : finset V),
  symm := assume s t e, e.symm }

def Kneser.map [decidable_eq V₁] [decidable_eq V₂]
  (f : V₁ ↪ V₂) (k : ℕ) :
  hom (Kneser V₁ k) (Kneser V₂ k) :=
{ to_fun    := λ s, ⟨finset.map f s, by { rw finset.card_map f, exact s.2 }⟩,
  map_edge' := assume s t e, show disjoint (finset.map f s) (finset.map f t),
    by rwa [finset.map_disjoint] }

@[simp]
lemma Kneser.map_id [decidable_eq V] (k : ℕ) :
  Kneser.map (function.embedding.refl V) k = hom.id _ :=
by { ext, dsimp [Kneser.map], apply subtype.eq, simp, refl, }

@[simp]
lemma Kneser.map_trans [decidable_eq V₁] [decidable_eq V₂] [decidable_eq V₃]
  (f : V₁ ↪ V₂) (g : V₂ ↪ V₃) (k : ℕ) :
  Kneser.map (f.trans g) k = hom.comp (Kneser.map g k) (Kneser.map f k) :=
by { ext, dsimp [Kneser.map], apply subtype.eq, simp, }

lemma Kneser.is_loopless_iff (V : Type u) [decidable_eq V] (k : ℕ) :
  (Kneser V k).is_loopless ↔ 0 < k :=
begin
  split,
  { unfold is_loopless,
    contrapose!,
    rw nat.le_zero_iff,
    rintro rfl,
    refine ⟨⟨∅, finset.card_empty⟩, disjoint_bot_left⟩ },
  { rintros h ⟨s, rfl⟩ e,
    replace e : s = ∅ := disjoint_self.mp e,
    subst s,
    rw finset.card_empty at h,
    exact nat.not_lt_zero _ h }
end

/-- A `multicolouring W k G` is a “k-fold colouring” of the graph `G`,
using colors from the type `W`.
In other words, an assignment of subsets of `W` of size `k` to the vertices of `G`,
in such a way that adjacent vertices are assigned disjoint sets.
These multicolourings are implemented as homomorphisms from `G` to the Kneser graph `Kneser W k`. -/
abbreviation multicolouring (W : Type*) [decidable_eq W] (k : ℕ) (G : graph V) :=
hom G (Kneser W k)

/-- A `nat_multicolouring n k G` is a “n:k-fold colouring” of the graph `G`.
In other words, an assignment of sets of size `k` to the vertices of `G`,
in such a way that adjacent vertices are assigned disjoint sets. -/
abbreviation nat_multicolouring (n k : ℕ) (G : graph V) := multicolouring (fin n) k G

def multicolouring.extend {W₁ : Type u₁} {W₂ : Type u₂} [decidable_eq W₁] [decidable_eq W₂] {k : ℕ}
  (c : multicolouring W₁ k G) (f : W₁ ↪ W₂) :
  multicolouring W₂ k G :=
(Kneser.map f k).comp c

@[simp]
lemma multicolouring.extend_id {W₁ : Type u₁} [decidable_eq W₁] {k : ℕ} (c : multicolouring W₁ k G) :
  c.extend (function.embedding.refl _) = c :=
by { dsimp [multicolouring.extend], simp, }

@[simp]
lemma multicolouring.extend_trans {W₁ : Type u₁} {W₂ : Type u₂} {W₃ : Type u₃} [decidable_eq W₁] [decidable_eq W₂] [decidable_eq W₃] {k : ℕ}
  (c : multicolouring W₁ k G) (f₁ : W₁ ↪ W₂) (f₂ : W₂ ↪ W₃) :
  c.extend (f₁.trans f₂) = (c.extend f₁).extend f₂:=
by { dsimp [multicolouring.extend], simp, }

def multicolouring.map_equiv {W₁ : Type u₁} {W₂ : Type u₂} [decidable_eq W₁] [decidable_eq W₂] {k : ℕ} (e : W₁ ≃ W₂) :
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
  {k : ℕ} (c : multicolouring W k G) (m n : ℕ) (hn : k * m = n)
  (f : W → finset W') (hf : ∀ w, (f w).card = m) (hf' : ∀ w₁ w₂, w₁ ≠ w₂ → disjoint (f w₁) (f w₂)) :
  multicolouring W' n G :=
{ to_fun    := λ v, ⟨finset.bind (c v : finset W) f,
  begin
    rw [finset.card_bind],
    { have : finset.card (c v : finset W) = k := (c v).property,
      simp [hf, hn, this] },
    { intros _ _ _ _ H, apply hf' _ _ H }
  end⟩,
  map_edge' := assume x y e, show disjoint (finset.bind ↑(c x) f) (finset.bind ↑(c y) f),
  begin
    rw finset.disjoint_bind_left, intros,
    rw finset.disjoint_bind_right, intros,
    apply hf',
    have : disjoint (c x : finset W) (c y) := c.map_edge e,
    rw finset.disjoint_iff_ne at this,
    solve_by_elim
  end }

def nat_multicolouring.multiply {n k : ℕ} (c : nat_multicolouring n k G) (m : ℕ) :
  nat_multicolouring (n * m) (k * m) G :=
begin
  apply (multicolouring.map_equiv (@fin_prod_fin_equiv n m)).to_fun,
  fapply multicolouring.multiply c m (k * m) rfl,
  { exact fintype.fibre (λ p, p.1) },
  { intro a, simp, },
  { apply fintype.fibres_disjoint, }
end

def nat_colouring.multiply {n : ℕ} (c : nat_colouring n G) (m : ℕ) :
  nat_multicolouring (n * m) m G :=
begin
  convert nat_multicolouring.multiply c.to_multi _,
  exact (one_mul m).symm,
end

structure is_multichromatic_number (G : graph V) (n k : ℕ) : Prop :=
(col_exists : nonempty (nat_multicolouring n k G))
(min        : ∀ {m}, nat_multicolouring m k G → n ≤ m)

section
open_locale classical

variable [fintype V]

lemma multichromatic_number_exists (G : graph V) (hG : G.is_loopless) (k : ℕ) :
  ∃ n, nonempty (nat_multicolouring n k G) :=
⟨(chromatic_number G hG) * k, ⟨nat_colouring.multiply (minimal_colouring G hG) k⟩⟩

noncomputable def multichromatic_number (G : graph V) (hG : G.is_loopless) (k : ℕ) : ℕ :=
nat.find (multichromatic_number_exists G hG k)

noncomputable def minimal_multicolouring [fintype V] (G : graph V) (hG : G.is_loopless)  (k : ℕ) :
  nat_multicolouring (multichromatic_number G hG k) k G :=
nonempty.choose (nat.find_spec (multichromatic_number_exists G hG k))

lemma multichromatic_number_is_multichromatic_number (G : graph V) (hG : G.is_loopless) (k : ℕ) :
  is_multichromatic_number G (multichromatic_number G hG k) k :=
begin
  refine ⟨nat.find_spec (multichromatic_number_exists G hG k), _⟩,
  intros m c,
  apply nat.find_min' (multichromatic_number_exists G hG k) ⟨c⟩,
end

end

structure is_frac_chromatic_number (G : graph V) (r : ℚ) : Prop :=
(col_exists : ∃ (n k : ℕ), nonempty (nat_multicolouring n k G) ∧ 0 < k ∧ r = n/k)
(min        : ∀ {n k}, nat_multicolouring n k G → 0 < k → r ≤ n/k)

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

lemma is_frac_chromatic_number_le_is_chromatic_number
  (G : graph V) (q : ℚ) (n : ℕ)
  (hq : is_frac_chromatic_number G q) (hn : is_chromatic_number G n) :
  q ≤ n :=
begin
  obtain ⟨c⟩ := hn.col_exists,
  have := hq.min c.to_multi zero_lt_one,
  simpa only [nat.cast_one, div_one],
end

lemma frac_chromatic_number_le_chromatic_number [fintype V] (G : graph V) (hG : G.is_loopless) :
  frac_chromatic_number G hG ≤ chromatic_number G hG :=
is_frac_chromatic_number_le_is_chromatic_number G _ _
  (frac_chromatic_number_is_frac_chromatic_number G hG)
  (chromatic_number_is_chromatic_number G hG)

end graph
