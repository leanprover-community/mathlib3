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

structure is_chromatic_number (G : graph V) (n : ℕ) : Prop :=
(col_exists : nonempty (nat_colouring n G))
(min        : ∀ {k}, nat_colouring k G → n ≤ k)

lemma is_chromatic_number.is_loopless {n} (h : is_chromatic_number G n) :
  G.is_loopless :=
begin
  rcases h.col_exists with ⟨c⟩,
  exact c.is_loopless
end

lemma is_chromatic_number_le_card_of_colouring {W : Type*} [fintype W] {n m}
  (c : colouring W G) (hn : is_chromatic_number G n) (hm : m = fintype.card W) :
  n ≤ m :=
begin
  obtain ⟨k, ⟨f⟩⟩ : ∃ k, nonempty (W ≃ fin k) :=
    fintype.exists_equiv_fin W,
  obtain rfl : m = k,
  { rw [hm, fintype.card_congr f, fintype.card_fin] },
  apply hn.min,
  exact c.extend f f.injective
end

lemma is_chromatic_number_le_card [fintype V] {n m}
  (hn : is_chromatic_number G n) (hm : m = fintype.card V) :
  n ≤ m :=
is_chromatic_number_le_card_of_colouring (colouring_id G hn.is_loopless) hn hm

section
open_locale classical

lemma chromatic_number_exists [fintype V] (G : graph V) (hG : G.is_loopless) :
  ∃ n, nonempty (nat_colouring n G) :=
begin
  obtain ⟨f⟩ := fintype.equiv_fin V,
  let c := colouring_id G hG,
  exact ⟨fintype.card V, ⟨c.extend f f.injective⟩⟩
end

noncomputable def chromatic_number [fintype V] (G : graph V) (hG : G.is_loopless) : ℕ :=
nat.find (chromatic_number_exists G hG)

lemma chromatic_number_is_chromatic_number [fintype V] (G : graph V) (hG : G.is_loopless) :
  is_chromatic_number G (chromatic_number G hG) :=
begin
  refine ⟨nat.find_spec (chromatic_number_exists G hG), _⟩,
  intros k c,
  apply nat.find_min' (chromatic_number_exists G hG) ⟨c⟩,
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

def Kneser.map {V₁ : Type u₁} {V₂ : Type u₂} [decidable_eq V₁] [decidable_eq V₂]
  (f : V₁ ↪ V₂) (k : ℕ) :
  hom (Kneser V₁ k) (Kneser V₂ k) :=
{ to_fun    := λ s, ⟨finset.map f s, by { rw finset.card_map f, exact s.2 }⟩,
  map_edge' := assume s t e, show disjoint (finset.map f s) (finset.map f t),
    by rwa [finset.map_disjoint] }

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

structure is_multichromatic_number (G : graph V) (n k : ℕ) : Prop :=
(col_exists : nonempty (nat_multicolouring n k G))
(min        : ∀ {m}, nat_multicolouring m k G → n ≤ m)

section
open_locale classical

variable [fintype V]

lemma multichromatic_number_exists (G : graph V) (hG : G.is_loopless) (k : ℕ) :
  ∃ n, nonempty (nat_multicolouring n k G) :=
begin
  suffices c : multicolouring (V × (fin k)) k G,
  { obtain ⟨f⟩ := fintype.equiv_fin (V × (fin k)),
    exact ⟨_, ⟨c.extend ⟨f, f.injective⟩⟩⟩ },
  let f : V → finset (V × (fin k)) := λ v, finset.univ.filter $ λ p, p.1 = v,
  apply multicolouring.multiply (colouring_id G hG).to_multi k k (one_mul k) f,
  { assume v,
    suffices : finset.card (f v) = finset.card (finset.univ : finset (fin k)),
    { simpa },
    refine finset.card_congr (λ (p : V × fin k) hp, p.2) _ _ _,
    { intros, exact finset.mem_univ _ },
    { intros p q hp hq H, ext1; [skip, assumption],
      replace hp := (finset.mem_filter.mp hp).2,
      replace hq := (finset.mem_filter.mp hq).2,
      rw [hp, hq] },
    { intros i hi,
      refine ⟨(v, i), finset.mem_filter.mpr _, rfl⟩,
      exact ⟨finset.mem_univ _, rfl⟩ } },
  { intros v₁ v₂ h,
    rw finset.disjoint_iff_ne,
    rintros p hp q hq rfl, apply h,
    replace hp := (finset.mem_filter.mp hp).2,
    replace hq := (finset.mem_filter.mp hq).2,
    rw [← hp, ← hq] }
end

noncomputable def multichromatic_number (G : graph V) (hG : G.is_loopless) (k : ℕ) : ℕ :=
nat.find (multichromatic_number_exists G hG k)

lemma multichromatic_number_is_multichromatic_number (G : graph V) (hG : G.is_loopless) (k : ℕ) :
  is_multichromatic_number G (multichromatic_number G hG k) k :=
begin
  refine ⟨nat.find_spec (multichromatic_number_exists G hG k), _⟩,
  intros m c,
  apply nat.find_min' (multichromatic_number_exists G hG k) ⟨c⟩,
end

end


end graph
