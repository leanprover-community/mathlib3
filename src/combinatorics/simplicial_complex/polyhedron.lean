import combinatorics.simplicial_complex.exposed
import combinatorics.simplicial_complex.convex_join

open set
open_locale classical

variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {X Y : finset E} {C : set E}

/-- A polytope is an intersection of finitely many halfspaces. -/
@[ext] structure polytope (E : Type*) [normed_group E] [normed_space ℝ E] :=
(carrier : set E)
(hcarrier : ∃ Hrepr : finset ((E →L[ℝ] ℝ) × ℝ), carrier = {x | ∀ l ∈ Hrepr, (l.1 x : ℝ) ≤ l.2})

instance : has_coe (polytope E) (set E) := { coe := λ P, P.carrier }

instance : has_emptyc (polytope E) := { emptyc := { carrier := ∅,
  hcarrier := begin
    refine ⟨{(0, -1)}, (subset_empty_iff.1 (λ x hx, _)).symm⟩,
    have : (0 : ℝ) ≤ -1 := hx (0, -1) (finset.mem_singleton_self _),
    linarith,
  end } }

namespace polytope

noncomputable def Hrepr (P : polytope E) : finset ((E →L[ℝ] ℝ) × ℝ) :=
classical.some P.hcarrier

lemma eq_Hrepr (P : polytope E) : (P : set E) = {x | ∀ l ∈ P.Hrepr, (l.1 x : ℝ) ≤ l.2} :=
classical.some_spec P.hcarrier

lemma convex (P : polytope E) : convex (P : set E) := sorry

def faces (P : polytope E) : set (polytope E) :=
{Q | (Q : set E).nonempty → ∃ l : (E →L[ℝ] ℝ) × ℝ, Q.Hrepr = insert l P.Hrepr ∧
  (Q : set E) = {x ∈ P | ∀ y ∈ (P : set E), l.1 y ≤ l.1 x}}

end polytope

lemma is_exposed_of_mem_faces {P Q : polytope E} (hQ : Q ∈ P.faces) : is_exposed (P : set E) Q :=
begin
  intro hQnemp,
  obtain ⟨l, hl, hQcarr⟩ := hQ hQnemp,
  exact ⟨l.1, hQcarr⟩,
end

instance complete_lattice_polytopes : complete_lattice (polytope E) :=
{ le := (λ x y, (x : set E) ⊆ y),
  le_refl := λ x, subset.refl x,
  le_trans := λ x y z, subset.trans,
  le_antisymm := λ x y hxy hyx, sorry, --hxy.antisymm hyx,

  sup := λ x y, { carrier := convex_join x y,
    hcarrier := sorry },
  le_sup_left := λ x y, subset_convex_join_left x y,
  le_sup_right := λ x y, subset_convex_join_right x y,
  sup_le := λ x y z hxz hyz, convex_join_min hxz hyz z.convex,

  inf := λ x y, { carrier := x ∩ y,
  hcarrier := begin
    use x.Hrepr ∪ y.Hrepr,
  end },
  inf_le_left := _,
  inf_le_right := _,
  le_inf := _,

  top := ⊤,
  le_top := _,
  bot := _,
  bot_le := _,
  Sup := _,
  le_Sup := _,
  Sup_le := _,
  Inf := _,
  Inf_le := _,
  le_Inf := _ }

/-- A polyhedron is the convex hull of a finite number of points. -/
@[ext] structure polyhedron (E : Type*) [normed_group E] [normed_space ℝ E] :=
(verts : finset E)

instance : has_coe (polyhedron E) (set E) := { coe := λ P, convex_hull P.verts }

instance complete_lattice_polyhedrons : complete_lattice (polyhedron E) :=
{ le := λ x y, (x : set E) ⊆ y,
  le_refl := λ x, subset.refl x,
  le_trans := λ x y z, subset.trans,
  le_antisymm := λ x y hxy hyx, sorry, --hxy.antisymm hyx,

  sup := λ x y, { verts := x.verts ∪ y.verts },
  le_sup_left := _,
  le_sup_right := _,
  sup_le := _,

  inf := _,
  inf_le_left := _,
  inf_le_right := _,
  le_inf := _,

  top := ⊤,
  le_top := _,
  bot := _,
  bot_le := _,
  Sup := _,
  le_Sup := _,
  Sup_le := _,
  Inf := _,
  Inf_le := _,
  le_Inf := _ }
