import combinatorics.simplicial_complex.exposed
import combinatorics.simplicial_complex.convex_join

open set
open_locale classical

variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {X Y : finset E} {C : set E}

/-! ### Polyhedrons -/

/-- A polyhedron is an intersection of finitely many halfspaces. -/
structure polyhedron (E : Type*) [normed_group E] [normed_space ℝ E] :=
(carrier : set E)
(hcarrier : ∃ Hrepr : finset ((E →L[ℝ] ℝ) × ℝ), carrier = {x | ∀ l ∈ Hrepr, (l.1 x : ℝ) ≤ l.2})

namespace polyhedron

instance : has_coe (polyhedron E) (set E) := { coe := λ P, P.carrier }

@[ext] protected lemma ext {P Q : polyhedron E} (h : (P : set E) = Q) : P = Q :=
begin
  sorry
end

noncomputable def Hrepr (P : polyhedron E) : finset ((E →L[ℝ] ℝ) × ℝ) :=
classical.some P.hcarrier

lemma eq_Hrepr (P : polyhedron E) : (P : set E) = {x | ∀ l ∈ P.Hrepr, (l.1 x : ℝ) ≤ l.2} :=
classical.some_spec P.hcarrier

lemma convex (P : polyhedron E) : convex (P : set E) := sorry

def faces (P : polyhedron E) : set (polyhedron E) :=
{Q | (Q : set E).nonempty → ∃ l : (E →L[ℝ] ℝ) × ℝ, Q.Hrepr = insert l P.Hrepr ∧
  (Q : set E) = {x ∈ P | ∀ y ∈ (P : set E), l.1 y ≤ l.1 x}}

lemma faces_finite {P : polyhedron E} : finite P.faces := sorry

protected noncomputable def std_simplex (ι : Type*) [fintype ι] : polyhedron (ι → ℝ) :=
{ carrier := std_simplex ι,
  hcarrier := begin
    sorry
  end }

end polyhedron

lemma is_exposed_of_mem_faces {P Q : polyhedron E} (hQ : Q ∈ P.faces) : is_exposed (P : set E) Q :=
begin
  intro hQnemp,
  obtain ⟨l, hl, hQcarr⟩ := hQ hQnemp,
  exact ⟨l.1, hQcarr⟩,
end

/---/
instance lattice_polyhedrons : semilattice_inf_top (polyhedron E) :=
{ le := (λ X Y, (X : set E) ⊆ Y),
  le_refl := λ X, subset.refl X,
  le_trans := λ X Y Z, subset.trans,
  le_antisymm := λ X Y hXY hYX, polyhedron.ext (subset.antisymm (hXY : _ ⊆ _) (hYX : _ ⊆ _)),

  inf := λ X Y, { carrier := X ∩ Y,
  hcarrier := begin
    use X.Hrepr ∪ Y.Hrepr,
    rw [X.eq_Hrepr, Y.eq_Hrepr],
    apply subset.antisymm,
    { rintro x ⟨hxX, hxY⟩ l hl,
      cases finset.mem_union.1 hl,
      { exact hxX l h },
      exact hxY l h },
    rintro x hx,
    exact ⟨λ l hl, hx l (finset.mem_union_left _ hl), λ l hl, hx l (finset.mem_union_right _ hl)⟩,
  end },
  inf_le_left := λ X Y, inter_subset_left X Y,
  inf_le_right := λ X Y, inter_subset_right X Y,
  le_inf := λ X Y Z, subset_inter,

  /-bot := { carrier := ∅,
    hcarrier := begin
      refine ⟨{(0, -1)}, (subset_empty_iff.1 (λ x hx, _)).symm⟩,
      have : (0 : ℝ) ≤ -1 := hx (0, -1) (finset.mem_singleton_self _),
      linarith,
    end },
  bot_le := λ X, empty_subset X,-/

  top := { carrier := univ,
    hcarrier := begin
      refine ⟨∅, (eq_univ_of_forall (λ x, _)).symm⟩,
      rintro l hl,
      exfalso,
      exact hl,
    end },
  le_top := λ X, subset_univ X }

lemma faces_mono {P Q : polyhedron E} (hPQ : P ≤ Q) : P.faces ⊆ Q.faces := sorry

/-! ### Polytopes -/

/-- A polytope is the convex hull of a finite number of points. -/
structure polytope (E : Type*) [normed_group E] [normed_space ℝ E] :=
(carrier : set E)
(hcarrier : ∃ Vrepr : finset E, carrier = convex_hull Vrepr)

namespace polytope

instance : has_coe (polytope E) (set E) := { coe := λ P, P.carrier }

instance : has_emptyc (polytope E) :=
{ emptyc := { carrier := ∅, hcarrier := ⟨∅, convex_hull_empty.symm⟩ } }

@[ext] protected lemma ext {P Q : polytope E} (h : (P : set E) = Q) : P = Q :=
begin
  sorry
end

noncomputable def Vrepr (P : polytope E) : finset E :=
classical.some P.hcarrier

lemma eq_convex_hull_Vrepr (P : polytope E) : (P : set E) = convex_hull P.Vrepr :=
classical.some_spec P.hcarrier

lemma convex (P : polytope E) : convex (P : set E) :=
begin
  rw P.eq_convex_hull_Vrepr,
  exact convex_convex_hull _,
end

instance lattice_polytopes : lattice (polytope E) :=
{ le := λ X Y, (X : set E) ⊆ Y,
  le_refl := λ X, subset.refl X,
  le_trans := λ X Y Z, subset.trans,
  le_antisymm := λ X Y hXY hYX, polytope.ext (subset.antisymm (hXY : _ ⊆ _) (hYX : _ ⊆ _)),

  sup := λ X Y, { carrier := convex_join X Y,
    hcarrier := begin
      use X.Vrepr ∪ Y.Vrepr,
      rw [X.eq_convex_hull_Vrepr, Y.eq_convex_hull_Vrepr, ←convex_hull_union],
      norm_cast,
    end },
  le_sup_left := λ X Y, subset_convex_join_left X Y,
  le_sup_right := λ X Y, subset_convex_join_right X Y,
  sup_le := λ X Y Z hXZ hYZ, convex_join_min hXZ hYZ Z.convex,

  inf := λ X Y, { carrier := X ∩ Y,
    hcarrier := begin
      sorry,
    end },
  inf_le_left := λ X Y, inter_subset_left X Y,
  inf_le_right := λ X Y, inter_subset_right X Y,
  le_inf := λ X Y Z, subset_inter,

  --bot := ∅,
  --bot_le := λ X, begin sorry end
  }

protected noncomputable def std_simplex (ι : Type*) [fintype ι] : polytope (ι → ℝ) :=
{ carrier := std_simplex ι,
  hcarrier := ⟨finset.image (λ (i j : ι), ite (i = j) 1 0) finset.univ,
    by rw [←convex_hull_basis_eq_std_simplex, finset.coe_image, finset.coe_univ, image_univ]⟩ }

end polytope

namespace linear_map
variables {F : Type*} [normed_group F] [normed_space ℝ F] (l : E →ₗ[ℝ] F)

def image_polytope (P : polytope E) : polytope F :=
{ carrier := l '' P,
  hcarrier :=  ⟨finset.image l P.Vrepr, by rw [P.eq_convex_hull_Vrepr, finset.coe_image,
    l.convex_hull_image]⟩ }

end linear_map


namespace polytope

protected def polyhedron (P : polytope E) : polyhedron E :=
{ carrier := P,
  hcarrier := begin
    sorry
  end }

end polytope
