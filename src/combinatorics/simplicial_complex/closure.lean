
import combinatorics.simplicial_complex.pure

open_locale classical affine big_operators
open set

namespace affine

variables {m n : ℕ} {E : Type*} [normed_group E] [normed_space ℝ E] {S : simplicial_complex E}
  {x : E} {X Y : finset E} {A B : set (finset E)}

/--
The closure of a set of faces is the set of their subfaces
-/
def simplicial_complex.closure (S : simplicial_complex E) (A : set (finset E)) :
  simplicial_complex E :=
simplicial_complex.of_surcomplex
  {X | X ∈ S.faces ∧ ∃ {X'}, X' ∈ A ∧ X ⊆ X'}
  (λ X ⟨hX, _⟩, hX)
  (λ X Y ⟨hX, X', hX', hXX'⟩ hYX, ⟨S.down_closed hX hYX, X', hX', subset.trans hYX hXX'⟩)

--Homonymy problem
lemma closure_empty :
  (S.closure ∅).faces = ∅ :=
begin
  unfold simplicial_complex.closure,
  simp,
end

lemma closure_singleton_empty (hS : S.faces.nonempty) :
  (S.closure {∅}).faces = {∅} :=
begin
  ext X,
  split,
  { rintro ⟨hX, X', (hX' : X' = ∅), hXX'⟩,
    rw hX' at hXX',
    exact finset.subset_empty.1 hXX' },
  { rintro (hX : X = ∅),
    rw hX,
    obtain ⟨Y, hY⟩ := hS,
    exact ⟨S.down_closed hY (empty_subset Y), ∅, mem_singleton ∅, subset.refl ∅⟩ }
end

--Homonymy problem
lemma closure_singleton (hx : {x} ∈ S.faces) :
  (S.closure {{x}}).faces = {∅, {x}} :=
begin
  ext Y,
  split,
  { rintro ⟨hY, Z, (hZ : Z = {x}), hYZ⟩,
    rw hZ at hYZ,
    simp only [mem_singleton_iff, mem_insert_iff],
    rwa ← finset.subset_singleton_iff },
  { have hxS : {x} ∈ (S.closure {{x}}).faces := ⟨hx, {x}, rfl, finset.subset.refl {x}⟩,
    simp only [mem_singleton_iff, mem_insert_iff],
    rintro (rfl | rfl),
    { exact empty_mem_faces_of_nonempty (nonempty_of_mem hxS) },
    { assumption } }
end

lemma mem_closure_singleton_iff :
  Y ∈ (S.closure {X}).faces ↔ Y ∈ S.faces ∧ Y ⊆ X :=
begin
  split,
  { rintro ⟨hY, Z, (hZ : Z = X), hYZ⟩,
    rw hZ at hYZ,
    exact ⟨hY, hYZ⟩ },
  { rintro ⟨hY, hYX⟩,
    exact ⟨hY, X, rfl, hYX⟩ }
end

lemma closure_subset :
  (S.closure A).faces ⊆ S.faces :=
λ X ⟨hX, _⟩, hX

--Homonymy problem
lemma faces_subset_closure :
  S.faces ∩ A ⊆ (S.closure A).faces :=
λ X hX, ⟨hX.1, X, hX.2, subset.refl _⟩

lemma closure_faces_subset_of_subset (hAB : A ⊆ B) :
  (S.closure A).faces ⊆ (S.closure B).faces :=
λ X ⟨hX, Y, hY, hXY⟩, ⟨hX, Y, hAB hY, hXY⟩

lemma pure_closure_of_pure (hS : S.pure_of n)
  (hA : ∀ {W}, W ∈ A → ∃ {X}, X ∈ A ∧ X ∈ S.faces ∧ (X : finset E).card = m) :
  (S.closure A).pure_of m :=
begin
  sorry
end

end affine
