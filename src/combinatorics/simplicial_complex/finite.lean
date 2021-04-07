import combinatorics.simplicial_complex.basic

namespace affine
open set
variables {m : ℕ}
local notation `E` := fin m → ℝ
variables {S : simplicial_complex m}

/--
A simplicial complex is finite iff it has finitely many faces.
-/
def simplicial_complex.finite (S : simplicial_complex m) : Prop := S.faces.finite

noncomputable def simplicial_complex.faces_finset (S : simplicial_complex m) (hS : S.finite) :
  finset (finset E) :=
hS.to_finset

@[simp]
lemma mem_faces_finset (hS : S.finite) (X : finset E) :
  X ∈ S.faces_finset hS ↔ X ∈ S.faces :=
set.finite.mem_to_finset _

/--
A simplicial complex `S` is locally finite at the face `X` iff `X` is a subface of finitely many
faces in `S`.
-/
def simplicial_complex.locally_finite_at (S : simplicial_complex m) (X : finset E) : Prop :=
set.finite {Y ∈ S.faces | X ⊆ Y}

/--
A simplicial complex `S` is locally finite at the face `X` iff `X` is a subface of infinitely many
faces in `S`.
-/
def simplicial_complex.locally_infinite_at (S : simplicial_complex m) (X : finset E) : Prop :=
set.infinite {Y ∈ S.faces | X ⊆ Y}

lemma simplicial_complex.locally_finite_at_iff_not_locally_infinite_at {S : simplicial_complex m}
  (X : finset E) :
  ¬S.locally_infinite_at X ↔ S.locally_finite_at X :=
not_not

/--
A simplicial complex is locally finite iff each of its faces belongs to finitely many faces.
-/
def simplicial_complex.locally_finite (S : simplicial_complex m) : Prop :=
∀ {X : finset _}, X ∈ S.faces → X.nonempty → S.locally_finite_at X

example {α : Type*} {s : set α} {p q : α → Prop} (h : ∀ x, p x → q x) :
  {x ∈ s | p x} ⊆ {x ∈ s | q x} :=
begin
  refine inter_subset_inter_right s h,
end

lemma locally_finite_at_up_closed {S : simplicial_complex m} {X Y : finset E}
  (hX : S.locally_finite_at X) (hXY : X ⊆ Y) : S.locally_finite_at Y :=
begin
  apply hX.subset,
  rintro Z ⟨_, _⟩,
  exact ⟨‹Z ∈ S.faces›, finset.subset.trans hXY ‹Y ⊆ Z›⟩,
end

lemma locally_infinite_at_down_closed {S : simplicial_complex m} {X Y : finset E}
  (hY : S.locally_infinite_at Y) (hXY : X ⊆ Y) : S.locally_infinite_at X :=
λ t, hY (locally_finite_at_up_closed t hXY)

lemma locally_finite_of_finite {S : simplicial_complex m} (hS : S.finite) : S.locally_finite :=
  λ X hX _, hS.subset (λ Y hY, hY.1)

end affine
