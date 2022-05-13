/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.homotopy
import algebraic_topology.dold_kan.notations

/-!

# Construction of homotopies for the Dold-Kan correspondence

TODO (@joelriou) continue adding the various files references below

(The general strategy of proof of the Dold-Kan correspondence is explained
in `equivalence.lean`.)

The purpose of the files `homotopies.lean`, `faces.lean`, `projections.lean`
and `p_infty.lean` is to construct an idempotent endomorphism
`P_infty : K[X] ⟶ K[X]` of the alternating face map complex
for each `X : simplicial_object C` when `C` is a preadditive category.
In the case `C` is abelian, this `P_infty` shall be the projection on the
normalized Moore subcomplex of `K[X]` associated to the decomposition of the
complex `K[X]` as a direct sum of this normalized subcomplex and of the
degenerate subcomplex.

In `p_infty.lean`, this endomorphism `P_infty` shall be obtained by
passing to the limit idempotent endomorphisms `P q` for all `(q : ℕ)`.
These endomorphisms `P q` are defined by induction. The idea is to
start from the identity endomorphism `P 0` of `K[X]` and to ensure by
induction that the `q` higher face maps (except $d_0$) vanish on the
image of `P q`. Then, in a certain degree `n`, the image of `P q` for
a big enough `q` will be contained in the normalized subcomplex. This
construction is done in `projections.lean`.

It would be easy to define the `P q` degreewise (similarly as it is done
in *Simplicial Homotopy Theory* by Goerrs-Jardine p. 149), but then we would
have to prove that they are compatible with the differential (i.e. they
are chain complex maps), and also that they are homotopic to the identity.
These two verifications are quite technical. In order to reduce the number
of such technical lemmas, the strategy that is followed here is to define
a series of null homotopic maps `Hσ q` (attached to families of maps `hσ`)
and use these in order to construct `P q` : the endomorphisms `P q`
shall basically be obtained by altering the identity endomorphism by adding
null homotopic maps, so that we get for free that they are morphisms
of chain complexes and that they are homotopic to the identity. The most
technical verifications that are needed about the null homotopic maps `Hσ`
are obtained in `faces.lean`.

In this file `homotopies.lean`, we define the null homotopic maps
`Hσ q : K[X] ⟶ K[X]`, show that they are natural (see `nat_trans_Hσ`) and
compatible the application of additive functors (see `map_Hσ`).

## References
* [Albrecht Dold, *Homology of Symmetric Products and Other Functors of Complexes*][dold1958]
* [Paul G. Goerss, John F. Jardine, *Simplical Homotopy Theory*][goerss-jardine-2009]

-/

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.preadditive
open category_theory.simplicial_object
open homotopy
open opposite
open_locale simplicial dold_kan

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]
variables {X : simplicial_object C}

/-- As we are using chain complexes indexed by `ℕ`, we shall need the relation
`c` such `c m n` if and only if `n+1=m`. -/
abbreviation c := complex_shape.down ℕ

/-- Helper when we need some `c.rel i j` (i.e. `complex_shape.down ℕ`),
e.g. `c_mk n (n+1) rfl` -/
lemma c_mk (i j : ℕ) (h : j+1 = i) : c.rel i j :=
complex_shape.down_mk i j h

/-- This lemma is meant to be used with `null_homotopic_map'_f_of_not_rel_left` -/
lemma cs_down_0_not_rel_left (j : ℕ) : ¬c.rel 0 j :=
begin
  intro hj,
  dsimp at hj,
  apply nat.not_succ_le_zero j,
  rw [nat.succ_eq_add_one, hj],
end

/-- The sequence of maps which gives the null homotopic maps `Hσ` that shall be in
the inductive construction of the projections `P q : K[X] ⟶ K[X]` -/
def hσ (q : ℕ) (n : ℕ) : X _[n] ⟶ X _[n+1] :=
if n<q
  then 0
  else (-1 : ℤ)^(n-q) • X.σ ⟨n-q, nat.sub_lt_succ n q⟩

/-- We can turn `hσ` into a datum that can be passed to `null_homotopic_map'`. -/
def hσ' (q : ℕ) : Π n m, c.rel m n → (K[X].X n ⟶ K[X].X m) :=
λ n m hnm, (hσ q n) ≫ eq_to_hom (by congr')

lemma hσ'_eq_zero {q n m : ℕ} (hnq : n<q) (hnm : c.rel m n) :
  (hσ' q n m hnm : X _[n] ⟶ X _[m])= 0 :=
by { simp only [hσ', hσ], split_ifs, exact zero_comp, }

lemma hσ'_eq {q n a m : ℕ} (ha : n=a+q) (hnm : c.rel m n) :
  (hσ' q n m hnm : X _[n] ⟶ X _[m]) =
  ((-1 : ℤ)^a • X.σ ⟨a, nat.lt_succ_iff.mpr (nat.le.intro (eq.symm ha))⟩) ≫
      eq_to_hom (by congr') :=
begin
  simp only [hσ', hσ],
  split_ifs,
  { exfalso, linarith, },
  { have h' := tsub_eq_of_eq_add ha,
    congr', }
end

/-- The null homotopic map $(hσ q) ∘ d + d ∘ (hσ q)$ -/
def Hσ (q : ℕ) : K[X] ⟶ K[X] := null_homotopic_map' (hσ' q)

/-- `Hσ` is null homotopic -/
def homotopy_Hσ_to_zero (q : ℕ) : homotopy (Hσ q : K[X] ⟶ K[X]) 0 :=
null_homotopy' (hσ' q)

/-- In degree `0`, the null homotopic map `Hσ` is zero. -/
lemma Hσ_eq_zero (q : ℕ) : (Hσ q : K[X] ⟶ K[X]).f 0 = 0  :=
begin
  unfold Hσ,
  rw null_homotopic_map'_f_of_not_rel_left (c_mk 1 0 rfl) cs_down_0_not_rel_left,
  cases q,
  { erw hσ'_eq (show 0=0+0, by refl) (c_mk 1 0 rfl),
    simp only [pow_zero, fin.mk_zero, one_zsmul, eq_to_hom_refl, category.comp_id],
    erw chain_complex.of_d,
    simp only [alternating_face_map_complex.obj_d, fin.sum_univ_two,
      fin.coe_zero, pow_zero, one_zsmul, fin.coe_one, pow_one, comp_add,
      neg_smul, one_zsmul, comp_neg, add_neg_eq_zero],
    erw [δ_comp_σ_self, δ_comp_σ_succ], },
  { erw [hσ'_eq_zero (nat.succ_pos q) (c_mk 1 0 rfl), zero_comp], },
end

/-- The maps `hσ' q n m hnm` are natural on the simplicial object -/
lemma hσ'_naturality (q : ℕ) (n m : ℕ) (hnm : c.rel m n)
  {X Y : simplicial_object C} (f : X ⟶ Y) :
  f.app (op [n]) ≫ hσ' q n m hnm = hσ' q n m hnm ≫ f.app (op [m]) :=
begin
  have h : n+1 = m := hnm,
  subst h,
  simp only [hσ', eq_to_hom_refl, comp_id],
  unfold hσ,
  split_ifs,
  { rw [zero_comp, comp_zero], },
  { simp only [zsmul_comp, comp_zsmul],
    erw f.naturality,
    refl, },
end

/-- For each q, `Hσ q` is a natural transformation. -/
def nat_trans_Hσ (q : ℕ) :
  alternating_face_map_complex C ⟶ alternating_face_map_complex C :=
{ app := λ X, Hσ q,
  naturality' := λ X Y f, begin
    unfold Hσ,
    rw [null_homotopic_map'_comp, comp_null_homotopic_map'],
    congr,
    ext n m hnm,
    simp only [alternating_face_map_complex_map, alternating_face_map_complex.map,
      chain_complex.of_hom_f, hσ'_naturality],
  end, }

/-- The maps `hσ' q n m hnm` are compatible with the application of additive functors. -/
lemma map_hσ' {D : Type*} [category D] [preadditive D]
  (G : C ⥤ D) [G.additive] (X : simplicial_object C)
  (q n m : ℕ) (hnm : c.rel m n) :
  (hσ' q n m hnm : K[((whiskering _ _).obj G).obj X].X n ⟶ _) =
    G.map (hσ' q n m hnm : K[X].X n ⟶ _) :=
begin
  unfold hσ' hσ,
  split_ifs,
  { simp only [functor.map_zero, zero_comp], },
  { simpa only [eq_to_hom_map, functor.map_comp, functor.map_zsmul], },
end

/-- The null homotopic maps `Hσ` are compatible with the application of additive functors. -/
lemma map_Hσ {D : Type*} [category D] [preadditive D]
  (G : C ⥤ D) [G.additive] (X : simplicial_object C) (q n : ℕ) :
  (Hσ q : K[((whiskering C D).obj G).obj X] ⟶ _).f n =
    G.map ((Hσ q : K[X] ⟶ _).f n) :=
begin
  unfold Hσ,
  have eq := homological_complex.congr_hom (map_null_homotopic_map' G (hσ' q)) n,
  simp only [functor.map_homological_complex_map_f, ← map_hσ'] at eq,
  rw eq,
  let h := (functor.congr_obj (map_alternating_face_map_complex G) X).symm,
  congr',
end

end dold_kan

end algebraic_topology
