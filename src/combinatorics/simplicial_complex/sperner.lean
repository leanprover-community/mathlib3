import tactic
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import analysis.convex.topology
import combinatorics.simplicial_complex.dump
import combinatorics.simplicial_complex.extreme_point
import combinatorics.simplicial_complex.basic
import combinatorics.simplicial_complex.topology
import data.nat.parity

namespace affine

open_locale classical affine big_operators
open set
variables {m n : ℕ} {S : simplicial_complex m}
local notation `E` := fin m → ℝ

def simplicial_complex.finite (S : simplicial_complex m) : Prop := S.faces.finite

noncomputable def simplicial_complex.faces_finset (S : simplicial_complex m) (hS : S.finite) :
  finset (finset E) :=
hS.to_finset

@[simp]
lemma mem_faces_finset (hS : S.finite) (X : finset E) :
  X ∈ S.faces_finset hS ↔ X ∈ S.faces :=
set.finite.mem_to_finset _

def is_sperner_colouring (S : simplicial_complex (m+1))
  (f : (fin (m+1) → ℝ) → fin (m+1)) : Prop :=
∀ (X : fin (m+1) → ℝ) i, X ∈ S.points → X i = 0 → f X ≠ i

def panchromatic {n m : ℕ} (f : (fin n → ℝ) → fin m) (X : finset (fin n → ℝ)) :=
  X.image f = finset.univ

lemma panchromatic_iff (f : E → fin m) (X : finset E) :
  panchromatic f X ↔ (X.image f).card = m :=
begin
  rw panchromatic,
  split,
  { intro h,
    simp [h] },
  { intro h,
    refine finset.eq_of_subset_of_card_le (finset.image f X).subset_univ _,
    simp [h] }
end

lemma std_simplex_one : std_simplex (fin 1) = { ![(1 : ℝ)]} :=
begin
  ext x,
  simp [std_simplex_eq_inter],
  split,
  { rintro ⟨-, hx⟩,
    ext i,
    have : i = 0 := subsingleton.elim _ _,
    rw this,
    apply hx },
  { rintro rfl,
    refine ⟨λ _, _, rfl⟩,
    simp only [matrix.cons_val_fin_one],
    apply zero_le_one }
end

lemma strong_sperner_zero_aux {S : simplicial_complex 1}
  (hS₁ : S.space = std_simplex (fin 1)) :
  S.faces = {∅, { ![1]}} :=
begin
  have X_subs : ∀ X ∈ S.faces, X ⊆ { ![(1:ℝ)]},
  { rintro X hX,
    have := face_subset_space hX,
    rw [hS₁, std_simplex_one] at this,
    rintro x hx,
    simpa using this hx },
  have : ∃ X ∈ S.faces, X = { ![(1:ℝ)]},
  { have std_eq := hS₁,
    have one_mem : ![(1:ℝ)] ∈ std_simplex (fin 1),
    { rw std_simplex_one,
      simp },
    rw [←std_eq, simplicial_complex.space, set.mem_bUnion_iff] at one_mem,
    rcases one_mem with ⟨X, hX₁, hX₂⟩,
    refine ⟨X, hX₁, _⟩,
    have := X_subs X hX₁,
    rw finset.subset_singleton_iff at this,
    rcases this with (rfl | rfl),
    { simp only [finset.coe_empty] at hX₂,
      rw convex_hull_empty at hX₂,
      apply hX₂.elim },
    { refl } },
  ext X,
  simp only [set.mem_insert_iff, set.mem_singleton_iff, ←finset.subset_singleton_iff],
  split,
  { intro hX,
    apply X_subs _ hX },
  { intro hX,
    rcases this with ⟨Y, hY₁, rfl⟩,
    exact S.down_closed hY₁ hX },
end

theorem strong_sperner_zero {S : simplicial_complex 1}
  (hS₁ : S.space = std_simplex (fin 1)) (hS₂ : S.finite)
  (f : (fin 1 → ℝ) → fin 1) :
  odd ((S.faces_finset hS₂).filter (panchromatic f)).card :=
begin
  have : (S.faces_finset hS₂).filter (panchromatic f) = {{ ![(1:ℝ)]}},
  { ext X,
    simp only [mem_faces_finset, finset.mem_singleton, finset.mem_filter,
      strong_sperner_zero_aux hS₁, mem_insert_iff, mem_singleton_iff],
    split,
    { rintro ⟨(rfl | rfl), h⟩,
      { change _ = _ at h,
        rw [univ_unique, fin.default_eq_zero, finset.image_empty, eq_comm] at h,
        simp only [finset.singleton_ne_empty] at h,
        cases h },
      { refl } },
    rintro rfl,
    refine ⟨or.inr rfl, _⟩,
    change _ = _,
    simp only [fin.default_eq_zero, finset.image_singleton, univ_unique],
    rw finset.singleton_inj,
    apply subsingleton.elim },
  rw this,
  simp,
end

-- { faces := {X ∈ S.faces | ∀ (x : fin (m+1) → ℝ), x ∈ X → x 0 = 0 },
-- := finset.image matrix.vec_tail '' S.faces,

lemma affine_independent_proj {n : ℕ} {ι : Type*}
  {p : ι → fin (n+1) → ℝ}
  (hp₁ : ∀ i, p i 0 = 0)
  (hp₂ : affine_independent ℝ p) :
  affine_independent ℝ (matrix.vec_tail ∘ p) :=
begin
  rw affine_independent_def,
  intros s w hw hs i hi,
  rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw (0:fin n → ℝ) at hs,
  rw finset.weighted_vsub_of_point_apply at hs,
  simp only [vsub_eq_sub, function.comp_app, sub_zero] at hs,
  have : s.weighted_vsub p w = (0:fin (n+1) → ℝ),
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw (0:fin (n+1) → ℝ),
    rw finset.weighted_vsub_of_point_apply,
    simp only [vsub_eq_sub, sub_zero],
    ext j,
    simp only [pi.zero_apply],
    rw finset.sum_apply _ s (λ i, w i • p i),
    refine fin.cases _ _ j,
    { simp [hp₁] },
    intro j,
    dsimp,
    rw function.funext_iff at hs,
    specialize hs j,
    simp only [pi.zero_apply] at hs,
    rw finset.sum_apply _ s (λ i, w i • matrix.vec_tail (p i)) at hs,
    dsimp [matrix.vec_tail] at hs,
    apply hs },
  exact hp₂ s w hw this i hi,
end

lemma is_linear_map_matrix_vec_tail {n : ℕ} :
  is_linear_map ℝ (matrix.vec_tail : (fin n.succ → ℝ) → (fin n → ℝ)) :=
{ map_add := by simp,
  map_smul := λ c x,
  begin
    ext i,
    simp [matrix.vec_tail],
  end }

def dimension_drop {S : simplicial_complex (m+1)} :
  simplicial_complex m :=
{ faces := {Y | ∃ X ∈ S.faces, finset.image matrix.vec_tail X = Y ∧ ∀ (x : fin (m+1) → ℝ), x ∈ X → x 0 = 0 },
  down_closed :=
  begin
    rintro _ Y ⟨X, hX₁, rfl, hX₂⟩ YX,
    refine ⟨Y.image (matrix.vec_cons 0), _, _⟩,
    { apply S.down_closed hX₁,
      rw finset.image_subset_iff,
      rintro y hY,
      have := YX hY,
      simp only [exists_prop, finset.mem_image] at this,
      rcases this with ⟨x, hx, rfl⟩,
      suffices : matrix.vec_head x = 0,
      { rw ← this,
        simpa },
      apply hX₂ _ hx },
    rw finset.image_image,
    refine ⟨_, _⟩,
    { convert finset.image_id,
      { ext x,
        dsimp,
        simp, },
      { exact classical.dec_eq (fin m → ℝ) } },
    simp,
  end,
  indep :=
  begin
    rintro _ ⟨X, hX₁, rfl, hX₂⟩,
    let f : ((finset.image matrix.vec_tail X : set (fin m → ℝ))) → (X : set (fin (m+1) → ℝ)),
    { intro t,
      refine ⟨matrix.vec_cons 0 t.1, _⟩,
      rcases t with ⟨t, ht⟩,
      simp only [set.mem_image, finset.mem_coe, finset.coe_image] at ht,
      rcases ht with ⟨x, hx, rfl⟩,
      suffices : matrix.vec_head x = 0,
      { rw ← this,
        simpa },
      apply hX₂ x hx },
    have hf : function.injective f,
    { rintro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ h,
      rw subtype.ext_iff at h,
      change matrix.vec_cons _ x₁ = matrix.vec_cons _ x₂ at h,
      apply subtype.ext,
      apply_fun matrix.vec_tail at h,
      simpa using h },
    have := affine_independent_proj _ (S.indep hX₁),
    { convert affine_independent_embedding_of_affine_independent ⟨f, hf⟩ this,
      ext p,
      dsimp,
      simp },
    rintro ⟨i, hi⟩,
    apply hX₂ _ hi,
  end,
  disjoint :=
  begin
    rintro _ _ ⟨X, hX₁, rfl, hX₂⟩ ⟨Y, hY₁, rfl, hY₂⟩,
    simp only [finset.coe_image],
    rw ← is_linear_map.image_convex_hull,
    rw ← is_linear_map.image_convex_hull,

    rw set.image_inter_on,
    refine set.subset.trans (set.image_subset matrix.vec_tail (S.disjoint hX₁ hY₁)) _,
    rw is_linear_map.image_convex_hull,
    apply convex_hull_mono,
    apply set.image_inter_subset,
    apply is_linear_map_matrix_vec_tail,
    { intros x hx y hy h,
      rw ← matrix.cons_head_tail x,
      rw ← matrix.cons_head_tail y,
      rw h,
      sorry -- want x 0 = 0 and y 0 = 0 because they're in the convex hull of points which are that

      -- rw (show matrix.vec_head x = 0, from hY₂ _ _),
      -- rw (show matrix.vec_head y = 0, from (convex_hull_face_subset _ hX hy).2)
      },
    apply is_linear_map_matrix_vec_tail,
    apply is_linear_map_matrix_vec_tail,
  end
}

theorem strong_sperner {S : simplicial_complex (m+1)}
  (hS₁ : S.space = std_simplex (fin (m+1))) (hS₂ : S.finite) (hS₃ : S.pure_of (m+1))
  {f} (hf : is_sperner_colouring S f) :
  odd ((S.faces_finset hS₂).filter (panchromatic f)).card :=
begin
  tactic.unfreeze_local_instances,
  induction m with n ih generalizing f,
  { apply strong_sperner_zero hS₁ },
  sorry
end

theorem sperner {S : simplicial_complex (m+1)}
  (hS₁ : S.space = std_simplex (fin (m+1))) (hS₂ : S.finite) (hS₃ : S.pure_of (m+1))
  {f} (hf : is_sperner_colouring S f) :
  ∃ X ∈ S.faces, panchromatic f X :=
begin
  have := nat.odd_gt_zero (strong_sperner hS₁ hS₂ hS₃ hf),
  rw finset.card_pos at this,
  rcases this with ⟨X, hX⟩,
  simp only [mem_faces_finset, finset.mem_filter] at hX,
  exact ⟨_, hX.1, hX.2⟩,
end

end affine
