/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.convex.topology
import combinatorics.simplicial_complex.to_move.default
import data.real.basic
import linear_algebra.affine_space.finite_dimensional
-- import data.nat.parity

open_locale classical affine big_operators
open set
variables {m n : ℕ} {α : Type} {E : Type*} [normed_group E] [normed_space ℝ E]
/-
MATHLIB DEPARTURE ZONE
A few PRs to be done
-/

-- TODO (Bhavik): Golf


#exit
/-
THEOREMS ON SALE
Previous attempts of Bhavik
-/

-- lemma of_affine_independent_set (X : set E) (hX : affine_independent ℝ (λ p, p : X → E)) :
--   ∀ (s : finset E) (w : E → ℝ), ∑ i in s, w i = 0 → s.weighted_vsub _ w = (0 : E) → ∀ i ∈ s, w i = 0 :=
-- begin
-- end

-- omit V
-- lemma filter_attach {ι : Type*} (s : finset ι) (p : ι → Prop) :
--   s.attach.filter (λ i, p i) = (s.filter p).attach.image (λ k, ⟨k, finset.filter_subset _ _ k.2⟩) :=
-- begin
--   ext ⟨a, ha⟩,
--   simp [ha],
-- end
-- include V

-- lemma of_affine_independent_set (s : set P) (hp : affine_independent k (λ p, p : s → P)) :
--   ∀ (t : finset ι) (w : ι → k) (z : ι → P), ∑ i in t, w i = 0 → (∀ i ∈ t, z i ∈ s) →
--   t.weighted_vsub z w = (0:V) → ∀ i ∈ t, w i = 0 :=
-- begin
--   rintro t w z hw₁ hz hw₂,
--   rw affine_independent_def at hp,
--   let s' : finset s := t.attach.image (λ i, ⟨z i, hz _ i.2⟩),
--   let w' : s → k,
--   { intro x,
--     apply ∑ i in (t.filter (λ j, z j = x)), w i },
--   have : ∑ (i : s) in s', w' i = 0,
--   { change ∑ (i : s) in s', ∑ j in _, _ = _,-- rintro ⟨_, _⟩ ⟨_, _⟩,
--     rw finset.sum_image' (λ (i : {x // x ∈ t}), w i),
--     { dsimp only,
--       rw finset.sum_attach,
--       rw hw₁ },
--     simp only [finset.mem_attach, subtype.mk_eq_mk, forall_true_left, subtype.coe_mk],
--     rintro c,
--     have : finset.filter (λ (c' : {x // x ∈ t}), z ↑c' = z ↑c) t.attach = _,
--     { exact filter_attach t (λ c', z c' = z c) },
--     simp only [finset.filter_congr_decidable],
--     simp only [finset.filter_congr_decidable] at this,
--     rw this,
--     simp [finset.sum_attach] },
--   have : s'.weighted_vsub (λ (p : ↥s), ↑p) w' = (0 : V),
--   { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ this (0:V),
--     rw finset.weighted_vsub_of_point_apply,
--     simp only [vsub_eq_sub, sub_zero],
--     change ∑ (i : s) in s', (∑ j in _, _) • _ = _,
--     simp_rw [finset.sum_smul],
--     rw finset.sum_image' (λ (i : {x // x ∈ t}), _),
--   },
--   -- specialize hp s' w' this,


--   -- sorry,

--   -- have := (t.image z).attach,
--   -- have : finset s := t.
-- end

-- example (X Y : finset E) (h : X ⊆ Y) : X ∩ Y = X :=
-- begin
--   library_search,
-- end

lemma thing {ι β : Type*} [add_comm_monoid β] (X : finset ι) (f : ι → β) :
  ∑ (x : (X : set ι)), f ↑x = ∑ x in X, f x :=
begin
  rw ←finset.sum_image,
  apply finset.sum_congr _ (λ _ _, rfl),
  { ext, simp },
  { simp },
end

def triangulation.facets (S : triangulation s) : set (finset E) :=
{X ∈ S.faces | ∀ Y ∈ S.faces, X ⊆ Y → X = Y}

def of_facets (S : set (finset E)) (hS₁ : ∀ X ∈ S, affine_independent ℝ (λ p, p : (X : set E) → E))
  (hS₂ : s = ⋃ (X ∈ S), convex_hull ↑X)
  (disjoint : ∀ (X Y ∈ S), convex_hull ↑X ∩ convex_hull ↑Y ⊆ convex_hull (X ∩ Y : set E)) :
  triangulation s :=
{ faces := {X | ∃ Y ∈ S, X ⊆ Y},
  indep :=
  begin
    rintro X ⟨Y, YS, XY⟩,
    apply affine_independent_of_subset_affine_independent (hS₁ _ YS),
    rwa finset.coe_subset,
  end,
  covering :=
  begin
    rw hS₂,
    ext x,
    simp only [exists_prop, set.mem_Union, set.mem_set_of_eq],
    split,
    { simp only [and_imp, exists_imp_distrib],
      rintro X hX hx,
      refine ⟨X, ⟨X, hX, set.subset.refl _⟩, hx⟩ },
    { simp only [and_imp, exists_imp_distrib],
      rintro X Y YS XY hx,
      refine ⟨Y, YS, convex_hull_mono XY hx⟩ }
  end,
  down_closed :=
  begin
    rintro X ⟨Y, YS, XY⟩ Z ZX,
    exact ⟨_, YS, set.subset.trans ZX XY⟩,
  end,
  disjoint :=
  begin
    rintro X Y ⟨Z, ZS, XZ⟩ ⟨W, WS, YW⟩,
    rintro x ⟨hx₁, hx₂⟩,
    rw ←finset.coe_inter,
    have : x ∈ convex_hull (Z ∩ W : set E),
      apply disjoint _ _ ZS WS ⟨convex_hull_mono XZ hx₁, convex_hull_mono YW hx₂⟩,
    rw ←finset.coe_inter at this,
    have := disjoint_convex_hulls (hS₁ _ ZS) XZ (finset.inter_subset_left Z W) ⟨hx₁, this⟩,
    rw ←finset.coe_inter at this,
    rw ←finset.inter_assoc at this,
    have := disjoint_convex_hulls (hS₁ _ WS) (finset.inter_subset_right (X ∩ Z) W) YW ⟨this, hx₂⟩,
    rw ←finset.coe_inter at this,
    convert this using 3,
    ext x,
    simp only [finset.inter_assoc, and.congr_right_iff, finset.mem_inter],
    intro hx₁,
    rw ← and_assoc,
    apply iff.symm,
    apply and_iff_right_of_imp,
    intro hx₂,
    refine ⟨XZ hx₁, YW hx₂⟩,
  end }

def std_basis (n : ℕ) : fin n → fin n → ℝ :=
λ i, linear_map.std_basis ℝ (λ i, ℝ) i 1

def basis_with_zero (n : ℕ) : fin (n+1) → fin n → ℝ :=
begin
  refine fin.cases _ _,
  apply (0 : fin n → ℝ),
  apply std_basis n,
end

lemma basis_with_zero_zero {n : ℕ} : basis_with_zero n 0 = 0 :=
by rw [basis_with_zero, fin.cases_zero]

lemma basis_with_zero_succ {n : ℕ} (j : fin n) : basis_with_zero n j.succ = std_basis n j :=
by rw [basis_with_zero, fin.cases_succ]

lemma linear_indep {n : ℕ} : linear_independent ℝ (std_basis n) :=
(pi.is_basis_fun ℝ (fin n)).1

lemma affine_indep {n : ℕ} : affine_independent ℝ (basis_with_zero n) :=
begin
  rw affine_independent_iff_linear_independent_vsub ℝ _ (0 : fin n.succ),
  simp only [basis_with_zero_zero],
  simp only [vsub_eq_sub, sub_zero],
  let g : {x : fin n.succ // x ≠ 0} → fin n := λ (j : {x : fin n.succ // x ≠ 0}), fin.pred j.1 j.2,
  have : std_basis n ∘ g = λ i, basis_with_zero n i,
  { ext j,
    dsimp,
    rw ← basis_with_zero_succ,
    simp },
  rw ← this,
  apply linear_independent.comp linear_indep g _,
  rintro i j hi,
  ext1,
  exact fin.pred_inj.1 hi,
end

def trivial {m : ℕ} : triangulation (std_simplex (fin (m+1))) :=
of_facets
  (singleton (finset.univ.image (std_basis (m+1))))
  (begin
    rintro X hX,
    simp only [set.mem_singleton_iff] at hX,
    subst hX,
    rw fintype.coe_image_univ,
    apply affine_independent_set_of_affine_independent,
    convert affine_independent_embedding_of_affine_independent (fin.succ_embedding _).to_embedding affine_indep,
    ext j x,
    simp only [function.comp_app, fin.coe_succ_embedding, rel_embedding.coe_fn_to_embedding, basis_with_zero_succ, std_basis],
  end)
  (begin
    rw [set.bUnion_singleton, fintype.coe_image_univ],
    rw ← convex_hull_basis_eq_std_simplex,
    rw std_basis,
    congr' 2,
    ext i j,
    rw linear_map.std_basis_apply,
    rw function.update,
    simp [eq_comm],
    convert rfl,
  end)
  (begin
    simp_rintro X Y hX hY,
    substs X Y,
    simp,
    exact set.subset.refl _,
  end)

variables {S : triangulation s}
def triangulation.finite (S : triangulation s) : Prop := S.faces.finite

noncomputable def triangulation.faces_finset (S : triangulation s) (hS : S.finite) :
  finset (finset E) :=
hS.to_finset

@[simp]
lemma mem_faces_finset (hS : S.finite) (X : finset E) :
  X ∈ S.faces_finset hS ↔ X ∈ S.faces :=
set.finite.mem_to_finset

def triangulation.points (S : triangulation s) : set E :=
⋃ k ∈ S.faces, (k : set E)

lemma convex_hull_face_subset (X) (hX : X ∈ S.faces) : convex_hull ↑X ⊆ s :=
begin
  rintro x hx,
  rw S.covering,
  apply set.mem_bUnion hX hx,
end

lemma face_subset {X} (hX : X ∈ S.faces) : ↑X ⊆ s :=
begin
  rintro x hx,
  rw S.covering,
  apply set.mem_bUnion hX,
  apply subset_convex_hull,
  apply hx
end

lemma points_subset : S.points ⊆ s :=
begin
  rintro x hx,
  rw S.covering,
  rw triangulation.points at hx,
  rw set.mem_bUnion_iff at hx,
  rcases hx with ⟨X, hX, hx⟩,
  exact set.mem_bUnion hX (subset_convex_hull X hx)
end

def is_sperner_colouring {s : set (fin (m+1) → ℝ)} (S : triangulation s)
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

def edge_of_std_simplex (m) : set (fin (m+1) → ℝ) :=
std_simplex (fin (m+1)) ∩ {x | x 0 = 0}

lemma convex_hull_ne_zero_points (X : set (fin (m+1) → ℝ)) (x : fin (m+1) → ℝ)
  (hX : ∀ (y : fin (m+1) → ℝ), y ∈ X → 0 ≤ y 0)
  (hx : x 0 = 0)
  (hXx : x ∈ convex_hull X) :
x ∈ convex_hull {y : fin (m+1) → ℝ | y ∈ X ∧ y 0 = 0} :=
begin
  rw convex_hull_eq.{37} at hXx,
  rcases hXx with ⟨ι, t, w, z, hw₀, hw₁, hz, x_eq⟩,
  have x_zero : t.center_mass w z 0 = 0,
  { rw [x_eq, hx] },
  rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at x_zero,
  dsimp only at x_zero,
  rw finset.sum_apply 0 t (λ i, w i • z i) at x_zero,
  dsimp at x_zero,
  have : ∀ (x : ι), x ∈ t → 0 ≤ w x * z x 0,
  { rintro y hy,
    exact mul_nonneg (hw₀ y hy) (hX (z y) (hz y hy)) },
  rw finset.sum_eq_zero_iff_of_nonneg this at x_zero,
  dsimp only at x_zero,
  rw convex_hull_eq.{37},
  refine ⟨ι, t.filter (λ i, w i ≠ 0), w, z, _, _, _, _⟩,
  { simp_rintro i hi only [finset.mem_filter],
    apply hw₀ _ hi.1 },
  { rw ←hw₁,
    exact finset.sum_filter_ne_zero },
  { simp_rintro i hi only [finset.mem_filter, set.mem_set_of_eq],
    refine ⟨hz i hi.1, _⟩,
    have := x_zero i hi.1,
    simp only [mul_eq_zero] at this,
    apply or.resolve_left this hi.2 },
  rw ← x_eq,
  exact finset.center_mass_filter_ne_zero z,
end

def lower_triangulation (S : triangulation (std_simplex (fin (m+1)))) :
  triangulation (edge_of_std_simplex m) :=
{ faces := {X ∈ S.faces | ∀ (x : fin (m+1) → ℝ), x ∈ X → x 0 = 0 },
  indep :=
  begin
    rintro X hX,
    simp only [set.mem_sep_eq] at hX,
    apply S.indep _ hX.1,
  end,
  down_closed :=
  begin
    rintro X hX Y YX,
    simp only [set.mem_sep_eq] at hX ⊢,
    refine ⟨S.down_closed X hX.left Y YX, _⟩,
    rintro x hx,
    apply hX.2,
    apply YX,
    apply hx
  end,
  covering :=
  begin
    rw edge_of_std_simplex,
    ext x,
    split,
    { rintro ⟨hx₁, hx₂⟩,
      rw S.covering at hx₁,
      rw set.mem_bUnion_iff at hx₁,
      rcases hx₁ with ⟨X, hX, hx⟩,
      have := convex_hull_ne_zero_points _ x _ hx₂ hx,
      { rw set.mem_bUnion_iff,
        refine ⟨X.filter (λ p, p 0 = 0), _, _⟩,
        { simp only [and_imp, imp_self, set.mem_sep_eq, and_true, finset.mem_filter,
            forall_true_iff],
          apply S.down_closed _ hX,
          apply finset.filter_subset },
        { convert this,
          simp only [finset.mem_coe, finset.coe_filter],
          ext x,
          simp } },
      rintro y hy,
      have : y ∈ std_simplex (fin (m+1)),
      { apply face_subset hX hy },
      rw std_simplex_eq_inter at this,
      simp only [set.mem_inter_eq, set.mem_Inter, set.mem_set_of_eq] at this,
      apply this.1 },
    { rw set.mem_bUnion_iff,
      rintro ⟨X, hX₁, hX₂⟩,
      simp only [set.mem_sep_eq] at hX₁,
      refine ⟨convex_hull_face_subset X hX₁.1 hX₂, _⟩,
      have : convex_hull ↑X ⊆ {x : fin (m+1) → ℝ | x 0 = 0},
      { apply convex_hull_min,
        { rintro x hx,
          exact hX₁.2 x hx },
        rintro x₁ x₂ hx₁ hx₂ a b ha hb q,
        simp only [set.mem_set_of_eq] at hx₁ hx₂ ⊢,
        simp [hx₁, hx₂] },
      apply this,
      apply hX₂ }
  end,
  disjoint :=
  begin
    rintro X Y hX hY,
    apply S.disjoint _ _ hX.1 hY.1,
  end }

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

lemma subset_singleton_iff {ι : Type*} (x : ι) (X : finset ι) :
  X ⊆ {x} ↔ X = ∅ ∨ X = {x} :=
begin
  split,
  { rcases X.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩),
    { intro,
      left,
      refl },
    { intro hx,
      right,
      apply finset.subset.antisymm hx,
      rw finset.singleton_subset_iff,
      have := hx hy,
      simp only [finset.mem_singleton] at this,
      rwa ← this } },
  { rintro (rfl | rfl),
    { apply finset.empty_subset },
    { refl } }
end

lemma convex_hull_empty : convex_hull (∅ : set E) = ∅ :=
convex_empty.convex_hull_eq

lemma strong_sperner_zero_aux (S : triangulation (std_simplex (fin 1))) :
  S.faces = {∅, { ![1]}} :=
begin
  have X_subs : ∀ X ∈ S.faces, X ⊆ { ![(1:ℝ)]},
  { rintro X hX,
    have := face_subset hX,
    rw std_simplex_one at this,
    rintro x hx,
    simpa using this hx },
  have : ∃ X ∈ S.faces, X = { ![(1:ℝ)]},
  { have std_eq := S.covering,
    have one_mem : ![(1:ℝ)] ∈ std_simplex (fin 1),
    { rw std_simplex_one,
      simp },
    rw [std_eq, set.mem_bUnion_iff] at one_mem,
    rcases one_mem with ⟨X, hX₁, hX₂⟩,
    refine ⟨X, hX₁, _⟩,
    have := X_subs X hX₁,
    rw subset_singleton_iff at this,
    rcases this with (rfl | rfl),
    { simp only [finset.coe_empty] at hX₂,
      rw convex_hull_empty at hX₂,
      apply hX₂.elim },
    { refl } },
  ext X,
  simp only [set.mem_insert_iff, set.mem_singleton_iff, ←subset_singleton_iff],
  split,
  { intro hX,
    apply X_subs _ hX },
  { intro hX,
    rcases this with ⟨Y, hY₁, rfl⟩,
    exact S.down_closed _ hY₁ X hX },
end

theorem strong_sperner_zero (S : triangulation (std_simplex (fin 1))) (hS : S.finite)
  (f : (fin 1 → ℝ) → fin 1) :
  odd ((S.faces_finset hS).filter (panchromatic f)).card :=
begin
  have : (S.faces_finset hS).filter (panchromatic f) = {{ ![(1:ℝ)]}},
  { ext X,
    simp only [mem_faces_finset, finset.mem_singleton, finset.mem_filter, strong_sperner_zero_aux],
    simp only [set.mem_insert_iff, set.mem_singleton_iff],
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

-- lemma affine_independent_image {n m : ℕ} {ι : Type*} (f : (fin n → ℝ) →ₗ[ℝ] (fin m → ℝ))
--   (hf : function.injective f)
--   (p : ι → fin n → ℝ)
--   (hp : affine_independent ℝ p) :
--   affine_independent ℝ (f ∘ p) :=
-- begin
--   rw affine_independent_def,
--   rintro s w hw hs i hi,
--   rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw (0:fin m → ℝ) at hs,
--   rw finset.weighted_vsub_of_point_apply at hs,
--   simp only [vsub_eq_sub, function.comp_app, sub_zero] at hs,
--   have : s.weighted_vsub p w = (0:fin n → ℝ),
--   { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw (0:fin n → ℝ),
--     rw finset.weighted_vsub_of_point_apply,
--     simp only [vsub_eq_sub, sub_zero],
--     apply hf,
--     simpa },
--   apply hp s w hw this _ hi,
-- end

lemma cons_inj {n : ℕ} (x y : fin (n+1) → ℝ) (h0 : x 0 = y 0)
  (h1 : matrix.vec_tail x = matrix.vec_tail y) :
  x = y :=
begin
  ext i,
  refine fin.cases h0 _ i,
  rw function.funext_iff at h1,
  apply h1,
end

lemma affine_independent_proj {n : ℕ} {ι : Type*}
  {p : ι → fin (n+1) → ℝ}
  (hp₁ : ∀ i, p i 0 = 0)
  (hp₂ : affine_independent ℝ p) :
  affine_independent ℝ (matrix.vec_tail ∘ p) :=
begin
  rw affine_independent_def,
  rintro s w hw hs i hi,
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

lemma thingy2 {α : Type*} [add_comm_monoid α] {n : ℕ} (k : fin n → α) :
  ∑ (i : fin n), k i = ∑ i in finset.fin_range n, k i :=
begin
  apply finset.sum_congr _ (λ x _, rfl),
  ext x,
  simp only [finset.mem_univ, finset.mem_fin_range],
end

example {α : Type*} {p : α → Prop} : subtype p ↪ α := function.embedding.subtype p

lemma thingy3 {α : Type*} [add_comm_monoid α] {n : ℕ} (k : fin n → α) :
  (∑ (i : fin (n+1)), fin.cases (0:α) k i : α) = ∑ i, k i :=
begin
  have : (fin.cases (0:α) k (0 : fin (n+1)) : α) = (0 : α),
    rw fin.cases_zero,
  rw ←finset.sum_erase finset.univ this,
  symmetry,
  apply finset.sum_bij _ _ _ _ _,
  { rintro a _,
    apply a.succ },
  { rintro a ha,
    simp only [and_true, finset.mem_univ, finset.mem_erase],
    apply fin.succ_ne_zero },
  { rintro a ha,
    symmetry,
    apply fin.cases_succ },
  { rintro a₁ a₂ _ _ h,
    apply fin.succ_injective,
    apply h },
  { rintro b hb,
    simp only [and_true, finset.mem_univ, finset.mem_erase] at hb,
    refine ⟨b.pred hb, by simp, _⟩,
    simp }
end

lemma vec_tail_smul {m : ℕ} (c : ℝ) (x : fin m.succ → ℝ) :
  matrix.vec_tail (c • x) = c • matrix.vec_tail x :=
begin
  ext i,
  simp [matrix.vec_tail],
end

lemma is_linear_map_matrix_vec_tail {n : ℕ} :
  is_linear_map ℝ (matrix.vec_tail : (fin n.succ → ℝ) → (fin n → ℝ)) :=
{ map_add := by simp,
  map_smul := λ c x,
  begin
    ext i,
    simp [matrix.vec_tail],
  end }

lemma vec_tail_mem_simplex_iff {n : ℕ} (y : fin n → ℝ) :
  matrix.vec_cons 0 y ∈ edge_of_std_simplex n ↔ y ∈ std_simplex (fin n) :=
begin
  rw [edge_of_std_simplex, set.mem_inter_eq, set.mem_set_of_eq, matrix.cons_val_zero,
    eq_self_iff_true, and_true, std_simplex, std_simplex, set.mem_set_of_eq, set.mem_set_of_eq,
    fin.forall_fin_succ, matrix.cons_val_zero],
  simp only [matrix.cons_val_succ],
  rw [matrix.vec_cons, fin.cons, thingy3],
  tauto,
end

-- def my_proj : (fin (n+1) → ℝ)
def flatten_triangulation (S : triangulation (edge_of_std_simplex m)) :
  triangulation (std_simplex (fin m)) :=
{ faces := finset.image matrix.vec_tail '' S.faces,
  indep :=
  begin
    rintro X hX,
    simp only [set.mem_image] at hX,
    rcases hX with ⟨X, hX, rfl⟩,
    let f : ((finset.image matrix.vec_tail X : set (fin m → ℝ))) → (X : set (fin (m+1) → ℝ)),
    { intro t,
      refine ⟨matrix.vec_cons 0 t.1, _⟩,
      rcases t with ⟨t, ht⟩,
      simp only [set.mem_image, finset.mem_coe, finset.coe_image] at ht,
      rcases ht with ⟨x, hx, rfl⟩,
      have : matrix.vec_head x = 0 := (face_subset hX hx).2,
      rw ← this,
      simpa },
    have hf : function.injective f,
    { rintro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ h,
      rw subtype.ext_iff at h,
      change matrix.vec_cons _ x₁ = matrix.vec_cons _ x₂ at h,
      apply subtype.ext,
      apply_fun matrix.vec_tail at h,
      simpa using h },
    have := affine_independent_proj _ (S.indep X hX),
    { convert affine_independent_embedding_of_affine_independent ⟨f, hf⟩ this,
      ext p,
      dsimp,
      simp },
    rintro ⟨i, hi⟩,
    apply (face_subset hX hi).2,
  end,
  down_closed :=
  begin
    rintro _ ⟨X, hX, rfl⟩ Y YX,
    refine ⟨Y.image (matrix.vec_cons 0), _, _⟩,
    { apply S.down_closed _ hX,
      rw finset.image_subset_iff,
      rintro y hY,
      have := YX hY,
      simp only [exists_prop, finset.mem_image] at this,
      rcases this with ⟨x, hx, rfl⟩,
      have : matrix.vec_head x = 0 := (face_subset hX hx).2,
      rw ←this,
      simpa },
    rw finset.image_image,
    convert finset.image_id,
    { ext x,
      dsimp,
      simp },
    { exact classical.dec_eq (fin m → ℝ) },
  end,
  covering :=
  begin
    ext i,
    rw set.mem_bUnion_iff,
    simp only [exists_prop, set.mem_image, exists_exists_and_eq_and, finset.coe_image],
    split,
    { intro hi,
      have : matrix.vec_cons 0 i ∈ edge_of_std_simplex m,
      { rwa vec_tail_mem_simplex_iff },
      rw [S.covering, set.mem_bUnion_iff] at this,
      rcases this with ⟨x, hx₁, hx₂⟩,
      refine ⟨x, hx₁, _⟩,
      rw ←is_linear_map.image_convex_hull,
      refine ⟨_, hx₂, _⟩,
      simp only [matrix.tail_cons],
      apply is_linear_map_matrix_vec_tail },
    { rintro ⟨X, hX₁, hX₂⟩,
      rw ← is_linear_map.image_convex_hull at hX₂,
      { rcases hX₂ with ⟨y, hy, rfl⟩,
        rcases convex_hull_face_subset _ hX₁ hy with ⟨hy₁, hy₂⟩,
        rw ← vec_tail_mem_simplex_iff,
        have : matrix.vec_head y = 0 := hy₂,
        rw ← this,
        simp only [matrix.cons_head_tail],
        apply convex_hull_face_subset _ hX₁ hy },
      apply is_linear_map_matrix_vec_tail,
    }
    -- },
    -- have : matrix.vec_cons 0 i ∈ std_simplex (fin (m+1)),
    -- have := S.covering,
  end,
  disjoint :=
  begin
    rintro _ _ ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩,
    simp only [finset.coe_image],
    rw ← is_linear_map.image_convex_hull,
    rw ← is_linear_map.image_convex_hull,

    rw set.image_inter_on,
    refine set.subset.trans (set.image_subset matrix.vec_tail (S.disjoint _ _ hX hY)) _,
    rw is_linear_map.image_convex_hull,
    apply convex_hull_mono,
    apply set.image_inter_subset,
    apply is_linear_map_matrix_vec_tail,
    { rintro x hx y hy h,
      rw ← matrix.cons_head_tail x,
      rw ← matrix.cons_head_tail y,
      rw h,
      rw (show matrix.vec_head x = 0, from (convex_hull_face_subset _ hY hx).2),
      rw (show matrix.vec_head y = 0, from (convex_hull_face_subset _ hX hy).2) },
    apply is_linear_map_matrix_vec_tail,
    apply is_linear_map_matrix_vec_tail,
  end }

def induct_down (S : triangulation (std_simplex (fin (m+1)))) :
  triangulation (std_simplex (fin m)) :=
flatten_triangulation (lower_triangulation S)

example {α : Type*} {s : set α} (p : α → Prop) (hs : s.finite) :
  {x ∈ s | p x}.finite :=
set.finite.subset hs (s.sep_subset p)

lemma induct_down_finite (S : triangulation (std_simplex (fin (m+1)))) (hS : S.finite) :
  (induct_down S).finite :=
begin
  rw triangulation.finite,
  rw induct_down,
  rw flatten_triangulation,
  apply set.finite.image,
  rw lower_triangulation,
  apply set.finite.subset hS (S.faces.sep_subset _)
end

lemma test {n m : ℕ} (h : n.pred ≤ m) : n ≤ m + 1 :=
begin
  exact nat.pred_le_iff.mp h,
end

lemma mwe {α : Type*} {n : ℕ} (X : set (finset α)) (bound : ∀ y ∈ X, finset.card y ≤ n) :
  ∀ y ∈ X, ∃ x ∈ X, y ⊆ x ∧ ∀ z ∈ X, x ⊆ z → x = z :=
begin
  rintro y hy,
  classical,
  rcases ((finset.range (n+1)).filter $ λ i, ∃ x ∈ X, y ⊆ x ∧ finset.card x = i).exists_maximal
    ⟨y.card, finset.mem_filter.2 ⟨finset.mem_range_succ_iff.2 $ bound y hy,
      y, hy, finset.subset.refl _, rfl⟩⟩ with ⟨i, hi1, hi2⟩,
  rw [finset.mem_filter, finset.mem_range_succ_iff] at hi1,
  rcases hi1 with ⟨hin, x, hx, hyx, hxi⟩,
  refine ⟨x, hx, hyx, λ z hz hxz, finset.eq_of_subset_of_card_le hxz _⟩,
  rw [hxi, ← not_lt],
  refine hi2 _ _,
  rw [finset.mem_filter, finset.mem_range_succ_iff],
  refine ⟨bound z hz, z, hz, finset.subset.trans hyx hxz, rfl⟩
end

lemma contained_in_facet (S : triangulation s) {X} (hX : X ∈ S.faces) :
  ∃ Y ∈ S.facets, X ⊆ Y :=
begin
  have : ∀ y ∈ S.faces, finset.card y ≤ m+1,
  { rintro y hy,
    apply size_bound (S.indep _ hy) },
  rcases mwe S.faces this X hX with ⟨Y, _, _, h₂⟩,
  refine ⟨Y, ⟨‹Y ∈ S.faces›, h₂⟩, ‹X ⊆ Y›⟩,
end

def is_homogeneous {m : ℕ} {s : set (fin m → ℝ)} (n : ℕ) (S : triangulation s) : Prop :=
∀ X ∈ S.facets, finset.card X = n
-- ∀ X ∈ S.faces, ∃ Y ∈ S.faces, X ⊆ Y ∧ finset.card Y = n

lemma is_homogeneous_induct_down (S : triangulation (std_simplex (fin (m+1))))
  (hS : is_homogeneous (m+1) S) :
  is_homogeneous m (induct_down S) :=
begin
  rintro X hX,
  simp only [induct_down, triangulation.facets, flatten_triangulation, lower_triangulation,
    and_imp, set.mem_sep_eq, set.mem_image, exists_imp_distrib] at hX,
  rcases hX with ⟨⟨X, ⟨hX₂, hX₄⟩, rfl⟩, hX₃⟩,
  have hX₁ : ∀ (Y ∈ S.faces), (∀ (i : fin (m+1) → ℝ), i ∈ Y → i 0 = 0) →
    finset.image matrix.vec_tail X ⊆ finset.image matrix.vec_tail Y →
    finset.image matrix.vec_tail X = finset.image matrix.vec_tail Y,
  { rintro Y hY₁ hY₂ hY₃,
    apply hX₃ _ _ hY₁ hY₂ rfl hY₃ },
  clear hX₃, -- just a less convenient form of hX₁
  have : ∀ (x : fin (m+1) → ℝ), x ∉ X → x 0 = 0 → insert x X ∉ S.faces,
  { rintro x hx₁ hx₂ t,
    have := hX₁ _ t (by simpa [hx₂] using hX₄) (finset.image_subset_image _),


  },
  -- have := set.image_subset,
  -- simp only [induct_down, flatten_triangulation, lower_triangulation, set.mem_image,
  --   set.mem_sep_eq] at hX,

  -- rcases hX with ⟨X, ⟨hX₁, hX₂⟩, rfl⟩,
  -- rcases hS X hX₁ with ⟨Y, hY₁, hY₂, hY₃⟩,
  -- -- refine ⟨sorry, _, _⟩,
  -- simp only [exists_prop, induct_down, flatten_triangulation, lower_triangulation, set.mem_sep_eq,
  --   set.mem_image, exists_exists_and_eq_and],

  -- -- simp only [induct_down],

end

lemma subset_iff_eq_or_ssubset {α : Type*} {s t : finset α} :
  s ⊆ t ↔ s = t ∨ s ⊂ t :=
begin
  split,
  { intro h,
    rw finset.ssubset_iff_of_subset h,
    apply or.imp _ _ (t \ s).eq_empty_or_nonempty,
    { intro q,
      rw finset.sdiff_eq_empty_iff_subset at q,
      apply finset.subset.antisymm h q },
    { rintro ⟨x, hx⟩,
      simp only [finset.mem_sdiff] at hx,
      exact ⟨x, hx.1, hx.2⟩ } },
  { rintro (rfl | ss),
    { apply finset.subset.refl },
    { apply ss.1 } }
end

noncomputable def good_pairs {S : triangulation (std_simplex (fin (m+1)))} (hS : S.finite)
  (f : (fin (m + 1) → ℝ) → fin (m + 1)) :
  finset (finset (fin (m+1) → ℝ) × finset (fin (m+1) → ℝ)) :=
((S.faces_finset hS).product (S.faces_finset hS)).filter
      (λ (XY : finset _ × finset _),
          XY.2.card = m ∧ XY.1.card = m+1 ∧ XY.2.image f = finset.univ.erase 0 ∧ XY.2 ⊆ XY.1)

@[simp]
lemma mem_good_pairs {S : triangulation (std_simplex (fin (m+1)))} (hS : S.finite)
  {f} (X Y : finset _) :
  (X,Y) ∈ good_pairs hS f ↔
      X ∈ S.faces
    ∧ Y ∈ S.faces
    ∧ Y.card = m
    ∧ X.card = m+1
    ∧ Y.image f = finset.univ.erase 0
    ∧ Y ⊆ X :=
begin
  simp [good_pairs, and_assoc],
end

noncomputable def panchromatic_pairs {S : triangulation (std_simplex (fin (m+1)))} (hS : S.finite)
  (f : (fin (m+1) → ℝ) → (fin (m+1))) :=
(good_pairs hS f).filter (λ (XY : _ × _), panchromatic f XY.1)

noncomputable def almost_panchromatic_pairs {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) (f : (fin (m+1) → ℝ) → (fin (m+1))) :=
(good_pairs hS f).filter (λ (XY : _ × _), XY.1.image f = finset.univ.erase 0)

noncomputable def almost_panchromatic_simplices {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) (f : (fin (m+1) → ℝ) → (fin (m+1))) :=
(S.faces_finset hS).filter (λ (X : finset _), X.card = m+1 ∧ X.image f = finset.univ.erase 0)

lemma almost_panchromatic_pairs_card_eq_twice {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) (f : (fin (m+1) → ℝ) → (fin (m+1))) :
  (almost_panchromatic_pairs hS f).card = (almost_panchromatic_simplices hS f).card * 2 :=
begin
  have H : ∀ x ∈ almost_panchromatic_pairs hS f, prod.fst x ∈ almost_panchromatic_simplices hS f,
  { rintro ⟨X, Y⟩ h,
    simp only [almost_panchromatic_pairs, mem_good_pairs, finset.mem_filter] at h,
    simp only [almost_panchromatic_simplices, mem_faces_finset, finset.mem_filter],
    tauto },
  rw finset.card_eq_sum_card_fiberwise H,
  apply finset.sum_const_nat,
  rintro X hX,
  simp only [almost_panchromatic_simplices, mem_faces_finset, finset.mem_filter] at hX,
  rcases hX with ⟨hX₁, hX₂, hX₃⟩,
  dsimp,
  suffices : ((almost_panchromatic_pairs hS f).filter (λ (x : _ × _), x.fst = X)).card =
    (X.filter (λ x, ∃ y ∈ X, x ≠ y ∧ f x = f y)).card,
  { rw this,
    apply non_inj_card_two f,
    rw hX₂,
    rw hX₃,
    simp [finset.card_erase_of_mem] },
  apply (finset.card_congr (λ x hx, (X, X.erase x)) _ _ _).symm,
  { rintro x hx,
    dsimp,
    simp only [exists_prop, finset.mem_filter] at hx,
    simp only [almost_panchromatic_pairs, and_true, eq_self_iff_true, mem_good_pairs,
      finset.mem_filter, hX₃, true_and, hX₂, hX₁, finset.card_erase_of_mem, hx.1, nat.pred_succ,
      finset.erase_subset],
    rw ← hX₃,
    refine ⟨S.down_closed _ hX₁ _ (finset.erase_subset _ _), _⟩,
    conv_rhs {rw ←finset.insert_erase hx.1},
    rw finset.image_insert,
    rw finset.insert_eq_of_mem,
    rw finset.mem_image,
    simp only [exists_prop, finset.mem_erase],
    simpa [and_assoc, and_comm (_ ∈ X), ←ne.def, ne_comm, eq_comm] using hx.2 },
  { rintro a b ha hb h,
    dsimp at h,
    injection h,
    apply erase_inj_on _ (finset.filter_subset _ _ ha) ‹X.erase a = X.erase b› },
  { rintro ⟨X', Y⟩ hX,
    dsimp [←ne.def],
    simp only [finset.mem_filter, almost_panchromatic_pairs, mem_good_pairs] at hX,
    rcases hX with ⟨⟨⟨_, _, _, _, _, _⟩, _⟩, rfl⟩,
    have : (X' \ Y).nonempty,
    { rw [←finset.card_pos, finset.card_sdiff ‹Y ⊆ X'›, ‹X'.card = m + 1›, ‹Y.card = m›],
      simp only [nat.zero_lt_one, nat.add_sub_cancel_left] },
    rcases this with ⟨z, hz⟩,
    simp only [finset.mem_sdiff] at hz,
    rcases hz,
    simp only [true_and, exists_prop, prod.mk.inj_iff, eq_self_iff_true, finset.mem_filter],
    refine ⟨z, ⟨‹_›, _⟩, _⟩,
    { have : f z ∈ Y.image f,
      { rw [‹Y.image f = _›, ←‹X'.image f = _›],
        apply finset.mem_image_of_mem f ‹z ∈ X'› },
      rcases finset.mem_image.1 this with ⟨y, hy₁, hy₂⟩,
      refine ⟨y, ‹Y ⊆ X'› ‹y ∈ Y›, (ne_of_mem_of_not_mem ‹y ∈ Y› ‹z ∉ Y›).symm, ‹f y = f z›.symm⟩ },
    { symmetry,
      apply finset.eq_of_subset_of_card_le,
      simp only [subset_erase_iff, ‹Y ⊆ X'›, ‹z ∉ Y›, not_false_iff, and_self],
      rw [finset.card_erase_of_mem ‹_ ∈ _›, ‹X'.card = _›, nat.pred_succ, ‹Y.card = m›] } }
end

lemma panchromatic_splits {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) {f : (fin (m+1) → ℝ) → (fin (m+1))} :
  panchromatic_pairs hS f ∪ almost_panchromatic_pairs hS f = good_pairs hS f :=
begin
  rw [panchromatic_pairs, almost_panchromatic_pairs, ←finset.filter_or, finset.filter_true_of_mem],
  rintro ⟨X,Y⟩ h,
  simp only [mem_good_pairs] at h,
  rcases h with ⟨hX₁, hY₁, hY₂, hX₂, hY₃, YX⟩,
  have : finset.univ.erase 0 ⊆ X.image f,
  { rw ← hY₃,
    apply finset.image_subset_image,
    apply YX },
  rw subset_iff_eq_or_ssubset at this,
  cases this,
  { right,
    apply this.symm },
  { left,
    apply finset.eq_of_subset_of_card_le,
    apply finset.subset_univ,
    simp only [finset.card_fin],
    rw nat.succ_le_iff,
    apply lt_of_le_of_lt _ (finset.card_lt_card this),
    rw finset.card_erase_of_mem (finset.mem_univ _),
    simp only [finset.card_fin, nat.pred_succ] }
end

lemma disjoint_split {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) {f : (fin (m+1) → ℝ) → (fin (m+1))} :
  disjoint (panchromatic_pairs hS f) (almost_panchromatic_pairs hS f) :=
begin
  rw finset.disjoint_left,
  simp only [panchromatic_pairs, almost_panchromatic_pairs, and_imp, prod.forall, not_and,
    mem_good_pairs, finset.mem_filter],
  rintro X Y - - - - - - (h : _ = _) - - - - - - t,
  rw h at t,
  have : (0 : fin (m+1)) ∉ finset.univ,
  { intro q,
    rw t at q,
    rw finset.mem_erase at q,
    apply q.1 rfl },
  simpa using this
end

-- lemma image_subset_image_iff {α β : Type*}
--   [decidable_eq α] [decidable_eq β] (s t : finset α)
--   {f : α → β} : s.image f ⊆ t.image f → s ⊆ t :=
-- begin
--   rintro h x hx,
--   have : f x ∈ t.image f,
--   sorry,
--   simp at this,

--   -- refine ⟨_, finset.subset_image _⟩,

--   -- refine (iff.symm $ iff.intro (image_subset f) $ assume h, _),
--   -- rw [← preimage_image_eq s hf, ← preimage_image_eq t hf],
--   -- exact preimage_mono h
-- end

lemma subset_erase_iff {α : Type*} [decidable_eq α] (x : α) {s t : finset α} :
  s ⊆ t.erase x ↔ s ⊆ t ∧ x ∉ s :=
⟨λ h, ⟨finset.subset.trans h (finset.erase_subset x t), λ q, by simpa using h q⟩,
 λ ⟨h₁, h₂⟩ y hy, finset.mem_erase_of_ne_of_mem (ne_of_mem_of_not_mem hy h₂) (h₁ hy)⟩

-- lemma sum_mul {α β : Type*} [add_comm_monoid β] {s : finset α} (b : β) (f : α → β) :
--   ∑ x in s, b * f x = _ :=
-- begin
-- end

def plane : affine_subspace ℝ E :=
{ carrier := {X | ∑ i, X i = 1},
  smul_vsub_vadd_mem :=
  begin
    rintro c p₁ p₂ p₃ (hp₁ hp₂ hp₃ : _ = _),
    simp [finset.sum_add_distrib, ←finset.mul_sum, hp₁, hp₂, hp₃],
  end }

lemma obvious {m : ℕ} : ∑ (i : fin m), (0 : fin m → ℝ) i = 1 → false :=
begin
  simp,
end

lemma better_size_bound {X : finset E}
  (hX₁ : affine_independent ℝ (λ p, p : (X : set E) → E))
  (hX₂ : ∀ x ∈ X, x ∈ std_simplex (fin m)) :
  X.card ≤ m :=
begin
  cases nat.eq_or_lt_of_le (size_bound hX₁),
  { have card_eq : fintype.card (X : set E) = finite_dimensional.findim ℝ (fin m → ℝ) + 1,
    { simp [h] },
    have : affine_span ℝ (X : set E) = ⊤,
    { convert affine_span_eq_top_of_affine_independent_of_card_eq_findim_add_one hX₁ card_eq,
      simp },
    have zero_mem : (0 : E) ∈ affine_span ℝ (X : set E),
    { rw this,
      apply affine_subspace.mem_top },
    have : (X : set E) ≤ (↑plane : set E),
    { rintro x hx,
      rw affine_subspace.mem_coe,
      apply (hX₂ _ hx).2 },
    rw ←((affine_subspace.gi ℝ (fin m → ℝ) (fin m → ℝ)).gc (X : set E) plane) at this,
    have q : _ = _ := this zero_mem,
    apply (obvious q).elim },
  rwa ← nat.lt_succ_iff,
end

lemma card_eq_of_panchromatic {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) (f : (fin (m+1) → ℝ) → (fin (m+1))) {X} (hX : X ∈ S.faces)
  (hf : panchromatic f X) :
  X.card = m+1 :=
le_antisymm
  (better_size_bound (S.indep X hX) (λ x hx, face_subset hX hx))
  begin
    change _ = _ at hf,
    have : (X.image f).card ≤ X.card := finset.card_image_le,
    simpa [hf] using this,
  end

lemma erase_image_subset_image_erase {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α → β)
  (s : finset α) (a : α) :
  (s.image f).erase (f a) ⊆ finset.image f (s.erase a) :=
begin
  intro b,
  simp only [and_imp, exists_prop, finset.mem_image, exists_imp_distrib, finset.mem_erase],
  rintro hb x hx rfl,
  exact ⟨_, ⟨ne_of_apply_ne f hb, hx⟩, rfl⟩,
end

lemma panchromatic_pairs_card_eq_panchromatic_card {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) (f : (fin (m+1) → ℝ) → (fin (m+1))) :
  (panchromatic_pairs hS f).card = ((S.faces_finset hS).filter (panchromatic f)).card :=
begin
  apply finset.card_congr _ _ _ _,
  { rintro X hX,
    apply X.1 },
  { rintro ⟨X, Y⟩ hX,
    simp only [panchromatic_pairs, mem_good_pairs, finset.mem_filter] at hX,
    simp only [mem_faces_finset, finset.mem_filter],
    tauto },
  { rintro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ h₁ h₂ (rfl : X₁ = X₂),
    simp only [panchromatic_pairs, finset.mem_filter, mem_good_pairs, and_assoc] at h₁ h₂,
    rcases h₁ with ⟨X₁S, Y₁S, Y₁c, hX₁, hY₁, hY₁X, hX₂ : _ = _⟩,
    rcases h₂ with ⟨-, Y₂S, Y₂c, -, hY₂, hY₂X, -⟩,
    ext1,
    { refl },
    change Y₁ = Y₂,
    have : ∃ x ∈ X₁, f x = 0,
    { suffices : (0 : fin (m+1)) ∈ X₁.image f,
      { simpa using this },
      rw hX₂,
      simp },
    rcases this with ⟨x, hx₁, hx₂⟩,
    have : x ∉ Y₁,
    { intro q,
      simpa [‹f x = 0›, hY₁, fin.succ_ne_zero] using finset.mem_image_of_mem f q },
    have : Y₁ ⊆ X₁.erase x,
    { rw subset_erase_iff,
      exact ⟨‹Y₁ ⊆ X₁›, ‹x ∉ Y₁›⟩ },
    have : Y₁ = X₁.erase x,
    { apply finset.eq_of_subset_of_card_le ‹Y₁ ⊆ X₁.erase x›,
      simp [finset.card_erase_of_mem ‹x ∈ X₁›, ‹X₁.card = m+1›, ‹Y₁.card = m›] },
    have : x ∉ Y₂,
    { intro q,
      simpa [‹f x = 0›, hY₂, fin.succ_ne_zero] using finset.mem_image_of_mem f q },
    have : Y₂ ⊆ X₁.erase x,
    { rw subset_erase_iff,
      exact ⟨‹Y₂ ⊆ X₁›, ‹x ∉ Y₂›⟩ },
    have : Y₂ = X₁.erase x,
    { apply finset.eq_of_subset_of_card_le ‹Y₂ ⊆ X₁.erase x›,
      simp [finset.card_erase_of_mem ‹x ∈ X₁›, ‹X₁.card = m+1›, ‹Y₂.card = m›] },
    rw [‹Y₁ = X₁.erase x›, ‹Y₂ = X₁.erase x›] },
  { simp_rintro X hX only [finset.mem_filter, mem_faces_finset],
    have : ∃ x ∈ X, f x = 0,
    { suffices : (0 : fin (m+1)) ∈ X.image f,
      { simpa using this },
      rw (show _ = _, from hX.2),
      simp },
    rcases this with ⟨x, hx₁, hx₂⟩,
    refine ⟨⟨X, X.erase x⟩, _, rfl⟩,
    have Xc : finset.card X = m+1 := card_eq_of_panchromatic hS f hX.1 hX.2,
    simp only [panchromatic_pairs, hX.1, hX.2, finset.erase_subset, and_true, true_and, Xc,
      finset.card_erase_of_mem hx₁, eq_self_iff_true, mem_good_pairs, finset.mem_filter,
      nat.pred_succ],
    refine ⟨S.down_closed _ hX.1 _ (finset.erase_subset _ _), _⟩,
    symmetry,
    apply finset.eq_of_subset_of_card_le,
    { rw ←(show finset.image f X = finset.univ, from hX.2),
      rw ←hx₂,
      apply erase_image_subset_image_erase f X x },
    rw finset.card_erase_of_mem (finset.mem_univ _),
    simp only [finset.card_fin, nat.pred_succ],
    apply le_trans finset.card_image_le,
    rw finset.card_erase_of_mem hx₁,
    rw Xc,
    simp, }
end

theorem strong_sperner (S : triangulation (std_simplex (fin (m+1)))) (hS : S.finite)
  {f} (hf : is_sperner_colouring S f) (hS₂ : is_homogeneous (m+1) S):
  odd ((S.faces_finset hS).filter (panchromatic f)).card :=
begin
  tactic.unfreeze_local_instances,
  induction m with n ih generalizing f,
  { apply strong_sperner_zero _ },
  let f' : (fin (n + 1) → ℝ) → fin (n + 1),
  { intro x,
    apply fin.pred_above 0 (f (matrix.vec_cons 0 x)) },
  have hf' : is_sperner_colouring (induct_down S) f',
  { rintro x i hx hi,
    simp only [induct_down, flatten_triangulation, lower_triangulation, triangulation.points,
      set.mem_bUnion_iff, exists_prop, set.mem_sep_eq, finset.mem_image, set.mem_image,
      finset.mem_coe, finset.mem_image, exists_exists_and_eq_and] at hx,
    rcases hx with ⟨X, ⟨hX₁, hX₂⟩, y, hy, rfl⟩,
    rw matrix.vec_tail at hi,
    dsimp at hi,
    have : y ∈ S.points,
    { apply set.mem_bUnion, apply hX₁, apply hy },
    have : f y ≠ i.succ,
    { apply hf _ _ _ hi,
      apply this },
    change fin.pred_above _ _ ≠ _,
    have : y 0 = 0,
    { apply hX₂,
      apply hy },
    have : matrix.vec_cons 0 (matrix.vec_tail y) = y,
    { rw ← this,
      exact matrix.cons_head_tail y },
    rw this,
    have := ‹is_sperner_colouring S f› _ _ ‹y ∈ S.points› ‹y 0 = 0›,
    rw fin.pred_above_zero this,
    intro q,
    apply ‹f y ≠ i.succ›,
    rw ← q,
    simp },
  specialize ih (induct_down S) (induct_down_finite _ hS) _ hf',


  -- want that the number `x` of (n+2)-sets which are coloured by all n+2 colours is odd
  -- let `y` be the (n+2)-sets coloured by the colours 1..(n+1)
  -- let `p` be the (n+1)-sets coloured by 1..(n+1) on the 0-boundary
  -- let `q` be the (n+1)-sets coloured by 1..(n+1) not on the 0-boundary

  -- we know `p` is odd
  -- we know p + 2 q = x + 2 y
  -- therefore `x` is odd.

  sorry
end

end affine

-- brb
