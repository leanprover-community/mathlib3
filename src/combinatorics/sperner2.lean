import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import geometry.euclidean.basic
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.finite_dimensional
import analysis.convex.basic
import analysis.convex.mwe2
import data.nat.parity

lemma subset_iff_inter_eq_left {ι : Type*} {X Y : finset ι} (h : Y ⊆ X) [decidable_eq ι] :
  X ∩ Y = Y :=
begin
  ext t,
  simp only [and_iff_right_iff_imp, finset.mem_inter],
  apply h
end

open_locale classical affine

namespace affine

variables {m : ℕ}
local notation `E` := fin m → ℝ

-- def simplex.point_set {n : ℕ} (S : affine.simplex ℝ E n) : set E :=
-- set.range S.points

structure triangulation (s : set E) :=
(faces : set (finset E))
(indep : ∀ (X ∈ faces), affine_independent ℝ (λ p, p : (X : set E) → E))
(down_closed : ∀ (X ∈ faces) Y, Y ⊆ X → Y ∈ faces)
(covering : s = ⋃ (X ∈ faces), convex_hull ↑X)
(disjoint : ∀ (X Y ∈ faces), convex_hull ↑X ∩ convex_hull ↑Y ⊆ convex_hull (X ∩ Y : set E))

variables {s : set E}

lemma kenny (M : Type*) [add_comm_group M] [vector_space ℝ M] (s : affine_subspace ℝ M) :
  convex (s : set M) :=
λ x y hxs hys a b ha hb hab,
calc a • x + b • y = b • (y - x) + x : convex.combo_to_vadd hab
               ... ∈ s : s.2 _ hys hxs hxs

lemma convex_hull_subset_span_points (X : set E) :
  convex_hull X ⊆ affine_span ℝ X :=
begin
  apply convex_hull_min,
  apply subset_affine_span,
  apply kenny,
end

lemma thingy {X Y : set E} (hY₁ : Y ⊆ X) : (λ p, p : X → E) '' {t : X | ↑t ∈ Y} = Y :=
begin
  ext y,
  specialize @hY₁ y,
  simpa [←and_assoc],
end

open_locale big_operators

lemma center_mass_eq_affine_combination {ι : Type*} {t : finset ι} {p : ι → E} {w : ι → ℝ}
  (hw₂ : ∑ i in t, w i = 1) :
  finset.affine_combination t p w = finset.center_mass t w p :=
begin
  rw finset.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one _ w _ hw₂ (0 : E),
  simp only [vsub_eq_sub, add_zero, finset.weighted_vsub_of_point_apply, vadd_eq_add, sub_zero],
  rw finset.center_mass_eq_of_sum_1 _ _ hw₂,
end

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
--   intros t w z hw₁ hz hw₂,
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
--     intros c,
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


lemma disjoint_convex_hulls {X : finset E} (hX : affine_independent ℝ (λ p, p : (X : set E) → E))
  {Y₁ Y₂ : finset E} (hY₁ : Y₁ ⊆ X) (hY₂ : Y₂ ⊆ X) :
  convex_hull (Y₁ : set E) ∩ convex_hull (Y₂ : set E) ⊆ convex_hull (Y₁ ∩ Y₂ : set E) :=
begin
  rintro x ⟨hx₁, hx₂⟩,
  rw ←finset.coe_inter,
  rw finset.convex_hull_eq at hx₁ hx₂,
  rcases hx₁ with ⟨w₁, h₁w₁, h₂w₁, h₃w₁⟩,
  rcases hx₂ with ⟨w₂, h₁w₂, h₂w₂, h₃w₂⟩,
  rw finset.center_mass_eq_of_sum_1 _ _ h₂w₁ at h₃w₁,
  rw finset.center_mass_eq_of_sum_1 _ _ h₂w₂ at h₃w₂,
  dsimp at h₃w₁,
  dsimp at h₃w₂,
  rw affine_independent_def at hX,
  let w : E → ℝ,
  { intro x,
    apply (if x ∈ Y₁ then w₁ x else 0) - (if x ∈ Y₂ then w₂ x else 0) },
  have h₁w : ∑ (i : (X : set E)), w i = 0,
  { rw thing,
    rw finset.sum_sub_distrib,
    rw ←finset.sum_filter,
    rw finset.filter_mem_eq_inter,
    rw ←finset.sum_filter,
    rw finset.filter_mem_eq_inter,
    rw subset_iff_inter_eq_left hY₁,
    rw subset_iff_inter_eq_left hY₂,
    rw h₂w₁,
    rw h₂w₂,
    simp only [sub_self] },
  have h₂w : finset.univ.weighted_vsub (λ (p : (X : set E)), (p : E)) (λ (i : (X : set E)), w i) = (0 : E),
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ h₁w (0 : E),
    rw finset.weighted_vsub_of_point_apply,
    simp only [vsub_eq_sub, sub_zero],
    rw thing X (λ i, w i • i),
    dsimp only,
    change ∑ i in X, (_ - _) • i = 0,
    simp_rw sub_smul,
    simp_rw ite_smul,
    simp_rw zero_smul,
    rw [finset.sum_sub_distrib, ←finset.sum_filter, finset.filter_mem_eq_inter,
      subset_iff_inter_eq_left hY₁, ←finset.sum_filter, finset.filter_mem_eq_inter,
      subset_iff_inter_eq_left hY₂, h₃w₁, h₃w₂, sub_self] },
  specialize hX finset.univ _ h₁w h₂w,
  simp only [finset.mem_univ, set_coe.forall, forall_true_left] at hX,
  rw finset.convex_hull_eq,
  have t₁ : ∀ x, x ∈ Y₁ → x ∉ Y₂ → w₁ x = 0,
  { intros x hx₁ hx₂,
    have : ite (x ∈ Y₁) (w₁ x) 0 - ite (x ∈ Y₂) (w₂ x) 0 = 0 := hX x _,
    rw if_pos hx₁ at this,
    rw if_neg hx₂ at this,
    rw sub_zero at this,
    apply this,
    simp only [finset.mem_coe],
    apply hY₁,
    apply hx₁ },
  have h₄w₁ : ∑ (y : fin m → ℝ) in Y₁ ∩ Y₂, w₁ y = 1,
  { rw [finset.sum_subset (finset.inter_subset_left Y₁ Y₂), h₂w₁],
    simp_intros x hx₁ hx₂,
    specialize hx₂ hx₁,
    apply t₁,
    apply hx₁,
    apply hx₂ },
  refine ⟨w₁, _, h₄w₁, _⟩,
  { simp only [and_imp, finset.mem_inter],
    intros y hy₁ hy₂,
    apply h₁w₁,
    apply hy₁ },
  { rw finset.center_mass_eq_of_sum_1 _ _ h₄w₁,
    dsimp only [id.def],
    rw [finset.sum_subset (finset.inter_subset_left Y₁ Y₂), h₃w₁],
    simp_intros x hx₁ hx₂,
    left,
    apply t₁,
    apply hx₁,
    apply hx₂,
    apply hx₁ },
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
      intros X hX hx,
      refine ⟨X, ⟨X, hX, set.subset.refl _⟩, hx⟩ },
    { simp only [and_imp, exists_imp_distrib],
      intros X Y YS XY hx,
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
  intros i j hi,
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
    simp_intros X Y hX hY,
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
  intros x hx,
  rw S.covering,
  apply set.mem_bUnion hX hx,
end

lemma face_subset {X} (hX : X ∈ S.faces) : ↑X ⊆ s :=
begin
  intros x hx,
  rw S.covering,
  apply set.mem_bUnion hX,
  apply subset_convex_hull,
  apply hx
end

lemma points_subset : S.points ⊆ s :=
begin
  intros x hx,
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
  { intros y hy,
    exact mul_nonneg (hw₀ y hy) (hX (z y) (hz y hy)) },
  rw finset.sum_eq_zero_iff_of_nonneg this at x_zero,
  dsimp only at x_zero,
  rw convex_hull_eq.{37},
  refine ⟨ι, t.filter (λ i, w i ≠ 0), w, z, _, _, _, _⟩,
  { simp_intros i hi only [finset.mem_filter],
    apply hw₀ _ hi.1 },
  { rw ←hw₁,
    exact finset.sum_filter_ne_zero },
  { simp_intros i hi only [finset.mem_filter, set.mem_set_of_eq],
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
    intros X hX,
    simp only [set.mem_sep_eq] at hX,
    apply S.indep _ hX.1,
  end,
  down_closed :=
  begin
    intros X hX Y YX,
    simp only [set.mem_sep_eq] at hX ⊢,
    refine ⟨S.down_closed X hX.left Y YX, _⟩,
    intros x hx,
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
      intros y hy,
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
        { intros x hx,
          exact hX₁.2 x hx },
        intros x₁ x₂ hx₁ hx₂ a b ha hb q,
        simp only [set.mem_set_of_eq] at hx₁ hx₂ ⊢,
        simp [hx₁, hx₂] },
      apply this,
      apply hX₂ }
  end,
  disjoint :=
  begin
    intros X Y hX hY,
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
  { intros X hX,
    have := face_subset hX,
    rw std_simplex_one at this,
    intros x hx,
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
--   intros s w hw hs i hi,
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
  { intros a _,
    apply a.succ },
  { intros a ha,
    simp only [and_true, finset.mem_univ, finset.mem_erase],
    apply fin.succ_ne_zero },
  { intros a ha,
    symmetry,
    apply fin.cases_succ },
  { rintro a₁ a₂ _ _ h,
    apply fin.succ_injective,
    apply h },
  { intros b hb,
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
    intros X hX,
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
      intros y hY,
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
    { intros x hx y hy h,
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

lemma size_bound (S : triangulation s) {X : finset _} (hX : X ∈ S.faces) :
  X.card ≤ m+1 :=
begin
  cases X.eq_empty_or_nonempty,
  { simp [h] },
  rcases h with ⟨y, hy⟩,
  have y_mem : y ∈ (X : set (fin m → ℝ)) := hy,
  have Xy : (↑X \ {y}) = ((↑(X.erase y)) : set (fin m → ℝ)),
  { simp },
  have := S.indep X hX,
  rw @affine_independent_set_iff_linear_independent_vsub ℝ _ _ _ _ _ _ ↑X y y_mem at this,
  letI q : fintype ↥((λ (p : fin m → ℝ), p -ᵥ y) '' (↑X \ {y})),
  { apply set.fintype_image _ _,
    { apply_instance },
    rw Xy,
    exact finset_coe.fintype _ },
  have := finite_dimensional.fintype_card_le_findim_of_linear_independent this,
  simp only [vsub_eq_sub, finite_dimensional.findim_fin_fun, fintype.card_of_finset] at this,
  rw finset.card_image_of_injective at this,
  simp only [set.to_finset_card] at this,
  rw fintype.card_of_finset' (X.erase y) at this,
  rw finset.card_erase_of_mem hy at this,
  rw nat.pred_le_iff at this,
  exact this,
  simp [and_comm],
  intros p q h,
  simpa using h,
end

-- lemma contained_in_facet (S : triangulation s) {X} (hX : X ∈ S.faces) :
--   ∃ Y ∈ S.facets, X ⊆ Y :=
-- begin
--   sorry,
--   -- just keep chucking vertices in, must terminate.

--   -- let Z := {Y ∈ S.faces | X ⊆ Y},
--   -- have : X ∈ Z,
--   -- { apply set.mem_sep,
--   --   apply hX,
--   --   apply finset.subset.refl },
--   -- have : ∀ c, c ⊆ Z → zorn.chain (≤) c → ∀ (y ∈ c), (∃ ub ∈ Z, ∀ z ∈ c, z ≤ ub),
--   -- { intros c hc₁ hc₂ y hy,


--   -- },
--   -- have := zorn.zorn_partial_order₀ Z _ X ‹X ∈ Z›,
-- end

def is_homogeneous {m : ℕ} {s : set (fin m → ℝ)} (n : ℕ) (S : triangulation s) : Prop :=
∀ X ∈ S.facets, finset.card X = n
-- ∀ X ∈ S.faces, ∃ Y ∈ S.faces, X ⊆ Y ∧ finset.card Y = n

-- lemma is_homogeneous_induct_down (S : triangulation (std_simplex (fin (m+1))))
--   (hS : is_homogeneous (m+1) S) :
--   is_homogeneous m (induct_down S) :=
-- begin
--   intros X hX,
--   simp only [induct_down, triangulation.facets, flatten_triangulation, lower_triangulation,
--     and_imp, set.mem_sep_eq, set.mem_image, exists_imp_distrib] at hX,
--   rcases hX with ⟨⟨X, ⟨hX₂, hX₄⟩, rfl⟩, hX₃⟩,
--   have hX₁ : ∀ (Y ∈ S.faces), (∀ (i : fin (m+1) → ℝ), i ∈ Y → i 0 = 0) →
--     finset.image matrix.vec_tail X ⊆ finset.image matrix.vec_tail Y →
--     finset.image matrix.vec_tail X = finset.image matrix.vec_tail Y,
--   { intros Y hY₁ hY₂ hY₃,
--     apply hX₃ _ _ hY₁ hY₂ rfl hY₃ },
--   -- have := set.image_subset,
--   -- simp only [induct_down, flatten_triangulation, lower_triangulation, set.mem_image,
--   --   set.mem_sep_eq] at hX,

--   -- rcases hX with ⟨X, ⟨hX₁, hX₂⟩, rfl⟩,
--   -- rcases hS X hX₁ with ⟨Y, hY₁, hY₂, hY₃⟩,
--   -- -- refine ⟨sorry, _, _⟩,
--   -- simp only [exists_prop, induct_down, flatten_triangulation, lower_triangulation, set.mem_sep_eq,
--   --   set.mem_image, exists_exists_and_eq_and],

--   -- -- simp only [induct_down],

-- end

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
          XY.1.card = m+1 ∧ XY.2.image f = finset.univ.image fin.succ ∧ XY.2 ⊆ XY.1)

@[simp]
lemma mem_good_pairs {S : triangulation (std_simplex (fin (m+1)))} (hS : S.finite)
  {f} (X Y : finset _) :
  (X,Y) ∈ good_pairs hS f ↔
      X ∈ S.faces
    ∧ Y ∈ S.faces
    ∧ X.card = m+1
    ∧ Y.image f = finset.univ.image fin.succ
    ∧ Y ⊆ X :=
begin
  simp [good_pairs, and_assoc],
end

noncomputable def panchromatic_pairs {S : triangulation (std_simplex (fin (m+1)))} (hS : S.finite)
  (f : (fin (m+1) → ℝ) → (fin (m+1))) :=
(good_pairs hS f).filter (λ (XY : _ × _), panchromatic f XY.1)

noncomputable def almost_panchromatic_pairs {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) (f : (fin (m+1) → ℝ) → (fin (m+1))) :=
(good_pairs hS f).filter (λ (XY : _ × _), XY.1.image f = finset.univ.image fin.succ)

lemma panchromatic_splits {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) {f : (fin (m+1) → ℝ) → (fin (m+1))} :
  panchromatic_pairs hS f ∪ almost_panchromatic_pairs hS f = good_pairs hS f :=
begin
  rw [panchromatic_pairs, almost_panchromatic_pairs, ←finset.filter_or, finset.filter_true_of_mem],
  rintro ⟨X,Y⟩ h,
  simp only [mem_good_pairs] at h,
  rcases h with ⟨hX₁, hY₁, hX₂, hY₂, YX⟩,
  have : finset.univ.image fin.succ ⊆ X.image f,
  { rw ← hY₂,
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
    rw finset.card_image_of_injective _ (fin.succ_injective m),
    simp }
end

lemma inj_on_of_card_image_eq {α β : Type*} [decidable_eq β] {f : α → β} {s : finset α}
  (H : (s.image f).card = s.card) :
  ∀ (x y ∈ s), f x = f y → x = y :=
begin
  change (s.1.map f).erase_dup.card = s.1.card at H,
  have : (s.1.map f).erase_dup = s.1.map f,
  { apply multiset.eq_of_le_of_card_le,
    { apply multiset.erase_dup_le },
    rw H,
    simp only [multiset.card_map] },
  rw multiset.erase_dup_eq_self at this,
  rw multiset.nodup_iff_pairwise at this,


  -- cases s,
  -- dsimp at H,

end

#exit

theorem card_image_of_inj_on [decidable_eq β] {f : α → β} {s : finset α}
  (H : ∀x∈s, ∀y∈s, f x = f y → x = y) : card (image f s) = card s :=
by simp only [card, image_val_of_inj_on H, card_map]

lemma panchromatic_pairs_card_eq_panchromatic_card {S : triangulation (std_simplex (fin (m+1)))}
  (hS : S.finite) (f : (fin (m+1) → ℝ) → (fin (m+1))) :
  (panchromatic_pairs hS f).card = ((S.faces_finset hS).filter (panchromatic f)).card :=
begin
  apply finset.card_congr _ _ _ _,
  { intros X hX,
    apply X.1 },
  { rintro ⟨X, Y⟩ hX,
    simp only [panchromatic_pairs, mem_good_pairs, finset.mem_filter] at hX,
    simp only [mem_faces_finset, finset.mem_filter],
    tauto },
  { rintro ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ h₁ h₂ (rfl : X₁ = X₂),
    simp only [panchromatic_pairs, finset.mem_filter, mem_good_pairs, and_assoc] at h₁ h₂,
    ext1,
    { refl },
    change Y₁ = Y₂,
    have := finset.card_image_of_inj_on,
  }
end

#exit
theorem strong_sperner (S : triangulation (std_simplex (fin (m+1)))) (hS : S.finite)
  {f} (hf : is_sperner_colouring S f) :
  odd ((S.faces_finset hS).filter (panchromatic f)).card :=
begin
  tactic.unfreeze_local_instances,
  induction m with n ih generalizing f,
  { apply strong_sperner_zero _ },
  let f' : (fin (n + 1) → ℝ) → fin (n + 1),
  { intro x,
    apply fin.pred_above 0 (f (matrix.vec_cons 0 x)) },
  have hf' : is_sperner_colouring (induct_down S) f',
  { intros x i hx hi,
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
  specialize ih (induct_down S) (induct_down_finite _ hS) hf',
  let T : finset (finset (fin (n+2) → ℝ) × finset (fin (n+2) → ℝ)),
  { apply ((S.faces_finset hS).product (S.faces_finset hS)).filter
      (λ (XY : _ × _), finset.card XY.1 = n+2 ∧ finset.card XY.2 = n+1 ∧ XY.2 ⊆ XY.1) },
  have : ∀ X Y,
      (X,Y) ∈ T ↔ X ∈ S.faces ∧ Y ∈ S.faces ∧ finset.card X = n+2 ∧ finset.card Y = n+1 ∧ Y ⊆ X,
  { intros X Y,
    simp [mem_faces_finset, and_assoc] },
  let T' := T.filter (λ (XY : _ × finset _), XY.2.image f = finset.univ.image fin.succ),
  let x := ((S.faces_finset hS).filter (panchromatic f)).card,
  let T'x := T'.filter (λ (XY : _ × _), panchromatic f XY.1),
  let T'y := T'.filter (λ (XY : finset _ × _), XY.1.image f = finset.univ.image fin.succ),
  let p := (((induct_down S).faces_finset (induct_down_finite _ hS)).filter (panchromatic f')).card,
  have : T'x.card + T'y.card = T'.card,
  { rw ← finset.card_disjoint_union,
    { congr' 1,
      rw ←finset.filter_or,
      apply finset.filter_true_of_mem,
      rintro ⟨X, Y⟩ h,
      simp only [mem_faces_finset, and_assoc, finset.mem_filter, finset.mem_product] at h,
      rcases h with ⟨hX, hY, Xc, Yc, YX, Yf⟩,
      change X.image f = _ ∨ X.image f = _,
      have : finset.univ.image fin.succ ⊆ X.image f,
      { rw ← Yf,
        apply finset.image_subset_image,
        apply YX },
      rw subset_iff_eq_or_ssubset at this,
      cases this,
      { right,
        apply this_1.symm },
      { left,
        apply finset.eq_of_subset_of_card_le,
        apply finset.subset_univ,
        simp only [finset.card_fin],
        rw nat.succ_le_iff,
        have := finset.card_lt_card this_1,
      }


    }

  },

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
