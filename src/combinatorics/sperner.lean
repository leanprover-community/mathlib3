import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import combinatorics.simple_graph.basic
import geometry.euclidean.basic
import linear_algebra.affine_space.finite_dimensional
import analysis.convex.basic
import analysis.convex.mwe2
import data.nat.parity

open_locale classical

structure combinatorial_manifold (S : Type*) (r : ℕ) :=
(faces : finset (finset S)) -- A collection of subsets
(sizes : ∀ X ∈ faces, finset.card X = r+1) -- each with size `r+1`
(neighbouring : ∀ (Z : finset S), Z.card = r → (faces.filter (λ X, Z ⊆ X)).card ∈ ({0,2} : set ℕ))

structure combinatorial_manifold_with_boundary (S : Type*) (r : ℕ) :=
(faces : finset (finset S)) -- A collection of subsets
(sizes : ∀ X ∈ faces, finset.card X = r+1) -- each with size `r+1`
(neighbouring : ∀ (Z : finset S), Z.card = r → (faces.filter (λ X, Z ⊆ X)).card ≤ 2)

open_locale affine
namespace affine

-- variables {E : Type*} [add_comm_group E] [vector_space ℝ E]
-- variables {V : Type*} {P : Type*} [add_comm_group V] [module ℝ V]
-- variables [affine_space V P]
-- include V
variables {m : ℕ}
local notation `E` := fin m → ℝ

def simplex.point_set {n : ℕ} (S : affine.simplex ℝ E n) : set E :=
set.range S.points

structure triangulation (s : set E) (n : ℕ) :=
(faces : set (affine.simplex ℝ E n))
(covering : s = ⋃ (k ∈ faces), convex_hull (simplex.point_set k))
(disjoint : ∀ (X Y : affine.simplex ℝ E n), X ∈ faces → Y ∈ faces →
    convex_hull X.point_set ∩ convex_hull Y.point_set ⊆ convex_hull (X.point_set ∩ Y.point_set))
(different : ∀ (X Y : affine.simplex ℝ E n), X ∈ faces → Y ∈ faces → X.point_set = Y.point_set → X = Y)

def std_basis (n : ℕ) : fin n → fin n → ℝ :=
λ i, (linear_map.std_basis ℝ (λ i, ℝ) i) 1

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


-- lemma std_basis_apply (i : ι) (b : φ i) : std_basis R φ i b = update 0 i b :=
-- rfl

-- lemma coe_std_basis (i : ι) : ⇑(std_basis R φ i) = pi.single i :=
-- funext $ std_basis_apply R φ i

-- @[simp] lemma std_basis_same (i : ι) (b : φ i) : std_basis R φ i b i = b :=
-- by rw [std_basis_apply, update_same]

-- lemma std_basis_ne (i j : ι) (h : j ≠ i) (b : φ i) : std_basis R φ i b j = 0 :=
-- by rw [std_basis_apply, update_noteq h]; refl

def affine_std_simplex (n : ℕ) : affine.simplex ℝ (fin (n+1) → ℝ) n :=
{ points := std_basis (n+1),
  independent :=
  begin
    convert affine_independent_embedding_of_affine_independent (fin.succ_embedding _).to_embedding affine_indep,
    ext j x,
    simp only [function.comp_app, fin.coe_succ_embedding, rel_embedding.coe_fn_to_embedding, basis_with_zero_succ, std_basis],
  end }

def trivial {m : ℕ} :
  triangulation (std_simplex (fin (m+1))) m :=
{ faces := singleton (affine_std_simplex m),
  covering :=
  begin
    rw [set.bUnion_singleton, affine.simplex.point_set, affine_std_simplex],
    dsimp,
    rw ← convex_hull_basis_eq_std_simplex,
    rw std_basis,
    congr' 2,
    ext i j,
    rw linear_map.std_basis_apply,
    rw function.update,
    simp [eq_comm],
    convert rfl,
  end,
  disjoint := λ X Y hX hY,
  begin
    simp only [set.mem_singleton_iff] at hX hY,
    subst X, subst Y,
    simp,
    exact set.subset.refl _,
  end,
  different := λ X Y hX hY,
  begin
    simp only [set.mem_singleton_iff] at hX hY,
    subst X, subst Y,
    intro,
    refl,
  end }

lemma point_set_subset_convex_hull {s : set E} {n : ℕ} {S : triangulation s n}
  {X : simplex ℝ E n} (hX : X ∈ S.faces) :
  convex_hull X.point_set ⊆ s :=
begin
  rw S.covering,
  intros x,
  apply set.mem_bUnion hX,
end

variables {s : set E} {n : ℕ} (S : triangulation s n)

@[class] def triangulation.finite : Prop := S.faces.finite

noncomputable def triangulation.faces_finset [hS : S.finite] : finset (simplex _ _ _) :=
hS.to_finset

@[simp] lemma mem_faces_finset [S.finite] (X) :
  X ∈ S.faces_finset ↔ X ∈ S.faces :=
set.finite.mem_to_finset

def triangulation.points : set E :=
⋃ k ∈ S.faces, simplex.point_set k

def is_extreme (s : set E) (x : E) : Prop :=
x ∈ s ∧ ∀ (x₁ x₂ ∈ s), x ∈ segment x₁ x₂ → x = x₁ ∨ x = x₂

lemma extreme_sub {s t : set E} {x : E} (hx : is_extreme s x) (ht : x ∈ t) (st : t ⊆ s) :
  is_extreme t x :=
begin
  refine ⟨ht, _⟩,
  intros x₁ x₂ hx₁ hx₂ q,
  apply hx.2 x₁ x₂ (st hx₁) (st hx₂) q,
end

lemma remove_is_convex {s : set E} {x : E} (hx : is_extreme s x) (hs : convex s) :
  convex (s \ {x}) :=
begin
  rw convex_iff_segment_subset,
  rintro y₁ y₂ ⟨hy₁, y₁x : _ ≠ _⟩ ⟨hy₂, y₂x : _ ≠ _⟩,
  intros z hz,
  refine ⟨_, _⟩,
  apply hs.segment_subset hy₁ hy₂ hz,
  intro t,
  simp only [set.mem_singleton_iff] at t,
  subst t,
  rcases hx.2 _ _ hy₁ hy₂ hz with (rfl | rfl),
  { apply y₁x, refl },
  { apply y₂x, refl },
end

lemma is_extreme_convex_hull {s : set E} (hs : convex s) {x : E} (t : set E) (hx : is_extreme s x)
  (ts : t ⊆ s) :
  x ∈ convex_hull t → x ∈ t :=
begin
  intros ht,
  have : is_extreme (convex_hull t) x,
  { apply extreme_sub hx ht,
    apply convex_hull_min ts hs },
  have : ¬(t ⊆ convex_hull t \ {x}),
  { intro hq,
    apply (convex_hull_min hq (remove_is_convex this (convex_convex_hull _)) ht).2,
    simp },
  by_contra hq,
  apply this,
  intros z hz,
  refine ⟨subset_convex_hull _ hz, _⟩,
  intro b,
  apply hq,
  convert hz,
  exact b.symm,
end

lemma triangulation.mem_points_of_extreme (S : triangulation s n) {x : E}
  (hs : convex s) (hx : is_extreme s x) : x ∈ S.points :=
begin
  simp only [triangulation.points, set.mem_bUnion_iff, exists_prop],
  have : x ∈ s := hx.1,
  rw [S.covering, set.mem_bUnion_iff] at this,
  rcases this with ⟨X, hX₁, hX₂⟩,
  refine ⟨X, hX₁, _⟩,
  refine is_extreme_convex_hull hs X.point_set hx _ hX₂,
  apply set.subset.trans (subset_convex_hull X.point_set) (point_set_subset_convex_hull hX₁),
end

open set

-- lemma std_simplex_extreme_points (i : fin m) :
--   is_extreme (std_simplex (fin m)) (λ j, ite (i = j) 1 0) :=
-- begin
--   refine ⟨_, _⟩,
--   { convert ite_eq_mem_std_simplex i,
--     ext j,
--     split_ifs; refl },
--   { intros x₁ x₂ hx₁ hx₂ hs,

--     -- rw [segment_eq_image] at hs,
--     -- rcases hs with ⟨θ, hθ, q⟩,
--     -- dsimp at q,
--     -- rw function.funext_iff at q,
--     -- have := q i,
--     -- simp only [algebra.id.smul_eq_mul, if_true, pi.add_apply, eq_self_iff_true, pi.smul_apply] at this,
--     -- have := mem_Icc_of_mem_std_simplex hx₁ i,
--     -- sorry
--     }
-- end

lemma std_basis_mem_std_simplex (i : fin m) :
  linear_map.std_basis ℝ (λ i, ℝ) i 1 ∈ std_simplex (fin m) :=
begin
  convert ite_eq_mem_std_simplex i,
  ext j,
  split_ifs,
  { cases h,
    simp },
  { rw [linear_map.std_basis_ne],
    symmetry, apply h },
end

example {x y z : ℝ} (h : max x y = z) : x = z ∨ y = z :=
begin
  rw max at h,
  split_ifs at h;
  tauto
end

lemma extreme_zero_one {x y θ : ℝ}
  (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) (hθ : θ ∈ Icc (0:ℝ) 1)
  (t : (1 - θ) * x + θ * y = 1) : x = 1 ∨ y = 1 :=
begin
  have : (1 : ℝ) ∈ segment x y,
  { rw segment_eq_image,
    refine ⟨_, hθ, t⟩ },
  rw [segment_eq_interval, interval, set.mem_Icc] at this,
  have : max x y = 1 := le_antisymm (max_le hx.2 hy.2) this.2,
  rw max at this,
  split_ifs at this;
  tauto
end

lemma std_simplex_extreme_points' (i : fin m) :
  is_extreme (std_simplex (fin m)) (linear_map.std_basis ℝ _ i 1) :=
begin
  refine ⟨std_basis_mem_std_simplex _, _⟩,
  { intros x₁ x₂ hx₁ hx₂ hs,
    -- have := segment_image (linear_map.proj i : (fin m → ℝ) →ₗ[ℝ] _) x₁ x₂,
    -- dsimp at this,
    -- rw [segment_eq_image] at hs,
    -- rcases hs with ⟨θ, hθ, q⟩,
    -- dsimp at q,
    -- rw function.funext_iff at q,
    -- have := q i,
    -- simp only [algebra.id.smul_eq_mul, if_true, pi.add_apply, eq_self_iff_true, pi.smul_apply] at this,
    -- have := mem_Icc_of_mem_std_simplex hx₁ i,
    sorry }
end

def is_sperner_colouring (S : triangulation (std_simplex (fin (m+1))) m)
  (f : (fin (m+1) → ℝ) → fin (m+1)) : Prop :=
∀ (X : fin (m+1) → ℝ) i, X ∈ S.points → X i = 0 → f X ≠ i

def panchromatic (f : (fin (m+1) → ℝ) → fin (m+1)) (X : simplex ℝ _ m) :=
  function.bijective (f ∘ X.points)

lemma std_simplex_one : std_simplex (fin 1) = ({ ![(1 : ℝ)] }) :=
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

lemma strong_sperner_zero_aux (S : triangulation (std_simplex (fin 1)) 0) :
  S.faces = {simplex.mk_of_point ℝ ![1]} :=
begin
  have q : ∀ (X ∈ S.faces) x, simplex.points X x = ![(1:ℝ)],
  { intros X hX i,
    have : X.points i ∈ std_simplex (fin 1),
    { rw S.covering,
      apply set.mem_bUnion hX,
      apply subset_convex_hull,
      rw simplex.point_set,
      refine ⟨i, rfl⟩ },
    rw std_simplex_one at this,
    exact this },
  have z : ∀ (X ∈ S.faces), X = simplex.mk_of_point ℝ ![(1:ℝ)],
  { intros X hX,
    ext1 x,
    apply q,
    apply hX },
  have : ![(1 : ℝ)] ∈ std_simplex (fin 1),
  { rw std_simplex_one,
    apply set.mem_singleton },
  rw S.covering at this,
  simp only [exists_prop, mem_Union] at this,
  rcases this with ⟨X, hX₁, hX₂⟩,
  apply set.subset.antisymm,
  { intros Y hY,
    rw set.mem_singleton_iff,
    apply z _ hY },
  { rw set.singleton_subset_iff,
    rw ← z X hX₁,
    apply hX₁ }
end

lemma unique_bijective {α β : Type*} (f : α → β) [unique α] [unique β] : function.bijective f :=
begin
  convert equiv_of_unique_of_unique.bijective;
  apply_instance
end

theorem strong_sperner_zero (S : triangulation (std_simplex (fin 1)) 0) [S.finite]
  {f : (fin 1 → ℝ) → fin 1} :
  odd (S.faces_finset.filter (panchromatic f)).card :=
begin
  have : S.faces_finset.filter (panchromatic f) = {simplex.mk_of_point _ ![(1:ℝ)]},
  { ext X,
    simp only [mem_faces_finset, finset.mem_singleton, finset.mem_filter],
    rw strong_sperner_zero_aux,
    simp only [mem_singleton_iff, and_iff_left_iff_imp],
    rintro rfl,
    apply unique_bijective },
  rw this,
  simp
end

-- def lower (S : triangulation (std_simplex (fin (m+2))) (m+1)) :
--   triangulation (std_simplex (fin (m+1))) m :=
-- { faces := {X | ∃ (Y : simplex ℝ (fin (m+2) → ℝ) (m+1)) x, _ }

-- }
-- { faces := _ '' S.faces

-- }

def almost_panchromatic (f : (fin (m+1) → ℝ) → fin (m+1)) (X : simplex ℝ (fin (m+1) → ℝ) m) :
  Prop :=
finset.univ.image (f ∘ X.points) = finset.univ.image fin.succ
-- Might need to be fin.cast_succ...

def lowerable_simplex (X : simplex ℝ (fin (m+2) → ℝ) (m+1)) : Prop :=
m + 1 ≤ (finset.univ.filter (λ (t : fin (m+2)), X.points t 0 = 0)).card

-- m = 1: X is subset of triangle, X is a triangle
--

lemma true_of_filter_eq_self {α : Type*} [decidable_eq α] {s : finset α} {p : α → Prop}
  [decidable_pred p] (hs : s.filter p = s) : ∀ x ∈ s, p x :=
begin
  intros x hx,
  rw ←hs at hx,
  simp only [finset.mem_filter] at hx,
  apply hx.2,
end

example {m : ℕ}
  (points : fin (m + 1) → fin (m + 1) → ℝ) -- We have (m+1) points in R^(m+1)
  (independent : affine_independent ℝ points) -- which are affinely independent
  (on_simplex : ∀ (x : fin (m + 1)), points x ∈ std_simplex (fin (m + 1)))
      -- and they're all on the standard (m+1)-simplex
  (h3 : ∀ (x : fin (m + 1)), points x 0 = 0) : -- and they all have x₀ = 0
  false := -- is a contradiction
begin

end


lemma lowerable_simplex_eq {X : simplex ℝ (fin (m+2) → ℝ) (m+1)} :
  lowerable_simplex X ↔ m + 1 = (finset.univ.filter (λ (t : fin (m+2)), X.points t 0 = 0)).card :=
begin
  split,
  { intro h,
    apply le_antisymm h,
    by_contra,
    have : m + 2 ≤ (finset.univ.filter (λ (t : fin (m+2)), X.points t 0 = 0)).card,
    { simpa using h },
    conv_lhs at this {rw ← finset.card_fin (m+2)},
    have := finset.eq_of_subset_of_card_le (finset.filter_subset _ _) this,
    have := true_of_filter_eq_self this,
    simp only [finset.mem_univ, forall_true_left] at this,
    sorry },
  { intro h,
    apply le_of_eq h }
end

lemma lowerable_simplex.eq {X : simplex ℝ (fin (m+2) → ℝ) (m+1)}
  (hX : lowerable_simplex X) :
(finset.univ.filter (λ (t : fin (m+2)), X.points t 0 = 0)).card = m+1 :=
(lowerable_simplex_eq.1 hX).symm

def edge_of_std_simplex (m) : set (fin (m+1) → ℝ) :=
std_simplex (fin (m+1)) ∩ {x | x 0 = 0}

#check finset.sum_eq_zero_iff_of_nonneg

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
  { simp_intros i hi only [finset.mem_filter, mem_set_of_eq],
    refine ⟨hz i hi.1, _⟩,
    have := x_zero i hi.1,
    simp only [mul_eq_zero] at this,
    apply or.resolve_left this hi.2 },
  rw ← x_eq,
  exact finset.center_mass_filter_ne_zero z,
end

lemma face_point_set_subset {X : simplex ℝ E n} (fs : finset (fin (n+1))) (h : fs.card = m+1) :
  (X.face h).point_set ⊆ X.point_set :=
by simp [simplex.point_set]

def lower_triangulation (S : triangulation (std_simplex (fin (m+2))) (m+1)) :
  triangulation (edge_of_std_simplex (m+1)) m :=
{ faces := { X | ∃ (Y ∈ S.faces) (HY : lowerable_simplex Y), X = Y.face HY.eq},
  covering :=
  begin
    ext x,
    split,
    { simp_intros hx,
      simp only [←exists_and_distrib_right],
      rw exists_comm,
      simp only [←exists_and_distrib_left],

    },

    -- rw edge_of_std_simplex,
    -- conv_lhs {rw S.covering},
    -- ext x,
    -- simp only [exists_prop, mem_Union, mem_inter_eq, mem_set_of_eq],
    -- split,
    -- { simp only [and_imp, exists_imp_distrib],
    --   intros X hX hx₁ hx₂,
    --   have lX : lowerable_simplex X,
    --   { change _ ≤ _,

    --   },
    --   refine ⟨_, ⟨X, hX, lX, rfl⟩, _⟩,
    --   rw simplex.point_set,
    --   simp only [sep_univ, simplex.range_face_points, finset.coe_univ, finset.coe_filter],
    --   have : X.points '' {a : fin (m+2) | X.points a 0 = 0} = {y ∈ X.point_set | y 0 = 0},
    --   { ext y,
    --     simp only [simplex.point_set, mem_image, mem_sep_eq, mem_range, mem_set_of_eq],
    --     split,
    --     { rintro ⟨y, hy, rfl⟩,
    --       exact ⟨⟨y, rfl⟩, hy⟩ },
    --     { rintro ⟨⟨y, rfl⟩, hy⟩,
    --       exact ⟨y, hy, rfl⟩ } },
    --   rw this,
    --   apply convex_hull_ne_zero_points,
    --   { intros y hy, sorry, },
    --   { apply hx₂ },
    --   { apply hx₁ } },
    -- { simp only [and_imp, exists_imp_distrib],
    --   rintro _ X₂ hX₂ hX rfl hx,
    --   refine ⟨⟨X₂, hX₂, _⟩, _⟩,
    --   -- { apply convex_hull_mono _ hx,
    --   --   apply face_point_set_subset }
    -- }
  end,
  disjoint := sorry,
  different := sorry

}

theorem strong_sperner (S : triangulation (std_simplex (fin (m+1))) m) [S.finite]
  {f} (hf : is_sperner_colouring S f) :
  odd (S.faces_finset.filter (panchromatic f)).card :=
begin
  tactic.unfreeze_local_instances,
  induction m with n ih generalizing f,
  { apply strong_sperner_zero _ },
  have := S.faces_finset,
  have := S.faces_finset.filter lowerable_simplex,

end

theorem sperner (S : triangulation (std_simplex (fin (m+1))) m) [S.finite]
  {f} (hf : is_sperner_colouring S f) :
  ∃ (X : simplex _ _ _), X ∈ S.faces ∧ function.bijective (f ∘ X.points) :=
begin
  have := nat.odd_gt_zero (strong_sperner S hf),
  rw finset.card_pos at this,
  rcases this with ⟨X, hX⟩,
  simp only [mem_faces_finset, finset.mem_filter] at hX,
  refine ⟨X, hX⟩,
end

-- ∀ i, f (std_basis _ i) = i

-- Needs condition that boundary points match up
-- def bind {s : set E} {n : ℕ} (S : triangulation s n)
--   (T : Π f ∈ S.faces, triangulation (convex_hull (simplex.point_set f)) n) :
--   triangulation s n :=
-- { faces := ⋃ (f ∈ S.faces), (T _ H).faces,
--   covering :=
--   begin
--     ext x,
--     simp only [exists_prop, set.mem_Union],
--     split,
--     { intros hx,
--       rw S.covering at hx,
--       obtain ⟨_, ⟨Y, rfl⟩, ⟨_, ⟨hY₁, rfl⟩, hY₂ : x ∈ convex_hull _⟩⟩ := hx,
--       rw (T _ hY₁).covering at hY₂,
--       obtain ⟨_, ⟨Z, rfl⟩, ⟨_, ⟨hZ₁, rfl⟩, hZ₂ : _ ∈ convex_hull _⟩⟩ := hY₂,
--       exact ⟨_, ⟨_, _, hZ₁⟩, hZ₂⟩ },
--     { rintro ⟨X, ⟨Y, YS, XY⟩, xX⟩,
--       rw S.covering,
--       refine ⟨_, ⟨_, rfl⟩, _, ⟨YS, rfl⟩, _⟩,
--       rw (T _ YS).covering,
--       refine ⟨_, ⟨_, rfl⟩, _, ⟨XY, rfl⟩, xX⟩ }
--   end,
--   disjoint :=
--   begin
--     rintro X₁ X₂ hX₁ hX₂ x hx,
--     simp only [set.mem_Union, exists_prop, set.mem_inter] at hX₁ hX₂,
--     rcases hX₁ with ⟨Y₁, Y₁S, X₁TY₁⟩,
--     rcases hX₂ with ⟨Y₂, Y₂S, X₂TY₂⟩,
--     have ss : X₁.point_set ∩ X₂.point_set ⊆ convex_hull Y₁.point_set ∩ convex_hull Y₂.point_set,
--     { apply set.inter_subset_inter,
--       apply set.subset.trans (subset_convex_hull _) (point_set_subset_convex_hull X₁TY₁),
--       apply set.subset.trans (subset_convex_hull _) (point_set_subset_convex_hull X₂TY₂) },
--     have hx' : x ∈ convex_hull Y₁.point_set ∩ convex_hull Y₂.point_set,
--     { split,
--       { rw (T Y₁ Y₁S).covering,
--         simp only [set.mem_Union, exists_prop],
--         exact ⟨_, X₁TY₁, hx.1⟩ },
--       { rw (T Y₂ Y₂S).covering,
--         simp only [set.mem_Union, exists_prop],
--         exact ⟨_, X₂TY₂, hx.2⟩ } },
--     have := S.disjoint _ _ Y₁S Y₂S hx',
--     -- have : convex_hull (X₁.point_set ∩ X₂.point_set) ⊆ convex_hull (Y₁.point_set ∩ Y₂.point_set),
--     -- { refine convex_hull_min _ _,
--     --   -- apply convex_hull_min _ _,

--     --  },
--   end

-- }

-- (covering : ∀ x ∈ s, ∃ (y : simplex ℝ E n), y ∈ faces ∧ x ∈ convex_hull y.point_set)
-- (disjoint : ∀ (x ∈ ⋃ y ∈ faces, y.point_set) (y ∈ faces), x ∈ convex_hull (set.range (simplex.points y)) → _)

-- def main_one (k : ℕ) : combinatorial_manifold_with_boundary (fin 3 → ℝ) 2 :=
-- {

-- }

-- theorem sperner {r : ℕ} (K : combinatorial_manifold_with_boundary (fin r → ℝ) ):

-- import data.real.basic
-- import linear_algebra.affine_space.independent
-- import combinatorics.simple_graph.basic
-- import geometry.euclidean.basic
-- import linear_algebra.affine_space.finite_dimensional

-- open_locale classical affine

-- -- variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
-- --     [normed_add_torsor V P]

-- variables {V : Type*} [add_comm_group V] [vector_space ℝ V]

-- def simplex.span {n m : ℕ} (s : affine.simplex ℝ V n) : set V :=
-- convex_hull (set.range s.points)

-- structure simplicial_complex {m : ℕ} :=
-- (cells : Π (n : ℕ), finset (affine.simplex ℝ V n))

-- -- ()

-- -- structure abstract_simplicial_complex (S : Type*) :=
-- -- (faces : set (finset S))
-- -- (ne : ∀ X ∈ faces, finset.nonempty X)
-- -- (down_closed : ∀ (X ∈ faces) (Y ⊆ X), finset.nonempty Y → Y ∈ faces)

-- -- namespace abstract_simplicial_complex

-- -- variables {S : Type*} {K : abstract_simplicial_complex S}

-- -- def from_faces (K : set (finset S)) : abstract_simplicial_complex S :=
-- -- { faces := {X | X.nonempty ∧ ∃ Y ∈ K, X ⊆ Y},
-- --   ne := λ X hX, hX.1,
-- --   down_closed := λ X ⟨neX, Z, ZK, XZ⟩ Y YX neY, ⟨neY, _, ZK, trans YX XZ⟩ }

-- -- def vertex_set (K : abstract_simplicial_complex S) : set S := K.faces >>= λ v, v

-- -- lemma mem_vertex_set {v : S} : v ∈ K.vertex_set ↔ ∃ (X ∈ K.faces), v ∈ X :=
-- -- by simp [vertex_set]

-- -- lemma singleton_mem_face (v : S) (hv : v ∈ K.vertex_set) : {v} ∈ K.faces :=
-- -- K.down_closed
-- --   (classical.some (mem_vertex_set.1 hv))
-- --   (classical.some (classical.some_spec (mem_vertex_set.1 hv)))
-- --   _
-- --   (by { rw finset.singleton_subset_iff,
-- --         apply classical.some_spec (classical.some_spec (mem_vertex_set.1 hv)) })
-- --   (finset.singleton_nonempty v)

-- -- lemma face_subset_vertex_set {X : finset S} (hX : X ∈ K.faces) {x : S} (hx : x ∈ X) :
-- --   x ∈ K.vertex_set :=
-- -- mem_vertex_set.2 ⟨X, hX, hx⟩

-- -- def facets (K : abstract_simplicial_complex S) : set (finset S) :=
-- -- {T | T ∈ K.faces ∧ ∀ T' ∈ K.faces, T ⊆ T' → T = T'}

-- -- noncomputable def dimension (K : abstract_simplicial_complex S) : enat :=
-- -- Sup ((λ T, ↑(finset.card T - 1)) '' K.faces)

-- -- def finite (K : abstract_simplicial_complex S) : Prop := K.faces.finite

-- -- lemma finite_iff_vertex_set_finite : K.finite ↔ K.vertex_set.finite :=
-- -- begin
-- --   split,
-- --   { intro h,
-- --     apply set.finite_bUnion h,
-- --     intros a ha,
-- --     exact finset.finite_to_set a },
-- --   { intro h,
-- --     apply h.to_finset.powerset.finite_to_set.subset,
-- --     intros X hX,
-- --     simp only [finset.mem_powerset, finset.mem_coe],
-- --     intros x hx,
-- --     simp [face_subset_vertex_set hX hx] }
-- -- end

-- -- def skeleton (K : abstract_simplicial_complex S) (d : ℕ) : abstract_simplicial_complex S :=
-- -- { faces := { X | X ∈ K.faces ∧ X.card - 1 ≤ d },
-- --   ne := λ X hX, K.ne _ hX.1,
-- --   down_closed :=
-- --     λ X hX Y YX hY,
-- --      ⟨K.down_closed _ hX.1 _ YX hY,
-- --       le_trans (nat.sub_le_sub_right (finset.card_le_of_subset YX) 1) hX.2⟩ }

-- -- lemma skeleton_dimension {d : ℕ} : (K.skeleton d).dimension ≤ d :=
-- -- begin
-- --   change Sup _ ≤ _,
-- --   rw Sup_le_iff,
-- --   rintro a ⟨X, hX, rfl⟩,
-- --   norm_cast,
-- --   apply hX.2,
-- -- end

-- -- def neighbours (K : abstract_simplicial_complex S) (X : finset S) : set (finset S) :=
-- -- {Y | Y ∈ K.faces ∧ Y ⊆ X ∧ Y.card = X.card + 1}



-- -- def pure (K : abstract_simplicial_complex S) : Prop :=
-- -- ∀ X Y ∈ K.facets, finset.card X = finset.card Y

-- -- def just_graphs : {K : abstract_simplicial_complex S // K.dimension ≤ 1} ≃ simple_graph S :=
-- -- { to_fun := λ K, simple_graph.from_rel (λ (x y : S), {x,y} ∈ K.1.faces),
-- --   inv_fun := λ G,
-- --   { val :=
-- --     { faces := _

-- --     }

-- --   }

-- -- }

-- -- #exit


-- -- open affine

-- -- variables {V : Type*} [add_comm_group V] [module ℝ V]

-- -- structure triangulation {n : ℕ} (s : simplex ℝ V n) :=
-- -- -- (points : finset V)

-- -- -- (bits : finset (simplex ℝ V n))
-- -- -- (disjoint : ∀ x y ∈ bits, sorry)
