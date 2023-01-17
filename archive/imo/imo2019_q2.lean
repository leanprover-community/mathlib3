/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import geometry.euclidean.angle.sphere

/-!
# IMO 2019 Q2

In triangle `ABC`, point `A₁` lies on side `BC` and point `B₁` lies on side `AC`. Let `P` and
`Q` be points on segments `AA₁` and `BB₁`, respectively, such that `PQ` is parallel to `AB`.
Let `P₁` be a point on line `PB₁`, such that `B₁` lies strictly between `P` and `P₁`, and
`∠PP₁C = ∠BAC`. Similarly, let `Q₁` be a point on line `QA₁`, such that `A₁` lies strictly
between `Q` and `Q₁`, and `∠CQ₁Q = ∠CBA`.

Prove that points `P`, `Q`, `P₁`, and `Q₁` are concyclic.

We follow Solution 1 from the
[official solutions](https://www.imo2019.uk/wp-content/uploads/2018/07/solutions-r856.pdf).
Letting the rays `AA₁` and `BB₁` intersect the circumcircle of `ABC` at `A₂` and `B₂`
respectively, we show with an angle chase that `P`, `Q`, `A₂`, `B₂` are concyclic and let `ω` be
the circle through those points. We then show that `C`, `Q₁`, `A₂`, `A₁` are concyclic, and
then that `Q₁` lies on `ω`, and similarly that `P₁` lies on `ω`, so the required four points are
concyclic.

Note that most of the formal proof is actually proving nondegeneracy conditions needed for that
angle chase / concyclicity argument, where an informal solution doesn't discuss those conditions
at all. Also note that (as described in `geometry.euclidean.angle.oriented.basic`) the oriented
angles used are modulo `2 * π`, so parts of the angle chase that are only valid for angles modulo
`π` (as used in the informal solution) are represented as equalities of twice angles, which we write
as `(2 : ℤ) • ∡ _ _ _ = (2 : ℤ) • _ _ _`.
-/

/--
We apply the following conventions for formalizing IMO geometry problems. A problem is assumed
to take place in the plane unless that is clearly not intended, so it is not required to prove
that the points are coplanar (whether or not that in fact follows from the other conditions).
Angles in problem statements are taken to be unoriented. A reference to an angle `∠XYZ` is taken
to imply that `X` and `Z` are not equal to `Y`, since choices of junk values play no role in
informal mathematics, and those implications are included as hypotheses for the problem whether
or not they follow from the other hypotheses. Similar, a reference to `XY` as a line is taken to
imply that `X` does not equal `Y` and that is included as a hypothesis, and a reference to `XY`
being parallel to something is considered a reference to it as a line. However, such an implicit
hypothesis about two points being different is included only once for any given two points (even
if it follows from more than one reference to a line or an angle), if `X ≠ Y` is included then
`Y ≠ X` is not included separately, and such hypotheses are not included in the case where there
is also a reference in the problem to a triangle including those two points, or to strict
betweenness of three points including those two. If betweenness is stated, it is taken to be
strict betweenness. However, segments and sides are taken to include their endpoints (unless
this makes a problem false), although those degenerate cases might not necessarily have been
considered when the problem was formulated and contestants might not have been expected to deal
with them. A reference to a point being on a side or a segment is expressed directly with `wbtw`
rather than more literally with `affine_segment`.
-/
library_note "IMO geometry formalization conventions"

noncomputable theory

open affine affine.simplex euclidean_geometry finite_dimensional
open_locale affine euclidean_geometry real

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

variables (V : Type*) (Pt : Type*) [inner_product_space ℝ V] [metric_space Pt]
variables [normed_add_torsor V Pt] [hd2 : fact (finrank ℝ V = 2)]
include hd2

/-- A configuration satisfying the conditions of the problem. We define this structure to avoid
passing many hypotheses around as we build up information about the configuration; the final
result for a statement of the problem not using this structure is then deduced from one in terms
of this structure. -/
@[nolint has_nonempty_instance]
structure imo2019q2_cfg :=
(A B C A₁ B₁ P Q P₁ Q₁ : Pt)
(affine_independent_ABC : affine_independent ℝ ![A, B, C])
(wbtw_B_A₁_C : wbtw ℝ B A₁ C)
(wbtw_A_B₁_C : wbtw ℝ A B₁ C)
(wbtw_A_P_A₁ : wbtw ℝ A P A₁)
(wbtw_B_Q_B₁ : wbtw ℝ B Q B₁)
(PQ_parallel_AB : line[ℝ, P, Q] ∥ line[ℝ, A, B])
-- A hypothesis implicit in the named line.
(P_ne_Q : P ≠ Q)
(sbtw_P_B₁_P₁ : sbtw ℝ P B₁ P₁)
(angle_PP₁C_eq_angle_BAC : ∠ P P₁ C = ∠ B A C)
-- A hypothesis implicit in the first named angle.
(C_ne_P₁ : C ≠ P₁)
(sbtw_Q_A₁_Q₁ : sbtw ℝ Q A₁ Q₁)
(angle_CQ₁Q_eq_angle_CBA : ∠ C Q₁ Q = ∠ C B A)
-- A hypothesis implicit in the first named angle.
(C_ne_Q₁ : C ≠ Q₁)

/-- A default choice of orientation, for lemmas that need to pick one. -/
def some_orientation : module.oriented ℝ V (fin 2) :=
⟨basis.orientation (fin_basis_of_finrank_eq _ _ hd2.out)⟩

variables {V Pt}

namespace imo2019q2_cfg

variables (cfg : imo2019q2_cfg V Pt)

/-- The configuration has symmetry, allowing results proved for one point to be applied for
another (where the informal solution says "similarly"). -/
def symm : imo2019q2_cfg V Pt :=
{ A := cfg.B,
  B := cfg.A,
  C := cfg.C,
  A₁ := cfg.B₁,
  B₁ := cfg.A₁,
  P := cfg.Q,
  Q := cfg.P,
  P₁ := cfg.Q₁,
  Q₁ := cfg.P₁,
  affine_independent_ABC := begin
    rw ←affine_independent_equiv (equiv.swap (0 : fin 3) 1),
    convert cfg.affine_independent_ABC using 1,
    ext x,
    fin_cases x;
      refl
  end,
  wbtw_B_A₁_C := cfg.wbtw_A_B₁_C,
  wbtw_A_B₁_C := cfg.wbtw_B_A₁_C,
  wbtw_A_P_A₁ := cfg.wbtw_B_Q_B₁,
  wbtw_B_Q_B₁ := cfg.wbtw_A_P_A₁,
  PQ_parallel_AB := set.pair_comm cfg.P cfg.Q ▸ set.pair_comm cfg.A cfg.B ▸ cfg.PQ_parallel_AB,
  P_ne_Q := cfg.P_ne_Q.symm,
  sbtw_P_B₁_P₁ := cfg.sbtw_Q_A₁_Q₁,
  angle_PP₁C_eq_angle_BAC :=
    angle_comm cfg.C cfg.Q₁ cfg.Q ▸ angle_comm cfg.C cfg.B cfg.A ▸ cfg.angle_CQ₁Q_eq_angle_CBA,
  C_ne_P₁ := cfg.C_ne_Q₁,
  sbtw_Q_A₁_Q₁ := cfg.sbtw_P_B₁_P₁,
  angle_CQ₁Q_eq_angle_CBA :=
    angle_comm cfg.P cfg.P₁ cfg.C ▸ angle_comm cfg.B cfg.A cfg.C ▸ cfg.angle_PP₁C_eq_angle_BAC,
  C_ne_Q₁ := cfg.C_ne_P₁ }

/-! ### Configuration properties that are obvious from the diagram, and construction of the
points `A₂` and `B₂` -/

lemma A_ne_B : cfg.A ≠ cfg.B := cfg.affine_independent_ABC.injective.ne
  (dec_trivial : (0 : fin 3) ≠ 1)

lemma A_ne_C : cfg.A ≠ cfg.C := cfg.affine_independent_ABC.injective.ne
  (dec_trivial : (0 : fin 3) ≠ 2)

lemma B_ne_C : cfg.B ≠ cfg.C := cfg.affine_independent_ABC.injective.ne
  (dec_trivial : (1 : fin 3) ≠ 2)

lemma not_collinear_ABC : ¬collinear ℝ ({cfg.A, cfg.B, cfg.C} : set Pt) :=
affine_independent_iff_not_collinear_set.1 cfg.affine_independent_ABC

/-- `ABC` as a `triangle`. -/
def triangle_ABC : triangle ℝ Pt := ⟨_, cfg.affine_independent_ABC⟩

lemma A_mem_circumsphere : cfg.A ∈ cfg.triangle_ABC.circumsphere :=
cfg.triangle_ABC.mem_circumsphere 0

lemma B_mem_circumsphere : cfg.B ∈ cfg.triangle_ABC.circumsphere :=
cfg.triangle_ABC.mem_circumsphere 1

lemma C_mem_circumsphere : cfg.C ∈ cfg.triangle_ABC.circumsphere :=
cfg.triangle_ABC.mem_circumsphere 2

lemma symm_triangle_ABC : cfg.symm.triangle_ABC = cfg.triangle_ABC.reindex (equiv.swap 0 1) :=
by { ext i, fin_cases i; refl }

lemma symm_triangle_ABC_circumsphere :
  cfg.symm.triangle_ABC.circumsphere = cfg.triangle_ABC.circumsphere :=
by rw [symm_triangle_ABC, affine.simplex.circumsphere_reindex]

/-- `A₂` is the second point of intersection of the ray `AA₁` with the circumcircle of `ABC`. -/
def A₂ : Pt := cfg.triangle_ABC.circumsphere.second_inter cfg.A (cfg.A₁ -ᵥ cfg.A)

/-- `B₂` is the second point of intersection of the ray `BB₁` with the circumcircle of `ABC`. -/
def B₂ : Pt := cfg.triangle_ABC.circumsphere.second_inter cfg.B (cfg.B₁ -ᵥ cfg.B)

lemma A₂_mem_circumsphere : cfg.A₂ ∈ cfg.triangle_ABC.circumsphere :=
(sphere.second_inter_mem _).2 cfg.A_mem_circumsphere

lemma B₂_mem_circumsphere : cfg.B₂ ∈ cfg.triangle_ABC.circumsphere :=
(sphere.second_inter_mem _).2 cfg.B_mem_circumsphere

lemma symm_A₂ : cfg.symm.A₂ = cfg.B₂ :=
by { simp_rw [A₂, B₂, symm_triangle_ABC_circumsphere], refl }

lemma QP_parallel_BA : line[ℝ, cfg.Q, cfg.P] ∥ line[ℝ, cfg.B, cfg.A] :=
by { rw [set.pair_comm cfg.Q, set.pair_comm cfg.B], exact cfg.PQ_parallel_AB }

lemma A_ne_A₁ : cfg.A ≠ cfg.A₁ :=
begin
  intro h,
  have h' := cfg.not_collinear_ABC,
  rw [h, set.insert_comm] at h',
  exact h' cfg.wbtw_B_A₁_C.collinear
end

lemma collinear_PAA₁A₂ : collinear ℝ ({cfg.P, cfg.A, cfg.A₁, cfg.A₂} : set Pt) :=
begin
  rw [A₂,
      (cfg.triangle_ABC.circumsphere.second_inter_collinear cfg.A cfg.A₁).collinear_insert_iff_of_ne
        (set.mem_insert _ _) (set.mem_insert_of_mem _ (set.mem_insert _ _)) cfg.A_ne_A₁,
      set.insert_comm],
  exact cfg.wbtw_A_P_A₁.collinear
end

lemma A₁_ne_C : cfg.A₁ ≠ cfg.C :=
begin
  intro h,
  have hsbtw := cfg.sbtw_Q_A₁_Q₁,
  rw h at hsbtw,
  have ha := hsbtw.angle₂₃₁_eq_zero,
  rw [angle_CQ₁Q_eq_angle_CBA, angle_comm] at ha,
  exact (angle_ne_zero_of_not_collinear cfg.not_collinear_ABC) ha
end

lemma B₁_ne_C : cfg.B₁ ≠ cfg.C := cfg.symm.A₁_ne_C

lemma Q_not_mem_CB : cfg.Q ∉ line[ℝ, cfg.C, cfg.B] :=
begin
  intro hQ,
  have hQA₁ : line[ℝ, cfg.Q, cfg.A₁] ≤ line[ℝ, cfg.C, cfg.B] :=
    affine_span_pair_le_of_mem_of_mem hQ cfg.wbtw_B_A₁_C.symm.mem_affine_span,
  have hQ₁ : cfg.Q₁ ∈ line[ℝ, cfg.C, cfg.B],
  { rw affine_subspace.le_def' at hQA₁,
    exact hQA₁ _ cfg.sbtw_Q_A₁_Q₁.right_mem_affine_span },
  have hc : collinear ℝ ({cfg.C, cfg.Q₁, cfg.Q} : set Pt),
  { have hc' : collinear ℝ ({cfg.B, cfg.C, cfg.Q₁, cfg.Q} : set Pt),
    { rw [set.insert_comm cfg.B, set.insert_comm cfg.B, set.pair_comm, set.insert_comm cfg.C,
          set.insert_comm cfg.C],
      exact collinear_insert_insert_of_mem_affine_span_pair hQ₁ hQ },
    exact hc'.subset (set.subset_insert _ _) },
  rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, cfg.angle_CQ₁Q_eq_angle_CBA,
      or_iff_right cfg.C_ne_Q₁, or_iff_right cfg.sbtw_Q_A₁_Q₁.left_ne_right, angle_comm] at hc,
  exact cfg.not_collinear_ABC (hc.elim collinear_of_angle_eq_zero collinear_of_angle_eq_pi)
end

lemma Q_ne_B : cfg.Q ≠ cfg.B :=
begin
  intro h,
  have h' := cfg.Q_not_mem_CB,
  rw h at h',
  exact h' (right_mem_affine_span_pair _ _ _)
end

lemma s_opp_side_CB_Q_Q₁ : line[ℝ, cfg.C, cfg.B].s_opp_side cfg.Q cfg.Q₁ :=
cfg.sbtw_Q_A₁_Q₁.s_opp_side_of_not_mem_of_mem cfg.Q_not_mem_CB cfg.wbtw_B_A₁_C.symm.mem_affine_span

/-! ### Relate the orientations of different angles in the configuration -/

section oriented

variables [module.oriented ℝ V (fin 2)]

lemma oangle_CQ₁Q_sign_eq_oangle_CBA_sign :
  (∡ cfg.C cfg.Q₁ cfg.Q).sign = (∡ cfg.C cfg.B cfg.A).sign :=
by rw [←cfg.sbtw_Q_A₁_Q₁.symm.oangle_eq_right,
       cfg.s_opp_side_CB_Q_Q₁.oangle_sign_eq_neg (left_mem_affine_span_pair ℝ cfg.C cfg.B)
        cfg.wbtw_B_A₁_C.symm.mem_affine_span, ←real.angle.sign_neg, ←oangle_rev,
      cfg.wbtw_B_A₁_C.oangle_sign_eq_of_ne_right cfg.Q cfg.A₁_ne_C, oangle_rotate_sign,
      cfg.wbtw_B_Q_B₁.oangle_eq_right cfg.Q_ne_B,
      cfg.wbtw_A_B₁_C.symm.oangle_sign_eq_of_ne_left cfg.B cfg.B₁_ne_C.symm]

lemma oangle_CQ₁Q_eq_oangle_CBA : ∡ cfg.C cfg.Q₁ cfg.Q = ∡ cfg.C cfg.B cfg.A :=
oangle_eq_of_angle_eq_of_sign_eq cfg.angle_CQ₁Q_eq_angle_CBA cfg.oangle_CQ₁Q_sign_eq_oangle_CBA_sign

end oriented

/-! ### More obvious configuration properties -/

lemma A₁_ne_B : cfg.A₁ ≠ cfg.B :=
begin
  intro h,
  have hwbtw := cfg.wbtw_A_P_A₁,
  rw h at hwbtw,
  have hPQ : line[ℝ, cfg.P, cfg.Q] = line[ℝ, cfg.A, cfg.B],
  { rw affine_subspace.eq_iff_direction_eq_of_mem (left_mem_affine_span_pair _ _ _)
         hwbtw.mem_affine_span,
    exact cfg.PQ_parallel_AB.direction_eq },
  haveI := some_orientation V,
  have haQ : (2 : ℤ) • ∡ cfg.C cfg.B cfg.Q = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A,
  { rw [collinear.two_zsmul_oangle_eq_right _ cfg.A_ne_B cfg.Q_ne_B],
    rw [set.pair_comm, set.insert_comm],
    refine collinear_insert_of_mem_affine_span_pair _,
    rw ←hPQ,
    exact right_mem_affine_span_pair _ _ _ },
  have ha : (2 : ℤ) • ∡ cfg.C cfg.B cfg.Q = (2 : ℤ) • ∡ cfg.C cfg.Q₁ cfg.Q,
  { rw [oangle_CQ₁Q_eq_oangle_CBA, haQ] },
  have hn : ¬collinear ℝ ({cfg.C, cfg.B, cfg.Q} : set Pt),
  { rw [collinear_iff_of_two_zsmul_oangle_eq haQ, set.pair_comm, set.insert_comm, set.pair_comm],
    exact cfg.not_collinear_ABC },
  have hc := cospherical_of_two_zsmul_oangle_eq_of_not_collinear ha hn,
  have hBQ₁ : cfg.B ≠ cfg.Q₁, { rw [←h], exact cfg.sbtw_Q_A₁_Q₁.ne_right },
  have hQQ₁ : cfg.Q ≠ cfg.Q₁ := cfg.sbtw_Q_A₁_Q₁.left_ne_right,
  have hBQ₁Q : affine_independent ℝ ![cfg.B, cfg.Q₁, cfg.Q] :=
    hc.affine_independent_of_mem_of_ne (set.mem_insert_of_mem _ (set.mem_insert _ _))
      (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_insert _ _)))
      (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_insert_of_mem _
        (set.mem_singleton _)))) hBQ₁ cfg.Q_ne_B.symm hQQ₁.symm,
  rw affine_independent_iff_not_collinear_set at hBQ₁Q,
  refine hBQ₁Q _,
  rw [←h, set.pair_comm, set.insert_comm],
  exact cfg.sbtw_Q_A₁_Q₁.wbtw.collinear
end

lemma sbtw_B_A₁_C : sbtw ℝ cfg.B cfg.A₁ cfg.C := ⟨cfg.wbtw_B_A₁_C, cfg.A₁_ne_B, cfg.A₁_ne_C⟩

lemma sbtw_A_B₁_C : sbtw ℝ cfg.A cfg.B₁ cfg.C := cfg.symm.sbtw_B_A₁_C

lemma sbtw_A_A₁_A₂ : sbtw ℝ cfg.A cfg.A₁ cfg.A₂ :=
begin
  refine sphere.sbtw_second_inter cfg.A_mem_circumsphere _,
  convert cfg.sbtw_B_A₁_C.dist_lt_max_dist _,
  change _ = max (dist (cfg.triangle_ABC.points 1) _) (dist (cfg.triangle_ABC.points 2) _),
  simp_rw [circumsphere_center, circumsphere_radius, dist_circumcenter_eq_circumradius, max_self]
end

lemma sbtw_B_B₁_B₂ : sbtw ℝ cfg.B cfg.B₁ cfg.B₂ :=
by { rw ←cfg.symm_A₂, exact cfg.symm.sbtw_A_A₁_A₂ }

lemma A₂_ne_A : cfg.A₂ ≠ cfg.A := cfg.sbtw_A_A₁_A₂.left_ne_right.symm

lemma A₂_ne_P : cfg.A₂ ≠ cfg.P := (cfg.sbtw_A_A₁_A₂.trans_wbtw_left_ne cfg.wbtw_A_P_A₁).symm

lemma A₂_ne_B : cfg.A₂ ≠ cfg.B :=
begin
  intro h,
  have h₁ := cfg.sbtw_A_A₁_A₂,
  rw h at h₁,
  refine cfg.not_collinear_ABC _,
  have hc : collinear ℝ ({cfg.A, cfg.C, cfg.B, cfg.A₁} : set Pt) :=
    collinear_insert_insert_of_mem_affine_span_pair h₁.left_mem_affine_span
      cfg.sbtw_B_A₁_C.right_mem_affine_span,
  refine hc.subset _,
  rw [set.pair_comm _ cfg.A₁, set.insert_comm _ cfg.A₁, set.insert_comm _ cfg.A₁, set.pair_comm],
  exact set.subset_insert _ _
end

lemma A₂_ne_C : cfg.A₂ ≠ cfg.C :=
begin
  intro h,
  have h₁ := cfg.sbtw_A_A₁_A₂,
  rw h at h₁,
  refine cfg.not_collinear_ABC _,
  have hc : collinear ℝ ({cfg.A, cfg.B, cfg.C, cfg.A₁} : set Pt) :=
    collinear_insert_insert_of_mem_affine_span_pair h₁.left_mem_affine_span
      cfg.sbtw_B_A₁_C.left_mem_affine_span,
  refine hc.subset (set.insert_subset_insert (set.insert_subset_insert _)),
  rw set.singleton_subset_iff,
  exact set.mem_insert _ _
end

lemma B₂_ne_B : cfg.B₂ ≠ cfg.B := by { rw ←symm_A₂, exact cfg.symm.A₂_ne_A }

lemma B₂_ne_Q : cfg.B₂ ≠ cfg.Q := by { rw ←symm_A₂, exact cfg.symm.A₂_ne_P }

lemma B₂_ne_A₂ : cfg.B₂ ≠ cfg.A₂ :=
begin
  intro h,
  have hA : sbtw ℝ (cfg.triangle_ABC.points 1) cfg.A₁ (cfg.triangle_ABC.points 2) :=
    cfg.sbtw_B_A₁_C,
  have hB : sbtw ℝ (cfg.triangle_ABC.points 0) cfg.B₁ (cfg.triangle_ABC.points 2) :=
    cfg.sbtw_A_B₁_C,
  have hA' : cfg.A₂ ∈ line[ℝ, cfg.triangle_ABC.points 0, cfg.A₁] :=
    sphere.second_inter_vsub_mem_affine_span _ _ _,
  have hB' : cfg.A₂ ∈ line[ℝ, cfg.triangle_ABC.points 1, cfg.B₁],
  { rw ←h, exact sphere.second_inter_vsub_mem_affine_span _ _ _ },
  exact (sbtw_of_sbtw_of_sbtw_of_mem_affine_span_pair dec_trivial hA hB hA' hB').symm.not_rotate
    cfg.sbtw_A_A₁_A₂.wbtw
end

lemma wbtw_B_Q_B₂ : wbtw ℝ cfg.B cfg.Q cfg.B₂ := cfg.sbtw_B_B₁_B₂.wbtw.trans_left cfg.wbtw_B_Q_B₁

/-! ### The first equality in the first angle chase in the solution -/

section oriented

variables [module.oriented ℝ V (fin 2)]

lemma two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂ :
  (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ = (2 : ℤ) • ∡ cfg.B cfg.A cfg.A₂ :=
begin
  refine two_zsmul_oangle_of_parallel cfg.QP_parallel_BA _,
  convert affine_subspace.parallel.refl _ using 1,
  rw [cfg.collinear_PAA₁A₂.affine_span_eq_of_ne
        (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_insert_of_mem _
          (set.mem_singleton _))))
        (set.mem_insert_of_mem _ (set.mem_insert _ _)) cfg.A₂_ne_A,
      cfg.collinear_PAA₁A₂.affine_span_eq_of_ne
        (set.mem_insert_of_mem _ (set.mem_insert_of_mem _ (set.mem_insert_of_mem _
          (set.mem_singleton _))))
        (set.mem_insert _ _) cfg.A₂_ne_P]
end

end oriented

/-! ### More obvious configuration properties -/

lemma not_collinear_QPA₂ : ¬ collinear ℝ ({cfg.Q, cfg.P, cfg.A₂} : set Pt) :=
begin
  haveI := some_orientation V,
  rw [collinear_iff_of_two_zsmul_oangle_eq cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂,
      ←affine_independent_iff_not_collinear_set],
  have h : cospherical ({cfg.B, cfg.A, cfg.A₂} : set Pt),
  { refine cfg.triangle_ABC.circumsphere.cospherical.subset _,
    simp [set.insert_subset, cfg.A_mem_circumsphere, cfg.B_mem_circumsphere,
          cfg.A₂_mem_circumsphere] },
  exact h.affine_independent_of_ne cfg.A_ne_B.symm cfg.A₂_ne_B.symm cfg.A₂_ne_A.symm
end

lemma Q₁_ne_A₂ : cfg.Q₁ ≠ cfg.A₂ :=
begin
  intro h,
  have h₁ := cfg.sbtw_Q_A₁_Q₁,
  rw h at h₁,
  refine cfg.not_collinear_QPA₂ _,
  have hA₂ := cfg.sbtw_A_A₁_A₂.right_mem_affine_span,
  have hA₂A₁ : line[ℝ, cfg.A₂, cfg.A₁] ≤ line[ℝ, cfg.A, cfg.A₁] :=
    affine_span_pair_le_of_left_mem hA₂,
  have hQ : cfg.Q ∈ line[ℝ, cfg.A, cfg.A₁],
  { rw affine_subspace.le_def' at hA₂A₁,
    exact hA₂A₁ _ h₁.left_mem_affine_span },
  exact collinear_triple_of_mem_affine_span_pair hQ cfg.wbtw_A_P_A₁.mem_affine_span hA₂
end

lemma affine_independent_QPA₂ : affine_independent ℝ ![cfg.Q, cfg.P, cfg.A₂] :=
affine_independent_iff_not_collinear_set.2 cfg.not_collinear_QPA₂

lemma affine_independent_PQB₂ : affine_independent ℝ ![cfg.P, cfg.Q, cfg.B₂] :=
by { rw ←symm_A₂, exact cfg.symm.affine_independent_QPA₂ }

/-- `QPA₂` as a `triangle`. -/
def triangle_QPA₂ : triangle ℝ Pt := ⟨_, cfg.affine_independent_QPA₂⟩

/-- `PQB₂` as a `triangle`. -/
def triangle_PQB₂ : triangle ℝ Pt := ⟨_, cfg.affine_independent_PQB₂⟩

lemma symm_triangle_QPA₂ : cfg.symm.triangle_QPA₂ = cfg.triangle_PQB₂ :=
by { simp_rw [triangle_PQB₂, ←symm_A₂], ext i, fin_cases i; refl }

/-- `ω` is the circle containing `Q`, `P` and `A₂`, which will be shown also to contain `B₂`,
`P₁` and `Q₁`. -/
def ω : sphere Pt := cfg.triangle_QPA₂.circumsphere

lemma P_mem_ω : cfg.P ∈ cfg.ω := cfg.triangle_QPA₂.mem_circumsphere 1

lemma Q_mem_ω : cfg.Q ∈ cfg.ω := cfg.triangle_QPA₂.mem_circumsphere 0

/-! ### The rest of the first angle chase in the solution -/

section oriented

variables [module.oriented ℝ V (fin 2)]

lemma two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_QB₂A₂ :
  (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ = (2 : ℤ) • ∡ cfg.Q cfg.B₂ cfg.A₂ :=
calc (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ = (2 : ℤ) • ∡ cfg.B cfg.A cfg.A₂ :
    cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂
  ... = (2 : ℤ) • ∡ cfg.B cfg.B₂ cfg.A₂ :
    sphere.two_zsmul_oangle_eq cfg.B_mem_circumsphere cfg.A_mem_circumsphere
      cfg.B₂_mem_circumsphere cfg.A₂_mem_circumsphere cfg.A_ne_B cfg.A₂_ne_A.symm
      cfg.B₂_ne_B cfg.B₂_ne_A₂
  ... = (2 : ℤ) • ∡ cfg.Q cfg.B₂ cfg.A₂ :
    by rw cfg.wbtw_B_Q_B₂.symm.oangle_eq_left cfg.B₂_ne_Q.symm

end oriented

/-! ### Conclusions from that first angle chase -/

lemma cospherical_QPB₂A₂ : cospherical ({cfg.Q, cfg.P, cfg.B₂, cfg.A₂} : set Pt) :=
begin
  haveI := some_orientation V,
  exact cospherical_of_two_zsmul_oangle_eq_of_not_collinear
    cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_QB₂A₂ cfg.not_collinear_QPA₂
end

lemma symm_ω_eq_triangle_PQB₂_circumsphere : cfg.symm.ω = cfg.triangle_PQB₂.circumsphere :=
by rw [ω, symm_triangle_QPA₂]

lemma symm_ω : cfg.symm.ω = cfg.ω :=
begin
  rw [symm_ω_eq_triangle_PQB₂_circumsphere, ω],
  refine circumsphere_eq_of_cospherical hd2.out cfg.cospherical_QPB₂A₂ _ _,
  { simp only [triangle_PQB₂, matrix.range_cons, matrix.range_empty, set.singleton_union,
               insert_emptyc_eq],
    rw set.insert_comm,
    refine set.insert_subset_insert (set.insert_subset_insert _),
    simp },
  { simp only [triangle_QPA₂, matrix.range_cons, matrix.range_empty, set.singleton_union,
               insert_emptyc_eq],
    refine set.insert_subset_insert (set.insert_subset_insert _),
    simp }
end

/-! ### The second angle chase in the solution -/

section oriented

variables [module.oriented ℝ V (fin 2)]

lemma two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA :
  (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A₁ = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A :=
calc (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A₁ = (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A :
    by rw cfg.sbtw_A_A₁_A₂.symm.oangle_eq_right
  ... = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A :
    sphere.two_zsmul_oangle_eq cfg.C_mem_circumsphere cfg.A₂_mem_circumsphere
      cfg.B_mem_circumsphere cfg.A_mem_circumsphere cfg.A₂_ne_C cfg.A₂_ne_A cfg.B_ne_C
      cfg.A_ne_B.symm

lemma two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CQ₁A₁ :
  (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A₁ = (2 : ℤ) • ∡ cfg.C cfg.Q₁ cfg.A₁ :=
calc (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A₁ = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A :
    cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA
  ... = (2 : ℤ) • ∡ cfg.C cfg.Q₁ cfg.Q : by rw oangle_CQ₁Q_eq_oangle_CBA
  ... = (2 : ℤ) • ∡ cfg.C cfg.Q₁ cfg.A₁ : by rw cfg.sbtw_Q_A₁_Q₁.symm.oangle_eq_right

end oriented

/-! ### Conclusions from that second angle chase -/

lemma not_collinear_CA₂A₁ : ¬collinear ℝ ({cfg.C, cfg.A₂, cfg.A₁} : set Pt) :=
begin
  haveI := some_orientation V,
  rw [collinear_iff_of_two_zsmul_oangle_eq cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA,
      set.pair_comm, set.insert_comm, set.pair_comm],
  exact cfg.not_collinear_ABC
end

lemma cospherical_A₁Q₁CA₂ : cospherical ({cfg.A₁, cfg.Q₁, cfg.C, cfg.A₂} : set Pt) :=
begin
  haveI := some_orientation V,
  rw [set.insert_comm cfg.Q₁, set.insert_comm cfg.A₁, set.pair_comm, set.insert_comm cfg.A₁,
      set.pair_comm],
  exact cospherical_of_two_zsmul_oangle_eq_of_not_collinear
    cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CQ₁A₁ cfg.not_collinear_CA₂A₁
end

/-! ### The third angle chase in the solution -/

section oriented

variables [module.oriented ℝ V (fin 2)]

lemma two_zsmul_oangle_QQ₁A₂_eq_two_zsmul_oangle_QPA₂ :
  (2 : ℤ) • ∡ cfg.Q cfg.Q₁ cfg.A₂ = (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ :=
calc (2 : ℤ) • ∡ cfg.Q cfg.Q₁ cfg.A₂ = (2 : ℤ) • ∡ cfg.A₁ cfg.Q₁ cfg.A₂ :
    by rw cfg.sbtw_Q_A₁_Q₁.symm.oangle_eq_left
  ... = (2 : ℤ) • ∡ cfg.A₁ cfg.C cfg.A₂ :
    cfg.cospherical_A₁Q₁CA₂.two_zsmul_oangle_eq cfg.sbtw_Q_A₁_Q₁.right_ne cfg.Q₁_ne_A₂
      cfg.A₁_ne_C.symm cfg.A₂_ne_C.symm
  ... = (2 : ℤ) • ∡ cfg.B cfg.C cfg.A₂ : by rw cfg.sbtw_B_A₁_C.symm.oangle_eq_left
  ... = (2 : ℤ) • ∡ cfg.B cfg.A cfg.A₂ :
    sphere.two_zsmul_oangle_eq cfg.B_mem_circumsphere cfg.C_mem_circumsphere
      cfg.A_mem_circumsphere cfg.A₂_mem_circumsphere cfg.B_ne_C.symm cfg.A₂_ne_C.symm cfg.A_ne_B
      cfg.A₂_ne_A.symm
  ... = (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ : cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂.symm

end oriented

/-! ### Conclusions from that third angle chase -/

lemma Q₁_mem_ω : cfg.Q₁ ∈ cfg.ω :=
begin
  haveI := some_orientation V,
  exact affine.triangle.mem_circumsphere_of_two_zsmul_oangle_eq (dec_trivial : (0 : fin 3) ≠ 1)
    (dec_trivial : (0 : fin 3) ≠ 2) dec_trivial cfg.two_zsmul_oangle_QQ₁A₂_eq_two_zsmul_oangle_QPA₂
end

lemma P₁_mem_ω : cfg.P₁ ∈ cfg.ω := by { rw ←symm_ω, exact cfg.symm.Q₁_mem_ω }

theorem result : concyclic ({cfg.P, cfg.Q, cfg.P₁, cfg.Q₁} : set Pt) :=
begin
  refine ⟨_, coplanar_of_fact_finrank_eq_two _⟩,
  rw cospherical_iff_exists_sphere,
  refine ⟨cfg.ω, _⟩,
  simp only [set.insert_subset, set.singleton_subset_iff],
  exact ⟨cfg.P_mem_ω, cfg.Q_mem_ω, cfg.P₁_mem_ω, cfg.Q₁_mem_ω⟩
end

end imo2019q2_cfg

theorem imo2019_q2 (A B C A₁ B₁ P Q P₁ Q₁ : Pt)
  (affine_independent_ABC : affine_independent ℝ ![A, B, C])
  (wbtw_B_A₁_C : wbtw ℝ B A₁ C) (wbtw_A_B₁_C : wbtw ℝ A B₁ C) (wbtw_A_P_A₁ : wbtw ℝ A P A₁)
  (wbtw_B_Q_B₁ : wbtw ℝ B Q B₁) (PQ_parallel_AB : line[ℝ, P, Q] ∥ line[ℝ, A, B]) (P_ne_Q : P ≠ Q)
  (sbtw_P_B₁_P₁ : sbtw ℝ P B₁ P₁) (angle_PP₁C_eq_angle_BAC : ∠ P P₁ C = ∠ B A C)
  (C_ne_P₁ : C ≠ P₁) (sbtw_Q_A₁_Q₁ : sbtw ℝ Q A₁ Q₁)
  (angle_CQ₁Q_eq_angle_CBA : ∠ C Q₁ Q = ∠ C B A) (C_ne_Q₁ : C ≠ Q₁) :
  concyclic ({P, Q, P₁, Q₁} : set Pt) :=
(⟨A, B, C, A₁, B₁, P, Q, P₁, Q₁, affine_independent_ABC, wbtw_B_A₁_C, wbtw_A_B₁_C, wbtw_A_P_A₁,
  wbtw_B_Q_B₁, PQ_parallel_AB, P_ne_Q, sbtw_P_B₁_P₁, angle_PP₁C_eq_angle_BAC, C_ne_P₁,
  sbtw_Q_A₁_Q₁, angle_CQ₁Q_eq_angle_CBA, C_ne_Q₁⟩ : imo2019q2_cfg V Pt).result
