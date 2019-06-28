/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Fundamental groupoid.
-/

import topology.basic category_theory.groupoid topology.instances.real

universes u v

instance {α : Type u} [linear_ordered_semiring α] : has_zero (set.Icc (0:α) 1) :=
⟨⟨0, le_refl 0, zero_le_one⟩⟩

@[simp] lemma set.Icc_zero_val {α : Type u} [linear_ordered_semiring α] :
  (0 : set.Icc (0:α) 1).1 = 0 :=
rfl

@[simp] lemma set.Icc_coe_zero {α : Type u} [linear_ordered_semiring α] :
  ((0 : set.Icc (0:α) 1) : α) = 0 :=
rfl

instance {α : Type u} [linear_ordered_semiring α] : has_one (set.Icc (0:α) 1) :=
⟨⟨1, zero_le_one, le_refl 1⟩⟩

@[simp] lemma set.Icc_one_val {α : Type u} [linear_ordered_semiring α] :
  (1 : set.Icc (0:α) 1).1 = 1 :=
rfl

@[simp] lemma set.Icc_coe_one {α : Type u} [linear_ordered_semiring α] :
  ((1 : set.Icc (0:α) 1) : α) = 1 :=
rfl

variables {X : Type u} [topological_space X]

structure path (x y : X) : Type u :=
(to_fun : set.Icc (0:ℝ) 1 → X)
(continuous : continuous to_fun)
(initial : to_fun 0 = x)
(final : to_fun 1 = y)

namespace path

variables {x y z : X}

@[extensionality] lemma ext {f g : path x y} (H : ∀ s, f.1 s = g.1 s) : f = g :=
by cases f; cases g; congr' 1; ext s; exact H s

protected def id (x : X) : path x x :=
{ to_fun := λ p, x,
  continuous := continuous_const,
  initial := rfl,
  final := rfl }

@[simp] lemma id_apply (p) : (path.id x).1 p = x := rfl

noncomputable def comp (f : path x y) (g : path y z) : path x z :=
{ to_fun := λ p, if p.1 ≤ 0.5 then f.1 ⟨min (p.1 + p.1) 1,
      le_min (add_nonneg p.2.1 p.2.1) zero_le_one, min_le_right _ _⟩
    else g.1 ⟨max (p.1 + p.1 - 1) 0, le_max_right _ _,
      max_le (sub_le_iff_le_add.2 (add_le_add p.2.2 p.2.2)) zero_le_one⟩,
  continuous := continuous_if
    (λ p hp, have p.1 = 0.5, from frontier_le_subset_eq continuous_induced_dom continuous_const hp,
      by simp only [this, add_halves, sub_self, min_self, max_self]; erw [f.4, g.3])
    (continuous.comp f.2 (continuous_induced_rng $ continuous_min
      (continuous_add continuous_induced_dom continuous_induced_dom)
      continuous_const))
    (continuous.comp g.2 (continuous_induced_rng $ continuous_max (continuous_sub
        (continuous_add continuous_induced_dom continuous_induced_dom)
        continuous_const)
      continuous_const)),
  initial := by erw [if_pos (le_of_lt $ half_pos $ (zero_lt_one : (0:ℝ)<1))];
    simp only [set.Icc_zero_val, add_zero, min_eq_left (zero_le_one : (0:ℝ)≤1)]; convert f.3,
  final := by erw [if_neg (not_le_of_lt $ half_lt_self $ (zero_lt_one : (0:ℝ)<1))];
    simp only [set.Icc_one_val, add_sub_cancel, max_eq_left (zero_le_one : (0:ℝ)≤1)]; convert g.4 }

@[simp] lemma comp_apply_le (f : path x y) (g : path y z) (p : set.Icc (0:ℝ) 1) (hp : p.1 ≤ 0.5) :
  (f.comp g).1 p =
  f.1 ⟨p.1 + p.1, add_nonneg p.2.1 p.2.1, le_trans (add_le_add hp hp) (by rw add_halves)⟩ :=
eq.trans (if_pos hp) $ congr_arg f.1 $ subtype.eq $ min_eq_left $
le_trans (add_le_add hp hp) $ by rw add_halves

@[simp] lemma comp_apply_ge (f : path x y) (g : path y z) (p : set.Icc (0:ℝ) 1) (hp : 0.5 ≤ p.1) :
  (f.comp g).1 p = g.1 ⟨p.1 + p.1 - 1,
      sub_nonneg.2 $ le_trans (by rw add_halves) (add_le_add hp hp),
      sub_le_iff_le_add.2 $ add_le_add p.2.2 p.2.2⟩ :=
or.cases_on (lt_or_eq_of_le hp)
  (λ h, eq.trans (if_neg $ not_le_of_lt h) $ congr_arg g.1 $ subtype.eq $ max_eq_left $
    sub_nonneg.2 $ le_trans (by rw add_halves) (add_le_add hp hp))
  (λ h, eq.trans (if_pos $ ge_of_eq h) $
    by simp only [h.symm, add_halves, min_self, sub_self]; erw [f.4, g.3])

def inv (f : path x y) : path y x :=
{ to_fun := λ p, f.1 ⟨1 - p.1, sub_nonneg.2 p.2.2, sub_le.2 (by rw sub_self; exact p.2.1)⟩,
  continuous := f.2.comp $ continuous_induced_rng $
    continuous_sub continuous_const continuous_induced_dom,
  initial := by simp only [set.Icc_zero_val, sub_zero]; convert f.4,
  final := by simp only [set.Icc_one_val, sub_self]; convert f.3 }

@[simp] lemma inv_apply (f : path x y) (p) :
  f.inv.1 p = f.1 ⟨1 - p.1, sub_nonneg.2 p.2.2, sub_le.2 (by rw sub_self; exact p.2.1)⟩ :=
rfl

@[simp] lemma inv_inv (f : path x y) : f.inv.inv = f :=
ext $ λ s, congr_arg f.1 $ subtype.eq $ by convert sub_sub_cancel 1 s.1

@[simp] lemma inv_comp (f : path x y) (g : path y z) : (f.comp g).inv = g.inv.comp f.inv :=
begin
  ext s,
  cases le_total s.1 0.5 with hs hs,
  { have : 0.5 ≤ 1 - s.1,
    { exact le_sub_iff_add_le.2 (le_trans (add_le_add_left hs _) (by rw add_halves)) },
    rw inv_apply,
    rw comp_apply_ge f g ⟨1 - s.1, sub_nonneg.2 s.2.2, sub_le.2 (by rw sub_self; exact s.2.1)⟩ this,
    rw [comp_apply_le _ _ _ hs, inv_apply],
    congr' 2,
    rw [(add_sub_comm _ _ _ _).symm, sub_right_comm, add_sub_cancel] },
  { have : 1 - s.1 ≤ 0.5 := le_trans (sub_le_sub_left hs _) (by rw sub_half),
    rw inv_apply,
    rw comp_apply_le f g ⟨1 - s.1, sub_nonneg.2 s.2.2, sub_le.2 (by rw sub_self; exact s.2.1)⟩ this,
    rw [comp_apply_ge _ _ _ hs, inv_apply],
    congr' 2,
    rw [← sub_add, sub_add_eq_add_sub 1 (s.1 + s.1), add_sub_comm] }
end

@[simp] lemma inv_id (x : X) : (path.id x).inv = path.id x :=
ext $ λ s, rfl

end path

structure homotopy {x y : X} (f g : path x y) : Type u :=
(to_fun : set.Icc (0:ℝ) 1 × set.Icc (0:ℝ) 1 → X)
(continuous : continuous to_fun)
(initial : ∀ s, to_fun (s, 0) = x)
(final : ∀ s, to_fun (s, 1) = y)
(start : ∀ t, to_fun (0, t) = f.1 t)
(finish : ∀ t, to_fun (1, t) = g.1 t)

namespace homotopy

variables {w x y z : X} {f g h : path x y}

def refl (f : path x y) : homotopy f f :=
{ to_fun := λ p, f.1 p.2,
  continuous := f.2.comp continuous_snd,
  initial := λ s, f.3,
  final := λ s, f.4,
  start := λ t, rfl,
  finish := λ t, rfl }

def symm (F : homotopy f g) : homotopy g f :=
{ to_fun := λ p, F.1 (⟨1 - p.1.1, sub_nonneg.2 p.1.2.2,
    sub_le.2 (by rw sub_self; exact p.1.2.1)⟩, p.2),
  continuous := F.2.comp $ continuous.prod_mk
    (continuous_induced_rng $ continuous_sub continuous_const $
      continuous_induced_dom.comp continuous_fst)
    continuous_snd,
  initial := λ s, F.3 _,
  final := λ s, F.4 _,
  start := λ t, by simp only [set.Icc_zero_val, sub_zero]; convert F.6 t,
  finish := λ t, by simp only [set.Icc_one_val, sub_self]; convert F.5 t }

noncomputable def trans (F : homotopy f g) (G : homotopy g h) : homotopy f h :=
{ to_fun := λ p, if p.1.1 ≤ 0.5
    then F.1 (⟨min (p.1.1 + p.1.1) 1, le_min (add_nonneg p.1.2.1 p.1.2.1) zero_le_one,
        min_le_right _ _⟩,
      p.2)
    else G.1 (⟨max (p.1.1 + p.1.1 - 1) 0, le_max_right _ _,
        max_le (sub_le_iff_le_add.2 (add_le_add p.1.2.2 p.1.2.2)) zero_le_one⟩,
      p.2),
  continuous := continuous_if
    (λ p hp, have p.1.1 = 0.5,
      from frontier_le_subset_eq (continuous_induced_dom.comp continuous_fst) continuous_const hp,
      by simp only [this, add_halves, sub_self, min_self, max_self]; erw [F.6, G.5])
    (F.2.comp $ continuous.prod_mk (continuous_induced_rng $
        continuous_min (continuous_add (continuous_induced_dom.comp continuous_fst)
            (continuous_induced_dom.comp continuous_fst))
          continuous_const)
      continuous_snd)
    (G.2.comp $ continuous.prod_mk (continuous_induced_rng $
        continuous_max (continuous_sub (continuous_add (continuous_induced_dom.comp continuous_fst)
            (continuous_induced_dom.comp continuous_fst))
          continuous_const) continuous_const)
      continuous_snd),
  initial := λ s, by dsimp only; split_ifs; simp only [F.3, G.3],
  final := λ s, by dsimp only; split_ifs; simp only [F.4, G.4],
  start := λ t, by erw [if_pos (le_of_lt $ half_pos (zero_lt_one : (0:ℝ)<1))];
    simp only [set.Icc_zero_val, add_zero, min_eq_left (zero_le_one : (0:ℝ)≤1)]; exact F.5 t,
  finish := λ t, by erw [if_neg (not_le_of_lt $ half_lt_self (zero_lt_one : (0:ℝ)<1))];
    simp only [set.Icc_one_val, add_sub_cancel, max_eq_left (zero_le_one : (0:ℝ)≤1)]; exact G.6 t }

noncomputable def comp {α β : path y z} (F : homotopy f g) (G : homotopy α β) :
  homotopy (f.comp α) (g.comp β) :=
{ to_fun := λ p, if p.2.1 ≤ 0.5
    then F.1 (p.1, ⟨min (p.2.1 + p.2.1) 1,
      le_min (add_nonneg p.2.2.1 p.2.2.1) zero_le_one, min_le_right _ _⟩)
    else G.1 (p.1, ⟨max (p.2.1 + p.2.1 - 1) 0, le_max_right _ _,
      max_le (sub_le_iff_le_add.2 (add_le_add p.2.2.2 p.2.2.2)) zero_le_one⟩),
  continuous := continuous_if
    (λ p hp, have p.2.1 = 0.5,
      from frontier_le_subset_eq (continuous_induced_dom.comp continuous_snd) continuous_const hp,
      by simp only [this, add_halves, sub_self, min_self, max_self]; erw [F.4, G.3])
    (F.2.comp $ continuous.prod_mk continuous_fst (continuous_induced_rng $
        continuous_min (continuous_add (continuous_induced_dom.comp continuous_snd)
            (continuous_induced_dom.comp continuous_snd))
          continuous_const))
    (G.2.comp $ continuous.prod_mk continuous_fst (continuous_induced_rng $
        continuous_max (continuous_sub (continuous_add (continuous_induced_dom.comp continuous_snd)
            (continuous_induced_dom.comp continuous_snd))
          continuous_const) continuous_const)),
  initial := λ s, by erw [if_pos (le_of_lt $ half_pos (zero_lt_one : (0:ℝ)<1))];
    simp only [set.Icc_zero_val, add_zero, min_eq_left (zero_le_one : (0:ℝ)≤1)]; exact F.3 s,
  final := λ s, by erw [if_neg (not_le_of_lt $ half_lt_self (zero_lt_one : (0:ℝ)<1))];
    simp only [set.Icc_one_val, add_sub_cancel, max_eq_left (zero_le_one : (0:ℝ)≤1)]; exact G.4 s,
  start := λ t, by dsimp only [path.comp]; split_ifs; simp only [F.5, G.5],
  finish := λ t, by dsimp only [path.comp]; split_ifs; simp only [F.6, G.6] }

def inv {f g : path x y} (F : homotopy f g) : homotopy f.inv g.inv :=
{ to_fun := λ p, F.1 (p.1, ⟨1 - p.2.1, sub_nonneg.2 p.2.2.2,
    sub_le.2 (by rw sub_self; exact p.2.2.1)⟩),
  continuous := F.2.comp $ continuous.prod_mk continuous_fst $ continuous_induced_rng $
    continuous_sub continuous_const (continuous_induced_dom.comp continuous_snd),
  initial := λ s, by simp only [set.Icc_zero_val, sub_zero]; convert F.4 s,
  final := λ s, by simp only [set.Icc_one_val, sub_self]; convert F.3 s,
  start := λ t, F.5 _,
  finish := λ t, F.6 _ }

noncomputable def comp_id (f : path x y) : homotopy (f.comp (path.id y)) f :=
{ to_fun := λ p, f.1 ⟨min ((2 - p.1.1) * p.2.1) 1, le_min
      (mul_nonneg (sub_nonneg_of_le $ le_trans p.1.2.2 $ le_add_of_nonneg_left zero_le_one) p.2.2.1)
      zero_le_one,
    min_le_right _ _⟩,
  continuous := f.2.comp $ continuous_induced_rng $ continuous_min
    (continuous_mul (continuous_sub continuous_const (continuous_induced_dom.comp continuous_fst))
      (continuous_induced_dom.comp continuous_snd))
    continuous_const,
  initial := λ s, by convert f.3; erw mul_zero; rw min_eq_left (zero_le_one : (0:ℝ) ≤ 1),
  final := λ s, have 1 ≤ 2 - s.1, from le_sub_iff_add_le.2 (add_le_add (le_refl _) s.2.2),
    by simp only [set.Icc_one_val, mul_one, min_eq_right this]; convert f.4,
  start := begin
    intros t, simp only [set.Icc_zero_val, sub_zero, min], split_ifs with h h,
    { rw path.comp_apply_le _ _ _ ((le_div_iff' two_pos).2 h), simp only [two_mul], refl },
    { rw [path.comp_apply_ge _ _ _ ((div_le_iff' two_pos).2 (le_of_not_le h)), path.id_apply],
      erw f.4 }
  end,
  finish := λ t, by simp only [set.Icc_one_val, bit0, add_sub_cancel, one_mul, min_eq_left t.2.2];
    cases t; refl }

noncomputable def comp_inv (f : path x y) : homotopy (f.comp f.inv) (path.id x) :=
{ to_fun := λ p, f.1 ⟨min (min (p.2.1+p.2.1) ((1-p.2.1)+(1-p.2.1))) (1-p.1.1), le_min (le_min
        (add_nonneg p.2.2.1 p.2.2.1)
        (add_nonneg (sub_nonneg.2 p.2.2.2) (sub_nonneg.2 p.2.2.2))) $
      sub_nonneg_of_le p.1.2.2,
    le_trans (min_le_right _ _) (sub_le_self _ p.1.2.1)⟩,
  continuous := f.2.comp (continuous_induced_rng $
    continuous_min (continuous_min
      (continuous_add (continuous_induced_dom.comp continuous_snd) $
        continuous_induced_dom.comp continuous_snd)
      (continuous_add (continuous_sub continuous_const (continuous_induced_dom.comp continuous_snd))
        (continuous_sub continuous_const $ continuous_induced_dom.comp continuous_snd)))
      (continuous_sub continuous_const $ continuous_induced_dom.comp continuous_fst)),
  initial := λ s, by simp only [set.Icc_zero_val, add_zero, sub_zero,
      min_eq_left (add_nonneg (zero_le_one : (0:ℝ)≤1) zero_le_one),
      min_eq_left (sub_nonneg_of_le s.2.2)]; convert f.3,
  final := λ s, by simp only [set.Icc_one_val, sub_self, add_zero,
      min_eq_right (add_nonneg (zero_le_one : (0:ℝ)≤1) zero_le_one),
      min_eq_left (sub_nonneg_of_le s.2.2)]; convert f.3,
  start := λ t, or.cases_on (le_total t.1 0.5)
    (λ ht, by rw path.comp_apply_le _ _ _ ht; congr' 2; simp only [set.Icc_zero_val, sub_zero];
      exact (min_eq_left $ le_trans (min_le_left _ _) $
          le_trans (add_le_add ht ht) $ by rw add_halves).trans
      (min_eq_left $ add_le_add (le_sub_iff_add_le.2 $
          le_trans (add_le_add ht ht) $ by rw add_halves) $
        le_sub_iff_add_le.2 $ le_trans (add_le_add ht ht) $ by rw add_halves))
    (λ ht, by rw [path.comp_apply_ge _ _ _ ht, path.inv_apply]; congr' 2;
      simp only [set.Icc_zero_val, sub_zero];
      rw [← sub_add, sub_add_eq_add_sub 1 (t.1 + t.1), add_sub_comm]; exact
      (min_eq_left $ le_trans (min_le_right _ _) $
        le_trans (add_le_add (sub_le_sub_left ht _) (sub_le_sub_left ht _)) $
        by rw [sub_half, add_halves]).trans
      (min_eq_right $ add_le_add (sub_le_iff_le_add.2 $
        le_trans (by rw add_halves) (add_le_add ht ht)) $
        sub_le_iff_le_add.2 $ le_trans (by rw add_halves) (add_le_add ht ht))),
  finish := λ t, by simp only [set.Icc_one_val, sub_self, path.id_apply];
    refine eq.trans _ f.3; congr' 2; exact
    min_eq_right (le_min (add_nonneg t.2.1 t.2.1) $
    add_nonneg (sub_nonneg.2 t.2.2) $ sub_nonneg.2 t.2.2) }

noncomputable def inv_comp (f : path x y) : homotopy (f.inv.comp f) (path.id y) :=
by convert comp_inv f.inv; rw f.inv_inv

noncomputable def id_comp (f : path x y) : homotopy ((path.id x).comp f) f :=
by convert (comp_id f.inv).inv; simp only [inv_inv, path.inv_comp, path.inv_inv, path.inv_id]

noncomputable def assoc (f : path w x) (g : path x y) (h : path y z) :
  homotopy ((f.comp g).comp h) (f.comp (g.comp h)) :=
{ to_fun := λ p, if 4 * p.2.1 / (1 + p.1.1) ≤ 1
    then f.1 ⟨min (4 * p.2.1 / (1 + p.1.1)) 1,
      le_min (div_nonneg (mul_nonneg (add_nonneg (le_of_lt two_pos) (le_of_lt two_pos)) p.2.2.1)
          (add_pos_of_pos_of_nonneg zero_lt_one p.1.2.1))
        zero_le_one,
      min_le_right _ _⟩
    else if 4 * p.2.1 - (1 + p.1.1) ≤ 1
    then g.1 ⟨max 0 (min (4 * p.2.1 - (1 + p.1.1)) 1), le_max_left _ _,
      max_le zero_le_one (min_le_right _ _)⟩
    else h.1 ⟨max 0 (1 - 4 * (1 - p.2.1) / (1 + (1 - p.1.1))), le_max_left _ _,
      max_le zero_le_one $ sub_le_self _ $ div_nonneg
        (mul_nonneg (add_nonneg (le_of_lt two_pos) (le_of_lt two_pos)) (sub_nonneg_of_le p.2.2.2)) $
      add_pos_of_pos_of_nonneg zero_lt_one $ sub_nonneg_of_le p.1.2.2⟩,
  continuous := have hc1 : _root_.continuous
      (λ p : set.Icc (0:ℝ) 1 × set.Icc (0:ℝ) 1, 4 * p.2.1 / (1 + p.1.1)),
    from continuous_mul (continuous_mul continuous_const $
        continuous_induced_dom.comp continuous_snd) $
      real.continuous_inv (λ p, ne_of_gt $ add_pos_of_pos_of_nonneg zero_lt_one p.1.2.1) $
      continuous_add continuous_const $ continuous_induced_dom.comp continuous_fst,
    continuous_if
    (λ p hp, have h1 : 4 * p.2.1 / (1 + p.1.1) = 1,
      from frontier_le_subset_eq hc1 continuous_const hp,
      have h2 : 4 * p.2.1 - (1 + p.1.1) = 0, from sub_eq_zero_of_eq $
        (div_eq_one_iff_eq _ $ ne_of_gt $ add_pos_of_pos_of_nonneg zero_lt_one p.1.2.1).1 h1,
      have h3 : 4 * p.2.1 - (1 + p.1.1) ≤ 1, from h2.symm ▸ zero_le_one,
      have h4 : max 0 (min (4 * p.2.1 - (1 + p.1.1)) 1) = 0,
      from max_eq_left $ le_trans (min_le_left _ _) $ by rw h2,
      by simp only [h1, min_self, if_pos h3, h4]; erw [f.4, g.3])
    (f.2.comp $ continuous_induced_rng $ continuous_min hc1 continuous_const) $
    have hc2 : _root_.continuous (λ p : set.Icc (0:ℝ) 1 × set.Icc (0:ℝ) 1, 4 * p.2.1 - (1 + p.1.1)),
    from continuous_sub (continuous_mul continuous_const $
        continuous_induced_dom.comp continuous_snd) $
      continuous_add continuous_const $ continuous_induced_dom.comp continuous_fst,
    continuous_if
      (λ p hp, have h1 : 4 * p.2.1 - (1 + p.1.1) = 1,
        from frontier_le_subset_eq hc2 continuous_const hp,
        have h2 : 4 * (1 - p.2.1) = 1 + (1 - p.1.1),
        by rw [mul_sub, mul_one, eq_add_of_sub_eq h1, ← sub_sub, ← sub_sub, ← add_sub_assoc,
            bit0, bit0, ← add_assoc, add_sub_cancel, add_sub_cancel],
        have h3 : 1 + (1 - p.1.1) ≠ 0,
        from ne_of_gt $ add_pos_of_pos_of_nonneg zero_lt_one $ sub_nonneg_of_le p.1.2.2,
        have h4 : 1 - 4 * (1 - p.2.1) / (1 + (1 - p.1.1)) = 0, by rw [h2, div_self h3, sub_self],
        by simp only [h1, min_self, max_eq_right (zero_le_one : (0:ℝ)≤1), h4, max_self];
          erw [g.4, h.3])
      (g.2.comp $ continuous_induced_rng $ continuous_max continuous_const $
        continuous_min hc2 continuous_const)
      (h.2.comp $ continuous_induced_rng $ continuous_max continuous_const $
        continuous_sub continuous_const $ continuous_mul
          (continuous_mul continuous_const $ continuous_sub continuous_const $
            continuous_induced_dom.comp continuous_snd) $
          real.continuous_inv (λ p, ne_of_gt $
            add_pos_of_pos_of_nonneg zero_lt_one $ sub_nonneg_of_le p.1.2.2) $
          continuous_add continuous_const $ continuous_sub continuous_const $
            continuous_induced_dom.comp continuous_fst),
  initial := λ p, by simp only [set.Icc_zero_val, mul_zero, zero_div, if_pos zero_le_one,
      min_eq_left (zero_le_one : (0:ℝ)≤1)]; convert f.3,
  final := λ p, have h1 : ¬(4 * 1 / (1 + p.1) ≤ 1),
    from not_le_of_lt $ lt_of_lt_of_le one_lt_two $ le_trans
    (le_div_of_mul_le two_pos $ by rw [two_mul, mul_one]; refl : (2:ℝ) ≤ (4*1/(1+1):ℝ)) $
    (div_le_div_left (by rw mul_one; exact add_pos two_pos two_pos) two_pos $
      add_pos_of_pos_of_nonneg (zero_lt_one : (0:ℝ)<1) p.2.1).2 $
    add_le_add_left p.2.2 _,
    have h2 : ¬(4 * 1 - (1 + p.1) ≤ 1),
    from not_le_of_lt $ lt_sub_right_of_add_lt $ lt_of_le_of_lt
      (add_le_add_left (add_le_add_left p.2.2 _) _) $
      by rw mul_one; exact add_lt_add_right one_lt_two _,
    eq.trans (if_neg h1) $ eq.trans (if_neg h2) $
    by simp only [set.Icc_one_val, sub_self, mul_zero, zero_div, sub_zero,
        max_eq_right (zero_le_one : (0:ℝ)≤1)]; convert h.4,
  start := begin
    intros t, simp only [set.Icc_zero_val, add_zero, div_one, sub_zero],
    have ha1 : t.1 ≤ 0.25 ↔ 4 * t.1 ≤ 1 := le_div_iff' (add_pos two_pos two_pos),
    have ha2 : (0.25:ℝ) + 0.25 = 0.5 := by rw [← two_mul, ← mul_div_assoc, mul_one, bit0, bit0,
        ← two_mul, ← two_mul, mul_div_mul_left _
          (show (2 * 1:ℝ) ≠ 0, by rw mul_one; exact ne_of_gt two_pos) (ne_of_gt two_pos)],
    have ha3 : (0.25:ℝ) ≤ 0.5 := ha2 ▸ le_add_of_nonneg_left
      (le_of_lt $ one_div_pos_of_pos $ add_pos two_pos two_pos),
    have ha4 : (4:ℝ) * 0.5 = 1 + 1,
    by rw [← mul_div_assoc, mul_one, bit0, add_div, div_self (ne_of_gt two_pos)],
    have ha5 : t.1 ≤ 0.5 ↔ 4 * t.1 - 1 ≤ 1,
    by rw [sub_le_iff_le_add, ← mul_le_mul_left (show 0<(4:ℝ), from add_pos two_pos two_pos), ha4],
    by_cases ht1 : t.1 ≤ 0.25,
    { have h2 : t.1 ≤ 0.5 := le_trans ht1 ha3,
      have h3 : t.1 + t.1 ≤ 0.5 := le_trans (add_le_add ht1 ht1)
        (by rw [← two_mul, ← mul_div_assoc, mul_one, bit0, bit0, ← two_mul, ← two_mul,
            mul_div_mul_left _ (show (2 * 1:ℝ) ≠ 0, by rw mul_one; exact ne_of_gt two_pos)
              (ne_of_gt two_pos)]),
      convert eq.trans (if_pos (ha1.1 ht1)) _,
      rw [path.comp_apply_le _ _ _ h2, path.comp_apply_le], swap, exact h3, congr' 2,
      rw [min_eq_left (ha1.1 ht1), bit0, add_mul, two_mul] },
    by_cases ht2 : t.1 ≤ 0.5,
    { have h1 : 0.5 ≤ t.1 + t.1 := ha2 ▸ add_le_add (le_of_not_le ht1) (le_of_not_le ht1),
      convert eq.trans (if_neg ((not_congr ha1).1 ht1)) (eq.trans (if_pos (ha5.1 ht2)) _),
      rw [path.comp_apply_le _ _ _ ht2, path.comp_apply_ge], swap, exact h1, congr' 2,
      rw min_eq_left (ha5.1 ht2),
      rw max_eq_right (sub_nonneg_of_le $ le_of_not_le $ (not_congr ha1).1 ht1),
      rw [bit0, add_mul, two_mul] },
    { have h1 : 0 ≤ 1 - 4 * (1 - t.1) / (1 + 1) := sub_nonneg_of_le
        (by rw [mul_div_right_comm, bit0, bit0, add_div,
            div_self (ne_of_gt $ add_pos (zero_lt_one : (0:ℝ)<1) zero_lt_one),
            mul_sub, mul_one, sub_le, add_sub_cancel, add_mul, one_mul]; exact
          le_trans (by rw add_halves) (add_le_add (le_of_not_le ht2) (le_of_not_le ht2))),
      convert eq.trans (if_neg ((not_congr ha1).1 ht1))
        (eq.trans (if_neg ((not_congr ha5).1 ht2)) _),
      rw path.comp_apply_ge _ _ _ (le_of_not_le ht2), congr' 2, rw max_eq_right h1,
      rw [mul_div_right_comm, bit0, bit0, add_div],
      rw [div_self (ne_of_gt $ add_pos (zero_lt_one : (0:ℝ)<1) zero_lt_one), mul_sub, mul_one],
      rw [← sub_add, sub_add_eq_add_sub, ← sub_sub, add_sub_cancel', add_mul, one_mul] }
  end,
  finish := begin
    intros t, dsimp only [set.Icc_one_val],
    have ha1 : 4 * t.1 / (1 + 1) ≤ 1 ↔ t.1 ≤ 0.5 :=
    by rw [div_le_iff (show (1:ℝ)+1>0, from two_pos), one_mul,
        ← le_div_iff' (show (4:ℝ)>0, from add_pos two_pos two_pos), bit0,
        ← two_mul, ← two_mul, mul_div_mul_left _ (ne_of_gt two_pos) (ne_of_gt two_pos)],
    have ha2 : 4 * t.1 - (1 + 1) ≤ 1 ↔ t.1 + t.1 - 1 ≤ 0.5 :=
    by rw [sub_le_iff_le_add, sub_le_iff_le_add, ← two_mul t.1, ← le_div_iff' two_pos,
        ← le_div_iff' (show (4:ℝ)>0, from add_pos two_pos two_pos),
        add_div (0.5:ℝ), field.div_div_eq_div_mul _ (ne_of_gt two_pos) (ne_of_gt two_pos),
        div_add_div _ _ (ne_of_gt $ mul_pos (two_pos : (2:ℝ)>0) two_pos) (ne_of_gt two_pos),
        mul_one, ← add_mul, mul_div_mul_right' _ _ (ne_of_gt (two_pos : (2:ℝ)>0)), two_mul]; refl,
    split_ifs with ht1 ht2,
    { rw path.comp_apply_le _ _ _ (ha1.1 ht1), congr' 2,
      rw [min_eq_left ht1, mul_div_right_comm, bit0, ← two_mul, ← two_mul,
          mul_div_mul_left _ one_ne_zero (ne_of_gt two_pos), div_one, two_mul] },
    { have h1 : 0 ≤ 4 * t.1 - (1 + 1) :=
        sub_nonneg_of_le ((one_le_div_iff_le two_pos).1 (le_of_not_le ht1)),
      rw path.comp_apply_ge _ _ _ (le_of_not_le $ (not_congr ha1).1 ht1),
      rw path.comp_apply_le, swap, exact ha2.1 ht2, congr' 2, dsimp only,
      rw [min_eq_left ht2, max_eq_right h1, bit0, add_mul, add_sub_comm, two_mul] },
    { have h1 : 0 ≤ 4 * t.1 + 1 - 4,
      exact sub_nonneg_of_le (sub_le_iff_le_add.1 $ (sub_le_sub_iff_right (1+1)).1 $ le_trans
        (by rw [bit0, bit0, ← sub_sub, ← add_assoc, add_sub_cancel, add_sub_cancel, add_sub_cancel])
        (le_of_not_le ht2)),
      rw path.comp_apply_ge _ _ _ (le_of_not_le $ (not_congr ha1).1 ht1),
      rw path.comp_apply_ge, swap, exact (le_of_not_le $ (not_congr ha2).1 ht2),
      congr' 2, dsimp only,
      rw [sub_self, add_zero, div_one, mul_sub, mul_one, ← sub_add, add_comm, ← add_sub_assoc],
      rw [max_eq_right h1, bit0, add_mul, ← add_sub_comm, two_mul, ← sub_sub, ← sub_sub, bit0],
      rw [← sub_sub, ← sub_sub, add_sub_cancel] }
  end }

end homotopy

instance path.setoid (x y : X) : setoid (path x y) :=
{ r := λ f g, nonempty (homotopy f g),
  iseqv := ⟨λ f, ⟨homotopy.refl f⟩, λ f g ⟨F⟩, ⟨F.symm⟩, λ f g h ⟨F⟩ ⟨G⟩, ⟨F.trans G⟩⟩ }

noncomputable instance fundamental_groupoid (X : Type u) [topological_space X] :
  category_theory.groupoid X :=
{ hom := λ x y, quotient (path.setoid x y),
  id := λ x, ⟦path.id x⟧,
  comp := λ x y z p q, quotient.lift_on₂ p q (λ f g, (⟦f.comp g⟧ : quotient (path.setoid x z))) $
    λ p₁ p₂ q₁ q₂ ⟨F⟩ ⟨G⟩, quotient.sound ⟨F.comp G⟩,
  comp_id' := λ x y p, quotient.induction_on p $ λ f, quotient.sound ⟨homotopy.comp_id f⟩,
  id_comp' := λ x y p, quotient.induction_on p $ λ f, quotient.sound ⟨homotopy.id_comp f⟩,
  assoc' := λ w x y z p q r, quotient.induction_on₃ p q r $ λ f g h,
    quotient.sound ⟨homotopy.assoc f g h⟩,
  inv := λ x y p, quotient.lift_on p (λ f, ⟦f.inv⟧) $ λ f g ⟨F⟩, quotient.sound ⟨F.inv⟩,
  inv_comp' := λ x y p, quotient.induction_on p $ λ f, quotient.sound ⟨homotopy.inv_comp f⟩,
  comp_inv' := λ x y p, quotient.induction_on p $ λ f, quotient.sound ⟨homotopy.comp_inv f⟩ }
