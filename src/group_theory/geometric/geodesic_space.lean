/-
Copyright (c) 2022 Georgi Kocharyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgi Kocharyan
-/
import .quasi_iso
import topology.metric_space.isometry
import topology.unit_interval

open_locale unit_interval

variables {X : Type*} [pseudo_metric_space X] {f : ℝ → X} {b c L L' : ℝ} {x y : X}

def geodesic (L : ℝ) (Lnonneg : 0 ≤ L) (f : ((set.Icc) (0 : ℝ) L) → X) (x y : X) :=
f (⟨0, le_rfl, Lnonneg⟩) = x ∧ f (⟨L, Lnonneg, le_rfl⟩) = y ∧ isometry f

def conn_by_geodesic (x y : X) : Prop :=
∃ (L : ℝ) (Lpos : 0 ≤ L) (f : ((set.Icc) (0 : ℝ) L) → X), geodesic L Lpos f x y

class geodesic_space (β : Type*) extends pseudo_metric_space β :=
(geodesics : ∀ x y : β, conn_by_geodesic x y)

-- def quasigeodesic (L : ℝ) (Lnonneg : 0 ≤ L) (f: ((set.Icc) (0 : ℝ) L) → X)
--  (x y : X) (c b : ℝ) :=
--  f (⟨0, le_rfl, Lnonneg⟩) = x ∧ f (⟨L, Lnonneg, le_rfl⟩) = y ∧ is_QIE' f c b

/-- Quasi-geodesic connecting two points `x` and `y` in a metric space. -/
@[nolint has_nonempty_instance]
structure bundled_quasigeodesic (x y : X) (c b : ℝ) :=
(to_fun : I → X)
(source' : to_fun 0 = x)
(target' : to_fun 1 = y)
(quasi_iso_lower' : ∀ m n, c⁻¹ * dist m n - b ≤ dist (f m) (f n))
(quasi_iso_upper' : ∀ m n, dist (f m) (f n) ≤ c * dist m n + b)

def quasigeodesic (L : ℝ) (f : ℝ → X) (x y : X) (c b : ℝ) :=
f 0 = x ∧ f L = y ∧ ∀ ⦃m⦄, m ∈ set.Icc 0 L → ∀ ⦃n⦄, n ∈ set.Icc 0 L →
  c⁻¹ * |m - n| - b ≤ dist (f m) (f n) ∧ dist (f m) (f n) ≤ c * |m - n| + b

/-- Any segment of a quasigeodesic is also a quasigeodesic. -/
lemma quasigeodesic.mono (f : ℝ → X) (hL' : L' ≤ L) (hf : quasigeodesic L f x y c b) :
  quasigeodesic L' f x (f L') c b :=
⟨hf.1, rfl, λ a ha b hb, hf.2.2 ⟨ha.1, ha.2.trans hL'⟩ ⟨hb.1, hb.2.trans hL'⟩⟩

lemma quasigeodesic.symm (hf : quasigeodesic L f x y c b) :
  quasigeodesic L (λ x, f (L - x)) y x c b :=
⟨by simp_rw [sub_zero, hf.2.1], by simp_rw [sub_self, hf.1], λ m hm n hn,
  by simpa [and.comm, abs_sub_comm] using hf.2.2 ⟨sub_nonneg.2 hm.2,
    sub_le_self _ hm.1⟩ ⟨sub_nonneg.2 hn.2, sub_le_self _ hn.1⟩⟩

/-- If a geodesic has length `0`, the endpoints are the same. -/
lemma degenerate_quasigeodesic (f: ℝ → X) (x y : X) (c b : ℝ) (hf : quasigeodesic 0 f x y c b) :
  x = y :=
hf.1.symm.trans hf.2.1

def conn_by_quasigeodesic (x y : X) : Prop :=
∃ (L : ℝ) (hL : 0 ≤ L) (f : ℝ → X) (c b : ℝ), quasigeodesic L f x y c b

def conn_by_quasigeodesic' (x y : X) (c b : ℝ) : Prop :=
∃ (L : ℝ) (hL : 0 ≤ L) (f : ℝ → X), quasigeodesic L f x y c b

lemma conn_by_quasigeodesic'.symm : conn_by_quasigeodesic' x y c b → conn_by_quasigeodesic' y x c b :=
λ ⟨L, hL, f, hf⟩, ⟨L, hL, _, hf.symm⟩

class quasigeodesic_space (β : Type*) (c b : out_param ℝ) extends pseudo_metric_space β :=
(quasigeodesics : ∀ x y : β, conn_by_quasigeodesic' x y c b)

attribute [nolint dangerous_instance] quasigeodesic_space.to_pseudo_metric_space
