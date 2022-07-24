/-
Copyright (c) 2022 Georgi Kocharyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Authors: Georgi Kocharyan
-/
import .quasi_iso
import tactic
import data.real.basic
import topology.metric_space.isometry

variables {X : Type*} [pseudo_metric_space X]

def geodesic {X : Type*} [pseudo_metric_space X] (L : ℝ) (Lnonneg : L ≥ 0) (f: ((set.Icc) (0 : ℝ) L) → X) (x : X) (y: X) :=
 f (⟨0, le_rfl, Lnonneg⟩) = x ∧ f (⟨L, Lnonneg, le_rfl⟩) = y ∧ isometry f

def conn_by_geodesic {X : Type*} [pseudo_metric_space X] (x : X) (y: X) : Prop :=
∃ (L : ℝ) (Lpos : L ≥ 0) (f: ((set.Icc) (0 : ℝ) L) → X), geodesic L Lpos f x y

class geodesic_space (β : Type*)  extends pseudo_metric_space β :=
(geodesics: ∀ x y : β, conn_by_geodesic x y)

-- def quasigeodesic {X : Type*} [pseudo_metric_space X] (L : ℝ) (Lnonneg : L ≥ 0) (f: ((set.Icc) (0 : ℝ) L) → X)
--  (x : X) (y: X) (c : ℝ) (b : ℝ) :=
--  f (⟨0, le_rfl, Lnonneg⟩) = x ∧ f (⟨L, Lnonneg, le_rfl⟩) = y ∧ is_QIE' f c b

def quasigeodesic {X : Type*} [pseudo_metric_space X] (L : ℝ) (Lnonneg : L ≥ 0) (f: ℝ → X)
 (x : X) (y: X) (c : ℝ) (b : ℝ) :=
 f 0 = x ∧ f L = y ∧ (∀ m n  ∈ {x : ℝ| 0 ≤ x ∧ x ≤ L}, (1/c)*(abs (m-n)) - b ≤ dist (f m) (f n) ∧ dist (f m) (f n) ≤ c * (abs (m-n)) + b)

-- any segment of a quasigeodesic is also a quasigeodesic

lemma trunc_quasigeodesic {X : Type*} [pseudo_metric_space X] (L : ℝ) (Lnonneg : L ≥ 0) (f: ℝ → X)
 (x : X) (y: X) (c : ℝ) (b : ℝ) {L' : ℝ} (hL' : L' ≤ L) (L'nonneg : L' ≥ 0) (hf : quasigeodesic L Lnonneg f x y c b)
  : quasigeodesic L' L'nonneg f x (f L') c b :=
begin
split,
exact hf.1,
split, refl,
intros a ha b hb,
have ha' : a ∈ {x : ℝ| 0 ≤ x ∧ x ≤ L},
  { exact ⟨ha.1, le_trans ha.2 hL'⟩, },
have hb' : b ∈ {x : ℝ| 0 ≤ x ∧ x ≤ L},
  { exact ⟨hb.1, le_trans hb.2 hL'⟩,},
apply (hf.2).2 a ha' b hb',
end

-- if a geodesic has length 0, the endpoints are the same

lemma degenerate_quasigeodesic {X : Type*} [pseudo_metric_space X] (f: ℝ → X)
 (x : X) (y: X) (c : ℝ) (b : ℝ) (hf : quasigeodesic 0 (le_refl 0) f x y c b) : x = y :=
 eq.trans (hf.1.symm) hf.2.1


def conn_by_quasigeodesic {X : Type*} [pseudo_metric_space X] (x : X) (y: X) : Prop :=
∃ (L : ℝ) (Lnonneg : L ≥ 0) (f: ℝ → X) (c : ℝ) (b : ℝ), quasigeodesic L Lnonneg f x y c b

def conn_by_quasigeodesic' {X : Type*} [pseudo_metric_space X] (x : X) (y: X) (c : ℝ) (b : ℝ) : Prop :=
∃ (L : ℝ) (Lnonneg : L ≥ 0) (f: ℝ → X) , quasigeodesic L Lnonneg f x y c b

class quasigeodesic_space (β : Type*) (c : ℝ) (b : ℝ) (cpos: c > 0) (bnonneg: b ≥ 0)  extends pseudo_metric_space β :=
(quasigeodesics: ∀ x y : β, conn_by_quasigeodesic' x y c b)
