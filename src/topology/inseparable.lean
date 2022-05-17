/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.basic
import data.setoid.basic
import tactic.tfae

/-!
-/

open set filter function
open_locale topological_space filter

variables {X Y : Type*} [topological_space X] [topological_space Y] {x y : X}
  {s : set X}

lemma nhds_le_nhds_tfae (x y : X) :
  tfae [𝓝 x ≤ 𝓝 y,
    pure x ≤ 𝓝 y,
    ∀ s : set X, is_open s → y ∈ s → x ∈ s,
    ∀ s : set X, is_closed s → x ∈ s → y ∈ s,
    y ∈ closure ({x} : set X),
    cluster_pt y (pure x)] :=
begin
  tfae_have : 1 → 2, from (pure_le_nhds _).trans,
  tfae_have : 2 → 3, from λ h s hso hy, h (hso.mem_nhds hy),
  tfae_have : 3 → 4, from λ h s hsc hx, of_not_not $ λ hy, h sᶜ hsc.is_open_compl hy hx,
  tfae_have : 4 → 5, from λ h, h _ is_closed_closure (subset_closure $ mem_singleton _),
  tfae_have : 5 ↔ 6, by rw [mem_closure_iff_cluster_pt, principal_singleton],
  tfae_have : 6 → 1,
  { refine λ h, (nhds_basis_opens _).ge_iff.2 _,
    rintro s ⟨hy, ho⟩,
    have := cluster_pt_iff.1 h (ho.mem_nhds hy) (mem_pure.2 $ mem_singleton _),
    exact ho.mem_nhds (inter_singleton_nonempty.1 this) },
  tfae_finish
end

lemma nhds_le_nhds_iff_open : 𝓝 x ≤ 𝓝 y ↔ ∀ ⦃s : set X⦄, is_open s → y ∈ s → x ∈ s :=
(nhds_le_nhds_tfae x y).out 0 2

lemma nhds_le_nhds_iff_closed : 𝓝 x ≤ 𝓝 y ↔ ∀ ⦃s : set X⦄, is_closed s → x ∈ s → y ∈ s :=
(nhds_le_nhds_tfae x y).out 0 3

lemma nhds_le_nhds_iff_mem_closure : 𝓝 x ≤ 𝓝 y ↔ y ∈ closure ({x} : set X) :=
(nhds_le_nhds_tfae x y).out 0 4

lemma nhds_le_nhds_iff_cluster_pt : 𝓝 x ≤ 𝓝 y ↔ cluster_pt y (pure x) :=
(nhds_le_nhds_tfae x y).out 0 5

def inseparable (x y : X) : Prop := 𝓝 x = 𝓝 y

local infix ` ~ ` := inseparable

lemma inseparable_def : x ~ y ↔ 𝓝 x = 𝓝 y := iff.rfl
lemma inseparable.nhds_eq (h : x ~ y) : 𝓝 x = 𝓝 y := h

lemma inseparable_tfae (x y : X) :
  tfae [x ~ y,
    pure x ≤ 𝓝 y ∧ pure y ≤ 𝓝 x,
    ∀ s : set X, is_open s → (x ∈ s ↔ y ∈ s),
    ∀ s : set X, is_closed s → (x ∈ s ↔ y ∈ s),
    x ∈ closure ({y} : set X) ∧ y ∈ closure ({x} : set X),
    cluster_pt y (pure x) ∧ cluster_pt x (pure y)] :=
by simpa [← le_antisymm_iff, ← forall_and_distrib, ← iff_def, iff.comm, and_comm]
  using (nhds_le_nhds_tfae x y).zip_with (nhds_le_nhds_tfae y x) (∧)

lemma inseparable_iff_open : x ~ y ↔ ∀ s : set X, is_open s → (x ∈ s ↔ y ∈ s) :=
(inseparable_tfae x y).out 0 2

lemma not_inseparable_iff_open : ¬(x ~ y) ↔ ∃ s : set X, is_open s ∧ xor (x ∈ s) (y ∈ s) :=
by simp [inseparable_iff_open, ← xor_iff_not_iff]

lemma inseparable.mem_open_iff (h : x ~ y) (hs : is_open s) : x ∈ s ↔ y ∈ s :=
inseparable_iff_open.1 h s hs

lemma inseparable_iff_closed : x ~ y ↔ ∀ s : set X, is_closed s → (x ∈ s ↔ y ∈ s) :=
(inseparable_tfae x y).out 0 3

lemma inseparable.mem_closed_iff (h : x ~ y) (hs : is_closed s) : x ∈ s ↔ y ∈ s :=
inseparable_iff_closed.1 h s hs

variable (X)

def inseparable_setoid : setoid X :=
{ r := (~),
  .. setoid.comap 𝓝 ⊥ }

def inseparable_quotient := quotient (inseparable_setoid X)
