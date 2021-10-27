/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Heather Macbeth
-/
import topology.algebra.ordered.basic
import topology.algebra.ordered.left_right

/-!
# Continuity of monotone functions

In this file we prove the following fact: if `f` is a monotone function on a neighborhood of `a`
and the image of this neighborhood is a neighborhood of `f a`, then `f` is continuous at `a`, see
`continuous_at_of_monotone_on_of_image_mem_nhds`, as well as several similar facts.

We also prove that an `order_iso` is continuous.

## Tags

continuous, monotone
-/

open set filter
open_locale topological_space

section linear_order
variables {α β : Type*} [linear_order α] [topological_space α] [order_topology α]
variables [linear_order β] [topological_space β] [order_topology β]

/-- If `f` is a function strictly monotone on a right neighborhood of `a` and the
image of this neighborhood under `f` meets every interval `(f a, b]`, `b > f a`, then `f` is
continuous at `a` from the right.

The assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b` is required because otherwise the
function `f : ℝ → ℝ` given by `f x = if x ≤ 0 then x else x + 1` would be a counter-example at
`a = 0`. -/
lemma strict_mono_on.continuous_at_right_of_exists_between {f : α → β} {s : set α} {a : α}
  (h_mono : strict_mono_on f s) (hs : s ∈ 𝓝[Ici a] a)
  (hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b) :
  continuous_within_at f (Ici a) a :=
begin
  have ha : a ∈ Ici a := left_mem_Ici,
  have has : a ∈ s := mem_of_mem_nhds_within ha hs,
  refine tendsto_order.2 ⟨λ b hb, _, λ b hb, _⟩,
  { filter_upwards [hs, self_mem_nhds_within],
    intros x hxs hxa,
    exact hb.trans_le ((h_mono.le_iff_le has hxs).2 hxa) },
  { rcases hfs b hb with ⟨c, hcs, hac, hcb⟩,
    rw [h_mono.lt_iff_lt has hcs] at hac,
    filter_upwards [hs, Ico_mem_nhds_within_Ici (left_mem_Ico.2 hac)],
    rintros x hx ⟨hax, hxc⟩,
    exact ((h_mono.lt_iff_lt hx hcs).2 hxc).trans_le hcb }
end

/-- If `f` is a monotone function on a right neighborhood of `a` and the image of this neighborhood
under `f` meets every interval `(f a, b)`, `b > f a`, then `f` is continuous at `a` from the right.

The assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b` cannot be replaced by the weaker
assumption `hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b` we use for strictly monotone functions
because otherwise the function `ceil : ℝ → ℤ` would be a counter-example at `a = 0`. -/
lemma continuous_at_right_of_monotone_on_of_exists_between {f : α → β} {s : set α} {a : α}
  (h_mono : monotone_on f s) (hs : s ∈ 𝓝[Ici a] a)
  (hfs : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b) :
  continuous_within_at f (Ici a) a :=
begin
  have ha : a ∈ Ici a := left_mem_Ici,
  have has : a ∈ s := mem_of_mem_nhds_within ha hs,
  refine tendsto_order.2 ⟨λ b hb, _, λ b hb, _⟩,
  { filter_upwards [hs, self_mem_nhds_within],
    intros x hxs hxa,
    exact hb.trans_le (h_mono has hxs hxa) },
  { rcases hfs b hb with ⟨c, hcs, hac, hcb⟩,
    have : a < c, from not_le.1 (λ h, hac.not_le $ h_mono hcs has h),
    filter_upwards [hs, Ico_mem_nhds_within_Ici (left_mem_Ico.2 this)],
    rintros x hx ⟨hax, hxc⟩,
    exact (h_mono hx hcs hxc.le).trans_lt hcb }
end

/-- If a function `f` with a densely ordered codomain is monotone on a right neighborhood of `a` and
the closure of the image of this neighborhood under `f` is a right neighborhood of `f a`, then `f`
is continuous at `a` from the right. -/
lemma continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within [densely_ordered β]
  {f : α → β} {s : set α} {a : α} (h_mono : monotone_on f s)
  (hs : s ∈ 𝓝[Ici a] a) (hfs : closure (f '' s) ∈ 𝓝[Ici (f a)] (f a)) :
  continuous_within_at f (Ici a) a :=
begin
  refine continuous_at_right_of_monotone_on_of_exists_between h_mono hs (λ b hb, _),
  rcases (mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hb).1 hfs with ⟨b', ⟨hab', hbb'⟩, hb'⟩,
  rcases exists_between hab' with ⟨c', hc'⟩,
  rcases mem_closure_iff.1 (hb' ⟨hc'.1.le, hc'.2⟩) (Ioo (f a) b') is_open_Ioo hc'
    with ⟨_, hc, ⟨c, hcs, rfl⟩⟩,
  exact ⟨c, hcs, hc.1, hc.2.trans_le hbb'⟩
end

/-- If a function `f` with a densely ordered codomain is monotone on a right neighborhood of `a` and
the image of this neighborhood under `f` is a right neighborhood of `f a`, then `f` is continuous at
`a` from the right. -/
lemma continuous_at_right_of_monotone_on_of_image_mem_nhds_within [densely_ordered β] {f : α → β}
  {s : set α} {a : α} (h_mono : monotone_on f s) (hs : s ∈ 𝓝[Ici a] a)
  (hfs : f '' s ∈ 𝓝[Ici (f a)] (f a)) :
  continuous_within_at f (Ici a) a :=
continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within h_mono hs $
  mem_of_superset hfs subset_closure

/-- If a function `f` with a densely ordered codomain is strictly monotone on a right neighborhood
of `a` and the closure of the image of this neighborhood under `f` is a right neighborhood of `f a`,
then `f` is continuous at `a` from the right. -/
lemma strict_mono_on.continuous_at_right_of_closure_image_mem_nhds_within [densely_ordered β]
  {f : α → β} {s : set α} {a : α} (h_mono : strict_mono_on f s) (hs : s ∈ 𝓝[Ici a] a)
  (hfs : closure (f '' s) ∈ 𝓝[Ici (f a)] (f a)) :
  continuous_within_at f (Ici a) a :=
continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within
  (λ x hx y hy, (h_mono.le_iff_le hx hy).2) hs hfs

/-- If a function `f` with a densely ordered codomain is strictly monotone on a right neighborhood
of `a` and the image of this neighborhood under `f` is a right neighborhood of `f a`, then `f` is
continuous at `a` from the right. -/
lemma strict_mono_on.continuous_at_right_of_image_mem_nhds_within [densely_ordered β]
  {f : α → β} {s : set α} {a : α} (h_mono : strict_mono_on f s) (hs : s ∈ 𝓝[Ici a] a)
  (hfs : f '' s ∈ 𝓝[Ici (f a)] (f a)) :
  continuous_within_at f (Ici a) a :=
h_mono.continuous_at_right_of_closure_image_mem_nhds_within hs
  (mem_of_superset hfs subset_closure)

/-- If a function `f` is strictly monotone on a right neighborhood of `a` and the image of this
neighborhood under `f` includes `Ioi (f a)`, then `f` is continuous at `a` from the right. -/
lemma strict_mono_on.continuous_at_right_of_surj_on {f : α → β} {s : set α} {a : α}
  (h_mono : strict_mono_on f s) (hs : s ∈ 𝓝[Ici a] a) (hfs : surj_on f s (Ioi (f a))) :
  continuous_within_at f (Ici a) a :=
h_mono.continuous_at_right_of_exists_between hs $ λ b hb, let ⟨c, hcs, hcb⟩ := hfs hb in
⟨c, hcs, hcb.symm ▸ hb, hcb.le⟩

/-- If `f` is a strictly monotone function on a left neighborhood of `a` and the image of this
neighborhood under `f` meets every interval `[b, f a)`, `b < f a`, then `f` is continuous at `a`
from the left.

The assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)` is required because otherwise the
function `f : ℝ → ℝ` given by `f x = if x < 0 then x else x + 1` would be a counter-example at
`a = 0`. -/
lemma strict_mono_on.continuous_at_left_of_exists_between {f : α → β} {s : set α} {a : α}
  (h_mono : strict_mono_on f s) (hs : s ∈ 𝓝[Iic a] a)
  (hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)) :
  continuous_within_at f (Iic a) a :=
h_mono.dual.continuous_at_right_of_exists_between hs $
  λ b hb, let ⟨c, hcs, hcb, hca⟩ := hfs b hb in ⟨c, hcs, hca, hcb⟩

/-- If `f` is a monotone function on a left neighborhood of `a` and the image of this neighborhood
under `f` meets every interval `(b, f a)`, `b < f a`, then `f` is continuous at `a` from the left.

The assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a)` cannot be replaced by the weaker
assumption `hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)` we use for strictly monotone functions
because otherwise the function `floor : ℝ → ℤ` would be a counter-example at `a = 0`. -/
lemma continuous_at_left_of_monotone_on_of_exists_between {f : α → β} {s : set α} {a : α}
  (hf : monotone_on f s) (hs : s ∈ 𝓝[Iic a] a)
  (hfs : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a)) :
  continuous_within_at f (Iic a) a :=
@continuous_at_right_of_monotone_on_of_exists_between (order_dual α) (order_dual β) _ _ _ _ _ _
  f s a hf.dual hs $
  λ b hb, let ⟨c, hcs, hcb, hca⟩ := hfs b hb in ⟨c, hcs, hca, hcb⟩

/-- If a function `f` with a densely ordered codomain is monotone on a left neighborhood of `a` and
the closure of the image of this neighborhood under `f` is a left neighborhood of `f a`, then `f` is
continuous at `a` from the left -/
lemma continuous_at_left_of_monotone_on_of_closure_image_mem_nhds_within [densely_ordered β]
  {f : α → β} {s : set α} {a : α} (hf : monotone_on f s)
  (hs : s ∈ 𝓝[Iic a] a) (hfs : closure (f '' s) ∈ 𝓝[Iic (f a)] (f a)) :
  continuous_within_at f (Iic a) a :=
@continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within (order_dual α) (order_dual β)
  _ _ _ _ _ _ _ f s a hf.dual hs hfs

/-- If a function `f` with a densely ordered codomain is monotone on a left neighborhood of `a` and
the image of this neighborhood under `f` is a left neighborhood of `f a`, then `f` is continuous at
`a` from the left. -/
lemma continuous_at_left_of_monotone_on_of_image_mem_nhds_within [densely_ordered β]
  {f : α → β} {s : set α} {a : α} (h_mono : monotone_on f s)
  (hs : s ∈ 𝓝[Iic a] a) (hfs : f '' s ∈ 𝓝[Iic (f a)] (f a)) :
  continuous_within_at f (Iic a) a :=
continuous_at_left_of_monotone_on_of_closure_image_mem_nhds_within h_mono hs
  (mem_of_superset hfs subset_closure)

/-- If a function `f` with a densely ordered codomain is strictly monotone on a left neighborhood of
`a` and the closure of the image of this neighborhood under `f` is a left neighborhood of `f a`,
then `f` is continuous at `a` from the left. -/
lemma strict_mono_on.continuous_at_left_of_closure_image_mem_nhds_within [densely_ordered β]
  {f : α → β} {s : set α} {a : α} (h_mono : strict_mono_on f s) (hs : s ∈ 𝓝[Iic a] a)
  (hfs : closure (f '' s) ∈ 𝓝[Iic (f a)] (f a)) :
  continuous_within_at f (Iic a) a :=
h_mono.dual.continuous_at_right_of_closure_image_mem_nhds_within hs hfs

/-- If a function `f` with a densely ordered codomain is strictly monotone on a left neighborhood of
`a` and the image of this neighborhood under `f` is a left neighborhood of `f a`, then `f` is
continuous at `a` from the left. -/
lemma strict_mono_on.continuous_at_left_of_image_mem_nhds_within [densely_ordered β]
  {f : α → β} {s : set α} {a : α} (h_mono : strict_mono_on f s) (hs : s ∈ 𝓝[Iic a] a)
  (hfs : f '' s ∈ 𝓝[Iic (f a)] (f a)) :
  continuous_within_at f (Iic a) a :=
h_mono.dual.continuous_at_right_of_image_mem_nhds_within hs hfs

/-- If a function `f` is strictly monotone on a left neighborhood of `a` and the image of this
neighborhood under `f` includes `Iio (f a)`, then `f` is continuous at `a` from the left. -/
lemma strict_mono_on.continuous_at_left_of_surj_on {f : α → β} {s : set α} {a : α}
  (h_mono : strict_mono_on f s) (hs : s ∈ 𝓝[Iic a] a) (hfs : surj_on f s (Iio (f a))) :
  continuous_within_at f (Iic a) a :=
h_mono.dual.continuous_at_right_of_surj_on hs hfs

/-- If a function `f` is strictly monotone on a neighborhood of `a` and the image of this
neighborhood under `f` meets every interval `[b, f a)`, `b < f a`, and every interval
`(f a, b]`, `b > f a`, then `f` is continuous at `a`. -/
lemma strict_mono_on.continuous_at_of_exists_between {f : α → β} {s : set α} {a : α}
  (h_mono : strict_mono_on f s) (hs : s ∈ 𝓝 a)
  (hfs_l : ∀ b < f a, ∃ c ∈ s, f c ∈ Ico b (f a)) (hfs_r : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioc (f a) b) :
  continuous_at f a :=
continuous_at_iff_continuous_left_right.2
  ⟨h_mono.continuous_at_left_of_exists_between (mem_nhds_within_of_mem_nhds hs) hfs_l,
   h_mono.continuous_at_right_of_exists_between (mem_nhds_within_of_mem_nhds hs) hfs_r⟩

/-- If a function `f` with a densely ordered codomain is strictly monotone on a neighborhood of `a`
and the closure of the image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is
continuous at `a`. -/
lemma strict_mono_on.continuous_at_of_closure_image_mem_nhds [densely_ordered β] {f : α → β}
  {s : set α} {a : α} (h_mono : strict_mono_on f s) (hs : s ∈ 𝓝 a)
  (hfs : closure (f '' s) ∈ 𝓝 (f a)) :
  continuous_at f a :=
continuous_at_iff_continuous_left_right.2
  ⟨h_mono.continuous_at_left_of_closure_image_mem_nhds_within (mem_nhds_within_of_mem_nhds hs)
     (mem_nhds_within_of_mem_nhds hfs),
   h_mono.continuous_at_right_of_closure_image_mem_nhds_within (mem_nhds_within_of_mem_nhds hs)
     (mem_nhds_within_of_mem_nhds hfs)⟩

/-- If a function `f` with a densely ordered codomain is strictly monotone on a neighborhood of `a`
and the image of this set under `f` is a neighborhood of `f a`, then `f` is continuous at `a`. -/
lemma strict_mono_on.continuous_at_of_image_mem_nhds [densely_ordered β] {f : α → β}
  {s : set α} {a : α} (h_mono : strict_mono_on f s) (hs : s ∈ 𝓝 a) (hfs : f '' s ∈ 𝓝 (f a)) :
  continuous_at f a :=
h_mono.continuous_at_of_closure_image_mem_nhds hs (mem_of_superset hfs subset_closure)

/-- If `f` is a monotone function on a neighborhood of `a` and the image of this neighborhood under
`f` meets every interval `(b, f a)`, `b < f a`, and every interval `(f a, b)`, `b > f a`, then `f`
is continuous at `a`. -/
lemma continuous_at_of_monotone_on_of_exists_between {f : α → β} {s : set α} {a : α}
  (h_mono : monotone_on f s) (hs : s ∈ 𝓝 a)
  (hfs_l : ∀ b < f a, ∃ c ∈ s, f c ∈ Ioo b (f a)) (hfs_r : ∀ b > f a, ∃ c ∈ s, f c ∈ Ioo (f a) b) :
  continuous_at f a :=
continuous_at_iff_continuous_left_right.2
  ⟨continuous_at_left_of_monotone_on_of_exists_between h_mono
     (mem_nhds_within_of_mem_nhds hs) hfs_l,
   continuous_at_right_of_monotone_on_of_exists_between h_mono
     (mem_nhds_within_of_mem_nhds hs) hfs_r⟩

/-- If a function `f` with a densely ordered codomain is monotone on a neighborhood of `a` and the
closure of the image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is
continuous at `a`. -/
lemma continuous_at_of_monotone_on_of_closure_image_mem_nhds [densely_ordered β] {f : α → β}
  {s : set α} {a : α} (h_mono : monotone_on f s) (hs : s ∈ 𝓝 a)
  (hfs : closure (f '' s) ∈ 𝓝 (f a)) :
  continuous_at f a :=
continuous_at_iff_continuous_left_right.2
  ⟨continuous_at_left_of_monotone_on_of_closure_image_mem_nhds_within h_mono
     (mem_nhds_within_of_mem_nhds hs) (mem_nhds_within_of_mem_nhds hfs),
   continuous_at_right_of_monotone_on_of_closure_image_mem_nhds_within h_mono
     (mem_nhds_within_of_mem_nhds hs) (mem_nhds_within_of_mem_nhds hfs)⟩

/-- If a function `f` with a densely ordered codomain is monotone on a neighborhood of `a` and the
image of this neighborhood under `f` is a neighborhood of `f a`, then `f` is continuous at `a`. -/
lemma continuous_at_of_monotone_on_of_image_mem_nhds [densely_ordered β] {f : α → β}
  {s : set α} {a : α} (h_mono : monotone_on f s) (hs : s ∈ 𝓝 a)
  (hfs : f '' s ∈ 𝓝 (f a)) :
  continuous_at f a :=
continuous_at_of_monotone_on_of_closure_image_mem_nhds h_mono hs
  (mem_of_superset hfs subset_closure)

/-- A monotone function with densely ordered codomain and a dense range is continuous. -/
lemma monotone.continuous_of_dense_range [densely_ordered β] {f : α → β}
  (h_mono : monotone f) (h_dense : dense_range f) :
  continuous f :=
continuous_iff_continuous_at.mpr $ λ a,
  continuous_at_of_monotone_on_of_closure_image_mem_nhds (λ x hx y hy hxy, h_mono hxy)
    univ_mem $ by simp only [image_univ, h_dense.closure_eq, univ_mem]

/-- A monotone surjective function with a densely ordered codomain is continuous. -/
lemma monotone.continuous_of_surjective [densely_ordered β] {f : α → β} (h_mono : monotone f)
  (h_surj : function.surjective f) :
  continuous f :=
h_mono.continuous_of_dense_range h_surj.dense_range

end linear_order

/-!
### Continuity of order isomorphisms

In this section we prove that an `order_iso` is continuous, hence it is a `homeomorph`. We prove
this for an `order_iso` between to partial orders with order topology.
-/

namespace order_iso

variables {α β : Type*} [partial_order α] [partial_order β] [topological_space α]
  [topological_space β] [order_topology α] [order_topology β]

protected lemma continuous (e : α ≃o β) : continuous e :=
begin
  rw [‹order_topology β›.topology_eq_generate_intervals],
  refine continuous_generated_from (λ s hs, _),
  rcases hs with ⟨a, rfl|rfl⟩,
  { rw e.preimage_Ioi, apply is_open_lt' },
  { rw e.preimage_Iio, apply is_open_gt' }
end

/-- An order isomorphism between two linear order `order_topology` spaces is a homeomorphism. -/
def to_homeomorph (e : α ≃o β) : α ≃ₜ β :=
{ continuous_to_fun := e.continuous,
  continuous_inv_fun := e.symm.continuous,
  .. e }

@[simp] lemma coe_to_homeomorph (e : α ≃o β) : ⇑e.to_homeomorph = e := rfl
@[simp] lemma coe_to_homeomorph_symm (e : α ≃o β) : ⇑e.to_homeomorph.symm = e.symm := rfl

end order_iso
