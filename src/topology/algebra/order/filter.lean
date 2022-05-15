import topology.algebra.order.basic
import topology.filter

/-!
-/

open_locale topological_space

namespace filter

variables {α X : Type*} [topological_space X] [partial_order X] [order_topology X]

lemma tendsto.nhds_at_top [no_max_order X] {f : α → X} {l : filter α} (h : tendsto f l at_top) :
  tendsto (𝓝 ∘ f) l (𝓝 at_top) :=
filter.tendsto_nhds_at_top.mpr $
  λ x, (h.eventually (eventually_gt_at_top x)).mono (λ y, le_mem_nhds)

lemma tendsto.nhds_at_bot [no_min_order X] {f : α → X} {l : filter α} (h : tendsto f l at_bot) :
  tendsto (𝓝 ∘ f) l (𝓝 at_bot) :=
@tendsto.nhds_at_top α Xᵒᵈ _ _ _ _ _ _ h

end filter
