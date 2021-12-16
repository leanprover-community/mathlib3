/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.weighted_graph.basic

/-!
# Orders on weighted graphs

There are two natural orders on `weighted_graph α W`:
* The label order, aka definition order. `G₁ ≤ G₂` if `G₂` is "more defined" or "more labelled" than
  than `G₁`: every edge of `G₁` corresponds to an edge of the same weight in `G₂`.
* The weight order. `G₁ ≤ G₂` if every edge of `G₁` corresponds to an edge of greater weight in
  `G₂`.
-/

variables {α W : Type*}

namespace weighted_graph
variables {G₁ G₂ : weighted_graph α W} {a b : α}

/-! ### Common constructions -/

section common
variables (α W)

/-- The bottom weighted graph is the one with no edge. -/
instance : has_bot (weighted_graph α W) :=
⟨{ weight := λ a b, none,
  weight_self := λ a, rfl,
  weight_comm := λ a b, rfl }⟩

variables {α W}

lemma weight_bot (a b : α) : (⊥ : weighted_graph α W).weight a b = none := rfl

lemma adj_bot : ¬ (⊥ : weighted_graph α W).adj a b := λ h, h rfl

end common

/-! ### Labelled graphs -/

namespace label
variables (α W)

/-- `G₁ ≤ G₂` means that the edges of `G₁` are edges of `G₂` and have the same label.

Turn this on using `open_locale label_graph`. -/
protected def has_le : has_le (weighted_graph α W) :=
⟨λ G₁ G₂, ∀ ⦃a b⦄, G₁.adj a b → G₁.weight a b = G₂.weight a b⟩

localized "attribute [instance] weighted_graph.label.has_le" in label_graph

variables {α W}

lemma le_def : G₁ ≤ G₂ ↔ ∀ ⦃a b⦄, G₁.adj a b → G₁.weight a b = G₂.weight a b := iff.rfl

lemma adj_mono (h : G₁ ≤ G₂) (hab : G₁.adj a b) : G₂.adj a b := λ h', hab $ (h hab).trans h'

variables (α W)

/-- The `partial_order` instance on labelled graphs.

Turn this on using `open_locale label_graph`. -/
protected def partial_order : partial_order (weighted_graph α W) :=
{ le_refl := λ G a b _, rfl,
  le_trans := λ G₁ G₂ G₃ h₁₂ h₂₃ a b h, (h₁₂ h).trans $ h₂₃ $ adj_mono h₁₂ h,
  le_antisymm := λ G₁ G₂ h₁ h₂, begin
    ext a b o,
    exact ⟨λ h, by rwa ←h₁ h.ne_none, λ h, by rwa ←h₂ h.ne_none⟩,
  end,
  .. weighted_graph.label.has_le α W }

localized "attribute [instance] weighted_graph.label.partial_order" in label_graph

/-- The `order_bot` instance on labelled graphs.

Turn this on using `open_locale label_graph`. -/
protected def order_bot : order_bot (weighted_graph α W) :=
{ bot_le := λ G a b h, (h rfl).elim, .. weighted_graph.has_bot α W }

localized "attribute [instance] weighted_graph.label.order_bot" in label_graph

variables [decidable_eq W]

/-- The infimum `G₁ ⊓ G₂`of two labelled graphs has the edges which have the same weight in `G₁` and
`G₂`.

Turn this on using `open_locale label_graph`. -/
protected def has_inf : has_inf (weighted_graph α W) :=
⟨λ G₁ G₂,
  { weight := λ a b, if G₁.weight a b = G₂.weight a b then G₁.weight a b else none,
    weight_self := λ a, by rw [G₁.weight_self, if_t_t],
    weight_comm := λ a b, by { simp_rw weight_comm _ a, congr } }⟩

localized "attribute [instance] weighted_graph.label.has_inf" in label_graph

variables {α W}

@[simp] lemma weight_inf (G₁ G₂ : weighted_graph α W) :
  (G₁ ⊓ G₂).weight a b = if G₁.weight a b = G₂.weight a b then G₁.weight a b else none := rfl

@[simp] lemma adj_inf (G₁ G₂ : weighted_graph α W) :
  (G₁ ⊓ G₂).adj a b ↔ G₁.weight a b = G₂.weight a b ∧ G₁.adj a b ∧ G₂.adj a b :=
ite_ne_right_iff.trans $ and_congr_right $ λ h, (and_iff_left_of_imp $ by { rw h, exact id }).symm

variables (α W)

/-- The `semilattice_inf` instance on labelled graphs.

Turn this on using `open_locale label_graph`. -/
protected def semilattice_inf : semilattice_inf (weighted_graph α W) :=
{ inf_le_left := λ G₁ G₂ a b h, if_pos (ite_ne_right_iff.1 h).1,
  inf_le_right := λ G₁ G₂ a b h, begin
    rw weight_inf,
    split_ifs with h',
    { exact h' },
    { exact (h (if_neg h')).elim }
  end,
  le_inf := λ G G₁ G₂ h₁ h₂ a b h, (h₁ h).trans (if_pos $ (h₁ h).symm.trans (h₂ h)).symm,
  .. weighted_graph.label.partial_order α W,
  .. weighted_graph.label.has_inf α W }

localized "attribute [instance] weighted_graph.label.semilattice_inf" in label_graph

/-- The difference `G₁ \ G₂`of two labelled graphs has the edges of `G₁` with the edges of `G₂`
removed.

Turn this on using `open_locale label_graph`. -/
protected def has_sdiff : has_sdiff (weighted_graph α W) :=
⟨λ G₁ G₂,
  { weight := λ a b, if G₂.adj a b then none else G₁.weight a b,
    weight_self := λ a, by rw [G₁.weight_self, if_t_t],
    weight_comm := λ a b, if_congr G₂.adj_comm rfl (G₁.weight_comm a b) }⟩

localized "attribute [instance] weighted_graph.label.has_sdiff" in label_graph

variables {α W}

@[simp] lemma weight_sdiff : (G₁ \ G₂).weight a b = ite (G₂.adj a b) none (G₁.weight a b) := rfl

@[simp] lemma adj_sdiff (G₁ G₂ : weighted_graph α W) :
  (G₁ \ G₂).adj a b ↔ G₁.adj a b ∧ ¬ G₂.adj a b :=
ite_ne_left_iff.trans $ (and_comm _ _).trans $ and_congr_left' ne_comm

lemma sdiff_le : G₁ \ G₂ ≤ G₁ := λ a b h, if_neg ((adj_sdiff _ _).1 h).2

lemma sdiff_disjoint : disjoint (G₁ \ G₂) G₂ :=
begin
  rintro a b h,
  rw [adj_inf, adj_sdiff] at h,
  exact (h.2.1.2 h.2.2).elim,
end

end label

section weight
variables (α W)

/-- `G₁ ≤ G₂` means that the edges of `G₁` are less than edges of `G₂`. -/
instance has_le [has_le W] : has_le (weighted_graph α W) :=
⟨λ G₁ G₂, ∀ a b, @has_le.le (with_bot W) _ (G₁.weight a b) (G₂.weight a b)⟩

variables {α W}

lemma le_def [has_le W] :
  G₁ ≤ G₂ ↔ ∀ a b, @has_le.le (with_bot W) _ (G₁.weight a b) (G₂.weight a b) :=
iff.rfl

lemma weight_mono [partial_order W] (h : G₁ ≤ G₂) :
  ∀ a b, @has_le.le (with_bot W) _ (G₁.weight a b) (G₂.weight a b) :=
le_def.1 h

lemma adj_mono [partial_order W] (h : G₁ ≤ G₂) (hab : G₁.adj a b) : G₂.adj a b :=
λ h', hab $ eq_bot_mono (h _ _) h'

variables (α W)

/-- The `preorder` instance on weighted graphs. -/
instance preorder [preorder W] : preorder (weighted_graph α W) :=
{ le_refl := λ G a b, le_rfl,
  le_trans := λ G₁ G₂ G₃ h₁₂ h₂₃ a b, (h₁₂ _ _).trans $ h₂₃ _ _,
  .. weighted_graph.has_le α W }

/-- The `partial_order` instance on weighted graphs. -/
instance partial_order [partial_order W] : partial_order (weighted_graph α W) :=
{ le_antisymm := λ G₁ G₂ h₁ h₂, by { ext a b o, rw (h₁ _ _).antisymm (h₂ _ _) },
  .. weighted_graph.preorder α W }

/-- The `order_bot` instance on weighted graphs. -/
instance order_bot [has_le W] : order_bot (weighted_graph α W) :=
{ bot_le := λ G a b, bot_le, .. weighted_graph.has_bot α W }

localized "attribute [instance] weighted_graph.label.order_bot" in label_graph

variables [decidable_eq W]

/-- The infimum `G₁ ⊓ G₂`of two weighted graphs has the edges which have the same weight in `G₁` and
`G₂`. -/
instance has_inf [has_inf W] : has_inf (weighted_graph α W) :=
⟨λ G₁ G₂,
  { weight := λ a b, if G₁.weight a b = G₂.weight a b then G₁.weight a b else none,
    weight_self := λ a, by rw [G₁.weight_self, if_t_t],
    weight_comm := λ a b, by { simp_rw weight_comm _ a, congr } }⟩

/-- The `semilattice_inf` instance on weighted graphs. -/
instance semilattice_inf : semilattice_inf (weighted_graph α W) :=
{ inf_le_left := λ G₁ G₂ a b h, if_pos (ite_ne_right_iff.1 h).1,
  inf_le_right := λ G₁ G₂ a b h, begin
    change ite _ _ _ = _,
    split_ifs with h',
    { exact h' },
    { exact (h (if_neg h')).elim }
  end,
  le_inf := λ G G₁ G₂ h₁ h₂ a b h, (h₁ h).trans (if_pos $ (h₁ h).symm.trans (h₂ h)).symm,
  .. weighted_graph.label.partial_order α W,
  .. weighted_graph.label.has_inf α W }

variables {α W}

@[simp] lemma weight_inf (G₁ G₂ : weighted_graph α W) :
  (G₁ ⊓ G₂).weight a b = if G₁.weight a b = G₂.weight a b then G₁.weight a b else none := rfl

@[simp] lemma adj_inf (G₁ G₂ : weighted_graph α W) :
  (G₁ ⊓ G₂).adj a b ↔ G₁.weight a b = G₂.weight a b ∧ G₁.adj a b ∧ G₂.adj a b :=
ite_ne_right_iff.trans $ and_congr_right $ λ h, (and_iff_left_of_imp $ by { rw h, exact id }).symm

variables (α W)

/-- The difference `G₁ \ G₂`of two labelled graphs has the edges of `G₁` with the edges of `G₂`
removed. -/
instance has_sdiff : has_sdiff (weighted_graph α W) :=
⟨λ G₁ G₂,
  { weight := λ a b, if G₂.adj a b then none else G₁.weight a b,
    weight_self := λ a, by rw [G₁.weight_self, if_t_t],
    weight_comm := λ a b, if_congr G₂.adj_comm rfl (G₁.weight_comm a b) }⟩

localized "attribute [instance] weighted_graph.label.has_sdiff" in label_graph

variables {α W}

@[simp] lemma weight_sdiff : (G₁ \ G₂).weight a b = ite (G₂.adj a b) none (G₁.weight a b) := rfl

@[simp] lemma adj_sdiff (G₁ G₂ : weighted_graph α W) :
  (G₁ \ G₂).adj a b ↔ G₁.adj a b ∧ ¬ G₂.adj a b :=
ite_ne_left_iff.trans $ (and_comm _ _).trans $ and_congr_left' ne_comm

lemma sdiff_le : G₁ \ G₂ ≤ G₁ := λ a b h, if_neg ((adj_sdiff _ _).1 h).2

lemma sdiff_disjoint : disjoint (G₁ \ G₂) G₂ :=
begin
  rintro a b h,
  rw [adj_inf, adj_sdiff] at h,
  exact (h.2.1.2 h.2.2).elim,
end

end weight

end weighted_graph
