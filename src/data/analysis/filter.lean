/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Computational realization of filters (experimental).
-/
import order.filter.cofinite
open set filter

/-- A `cfilter α σ` is a realization of a filter (base) on `α`,
  represented by a type `σ` together with operations for the top element and
  the binary inf operation. -/
structure cfilter (α σ : Type*) [partial_order α] :=
(f : σ → α)
(pt : σ)
(inf : σ → σ → σ)
(inf_le_left : ∀ a b : σ, f (inf a b) ≤ f a)
(inf_le_right : ∀ a b : σ, f (inf a b) ≤ f b)

variables {α : Type*} {β : Type*} {σ : Type*} {τ : Type*}

namespace cfilter
section
variables [partial_order α] (F : cfilter α σ)

instance : has_coe_to_fun (cfilter α σ) := ⟨_, cfilter.f⟩

@[simp] theorem coe_mk (f pt inf h₁ h₂ a) : (@cfilter.mk α σ _ f pt inf h₁ h₂) a = f a := rfl

/-- Map a cfilter to an equivalent representation type. -/
def of_equiv (E : σ ≃ τ) : cfilter α σ → cfilter α τ
| ⟨f, p, g, h₁, h₂⟩ :=
  { f            := λ a, f (E.symm a),
    pt           := E p,
    inf          := λ a b, E (g (E.symm a) (E.symm b)),
    inf_le_left  := λ a b, by simpa using h₁ (E.symm a) (E.symm b),
    inf_le_right := λ a b, by simpa using h₂ (E.symm a) (E.symm b) }

@[simp] theorem of_equiv_val (E : σ ≃ τ) (F : cfilter α σ) (a : τ) :
  F.of_equiv E a = F (E.symm a) := by cases F; refl

end

/-- The filter represented by a `cfilter` is the collection of supersets of
  elements of the filter base. -/
def to_filter (F : cfilter (set α) σ) : filter α :=
{ sets             := {a | ∃ b, F b ⊆ a},
  univ_sets        := ⟨F.pt, subset_univ _⟩,
  sets_of_superset := λ x y ⟨b, h⟩ s, ⟨b, subset.trans h s⟩,
  inter_sets       := λ x y ⟨a, h₁⟩ ⟨b, h₂⟩, ⟨F.inf a b,
    subset_inter (subset.trans (F.inf_le_left _ _) h₁) (subset.trans (F.inf_le_right _ _) h₂)⟩ }

@[simp] theorem mem_to_filter_sets (F : cfilter (set α) σ) {a : set α} :
  a ∈ F.to_filter ↔ ∃ b, F b ⊆ a := iff.rfl

end cfilter

/-- A realizer for filter `f` is a cfilter which generates `f`. -/
structure filter.realizer (f : filter α) :=
(σ : Type*)
(F : cfilter (set α) σ)
(eq : F.to_filter = f)

protected def cfilter.to_realizer (F : cfilter (set α) σ) : F.to_filter.realizer := ⟨σ, F, rfl⟩

namespace filter.realizer

theorem mem_sets {f : filter α} (F : f.realizer) {a : set α} : a ∈ f ↔ ∃ b, F.F b ⊆ a :=
by cases F; subst f; simp

-- Used because it has better definitional equalities than the eq.rec proof
def of_eq {f g : filter α} (e : f = g) (F : f.realizer) : g.realizer :=
⟨F.σ, F.F, F.eq.trans e⟩

/-- A filter realizes itself. -/
def of_filter (f : filter α) : f.realizer := ⟨f.sets,
{ f            := subtype.val,
  pt           := ⟨univ, univ_mem⟩,
  inf          := λ ⟨x, h₁⟩ ⟨y, h₂⟩, ⟨_, inter_mem h₁ h₂⟩,
  inf_le_left  := λ ⟨x, h₁⟩ ⟨y, h₂⟩, inter_subset_left x y,
  inf_le_right := λ ⟨x, h₁⟩ ⟨y, h₂⟩, inter_subset_right x y },
filter_eq $ set.ext $ λ x, set_coe.exists.trans exists_mem_subset_iff⟩

/-- Transfer a filter realizer to another realizer on a different base type. -/
def of_equiv {f : filter α} (F : f.realizer) (E : F.σ ≃ τ) : f.realizer :=
⟨τ, F.F.of_equiv E, by refine eq.trans _ F.eq; exact filter_eq (set.ext $ λ x,
⟨λ ⟨s, h⟩, ⟨E.symm s, by simpa using h⟩, λ ⟨t, h⟩, ⟨E t, by simp [h]⟩⟩)⟩

@[simp] theorem of_equiv_σ {f : filter α} (F : f.realizer) (E : F.σ ≃ τ) :
  (F.of_equiv E).σ = τ := rfl
@[simp] theorem of_equiv_F {f : filter α} (F : f.realizer) (E : F.σ ≃ τ) (s : τ) :
  (F.of_equiv E).F s = F.F (E.symm s) := by delta of_equiv; simp

/-- `unit` is a realizer for the principal filter -/
protected def principal (s : set α) : (principal s).realizer := ⟨unit,
{ f            := λ _, s,
  pt           := (),
  inf          := λ _ _, (),
  inf_le_left  := λ _ _, le_refl _,
  inf_le_right := λ _ _, le_refl _ },
filter_eq $ set.ext $ λ x,
⟨λ ⟨_, s⟩, s, λ h, ⟨(), h⟩⟩⟩

@[simp] theorem principal_σ (s : set α) : (realizer.principal s).σ = unit := rfl
@[simp] theorem principal_F (s : set α) (u : unit) : (realizer.principal s).F u = s := rfl

/-- `unit` is a realizer for the top filter -/
protected def top : (⊤ : filter α).realizer :=
(realizer.principal _).of_eq principal_univ

@[simp] theorem top_σ : (@realizer.top α).σ = unit := rfl
@[simp] theorem top_F (u : unit) : (@realizer.top α).F u = univ := rfl

/-- `unit` is a realizer for the bottom filter -/
protected def bot : (⊥ : filter α).realizer :=
(realizer.principal _).of_eq principal_empty

@[simp] theorem bot_σ : (@realizer.bot α).σ = unit := rfl
@[simp] theorem bot_F (u : unit) : (@realizer.bot α).F u = ∅ := rfl

/-- Construct a realizer for `map m f` given a realizer for `f` -/
protected def map (m : α → β) {f : filter α} (F : f.realizer) : (map m f).realizer := ⟨F.σ,
{ f            := λ s, image m (F.F s),
  pt           := F.F.pt,
  inf          := F.F.inf,
  inf_le_left  := λ a b, image_subset _ (F.F.inf_le_left _ _),
  inf_le_right := λ a b, image_subset _ (F.F.inf_le_right _ _) },
filter_eq $ set.ext $ λ x, by simp [cfilter.to_filter]; rw F.mem_sets; refl ⟩

@[simp] theorem map_σ (m : α → β) {f : filter α} (F : f.realizer) : (F.map m).σ = F.σ := rfl
@[simp] theorem map_F (m : α → β) {f : filter α} (F : f.realizer) (s) :
  (F.map m).F s = image m (F.F s) := rfl

/-- Construct a realizer for `comap m f` given a realizer for `f` -/
protected def comap (m : α → β) {f : filter β} (F : f.realizer) : (comap m f).realizer := ⟨F.σ,
{ f            := λ s, preimage m (F.F s),
  pt           := F.F.pt,
  inf          := F.F.inf,
  inf_le_left  := λ a b, preimage_mono (F.F.inf_le_left _ _),
  inf_le_right := λ a b, preimage_mono (F.F.inf_le_right _ _) },
filter_eq $ set.ext $ λ x, by cases F; subst f; simp [cfilter.to_filter, mem_comap]; exact
⟨λ ⟨s, h⟩, ⟨_, ⟨s, subset.refl _⟩, h⟩,
 λ ⟨y, ⟨s, h⟩, h₂⟩, ⟨s, subset.trans (preimage_mono h) h₂⟩⟩⟩

/-- Construct a realizer for the sup of two filters -/
protected def sup {f g : filter α} (F : f.realizer) (G : g.realizer) :
  (f ⊔ g).realizer := ⟨F.σ × G.σ,
{ f            := λ ⟨s, t⟩, F.F s ∪ G.F t,
  pt           := (F.F.pt, G.F.pt),
  inf          := λ ⟨a, a'⟩ ⟨b, b'⟩, (F.F.inf a b, G.F.inf a' b'),
  inf_le_left  := λ ⟨a, a'⟩ ⟨b, b'⟩, union_subset_union (F.F.inf_le_left _ _) (G.F.inf_le_left _ _),
  inf_le_right := λ ⟨a, a'⟩ ⟨b, b'⟩, union_subset_union (F.F.inf_le_right _ _)
                    (G.F.inf_le_right _ _) },
filter_eq $ set.ext $ λ x, by cases F; cases G; substs f g; simp [cfilter.to_filter]; exact
⟨λ ⟨s, t, h⟩, ⟨⟨s, subset.trans (subset_union_left _ _) h⟩,
               ⟨t, subset.trans (subset_union_right _ _) h⟩⟩,
 λ ⟨⟨s, h₁⟩, ⟨t, h₂⟩⟩, ⟨s, t, union_subset h₁ h₂⟩⟩⟩

/-- Construct a realizer for the inf of two filters -/
protected def inf {f g : filter α} (F : f.realizer) (G : g.realizer) :
  (f ⊓ g).realizer := ⟨F.σ × G.σ,
{ f            := λ ⟨s, t⟩, F.F s ∩ G.F t,
  pt           := (F.F.pt, G.F.pt),
  inf          := λ ⟨a, a'⟩ ⟨b, b'⟩, (F.F.inf a b, G.F.inf a' b'),
  inf_le_left  := λ ⟨a, a'⟩ ⟨b, b'⟩, inter_subset_inter (F.F.inf_le_left _ _) (G.F.inf_le_left _ _),
  inf_le_right := λ ⟨a, a'⟩ ⟨b, b'⟩, inter_subset_inter (F.F.inf_le_right _ _)
                    (G.F.inf_le_right _ _) },
 begin
   ext x,
   cases F; cases G; substs f g; simp [cfilter.to_filter],
   split,
   { rintro ⟨s : F_σ, t : G_σ, h⟩,
     apply mem_inf_of_inter _ _ h,
     use s,
     use t, },
   { rintros ⟨s, ⟨a, ha⟩, t, ⟨b, hb⟩, rfl⟩,
     exact ⟨a, b, inter_subset_inter ha hb⟩ }
 end⟩

/-- Construct a realizer for the cofinite filter -/
protected def cofinite [decidable_eq α] : (@cofinite α).realizer := ⟨finset α,
{ f            := λ s, {a | a ∉ s},
  pt           := ∅,
  inf          := (∪),
  inf_le_left  := λ s t a, mt (finset.mem_union_left _),
  inf_le_right := λ s t a, mt (finset.mem_union_right _) },
filter_eq $ set.ext $ λ x,
⟨λ ⟨s, h⟩, s.finite_to_set.subset (compl_subset_comm.1 h),
 λ ⟨fs⟩, by exactI ⟨xᶜ.to_finset, λ a (h : a ∉ xᶜ.to_finset),
  classical.by_contradiction $ λ h', h (mem_to_finset.2 h')⟩⟩⟩

/-- Construct a realizer for filter bind -/
protected def bind {f : filter α} {m : α → filter β} (F : f.realizer) (G : ∀ i, (m i).realizer) :
  (f.bind m).realizer :=
⟨Σ s : F.σ, Π i ∈ F.F s, (G i).σ,
{ f            := λ ⟨s, f⟩, ⋃ i ∈ F.F s, (G i).F (f i H),
  pt           := ⟨F.F.pt, λ i H, (G i).F.pt⟩,
  inf          := λ ⟨a, f⟩ ⟨b, f'⟩, ⟨F.F.inf a b, λ i h,
    (G i).F.inf (f i (F.F.inf_le_left _ _ h)) (f' i (F.F.inf_le_right _ _ h))⟩,
  inf_le_left  := λ ⟨a, f⟩ ⟨b, f'⟩ x,
    show (x ∈ ⋃ (i : α) (H : i ∈ F.F (F.F.inf a b)), _) →
          x ∈ ⋃ i (H : i ∈ F.F a), ((G i).F) (f i H), by simp; exact
    λ i h₁ h₂, ⟨i, F.F.inf_le_left _ _ h₁, (G i).F.inf_le_left _ _ h₂⟩,
  inf_le_right := λ ⟨a, f⟩ ⟨b, f'⟩ x,
    show (x ∈ ⋃ (i : α) (H : i ∈ F.F (F.F.inf a b)), _) →
          x ∈ ⋃ i (H : i ∈ F.F b), ((G i).F) (f' i H), by simp; exact
    λ i h₁ h₂, ⟨i, F.F.inf_le_right _ _ h₁, (G i).F.inf_le_right _ _ h₂⟩ },
filter_eq $ set.ext $ λ x,
by cases F with _ F _; subst f; simp [cfilter.to_filter, mem_bind]; exact
⟨λ ⟨s, f, h⟩, ⟨F s, ⟨s, subset.refl _⟩, λ i H, (G i).mem_sets.2
   ⟨f i H, λ a h', h ⟨_, ⟨i, rfl⟩, _, ⟨H, rfl⟩, h'⟩⟩⟩,
 λ ⟨y, ⟨s, h⟩, f⟩,
  let ⟨f', h'⟩ := classical.axiom_of_choice (λ i:F s, (G i).mem_sets.1 (f i (h i.2))) in
  ⟨s, λ i h, f' ⟨i, h⟩, λ a ⟨_, ⟨i, rfl⟩, _, ⟨H, rfl⟩, m⟩, h' ⟨_, H⟩ m⟩⟩⟩

/-- Construct a realizer for indexed supremum -/
protected def Sup {f : α → filter β} (F : ∀ i, (f i).realizer) : (⨆ i, f i).realizer :=
let F' : (⨆ i, f i).realizer :=
  ((realizer.bind realizer.top F).of_eq $
    filter_eq $ set.ext $ by simp [filter.bind, eq_univ_iff_forall, supr_sets_eq]) in
F'.of_equiv $ show (Σ u:unit, Π (i : α), true → (F i).σ) ≃ Π i, (F i).σ, from
⟨λ⟨_,f⟩ i, f i ⟨⟩, λ f, ⟨(), λ i _, f i⟩,
 λ ⟨⟨⟩, f⟩, by dsimp; congr; simp, λ f, rfl⟩

/-- Construct a realizer for the product of filters -/
protected def prod {f g : filter α} (F : f.realizer) (G : g.realizer) : (f.prod g).realizer :=
(F.comap _).inf (G.comap _)

theorem le_iff {f g : filter α} (F : f.realizer) (G : g.realizer) :
  f ≤ g ↔ ∀ b : G.σ, ∃ a : F.σ, F.F a ≤ G.F b :=
⟨λ H t, F.mem_sets.1 (H (G.mem_sets.2 ⟨t, subset.refl _⟩)),
 λ H x h, F.mem_sets.2 $
   let ⟨s, h₁⟩ := G.mem_sets.1 h, ⟨t, h₂⟩ := H s in ⟨t, subset.trans h₂ h₁⟩⟩

theorem tendsto_iff (f : α → β) {l₁ : filter α} {l₂ : filter β} (L₁ : l₁.realizer)
  (L₂ : l₂.realizer) :
  tendsto f l₁ l₂ ↔ ∀ b, ∃ a, ∀ x ∈ L₁.F a, f x ∈ L₂.F b :=
(le_iff (L₁.map f) L₂).trans $ forall_congr $ λ b, exists_congr $ λ a, image_subset_iff

theorem ne_bot_iff {f : filter α} (F : f.realizer) :
  f ≠ ⊥ ↔ ∀ a : F.σ, (F.F a).nonempty :=
begin
  classical,
  rw [not_iff_comm, ← le_bot_iff, F.le_iff realizer.bot, not_forall],
  simp only [set.not_nonempty_iff_eq_empty],
  exact ⟨λ ⟨x, e⟩ _, ⟨x, le_of_eq e⟩,
    λ h, let ⟨x, h⟩ := h () in ⟨x, le_bot_iff.1 h⟩⟩
end

end filter.realizer
