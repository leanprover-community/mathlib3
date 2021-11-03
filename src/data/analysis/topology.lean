/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Computational realization of topological spaces (experimental).
-/
import topology.bases
import data.analysis.filter
open set
open filter (hiding realizer)
open_locale topological_space

/-- A `ctop α σ` is a realization of a topology (basis) on `α`,
  represented by a type `σ` together with operations for the top element and
  the intersection operation. -/
structure ctop (α σ : Type*) :=
(f : σ → set α)
(top : α → σ)
(top_mem : ∀ x : α, x ∈ f (top x))
(inter : Π a b (x : α), x ∈ f a ∩ f b → σ)
(inter_mem : ∀ a b x h, x ∈ f (inter a b x h))
(inter_sub : ∀ a b x h, f (inter a b x h) ⊆ f a ∩ f b)

variables {α : Type*} {β : Type*} {σ : Type*} {τ : Type*}

namespace ctop
section
variables (F : ctop α σ)

instance : has_coe_to_fun (ctop α σ) (λ _, σ → set α) := ⟨ctop.f⟩

@[simp] theorem coe_mk (f T h₁ I h₂ h₃ a) : (@ctop.mk α σ f T h₁ I h₂ h₃) a = f a := rfl

/-- Map a ctop to an equivalent representation type. -/
def of_equiv (E : σ ≃ τ) : ctop α σ → ctop α τ
| ⟨f, T, h₁, I, h₂, h₃⟩ :=
  { f         := λ a, f (E.symm a),
    top       := λ x, E (T x),
    top_mem   := λ x, by simpa using h₁ x,
    inter     := λ a b x h, E (I (E.symm a) (E.symm b) x h),
    inter_mem := λ a b x h, by simpa using h₂ (E.symm a) (E.symm b) x h,
    inter_sub := λ a b x h, by simpa using h₃ (E.symm a) (E.symm b) x h }

@[simp] theorem of_equiv_val (E : σ ≃ τ) (F : ctop α σ) (a : τ) :
  F.of_equiv E a = F (E.symm a) := by cases F; refl

end

/-- Every `ctop` is a topological space. -/
def to_topsp (F : ctop α σ) : topological_space α :=
topological_space.generate_from (set.range F.f)

theorem to_topsp_is_topological_basis (F : ctop α σ) :
  @topological_space.is_topological_basis _ F.to_topsp (set.range F.f) :=
by letI := F.to_topsp; exact
⟨λ u ⟨a, e₁⟩ v ⟨b, e₂⟩, e₁ ▸ e₂ ▸
   λ x h, ⟨_, ⟨_, rfl⟩, F.inter_mem a b x h, F.inter_sub a b x h⟩,
eq_univ_iff_forall.2 $ λ x, ⟨_, ⟨_, rfl⟩, F.top_mem x⟩, rfl⟩

@[simp] theorem mem_nhds_to_topsp (F : ctop α σ) {s : set α} {a : α} :
  s ∈ @nhds _ F.to_topsp a ↔ ∃ b, a ∈ F b ∧ F b ⊆ s :=
(@topological_space.is_topological_basis.mem_nhds_iff
  _ F.to_topsp _ _ _ F.to_topsp_is_topological_basis).trans $
⟨λ ⟨_, ⟨x, rfl⟩, h⟩, ⟨x, h⟩, λ ⟨x, h⟩, ⟨_, ⟨x, rfl⟩, h⟩⟩

end ctop

/-- A `ctop` realizer for the topological space `T` is a `ctop`
  which generates `T`. -/
structure ctop.realizer (α) [T : topological_space α] :=
(σ : Type*)
(F : ctop α σ)
(eq : F.to_topsp = T)
open ctop

protected def ctop.to_realizer (F : ctop α σ) : @ctop.realizer _ F.to_topsp :=
@ctop.realizer.mk _ F.to_topsp σ F rfl

namespace ctop.realizer

protected theorem is_basis [T : topological_space α] (F : realizer α) :
  topological_space.is_topological_basis (set.range F.F.f) :=
by have := to_topsp_is_topological_basis F.F; rwa F.eq at this

protected theorem mem_nhds [T : topological_space α] (F : realizer α) {s : set α} {a : α} :
  s ∈ 𝓝 a ↔ ∃ b, a ∈ F.F b ∧ F.F b ⊆ s :=
by have := mem_nhds_to_topsp F.F; rwa F.eq at this

theorem is_open_iff [topological_space α] (F : realizer α) {s : set α} :
  is_open s ↔ ∀ a ∈ s, ∃ b, a ∈ F.F b ∧ F.F b ⊆ s :=
is_open_iff_mem_nhds.trans $ ball_congr $ λ a h, F.mem_nhds

theorem is_closed_iff [topological_space α] (F : realizer α) {s : set α} :
  is_closed s ↔ ∀ a, (∀ b, a ∈ F.F b → ∃ z, z ∈ F.F b ∩ s) → a ∈ s :=
is_open_compl_iff.symm.trans $ F.is_open_iff.trans $ forall_congr $ λ a,
show (a ∉ s → (∃ (b : F.σ), a ∈ F.F b ∧ ∀ z ∈ F.F b, z ∉ s)) ↔ _,
by haveI := classical.prop_decidable; rw [not_imp_comm];
   simp [not_exists, not_and, not_forall, and_comm]

theorem mem_interior_iff [topological_space α] (F : realizer α) {s : set α} {a : α} :
  a ∈ interior s ↔ ∃ b, a ∈ F.F b ∧ F.F b ⊆ s :=
mem_interior_iff_mem_nhds.trans F.mem_nhds

protected theorem is_open [topological_space α] (F : realizer α) (s : F.σ) : is_open (F.F s) :=
is_open_iff_nhds.2 $ λ a m, by simpa using F.mem_nhds.2 ⟨s, m, subset.refl _⟩

theorem ext' [T : topological_space α] {σ : Type*} {F : ctop α σ}
  (H : ∀ a s, s ∈ 𝓝 a ↔ ∃ b, a ∈ F b ∧ F b ⊆ s) :
  F.to_topsp = T :=
begin
  refine eq_of_nhds_eq_nhds (λ x, _),
  ext s,
  rw [mem_nhds_to_topsp, H]
end

theorem ext [T : topological_space α] {σ : Type*} {F : ctop α σ}
  (H₁ : ∀ a, is_open (F a))
  (H₂ : ∀ a s, s ∈ 𝓝 a → ∃ b, a ∈ F b ∧ F b ⊆ s) :
  F.to_topsp = T :=
ext' $ λ a s, ⟨H₂ a s, λ ⟨b, h₁, h₂⟩, mem_nhds_iff.2 ⟨_, h₂, H₁ _, h₁⟩⟩

variable [topological_space α]

protected def id : realizer α := ⟨{x:set α // is_open x},
{ f            := subtype.val,
  top          := λ _, ⟨univ, is_open_univ⟩,
  top_mem      := mem_univ,
  inter        := λ ⟨x, h₁⟩ ⟨y, h₂⟩ a h₃, ⟨_, h₁.inter h₂⟩,
  inter_mem    := λ ⟨x, h₁⟩ ⟨y, h₂⟩ a, id,
  inter_sub    := λ ⟨x, h₁⟩ ⟨y, h₂⟩ a h₃, subset.refl _ },
ext subtype.property $ λ x s h,
  let ⟨t, h, o, m⟩ := mem_nhds_iff.1 h in ⟨⟨t, o⟩, m, h⟩⟩

def of_equiv (F : realizer α) (E : F.σ ≃ τ) : realizer α :=
⟨τ, F.F.of_equiv E, ext' (λ a s, F.mem_nhds.trans $
 ⟨λ ⟨s, h⟩, ⟨E s, by simpa using h⟩, λ ⟨t, h⟩, ⟨E.symm t, by simpa using h⟩⟩)⟩

@[simp] theorem of_equiv_σ (F : realizer α) (E : F.σ ≃ τ) : (F.of_equiv E).σ = τ := rfl
@[simp] theorem of_equiv_F (F : realizer α) (E : F.σ ≃ τ) (s : τ) :
  (F.of_equiv E).F s = F.F (E.symm s) := by delta of_equiv; simp

protected def nhds (F : realizer α) (a : α) : (𝓝 a).realizer :=
⟨{s : F.σ // a ∈ F.F s},
{ f            := λ s, F.F s.1,
  pt           := ⟨_, F.F.top_mem a⟩,
  inf          := λ ⟨x, h₁⟩ ⟨y, h₂⟩, ⟨_, F.F.inter_mem x y a ⟨h₁, h₂⟩⟩,
  inf_le_left  := λ ⟨x, h₁⟩ ⟨y, h₂⟩ z h, (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).1,
  inf_le_right := λ ⟨x, h₁⟩ ⟨y, h₂⟩ z h, (F.F.inter_sub x y a ⟨h₁, h₂⟩ h).2 },
filter_eq $ set.ext $ λ x,
⟨λ ⟨⟨s, as⟩, h⟩, mem_nhds_iff.2 ⟨_, h, F.is_open _, as⟩,
 λ h, let ⟨s, h, as⟩ := F.mem_nhds.1 h in ⟨⟨s, h⟩, as⟩⟩⟩

@[simp] theorem nhds_σ (m : α → β) (F : realizer α) (a : α) :
  (F.nhds a).σ = {s : F.σ // a ∈ F.F s} := rfl
@[simp] theorem nhds_F (m : α → β) (F : realizer α) (a : α) (s) :
  (F.nhds a).F s = F.F s.1 := rfl

theorem tendsto_nhds_iff {m : β → α} {f : filter β} (F : f.realizer) (R : realizer α) {a : α} :
  tendsto m f (𝓝 a) ↔ ∀ t, a ∈ R.F t → ∃ s, ∀ x ∈ F.F s, m x ∈ R.F t :=
(F.tendsto_iff _ (R.nhds a)).trans subtype.forall

end ctop.realizer

structure locally_finite.realizer [topological_space α] (F : realizer α) (f : β → set α) :=
(bas : ∀ a, {s // a ∈ F.F s})
(sets : ∀ x:α, fintype {i | (f i ∩ F.F (bas x)).nonempty})

theorem locally_finite.realizer.to_locally_finite [topological_space α]
  {F : realizer α} {f : β → set α} (R : locally_finite.realizer F f) :
  locally_finite f :=
λ a, ⟨_, F.mem_nhds.2
  ⟨(R.bas a).1, (R.bas a).2, subset.refl _⟩, ⟨R.sets a⟩⟩

theorem locally_finite_iff_exists_realizer [topological_space α]
  (F : realizer α) {f : β → set α} : locally_finite f ↔ nonempty (locally_finite.realizer F f) :=
⟨λ h, let ⟨g, h₁⟩ := classical.axiom_of_choice h,
    ⟨g₂, h₂⟩ := classical.axiom_of_choice (λ x,
       show ∃ (b : F.σ), x ∈ (F.F) b ∧ (F.F) b ⊆ g x, from
       let ⟨h, h'⟩ := h₁ x in F.mem_nhds.1 h) in
  ⟨⟨λ x, ⟨g₂ x, (h₂ x).1⟩, λ x, finite.fintype $
    let ⟨h, h'⟩ := h₁ x in h'.subset $ λ i hi,
    hi.mono (inter_subset_inter_right _ (h₂ x).2)⟩⟩,
 λ ⟨R⟩, R.to_locally_finite⟩

def compact.realizer [topological_space α] (R : realizer α) (s : set α) :=
∀ {f : filter α} (F : f.realizer) (x : F.σ), f ≠ ⊥ →
  F.F x ⊆ s → {a // a∈s ∧ 𝓝 a ⊓ f ≠ ⊥}
