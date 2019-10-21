/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro
-/
import algebra.big_operators
import data.finset
import tactic.subtype_instance

variables {α : Type*} [monoid α] {s : set α}
variables {β : Type*} [add_monoid β] {t : set β}

/-- `s` is an additive submonoid: a set containing 0 and closed under addition. -/
class is_add_submonoid (s : set β) : Prop :=
(zero_mem : (0:β) ∈ s)
(add_mem {a b} : a ∈ s → b ∈ s → a + b ∈ s)

/-- `s` is a submonoid: a set containing 1 and closed under multiplication. -/
@[to_additive is_add_submonoid]
class is_submonoid (s : set α) : Prop :=
(one_mem : (1:α) ∈ s)
(mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s)

instance additive.is_add_submonoid
  (s : set α) : ∀ [is_submonoid s], @is_add_submonoid (additive α) _ s
| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩

theorem additive.is_add_submonoid_iff
  {s : set α} : @is_add_submonoid (additive α) _ s ↔ is_submonoid s :=
⟨λ ⟨h₁, h₂⟩, ⟨h₁, @h₂⟩, λ h, by resetI; apply_instance⟩

instance multiplicative.is_submonoid
  (s : set β) : ∀ [is_add_submonoid s], @is_submonoid (multiplicative β) _ s
| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩

theorem multiplicative.is_submonoid_iff
  {s : set β} : @is_submonoid (multiplicative β) _ s ↔ is_add_submonoid s :=
⟨λ ⟨h₁, h₂⟩, ⟨h₁, @h₂⟩, λ h, by resetI; apply_instance⟩

@[to_additive]
instance is_submonoid.inter (s₁ s₂ : set α) [is_submonoid s₁] [is_submonoid s₂] :
  is_submonoid (s₁ ∩ s₂) :=
{ one_mem := ⟨is_submonoid.one_mem _, is_submonoid.one_mem _⟩,
  mul_mem := λ x y hx hy,
    ⟨is_submonoid.mul_mem hx.1 hy.1, is_submonoid.mul_mem hx.2 hy.2⟩ }

@[to_additive]
instance is_submonoid.Inter {ι : Sort*} (s : ι → set α) [h : ∀ y : ι, is_submonoid (s y)] :
  is_submonoid (set.Inter s) :=
{ one_mem := set.mem_Inter.2 $ λ y, is_submonoid.one_mem (s y),
  mul_mem := λ x₁ x₂ h₁ h₂, set.mem_Inter.2 $
    λ y, is_submonoid.mul_mem (set.mem_Inter.1 h₁ y) (set.mem_Inter.1 h₂ y) }

@[to_additive is_add_submonoid_Union_of_directed]
lemma is_submonoid_Union_of_directed {ι : Type*} [hι : nonempty ι]
  (s : ι → set α) [∀ i, is_submonoid (s i)]
  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
  is_submonoid (⋃i, s i) :=
{ one_mem := let ⟨i⟩ := hι in set.mem_Union.2 ⟨i, is_submonoid.one_mem _⟩,
  mul_mem := λ a b ha hb,
    let ⟨i, hi⟩ := set.mem_Union.1 ha in
    let ⟨j, hj⟩ := set.mem_Union.1 hb in
    let ⟨k, hk⟩ := directed i j in
    set.mem_Union.2 ⟨k, is_submonoid.mul_mem (hk.1 hi) (hk.2 hj)⟩ }

section powers

def powers (x : α) : set α := {y | ∃ n:ℕ, x^n = y}
def multiples (x : β) : set β := {y | ∃ n:ℕ, add_monoid.smul n x = y}
attribute [to_additive multiples] powers

lemma powers.one_mem {x : α} : (1 : α) ∈ powers x := ⟨0, pow_zero _⟩

lemma multiples.zero_mem {x : β} : (0 : β) ∈ multiples x := ⟨0, add_monoid.zero_smul _⟩
attribute [to_additive] powers.one_mem

lemma powers.self_mem {x : α} : x ∈ powers x := ⟨1, pow_one _⟩

lemma multiples.self_mem {x : β} : x ∈ multiples x := ⟨1, add_monoid.one_smul _⟩
attribute [to_additive] powers.self_mem

lemma powers.mul_mem {x y z: α} : (y ∈ powers x) → (z ∈ powers x) → (y * z ∈ powers x) :=
λ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩, ⟨n₁ + n₂, by simp only [pow_add, *]⟩

lemma multiples.add_mem {x y z: β} : (y ∈ multiples x) → (z ∈ multiples x) → (y + z ∈ multiples x) :=
@powers.mul_mem (multiplicative β) _ _ _ _
attribute [to_additive] powers.mul_mem

@[to_additive is_add_submonoid]
instance powers.is_submonoid (x : α) : is_submonoid (powers x) :=
{ one_mem := powers.one_mem,
  mul_mem := λ y z, powers.mul_mem }

@[to_additive is_add_submonoid]
instance univ.is_submonoid : is_submonoid (@set.univ α) := by split; simp

@[to_additive is_add_submonoid]
instance preimage.is_submonoid {γ : Type*} [monoid γ] (f : α → γ) [is_monoid_hom f]
  (s : set γ) [is_submonoid s] : is_submonoid (f ⁻¹' s) :=
{ one_mem := show f 1 ∈ s, by rw is_monoid_hom.map_one f; exact is_submonoid.one_mem s,
  mul_mem := λ a b (ha : f a ∈ s) (hb : f b ∈ s),
    show f (a * b) ∈ s, by rw is_monoid_hom.map_mul f; exact is_submonoid.mul_mem ha hb }

@[instance, to_additive is_add_submonoid]
lemma image.is_submonoid {γ : Type*} [monoid γ] (f : α → γ) [is_monoid_hom f]
  (s : set α) [is_submonoid s] : is_submonoid (f '' s) :=
{ one_mem := ⟨1, is_submonoid.one_mem s, is_monoid_hom.map_one f⟩,
  mul_mem := λ a b ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, is_submonoid.mul_mem hx.1 hy.1,
    by rw [is_monoid_hom.map_mul f, hx.2, hy.2]⟩ }

@[to_additive is_add_submonoid]
instance range.is_submonoid {γ : Type*} [monoid γ] (f : α → γ) [is_monoid_hom f] :
  is_submonoid (set.range f) :=
by rw ← set.image_univ; apply_instance

lemma is_submonoid.pow_mem {a : α} [is_submonoid s] (h : a ∈ s) : ∀ {n : ℕ}, a ^ n ∈ s
| 0 := is_submonoid.one_mem s
| (n + 1) := is_submonoid.mul_mem h is_submonoid.pow_mem

lemma is_add_submonoid.smul_mem {a : β} [is_add_submonoid t] :
  ∀ (h : a ∈ t) {n : ℕ}, add_monoid.smul n a ∈ t :=
@is_submonoid.pow_mem (multiplicative β) _ _ _ _
attribute [to_additive smul_mem] is_submonoid.pow_mem

lemma is_submonoid.power_subset {a : α} [is_submonoid s] (h : a ∈ s) : powers a ⊆ s :=
assume x ⟨n, hx⟩, hx ▸ is_submonoid.pow_mem h

lemma is_add_submonoid.multiple_subset {a : β} [is_add_submonoid t] :
  a ∈ t → multiples a ⊆ t :=
@is_submonoid.power_subset (multiplicative β) _ _ _ _
attribute [to_additive multiple_subset] is_submonoid.power_subset

end powers

namespace is_submonoid

@[to_additive]
lemma list_prod_mem [is_submonoid s] : ∀{l : list α}, (∀x∈l, x ∈ s) → l.prod ∈ s
| []     h := one_mem s
| (a::l) h :=
  suffices a * l.prod ∈ s, by simpa,
  have a ∈ s ∧ (∀x∈l, x ∈ s), by simpa using h,
  is_submonoid.mul_mem this.1 (list_prod_mem this.2)

@[to_additive]
lemma multiset_prod_mem {α} [comm_monoid α] (s : set α) [is_submonoid s] (m : multiset α) :
  (∀a∈m, a ∈ s) → m.prod ∈ s :=
begin
  refine quotient.induction_on m (assume l hl, _),
  rw [multiset.quot_mk_to_coe, multiset.coe_prod],
  exact list_prod_mem hl
end

@[to_additive]
lemma finset_prod_mem {α β} [comm_monoid α] (s : set α) [is_submonoid s] (f : β → α) :
  ∀(t : finset β), (∀b∈t, f b ∈ s) → t.prod f ∈ s
| ⟨m, hm⟩ hs :=
  begin
    refine multiset_prod_mem s _ _,
    simp,
    rintros a b hb rfl,
    exact hs _ hb
  end

end is_submonoid

@[to_additive add_monoid]
instance subtype.monoid {s : set α} [is_submonoid s] : monoid s :=
by subtype_instance

@[to_additive add_comm_monoid]
instance subtype.comm_monoid {α} [comm_monoid α] {s : set α} [is_submonoid s] : comm_monoid s :=
by subtype_instance

@[simp, to_additive]
lemma is_submonoid.coe_one [is_submonoid s] : ((1 : s) : α) = 1 := rfl

@[simp, to_additive]
lemma is_submonoid.coe_mul [is_submonoid s] (a b : s) : ((a * b : s) : α) = a * b := rfl

@[simp] lemma is_submonoid.coe_pow [is_submonoid s] (a : s) (n : ℕ) : ((a ^ n : s) : α) = a ^ n :=
by induction n; simp [*, pow_succ]

@[simp] lemma is_add_submonoid.smul_coe {β : Type*} [add_monoid β] {s : set β}
  [is_add_submonoid s] (a : s) (n : ℕ) : ((add_monoid.smul n a : s) : β) = add_monoid.smul n a :=
by induction n; [refl, simp [*, succ_smul]]
attribute [to_additive smul_coe] is_submonoid.coe_pow

@[to_additive is_add_monoid_hom]
instance subtype_val.is_monoid_hom [is_submonoid s] : is_monoid_hom (subtype.val : s → α) :=
{ map_one := rfl, map_mul := λ _ _, rfl }

@[to_additive is_add_monoid_hom]
instance coe.is_monoid_hom [is_submonoid s] : is_monoid_hom (coe : s → α) :=
subtype_val.is_monoid_hom

@[to_additive is_add_monoid_hom]
instance subtype_mk.is_monoid_hom {γ : Type*} [monoid γ] [is_submonoid s] (f : γ → α)
  [is_monoid_hom f] (h : ∀ x, f x ∈ s) : is_monoid_hom (λ x, (⟨f x, h x⟩ : s)) :=
{ map_one := subtype.eq (is_monoid_hom.map_one f),
  map_mul := λ x y, subtype.eq (is_monoid_hom.map_mul f x y) }

@[to_additive is_add_monoid_hom]
instance set_inclusion.is_monoid_hom (t : set α) [is_submonoid s] [is_submonoid t] (h : s ⊆ t) :
  is_monoid_hom (set.inclusion h) :=
subtype_mk.is_monoid_hom _ _

namespace add_monoid

inductive in_closure (s : set β) : β → Prop
| basic {a : β} : a ∈ s → in_closure a
| zero : in_closure 0
| add {a b : β} : in_closure a → in_closure b → in_closure (a + b)

end add_monoid

namespace monoid

inductive in_closure (s : set α) : α → Prop
| basic {a : α} : a ∈ s → in_closure a
| one : in_closure 1
| mul {a b : α} : in_closure a → in_closure b → in_closure (a * b)

attribute [to_additive] monoid.in_closure
attribute [to_additive] monoid.in_closure.one
attribute [to_additive] monoid.in_closure.mul

@[to_additive]
def closure (s : set α) : set α := {a | in_closure s a }

@[to_additive is_add_submonoid]
instance closure.is_submonoid (s : set α) : is_submonoid (closure s) :=
{ one_mem := in_closure.one s, mul_mem := assume a b, in_closure.mul }

@[to_additive]
theorem subset_closure {s : set α} : s ⊆ closure s :=
assume a, in_closure.basic

@[to_additive]
theorem closure_subset {s t : set α} [is_submonoid t] (h : s ⊆ t) : closure s ⊆ t :=
assume a ha, by induction ha; simp [h _, *, is_submonoid.one_mem, is_submonoid.mul_mem]

@[to_additive]
theorem closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans h subset_closure

@[to_additive]
theorem closure_singleton {x : α} : closure ({x} : set α) = powers x :=
set.eq_of_subset_of_subset (closure_subset $ set.singleton_subset_iff.2 $ powers.self_mem) $
  is_submonoid.power_subset $ set.singleton_subset_iff.1 $ subset_closure

@[to_additive]
lemma image_closure {β : Type*} [monoid β] (f : α → β) [is_monoid_hom f] (s : set α) :
  f '' closure s = closure (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { solve_by_elim [subset_closure, set.mem_image_of_mem] },
    { rw [is_monoid_hom.map_one f], apply is_submonoid.one_mem },
    { rw [is_monoid_hom.map_mul f], solve_by_elim [is_submonoid.mul_mem] }
  end
  (closure_subset $ set.image_subset _ subset_closure)

@[to_additive]
theorem exists_list_of_mem_closure {s : set α} {a : α} (h : a ∈ closure s) :
  (∃l:list α, (∀x∈l, x ∈ s) ∧ l.prod = a) :=
begin
  induction h,
  case in_closure.basic : a ha { existsi ([a]), simp [ha] },
  case in_closure.one { existsi ([]), simp },
  case in_closure.mul : a b _ _ ha hb {
    rcases ha with ⟨la, ha, eqa⟩,
    rcases hb with ⟨lb, hb, eqb⟩,
    existsi (la ++ lb),
    simp [eqa.symm, eqb.symm, or_imp_distrib],
    exact assume a, ⟨ha a, hb a⟩
  }
end

@[to_additive]
theorem mem_closure_union_iff {α : Type*} [comm_monoid α] {s t : set α} {x : α} :
  x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y * z = x :=
⟨λ hx, let ⟨L, HL1, HL2⟩ := exists_list_of_mem_closure hx in HL2 ▸
  list.rec_on L (λ _, ⟨1, is_submonoid.one_mem _, 1, is_submonoid.one_mem _, mul_one _⟩)
    (λ hd tl ih HL1, let ⟨y, hy, z, hz, hyzx⟩ := ih (list.forall_mem_of_forall_mem_cons HL1) in
      or.cases_on (HL1 hd $ list.mem_cons_self _ _)
        (λ hs, ⟨hd * y, is_submonoid.mul_mem (subset_closure hs) hy, z, hz, by rw [mul_assoc, list.prod_cons, ← hyzx]; refl⟩)
        (λ ht, ⟨y, hy, z * hd, is_submonoid.mul_mem hz (subset_closure ht), by rw [← mul_assoc, list.prod_cons, ← hyzx, mul_comm hd]; refl⟩)) HL1,
λ ⟨y, hy, z, hz, hyzx⟩, hyzx ▸ is_submonoid.mul_mem (closure_mono (set.subset_union_left _ _) hy)
  (closure_mono (set.subset_union_right _ _) hz)⟩

end monoid

