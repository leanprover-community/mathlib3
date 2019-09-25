/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard, Amelia Livingston
-/
import algebra.big_operators
import data.finset
import tactic.subtype_instance

/-!

# Submonoids

First unbundled (is_submonoid) (deprecated) and then bundled.

-- mention ≤ instead of ⊆ for inclusions

no coercion from submonoid to subset, the idea is that the API does it all for us.
there is ∈ though
-/

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
lemma is_submonoid.inter (s₁ s₂ : set α) [is_submonoid s₁] [is_submonoid s₂] :
  is_submonoid (s₁ ∩ s₂) :=
{ one_mem := ⟨is_submonoid.one_mem _, is_submonoid.one_mem _⟩,
  mul_mem := λ x y hx hy,
    ⟨is_submonoid.mul_mem hx.1 hy.1, is_submonoid.mul_mem hx.2 hy.2⟩ }

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

-- bundled submonoids and add_submonoids

/-- A submonoid of a monoid α is a subset containing 1 and closed under multiplication. -/
structure submonoid (α : Type*) [monoid α] :=
(carrier : set α)
(one_mem' : (1 : α) ∈ carrier)
(mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier)

/-- An  additive submonoid of an additive monoid α is a subset containing 0 and
  closed under addition. -/
structure add_submonoid (α : Type*) [add_monoid α] :=
(carrier : set α)
(zero_mem' : (0 : α) ∈ carrier)
(add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier)

attribute [to_additive add_submonoid] submonoid

/-- Map from submonoids of monoid α to add_submonoids of additive α. -/
def submonoid.to_add_submonoid {α : Type*} [monoid α] (S : submonoid α) :
  add_submonoid (additive α) :=
{ carrier := S.carrier,
  zero_mem' := S.one_mem',
  add_mem' := S.mul_mem' }

/-- Map from add_submonoids of additive α to submonoids of α. -/
def submonoid.of_add_submonoid {α : Type*} [monoid α] (S : add_submonoid (additive α)) :
  submonoid α :=
{ carrier := S.carrier,
  one_mem' := S.zero_mem',
  mul_mem' := S.add_mem' }

/-- Map from add_submonoids of add_monoid α to submonoids of multiplicative α. -/
def add_submonoid.to_submonoid {α : Type*} [add_monoid α] (S : add_submonoid α) :
  submonoid (multiplicative α) :=
{ carrier := S.carrier,
  one_mem' := S.zero_mem',
  mul_mem' := S.add_mem' }

/-- Map from submonoids of multiplicative α to add_submonoids of add_monoid α. -/
def add_submonoid.of_submonoid {α : Type*} [add_monoid α] (S : submonoid (multiplicative α)) :
  add_submonoid α :=
{ carrier := S.carrier,
  zero_mem' := S.one_mem',
  add_mem' := S.mul_mem' }

/-- submonoids of monoid α are isomorphic to additive submonoids of additive α. -/
def submonoid.add_submonoid_equiv (α : Type*) [monoid α] :
submonoid α ≃ add_submonoid (additive α) :=
{ to_fun := submonoid.to_add_submonoid,
  inv_fun := submonoid.of_add_submonoid,
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl }

namespace submonoid

variables {M : Type*} [monoid M] (S : submonoid M)

@[to_additive]
instance : has_coe (submonoid M) (set M) := ⟨submonoid.carrier⟩

@[to_additive]
instance : has_mem M (submonoid M) := ⟨λ m S, m ∈ S.carrier⟩

@[to_additive]
instance : has_le (submonoid M) := ⟨λ S T, S.carrier ⊆ T.carrier⟩

@[simp, to_additive]
lemma mem_coe {m : M} : m ∈ (S : set M) ↔ m ∈ S := iff.rfl

/-- Two submonoids are equal if the underlying subsets are equal. -/
@[to_additive "Two add_submonoids are equal if the underlying subsets are equal."]
theorem ext' {S T : submonoid M} (h : (S : set M) = T) : S = T :=
by cases S; cases T; congr'

/-- Two submonoids are equal if and only if the underlying subsets are equal. -/
@[to_additive "Two add_submonoids are equal if and only if the underling subsets are equal."]
protected theorem ext'_iff {S T : submonoid M}  : (S : set M) = T ↔ S = T :=
⟨ext', λ h, h ▸ rfl⟩

/-- Two submonoids are equal if they have the same elements. -/
@[extensionality, to_additive "Two add_submonoids are equal if they have the same elements."]
theorem ext {S T : submonoid M}
  (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := ext' $ set.ext h

attribute [extensionality] add_submonoid.ext --I can't find whether there's a newer way to do this

/-- A submonoid contains the monoid's 1. -/
@[to_additive "An add_submonoid contains the monoid's 0."]
theorem one_mem : (1 : M) ∈ S := S.one_mem'

/-- A submonoid is closed under multiplication. -/
@[to_additive "An add_submonoid is closed under addition."]
theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S := submonoid.mul_mem' S

/-- A finite product of elements of a submonoid of a commutative monoid is in the submonoid. -/
@[to_additive "A finite sum of elements of an add_submonoid of an add_comm_monoid is in the add_submonoid."]
lemma prod_mem {M : Type*} [comm_monoid M] (S : submonoid M)
  {ι : Type*} [decidable_eq ι] {t : finset ι} {f : ι → M} :
  (∀c ∈ t, f c ∈ S) → t.prod f ∈ S :=
finset.induction_on t (by simp [S.one_mem]) (by simp [S.mul_mem] {contextual := tt})

/-- A directed union of submonoids is a submonoid. -/
@[to_additive "A directed union of add_submonoids is an add_submonoid."]
def Union_of_directed {ι : Type*} [hι : nonempty ι]
  (s : ι → submonoid M)
  (directed : ∀ i j, ∃ k, s i ≤ s k ∧ s j ≤ s k) :
  submonoid M :=
{ carrier := (⋃i, s i),
  one_mem' := let ⟨i⟩ := hι in set.mem_Union.2 ⟨i, submonoid.one_mem _⟩,
  mul_mem' := λ a b ha hb,
    let ⟨i, hi⟩ := set.mem_Union.1 ha in
    let ⟨j, hj⟩ := set.mem_Union.1 hb in
    let ⟨k, hk⟩ := directed i j in
    set.mem_Union.2 ⟨k, (s k).mul_mem (hk.1 hi) (hk.2 hj)⟩ }

/-- A submonoid of a monoid inherits a multiplication. -/
@[to_additive "An add_submonoid of an add_monoid inherits an addition."]
instance has_mul : has_mul S := ⟨λ a b, ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩

/-- A submonoid of a monoid inherits a 1. -/
@[to_additive "An add_submonoid of an add_monoid inherits a zero."]
instance has_one : has_one S := ⟨⟨_, S.one_mem⟩⟩

@[simp, to_additive] lemma coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y := rfl
@[simp, to_additive] lemma coe_one : ((1 : S) : M) = 1 := rfl

/-- A submonoid of a monoid inherits a monoid structure. -/
@[to_additive to_add_monoid "An add_submonoid of an add_monoid inherits an add_monoid structure."]
-- should I have to name the additive version here?
instance to_monoid {M : Type*} [monoid M] {S : submonoid M} : monoid S :=
by refine { mul := (*), one := 1, ..}; by simp [mul_assoc]

/-- A submonoid of a comm_monoid is a comm_monoid. -/
@[to_additive to_add_comm_monoid "An add_submonoid of an add_comm_monoid is an add_comm_monoid."]
instance to_comm_monoid {M} [comm_monoid M] (S : submonoid M) : comm_monoid S :=
{ mul_comm := λ _ _, subtype.ext.2 $ mul_comm _ _, ..submonoid.to_monoid}

/-- The natural monoid hom from a submonoid of monoid M to M. -/
@[to_additive "The natural monoid hom from an add_submonoid of add_monoid M to M."]
def subtype : S →* M :=
{ to_fun := coe,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

@[simp, to_additive] theorem subtype_apply (x : S) : S.subtype x = x := rfl

@[to_additive] lemma subtype_eq_val : (S.subtype : S → M) = subtype.val := rfl

-- to_additive cannot handle powers v multiples very well because the inputs of
-- x ^ n and n • x are in different orders. So we have to do a manual intervention here.

/-- The powers 1, x, x^2, ... of an element x of a monoid M are a submonoid. -/
def powers (x : M) : submonoid M :=
{ carrier := {y | ∃ n:ℕ, x^n = y},
  one_mem' := ⟨0, pow_zero x⟩,
  mul_mem' := by rintros x₁ x₂ ⟨n₁, rfl⟩ ⟨n₂, rfl⟩; exact ⟨n₁ + n₂, pow_add _ _ _ ⟩ }

/-- x is in the submonoid generated by x. -/
lemma powers.self_mem {x : M} : x ∈ powers x := ⟨1, pow_one _⟩

/-- If a is in a submonoid, so are all its natural number powers. -/
lemma pow_mem {a : M} (h : a ∈ S) : ∀ {n : ℕ}, a ^ n ∈ S
| 0 := S.one_mem
| (n + 1) := S.mul_mem h pow_mem

-- @[to_additive] -- seems to fail even if I put this after the below add_submonoid stuff.
lemma powers_subset {a : M} (h : a ∈ S) : powers a ≤ S :=
assume x ⟨n, hx⟩, hx ▸ S.pow_mem h

@[simp] lemma coe_pow (a : S) (n : ℕ) : ((a ^ n : S) : M) = a ^ n :=
by induction n; simp [*, pow_succ]

end submonoid

-- Now the additive versions.

namespace add_submonoid

variables {M : Type*} [add_monoid M]  (S : add_submonoid M)

/-- The multiples 0, x, 2x, ... of an element x of an add_monoid M are an add_submonoid. -/
def multiples (x : M) : add_submonoid M :=
{ carrier := {y | ∃ n:ℕ, add_monoid.smul n x = y},
  zero_mem' := ⟨0, add_monoid.zero_smul x⟩,
  add_mem' := by rintros x₁ x₂ ⟨n₁, rfl⟩ ⟨n₂, rfl⟩; exact ⟨n₁ + n₂, add_monoid.add_smul _ _ _ ⟩ }

-- attribute [to_additive add_submonoid.multiples] submonoid.powers -- works, but doesn't seem to be
-- of any use here.

/-- x is in the add_submonoid generated by x. -/
lemma add_submonoid.multiples.self_mem {x : M} : x ∈ multiples x := ⟨1, add_monoid.one_smul x⟩

--attribute [to_additive add_submonoid.multiples.self_mem] submonoid.powers.self_mem -- fails

lemma smul_mem {a : M} (h : a ∈ S) {n : ℕ} : add_monoid.smul n a ∈ S :=
submonoid.pow_mem (add_submonoid.to_submonoid S) h -- or should I just be modding the proof?

attribute [to_additive is_add_submonoid.smul_mem] is_submonoid.pow_mem -- this works, but
-- I'm not sure if it's of any use.

lemma multiples_subset {a : M} (h : a ∈ S) : multiples a ≤ S :=
submonoid.powers_subset (add_submonoid.to_submonoid S) h

attribute [to_additive add_submonoid.multiples_subset] submonoid.powers_subset -- ditto

@[simp] lemma coe_smul (a : S) (n : ℕ) : ((add_monoid.smul n a : S) : M) = add_monoid.smul n a :=
submonoid.coe_pow (add_submonoid.to_submonoid S) a n
--by induction n; simp [*, succ_smul] -- works just as well

end add_submonoid

namespace submonoid

variables {M : Type*} [monoid M] (S : submonoid M)

/-- `univ` is the submonoid M of the monoid M. -/
@[to_additive "`univ` is the add_submonoid M of the add_monoid M."]
def univ : submonoid M :=
{ carrier := set.univ,
  one_mem' := set.mem_univ 1,
  mul_mem' := λ _ _ _ _, set.mem_univ _ }

/-- ⊥ is the trivial submonoid {1} of the monoid M. -/
@[to_additive "⊥ is the zero submonoid of the add_monoid M."]
def bot : submonoid M :=
{ carrier := {1},
  one_mem' := set.mem_singleton 1,
  mul_mem' := λ a b ha hb, by simp * at *}

/-- Submonoids of a monoid are partially ordered (by inclusion). -/
@[to_additive "Add_submonoids of an add_monoid are partially ordered (by inclusion)."]
instance : partial_order (submonoid M) :=
partial_order.lift (coe : submonoid M → set M) (λ a b, ext') (by apply_instance)

@[to_additive]
lemma le_def (p p' : submonoid M) : p ≤ p' ↔ ∀ x ∈ p, x ∈ p' := iff.rfl

open lattice

@[to_additive]
instance : has_bot (submonoid M) := ⟨submonoid.bot⟩

@[simp, to_additive] lemma mem_bot {x : M} : x ∈ (⊥ : submonoid M) ↔ x = 1 := set.mem_singleton_iff

@[to_additive]
instance : order_bot (submonoid M) :=
{ bot := ⊥,
  bot_le := λ P x hx, by simp * at *; exact P.one_mem,
  ..submonoid.partial_order
  }

@[to_additive]
instance : has_top (submonoid M) := ⟨univ⟩

@[simp, to_additive] lemma mem_top (x : M) : x ∈ (⊤ : submonoid M) := set.mem_univ x

@[to_additive]
instance : order_top (submonoid M) :=
{ top := ⊤,
  le_top := λ p x _, mem_top x,
  ..submonoid.partial_order}

/-- The inf of two submonoids is their intersection. -/
@[to_additive "The inf of two add_submonoids is their intersection."]
def inf (S₁ S₂ : submonoid M) :
  submonoid M :=
{ carrier := S₁ ∩ S₂,
  one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩,
  mul_mem' := λ _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩,
    ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }

@[to_additive]
instance : has_inf (submonoid M) := ⟨inf⟩

@[to_additive]
lemma mem_inf {p p' : submonoid M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
⟨λ h, ⟨h.1, h.2⟩, λ h, (p ⊓ p').mem_coe.2 ⟨h.1, h.2⟩⟩

@[to_additive]
instance : has_Inf (submonoid M) :=
⟨λ s, {
  carrier := ⋂ t ∈ s, ↑t,
  one_mem' := set.mem_bInter $ λ i h, i.one_mem,
  mul_mem' := λ x y hx hy, set.mem_bInter $ λ i h,
    i.mul_mem (by apply set.mem_bInter_iff.1 hx i h) (by apply set.mem_bInter_iff.1 hy i h) }⟩

@[to_additive]
lemma Inf_le' {S : set (submonoid M)} {p} : p ∈ S → Inf S ≤ p :=
set.bInter_subset_of_mem

@[to_additive]
lemma le_Inf' {S : set (submonoid M)} {p} : (∀p' ∈ S, p ≤ p') → p ≤ Inf S :=
set.subset_bInter

@[to_additive]
lemma mem_Inf {S : set (submonoid M)} {x : M} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p := set.mem_bInter_iff

/-- Submonoids of a monoid form a lattice. -/
@[to_additive "Add_submonoids of an add_monoid form a lattice."]
instance lattice.lattice : lattice (submonoid M) :=
{ sup          := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left  := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, ha,
  le_sup_right := λ a b, le_Inf' $ λ x ⟨ha, hb⟩, hb,
  sup_le       := λ a b c h₁ h₂, Inf_le' ⟨h₁, h₂⟩,
  inf          := (⊓),
  le_inf       := λ a b c ha hb, set.subset_inter ha hb,
  inf_le_left  := λ a b, set.inter_subset_left _ _,
  inf_le_right := λ a b, set.inter_subset_right _ _, ..submonoid.partial_order}

/-- Submonoids of a monoid form a complete lattice. -/
@[to_additive "Add_submonoids of an add_monoid form a complete lattice."]
instance : complete_lattice (submonoid M) :=
{ Sup          := λ tt, Inf {t | ∀t'∈tt, t' ≤ t},
  le_Sup       := λ s p hs, le_Inf' $ λ p' hp', hp' _ hs,
  Sup_le       := λ s p hs, Inf_le' hs,
  Inf          := Inf,
  le_Inf       := λ s a, le_Inf',
  Inf_le       := λ s a, Inf_le',
  ..submonoid.lattice.order_top,
  ..submonoid.lattice.order_bot,
  ..submonoid.lattice.lattice}

-- Need the additive version of this not to be called 'add_submonoid.add_comm_monoid' but I can't think of a good alternative...
/-- Submonoids of a monoid form an add_comm_monoid. -/
@[to_additive "Add_submonoids of an add_monoid form an add_comm_monoid."]
instance complete_lattice.add_comm_monoid :
  add_comm_monoid (submonoid M) :=
{ add := (⊔),
  add_assoc := λ _ _ _, sup_assoc,
  zero := ⊥,
  zero_add := λ _, bot_sup_eq,
  add_zero := λ _, sup_bot_eq,
  add_comm := λ _ _, sup_comm }

end submonoid

namespace monoid_hom

variables {M : Type*} [monoid M] (S : submonoid M)

open submonoid

/-- The preimage of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive "The preimage of an add_submonoid along an add_monoid homomorphism is an add_submonoid."]
def comap {N : Type*} [monoid N] (f : M →* N)
  (S : submonoid N) : submonoid M :=
{ carrier := (f ⁻¹' S),
  one_mem' := show f 1 ∈ S, by rw f.map_one; exact S.one_mem,
  mul_mem' := λ a b ha hb,
    show f (a * b) ∈ S, by rw f.map_mul; exact S.mul_mem ha hb }

/-- The image of a submonoid along a monoid homomorphism is a submonoid. -/
@[to_additive "The image of an add_submonoid along an add_monoid homomorphism is an add_submonoid."]
def map {N : Type*} [monoid N] (f : M →* N) (S : submonoid M) : submonoid N :=
{ carrier := (f '' S),
  one_mem' := ⟨1, S.one_mem, f.map_one⟩,
  mul_mem' := begin rintros _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩, exact ⟨x * y, S.mul_mem hx hy,
    by rw f.map_mul; refl⟩ end }

/-- The range of a monoid homomorphism is a submonoid. -/
@[to_additive "The range of an add_monoid_hom is an add_submonoid."]
def range {N : Type*} [monoid N] (f : M →* N) :
  submonoid N := map f univ

end monoid_hom

namespace submonoid

variables {M : Type*} [monoid M] (S : submonoid M)

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an add_submonoid is in the add_submonoid."]
lemma list_prod_mem : ∀ {l : list M}, (∀x∈l, x ∈ S) → l.prod ∈ S
| []     h := S.one_mem
| (a::l) h :=
  suffices a * l.prod ∈ S, by simpa,
  have a ∈ S ∧ (∀ x ∈ l, x ∈ S), by simpa using h,
  S.mul_mem this.1 (list_prod_mem this.2)

/-- Product of a multiset of elements in a submonoid of a comm_monoid is in the submonoid. -/
@[to_additive "Sum of a multiset of elements in an add_submonoid of an add_comm_monoid is in the add_submonoid."]
lemma multiset_prod_mem {M} [comm_monoid M] (S : submonoid M) (m : multiset M) :
  (∀a ∈ m, a ∈ S) → m.prod ∈ S :=
begin
  refine quotient.induction_on m (assume l hl, _),
  rw [multiset.quot_mk_to_coe, multiset.coe_prod],
  exact S.list_prod_mem hl
end

/-- Product of a finset of elements in a submonoid of a comm_monoid is in the submonoid. -/
@[to_additive "Sum of a finset of elements in an add_submonoid of an add_comm_monoid is in the add_submonoid."]
lemma finset_prod_mem {M ι} [comm_monoid M] (S : submonoid M) (f : ι → M) :
  ∀(t : finset ι), (∀b∈t, f b ∈ S) → t.prod f ∈ S
| ⟨m, hm⟩ hs :=
  begin
    refine S.multiset_prod_mem _ _,
    suffices : ∀ (a : M) (x : ι), x ∈ m → f x = a → a ∈ S,
      simpa using this,
    rintros a b hb rfl,
    exact hs _ hb
  end

end submonoid

namespace monoid_hom

variables {M : Type*} [monoid M] (S : submonoid M)

/-- Restriction of a monoid_hom to a submonoid of the codomain. -/
@[to_additive "Restriction of an add_monoid_hom to an add_submonoid of the codomain."]
-- 'would be nice if it errored if [the additive docstring] doesn't exist'
def subtype_mk {N : Type*} [monoid N] (f : N →* M) (h : ∀ x, f x ∈ S) : N →* S :=
{ to_fun := λ n, ⟨f n, h n⟩,
  map_one' := subtype.eq (is_monoid_hom.map_one f),
  map_mul' := λ x y, subtype.eq (is_monoid_hom.map_mul f x y) }


/-- Restriction of a monoid_hom to its range. -/
@[to_additive "Restriction of an add_monoid_hom to its range."]
def range_mk {N} [monoid N] (f : M →* N) : M →* f.range :=
subtype_mk f.range f $ λ x, ⟨x, submonoid.mem_top x, rfl⟩

/-- The range of a surjective monoid_hom is the top submonoid. -/
@[to_additive "The range of a surjective add_monoid_hom is the top add_submonoid."]
lemma range_top_of_surjective {N} [monoid N] (f : M →* N) (hf : function.surjective f) :
  f.range = (⊤ : submonoid N) :=
submonoid.ext'_iff.1 $ (set.ext_iff _ _).2 $ λ x,
⟨λ h, submonoid.mem_top x, λ h, exists.elim (hf x) $ λ w hw, ⟨w, submonoid.mem_top w, hw⟩⟩

/-- The monoid_hom associated to an inclusion of submonoids. -/
@[to_additive "The add_monoid_hom associated to an inclusion of submonoids."]
def set_inclusion (T : submonoid M) (h : S ≤ T) : S →* T :=
subtype_mk _ S.subtype (λ x, h x.2)

end monoid_hom

namespace monoid

variables {M : Type*} [monoid M] (S : submonoid M)

open submonoid

def closure' (s : set M) : submonoid M :=
{ carrier := in_closure s,
  one_mem' := in_closure.one s,
  mul_mem' := λ _ _, in_closure.mul}

theorem le_closure' {s : set M} : s ≤ closure' s :=
λ a, in_closure.basic

theorem closure'_le {s : set M} {T : submonoid M} (h : s ≤ T) : closure' s ≤ T :=
λ a ha, begin induction ha with _ hb _ _ _ _ ha hb,
  {exact h hb },
  {exact T.one_mem },
  {exact T.mul_mem ha hb }
end

theorem closure'_mono {s t : set M} (h : s ≤ t) : closure' s ≤ closure' t :=
closure'_le $ set.subset.trans h le_closure'

theorem closure'_singleton {x : M} : closure' ({x} : set M) = powers x :=
ext' $ set.eq_of_subset_of_subset (closure'_le $ set.singleton_subset_iff.2 powers.self_mem) $
submonoid.powers_subset _ $ in_closure.basic $ set.mem_singleton x

lemma image_closure' {N : Type*} [monoid N] (f : M →* N) (s : set M) :
  f.map (closure' s) = closure' (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { solve_by_elim [le_closure', set.mem_image_of_mem] },
    { rw f.map_one, apply submonoid.one_mem },
    { rw f.map_mul, solve_by_elim [submonoid.mul_mem] }
  end
  (closure'_le $ set.image_subset _ le_closure')

theorem exists_list_of_mem_closure' {s : set M} {a : M} (h : a ∈ closure' s) :
  (∃l:list M, (∀x∈l, x ∈ s) ∧ l.prod = a) :=
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

theorem mem_closure'_union_iff {M : Type*} [comm_monoid M] {s t : set M} {x : M} :
  x ∈ closure' (s ∪ t) ↔ ∃ y ∈ closure' s, ∃ z ∈ closure' t, y * z = x :=
⟨λ hx, let ⟨L, HL1, HL2⟩ := exists_list_of_mem_closure' hx in HL2 ▸
  list.rec_on L (λ _, ⟨1, submonoid.one_mem _, 1, submonoid.one_mem _, mul_one _⟩)
    (λ hd tl ih HL1, let ⟨y, hy, z, hz, hyzx⟩ := ih (list.forall_mem_of_forall_mem_cons HL1) in
      or.cases_on (HL1 hd $ list.mem_cons_self _ _)
        (λ hs, ⟨hd * y, submonoid.mul_mem _ (le_closure' hs) hy, z, hz,
          by rw [mul_assoc, list.prod_cons, ← hyzx]; refl⟩)
        (λ ht, ⟨y, hy, z * hd, submonoid.mul_mem _ hz (le_closure' ht),
          by rw [← mul_assoc, list.prod_cons, ← hyzx, mul_comm hd]; refl⟩)) HL1,
λ ⟨y, hy, z, hz, hyzx⟩, hyzx ▸ submonoid.mul_mem _
  ((closure_mono (set.subset_union_left s t)) hy)
  ((closure_mono (set.subset_union_right s t)) hz)⟩

end monoid

/-

-- some stuff from is_submonoid which might need to be put into this language:

namespace add_monoid

--def closure (s : set β) : set β := @monoid.closure (multiplicative β) _ s
--attribute [to_additive add_monoid.closure] monoid.closure

instance closure.is_add_submonoid (s : set β) : is_add_submonoid (closure s) :=
multiplicative.is_submonoid_iff.1 $ monoid.closure.is_submonoid s
attribute [to_additive add_monoid.closure.is_add_submonoid] monoid.closure.is_submonoid

theorem subset_closure {s : set β} : s ⊆ closure s :=
monoid.subset_closure
attribute [to_additive add_monoid.subset_closure] monoid.subset_closure

theorem closure_subset {s t : set β} [is_add_submonoid t] : s ⊆ t → closure s ⊆ t :=
monoid.closure_subset
attribute [to_additive add_monoid.closure_subset] monoid.closure_subset

theorem closure_mono {s t : set β} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans h subset_closure
attribute [to_additive add_monoid.closure_mono] monoid.closure_mono

theorem closure_singleton {x : β} : closure ({x} : set β) = multiples x :=
monoid.closure_singleton
attribute [to_additive add_monoid.closure_singleton] monoid.closure_singleton

theorem exists_list_of_mem_closure {s : set β} {a : β} :
  a ∈ closure s → ∃l:list β, (∀x∈l, x ∈ s) ∧ l.sum = a :=
monoid.exists_list_of_mem_closure
attribute [to_additive add_monoid.exists_list_of_mem_closure] monoid.exists_list_of_mem_closure

@[elab_as_eliminator]
theorem in_closure.rec_on {s : set β} {C : β → Prop}
  {a : β} (H : a ∈ closure s)
  (H1 : ∀ {a : β}, a ∈ s → C a) (H2 : C 0)
  (H3 : ∀ {a b : β}, a ∈ closure s → b ∈ closure s → C a → C b → C (a + b)) :
  C a :=
monoid.in_closure.rec_on H (λ _, H1) H2 (λ _ _, H3)

lemma image_closure {γ : Type*} [add_monoid γ] (f : β → γ) [is_add_monoid_hom f] (s : set β) :
  f '' closure s = closure (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { solve_by_elim [subset_closure, set.mem_image_of_mem] },
    { rw [is_add_monoid_hom.map_zero f], apply is_add_submonoid.zero_mem },
    { rw [is_add_monoid_hom.map_add f], solve_by_elim [is_add_submonoid.add_mem] }
  end
  (closure_subset $ set.image_subset _ subset_closure)
attribute [to_additive add_monoid.image_closure] monoid.image_closure

theorem mem_closure_union_iff {β : Type*} [add_comm_monoid β] {s t : set β} {x : β} :
  x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y + z = x :=
monoid.mem_closure_union_iff

end add_monoid
-/
