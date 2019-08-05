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

-- mention ≤ instead of ⊆ for inclusions

-/
--variables {α : Type*} [monoid α] {s : set α}
--variables {β : Type*} [add_monoid β] {t : set β}

/-- A submonoid of a monoid α is a subset containing 1 and closed under multiplication. -/
structure submonoid (α : Type*) [monoid α] :=
(carrier : set α)
(one_mem' : (1:α) ∈ carrier)
(mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier)

--/-- Coercion from a submonoid to the underlying subset -- TODO do I need this?-/
--instance (α : Type*) [monoid α] : has_coe_to_sort (submonoid α) := { S := _,
--  coe := submonoid.carrier }


-- TODO -- add_submonoid structure, to_additive stuff

-- TODO -- additive to multiplicative stuff

--instance additive.is_add_submonoid
--  (s : set α) : ∀ [is_submonoid s], @is_add_submonoid (additive α) _ s
--| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩

--theorem additive.is_add_submonoid_iff
--  {s : set α} : @is_add_submonoid (additive α) _ s ↔ is_submonoid s :=
--⟨λ ⟨h₁, h₂⟩, ⟨h₁, @h₂⟩, λ h, by resetI; apply_instance⟩

--instance multiplicative.is_submonoid
--  (s : set β) : ∀ [is_add_submonoid s], @is_submonoid (multiplicative β) _ s
--| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩

--theorem multiplicative.is_submonoid_iff
--  {s : set β} : @is_submonoid (multiplicative β) _ s ↔ is_add_submonoid s :=
--⟨λ ⟨h₁, h₂⟩, ⟨h₁, @h₂⟩, λ h, by resetI; apply_instance⟩

variables {M : Type*} [monoid M] (S : submonoid M)

namespace submonoid

instance : has_coe (submonoid M) (set M) := ⟨submonoid.carrier⟩

-- not sure if this is a good idea
--instance : has_coe_to_sort (submonoid M) := ⟨_, λ S, subtype (S.carrier)⟩

instance : has_mem M (submonoid M) := ⟨λ m S, m ∈ S.carrier⟩

instance : has_le (submonoid M) := ⟨λ S T, S.carrier ⊆ T.carrier⟩

@[simp] theorem mem_coe {m : M} : m ∈ (S : set M) ↔ m ∈ S := iff.rfl

theorem ext' {S T : submonoid M} (h : (S : set M) = T) : S = T :=
by cases S; cases T; congr'

protected theorem ext'_iff {S T : submonoid M}  : (S : set M) = T ↔ S = T :=
⟨ext', λ h, h ▸ rfl⟩

@[extensionality] theorem ext {S T : submonoid M}
  (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := ext' $ set.ext h

/-- A submonoid contains the monoid's 1. -/
def one_mem : (1 : M) ∈ S := S.one_mem'

/-- A submonoid is closed under multiplication. -/
def mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S := submonoid.mul_mem' S

-- TODO -- this is a theorem about comm_monoids; see line 275 of module
lemma prod_mem {M : Type*} [comm_monoid M] (S : submonoid M)
  {ι : Type*} [decidable_eq ι] {t : finset ι} {f : ι → M} :
  (∀c ∈ t, f c ∈ S) → t.prod f ∈ S :=
finset.induction_on t (by simp [S.one_mem]) (by simp [S.mul_mem] {contextual := tt})

--@[to_additive is_add_submonoid.inter]
lemma inter (S₁ S₂ : submonoid M) :
  submonoid M :=
{ carrier := S₁ ∩ S₂,
  one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩,
  mul_mem' := λ _ _ hx hy,
    ⟨S₁.mul_mem hx.1 hy.1, S₂.mul_mem hx.2 hy.2⟩ }

/-- A directed union of submonoids is a submonoid. -/
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

-- need an additive version
--lemma is_add_submonoid_Union_of_directed {ι : Type*} [hι : nonempty ι]
--  (s : ι → set β) [∀ i, is_add_submonoid (s i)]
--  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
--  is_add_submonoid (⋃i, s i) :=
--multiplicative.is_submonoid_iff.1 $
--  @is_submonoid_Union_of_directed (multiplicative β) _ _ _ s _ directed
--attribute [to_additive is_add_submonoid_Union_of_directed] is_submonoid_Union_of_directed

--section powers

--def powers.carrier (x : M) : set M := {y | ∃ n:ℕ, x^n = y}
--def multiples (x : β) : set β := {y | ∃ n:ℕ, add_monoid.smul n x = y}
--attribute [to_additive multiples] powers

--lemma powers'.one_mem {x : M} : (1 : M) ∈ powers' x := ⟨0, pow_zero _⟩

--lemma multiples.zero_mem {x : β} : (0 : β) ∈ multiples x := ⟨0, add_monoid.zero_smul _⟩
--attribute [to_additive multiples.zero_mem] powers.one_mem

--lemma powers'.self_mem {x : M} : x ∈ powers' x := ⟨1, pow_one _⟩

--lemma multiples.self_mem {x : β} : x ∈ multiples x := ⟨1, add_monoid.one_smul _⟩
--attribute [to_additive multiples.self_mem] powers.self_mem

def powers (x : M) : submonoid M :=
{ carrier := {y | ∃ n:ℕ, x^n = y},
  one_mem' := ⟨0, pow_zero x⟩,
  mul_mem' := by rintros x₁ x₂ ⟨n₁, rfl⟩ ⟨n₂, rfl⟩; exact ⟨n₁ + n₂, pow_add _ _ _ ⟩ }

--instance multiples.is_add_submonoid (x : β) : is_add_submonoid (multiples x) :=
--multiplicative.is_submonoid_iff.1 $ powers.is_submonoid _
--attribute [to_additive multiples.is_add_submonoid] powers.is_submonoid

--@[to_additive univ.is_add_submonoid]
def univ : submonoid M :=
{ carrier := set.univ,
  one_mem' := set.mem_univ 1,
  mul_mem' := λ _ _ _ _, set.mem_univ _ }

-- used to be "preimage"
/-- The preimage of a submonoid along a monoid homomorphism is a submonoid. -/
def comap {N : Type*} [monoid N] (f : M →* N)
  (S : submonoid N) : submonoid M :=
{ carrier := (f ⁻¹' S),
  one_mem' := show f 1 ∈ S, by rw f.map_one; exact S.one_mem,
  mul_mem' := λ a b ha hb,
    show f (a * b) ∈ S, by rw f.map_mul; exact S.mul_mem ha hb }

-- used to be "image"
--@[instance, to_additive image.is_add_submonoid]
/-- The image of a submonoid along a monoid homomorphism is a submonoid. -/
def map {N : Type*} [monoid N] (f : M →* N) (S : submonoid M) : submonoid N :=
{ carrier := (f '' S),
  one_mem' := ⟨1, S.one_mem, f.map_one⟩,
  mul_mem' := begin rintros _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩, exact ⟨x * y, S.mul_mem hx hy,
    by rw f.map_mul; refl⟩ end }

/-- The range of a monoid homomorphism is a submonoid. -/
def range {N : Type*} [monoid N] (f : M →* N) :
  submonoid N := map f univ

lemma pow_mem {a : M} (h : a ∈ S) : ∀ {n : ℕ}, a ^ n ∈ S
| 0 := S.one_mem
| (n + 1) := S.mul_mem h pow_mem

--lemma is_add_submonoid.smul_mem {a : β} [is_add_submonoid t] :
--  ∀ (h : a ∈ t) {n : ℕ}, add_monoid.smul n a ∈ t :=
--@is_submonoid.pow_mem (multiplicative β) _ _ _ _
--attribute [to_additive is_add_submonoid.smul_mem] is_submonoid.pow_mem

lemma power_subset {a : M} (h : a ∈ S) : powers a ≤ S :=
assume x ⟨n, hx⟩, hx ▸ S.pow_mem h

--lemma is_add_submonoid.multiple_subset {a : β} [is_add_submonoid t] :
--  a ∈ t → multiples a ⊆ t :=
--@is_submonoid.power_subset (multiplicative β) _ _ _ _
--attribute [to_additive is_add_submonoid.multiple_subset] is_add_submonoid.multiple_subset

--@[to_additive is_add_submonoid.list_sum_mem]
lemma list_prod_mem : ∀ {l : list M}, (∀x∈l, x ∈ S) → l.prod ∈ S
| []     h := S.one_mem
| (a::l) h :=
  suffices a * l.prod ∈ S, by simpa,
  have a ∈ S ∧ (∀ x ∈ l, x ∈ S), by simpa using h,
  S.mul_mem this.1 (list_prod_mem this.2)

--@[to_additive is_add_submonoid.multiset_sum_mem]
lemma multiset_prod_mem {M} [comm_monoid M] (S : submonoid M) (m : multiset M) :
  (∀a ∈ m, a ∈ S) → m.prod ∈ S :=
begin
  refine quotient.induction_on m (assume l hl, _),
  rw [multiset.quot_mk_to_coe, multiset.coe_prod],
  exact S.list_prod_mem hl
end

--@[to_additive is_add_submonoid.finset_sum_mem]
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

instance : has_mul S := ⟨λ a b, ⟨a.1 * b.1, S.mul_mem a.2 b.2⟩⟩
instance : has_one S := ⟨⟨_, S.one_mem⟩⟩

@[simp] lemma coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y := rfl
@[simp] lemma coe_one : ((1 : S) : M) = 1 := rfl

end submonoid

instance subtype.monoid {M : Type*} [monoid M] {S : submonoid M} : monoid S :=
{ mul := (*),
  mul_assoc := by { intros, apply set_coe.ext, apply mul_assoc },
  one := 1,
  one_mul := by { intros, apply set_coe.ext, apply one_mul },
  mul_one := by { intros, apply set_coe.ext, apply mul_one } }

--attribute [to_additive subtype.add_monoid._proof_1] subtype.monoid._proof_1
--attribute [to_additive subtype.add_monoid._proof_2] subtype.monoid._proof_2
--attribute [to_additive subtype.add_monoid._proof_3] subtype.monoid._proof_3
--attribute [to_additive subtype.add_monoid._proof_4] subtype.monoid._proof_4
--attribute [to_additive subtype.add_monoid._proof_5] subtype.monoid._proof_5
--attribute [to_additive subtype.add_monoid] subtype.monoid

--@[simp, to_additive is_add_submonoid.coe_zero]
--@[simp] lemma is_submonoid.coe_one [is_submonoid s] : ((1 : s) : α) = 1 := rfl

--@[simp, to_additive is_add_submonoid.coe_add]
--lemma is_submonoid.coe_mul [is_submonoid s] (a b : s) : ((a * b : s) : α) = a * b := rfl

namespace submonoid

@[simp] lemma coe_pow (a : S) (n : ℕ) : ((a ^ n : S) : M) = a ^ n :=
by induction n; simp [*, pow_succ]

--@[simp] lemma is_add_submonoid.smul_coe {β : Type*} [add_monoid β] {s : set β}
--  [is_add_submonoid s] (a : s) (n : ℕ) : ((add_monoid.smul n a : s) : β) = add_monoid.smul n a :=
--by induction n; [refl, simp [*, succ_smul]]
--attribute [to_additive is_add_submonoid.smul_coe] is_submonoid.coe_pow

--@[to_additive subtype_val.is_add_monoid_hom]
def subtype : S →* M :=
{ to_fun := coe,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

@[simp] theorem subtype_apply (x : S) : S.subtype x = x := rfl

lemma subtype_eq_val : (S.subtype : S → M) = subtype.val := rfl

--@[to_additive coe.is_add_monoid_hom]
--instance coe.is_monoid_hom [is_submonoid s] : is_monoid_hom (coe : s → α) :=
--subtype_val.is_monoid_hom

end submonoid

namespace monoid_hom

--@[to_additive subtype_mk.is_add_monoid_hom]
def subtype_mk {N : Type*} [monoid N] (f : N →* M) (h : ∀ x, f x ∈ S) : N →* S :=
{ to_fun := λ n, ⟨f n, h n⟩,
  map_one' := subtype.eq (is_monoid_hom.map_one f),
  map_mul' := λ x y, subtype.eq (is_monoid_hom.map_mul f x y) }

--@[to_additive set_inclusion.is_add_monoid_hom]
def set_inclusion (T : submonoid M) (h : S ≤ T) : S →* T :=
subtype_mk _ S.subtype (λ x, h x.2)

end monoid_hom

namespace submonoid

inductive in_closure (s : set M) : M → Prop
| basic {a : M} : a ∈ s → in_closure a
| one : in_closure 1
| mul {a b : M} : in_closure a → in_closure b → in_closure (a * b)

def closure (s : set M) : submonoid M :=
{ carrier := in_closure s,
  one_mem' := in_closure.one s,
  mul_mem' := λ _ _, in_closure.mul}

theorem subset_closure {s : set M} : s ≤ closure s :=
λ a, in_closure.basic

theorem closure_subset {s : set M} {T : submonoid M} (h : s ≤ T) : closure s ≤ T :=
assume a ha, by induction ha;
begin

  sorry
end
--simp [h _, *, T.one_mem, T.mul_mem]

theorem closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans h subset_closure

theorem closure_singleton {x : α} : closure ({x} : set α) = powers x :=
set.eq_of_subset_of_subset (closure_subset $ set.singleton_subset_iff.2 $ powers.self_mem) $
  is_submonoid.power_subset $ set.singleton_subset_iff.1 $ subset_closure

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

namespace add_monoid

def closure (s : set β) : set β := @monoid.closure (multiplicative β) _ s
attribute [to_additive add_monoid.closure] monoid.closure

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
