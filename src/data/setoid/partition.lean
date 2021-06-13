/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen, Patrick Massot
-/

import data.setoid.basic
import data.set.lattice

/-!
# Equivalence relations: partitions

This file comprises properties of equivalence relations viewed as partitions.
There are two implementations of partitions here:
* A collection `c : set (set α)` of sets is a partition of `α` if `∅ ∉ c` and each element `a : α`
  belongs to a unique set `b ∈ c`. This is expressed as `is_partition c`
* An indexed partition is a map `s : ι → α` whose image is a partition. This is
  expressed as `indexed_partition s`.

Of course both implementations are related to `quotient` and `setoid`.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation, partition, equivalence class
-/

namespace setoid

variables {α : Type*}

/-- If x ∈ α is in 2 elements of a set of sets partitioning α, those 2 sets are equal. -/
lemma eq_of_mem_eqv_class {c : set (set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b)
  {x b b'} (hc : b ∈ c) (hb : x ∈ b) (hc' : b' ∈ c) (hb' : x ∈ b') :
  b = b' :=
(H x).unique2 hc hb hc' hb'

/-- Makes an equivalence relation from a set of sets partitioning α. -/
def mk_classes (c : set (set α)) (H : ∀ a, ∃! b ∈ c, a ∈ b) :
  setoid α :=
⟨λ x y, ∀ s ∈ c, x ∈ s → y ∈ s, ⟨λ _ _ _ hx, hx,
 λ x y h s hs hy, (H x).elim2 $ λ t ht hx _,
   have s = t, from eq_of_mem_eqv_class H hs hy ht (h t ht hx),
   this.symm ▸ hx,
 λ x y z h1 h2 s hs hx, (H y).elim2 $ λ t ht hy _, (H z).elim2 $ λ t' ht' hz _,
   have hst : s = t, from eq_of_mem_eqv_class H hs (h1 _ hs hx) ht hy,
   have htt' : t = t', from eq_of_mem_eqv_class H ht (h2 _ ht hy) ht' hz,
   (hst.trans htt').symm ▸ hz⟩⟩

/-- Makes the equivalence classes of an equivalence relation. -/
def classes (r : setoid α) : set (set α) :=
{s | ∃ y, s = {x | r.rel x y}}

lemma mem_classes (r : setoid α) (y) : {x | r.rel x y} ∈ r.classes := ⟨y, rfl⟩

/-- Two equivalence relations are equal iff all their equivalence classes are equal. -/
lemma eq_iff_classes_eq {r₁ r₂ : setoid α} :
  r₁ = r₂ ↔ ∀ x, {y | r₁.rel x y} = {y | r₂.rel x y} :=
⟨λ h x, h ▸ rfl, λ h, ext' $ λ x, set.ext_iff.1 $ h x⟩

lemma rel_iff_exists_classes (r : setoid α) {x y} :
  r.rel x y ↔ ∃ c ∈ r.classes, x ∈ c ∧ y ∈ c :=
⟨λ h, ⟨_, r.mem_classes y, h, r.refl' y⟩,
  λ ⟨c, ⟨z, hz⟩, hx, hy⟩, by { subst c, exact r.trans' hx (r.symm' hy) }⟩

/-- Two equivalence relations are equal iff their equivalence classes are equal. -/
lemma classes_inj {r₁ r₂ : setoid α} :
  r₁ = r₂ ↔ r₁.classes = r₂.classes :=
⟨λ h, h ▸ rfl, λ h, ext' $ λ a b, by simp only [rel_iff_exists_classes, exists_prop, h] ⟩

/-- The empty set is not an equivalence class. -/
lemma empty_not_mem_classes {r : setoid α} : ∅ ∉ r.classes :=
λ ⟨y, hy⟩, set.not_mem_empty y $ hy.symm ▸ r.refl' y

/-- Equivalence classes partition the type. -/
lemma classes_eqv_classes {r : setoid α} (a) : ∃! b ∈ r.classes, a ∈ b :=
exists_unique.intro2 {x | r.rel x a} (r.mem_classes a) (r.refl' _) $
begin
  rintros _ ⟨y, rfl⟩ ha,
  ext x,
  exact ⟨λ hx, r.trans' hx (r.symm' ha), λ hx, r.trans' hx ha⟩
end

/-- If x ∈ α is in 2 equivalence classes, the equivalence classes are equal. -/
lemma eq_of_mem_classes {r : setoid α} {x b} (hc : b ∈ r.classes)
  (hb : x ∈ b) {b'} (hc' : b' ∈ r.classes) (hb' : x ∈ b') : b = b' :=
eq_of_mem_eqv_class classes_eqv_classes hc hb hc' hb'

/-- The elements of a set of sets partitioning α are the equivalence classes of the
    equivalence relation defined by the set of sets. -/
lemma eq_eqv_class_of_mem {c : set (set α)}
  (H : ∀ a, ∃! b ∈ c, a ∈ b) {s y} (hs : s ∈ c) (hy : y ∈ s) :
  s = {x | (mk_classes c H).rel x y} :=
set.ext $ λ x,
  ⟨λ hs', symm' (mk_classes c H) $ λ b' hb' h', eq_of_mem_eqv_class H hs hy hb' h' ▸ hs',
   λ hx, (H x).elim2 $ λ b' hc' hb' h',
     (eq_of_mem_eqv_class H hs hy hc' $ hx b' hc' hb').symm ▸ hb'⟩

/-- The equivalence classes of the equivalence relation defined by a set of sets
    partitioning α are elements of the set of sets. -/
lemma eqv_class_mem {c : set (set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {y} :
  {x | (mk_classes c H).rel x y} ∈ c :=
(H y).elim2 $ λ b hc hy hb, eq_eqv_class_of_mem H hc hy ▸ hc

lemma eqv_class_mem' {c : set (set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) {x} :
  {y : α | (mk_classes c H).rel x y} ∈ c :=
by { convert setoid.eqv_class_mem H, ext, rw setoid.comm }

/-- Distinct elements of a set of sets partitioning α are disjoint. -/
lemma eqv_classes_disjoint {c : set (set α)} (H : ∀ a, ∃! b ∈ c, a ∈ b) :
  set.pairwise_disjoint c :=
λ b₁ h₁ b₂ h₂ h, set.disjoint_left.2 $
  λ x hx1 hx2, (H x).elim2 $ λ b hc hx hb, h $ eq_of_mem_eqv_class H h₁ hx1 h₂ hx2

/-- A set of disjoint sets covering α partition α (classical). -/
lemma eqv_classes_of_disjoint_union {c : set (set α)}
  (hu : set.sUnion c = @set.univ α) (H : set.pairwise_disjoint c) (a) :
  ∃! b ∈ c, a ∈ b :=
let ⟨b, hc, ha⟩ := set.mem_sUnion.1 $ show a ∈ _, by rw hu; exact set.mem_univ a in
  exists_unique.intro2 b hc ha $ λ b' hc' ha', H.elim hc' hc a ha' ha

/-- Makes an equivalence relation from a set of disjoints sets covering α. -/
def setoid_of_disjoint_union {c : set (set α)} (hu : set.sUnion c = @set.univ α)
  (H : set.pairwise_disjoint c) : setoid α :=
setoid.mk_classes c $ eqv_classes_of_disjoint_union hu H

/-- The equivalence relation made from the equivalence classes of an equivalence
    relation r equals r. -/
theorem mk_classes_classes (r : setoid α) :
  mk_classes r.classes classes_eqv_classes = r :=
ext' $ λ x y, ⟨λ h, r.symm' (h {z | r.rel z x} (r.mem_classes x) $ r.refl' x),
  λ h b hb hx, eq_of_mem_classes (r.mem_classes x) (r.refl' x) hb hx ▸ r.symm' h⟩

@[simp] theorem sUnion_classes (r : setoid α) : ⋃₀ r.classes = set.univ :=
set.eq_univ_of_forall $ λ x, set.mem_sUnion.2 ⟨{ y | r.rel y x }, ⟨x, rfl⟩, setoid.refl _⟩

section partition

/-- A collection `c : set (set α)` of sets is a partition of `α` into pairwise
disjoint sets if `∅ ∉ c` and each element `a : α` belongs to a unique set `b ∈ c`. -/
def is_partition (c : set (set α)) :=
∅ ∉ c ∧ ∀ a, ∃! b ∈ c, a ∈ b

/-- A partition of `α` does not contain the empty set. -/
lemma nonempty_of_mem_partition {c : set (set α)} (hc : is_partition c) {s} (h : s ∈ c) :
  s.nonempty :=
set.ne_empty_iff_nonempty.1 $ λ hs0, hc.1 $ hs0 ▸ h

lemma is_partition_classes (r : setoid α) : is_partition r.classes :=
⟨empty_not_mem_classes, classes_eqv_classes⟩

lemma is_partition.pairwise_disjoint {c : set (set α)} (hc : is_partition c) :
  c.pairwise_disjoint :=
eqv_classes_disjoint hc.2

lemma is_partition.sUnion_eq_univ {c : set (set α)} (hc : is_partition c) :
  ⋃₀ c = set.univ :=
set.eq_univ_of_forall $ λ x, set.mem_sUnion.2 $
  let ⟨t, ht⟩ := hc.2 x in ⟨t, by clear_aux_decl; finish⟩

/-- All elements of a partition of α are the equivalence class of some y ∈ α. -/
lemma exists_of_mem_partition {c : set (set α)} (hc : is_partition c) {s} (hs : s ∈ c) :
  ∃ y, s = {x | (mk_classes c hc.2).rel x y} :=
let ⟨y, hy⟩ := nonempty_of_mem_partition hc hs in
  ⟨y, eq_eqv_class_of_mem hc.2 hs hy⟩

/-- The equivalence classes of the equivalence relation defined by a partition of α equal
    the original partition. -/
theorem classes_mk_classes (c : set (set α)) (hc : is_partition c) :
  (mk_classes c hc.2).classes = c :=
set.ext $ λ s,
  ⟨λ ⟨y, hs⟩, (hc.2 y).elim2 $ λ b hm hb hy,
    by rwa (show s = b, from hs.symm ▸ set.ext
      (λ x, ⟨λ hx, symm' (mk_classes c hc.2) hx b hm hb,
             λ hx b' hc' hx', eq_of_mem_eqv_class hc.2 hm hx hc' hx' ▸ hb⟩)),
   exists_of_mem_partition hc⟩

/-- Defining `≤` on partitions as the `≤` defined on their induced equivalence relations. -/
instance partition.le : has_le (subtype (@is_partition α)) :=
⟨λ x y, mk_classes x.1 x.2.2 ≤ mk_classes y.1 y.2.2⟩

/-- Defining a partial order on partitions as the partial order on their induced
    equivalence relations. -/
instance partition.partial_order : partial_order (subtype (@is_partition α)) :=
{ le := (≤),
  lt := λ x y, x ≤ y ∧ ¬y ≤ x,
  le_refl := λ _, @le_refl (setoid α) _ _,
  le_trans := λ _ _ _, @le_trans (setoid α) _ _ _ _,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ x y hx hy, let h := @le_antisymm (setoid α) _ _ _ hx hy in by
    rw [subtype.ext_iff_val, ←classes_mk_classes x.1 x.2, ←classes_mk_classes y.1 y.2, h] }

variables (α)

/-- The order-preserving bijection between equivalence relations and partitions of sets. -/
def partition.rel_iso :
  setoid α ≃o subtype (@is_partition α) :=
{ to_fun := λ r, ⟨r.classes, empty_not_mem_classes, classes_eqv_classes⟩,
  inv_fun := λ x, mk_classes x.1 x.2.2,
  left_inv := mk_classes_classes,
  right_inv := λ x, by rw [subtype.ext_iff_val, ←classes_mk_classes x.1 x.2],
  map_rel_iff' := λ x y,
    by { conv_rhs { rw [←mk_classes_classes x, ←mk_classes_classes y] }, refl } }

variables {α}

/-- A complete lattice instance for partitions; there is more infrastructure for the
    equivalent complete lattice on equivalence relations. -/
instance partition.complete_lattice : complete_lattice (subtype (@is_partition α)) :=
galois_insertion.lift_complete_lattice $ @rel_iso.to_galois_insertion
_ (subtype (@is_partition α)) _ (partial_order.to_preorder _) $ partition.rel_iso α

end partition

end setoid

/-- A partition of a type indexed by another type. -/
@[nolint has_inhabited_instance]
structure indexed_partition {ι α : Type*} (s : ι → set α) :=
(eq_of_mem : ∀ {x i j}, x ∈ s i → x ∈ s j → i = j)
(some : ι → α)
(some_mem : ∀ i, some i ∈ s i)
(index : α → ι)
(mem_index : ∀ x, x ∈ s (index x))

/-- The non-constructive constructor for `indexed_partition`. -/
noncomputable
def indexed_partition.mk' {ι α : Type*} (s : ι → set α) (dis : ∀ i j, i ≠ j → disjoint (s i) (s j))
(empty : ∀ i, (s i).nonempty) (ex : ∀ x, ∃ i, x ∈ s i) : indexed_partition s :=
{ eq_of_mem := begin
    classical,
    intros x i j hxi hxj,
    by_contra h,
    exact dis _ _ h ⟨hxi, hxj⟩
  end,
  some := λ i, (empty i).some,
  some_mem := λ i, (empty i).some_spec,
  index := λ x, (ex x).some,
  mem_index := λ x, (ex x).some_spec }

namespace indexed_partition

open set

variables {ι α : Type*} {s : ι → set α} (hs : indexed_partition s)
include hs

lemma exists_mem (x : α) : ∃ i, x ∈ s i := ⟨hs.index x, hs.mem_index x⟩

lemma Union : (⋃ i, s i) = univ :=
by { ext x, simp [hs.exists_mem x] }

lemma disjoint : ∀ {i j}, i ≠ j → disjoint (s i) (s j) :=
λ i j h x ⟨hxi, hxj⟩,h (hs.eq_of_mem hxi hxj)

lemma eq_index_of_mem {x i} (hxi : x ∈ s i) : i = hs.index x :=
hs.eq_of_mem hxi (hs.mem_index x)

/-- The equivalence relation associated to an indexed partition. Two
elements are equivalent if they belong to the same set of the partition. -/
protected def setoid (hs : indexed_partition s) : setoid α :=
{ r := λ x y, ∃ i, x ∈ s i ∧ y ∈ s i,
  iseqv := ⟨λ x, ⟨hs.index x, hs.mem_index x, hs.mem_index x⟩,
            λ x y ⟨i, hxi, hyi⟩, ⟨i, hyi, hxi⟩,
            λ x y z ⟨i, hxi, hyi⟩ ⟨j, hyj, hzj⟩, ⟨i, hxi, (hs.eq_of_mem hyj hyi) ▸ hzj⟩⟩ }

lemma some_index (x : α) : hs.setoid.rel (hs.some (hs.index x)) x :=
⟨hs.index x, hs.some_mem (hs.index x), hs.mem_index x⟩

@[simp] lemma index_some (i : ι) : hs.index (hs.some i) = i :=
(eq_index_of_mem _ $ hs.some_mem i).symm

/-- The quotient associated to an indexed partition. -/
@[nolint has_inhabited_instance]
protected def quotient := quotient hs.setoid

/-- The projection onto the quotient associated to an indexed partition. -/
def proj : α → hs.quotient := @quotient.mk α hs.setoid

lemma proj_eq_iff {x y : α} : hs.proj x = hs.proj y ↔ hs.setoid.rel x y :=
quotient.eq_rel

/-- A map choosing a representative for each element of the quotient associated to an indexed
partition. -/
noncomputable
def out : hs.quotient → α := @quotient.out α hs.setoid

@[simp] lemma proj_out (x : hs.quotient) : hs.proj (hs.out x) = x :=
quot.out_eq _

lemma out_proj (x : α) : hs.setoid.rel (hs.out (hs.proj x)) x :=
quotient.mk_out' x

@[simp] lemma out_proj_some (i : ι) : hs.out (hs.proj (hs.some i)) ∈ s i :=
begin
  letI : setoid α := hs.setoid,
  rcases quotient.mk_out (hs.some i) with ⟨j, hj, hj'⟩,
  rwa hs.eq_of_mem hj' (hs.some_mem i) at hj
end

@[simp] lemma index_out_proj_some (i : ι) : hs.index (hs.out $ hs.proj $ hs.some i) = i :=
hs.eq_of_mem (hs.mem_index $ hs.out $ hs.proj (hs.some i)) (hs.out_proj_some i)

lemma class_of {x : α} : set_of (hs.setoid.rel x) = s (hs.index x) :=
begin
  ext y,
  change (∃ i, x ∈ s i ∧ y ∈ s i) ↔ y ∈ s (hs.index x),
  split,
  { rintros ⟨i, hxi, hyi⟩,
    rwa hs.eq_index_of_mem hxi at hyi },
  { intro h,
    exact ⟨hs.index x, hs.mem_index x, h⟩ },
end

/-- The obvious equivalence between the quotient associated to an indexed partition and
the indexing type. -/
noncomputable
def equiv_quotient : ι ≃ hs.quotient :=
{ to_fun := hs.proj ∘ hs.some,
  inv_fun := hs.index ∘ hs.out,
  left_inv := hs.index_out_proj_some,
  right_inv := begin
    intros z,
    conv_rhs { rw ← hs.proj_out z},
    rw proj_eq_iff,
    apply some_index,
  end }

@[simp] lemma equiv_quotient_index_apply (x : α) : hs.equiv_quotient (hs.index x) = hs.proj x :=
hs.proj_eq_iff.mpr (some_index hs x)

lemma equiv_quotient_index : hs.equiv_quotient ∘ hs.index = hs.proj :=
funext hs.equiv_quotient_index_apply

lemma proj_fiber (x : hs.quotient) : hs.proj ⁻¹' {x} = s (hs.equiv_quotient.symm x) :=
begin
  letI := hs.setoid,
  change {y | ⟦y⟧ = x} = s(hs.index $ hs.out x),
  rw ← hs.class_of,
  ext y,
  change ⟦y⟧ = x ↔ hs.setoid.rel (hs.out x) y,
  rw [hs.setoid.comm, quotient.mk_eq_iff_out],
  refl
end

end indexed_partition
