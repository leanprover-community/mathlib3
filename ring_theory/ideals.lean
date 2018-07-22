/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes
-/
import algebra.module tactic.ring linear_algebra.quotient_module

universes u v
variables {α : Type u} {β : Type v} [comm_ring α] {a b : α}
open set function

local attribute [instance] classical.prop_decidable

class is_ideal {α : Type u} [comm_ring α] (S : set α) extends is_submodule S : Prop

namespace is_ideal

protected lemma zero (S : set α) [is_ideal S] : (0 : α) ∈ S := is_submodule.zero_ α S

protected lemma add {S : set α} [is_ideal S] : a ∈ S → b ∈ S → a + b ∈ S := is_submodule.add_ α

lemma neg_iff {S : set α} [is_ideal S] : a ∈ S ↔ -a ∈ S := ⟨is_submodule.neg, λ h, neg_neg a ▸ is_submodule.neg h⟩

protected lemma sub {S : set α} [is_ideal S] : a ∈ S → b ∈ S → a - b ∈ S := is_submodule.sub

lemma mul_left {S : set α} [is_ideal S] : b ∈ S → a * b ∈ S := @is_submodule.smul α α _ _ _ _ a _

lemma mul_right {S : set α} [is_ideal S] : a ∈ S → a * b ∈ S := mul_comm b a ▸ mul_left

end is_ideal

instance (S : set α) : is_ideal (span S) := {}

class is_proper_ideal {α : Type u} [comm_ring α] (S : set α) extends is_ideal S : Prop :=
(ne_univ : S ≠ set.univ)

lemma is_proper_ideal_iff_one_not_mem {S : set α} [hS : is_ideal S] : 
  is_proper_ideal S ↔ (1 : α) ∉ S :=
⟨λ h h1, by exactI is_proper_ideal.ne_univ S 
  (eq_univ_iff_forall.2 (λ a, mul_one a ▸ is_ideal.mul_left h1)), 
λ h, {ne_univ := mt eq_univ_iff_forall.1 (λ ha, h (ha _)), ..hS}⟩

class is_prime_ideal {α : Type u} [comm_ring α] (S : set α) extends is_proper_ideal S : Prop :=
(mem_or_mem_of_mul_mem : ∀ {x y : α}, x * y ∈ S → x ∈ S ∨ y ∈ S)

theorem mem_or_mem_of_mul_eq_zero {α : Type u} [comm_ring α] (S : set α) [is_prime_ideal S] :
  ∀ {x y : α}, x * y = 0 → x ∈ S ∨ y ∈ S :=
λ x y hxy, have x * y ∈ S, by rw hxy; from (@is_submodule.zero α α _ _ S _ : (0:α) ∈ S),
is_prime_ideal.mem_or_mem_of_mul_mem this

class is_maximal_ideal {α : Type u} [comm_ring α] (S : set α) extends is_proper_ideal S : Prop :=
mk' ::
  (eq_or_univ_of_subset : ∀ (T : set α) [is_submodule T], S ⊆ T → T = S ∨ T = set.univ)

theorem is_maximal_ideal.mk {α : Type u} [comm_ring α] (S : set α) [is_submodule S]
  (h₁ : (1:α) ∉ S) (h₂ : ∀ x (T : set α) [is_submodule T], S ⊆ T → x ∉ S → x ∈ T → (1:α) ∈ T) :
  is_maximal_ideal S :=
{ ne_univ              := assume hu, have (1:α) ∈ S, by rw hu; trivial, h₁ this,
  eq_or_univ_of_subset := assume T ht hst, classical.or_iff_not_imp_left.2 $ assume (hnst : T ≠ S),
    let ⟨x, hxt, hxns⟩ := set.exists_of_ssubset ⟨hst, hnst.symm⟩ in
    @@is_submodule.univ_of_one_mem _ T ht $ @@h₂ x T ht hst hxns hxt}

instance is_maximal_ideal.is_prime_ideal (S : set α) [hS : is_maximal_ideal S] : is_prime_ideal S :=
{ mem_or_mem_of_mul_mem := λ x y hxy, or_iff_not_imp_left.2 (λ h, 
  have (span (insert x S)) = univ := or.resolve_left (is_maximal_ideal.eq_or_univ_of_subset _ 
    (subset.trans (subset_insert _ _) subset_span)) (λ hS, h $ hS ▸ subset_span (mem_insert _ _)),
  have (1 : α) ∈ span (insert x S) := this.symm ▸ mem_univ _,
  let ⟨a, ha⟩ := mem_span_insert.1 this in
  have hy : y * (1 + a • x) - a * (x * y) = y := by rw smul_eq_mul; ring,
  hy ▸ is_ideal.sub (is_ideal.mul_left (span_eq_of_is_submodule (show is_submodule S, by apply_instance) 
    ▸ ha)) (is_ideal.mul_left hxy)),
  ..hS } 

def nonunits (α : Type u) [monoid α] : set α := { x | ¬∃ y, y * x = 1 }

theorem not_unit_of_mem_proper_ideal {α : Type u} [comm_ring α] (S : set α) [is_proper_ideal S] :
  S ⊆ nonunits α :=
λ x hx ⟨y, hxy⟩, is_proper_ideal.ne_univ S $ is_submodule.eq_univ_of_contains_unit S x y hx hxy

class local_ring (α : Type u) [comm_ring α] :=
(S : set α)
(max : is_maximal_ideal S)
(unique : ∀ T [is_maximal_ideal T], S = T)

def local_of_nonunits_ideal {α : Type u} [comm_ring α] (hnze : (0:α) ≠ 1)
  (h : ∀ x y ∈ nonunits α, x + y ∈ nonunits α) : local_ring α :=
have hi : is_submodule (nonunits α), from
  { zero_ := λ ⟨y, hy⟩, hnze $ by simpa using hy,
    add_  := h,
    smul  := λ x y hy ⟨z, hz⟩, hy ⟨x * z, by rw [← hz]; simp [mul_left_comm, mul_assoc]⟩ },
{ S      := nonunits α,
  max    := @@is_maximal_ideal.mk _ (nonunits α) hi (λ ho, ho ⟨1, mul_one 1⟩) $
    λ x T ht hst hxns hxt,
    let ⟨y, hxy⟩ := classical.by_contradiction hxns in
    by rw [← hxy]; exact @@is_submodule.smul _ _ ht y hxt,
  unique := λ T hmt, or.cases_on
    (@@is_maximal_ideal.eq_or_univ_of_subset _ hmt (nonunits α) hi $
      λ z hz, @@not_unit_of_mem_proper_ideal _ T (by resetI; apply_instance) hz)
    id
    (λ htu, false.elim $ ((set.ext_iff _ _).1 htu 1).2 trivial ⟨1, mul_one 1⟩) }

namespace quotient_ring
open is_ideal

def quotient_rel (S : set α) [is_ideal S] := is_submodule.quotient_rel S

def quotient (S : set α) [is_ideal S] := quotient (quotient_rel S)

def mk {S : set α} [is_ideal S] (a : α) : quotient S :=
quotient.mk' a

instance {S : set α} [is_ideal S] : has_coe α (quotient S) := ⟨mk⟩

instance (S : set α) [is_ideal S] : comm_ring (quotient S) :=
{ mul := λ a b, quotient.lift_on₂' a b (λ a b, ((a * b : α) : quotient S))
  (λ a₁ a₂ b₁ b₂ (h₁ : a₁ - b₁ ∈ S) (h₂ : a₂ - b₂ ∈ S), 
    quotient.sound'
    (show a₁ * a₂ - b₁ * b₂ ∈ S, from
    have h : a₂ * (a₁ - b₁) + (a₂ - b₂) * b₁ =
      a₁ * a₂ - b₁ * b₂, by ring,
    h ▸ is_ideal.add (mul_left h₁) (mul_right h₂))),
  mul_assoc := λ a b c, quotient.induction_on₃' a b c $ 
    λ a b c, congr_arg mk (mul_assoc a b c),
  mul_comm := λ a b, quotient.induction_on₂' a b $
    λ a b, congr_arg mk (mul_comm a b),
  one := (1 : α),
  one_mul := λ a, quotient.induction_on' a $
    λ a, congr_arg mk (one_mul a),
  mul_one := λ a, quotient.induction_on' a $
    λ a, congr_arg mk (mul_one a),
  left_distrib := λ a b c, quotient.induction_on₃' a b c $ 
    λ a b c, congr_arg mk (left_distrib a b c),
  right_distrib := λ a b c, quotient.induction_on₃' a b c $ 
    λ a b c, congr_arg mk (right_distrib a b c),
  ..is_submodule.quotient.add_comm_group S }

instance is_ring_hom_mk (S : set α) [is_ideal S] : 
  @is_ring_hom _ (quotient S) _ _ mk :=
by refine {..}; intros; refl

@[simp] lemma coe_zero (S : set α) [is_ideal S] : ((0 : α) : quotient S) = 0 := rfl
@[simp] lemma coe_one (S : set α) [is_ideal S] : ((1 : α) : quotient S) = 1 := rfl
@[simp] lemma coe_add (S : set α) [is_ideal S] (a b : α) : ((a + b : α) : quotient S) = a + b := rfl
@[simp] lemma coe_mul (S : set α) [is_ideal S] (a b : α) : ((a * b : α) : quotient S) = a * b := rfl
@[simp] lemma coe_neg (S : set α) [is_ideal S] (a : α) : ((-a : α) : quotient S) = -a := rfl
@[simp] lemma coe_sub (S : set α) [is_ideal S] (a b : α) : ((a - b : α) : quotient S) = a - b := rfl
@[simp] lemma coe_bit0 (S : set α) [is_ideal S] (a : α) : ((bit0 a : α) : quotient S) = bit0 a := rfl
@[simp] lemma coe_bit1 (S : set α) [is_ideal S] (a : α) : ((bit1 a : α) : quotient S) = bit1 a := rfl
@[simp] lemma coe_pow (S : set α) [is_ideal S] (a : α) (n : ℕ) : ((a ^ n : α) : quotient S) = a ^ n :=
by induction n; simp [*, pow_succ]

lemma eq_zero_iff_mem {S : set α} [is_ideal S] : 
  (a : quotient S) = 0 ↔ a ∈ S :=
by conv {to_rhs, rw ← sub_zero a }; exact quotient.eq'

instance (S : set α) [is_proper_ideal S] : nonzero_comm_ring (quotient S) :=
{ zero_ne_one := ne.symm $ mt eq_zero_iff_mem.1 
    (is_proper_ideal_iff_one_not_mem.1 (by apply_instance)),
  ..quotient_ring.comm_ring S }

instance (S : set α) [is_prime_ideal S] : integral_domain (quotient S) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b,
    quotient.induction_on₂' a b $ λ a b hab,
      (is_prime_ideal.mem_or_mem_of_mul_mem 
        (eq_zero_iff_mem.1 hab)).elim
      (or.inl ∘ eq_zero_iff_mem.2)
      (or.inr ∘ eq_zero_iff_mem.2),
  ..quotient_ring.nonzero_comm_ring S }

lemma exists_inv {S : set α} [is_maximal_ideal S] {a : quotient S} : a ≠ 0 →
  ∃ b : quotient S, a * b = 1 :=
quotient.induction_on' a $ λ a ha,
classical.by_contradiction $ λ h,
have haS : a ∉ S := mt eq_zero_iff_mem.2 ha,
by haveI hS : is_proper_ideal (span (set.insert a S)) :=
  is_proper_ideal_iff_one_not_mem.2
  (mt mem_span_insert.1 $ λ ⟨b, hb⟩,
  h ⟨-b, quotient.sound' (show a * -b - 1 ∈ S,
    from neg_iff.2 (begin
      rw [neg_sub, mul_neg_eq_neg_mul_symm, sub_eq_add_neg, neg_neg, mul_comm],
      rw span_eq_of_is_submodule (show is_submodule S, by apply_instance) at hb,
      exact hb
    end))⟩);
exact have span (set.insert a S) = S :=
    or.resolve_right (is_maximal_ideal.eq_or_univ_of_subset (span (set.insert a S))
    (subset.trans (subset_insert _ _) subset_span)) (is_proper_ideal.ne_univ _),
  haS (this ▸ subset_span (mem_insert _ _))

/- quotient by maximal ideal is a field. def rather than instance, since users will have
computable inverses in some applications -/
protected noncomputable def field (S : set α) [is_maximal_ideal S] : field (quotient S) :=
{ inv := λ a, if ha : a = 0 then 0 else classical.some (exists_inv ha),
  mul_inv_cancel := λ a (ha : a ≠ 0), show a * dite _ _ _ = _, 
    by rw dif_neg ha;
    exact classical.some_spec (exists_inv ha),
  inv_mul_cancel := λ a (ha : a ≠ 0), show dite _ _ _ * a = _, 
    by rw [mul_comm, dif_neg ha];
    exact classical.some_spec (exists_inv ha),
  ..quotient_ring.integral_domain S }

end quotient_ring
