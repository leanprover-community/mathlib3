/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Direct sum of abelian groups, indexed by a discrete type.
-/
import data.dfinsupp

universes u v w u₁

variables (ι : Type v) [decidable_eq ι] (β : ι → Type w) [Π i, add_comm_group (β i)]

def direct_sum : Type* := Π₀ i, β i

namespace direct_sum

variables {ι β}

instance : add_comm_group (direct_sum ι β) :=
dfinsupp.add_comm_group

instance : inhabited (direct_sum ι β) := ⟨0⟩

variables β
def mk : Π s : finset ι, (Π i : (↑s : set ι), β i.1) → direct_sum ι β :=
dfinsupp.mk

def of : Π i : ι, β i → direct_sum ι β :=
dfinsupp.single
variables {β}

instance mk.is_add_group_hom (s : finset ι) : is_add_group_hom (mk β s) :=
{ map_add := λ _ _, dfinsupp.mk_add }

@[simp] lemma mk_zero (s : finset ι) : mk β s 0 = 0 :=
is_add_group_hom.map_zero _

@[simp] lemma mk_add (s : finset ι) (x y) : mk β s (x + y) = mk β s x + mk β s y :=
is_add_hom.map_add _ x y

@[simp] lemma mk_neg (s : finset ι) (x) : mk β s (-x) = -mk β s x :=
is_add_group_hom.map_neg _ x

@[simp] lemma mk_sub (s : finset ι) (x y) : mk β s (x - y) = mk β s x - mk β s y :=
is_add_group_hom.map_sub _ x y

instance of.is_add_group_hom (i : ι) : is_add_group_hom (of β i) :=
{ map_add := λ _ _, dfinsupp.single_add }

@[simp] lemma of_zero (i : ι) : of β i 0 = 0 :=
is_add_group_hom.map_zero _

@[simp] lemma of_add (i : ι) (x y) : of β i (x + y) = of β i x + of β i y :=
is_add_hom.map_add _ x y

@[simp] lemma of_neg (i : ι) (x) : of β i (-x) = -of β i x :=
is_add_group_hom.map_neg _ x

@[simp] lemma of_sub (i : ι) (x y) : of β i (x - y) = of β i x - of β i y :=
is_add_group_hom.map_sub _ x y

theorem mk_inj (s : finset ι) : function.injective (mk β s) :=
dfinsupp.mk_inj s

theorem of_inj (i : ι) : function.injective (of β i) :=
λ x y H, congr_fun (mk_inj _ H) ⟨i, by simp⟩

@[elab_as_eliminator]
protected theorem induction_on {C : direct_sum ι β → Prop}
  (x : direct_sum ι β) (H_zero : C 0)
  (H_basic : ∀ (i : ι) (x : β i), C (of β i x))
  (H_plus : ∀ x y, C x → C y → C (x + y)) : C x :=
begin
  apply dfinsupp.induction x H_zero,
  intros i b f h1 h2 ih,
  solve_by_elim
end

variables {γ : Type u₁} [add_comm_group γ]
variables (φ : Π i, β i → γ) [Π i, is_add_group_hom (φ i)]

variables (φ)
def to_group (f : direct_sum ι β) : γ :=
quotient.lift_on f (λ x, x.2.to_finset.sum $ λ i, φ i (x.1 i)) $ λ x y H,
begin
  have H1 : x.2.to_finset ∩ y.2.to_finset ⊆ x.2.to_finset, from finset.inter_subset_left _ _,
  have H2 : x.2.to_finset ∩ y.2.to_finset ⊆ y.2.to_finset, from finset.inter_subset_right _ _,
  refine (finset.sum_subset H1 _).symm.trans ((finset.sum_congr rfl _).trans (finset.sum_subset H2 _)),
  { intros i H1 H2, rw finset.mem_inter at H2, rw H i,
    simp only [multiset.mem_to_finset] at H1 H2,
    rw [(y.3 i).resolve_left (mt (and.intro H1) H2), is_add_group_hom.map_zero (φ i)] },
  { intros i H1, rw H i },
  { intros i H1 H2, rw finset.mem_inter at H2, rw ← H i,
    simp only [multiset.mem_to_finset] at H1 H2,
    rw [(x.3 i).resolve_left (mt (λ H3, and.intro H3 H1) H2), is_add_group_hom.map_zero (φ i)] }
end
variables {φ}

instance to_group.is_add_group_hom : is_add_group_hom (to_group φ) :=
{ map_add := assume f g,
begin
  refine quotient.induction_on f (λ x, _),
  refine quotient.induction_on g (λ y, _),
  change finset.sum _ _ = finset.sum _ _ + finset.sum _ _,
  simp only, conv { to_lhs, congr, skip, funext, rw is_add_hom.map_add (φ i) },
  simp only [finset.sum_add_distrib],
  congr' 1,
  { refine (finset.sum_subset _ _).symm,
    { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inl },
    { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
      rw [(x.3 i).resolve_left H2, is_add_group_hom.map_zero (φ i)] } },
  { refine (finset.sum_subset _ _).symm,
    { intro i, simp only [multiset.mem_to_finset, multiset.mem_add], exact or.inr },
    { intros i H1 H2, simp only [multiset.mem_to_finset, multiset.mem_add] at H2,
      rw [(y.3 i).resolve_left H2, is_add_group_hom.map_zero (φ i)] } }
end }

variables (φ)
@[simp] lemma to_group_zero : to_group φ 0 = 0 :=
is_add_group_hom.map_zero _

@[simp] lemma to_group_add (x y) : to_group φ (x + y) = to_group φ x + to_group φ y :=
is_add_hom.map_add _ x y

@[simp] lemma to_group_neg (x) : to_group φ (-x) = -to_group φ x :=
is_add_group_hom.map_neg _ x

@[simp] lemma to_group_sub (x y) : to_group φ (x - y) = to_group φ x - to_group φ y :=
is_add_group_hom.map_sub _ x y

@[simp] lemma to_group_of (i) (x : β i) : to_group φ (of β i x) = φ i x :=
(add_zero _).trans $ congr_arg (φ i) $ show (if H : i ∈ finset.singleton i then x else 0) = x,
from dif_pos $ finset.mem_singleton_self i

variables (ψ : direct_sum ι β → γ) [is_add_group_hom ψ]

theorem to_group.unique (f : direct_sum ι β) :
  ψ f = @to_group _ _ _ _ _ _ (λ i, ψ ∘ of β i) (λ i, is_add_group_hom.comp (of β i) ψ) f :=
by haveI : ∀ i, is_add_group_hom (ψ ∘ of β i) := (λ _, is_add_group_hom.comp _ _); exact
direct_sum.induction_on f
  (by rw [is_add_group_hom.map_zero ψ, is_add_group_hom.map_zero (to_group (λ i, ψ ∘ of β i))])
  (λ i x, by rw [to_group_of])
  (λ x y ihx ihy, by rw [is_add_hom.map_add ψ, is_add_hom.map_add (to_group (λ i, ψ ∘ of β i)), ihx, ihy])

variables (β)
def set_to_set (S T : set ι) (H : S ⊆ T) :
  direct_sum S (β ∘ subtype.val) → direct_sum T (β ∘ subtype.val) :=
to_group $ λ i, of (β ∘ @subtype.val _ T) ⟨i.1, H i.2⟩
variables {β}

instance (S T : set ι) (H : S ⊆ T) : is_add_group_hom (set_to_set β S T H) :=
to_group.is_add_group_hom

protected def id (M : Type v) [add_comm_group M] : direct_sum punit (λ _, M) ≃ M :=
{ to_fun := direct_sum.to_group (λ _, id),
  inv_fun := of (λ _, M) punit.star,
  left_inv := λ x, direct_sum.induction_on x
    (by rw [to_group_zero, of_zero])
    (λ ⟨⟩ x, by rw [to_group_of]; refl)
    (λ x y ihx ihy, by rw [to_group_add, of_add, ihx, ihy]),
  right_inv := λ x, to_group_of _ _ _ }

instance : has_coe_to_fun (direct_sum ι β) :=
dfinsupp.has_coe_to_fun

end direct_sum
