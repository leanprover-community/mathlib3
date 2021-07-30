/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/

import group_theory.quotient_group

/-!
# The Zassenhaus (Butterfly) Lemma

This files develops the basic theory of quotients of groups by normal subgroups. In particular it
proves Noether's first and second isomorphism theorems.

## Main statements

* `Zassenhaus`: The main theorem `(A' ⊔ A ⊓ B') / (A' ⊔ A ⊓ B) ≃* (B' ⊔ B ⊓ A') / (B' ⊔ B ⊓ A)`

## Implementation Details

For instances `normal_Zassenhaus_subgroup`, `Zassenhaus_group`, etc,
the use of hypotheses `[hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]` is a hacky workaround.
If instead we use `(hA : A ≤ A')` or `{hA : A ≤ A'}`, type-class inference
seems to have problems synthesizing these instances.

There should be a better way to do this but the author doesn't know how.

## Tags

isomorphism theorems, Zassenhaus Lemma, Butterfly Lemma
-/

universes u v
open subgroup

namespace quotient_group
variables {G : Type u} [group G]

@[to_additive] lemma Zassenhaus_subgroup {A' A B' B : subgroup G} (hA : A' ≤ A) (hB : B' ≤ B) :
  ((A' ⊓ B) ⊔ (A ⊓ B') ≤ A ⊓ B) :=
sup_le (inf_le_inf hA (le_refl _)) (inf_le_inf (le_refl _) hB)

instance normal_Zassenhaus_subgroup
  {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  (((A' ⊓ B) ⊔ (A ⊓ B')).subgroup_of (A ⊓ B)).normal :=
begin
  haveI h₁ : ((A' ⊓ B).subgroup_of (A ⊓ B)).normal :=
  by { have := inf_subgroup_of_inf_normal_of_right B A' A hA.out,
    rw inf_comm, rwa @inf_comm _ _ A' B },
  haveI h₂ : ((A ⊓ B').subgroup_of (A ⊓ B)).normal :=
  by { have := inf_subgroup_of_inf_normal_of_right A B' B hB.out,
    rw inf_comm, rwa @inf_comm _ _ B A },
  rw subgroup_of_sup,
  { exact subgroup.sup_normal ((A' ⊓ B).subgroup_of (A ⊓ B)) ((A ⊓ B').subgroup_of (A ⊓ B)) },
  { exact inf_le_inf hA.out (le_refl _) },
  { exact inf_le_inf (le_refl _) hB.out },
end

/--
Construct the quotient `(A ⊓ B) / ((A' ⊓ B) ⊔ (A ⊓ B'))`.
We delay the hypotheses `A' ≤ A` and `B' ≤ B` as much as possible.
-/
@[derive inhabited] def Zassenhaus_quot (A' A B' B : subgroup G) :=
quotient_group.quotient $ ((A' ⊓ B) ⊔ (A ⊓ B')).subgroup_of (A ⊓ B)

instance Zassenhaus_group
  {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  group (Zassenhaus_quot A' A B' B) :=
begin
  dsimp [Zassenhaus_quot],
  haveI := @quotient_group.normal_Zassenhaus_subgroup _ _ A' A B' B hA hB,
  apply_instance,
end

lemma Zassenhaus_aux
  {A' A : subgroup G} (B : subgroup G) (hA : A' ≤ A) [hAN : (A'.subgroup_of A).normal] :
  ↑(A' ⊔ A ⊓ B) = (A' : set G) * (A ⊓ B : subgroup G) :=
coe_sup_of_normal_left hA (inf_le_of_left_le (le_refl A))

lemma Zassenhaus_quot_aux {A' A B' B : subgroup G} (hA : A' ≤ A) (hB : B' ≤ B)
  [hAN : (A'.subgroup_of A).normal] :
  ↑((A' ⊓ B) ⊔ (A ⊓ B')) = (A : set G) ⊓ B ⊓ (A' * B') :=
begin
  calc ↑((A' ⊓ B) ⊔ (A ⊓ B'))
      = ((A' : set G) ⊓ B) * (A ⊓ B') : _
  ... = ↑(A' ⊓ B) * ↑(B' ⊓ A) : by simp only [inf_comm, coe_inf, set.inf_eq_inter]
  ... = ↑(A' ⊓ B) * ↑B' ⊓ ↑A : mul_inf_assoc (A' ⊓ B) B' A (inf_le_of_left_le hA)
  ... = ↑(B ⊓ A') * ↑B' ⊓ ↑A : by { congr' 2, rw inf_comm }
  ... = ↑A ⊓ ↑B ⊓ (↑A' * ↑B') : by rw [inf_mul_assoc B A' B' hB, inf_comm, inf_assoc],
  haveI : ((A' ⊓ B).subgroup_of (A ⊓ B)).normal :=
  by { have := inf_subgroup_of_inf_normal_of_right B A' A hA,
    rw inf_comm, rwa @inf_comm _ _ A' B },
  exact coe_sup_of_normal_left (inf_le_inf hA le_rfl) (inf_le_inf le_rfl hB)
end

/--
The map `A' ⊔ A ⊓ B → (A ⊓ B) / ((A' ⊓ B) ⊔ (A ⊓ B'))`.
We prove that this map is in fact a group homomorphism with kernel `A' ⊔ A ⊓ B'`
in `Zassenhaus_fun` and `Zassenhaus_fun_ker`.
-/
noncomputable def Zassenhaus_fun_aux {A' A : subgroup G} (B' B : subgroup G) (hA : A' ≤ A)
  [hAN : (A'.subgroup_of A).normal] (x : A' ⊔ A ⊓ B) : Zassenhaus_quot A' A B' B :=
quotient.mk' ⟨_, ((mem_sup_iff (Zassenhaus_aux B hA)).mp x.2).some_spec.some_spec.2.1⟩

theorem Zassenhaus_fun_aux_app {A' A B' B : subgroup G} (hA : A' ≤ A)
  [hAN : (A'.subgroup_of A).normal] (a : A') (x : A ⊓ B) (h) :
  Zassenhaus_fun_aux B' B hA ⟨a * x, h⟩ = quotient.mk' x :=
begin
  apply quotient.sound',
  have H := (mem_sup_iff (Zassenhaus_aux B hA)).mp h,
  let u := H.some, let v := H.some_spec.some,
  cases a with a ha, cases x with x hx,
  obtain ⟨hu : u ∈ A', hv : v ∈ A ⊓ B, huv : u * v = a * x⟩ := H.some_spec.some_spec,
  refine mem_subgroup_of.2 (mem_of_le le_sup_left (_ : v⁻¹ * x ∈ A' ⊓ B)),
  have := mul_mem A' (inv_mem A' ha) hu,
  have inv_mul_eq_mul_inv : a⁻¹ * u = x * v⁻¹ :=
    inv_mul_eq_of_eq_mul (mul_assoc a x v⁻¹ ▸ eq_mul_inv_of_mul_eq huv),
  rw inv_mul_eq_mul_inv at this,
  haveI := inf_subgroup_of_inf_normal_of_left B hA,
  refine subgroup_normal.mem_comm (inf_le_inf hA (le_refl B)) (inv_mem (A ⊓ B) hv) _,
  refine mem_inf.mpr ⟨this, mul_mem _ (mem_inf.mp hx).2 (inv_mem _ (mem_inf.mp hv).2)⟩,
end

theorem Zassenhaus_fun_aux_app' {A' A B' B : subgroup G} (hA : A' ≤ A)
  [hAN : (A'.subgroup_of A).normal] (a : A') (x : A ⊓ B) (b : A' ⊔ A ⊓ B)
  (e : (a * x : G) = b.1) :
  Zassenhaus_fun_aux B' B hA b = quotient.mk' x :=
begin
  have h : (a * x : G) ∈ A' ⊔ A ⊓ B, { rw e, exact b.2 },
  convert ← Zassenhaus_fun_aux_app hA _ _ h, ext, exact e,
end

/--
The intermediary group homomorphism `A' ⊔ A ⊓ B →* (A ⊓ B) / ((A' ⊓ B) ⊔ (A ⊓ B'))`
that provides "one side" of the butterfly diagram. Exploiting the symmtery between
`A'/A` and `B'/B` and glueing the respective two sides together will give us the
full Zassenhaus lemma.
-/
noncomputable def Zassenhaus_fun (A' A B' B : subgroup G) [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  ↥(A' ⊔ A ⊓ B) →* Zassenhaus_quot A' A B' B :=
{ to_fun := Zassenhaus_fun_aux B' B hA.out,
  map_one' := Zassenhaus_fun_aux_app' _ 1 _ _ (by simp; refl),
  map_mul' := λ ⟨a, ha⟩ ⟨b, hb⟩,
  begin
    clear_,
    obtain ⟨a₁, a₂, rfl⟩ := (mem_sup_iff' (Zassenhaus_aux B hA.out)).1 ha,
    obtain ⟨b₁, b₂, rfl⟩ := (mem_sup_iff' (Zassenhaus_aux B hA.out)).1 hb,
    simp only [Zassenhaus_fun_aux_app],
    refine Zassenhaus_fun_aux_app' hA.out ⟨a₁ * (a₂ * b₁ * a₂⁻¹), _⟩ _ _ _,
    { rw normal_subgroup_of_iff hA.out at hAN,
      exact mul_mem A' a₁.2 (hAN ↑b₁ ↑a₂ b₁.2 (mem_inf.mp a₂.2).1) },
    simp [mul_assoc],
  end }

lemma Zassenhaus_fun_ker {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  (Zassenhaus_fun A' A B' B).ker = (A' ⊔ A ⊓ B').subgroup_of (A' ⊔ A ⊓ B) :=
begin
  ext ⟨x, hx⟩,
  obtain ⟨a, b, rfl⟩ := (mem_sup_iff' (Zassenhaus_aux B hA.out)).1 hx,
  change (Zassenhaus_fun A' A B' B) ⟨↑a * ↑b, hx⟩ = quotient.mk' 1 ↔ _,
  simp only [Zassenhaus_fun, monoid_hom.coe_mk, Zassenhaus_fun_aux_app' hA.out _ _ ⟨_, hx⟩ rfl,
    quotient.eq'],
  change b⁻¹ * 1 ∈ ((A' ⊓ B ⊔ A ⊓ B').subgroup_of (A ⊓ B)) ↔ _,
  simp only [mem_subgroup_of, subgroup.coe_mk, mem_inf, subgroup.coe_subtype,
    mul_one, coe_inv, inv_mem_iff],
  refine ⟨λ h, _, λ hx', _⟩,
  { letI := inf_subgroup_of_inf_normal_of_left B hA.out,
    have p :=
      coe_sup_of_normal_left (inf_le_inf hA.out (le_refl B)) (inf_le_inf (le_refl A) hB.out),
    obtain ⟨x, y, hmm⟩ := (mem_sup_iff' p).mp h, rw ← hmm,
    refine (mem_sup_iff' (Zassenhaus_aux B' hA.out)).mpr ⟨a * ⟨x, _⟩, y, _⟩,
    exact mem_of_le (inf_le_left) x.2,
    simp [mul_assoc] },
  obtain ⟨x, y, h⟩ := (mem_sup_iff' (Zassenhaus_aux B' hA.out)).1 hx',
  have : (b : G) * y⁻¹ ∈ A' ⊓ B ⊔ A ⊓ B',
  { refine mem_of_le le_sup_left _,
    have := mul_mem A' (inv_mem A' a.2) x.2,
    have inv_mul_eq_mul_inv : (a : G)⁻¹ * x = b * y⁻¹ :=
      inv_mul_eq_of_eq_mul (mul_assoc (a : G) b y⁻¹ ▸ eq_mul_inv_of_mul_eq h),
    simp only [inv_mul_eq_mul_inv, subtype.val_eq_coe] at this,
    have bval := (mem_inf.mp y.2).2, rw subtype.val_eq_coe at bval,
    refine mem_inf.mpr ⟨this, mul_mem _ (mem_inf.mp b.2).2 (mem_of_le hB.out (inv_mem _ bval))⟩ },
  have done : (b : G) * y⁻¹ * y ∈ A' ⊓ B ⊔ A ⊓ B' := mul_mem _ this (mem_of_le le_sup_right y.2),
  rwa [inv_mul_cancel_right] at done,
end

@[instance] lemma Zassenhaus_normal
  {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  ((A' ⊔ A ⊓ B').subgroup_of (A' ⊔ A ⊓ B)).normal :=
by { rw ← Zassenhaus_fun_ker, exact monoid_hom.normal_ker _, }

lemma Zassenhaus_fun_surjective {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  function.surjective (Zassenhaus_fun A' A B' B) := λ x, x.induction_on' $
begin
  rintro ⟨y, (hy : y ∈ ↑(A ⊓ B))⟩,
  have hy' := (mem_sup_iff' (Zassenhaus_aux B hA.out)).mpr ⟨1, ⟨y, hy⟩, one_mul _⟩,
  use ⟨y, hy'⟩,
  rw [subtype.coe_mk, ← one_mul y, ← subtype.coe_mk y hy] at hy',
  conv_lhs { find y { rw ← one_mul y, rw ← subtype.coe_mk y hy, } },
  simp only [Zassenhaus_fun, monoid_hom.coe_mk],
  exact Zassenhaus_fun_aux_app hA.out 1 ⟨y, hy⟩ hy',
end

/--
Technical lemma that proves `(A ⊓ B) / ((A' ⊓ B) ⊔ (A ⊓ B')) ≃* (B ⊓ A) / ((B' ⊓ A) ⊔ (B ⊓ A'))`,
which we must provide explictly due to the complex types of the LHS and RHS,
-/
def Zassenhaus_symm_equiv {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  Zassenhaus_quot A' A B' B ≃* Zassenhaus_quot B' B A' A :=
equiv_quotient_subgroup_of_of_eq (by { rwa [inf_comm, @inf_comm _ _ A B', sup_comm] } ) (inf_comm)

/--
**The Zassenhaus Lemma** (or the Butterfly Lemma) for groups:
`(A' ⊔ A ⊓ B') / (A' ⊔ A ⊓ B) ≃* (B' ⊔ B ⊓ A') / (B' ⊔ B ⊓ A)`
-/
noncomputable def Zassenhaus
  {A' A B' B : subgroup G} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  quotient ((A' ⊔ A ⊓ B').subgroup_of (A' ⊔ A ⊓ B)) ≃*
    quotient ((B' ⊔ B ⊓ A').subgroup_of (B' ⊔ B ⊓ A)) :=
(((equiv_quotient_of_eq Zassenhaus_fun_ker).symm.trans
  (quotient_ker_equiv_of_surjective (Zassenhaus_fun A' A B' B)
  Zassenhaus_fun_surjective)).trans Zassenhaus_symm_equiv).trans
  ((equiv_quotient_of_eq Zassenhaus_fun_ker).symm.trans
  (quotient_ker_equiv_of_surjective (Zassenhaus_fun B' B A' A)
  (Zassenhaus_fun_surjective))).symm

end quotient_group
