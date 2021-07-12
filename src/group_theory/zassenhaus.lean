/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import group_theory.subgroup
import group_theory.quotient_group
import data.setoid.basic
import tactic

universes u v w
open_locale classical

namespace subgroup
variables {α : Type u} [group α]

@[to_additive] lemma eq_of_subset_eq (A B : set α) (C : subgroup α) (hA : A ⊆ C) (hB : B ⊆ C)
  (h : C.subtype ⁻¹' A = C.subtype ⁻¹' B) : A = B :=
begin
  rwa [coe_subtype, @subtype.preimage_coe_eq_preimage_coe_iff _ ↑C A B,
    set.inter_eq_self_of_subset_left hA, set.inter_eq_self_of_subset_left hB] at h,
end

@[to_additive] lemma preimage_mul_of_injective
  {X : Type u} [monoid X] {Y : Type v} [monoid Y] (A B : set Y)
  (f : X → Y) [is_mul_hom f] (hf : function.injective f)
  (hA : A ⊆ set.range f) (hB : B ⊆ set.range f) :
  f ⁻¹' (A * B) = f ⁻¹' A * f⁻¹' B :=
begin
  refine set.subset.antisymm _ (set.preimage_mul_preimage_subset f),
  rintros x ⟨a, b, ha, hb, hab⟩,
  rw set.mem_mul,
  rcases set.mem_range.mp (hA ha) with ⟨xa, hxa⟩,
  rcases set.mem_range.mp (hB hb) with ⟨xb, hxb⟩,
  refine ⟨xa, xb, set.mem_preimage.mpr (hxa.symm.subst ha),
    set.mem_preimage.mpr (hxb.symm.subst hb), _⟩,
  apply_fun f, rwa [is_mul_hom.map_mul f, hxa, hxb],
end

/-- Construct the subgroup `H * N`, given that `H` is normal. -/
@[to_additive "Construct the subgroup `H + N`, given that `H` is normal."]
def mul_normal' (H N : subgroup α) [hN : N.normal] : subgroup α :=
{ carrier := (H : set α) * N,
  one_mem' := ⟨1, 1, H.one_mem, N.one_mem, by rw mul_one⟩,
  mul_mem' := λ a b ⟨h, n, hh, hn, ha⟩ ⟨h', n', hh', hn', hb⟩,
    ⟨h * h', h'⁻¹ * n * h' * n',
    H.mul_mem hh hh', N.mul_mem (by simpa using hN.conj_mem _ hn h'⁻¹) hn',
    by simp [← ha, ← hb, mul_assoc]⟩,
  inv_mem' := λ x ⟨h, n, hh, hn, hx⟩,
    ⟨h⁻¹, h * n⁻¹ * h⁻¹, H.inv_mem hh, hN.conj_mem _ (N.inv_mem hn) h,
    by rw [mul_assoc h, inv_mul_cancel_left, ← hx, mul_inv_rev]⟩ }

@[to_additive] lemma normal_subgroup_mul
  {A B C : subgroup α} (hA : A ≤ C) [hN : (A.subgroup_of C).normal] (hB : B ≤ C) :
  ((A ⊔ B : subgroup α) : set α) = A * B :=
begin
  suffices h : ((A ⊔ B).subgroup_of C : set C) = A.subgroup_of C * B.subgroup_of C,
  have key : (C.subtype) ⁻¹' (↑A * ↑B) = (C.subtype) ⁻¹' ↑A * (C.subtype) ⁻¹' ↑B,
  { refine preimage_mul_of_injective ↑A ↑B C.subtype subtype.coe_injective _ _;
    simp only [← monoid_hom.coe_range, subtype_range]; assumption, },
  have hsub : (A : set α) * B ⊆ C,
  { rintro _ ⟨p, q, hp, hq, rfl⟩,
    exact mul_mem _ (hA hp) (hB hq) },
  apply_fun set.image (C.subtype) at h,
  simp only [subgroup_of, coe_comap, ← key] at h,
  simp only [subtype.image_preimage_coe ↑C _, coe_subtype,
    set.inter_eq_self_of_subset_left hsub, inf_of_le_left (sup_le hA hB),
    set.inter_eq_self_of_subset_left (set_like.coe_subset_coe.mpr (sup_le hA hB))] at h,
  exact h,
  simp [subgroup_of_sup A B C hA hB, normal_mul],
end

-- Often times it's hard to write `hK h` directly because Lean seems to be unable to synthesize
-- the type of `hK` even though `H` and `K` are known? It happens below where `mem_of_le` is used.
@[to_additive] lemma mem_of_le {x : α} {H K : subgroup α} (hK : H ≤ K) (h : x ∈ H) : x ∈ K := hK h

@[to_additive] lemma mem_sup_iff {H K : subgroup α} {g : α} (h : ↑(H ⊔ K) = (H : set α) * K) :
  g ∈ H ⊔ K ↔ ∃ x y, x ∈ H ∧ y ∈ K ∧ x * y = g :=
set.ext_iff.1 h g


@[to_additive] lemma mem_sup_iff' {H K : subgroup α} {g : α} (h : ↑(H ⊔ K) = (H : set α) * K) :
  g ∈ H ⊔ K ↔ ∃ (x : H) (y : K), (x * y : α) = g :=
(mem_sup_iff h).trans
  ⟨λ ⟨a, b, ha, hb, h⟩, ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩,
  λ ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩, ⟨a, b, ha, hb, h⟩⟩


end subgroup

namespace subgroup
variables {α : Type u} [group α]

open quotient_group
section Zassenhaus

@[to_additive] lemma Zassenhaus_subgroup {A' A B' B : subgroup α} (hA : A' ≤ A) (hB : B' ≤ B) :
  ((A' ⊓ B) ⊔ (A ⊓ B') ≤ A ⊓ B) :=
sup_le (inf_le_inf hA (le_refl _)) (inf_le_inf (le_refl _) hB)


instance Zassenhaus
  {A' A B' B : subgroup α} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
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

/-- bruh  -/
@[derive inhabited] def Zassenhaus_quot (A' A B' B : subgroup α) :=
quotient_group.quotient $ ((A' ⊓ B) ⊔ (A ⊓ B')).subgroup_of (A ⊓ B)

instance Zassenhaus_group
  {A' A B' B : subgroup α} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  group (Zassenhaus_quot A' A B' B) :=
begin
  dsimp [Zassenhaus_quot],
  haveI := @subgroup.Zassenhaus _ _ A' A B' B hA hB,
  apply_instance,
end

lemma Zassenhaus_aux
  {A' A : subgroup α} (B : subgroup α) (hA : A' ≤ A) [hAN : (A'.subgroup_of A).normal] :
  ↑(A' ⊔ A ⊓ B) = (A' : set α) * (A ⊓ B : subgroup α) :=
normal_subgroup_mul hA (inf_le_of_left_le (le_refl A))

lemma Zassenhaus_quot_aux {A' A B' B : subgroup α} (hA : A' ≤ A) (hB : B' ≤ B)
  [hAN : (A'.subgroup_of A).normal] :
  ↑((A' ⊓ B) ⊔ (A ⊓ B')) = (A : set α) ⊓ B ⊓ (A' * B') :=
begin
  have : ↑((A' ⊓ B) ⊔ (A ⊓ B')) = ((A' : set α) ⊓ B) * (A ⊓ B'),
  { haveI : ((A' ⊓ B).subgroup_of (A ⊓ B)).normal :=
    by { have := inf_subgroup_of_inf_normal_of_right B A' A hA,
      rw inf_comm, rwa @inf_comm _ _ A' B },
    refine normal_subgroup_mul (inf_le_inf hA (le_refl B)) (inf_le_inf (le_refl A) hB), },
  rw this,
  clear this,
  have := mul_inf_assoc (A' ⊓ B) B' A _,
  rw @inf_comm _ _ _ A at this,
  rw @inf_comm _ _ (↑(A' ⊓ B) * ↑B') _ at this,
  have bleh : ↑(A' ⊓ B) * ↑B' = (B : set α) ⊓ (A' * B'),
  { have yes := inf_mul_assoc B A' B' hB, rwa inf_comm at yes },
  rw bleh at this,
  rw ← inf_assoc at this,
  convert this,
  exact inf_le_of_left_le hA,
end

lemma inv_mul_eq_mul_inv {u v a b : α} (h : u * v = a * b) : a⁻¹ * u = b * v⁻¹ :=
  inv_mul_eq_of_eq_mul (mul_assoc a b v⁻¹ ▸ eq_mul_inv_of_mul_eq h)


/-- bruh -/
noncomputable def Zassenhaus_fun_aux {A' A : subgroup α} (B' B : subgroup α) (hA : A' ≤ A)
  [hAN : (A'.subgroup_of A).normal] (x : A' ⊔ A ⊓ B) : Zassenhaus_quot A' A B' B :=
quotient.mk' ⟨_, ((mem_sup_iff (Zassenhaus_aux B hA)).mp x.2).some_spec.some_spec.2.1⟩

theorem Zassenhaus_fun_aux_app {A' A B' B : subgroup α} (hA : A' ≤ A)
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
  rw inv_mul_eq_mul_inv huv at this,
  haveI := inf_subgroup_of_inf_normal_of_left B hA,
  refine subgroup_normal.mem_comm (inf_le_inf hA (le_refl B)) (inv_mem (A ⊓ B) hv) _,
  refine mem_inf.mpr ⟨this, mul_mem _ (mem_inf.mp hx).2 (inv_mem _ (mem_inf.mp hv).2)⟩,
end

theorem Zassenhaus_fun_aux_app' {A' A B' B : subgroup α} (hA : A' ≤ A)
  [hAN : (A'.subgroup_of A).normal] (a : A') (x : A ⊓ B) (b : A' ⊔ A ⊓ B)
  (e : (a * x : α) = b.1) :
  Zassenhaus_fun_aux B' B hA b = quotient.mk' x :=
begin
  have h : (a * x : α) ∈ A' ⊔ A ⊓ B, { rw e, exact b.2 },
  convert ← Zassenhaus_fun_aux_app hA _ _ h, ext, exact e,
end

/-- bruh -/
noncomputable def Zassenhaus_fun (A' A B' B : subgroup α) [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
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

lemma Zassenhaus_fun_ker {A' A B' B : subgroup α} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  (Zassenhaus_fun A' A B' B).ker = (A' ⊔ A ⊓ B').subgroup_of (A' ⊔ A ⊓ B) :=
begin
  ext ⟨x, hx⟩,
  obtain ⟨a, b, rfl⟩ := (mem_sup_iff' (Zassenhaus_aux B hA.out)).1 hx,
  change (Zassenhaus_fun A' A B' B) ⟨↑a * ↑b, hx⟩ = quotient.mk' 1 ↔ _,
  simp only [Zassenhaus_fun, monoid_hom.coe_mk, Zassenhaus_fun_aux_app' hA.out _ _ ⟨_, hx⟩ rfl,
    quotient.eq'],
  change b⁻¹ * 1 ∈ ((A' ⊓ B ⊔ A ⊓ B').subgroup_of (A ⊓ B)) ↔ _,
  simp only [mem_subgroup_of, coe_mk, mem_inf, coe_subtype, mul_one, coe_inv, inv_mem_iff],
  refine ⟨λ h, _, λ hx', _⟩,
  { letI := inf_subgroup_of_inf_normal_of_left B hA.out,
    have p := normal_subgroup_mul (inf_le_inf hA.out (le_refl B)) (inf_le_inf (le_refl A) hB.out),
    obtain ⟨x, y, hmm⟩ := (mem_sup_iff' p).mp h, rw ← hmm,
    refine (mem_sup_iff' (Zassenhaus_aux B' hA.out)).mpr ⟨a * ⟨x, _⟩, y, _⟩,
    exact mem_of_le (inf_le_left) x.2,
    simp [mul_assoc] },
  obtain ⟨x, y, h⟩ := (mem_sup_iff' (Zassenhaus_aux B' hA.out)).1 hx',
  have : (b : α) * y⁻¹ ∈ A' ⊓ B ⊔ A ⊓ B',
  { refine mem_of_le le_sup_left _,
    have := mul_mem A' (inv_mem A' a.2) x.2,
    simp only [inv_mul_eq_mul_inv h, subtype.val_eq_coe] at this,
    have bval := (mem_inf.mp y.2).2, rw subtype.val_eq_coe at bval,
    refine mem_inf.mpr ⟨this, mul_mem _ (mem_inf.mp b.2).2 (mem_of_le hB.out (inv_mem _ bval))⟩ },
  have done : (b : α) * y⁻¹ * y ∈ A' ⊓ B ⊔ A ⊓ B' := mul_mem _ this (mem_of_le le_sup_right y.2),
  rwa [inv_mul_cancel_right] at done,
end

@[instance] lemma Zassenhaus_normal
  {A' A B' B : subgroup α} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  ((A' ⊔ A ⊓ B').subgroup_of (A' ⊔ A ⊓ B)).normal :=
by { rw ← Zassenhaus_fun_ker, exact monoid_hom.normal_ker _, }

lemma Zassenhaus_fun_surjective {A' A B' B : subgroup α} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
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

/-- bruh -/
def Zassenhaus' {A' A B' B : subgroup α} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  Zassenhaus_quot A' A B' B ≃* Zassenhaus_quot B' B A' A :=
equiv_quotient_subgroup_of_of_eq (by { rwa [inf_comm, @inf_comm _ _ A B', sup_comm] } ) (inf_comm)

/-- bruh  -/
noncomputable def Zassenhaus''
  {A' A B' B : subgroup α} [hA : fact (A' ≤ A)] [hB : fact (B' ≤ B)]
  [hAN : (A'.subgroup_of A).normal] [hBN : (B'.subgroup_of B).normal] :
  quotient ((A' ⊔ A ⊓ B').subgroup_of (A' ⊔ A ⊓ B)) ≃*
    quotient ((B' ⊔ B ⊓ A').subgroup_of (B' ⊔ B ⊓ A)) :=
(((equiv_quotient_of_eq Zassenhaus_fun_ker).symm.trans
  (quotient_ker_equiv_of_surjective (Zassenhaus_fun A' A B' B)
  Zassenhaus_fun_surjective)).trans Zassenhaus').trans
  ((equiv_quotient_of_eq Zassenhaus_fun_ker).symm.trans
  (quotient_ker_equiv_of_surjective (Zassenhaus_fun B' B A' A)
  (Zassenhaus_fun_surjective))).symm

end Zassenhaus

end subgroup
#lint
