/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import group_theory.subgroup
import group_theory.quotient_group
import data.setoid.basic

universes u v w
open_locale classical
variables (α : Type u) [group α]

namespace subgroup
variables {α} [group α]

/- View `H` as a subgroup of `K`. -/
def of (H : subgroup α) (K : subgroup α) : subgroup K := H.comap K.subtype

lemma of_carrier (H : subgroup α) (K : subgroup α) : (H.of K).carrier = K.subtype ⁻¹' H := rfl

lemma mem_of (H : subgroup α) (K : subgroup α) (h : K) : h ∈ H.of K ↔ K.subtype h ∈ H ⊓ K :=
begin
  split,
  intro hh,
  simp only [set_like.coe_mem, and_true, mem_inf, coe_subtype],
  rw ← mem_carrier at hh,
  rw of_carrier at hh,
  simp only [set.mem_preimage, set_like.mem_coe, coe_subtype] at hh,
  assumption,
  simp only [set_like.coe_mem, and_true, mem_inf, coe_subtype],
  intro hh,
  rw ← mem_carrier,
  rw of_carrier,
  simpa,
end

lemma prod_of_prod_normal {G₁ : Type u} [group G₁] {G₂ : Type v} [group G₂]
  {H₁ K₁ : subgroup G₁} {H₂ K₂ : subgroup G₂}
  [h₁ : (H₁.of K₁).normal] [h₂ : (H₂.of K₂).normal] :
  ((H₁.prod H₂).of (K₁.prod K₂)).normal :=
{ conj_mem := λ g hgHK n,
  begin
    cases n with n hn',
    cases g with g hg',
    have hn := mem_prod.mp hn',
    have hg := mem_prod.mp hg',
    rw mem_of at hgHK,
    simp at hgHK,
    replace hgHK := hgHK.1,
    rw mem_of,
    simp,
    have this2 : K₁.subtype ⟨g.fst, (mem_prod.mp hg').1⟩ ∈ H₁,
      { simp only [coe_mk, coe_subtype], exact (mem_prod.mp hgHK).1, },
    have := h₁.conj_mem ⟨g.fst, (mem_prod.mp hg').1⟩ this2 ⟨n.fst, (mem_prod.mp hn').1⟩,
    have this3 : K₂.subtype ⟨g.snd, (mem_prod.mp hg').2⟩ ∈ H₂,
     { simp [coe_mk, coe_subtype], exact (mem_prod.mp hgHK).2, },
    have this4 := h₂.conj_mem ⟨g.snd, (mem_prod.mp hg').2⟩ this3 ⟨n.snd, (mem_prod.mp hn').2⟩,
    rw mem_of at this,
    rw mem_of at this4,
    simp only [coe_mul, coe_mk, mem_inf, coe_subtype, coe_inv] at this,
    simp only [coe_mul, coe_mk, mem_inf, coe_subtype, coe_inv] at this4,
    refine ⟨mem_prod.mpr ⟨_, _⟩, mem_prod.mpr ⟨_, _⟩⟩,
    simp only [prod.fst_mul, prod.fst_inv], exact this.1,
    simp only [prod.snd_mul, prod.snd_inv], exact this4.1,
    simp only [prod.fst_mul, prod.fst_inv], exact this.2,
    simp only [prod.snd_mul, prod.snd_inv], exact this4.2,
  end }

instance prod_normal {G : Type u} [group G] {H : Type v} [group H]
  (N : subgroup G) (K : subgroup H) [hN : N.normal] [hK : K.normal] :
  (N.prod K).normal :=
{ conj_mem :=
  begin
    intros n hg g,
    rw subgroup.mem_prod,
    split,
    exact hN.conj_mem n.fst (subgroup.mem_prod.mp hg).1 g.fst,
    exact hK.conj_mem n.snd (subgroup.mem_prod.mp hg).2 g.snd,
  end }

lemma comap_bot (N : Type v) [group N] (f : α →* N) : (⊥ : subgroup N).comap f = f.ker := rfl

lemma subtype_injective {G : Type u} [group G] (H : subgroup G) : function.injective H.subtype :=
begin
  unfold function.injective,
  intros a b, simp,
end

lemma normal_of_def (H K : subgroup α) (hHK : H ≤ K) :
  (H.of K).normal ↔ ∀ h k, h ∈ H → k ∈ K → k * h * k⁻¹ ∈ H :=
⟨λ hN h k hH hK,
  begin
    have hmemK := set.mem_of_subset_of_mem hHK hH,
    have hof : (⟨h, hmemK⟩ : K) ∈ H.of K, { simp [mem_of], exact ⟨hH, hmemK⟩ },
    have := hN.conj_mem ⟨h, hmemK⟩ hof ⟨k, hK⟩,
    simp only [mem_of, coe_mul, coe_mk, mem_inf, coe_subtype, coe_inv] at this,
    exact this.1,
  end,
  λ hN, { conj_mem := λ h hm k,
  begin
    simp only [mem_of, set_like.coe_mem, and_true, mem_inf, coe_subtype, coe_mul, coe_inv] at *,
    exact ⟨hN h.1 k.1 hm k.2, mem_carrier.mp (set.mem_of_subset_of_mem hHK (hN h.1 k.1 hm k.2))⟩,
  end }⟩

lemma inf_normal_inf (A B' B : subgroup α) (hB : B' ≤ B) [hN : (B'.of B).normal] :
  ((A ⊓ B').of (A ⊓ B)).normal :=
{ conj_mem := λ n hn g,
  begin
    have h := hN.conj_mem,
    simp only [mem_of, coe_mul, mem_inf, coe_subtype, coe_inv] at *,
    have := h ⟨n.val, (mem_inf.mp n.2).2⟩ ⟨hn.1.2, hn.2.2⟩ ⟨g.val, (mem_inf.mp g.2).2⟩,
    refine ⟨⟨_, this.1⟩, ⟨_, this.2⟩⟩,
    exact mul_mem A (mul_mem A (mem_inf.1 g.2).1 (mem_inf.1 n.2).1) (inv_mem A (mem_inf.1 g.2).1),
    exact mul_mem A (mul_mem A (mem_inf.1 g.2).1 (mem_inf.1 n.2).1) (inv_mem A (mem_inf.1 g.2).1),
  end }

instance normal_sup_normal (H K : subgroup α) [hH : H.normal] [hK : K.normal] : (H ⊔ K).normal :=
{ conj_mem := λ n hmem g,
  begin
    change n ∈ ↑(H ⊔ K) at hmem,
    change g * n * g⁻¹ ∈ ↑(H ⊔ K),
    rw normal_mul at *,
    rw set.mem_mul at *,
    rcases hmem with ⟨h, k, hh, hk, hhk⟩,
    refine ⟨g * h * g⁻¹, g * k * g⁻¹, hH.conj_mem h hh g, hK.conj_mem k hk g, _⟩,
    rw ← hhk,
    sorry -- no abel/ring?
  end }

instance normal_inf_normal (H K : subgroup α) [hH : H.normal] [hK : K.normal] : (H ⊓ K).normal :=
{ conj_mem := λ n hmem g,
  begin
    rw mem_inf at *,
    exact ⟨hH.conj_mem n hmem.1 g, hK.conj_mem n hmem.2 g⟩,
  end }

lemma sup_normal_sup (A B' B : subgroup α) (hB : B' ≤ B) [hN : (B'.of B).normal] [hA : A.normal] :
  ((A ⊔ B').of (A ⊔ B)).normal :=
{ conj_mem := λ n hmem g,
  begin
    have h := hN.conj_mem,
    simp only [mem_of, coe_mul, mem_inf, coe_subtype, coe_inv] at *,
    change ↑g * ↑n * (↑g)⁻¹ ∈ ↑(A ⊔ B') ∧ ↑g * ↑n * (↑g)⁻¹ ∈ ↑(A ⊔ B),
    have := hmem.1,
    change ↑n ∈ ↑(A ⊔ B') at this,
    rcases g with ⟨g, hg⟩,
    change g ∈ ↑(A ⊔ B) at hg,
    rw [normal_mul, normal_mul] at *,
    rw [set.mem_mul, set.mem_mul] at *,

    rcases set.mem_mul.mp this with ⟨x₁, y₁, hx₁, hy₁, hxy₁⟩,
    rcases set.mem_mul.mp hg with ⟨x₂, y₂, hx₂, hy₂, hxy₂⟩,
    clear' this hg,
    sorry -- this is not true?
  end }

lemma map_inf {G : Type u} [group G] {N : Type v} [group N]
  (H K : subgroup G) (f : G →* N) :
  map f (H ⊓ K) ≤ map f H ⊓ map f K :=
le_inf (map_mono inf_le_left) (map_mono inf_le_right)

lemma map_inf_eq {G : Type u} [group G] {N : Type v} [group N]
  (H K : subgroup G) (f : G →* N) (hf : function.injective f):
  map f (H ⊓ K) = map f H ⊓ map f K :=
begin
  rw ← set_like.coe_set_eq,
  simp [set.image_inter hf],
end

lemma eq_of_map_eq_le_ker {G : Type u} [group G] {N : Type v} [group N]
  (H K : subgroup G) (f : G →* N) (hf : map f H = map f K) (hH : f.ker ≤ H) (hK : f.ker ≤ K) :
  H = K :=
begin
  apply_fun comap f at hf,
  rwa [comap_map_eq, comap_map_eq, sup_of_le_left hH, sup_of_le_left hK] at hf,
end

lemma comap_sup {G : Type u} [group G] {N : Type v} [group N]
  (H K : subgroup N) (f : G →* N) :
  comap f H ⊔ comap f K ≤ comap f (H ⊔ K) :=
sup_le (comap_mono le_sup_left) (comap_mono le_sup_right)

lemma comap_sup_eq {G : Type u} [group G] {N : Type v} [group N]
  (H K : subgroup N) (f : G →* N) (hf : function.surjective f):
  comap f H ⊔ comap f K = comap f (H ⊔ K) :=
begin
  have : map f (comap f H ⊔ comap f K) = map f (comap f (H ⊔ K)),
  { simp [subgroup.map_comap_eq, map_sup, f.range_top_of_surjective hf], },
  apply eq_of_map_eq_le_ker (comap f H ⊔ comap f K) (comap f (H ⊔ K)) f this,
  { calc f.ker ≤ comap f H : ker_le_comap f _
           ... ≤ comap f H ⊔ comap f K : le_sup_left, },
  exact ker_le_comap _ _,
end

lemma subtype_range {G : Type u} [group G] (H : subgroup G) : H.subtype.range = H :=
begin
  rw monoid_hom.range_eq_map,
  ext,
  refine ⟨λ h, _, λ h, _⟩,
  rcases mem_map.mp h with ⟨y, hy, heq⟩,
  rw coe_subtype at heq,
  have : ↑y ∈ H := y.2,
  rwa heq at this,
  rw mem_map,
  refine ⟨⟨x, h⟩, mem_top _, by simp⟩,
end

lemma sup_of (A A' B : subgroup α) (hA : A ≤ B) (hA' : A' ≤ B) :
  (A ⊔ A').of B = A.of B ⊔ A'.of B :=
begin
  have hAA' := sup_le hA hA',
  simp only [of],
  refine eq_of_map_eq_le_ker (comap B.subtype (A ⊔ A')) (comap B.subtype A ⊔ comap B.subtype A')
    B.subtype _ (ker_le_comap _ _) (le_trans (ker_le_comap B.subtype _) le_sup_left),
  { simp only [map_comap_eq, map_sup, subtype_range],
    rw [inf_of_le_right hAA', inf_of_le_right hA', inf_of_le_right hA] },
end

lemma mem_mul {G : Type u} [group G] {H K : subgroup G} {g : G} (h : ↑(H ⊔ K) = (H : set G) * K) :
  g ∈ H ⊔ K ↔ ∃ x y, x ∈ H ∧ y ∈ K ∧ x * y = g :=
begin
  refine ⟨λ (hg : g ∈ ↑(H ⊔ K)), _, λ hg,  (_ : g ∈ ↑(H ⊔ K))⟩,
  rwa [h, set.mem_mul] at hg,
  rwa [h, set.mem_mul],
end

lemma Zassenhaus_subgroup {A' A B' B : subgroup α} (hA : A' ≤ A) (hB : B' ≤ B)
  : ((A' ⊓ B) ⊔ (A ⊓ B') ≤ A ⊓ B) :=
sup_le (inf_le_inf hA (le_refl _)) (inf_le_inf (le_refl _) hB)


instance Zassenhaus1 {A' A B' B : subgroup α} (hA : A' ≤ A) (hB : B' ≤ B)
  [hAN : (A'.of A).normal] [hBN : (B'.of B).normal] : (((A' ⊓ B) ⊔ (A ⊓ B')).of (A ⊓ B)).normal :=
begin
  haveI h₁ : ((A' ⊓ B).of (A ⊓ B)).normal :=
  by { have := inf_normal_inf B A' A hA, rw inf_comm, rwa @inf_comm _ _ A' B },
  haveI h₂ : ((A ⊓ B').of (A ⊓ B)).normal :=
  by { have := inf_normal_inf A B' B hB, rw inf_comm, rwa @inf_comm _ _ B A },
  rw sup_of,
  { exact subgroup.normal_sup_normal ((A' ⊓ B).of (A ⊓ B)) ((A ⊓ B').of (A ⊓ B)) },
  { exact inf_le_inf hA (le_refl _) },
  { exact inf_le_inf (le_refl _) hB },
end

lemma eq_of_subset_eq (A B : set α) (C : subgroup α) (hA : A ⊆ C) (hB : B ⊆ C)
  (h : C.subtype ⁻¹' A = C.subtype ⁻¹' B) : A = B :=
begin
  apply_fun set.image (coe : C → α) at h,
  simp only [subtype.image_preimage_coe, set_like.mem_coe, coe_subtype] at h,
  change A ∩ C = B ∩ C at h,
  rw set.inter_eq_self_of_subset_left hA at h,
  rwa set.inter_eq_self_of_subset_left hB at h,
end

lemma mod_law_left (A' A B : subgroup α) (hA : A' ≤ A) :
  (A' : set α) * (A ⊓ B : subgroup α) = A ⊓ (A' * B) :=
begin
  simp only [coe_inf, set.inf_eq_inter],
  rw set_like.le_def at hA,
  ext,
  refine ⟨λ h, set.mem_inter _ _, λ h, _⟩,
  { rcases set.mem_mul.mp h with ⟨y, z, hy, hz, hyz⟩,
    rw set.mem_inter_iff at hz,
    have := mul_mem A (hA hy) hz.1,
    rwa hyz at this, },
  { rcases set.mem_mul.mp h with ⟨y, z, hy, hz, hyz⟩,
    rw set.mem_mul,
    exact ⟨y, z, hy, (set.mem_of_subset_of_mem (set.inter_subset_right ↑A ↑B) hz), hyz⟩, },
    rw set.mem_inter_iff at h,
    rcases h.2 with ⟨y, z, hy, hz, hyz⟩,
  rw set.mem_mul,
  refine ⟨x * z⁻¹, z, _, (set.mem_inter _ hz), _⟩,
  rwa ← eq_mul_inv_of_mul_eq hyz,
  have := eq_inv_mul_of_mul_eq hyz,
  have boo := mul_mem A (inv_mem A (hA hy)) h.1,
  rwa ← this at boo,
  simp only [inv_mul_cancel_right],
end

lemma mod_law_right (A' A B : subgroup α) (hA : A' ≤ A) :
  ((A ⊓ B : subgroup α) : set α) * A' = A ⊓ (B * A') :=
begin
  simp only [coe_inf, set.inf_eq_inter],
  rw set_like.le_def at hA,
  ext,
  refine ⟨λ h, set.mem_inter _ _, λ h, _⟩,
  { rcases set.mem_mul.mp h with ⟨y, z, hy, hz, hyz⟩,
    rw set.mem_inter_iff at hy,
    have := mul_mem A hy.1 (hA hz),
    rwa hyz at this, },
  { rcases set.mem_mul.mp h with ⟨y, z, hy, hz, hyz⟩,
    rw set.mem_mul,
    exact ⟨y, z, (set.mem_of_subset_of_mem (set.inter_subset_right ↑A ↑B) hy), hz, hyz⟩, },
    rw set.mem_inter_iff at h,
    rcases h.2 with ⟨y, z, hy, hz, hyz⟩,
  rw set.mem_mul,
  have boo := mul_mem A h.1 (inv_mem A (hA hz)),
  have := eq_mul_inv_of_mul_eq hyz,
  refine ⟨x * z⁻¹, z, set.mem_inter _ _, hz, _⟩,
  exact boo,
  rwa this at hy,
  simp only [inv_mul_cancel_right],
end

lemma preimage_mul_of_injective {X : Type u} [monoid X] {Y : Type v} [monoid Y] (A B : set Y)
  (f : X →* Y) (hf : function.injective f) (hA : A ⊆ set.range f) (hB : B ⊆ set.range f) :
  f ⁻¹' (A * B) = f ⁻¹' A * f⁻¹' B :=
begin
  let := f.to_fun,
  ext,
  refine ⟨λ h, _, λ h, _⟩,
  { rw set.mem_mul,
    rw set.mem_preimage at h,
    rw set.mem_mul at h,
    rcases h with ⟨a, b, ha, hb, hab⟩,
    rcases function.injective.exists_unique_of_mem_range hf (set.mem_of_subset_of_mem hA ha)
      with ⟨a', ha', hau⟩,
    rcases function.injective.exists_unique_of_mem_range hf (set.mem_of_subset_of_mem hB hb)
      with ⟨b', hb', hbu⟩,
    refine ⟨a', b', _, _, _⟩,
    rw ← ha' at ha,
    rwa set.mem_preimage,
    rw ← hb' at hb,
    rwa set.mem_preimage,
    rw ← ha' at hab,
    rw ← hb' at hab,
    rw ← monoid_hom.map_mul at hab,
    exact hf hab },
  rw set.mem_preimage,
  rw set.mem_mul at h,
  rcases h with ⟨a, b, ha, hb, hab⟩,
  rw set.mem_preimage at ha,
  rw set.mem_preimage at hb,
  rw set.mem_mul,
  refine ⟨f a, f b, ha, hb, _⟩,
  apply_fun f at hab,
  rwa ← monoid_hom.map_mul,
end

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

lemma coe_mul_self_eq {G : Type u} [group G] (H : subgroup G) :
  (H :set G) * H = H :=
begin
  ext x,
  refine ⟨_, λ h, ⟨x, 1, h, H.one_mem, mul_one x⟩⟩,
  rintros ⟨a, b, ha, hb, rfl⟩,
  exact H.mul_mem ha hb
end

lemma normal_subgroup_mul (A' A B : subgroup α) (hA : A' ≤ A) [hN : (A'.of A).normal] (hB : B ≤ A) :
  ((A' ⊔ B : subgroup α) : set α) = A' * B :=
begin
  suffices h : ((A' ⊔ B).of A : set A) = A'.of A * B.of A,
  simp only [of, coe_comap, coe_subtype] at h,
  apply_fun set.image (coe : A → α) at h,
  nth_rewrite 3 ← coe_subtype at h,
  nth_rewrite 3 ← coe_subtype at h,
  rw ← preimage_mul_of_injective at h,
  simp only [subtype.image_preimage_coe, set_like.mem_coe, coe_subtype] at h,
  change ((A' ⊔ B : subgroup α) : set α) ∩ A = ↑A' * ↑B ∩ A at h,
  rw set.inter_eq_self_of_subset_left at h,
  rwa set.inter_eq_self_of_subset_left at h,
  rw ← set.le_eq_subset,
  have : ↑A' * ↑B ⊆ ↑A * ↑A := set.mul_subset_mul hA hB,
  rw coe_mul_self_eq at this,
  exact this,
  exact sup_le hA hB,
  exact subtype_injective A,
  simp only [← monoid_hom.coe_range, subtype_range],
  exact hA,
  simp only [← monoid_hom.coe_range, subtype_range],
  exact hB,
  simp [sup_of A' B A hA hB, normal_mul],
end

def Zassenhaus_quot {A' A B' B : subgroup α} (hA : A' ≤ A) (hB : B' ≤ B)
  [hAN : (A'.of A).normal] [hBN : (B'.of B).normal] :=
quotient_group.quotient $ ((A' ⊓ B) ⊔ (A ⊓ B')).of (A ⊓ B)

instance bruh {A' A B' B : subgroup α} (hA : A' ≤ A) (hB : B' ≤ B)
  [hAN : (A'.of A).normal] [hBN : (B'.of B).normal] : group (Zassenhaus_quot hA hB) :=
begin
  dsimp [Zassenhaus_quot],
  haveI := subgroup.Zassenhaus1 hA hB,
  apply_instance,
end

lemma Zassenhaus_aux {A' A : subgroup α} (B : subgroup α) (hA : A' ≤ A) [hAN : (A'.of A).normal] :
  ↑(A' ⊔ A ⊓ B) = (A' : set α) * (A ⊓ B : subgroup α) :=
normal_subgroup_mul A' A (A ⊓ B) hA (inf_le_left_of_le (le_refl A))

instance wtff {A' A B : subgroup α} (hA : A' ≤ A) [hAN : (A'.of A).normal] : group ↥(A' ⊔ A ⊓ B) :=
begin
  apply_instance,
end

lemma Zassenhaus_quot_aux {A' A B' B : subgroup α} (hA : A' ≤ A) (hB : B' ≤ B)
  [hAN : (A'.of A).normal] [hBN : (B'.of B).normal] :
  ↑((A' ⊓ B) ⊔ (A ⊓ B')) = (A : set α) ⊓ B ⊓ (A' * B') :=
begin
  have : ↑((A' ⊓ B) ⊔ (A ⊓ B')) = ((A' : set α) ⊓ B) * (A ⊓ B'),
  { haveI : ((A' ⊓ B).of (A ⊓ B)).normal :=
    by { have := inf_normal_inf B A' A hA, rw inf_comm, rwa @inf_comm _ _ A' B },
    refine normal_subgroup_mul _ (A ⊓ B) _
      (inf_le_inf hA (le_refl B)) (inf_le_inf (le_refl A) hB), },
  rw this,
  clear this,
  have := mod_law_left (A' ⊓ B) A B' _,
  have bleh : ↑(A' ⊓ B) * ↑B' = (B : set α) ⊓ (A' * B'), sorry,
  rw bleh at this,
  rw ← inf_assoc at this,
  convert this,
  exact inf_le_left_of_le hA,
end

lemma set.subset_mul_left (s t : subgroup α) :
  (s : set α) ⊆ s * t :=
begin
  rw set.subset_def,
  intros x hx,
  rw set.mem_mul,
  refine ⟨x, 1, hx, one_mem t, mul_one x⟩,
end

lemma subgroup.subgroup_normal.mem_comm {G : Type u} [group G] {H K : subgroup G}
  (hK : H ≤ K) [hN : (H.of K).normal] {a b : G} (hb : b ∈ K) (h : a * b ∈ H) : b * a ∈ H :=
begin
  rw normal_of_def H K hK at hN,
  specialize hN (a * b) b h hb,
  rw mul_assoc at hN,
  rw mul_assoc at hN,
  rwa [mul_right_inv, mul_one] at hN,
end

noncomputable def Zassenhaus_fun {A' A B' B : subgroup α} (hA : A' ≤ A) (hB : B' ≤ B)
  [hAN : (A'.of A).normal] [hBN : (B'.of B).normal] :
  ↥(A' ⊔ A ⊓ B) →* (Zassenhaus_quot hA hB) :=
{ to_fun := λ x, quotient.mk' ⟨_, ((mem_mul (Zassenhaus_aux B hA)).mp x.2).some_spec.some_spec.2.1⟩,
  map_one' :=
  begin
    haveI := quotient_group.left_rel ((A' ⊓ B ⊔ A ⊓ B').of (A ⊓ B)),
    refine quot.sound _,
    let := ((mem_mul (Zassenhaus_aux B hA)).mp (1 : (A' ⊔ A ⊓ B)).2),
    let g : ↥(A ⊓ B) := ⟨this.some_spec.some, this.some_spec.some_spec.2.1⟩,
    have hs := inv_mem A' this.some_spec.some_spec.1,
    have hsg : this.some * g.val = 1 := this.some_spec.some_spec.2.2,
    suffices h : g⁻¹ * 1 ∈ ((A' ⊓ B ⊔ A ⊓ B').of (A ⊓ B)),
    exact h,
    rw [mem_of, mul_one, coe_subtype, mem_inf, coe_inv],
    rw [inv_mem_iff (A' ⊓ B ⊔ A ⊓ B'), inv_mem_iff (A ⊓ B)],
    refine ⟨_, g.2⟩,
    change ↑g ∈ ↑(A' ⊓ B ⊔ A ⊓ B'),
    rw Zassenhaus_quot_aux,
    rw mul_eq_one_iff_inv_eq at hsg,
    rw hsg at hs,
    rw [set.inf_eq_inter],
    rw set.mem_inter_eq,
    have boo : g.val ∈ (A : set α) ∩ B := g.2,
    refine ⟨boo, _⟩,
    change ↑g ∈ ↑A' at hs,
    exact set.mem_of_subset_of_mem (set.subset_mul_left A' B') hs,
    exact hA,
    exact hB,
  end,
  map_mul' := λ a b,
  begin
    haveI := subgroup.Zassenhaus1 hA hB,
    refine quot.sound _,
    let ainfo := ((mem_mul (Zassenhaus_aux B hA)).mp (a : (A' ⊔ A ⊓ B)).2),
    let binfo := ((mem_mul (Zassenhaus_aux B hA)).mp (b : (A' ⊔ A ⊓ B)).2),
    let abinfo := ((mem_mul (Zassenhaus_aux B hA)).mp (a * b : (A' ⊔ A ⊓ B)).2),
    let x : ↥(A ⊓ B) := ⟨ainfo.some_spec.some, ainfo.some_spec.some_spec.2.1⟩,
    let y : ↥(A ⊓ B) := ⟨binfo.some_spec.some, binfo.some_spec.some_spec.2.1⟩,
    let xy : ↥(A ⊓ B) := ⟨abinfo.some_spec.some, abinfo.some_spec.some_spec.2.1⟩,
    have hsa := inv_mem A' ainfo.some_spec.some_spec.1,
    have hsxm : ainfo.some * x.val = a := ainfo.some_spec.some_spec.2.2,
    have hsb := inv_mem A' binfo.some_spec.some_spec.1,
    have hsym : binfo.some * y.val = b := binfo.some_spec.some_spec.2.2,
    have hsab := inv_mem A' abinfo.some_spec.some_spec.1,
    have hsxym : abinfo.some * xy.val = (a * b) := abinfo.some_spec.some_spec.2.2,
    suffices h : xy⁻¹ * (x * y) ∈ ((A' ⊓ B ⊔ A ⊓ B').of (A ⊓ B)),
    exact h,
    rw [mem_of, coe_subtype, mem_inf, coe_mul, coe_inv, coe_mul],
    refine ⟨_, mul_mem (A ⊓ B) (inv_mem (A ⊓ B) xy.2) (mul_mem (A ⊓ B) x.2 y.2)⟩,
    refine subgroup.subgroup_normal.mem_comm (Zassenhaus_subgroup hA hB) (inv_mem (A ⊓ B) xy.2) _,
    change _ ∈ ↑(A' ⊓ B ⊔ A ⊓ B'),
    rw Zassenhaus_quot_aux hA hB,
    rw [← hsxm, ← hsym] at hsxym,
    have : ainfo.some * x.val * (binfo.some * y.val) = ainfo.some * (x * binfo.some * x⁻¹) * (x * y),
    { sorry },
    rw this at hsxym, clear this,
    rw ← eq_mul_inv_iff_mul_eq at hsxym,
    rw mul_assoc at hsxym,
    rw mul_assoc at hsxym,
    rw ← inv_mul_eq_iff_eq_mul at hsxym,
    rw ← inv_mul_eq_iff_eq_mul at hsxym,
    have mem : (↑x * binfo.some * (↑x)⁻¹)⁻¹ * ((ainfo.some)⁻¹ * abinfo.some) ∈ A', { sorry },
    rw hsxym at mem,
    have mem2 : ↑x * ↑y * (xy.val)⁻¹ ∈ (A : set α) ∩ B, { sorry },
    rw [set.inf_eq_inter],
    rw set.mem_inter_eq,
    refine ⟨mem2, _⟩,
    change _ ∈ ↑A' at mem,
    exact set.mem_of_subset_of_mem (set.subset_mul_left A' B') mem,
  end }

lemma mem_of_subset {x : α} {H K : subgroup α} (hK : H ≤ K) (h : x ∈ H) : x ∈ K :=
begin
  sorry
end

lemma Zassenhaus_fun_ker (A' A B' B : subgroup α) (hA : A' ≤ A) (hB : B' ≤ B)
  [hAN : (A'.of A).normal] [hBN : (B'.of B).normal] :
  (Zassenhaus_fun hA hB).ker = (A' ⊔ A ⊓ B').of (A' ⊔ A ⊓ B) :=
begin
  ext,
  refine ⟨λ h, _, λ h, _⟩,
  { rw monoid_hom.mem_ker at h,
    dsimp [Zassenhaus_fun] at h,
    sorry },
  rw monoid_hom.mem_ker,
  dsimp [Zassenhaus_fun],
  refine quot.sound _,
  simp only [mem_of, set_like.coe_mem, and_true, mem_inf, coe_subtype] at h,
  --have := ((mem_mul (Zassenhaus_aux B hA)).mp x.2),
  have := ((mem_mul (Zassenhaus_aux B' hA)).mp h),
  have hz' : _ ∈ A ⊓ B := mem_of_subset (inf_le_inf (le_refl A) hB) this.some_spec.some_spec.2.1,
  --have : ∃ y z, y ∈ A' ∧ z ∈ A ⊓ B ∧ y * z = ↑x := ⟨y, z, hy, hz, hz', hyz⟩,
  let g : ↥(A ⊓ B) := ⟨this.some_spec.some, hz'⟩,
  suffices h : g⁻¹ * 1 ∈ ((A' ⊓ B ⊔ A ⊓ B').of (A ⊓ B)),
  convert h,
  rw [mem_of, mul_one, coe_subtype, coe_inv, inv_mem_iff, mem_inf],
  have hz' : z ∈ A ⊓ B, sorry,
  have : g = ⟨z, hz'⟩,
  sorry
end

end subgroup
