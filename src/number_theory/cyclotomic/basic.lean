/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import ring_theory.polynomial.cyclotomic.roots
import number_theory.number_field.basic
import field_theory.galois

/-!
# Cyclotomic extensions

Let `A` and `B` be commutative rings with `algebra A B`. For `S : set ℕ+`, we define a class
`is_cyclotomic_extension S A B` expressing the fact that `B` is obtained from `A` by adding `n`-th
primitive roots of unity, for all `n ∈ S`.

## Main definitions

* `is_cyclotomic_extension S A B` : means that `B` is obtained from `A` by adding `n`-th primitive
  roots of unity, for all `n ∈ S`.
* `cyclotomic_field`: given `n : ℕ+` and a field `K`, we define `cyclotomic n K` as the splitting
  field of `cyclotomic n K`. If `n` is nonzero in `K`, it has the instance
  `is_cyclotomic_extension {n} K (cyclotomic_field n K)`.
* `cyclotomic_ring` : if `A` is a domain with fraction field `K` and `n : ℕ+`, we define
  `cyclotomic_ring n A K` as the `A`-subalgebra of `cyclotomic_field n K` generated by the roots of
  `X ^ n - 1`. If `n` is nonzero in `A`, it has the instance
  `is_cyclotomic_extension {n} A (cyclotomic_ring n A K)`.

## Main results

* `is_cyclotomic_extension.trans` : if `is_cyclotomic_extension S A B` and
  `is_cyclotomic_extension T B C`, then `is_cyclotomic_extension (S ∪ T) A C` if
  `function.injective (algebra_map B C)`.
* `is_cyclotomic_extension.union_right` : given `is_cyclotomic_extension (S ∪ T) A B`, then
  `is_cyclotomic_extension T (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) B`.
* `is_cyclotomic_extension.union_right` : given `is_cyclotomic_extension T A B` and `S ⊆ T`, then
  `is_cyclotomic_extension S A (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 })`.
* `is_cyclotomic_extension.finite` : if `S` is finite and `is_cyclotomic_extension S A B`, then
  `B` is a finite `A`-algebra.
* `is_cyclotomic_extension.number_field` : a finite cyclotomic extension of a number field is a
  number field.
* `is_cyclotomic_extension.splitting_field_X_pow_sub_one` : if `is_cyclotomic_extension {n} K L`,
  then `L` is the splitting field of `X ^ n - 1`.
* `is_cyclotomic_extension.splitting_field_cyclotomic` : if `is_cyclotomic_extension {n} K L`,
  then `L` is the splitting field of `cyclotomic n K`.

## Implementation details

Our definition of `is_cyclotomic_extension` is very general, to allow rings of any characteristic
and infinite extensions, but it will mainly be used in the case `S = {n}` and for integral domains.
All results are in the `is_cyclotomic_extension` namespace.
Note that some results, for example `is_cyclotomic_extension.trans`,
`is_cyclotomic_extension.finite`, `is_cyclotomic_extension.number_field`,
`is_cyclotomic_extension.finite_dimensional`, `is_cyclotomic_extension.is_galois` and
`cyclotomic_field.algebra_base` are lemmas, but they can be made local instances. Some of them are
included in the `cyclotomic` locale.

-/

open polynomial algebra finite_dimensional set

open_locale big_operators

universes u v w z

variables (n : ℕ+) (S T : set ℕ+) (A : Type u) (B : Type v) (K : Type w) (L : Type z)
variables [comm_ring A] [comm_ring B] [algebra A B]
variables [field K] [field L] [algebra K L]

noncomputable theory

/-- Given an `A`-algebra `B` and `S : set ℕ+`, we define `is_cyclotomic_extension S A B` requiring
that there is a `n`-th primitive root of unity in `B` for all `n ∈ S` and that `B` is generated
over `A` by the roots of `X ^ n - 1`. -/
@[mk_iff] class is_cyclotomic_extension : Prop :=
(exists_prim_root {n : ℕ+} (ha : n ∈ S) : ∃ r : B, is_primitive_root r n)
(adjoin_roots : ∀ (x : B), x ∈ adjoin A { b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1 })

namespace is_cyclotomic_extension

section basic

/-- A reformulation of `is_cyclotomic_extension` that uses `⊤`. -/
lemma iff_adjoin_eq_top : is_cyclotomic_extension S A B ↔
 (∀ (n : ℕ+), n ∈ S → ∃ r : B, is_primitive_root r n) ∧
 (adjoin A { b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1 } = ⊤) :=
⟨λ h, ⟨λ _, h.exists_prim_root, algebra.eq_top_iff.2 h.adjoin_roots⟩,
  λ h, ⟨h.1, algebra.eq_top_iff.1 h.2⟩⟩

/-- A reformulation of `is_cyclotomic_extension` in the case `S` is a singleton. -/
lemma iff_singleton : is_cyclotomic_extension {n} A B ↔
 (∃ r : B, is_primitive_root r n) ∧
 (∀ x, x ∈ adjoin A { b : B | b ^ (n : ℕ) = 1 }) :=
by simp [is_cyclotomic_extension_iff]

/-- If `is_cyclotomic_extension ∅ A B`, then the image of `A` in `B` equals `B`. -/
lemma empty [h : is_cyclotomic_extension ∅ A B] : (⊥ : subalgebra A B) = ⊤ :=
by simpa [algebra.eq_top_iff, is_cyclotomic_extension_iff] using h

/-- If `is_cyclotomic_extension {1} A B`, then the image of `A` in `B` equals `B`. -/
lemma singleton_one [h : is_cyclotomic_extension {1} A B] : (⊥ : subalgebra A B) = ⊤ :=
algebra.eq_top_iff.2 (λ x, by simpa [adjoin_singleton_one]
  using ((is_cyclotomic_extension_iff _ _ _).1 h).2 x)

variables {A B}

/-- If `(⊥ : subalgebra A B) = ⊤`, then `is_cyclotomic_extension ∅ A B`. -/
lemma singleton_zero_of_bot_eq_top (h : (⊥ : subalgebra A B) = ⊤) :
  is_cyclotomic_extension ∅ A B :=
begin
  refine (iff_adjoin_eq_top _ _ _).2 ⟨λ s hs, by simpa using hs, _root_.eq_top_iff.2 (λ x hx, _)⟩,
  rw [← h] at hx,
  simpa using hx,
end

variables (A B)

/-- Transitivity of cyclotomic extensions. -/
lemma trans (C : Type w) [comm_ring C] [algebra A C] [algebra B C]
  [is_scalar_tower A B C] [hS : is_cyclotomic_extension S A B]
  [hT : is_cyclotomic_extension T B C] (h : function.injective (algebra_map B C)) :
  is_cyclotomic_extension (S ∪ T) A C :=
begin
  refine ⟨λ n hn, _, λ x, _⟩,
  { cases hn,
    { obtain ⟨b, hb⟩ := ((is_cyclotomic_extension_iff _ _ _).1 hS).1 hn,
      refine ⟨algebra_map B C b, _⟩,
      exact hb.map_of_injective h },
    { exact ((is_cyclotomic_extension_iff _ _ _).1 hT).1 hn } },
  { refine adjoin_induction (((is_cyclotomic_extension_iff _ _ _).1 hT).2 x) (λ c ⟨n, hn⟩,
      subset_adjoin ⟨n, or.inr hn.1, hn.2⟩) (λ b, _) (λ x y hx hy, subalgebra.add_mem _ hx hy)
      (λ x y hx hy, subalgebra.mul_mem _ hx hy),
    { let f := is_scalar_tower.to_alg_hom A B C,
      have hb : f b ∈ (adjoin A { b : B | ∃ (a : ℕ+), a ∈ S ∧ b ^ (a : ℕ) = 1 }).map f :=
        ⟨b, ((is_cyclotomic_extension_iff _ _ _).1 hS).2 b, rfl⟩,
      rw [is_scalar_tower.to_alg_hom_apply, ← adjoin_image] at hb,
      refine adjoin_mono (λ y hy, _) hb,
      obtain ⟨b₁, ⟨⟨n, hn⟩, h₁⟩⟩ := hy,
      exact ⟨n, ⟨mem_union_left T hn.1, by rw [← h₁, ← alg_hom.map_pow, hn.2, alg_hom.map_one]⟩⟩ } }
end

@[nontriviality] lemma subsingleton_iff [subsingleton B] :
  is_cyclotomic_extension S A B ↔ S = {} ∨ S = {1} :=
begin
  split,
  { rintro ⟨hprim, -⟩,
    rw ←subset_singleton_iff_eq,
    intros t ht,
    obtain ⟨ζ, hζ⟩ := hprim ht,
    rw [mem_singleton_iff, ←pnat.coe_eq_one_iff],
    exact_mod_cast hζ.unique (is_primitive_root.of_subsingleton ζ) },
  { rintro (rfl|rfl),
    { refine ⟨λ _ h, h.elim, λ x, by convert (mem_top : x ∈ ⊤)⟩ },
    { rw iff_singleton,
      refine ⟨⟨0, is_primitive_root.of_subsingleton 0⟩, λ x, by convert (mem_top : x ∈ ⊤)⟩ } }
end

/-- If `B` is a cyclotomic extension of `A` given by roots of unity of order in `S ∪ T`, then `B`
is a cyclotomic extension of `adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } ` given by
roots of unity of order in `T`. -/
lemma union_right [h : is_cyclotomic_extension (S ∪ T) A B] :
  is_cyclotomic_extension T (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) B :=
begin
  have : { b : B | ∃ (n : ℕ+), n ∈ S ∪ T ∧ b ^ (n : ℕ) = 1 } =
    { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 } ∪
    { b : B | ∃ (n : ℕ+), n ∈ T ∧ b ^ (n : ℕ) = 1 },
  { refine le_antisymm (λ x hx, _) (λ x hx, _),
    { rcases hx with ⟨n, hn₁ | hn₂, hnpow⟩,
      { left, exact ⟨n, hn₁, hnpow⟩ },
      { right, exact ⟨n, hn₂, hnpow⟩ } },
    { rcases hx with ⟨n, hn⟩ | ⟨n, hn⟩,
      { exact ⟨n, or.inl hn.1, hn.2⟩ },
      { exact ⟨n, or.inr hn.1, hn.2⟩ } } },

  refine ⟨λ n hn, ((is_cyclotomic_extension_iff _ _ _).1 h).1 (mem_union_right S hn), λ b, _⟩,
  replace h := ((is_cyclotomic_extension_iff _ _ _).1 h).2 b,
  rwa [this, adjoin_union_eq_adjoin_adjoin, subalgebra.mem_restrict_scalars] at h
end

/-- If `B` is a cyclotomic extension of `A` given by roots of unity of order in `T` and `S ⊆ T`,
then `adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }` is a cyclotomic extension of `B`
given by roots of unity of order in `S`. -/
lemma union_left [h : is_cyclotomic_extension T A B] (hS : S ⊆ T) :
  is_cyclotomic_extension S A (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) :=
begin
  refine ⟨λ n hn, _, λ b, _⟩,
  { obtain ⟨b, hb⟩ := ((is_cyclotomic_extension_iff _ _ _).1 h).1 (hS hn),
    refine ⟨⟨b, subset_adjoin ⟨n, hn, hb.pow_eq_one⟩⟩, _⟩,
    rwa [← is_primitive_root.coe_submonoid_class_iff, subtype.coe_mk] },
  { convert mem_top,
    rw [← adjoin_adjoin_coe_preimage, preimage_set_of_eq],
    norm_cast }
end

variables {n S}

/-- If `∀ s ∈ S, n ∣ s` and `S` is not empty, then `is_cyclotomic_extension S A B` implies
`is_cyclotomic_extension (S ∪ {n}) A B`. -/
lemma of_union_of_dvd (h : ∀ s ∈ S, n ∣ s) (hS : S.nonempty) [H : is_cyclotomic_extension S A B] :
  is_cyclotomic_extension (S ∪ {n}) A B :=
begin
  refine (iff_adjoin_eq_top _ _ _).2 ⟨λ s hs, _, _⟩,
  { rw [mem_union, mem_singleton_iff] at hs,
    obtain hs|rfl := hs,
    { exact H.exists_prim_root hs },
    { obtain ⟨m, hm⟩ := hS,
      obtain ⟨x, rfl⟩ := h m hm,
      obtain ⟨ζ, hζ⟩ := H.exists_prim_root hm,
      refine ⟨ζ ^ (x : ℕ), _⟩,
      convert hζ.pow_of_dvd x.ne_zero (dvd_mul_left (x : ℕ) s),
      simp only [pnat.mul_coe, nat.mul_div_left, pnat.pos] } },
  { refine _root_.eq_top_iff.2 _,
    rw [← ((iff_adjoin_eq_top S A B).1 H).2],
    refine adjoin_mono (λ x hx, _),
    simp only [union_singleton, mem_insert_iff, mem_set_of_eq] at ⊢ hx,
    obtain ⟨m, hm⟩ := hx,
    exact ⟨m, ⟨or.inr hm.1, hm.2⟩⟩ }
end

/-- If `∀ s ∈ S, n ∣ s` and `S` is not empty, then `is_cyclotomic_extension S A B` if and only if
`is_cyclotomic_extension (S ∪ {n}) A B`. -/
lemma iff_union_of_dvd (h : ∀ s ∈ S, n ∣ s) (hS : S.nonempty) :
  is_cyclotomic_extension S A B ↔ is_cyclotomic_extension (S ∪ {n}) A B :=
begin
  refine ⟨λ H, by exactI of_union_of_dvd A B h hS, λ H, (iff_adjoin_eq_top _ _ _).2 ⟨λ s hs, _, _⟩⟩,
  { exact H.exists_prim_root (subset_union_left _ _ hs) },
  { rw [_root_.eq_top_iff, ← ((iff_adjoin_eq_top _ A B).1 H).2],
    refine adjoin_mono (λ x hx, _),
    simp only [union_singleton, mem_insert_iff, mem_set_of_eq] at ⊢ hx,
    obtain ⟨m, rfl|hm, hxpow⟩ := hx,
    { obtain ⟨y, hy⟩ := hS,
      refine ⟨y, ⟨hy, _⟩⟩,
      obtain ⟨z, rfl⟩ := h y hy,
      simp only [pnat.mul_coe, pow_mul, hxpow, one_pow] },
    { exact ⟨m, ⟨hm, hxpow⟩⟩ } }
end

variables (n S)

/-- `is_cyclotomic_extension S A B` is equivalent to `is_cyclotomic_extension (S ∪ {1}) A B`. -/
lemma iff_union_singleton_one :
  is_cyclotomic_extension S A B ↔ is_cyclotomic_extension (S ∪ {1}) A B :=
begin
  obtain hS|rfl := S.eq_empty_or_nonempty.symm,
  { exact iff_union_of_dvd _ _ (λ s hs, one_dvd _) hS },
  rw [empty_union],
  refine ⟨λ H, _, λ H, _⟩,
  { refine (iff_adjoin_eq_top _ _ _).2 ⟨λ s hs, ⟨1, by simp [mem_singleton_iff.1 hs]⟩, _⟩,
    simp [adjoin_singleton_one, @empty _ _ _ _ _ H] },
  { refine (iff_adjoin_eq_top _ _ _).2 ⟨λ s hs, (not_mem_empty s hs).elim, _⟩,
    simp [@singleton_one A B _ _ _ H] }
end

variables {A B}

/-- If `(⊥ : subalgebra A B) = ⊤`, then `is_cyclotomic_extension {1} A B`. -/
lemma singleton_one_of_bot_eq_top (h : (⊥ : subalgebra A B) = ⊤) :
  is_cyclotomic_extension {1} A B :=
begin
  convert (iff_union_singleton_one _ _ _).1 (singleton_zero_of_bot_eq_top h),
  simp
end

/-- If `function.surjective (algebra_map A B)`, then `is_cyclotomic_extension {1} A B`. -/
lemma singleton_one_of_algebra_map_bijective (h : function.surjective (algebra_map A B)) :
  is_cyclotomic_extension {1} A B :=
singleton_one_of_bot_eq_top (surjective_algebra_map_iff.1 h).symm

variables (A B)

/-- Given `(f : B ≃ₐ[A] C)`, if `is_cyclotomic_extension S A B` then
`is_cyclotomic_extension S A C`. -/
@[protected] lemma equiv {C : Type*} [comm_ring C] [algebra A C] [h : is_cyclotomic_extension S A B]
  (f : B ≃ₐ[A] C) : is_cyclotomic_extension S A C :=
begin
  letI : algebra B C := f.to_alg_hom.to_ring_hom.to_algebra,
  haveI : is_cyclotomic_extension {1} B C := singleton_one_of_algebra_map_bijective f.surjective,
  haveI : is_scalar_tower A B C := is_scalar_tower.of_ring_hom f.to_alg_hom,
  exact (iff_union_singleton_one _ _ _).2 (trans S {1} A B C f.injective)
end

@[protected]
lemma ne_zero [h : is_cyclotomic_extension {n} A B] [is_domain B] : ne_zero ((n : ℕ) : B) :=
begin
  obtain ⟨⟨r, hr⟩, -⟩ := (iff_singleton n A B).1 h,
  exact hr.ne_zero'
end

@[protected]
lemma ne_zero' [is_cyclotomic_extension {n} A B] [is_domain B] : ne_zero ((n : ℕ) : A) :=
begin
  apply ne_zero.nat_of_ne_zero (algebra_map A B),
  exact ne_zero n A B,
end

end basic

section fintype

lemma finite_of_singleton [is_domain B] [h : is_cyclotomic_extension {n} A B] : module.finite A B :=
begin
  classical,
  rw [module.finite_def, ← top_to_submodule, ← ((iff_adjoin_eq_top _ _ _).1 h).2],
  refine fg_adjoin_of_finite _ (λ b hb, _),
  { simp only [mem_singleton_iff, exists_eq_left],
    have : {b : B | b ^ (n : ℕ) = 1} = (nth_roots n (1 : B)).to_finset :=
      set.ext (λ x, ⟨λ h, by simpa using h, λ h, by simpa using h⟩),
    rw [this],
    exact (nth_roots ↑n 1).to_finset.finite_to_set },
  { simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hb,
    refine ⟨X ^ (n : ℕ) - 1, ⟨monic_X_pow_sub_C _ n.pos.ne.symm, by simp [hb]⟩⟩ }
end

/-- If `S` is finite and `is_cyclotomic_extension S A B`, then `B` is a finite `A`-algebra. -/
@[protected]
lemma finite [is_domain B] [h₁ : finite S] [h₂ : is_cyclotomic_extension S A B] :
  module.finite A B :=
begin
  casesI nonempty_fintype S with h,
  unfreezingI {revert h₂ A B},
  refine set.finite.induction_on (set.finite.intro h) (λ A B, _) (λ n S hn hS H A B, _),
  { introsI _ _ _ _ _,
    refine module.finite_def.2 ⟨({1} : finset B), _⟩,
    simp [← top_to_submodule, ← empty, to_submodule_bot] },
  { introsI _ _ _ _ h,
    haveI : is_cyclotomic_extension S A (adjoin A { b : B | ∃ (n : ℕ+),
      n ∈ S ∧ b ^ (n : ℕ) = 1 }) := union_left _ (insert n S) _ _ (subset_insert n S),
    haveI := H A (adjoin A { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 }),
    haveI : module.finite (adjoin A { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 }) B,
    { rw [← union_singleton] at h,
      letI := @union_right S {n} A B _ _ _ h,
      exact finite_of_singleton n _ _ },
    exact module.finite.trans (adjoin A { b : B | ∃ (n : ℕ+), n ∈ S ∧ b ^ (n : ℕ) = 1 }) _ }
end

/-- A cyclotomic finite extension of a number field is a number field. -/
lemma number_field [h : number_field K] [_root_.finite S] [is_cyclotomic_extension S K L] :
  number_field L :=
{ to_char_zero := char_zero_of_injective_algebra_map (algebra_map K L).injective,
  to_finite_dimensional := begin
    haveI := char_zero_of_injective_algebra_map (algebra_map K L).injective,
    haveI := finite S K L,
    exact module.finite.trans K _
  end }

localized "attribute [instance] is_cyclotomic_extension.number_field" in cyclotomic

/-- A finite cyclotomic extension of an integral noetherian domain is integral -/
lemma integral [is_domain B] [is_noetherian_ring A] [_root_.finite S]
  [is_cyclotomic_extension S A B] : algebra.is_integral A B :=
is_integral_of_noetherian $ is_noetherian_of_fg_of_noetherian' $ (finite S A B).out

/-- If `S` is finite and `is_cyclotomic_extension S K A`, then `finite_dimensional K A`. -/
lemma finite_dimensional (C : Type z) [_root_.finite S] [comm_ring C] [algebra K C] [is_domain C]
  [is_cyclotomic_extension S K C] : finite_dimensional K C :=
is_cyclotomic_extension.finite S K C

localized "attribute [instance] is_cyclotomic_extension.finite_dimensional" in cyclotomic

end fintype

section

variables {A B}

lemma adjoin_roots_cyclotomic_eq_adjoin_nth_roots [decidable_eq B] [is_domain B] {ζ : B}
  {n : ℕ+} (hζ : is_primitive_root ζ n) :
  adjoin A ((cyclotomic n A).root_set B) =
  adjoin A {b : B | ∃ (a : ℕ+), a ∈ ({n} : set ℕ+) ∧ b ^ (a : ℕ) = 1} :=
begin
  simp only [mem_singleton_iff, exists_eq_left, map_cyclotomic],
  refine le_antisymm (adjoin_mono (λ x hx, _)) (adjoin_le (λ x hx, _)),
  { rw [mem_root_set'] at hx,
    simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq],
    rw is_root_of_unity_iff n.pos,
    refine ⟨n, nat.mem_divisors_self n n.ne_zero, _⟩,
    rw [is_root.def, ←map_cyclotomic n (algebra_map A B), eval_map, ←aeval_def],
    exact hx.2 },
  { simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hx,
    obtain ⟨i, hin, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx n.pos,
    refine set_like.mem_coe.2 (subalgebra.pow_mem _ (subset_adjoin _) _),
    rw [mem_root_set', map_cyclotomic, aeval_def, ←eval_map, map_cyclotomic, ←is_root],
    refine ⟨cyclotomic_ne_zero n B, hζ.is_root_cyclotomic n.pos⟩ }
end

lemma adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic {n : ℕ+} [decidable_eq B] [is_domain B]
  {ζ : B} (hζ : is_primitive_root ζ n) :
  adjoin A ((cyclotomic n A).root_set B) = adjoin A ({ζ}) :=
begin
  refine le_antisymm (adjoin_le (λ x hx, _)) (adjoin_mono (λ x hx, _)),
  { suffices hx : x ^ ↑n = 1,
    obtain ⟨i, hin, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx n.pos,
    exact set_like.mem_coe.2 (subalgebra.pow_mem _ (subset_adjoin $ mem_singleton ζ) _),
    rw is_root_of_unity_iff n.pos,
    refine ⟨n, nat.mem_divisors_self n n.ne_zero, _⟩,
    rw [mem_root_set', aeval_def, ←eval_map, map_cyclotomic, ←is_root] at hx,
    exact hx.2 },
  { simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq] at hx,
    simpa only [hx, mem_root_set', map_cyclotomic, aeval_def, ←eval_map, is_root]
      using and.intro (cyclotomic_ne_zero n B) (hζ.is_root_cyclotomic n.pos) }
end

lemma adjoin_primitive_root_eq_top {n : ℕ+} [is_domain B] [h : is_cyclotomic_extension {n} A B]
  {ζ : B} (hζ : is_primitive_root ζ n) : adjoin A ({ζ} : set B) = ⊤ :=
begin
  classical,
  rw ←adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic hζ,
  rw adjoin_roots_cyclotomic_eq_adjoin_nth_roots hζ,
  exact ((iff_adjoin_eq_top {n} A B).mp h).2,
end

variable (A)

lemma _root_.is_primitive_root.adjoin_is_cyclotomic_extension {ζ : B} {n : ℕ+}
  (h : is_primitive_root ζ n) : is_cyclotomic_extension {n} A (adjoin A ({ζ} : set B)) :=
{ exists_prim_root := λ i hi,
  begin
    rw [set.mem_singleton_iff] at hi,
    refine ⟨⟨ζ, subset_adjoin $ set.mem_singleton ζ⟩, _⟩,
    rwa [← is_primitive_root.coe_submonoid_class_iff, subtype.coe_mk, hi],
  end,
  adjoin_roots := λ x,
  begin
    refine adjoin_induction' (λ b hb, _) (λ a, _) (λ b₁ b₂ hb₁ hb₂, _) (λ b₁ b₂ hb₁ hb₂, _) x,
    { rw [set.mem_singleton_iff] at hb,
      refine subset_adjoin _,
      simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq, hb],
      rw [← subalgebra.coe_eq_one, subalgebra.coe_pow, set_like.coe_mk],
      exact ((is_primitive_root.iff_def ζ n).1 h).1 },
    { exact subalgebra.algebra_map_mem _ _ },
    { exact subalgebra.add_mem _ hb₁ hb₂ },
    { exact subalgebra.mul_mem _ hb₁ hb₂ }
  end }

end

section field

variables {n S}

/-- A cyclotomic extension splits `X ^ n - 1` if `n ∈ S`.-/
lemma splits_X_pow_sub_one [H : is_cyclotomic_extension S K L] (hS : n ∈ S) :
  splits (algebra_map K L) (X ^ (n : ℕ) - 1) :=
begin
  rw [← splits_id_iff_splits, polynomial.map_sub, polynomial.map_one,
      polynomial.map_pow, polynomial.map_X],
  obtain ⟨z, hz⟩ := ((is_cyclotomic_extension_iff _ _ _).1 H).1 hS,
  exact X_pow_sub_one_splits hz,
end

/-- A cyclotomic extension splits `cyclotomic n K` if `n ∈ S` and `ne_zero (n : K)`.-/
lemma splits_cyclotomic [is_cyclotomic_extension S K L] (hS : n ∈ S) :
  splits (algebra_map K L) (cyclotomic n K) :=
begin
  refine splits_of_splits_of_dvd _ (X_pow_sub_C_ne_zero n.pos _)
    (splits_X_pow_sub_one K L hS) _,
  use (∏ (i : ℕ) in (n : ℕ).proper_divisors, polynomial.cyclotomic i K),
  rw [(eq_cyclotomic_iff n.pos _).1 rfl, ring_hom.map_one],
end

variables (n S)

section singleton

variables [is_cyclotomic_extension {n} K L]

/-- If `is_cyclotomic_extension {n} K L`, then `L` is the splitting field of `X ^ n - 1`. -/
lemma splitting_field_X_pow_sub_one : is_splitting_field K L (X ^ (n : ℕ) - 1) :=
{ splits := splits_X_pow_sub_one K L (mem_singleton n),
  adjoin_root_set :=
  begin
    rw [← ((iff_adjoin_eq_top {n} K L).1 infer_instance).2],
    congr,
    refine set.ext (λ x, _),
    simp only [polynomial.map_pow, mem_singleton_iff, multiset.mem_to_finset, exists_eq_left,
      mem_set_of_eq, polynomial.map_X, polynomial.map_one, finset.mem_coe, polynomial.map_sub],
    simp only [mem_root_set', map_sub, map_pow, aeval_one, aeval_X, sub_eq_zero, map_X,
               and_iff_right_iff_imp, polynomial.map_sub, polynomial.map_pow, polynomial.map_one],
    exact λ _, X_pow_sub_C_ne_zero n.pos (1 : L)
  end }

/-- Any two `n`-th cyclotomic extensions are isomorphic. -/
def alg_equiv (L' : Type*) [field L'] [algebra K L'] [is_cyclotomic_extension {n} K L'] :
  L ≃ₐ[K] L' :=
let _ := splitting_field_X_pow_sub_one n K L in let _ := splitting_field_X_pow_sub_one n K L' in
  by exactI (is_splitting_field.alg_equiv L (X ^ (n : ℕ) - 1)).trans
  (is_splitting_field.alg_equiv L' (X ^ (n : ℕ) - 1)).symm

localized "attribute [instance] is_cyclotomic_extension.splitting_field_X_pow_sub_one" in cyclotomic

include n

lemma is_galois : is_galois K L :=
begin
  letI := splitting_field_X_pow_sub_one n K L,
  exact is_galois.of_separable_splitting_field (X_pow_sub_one_separable_iff.2 ((ne_zero' n K L).1))
end

localized "attribute [instance] is_cyclotomic_extension.is_galois" in cyclotomic

/-- If `is_cyclotomic_extension {n} K L`, then `L` is the splitting field of `cyclotomic n K`. -/
lemma splitting_field_cyclotomic : is_splitting_field K L (cyclotomic n K) :=
{ splits := splits_cyclotomic K L (mem_singleton n),
  adjoin_root_set :=
  begin
    rw [← ((iff_adjoin_eq_top {n} K L).1 infer_instance).2],
    letI := classical.dec_eq L,
    -- todo: make `exists_prim_root` take an explicit `L`
    obtain ⟨ζ : L, hζ⟩ := is_cyclotomic_extension.exists_prim_root K (mem_singleton n),
    exact adjoin_roots_cyclotomic_eq_adjoin_nth_roots hζ,
    all_goals { apply_instance }
  end }

localized "attribute [instance] is_cyclotomic_extension.splitting_field_cyclotomic" in cyclotomic

end singleton

end field

end is_cyclotomic_extension

section cyclotomic_field

/-- Given `n : ℕ+` and a field `K`, we define `cyclotomic_field n K` as the
splitting field of `cyclotomic n K`. If `n` is nonzero in `K`, it has
the instance `is_cyclotomic_extension {n} K (cyclotomic_field n K)`. -/
@[derive [field, algebra K, inhabited]]
def cyclotomic_field : Type w := (cyclotomic n K).splitting_field

namespace cyclotomic_field

instance [char_zero K] : char_zero (cyclotomic_field n K) :=
char_zero_of_injective_algebra_map ((algebra_map K _).injective)

instance is_cyclotomic_extension [ne_zero ((n : ℕ) : K)] :
  is_cyclotomic_extension {n} K (cyclotomic_field n K) :=
begin
  haveI : ne_zero ((n : ℕ) : (cyclotomic_field n K)) :=
    ne_zero.nat_of_injective (algebra_map K _).injective,
  letI := classical.dec_eq (cyclotomic_field n K),
  obtain ⟨ζ, hζ⟩ := exists_root_of_splits (algebra_map K (cyclotomic_field n K))
    (splitting_field.splits _) (degree_cyclotomic_pos n K n.pos).ne',
  rw [← eval_map, ← is_root.def, map_cyclotomic, is_root_cyclotomic_iff] at hζ,
  refine ⟨forall_eq.2 ⟨ζ, hζ⟩, _⟩,
  rw [←algebra.eq_top_iff, ←splitting_field.adjoin_root_set, eq_comm],
  exact is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots hζ,
end

end cyclotomic_field

end cyclotomic_field

section is_domain

variables [is_domain A] [algebra A K] [is_fraction_ring A K]

section cyclotomic_ring

/-- If `K` is the fraction field of `A`, the `A`-algebra structure on `cyclotomic_field n K`.
-/
@[nolint unused_arguments]
instance cyclotomic_field.algebra_base : algebra A (cyclotomic_field n K) :=
splitting_field.algebra' (cyclotomic n K)

/-- Ensure there are no diamonds when `A = ℤ`. -/
example : algebra_int (cyclotomic_field n ℚ) = cyclotomic_field.algebra_base _ _ _ := rfl

instance cyclotomic_field.no_zero_smul_divisors : no_zero_smul_divisors A (cyclotomic_field n K) :=
no_zero_smul_divisors.of_algebra_map_injective $ function.injective.comp
(no_zero_smul_divisors.algebra_map_injective _ _) $ is_fraction_ring.injective A K

/-- If `A` is a domain with fraction field `K` and `n : ℕ+`, we define `cyclotomic_ring n A K` as
the `A`-subalgebra of `cyclotomic_field n K` generated by the roots of `X ^ n - 1`. If `n`
is nonzero in `A`, it has the instance `is_cyclotomic_extension {n} A (cyclotomic_ring n A K)`. -/
@[derive [comm_ring, is_domain, inhabited]]
def cyclotomic_ring : Type w := adjoin A { b : (cyclotomic_field n K) | b ^ (n : ℕ) = 1 }

namespace cyclotomic_ring

/-- The `A`-algebra structure on `cyclotomic_ring n A K`. -/
instance algebra_base : algebra A (cyclotomic_ring n A K) := (adjoin A _).algebra

-- Ensure that there is no diamonds with ℤ.
example {n : ℕ+} : cyclotomic_ring.algebra_base n ℤ ℚ = algebra_int _ := rfl

instance : no_zero_smul_divisors A (cyclotomic_ring n A K) := (adjoin A _).no_zero_smul_divisors_bot

lemma algebra_base_injective : function.injective $ algebra_map A (cyclotomic_ring n A K) :=
no_zero_smul_divisors.algebra_map_injective _ _

instance : algebra (cyclotomic_ring n A K) (cyclotomic_field n K) :=
(adjoin A _).to_algebra

lemma adjoin_algebra_injective :
  function.injective $ algebra_map (cyclotomic_ring n A K) (cyclotomic_field n K) :=
subtype.val_injective

instance : no_zero_smul_divisors (cyclotomic_ring n A K) (cyclotomic_field n K) :=
no_zero_smul_divisors.of_algebra_map_injective (adjoin_algebra_injective n A K)

instance : is_scalar_tower A (cyclotomic_ring n A K) (cyclotomic_field n K) :=
is_scalar_tower.subalgebra' _ _ _ _

instance is_cyclotomic_extension [ne_zero ((n : ℕ) : A)] :
  is_cyclotomic_extension {n} A (cyclotomic_ring n A K) :=
{ exists_prim_root := λ a han,
  begin
    rw mem_singleton_iff at han,
    subst a,
    haveI := ne_zero.of_no_zero_smul_divisors A K n,
    haveI := ne_zero.of_no_zero_smul_divisors A (cyclotomic_field n K) n,
    obtain ⟨μ, hμ⟩ :=
      (cyclotomic_field.is_cyclotomic_extension n K).exists_prim_root (mem_singleton n),
    refine ⟨⟨μ, subset_adjoin _⟩, _⟩,
    { apply (is_root_of_unity_iff n.pos (cyclotomic_field n K)).mpr,
      refine ⟨n, nat.mem_divisors_self _ n.ne_zero, _⟩,
      rwa [← is_root_cyclotomic_iff] at hμ },
    { rwa [← is_primitive_root.coe_submonoid_class_iff, subtype.coe_mk] }
  end,
  adjoin_roots := λ x,
  begin
    refine adjoin_induction' (λ y hy, _) (λ a, _) (λ y z hy hz, _) (λ y z hy hz, _) x,
    { refine subset_adjoin _,
      simp only [mem_singleton_iff, exists_eq_left, mem_set_of_eq],
      rwa [← subalgebra.coe_eq_one, subalgebra.coe_pow, subtype.coe_mk] },
    { exact subalgebra.algebra_map_mem _ a },
    { exact subalgebra.add_mem _ hy hz },
    { exact subalgebra.mul_mem _ hy hz },
  end }

instance [ne_zero ((n : ℕ) : A)] :
  is_fraction_ring (cyclotomic_ring n A K) (cyclotomic_field n K) :=
{ map_units := λ ⟨x, hx⟩, begin
    rw is_unit_iff_ne_zero,
    apply map_ne_zero_of_mem_non_zero_divisors,
    apply adjoin_algebra_injective,
    exact hx
  end,
  surj := λ x,
  begin
    letI : ne_zero ((n : ℕ) : K) := ne_zero.nat_of_injective (is_fraction_ring.injective A K),
    refine algebra.adjoin_induction (((is_cyclotomic_extension.iff_singleton n K _).1
      (cyclotomic_field.is_cyclotomic_extension n K)).2 x) (λ y hy, _) (λ k, _) _ _,
    { exact ⟨⟨⟨y, subset_adjoin hy⟩, 1⟩, by simpa⟩ },
    { have : is_localization (non_zero_divisors A) K := infer_instance,
      replace := this.surj,
      obtain ⟨⟨z, w⟩, hw⟩ := this k,
      refine ⟨⟨algebra_map A _ z, algebra_map A _ w, map_mem_non_zero_divisors _
        (algebra_base_injective n A K) w.2⟩, _⟩,
      letI : is_scalar_tower A K (cyclotomic_field n K) :=
        is_scalar_tower.of_algebra_map_eq (congr_fun rfl),
      rw [set_like.coe_mk, ← is_scalar_tower.algebra_map_apply,
        ← is_scalar_tower.algebra_map_apply, @is_scalar_tower.algebra_map_apply A K _ _ _ _ _
        (_root_.cyclotomic_field.algebra n K) _ _ w, ← ring_hom.map_mul, hw,
        ← is_scalar_tower.algebra_map_apply] },
    { rintro y z ⟨a, ha⟩ ⟨b, hb⟩,
      refine ⟨⟨a.1 * b.2 + b.1 * a.2, a.2 * b.2, mul_mem_non_zero_divisors.2 ⟨a.2.2, b.2.2⟩⟩, _⟩,
      rw [set_like.coe_mk, ring_hom.map_mul, add_mul, ← mul_assoc, ha,
        mul_comm ((algebra_map _ _) ↑a.2), ← mul_assoc, hb],
      simp only [map_add, map_mul] },
    { rintro y z ⟨a, ha⟩ ⟨b, hb⟩,
      refine ⟨⟨a.1 * b.1, a.2 * b.2, mul_mem_non_zero_divisors.2 ⟨a.2.2, b.2.2⟩⟩, _⟩,
      rw [set_like.coe_mk, ring_hom.map_mul, mul_comm ((algebra_map _ _) ↑a.2), mul_assoc,
        ← mul_assoc z, hb, ← mul_comm ((algebra_map _ _) ↑a.2), ← mul_assoc, ha],
      simp only [map_mul] }
  end,
  eq_iff_exists := λ x y, ⟨λ h, ⟨1, by rw adjoin_algebra_injective n A K h⟩,
    λ ⟨c, hc⟩, by rw mul_left_cancel₀ (non_zero_divisors.ne_zero c.prop) hc⟩ }

lemma eq_adjoin_primitive_root {μ : (cyclotomic_field n K)} (h : is_primitive_root μ n) :
  cyclotomic_ring n A K = adjoin A ({μ} : set ((cyclotomic_field n K))) :=
begin
  letI := classical.prop_decidable,
  rw [←is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic h,
      is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots h],
  simp [cyclotomic_ring]
end

end cyclotomic_ring

end cyclotomic_ring

end is_domain

section is_alg_closed

variables [is_alg_closed K]

/-- Algebraically closed fields are `S`-cyclotomic extensions over themselves if
`ne_zero ((a : ℕ) : K))` for all `a ∈ S`. -/
lemma is_alg_closed.is_cyclotomic_extension (h : ∀ a ∈ S, ne_zero ((a : ℕ) : K)) :
  is_cyclotomic_extension S K K :=
begin
  refine ⟨λ a ha, _,  algebra.eq_top_iff.mp $ subsingleton.elim _ _ ⟩,
  obtain ⟨r, hr⟩ := is_alg_closed.exists_aeval_eq_zero K _ (degree_cyclotomic_pos a K a.pos).ne',
  refine ⟨r, _⟩,
  haveI := h a ha,
  rwa [coe_aeval_eq_eval, ← is_root.def, is_root_cyclotomic_iff] at hr,
end

instance is_alg_closed_of_char_zero.is_cyclotomic_extension [char_zero K] :
  ∀ S, is_cyclotomic_extension S K K :=
λ S, is_alg_closed.is_cyclotomic_extension S K (λ a ha, infer_instance)

end is_alg_closed
