/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.perm group_theory.order_of_element group_theory.quotient_group

universes u v
open finset is_subgroup equiv equiv.perm quotient_group

instance {α β : Type*} [group α] [group β] [decidable_eq β] (f : α → β) [is_group_hom f] :
  decidable_pred (is_group_hom.ker f) :=
λ _, decidable_of_iff _ (is_group_hom.mem_ker f).symm

def alternating (α : Type*) [decidable_eq α] [fintype α] : Type* :=
is_group_hom.ker (sign : perm α → units ℤ)

/- not definitionally equal to `subtype.decidable_eq`, since `subtype.decidable_eq` does
  not reduce in the kernel -/
instance (α : Type*) [decidable_eq α] [fintype α] : decidable_eq (alternating α) :=
λ a b, decidable_of_iff (a.1 = b.1) (by cases a; cases b; simp [subtype.mk.inj_eq])

instance (α : Type*) [decidable_eq α] [fintype α] : fintype (alternating α) :=
set_fintype _

instance (α : Type*) [decidable_eq α] [fintype α] : group (alternating α) :=
by unfold alternating; apply_instance

section classical

local attribute [instance] classical.prop_decidable

lemma card_alternating (α : Type*) [decidable_eq α] [fintype α] (h : 2 ≤ fintype.card α):
  fintype.card (alternating α) * 2 = (fintype.card α).fact :=
have (quotient_group.quotient (is_group_hom.ker (sign : perm α → units ℤ))) ≃ units ℤ,
  from quotient_ker_equiv_of_surjective _ (sign_surjective h),
calc fintype.card (alternating α) * 2 = fintype.card (units ℤ × alternating α) :
  by rw [mul_comm, fintype.card_prod, fintype.card_units_int]
... = fintype.card (perm α) : fintype.card_congr
  (calc (units ℤ × alternating α) ≃
    (quotient_group.quotient (is_group_hom.ker (sign : perm α → units ℤ)) × alternating α)  :
      equiv.prod_congr this.symm (by refl)
  ... ≃ perm α : (group_equiv_quotient_times_subgroup _).symm)
... = (fintype.card α).fact : fintype.card_perm

end classical

local notation `A5` := alternating (fin 5)
variables {α : Type*} [fintype α] [decidable_eq α]

section meta_
local attribute [semireducible] reflected

meta instance fin_reflect (n : ℕ) : has_reflect (fin n) :=
λ a, `(@fin.mk %%`(n) %%(nat.reflect a.1) (of_as_true %%`(_root_.trivial)))

meta instance fin_fun.has_reflect : has_reflect (fin 5 → fin 5) :=
list.rec_on (quot.unquot (@univ (fin 5) _).1)
  (λ f, `(λ y : fin 5, y))
  (λ x l ih f, let e := ih f in
    if f x = x then e
    else let ex := fin_reflect 5 x in
      let efx := fin_reflect 5 (f x) in
      if e = `(λ y : fin 5, y)
      then `(λ y : fin 5, ite.{1} (y = %%ex) (%%efx) y)
      else `(λ y : fin 5, ite.{1} (y = %%ex) (%%efx) ((%%e : fin 5 → fin 5) y)))

meta instance : has_reflect (perm (fin 5)) :=
λ f, `(@equiv.mk.{1 1} (fin 5) (fin 5)
    %%(fin_fun.has_reflect f.to_fun)
  %%(fin_fun.has_reflect f.inv_fun)
  (of_as_true %%`(_root_.trivial)) (of_as_true %%`(_root_.trivial)))

meta instance I1 : has_reflect (alternating (fin 5)) :=
λ f, `(@subtype.mk (perm (fin 5)) (is_group_hom.ker (sign : perm (fin 5) → units ℤ))
   %%(@reflect (perm (fin 5)) f.1 (equiv.perm.has_reflect f.1))
  ((is_group_hom.mem_ker sign).2 %%`(@eq.refl (units ℤ) 1)))

meta instance multiset.has_reflect {α : Type} [reflected α] [has_reflect α] :
  has_reflect (multiset α) :=
λ s, let l : list α := quot.unquot s in `(@quotient.mk.{1} (list %%`(α)) _ %%`(l))

meta instance I2 (a : alternating (fin 5)) :
  has_reflect {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1} :=
λ b, `(@subtype.mk (alternating (fin 5) × alternating (fin 5))
  (λ b, b.2 * %%`(a) * b.2⁻¹ = b.1)
  %%(prod.has_reflect _ _ b.1) (of_as_true %%`(_root_.trivial)))

meta instance I3 (a : alternating (fin 5)) (m : reflected a) :
  reflected {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1} :=
`({b : alternating (fin 5) × alternating (fin 5) // b.2 * %%m * b.2⁻¹ = b.1})

meta instance I4 : has_reflect
  (Σ a : alternating (fin 5), multiset
  {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1}) :=
λ s, let ra : reflected s.1 := (I1 s.1) in
`(let a : alternating (fin 5) := %%ra in
  @sigma.mk (alternating (fin 5))
    (λ a, multiset {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1})
    a %%(@multiset.has_reflect _ (I3 s.1 ra) (I2 s.1) s.2))

meta def conjugacy_classes_A5_meta_aux : list (alternating (fin 5)) → list
  (Σ a : alternating (fin 5), list
  {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1})
| [] := []
| (a :: l) := let m : Σ a : alternating (fin 5), list
    {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1} :=
  ⟨a, ((quot.unquot (@univ (alternating (fin 5)) _).1).map
  (λ x, show {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1},
    from ⟨(x * a * x⁻¹, x), rfl⟩)).pw_filter (λ x y, x.1.1 ≠ y.1.1)⟩ in
m :: conjugacy_classes_A5_meta_aux (l.diff (m.2.map (prod.fst ∘ subtype.val)))

meta def conjugacy_classes_A5_meta : multiset (Σ a : alternating (fin 5), multiset
  {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1}) :=
(quotient.mk ((conjugacy_classes_A5_meta_aux (quot.unquot univ.1)).map
    (λ a, ⟨a.1, (quotient.mk a.2)⟩)))

meta def exact_reflect {α : Sort*} [has_reflect α] (a : α) : tactic unit :=
tactic.exact `(a)

end meta_

@[irreducible] def conjugacy_classes_A5_aux : multiset (Σ a : alternating (fin 5), multiset
  {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1}) :=
by exact_reflect (conjugacy_classes_A5_meta)

def conjugacy_classes_A5_aux2 : multiset (multiset (alternating (fin 5))) :=
conjugacy_classes_A5_aux.map (λ s, s.2.map (λ b, b.1.1))

lemma nodup_conjugacy_classes_A5_aux2_bind : (conjugacy_classes_A5_aux2.bind id).nodup :=
dec_trivial

lemma nodup_conjugacy_classes_A5_aux2 : ∀ s : multiset (alternating (fin 5)),
  s ∈ conjugacy_classes_A5_aux2 → s.nodup :=
(multiset.nodup_bind.1 nodup_conjugacy_classes_A5_aux2_bind).1

def conjugacy_classes_A5 : finset (finset (alternating (fin 5))) :=
⟨conjugacy_classes_A5_aux2.pmap finset.mk nodup_conjugacy_classes_A5_aux2, dec_trivial⟩

lemma nodup_conjugacy_classes_A5_bind : (conjugacy_classes_A5.1.bind finset.val).nodup :=
have conjugacy_classes_A5.1.bind finset.val =
  conjugacy_classes_A5_aux2.bind id,
from multiset.ext.2 $ λ a,
  by rw [conjugacy_classes_A5, @multiset.count_bind A5, @multiset.count_bind A5,
    multiset.map_pmap, multiset.pmap_eq_map]; refl,
by rw this; exact nodup_conjugacy_classes_A5_aux2_bind

lemma is_conj_conjugacy_classes_A5 (s : finset A5) (h : s ∈ conjugacy_classes_A5) :
  ∀ x y ∈ s, is_conj x y :=
assume x y hx hy,
begin
  simp only [conjugacy_classes_A5, finset.mem_def, multiset.mem_pmap,
    conjugacy_classes_A5_aux2] at h,
  rcases h with ⟨t, ht₁, ht₂⟩,
  rw [multiset.mem_map] at ht₁,
  rcases ht₁ with ⟨u, hu₁, hu₂⟩,
  have hx' : x ∈ multiset.map (λ (b : {b : A5 × A5 // b.2 * u.1 * b.2⁻¹ = b.1}), b.1.1) u.2,
  { simpa [ht₂.symm, hu₂] using hx },
  have hy' : y ∈ multiset.map (λ (b : {b : A5 × A5 // b.2 * u.1 * b.2⁻¹ = b.1}), b.1.1) u.2,
  { simpa [ht₂.symm, hu₂] using hy },
  cases multiset.mem_map.1 hx' with xc hxc,
  cases multiset.mem_map.1 hy' with yc hyc,
  exact is_conj_trans
    (is_conj_symm (show is_conj u.1 x, from hxc.2 ▸ ⟨_, xc.2⟩))
    (hyc.2 ▸ ⟨_, yc.2⟩)
end

variables {G : Type u} [group G] [decidable_eq G]

lemma normal_subgroup_eq_bind_conjugacy_classes (s : finset (finset G)) (h₁ : ∀ x, ∃ t ∈ s, x ∈ t)
  (h₂ : ∀ t ∈ s, ∀ x y ∈ t, is_conj x y) (I : finset G) [nI : normal_subgroup (↑I : set G)] :
  ∃ u ⊆ s, I = u.bind id :=
⟨(s.powerset.filter (λ u : finset (finset G), u.bind id ⊆ I)).bind id,
    (λ x, by simp only [finset.subset_iff, mem_bind, mem_filter, exists_imp_distrib, mem_powerset,
      and_imp, id.def] {contextual := tt}; tauto),
  le_antisymm
    (λ x hxI, let ⟨t, ht₁, ht₂⟩ := h₁ x in
      mem_bind.2 ⟨t, mem_bind.2 ⟨(s.powerset.filter (λ u : finset (finset G), u.bind id ⊆ I)).bind id,
          mem_filter.2 ⟨mem_powerset.2
            (λ u hu, let ⟨v, hv₁, hv₂⟩ := mem_bind.1 hu in
              mem_powerset.1 (mem_filter.1 hv₁).1 hv₂),
          λ y hy, let ⟨u, hu₁, hu₂⟩ := mem_bind.1 hy in
            let ⟨v, hv₁, hv₂⟩ := mem_bind.1 hu₁ in
            (mem_filter.1 hv₁).2 (mem_bind.2 ⟨u, hv₂, hu₂⟩)⟩,
        mem_bind.2 ⟨{t}, mem_filter.2 ⟨by simp [ht₁, finset.subset_iff],
            λ y hy, let ⟨u, hu₁, hu₂⟩ := mem_bind.1 hy in
              let ⟨z, hz⟩ := h₂ t ht₁ x y ht₂ (by simp * at *) in
              hz ▸ @normal_subgroup.normal G _ I.to_set nI _ hxI _⟩,
          by simp⟩⟩,
        ht₂⟩)
    (λ x, by simp only [finset.subset_iff, mem_bind, exists_imp_distrib, mem_filter, mem_powerset]; tauto)⟩

lemma simple_of_card_conjugacy_classes [fintype G] (s : finset (finset G))
  (h₁ : ∀ x, ∃ t ∈ s, x ∈ t) (h₂ : ∀ t ∈ s, ∀ x y ∈ t, is_conj x y)
  (hs : (s.1.bind finset.val).nodup)
  (h₃ : ∀ t ≤ s.1.map finset.card, 1 ∈ t → t.sum ∣ fintype.card G → t.sum = 1 ∨ t.sum = fintype.card G) :
  simple_group G :=
by haveI := classical.dec; exact
⟨λ H iH,
  let I := (set.to_finset H) in
  have Ii : normal_subgroup (↑I : set G), by simpa using iH,
  let ⟨u, hu₁, hu₂⟩ :=
    @normal_subgroup_eq_bind_conjugacy_classes G _ _ s h₁ h₂ I Ii in
  have hInd : ∀ (x : finset G), x ∈ u → ∀ (y : finset G), y ∈ u → x ≠ y → id x ∩ id y = ∅,
    from λ x hxu y hyu hxy,
      begin
        rw multiset.nodup_bind at hs,
        rw [← finset.disjoint_iff_inter_eq_empty, finset.disjoint_left],
        exact multiset.forall_of_pairwise
          (λ (a b : finset G) (h : multiset.disjoint a.1 b.1),
          multiset.disjoint.symm h) hs.2 x (hu₁ hxu) y (hu₁ hyu) hxy
      end,
  have hci : card I = u.sum finset.card,
    by rw [hu₂, card_bind hInd]; refl,
  have hu1 : (1 : G) ∈ u.bind id, by exactI hu₂ ▸ is_submonoid.one_mem (↑I : set G),
  let ⟨v, hv₁, hv₂⟩ := mem_bind.1 hu1 in
  have hv : v = finset.singleton (1 : G),
    from finset.ext.2 $ λ a, ⟨λ hav, mem_singleton.2 $
        is_conj_one_right.1 (h₂ v (hu₁ hv₁) _ _ hv₂ hav),
      by simp [show (1 : G) ∈ v, from hv₂] {contextual := tt}⟩,
  have hci' : card I = 1 ∨ card I = fintype.card G,
    begin
      rw [hci],
      exact h₃ _ (multiset.map_le_map (show u.1 ≤ s.1,
        from (multiset.le_iff_subset u.2).2 hu₁))
          (multiset.mem_map.2 ⟨finset.singleton 1, hv ▸ hv₁, rfl⟩)
          (calc u.sum finset.card = card I : hci.symm
            ... = fintype.card (↑I : set G) : (set.card_fintype_of_finset' I (by simp)).symm
            ... ∣ fintype.card G : by exactI card_subgroup_dvd_card _)
    end,
    hci'.elim
      (λ hci', or.inl (set.ext (λ x,
        let ⟨y, hy⟩ := finset.card_eq_one.1 hci' in
        by resetI;
          simp only [I, finset.ext, set.mem_to_finset, finset.mem_singleton] at hy;
          simp [is_subgroup.mem_trivial, hy, (hy 1).1 (is_submonoid.one_mem H)])))
      (λ hci', or.inr $
        suffices I = finset.univ,
          by simpa [I, set.ext_iff, finset.ext] using this,
        finset.eq_of_subset_of_card_le (λ _, by simp) (by rw hci'; refl))⟩

lemma card_A5 : fintype.card A5 = 60 :=
(nat.mul_right_inj (show 2 > 0, from dec_trivial)).1 $
have 2 ≤ fintype.card (fin 5), from dec_trivial,
  by rw [card_alternating _ this]; simp; refl

lemma conjugacy_classes_A5_bind_eq_univ :
  conjugacy_classes_A5.bind (λ t, t) = univ :=
eq_of_subset_of_card_le (λ _, by simp)
  (calc card univ = 60 : card_A5
    ... ≤ (conjugacy_classes_A5.1.bind finset.val).card : dec_trivial
    ... = (conjugacy_classes_A5.bind id).card :
      begin
        rw [finset.card_bind, multiset.card_bind], refl,
        { exact multiset.forall_of_pairwise (λ a b, by simp [finset.inter_comm])
            (by simp only [finset.disjoint_iff_inter_eq_empty.symm, finset.disjoint_left];
              exact (multiset.nodup_bind.1 nodup_conjugacy_classes_A5_bind).2) }
      end)

lemma simple_group_A5 : simple_group A5 :=
simple_of_card_conjugacy_classes conjugacy_classes_A5
  (λ x, mem_bind.1 $ by rw [conjugacy_classes_A5_bind_eq_univ]; simp)
  is_conj_conjugacy_classes_A5
  nodup_conjugacy_classes_A5_bind
  (by simp only [multiset.mem_powerset.symm, card_A5];
    exact dec_trivial)
