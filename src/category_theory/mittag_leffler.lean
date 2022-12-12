import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic
import category_theory.category.basic
import category_theory.full_subcategory
import data.set.finite
import data.fintype.basic
import category_theory.types

universes u v w

open classical
open category_theory

noncomputable theory
local attribute [instance] prop_decidable


def category_theory.functor.eventual_range
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) :=
λ (j : J), ⋂ (i : J) (f : i ⟶ j), set.range (F.map f)

def category_theory.functor.is_mittag_leffler
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) :=
  ∀ (j : J), ∃ (i) (f : i ⟶ j),
             ∀ (i') (f' : i' ⟶ j), set.range (F.map f) ⊆ set.range (F.map f')

lemma category_theory.functor.is_mittag_leffler_iff_eventual_range
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) :
  F.is_mittag_leffler ↔ ∀ (j : J), ∃ (i : J) (f : i ⟶ j), F.eventual_range j = set.range (F.map f) :=
begin
  dsimp [category_theory.functor.eventual_range],
  sorry,
end

lemma category_theory.is_cofiltered.cone_over_cospan
  {J : Type u} [category J] [is_cofiltered J] {i j j' : J} (f : j ⟶ i) (f' : j' ⟶ i)  :
  ∃ (k : J) (g : k ⟶ j) (g' : k ⟶ j'), g ≫ f = g' ≫ f' :=
begin
  let h := is_cofiltered.min_to_left j j',
  let h' := is_cofiltered.min_to_right j j',
  let G := is_cofiltered.eq_hom (h ≫ f) (h' ≫ f'),
  refine ⟨_, G ≫ h, G ≫ h', _⟩,
  simp only [category.assoc, is_cofiltered.eq_condition],
end

/--
There is probably a nice general argument along the lines of:
* If J is cofiltered, then so is J/j (the comma category) for any j.
* The functor F : J ⥤ Type v defines a functor J/j ⥤ (F.obj j) by sending (f : i ⟶ j) to set.range $ F.map f
* The image of a cofiltered category is cofiltered
-/
lemma category_theory.functor.ranges_directed_of_is_cofiltered
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) (j : J) :
  directed_on (⊇) (set.range (λ ( f : Σ' (i : J), i ⟶ j), set.range (F.map f.2))) :=
begin
  rintros _ ⟨⟨i,ij⟩,rfl⟩ _ ⟨⟨k,kj⟩,rfl⟩,
  obtain ⟨l, li, lk, e⟩ := category_theory.is_cofiltered.cone_over_cospan ij kj,
  refine ⟨set.range (F.map $ li ≫ ij), _⟩,
  rw [set.mem_range, exists_prop],
  refine ⟨⟨⟨l, li ≫ ij⟩, rfl⟩, ⟨_, _⟩⟩,
  rotate, rw e,
  all_goals
  { simp_rw [functor.map_comp, types_comp],
    apply set.range_comp_subset_range, },
end

-- Probably exists somewhere
lemma directed_on_min {J : Type u} {s : set J} [preorder J] (h : directed_on (≥) s)
  (m ∈ s) (min : ∀ (a ∈ s), a ≤ m → a = m) : ∀ a ∈ s, m ≤ a :=
λ a as, let ⟨x, xs, xm, xa⟩ := h m H a as in (min x xs xm) ▸ xa

lemma category_theory.functor.is_mittag_leffler_of_exists_finite_range
  {J : Type u} [category.{w} J] [is_cofiltered J] (F : J ⥤ Type v)
  (h : ∀ (j : J), ∃ i (f : i ⟶ j), (set.range (F.map f)).finite ) :
  F.is_mittag_leffler :=
begin
  rintro j,
  suffices : ∃ (f : Σ' i, i ⟶ j), ∀ (f' : Σ' i, i ⟶ j),
               set.range (F.map f'.2) ≤ set.range (F.map f.2) →
                 set.range (F.map f'.2) = set.range (F.map f.2),
  { obtain ⟨⟨i, f⟩, fmin⟩ := this,
    refine ⟨i, f, λ i' f', _⟩,
    refine directed_on_min (F.ranges_directed_of_is_cofiltered j) _ ⟨⟨i, f⟩,rfl⟩ _ _ ⟨⟨i',f'⟩,rfl⟩,
    simp only [set.mem_range, psigma.exists, forall_exists_index],
    rintro _ k g rfl gf,
    exact fmin ⟨k,g⟩ gf, },

  let fins := subtype { f : Σ' i, i ⟶ j | (set.range (F.map f.2)).finite },
  haveI : nonempty fins := by { obtain ⟨i,f,fin⟩ := h j, exact ⟨⟨⟨i,f⟩,fin⟩⟩, },
  let fmin := function.argmin (λ (f : fins), f.prop.to_finset.card) nat.lt_wf,
  use fmin.val,
  rintro g gf,
  cases lt_or_eq_of_le gf,
  { have gfin : (set.range (F.map g.2)).finite := fmin.prop.subset gf,
    refine ((λ (f : fins), f.prop.to_finset.card).not_lt_argmin nat.lt_wf ⟨g, gfin⟩ _).elim,
    exact finset.card_lt_card (set.finite.to_finset_ssubset.mpr h_1), },
  { assumption, },
end

def category_theory.functor.to_eventual_ranges
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) : J ⥤ Type v :=
{ obj := λ j, F.eventual_range j,
  map := λ i j f, set.maps_to.restrict (F.map f) _ _ ( by
    { rintro x h,
      simp only [category_theory.functor.eventual_range, set.mem_Inter, set.mem_range] at h ⊢,
      rintro i' f',
      obtain ⟨l, g, g', e⟩ := category_theory.is_cofiltered.cone_over_cospan f f',
      obtain ⟨z,rfl⟩ := h l g,
      use F.map g' z,
      replace e := congr_fun (congr_arg F.map e) z,
      simp_rw functor_to_types.map_comp_apply at e,
      exact e.symm, } ),
  map_id' := by
    { rintros, ext,
      simp only [set.maps_to.coe_restrict_apply, types_id_apply, category_theory.functor.map_id], },
  map_comp' := by
    { intros, ext,
      simp only [functor.map_comp, set.maps_to.coe_restrict_apply, types_comp_apply], }, }

def category_theory.functor.to_eventual_ranges_surjective
  {J : Type u} [category J] [is_cofiltered J] (F : J ⥤ Type v) (fm : F.is_mittag_leffler) :
  ∀ (i j : J) (f : i ⟶ j), (F.to_eventual_ranges.map f).surjective :=
begin
  rintros i j f ⟨x,hx⟩,
  dsimp [category_theory.functor.is_mittag_leffler] at fm,
end

lemma nonempty_sections_of_countable_mittag_leffner_inverse_system
  {J : Type u} [denumerable J] [category J] [is_cofiltered J] (F : J ⥤ Type v)
  (ml : F.is_mittag_leffler) [nempty : ∀ (j : J), nonempty (F.obj j)] : nonempty F.sections := sorry



/-
section prerequisites

-- Thanks Junyan Xu
lemma sInter_of_directed_nonempty {α : Type*} [fintype α] [nonempty α] (S : set (set α))
  (allsnempty : ∀ s ∈ S, set.nonempty s) (dir : directed_on (⊇) S) : S.sInter.nonempty :=
begin
  obtain rfl | h := S.eq_empty_or_nonempty,
  { rw set.sInter_empty, exact set.univ_nonempty },
  haveI := h.coe_sort,
  obtain ⟨⟨s, hs⟩, h'⟩ := dir.directed_coe.finset_le set.finite_univ.to_finset,
  simp_rw set.finite.mem_to_finset at h',
  exact (allsnempty s hs).mono (λ a ha t ht, h' ⟨t, ht⟩ trivial ha),
end

lemma equiv.of_bijective_trans {α β γ : Type*} {f : α → β} {g : β → γ}
  (hf : function.bijective f) (hg : function.bijective g) :
  (equiv.of_bijective f hf).trans (equiv.of_bijective g hg) =
   equiv.of_bijective (g ∘ f) (function.bijective.comp hg hf) := by { ext, refl, }

end prerequisites




--set_option profiler true




variables {J : Type u} [preorder J] [is_directed J ge] (F : J ⥤ Type v)


-- Thanks Junyan Xu
theorem nonempty_sections_of_fintype_inverse_system'
  [fin : Π (j : J), fintype (F.obj j)] [nempty : ∀ (j : J), nonempty (F.obj j)] :
  F.sections.nonempty :=
begin
  casesI is_empty_or_nonempty J,
  { exact ⟨is_empty_elim, is_empty_elim⟩, },
  { exact nonempty_sections_of_fintype_cofiltered_system _, },
end

lemma to_surjective.subfunctor  (i j : J) (ij : i ⟶ j) :
  subtype.simps.coe ∘ F.to_surjective.map ij = (F.map ij) ∘ subtype.simps.coe := rfl

lemma to_surjective.subfunctor_apply (i j : J) (ij : i ⟶ j) (x : F.to_surjective.obj i) :
  subtype.simps.coe (F.to_surjective.map ij x) = F.map ij (subtype.simps.coe x) := rfl

instance to_surjective.fintype [Π (j : J), fintype (F.obj j)] :
  Π (j : J), fintype  (F.to_surjective.obj j) := λ j, subtype.fintype _

instance to_surjective.nonempty
  [Π (j : J), fintype (F.obj j)] [Π (j : J), nonempty (F.obj j)] :
  Π (j : J), nonempty  (F.to_surjective.obj j) :=
begin
  rintro j,
  dsimp only [category_theory.functor.to_surjective],
  change nonempty (subtype _),
  rw nonempty_subtype,
  refine sInter_of_directed_nonempty _ _ _,
  { rintro s ⟨_, rfl⟩,
    exact set.range_nonempty _,},
  { rintro X ⟨⟨i,ij⟩,rfl⟩ Y ⟨⟨k,kj⟩,rfl⟩,
    obtain ⟨l,lk,li⟩ := directed_of (≥) k i,
    use [set.range (F.map $ hom_of_le lk ≫ hom_of_le kj), l, lk.le.trans kj, rfl],
    split,
    change hom_of_le lk ≫ hom_of_le kj with hom_of_le li ≫ hom_of_le ij,
    all_goals
    { rw [functor.map_comp, types_comp],
      apply set.range_comp_subset_range, }, },
end

lemma to_surjective.is_surjective
  [Π (j : J), fintype (F.obj j)] [nempties : Π (j : J), nonempty (F.obj j)] :
  ∀ (i j : J) (ij : i ≤ j), function.surjective (F.to_surjective.map (hom_of_le ij)) :=
begin
  rintros i j ij ⟨x,xh⟩,

  let S := set.range
    (λ k : {k : J | k ≤ i},
      (set.range (F.map (hom_of_le k.prop))) ∩ set.preimage (F.map  $ hom_of_le ij) {x}),

  have Ssnempty : ∀ s ∈ S, set.nonempty s, by
  { rintro s hs,
    obtain ⟨⟨k,ki⟩,rfl⟩ := hs,
    simp only [set.mem_set_of_eq] at ki,
    have xh : x ∈ ⋂ (l : {l | l ≤ j}), set.range (F.map (hom_of_le l.prop)) := xh,
    rw set.mem_Inter at xh,
    obtain ⟨z,rfl⟩ := xh ⟨k,ki.trans ij⟩,
    use F.map (hom_of_le ki) z,
    use ⟨z,rfl⟩,
    simp only [set.mem_preimage, set.mem_singleton_iff],
    rw ←functor_to_types.map_comp_apply,
    reflexivity,},

  have : (⋂₀ S).nonempty, by {
    refine sInter_of_directed_nonempty S Ssnempty _,
    unfold directed_on,
    rintros X ⟨⟨l,li⟩,rfl⟩ Y ⟨⟨k,ki⟩,rfl⟩,
    rw set.mem_set_of_eq at li ki,
    obtain ⟨m,mk,ml⟩ := directed_of (≥) k l,
    use set.range (F.map $ hom_of_le $ mk.le.trans ki) ∩ set.preimage (F.map  $ hom_of_le ij) {x},
    use [m,mk.le.trans ki,rfl],
    split,
    change hom_of_le (mk.le.trans ki) with (hom_of_le ml.le) ≫ (hom_of_le li), rotate,
    change hom_of_le (mk.le.trans ki) with (hom_of_le mk.le) ≫ (hom_of_le ki),
    all_goals
    { apply set.inter_subset_inter_left,
      rw [functor.map_comp, types_comp],
      apply set.range_comp_subset_range,}, },

  obtain ⟨y,y_mem⟩ := this,
  dsimp at y_mem,
  simp only [set.mem_Inter, set.mem_range, set.mem_preimage, set.mem_singleton_iff, subtype.forall]
    at y_mem,
  use y,
  { rintro s ⟨⟨m,mi⟩,rfl⟩,
    obtain ⟨⟨z,ztoy⟩,ytox⟩ := y_mem m mi,
    use [z,ztoy],},
  { obtain ⟨⟨z,ztoy⟩,ytox⟩ := y_mem i (le_refl i),
    apply subtype.mk_eq_mk.mpr ytox,},
end

namespace inverse_system

lemma sections_in_to_surjective (s : F.sections) (j : J) :
  (s.val j) ∈ set.range (subtype.val : (F.to_surjective.obj j) → F.obj j) :=
begin
  simp only [set.mem_range, set.mem_set_of_eq, set.Inter_coe_set, subtype.val_eq_coe,
             subtype.exists, set.mem_set_of_eq, set.Inter_coe_set, subtype.val_eq_coe,
             set.mem_range, subtype.exists],
  refine ⟨s.val j, _, rfl⟩,
  rintro s ⟨i,rfl⟩,
  simp only [set.mem_Inter],
  exact λ ij, ⟨s.val i, s.prop (hom_of_le ij)⟩,
end

lemma sections_in_surjective' (s : F.sections) (j : J) :
  (s.val j) ∈ ⋂ (i : { i | i ≤ j}), set.range (F.map (hom_of_le i.prop)) :=
begin
  rw set.mem_Inter,
  rintro ⟨i,ij⟩,
  exact ⟨s.val i, s.prop (hom_of_le ij)⟩,
end

def to_surjective.sections_equiv : F.sections ≃ F.to_surjective.sections :=
{ to_fun := λ s,
    ⟨ λ j, ⟨s.val j, set.mem_Inter.mpr (λ ii, ⟨s.val ii.val, s.prop (hom_of_le ii.prop)⟩)⟩,
      λ i j ij, subtype.mk_eq_mk.mpr (s.prop ij)⟩,
  inv_fun := λ ss,
    ⟨ λ j, (ss.val j).val, λ i j ij,
      by simpa only [←subtype.coe_inj, subtype.coe_mk] using ss.prop ij ⟩,
  left_inv := by
    { simp only [function.left_inverse, eq_self_iff_true, set_coe.forall, implies_true_iff], },
  right_inv := by
    { simp only [function.right_inverse, function.left_inverse, subtype.val_eq_coe, set_coe.forall,
                 subtype.coe_mk, subtype.coe_eta, eq_self_iff_true, implies_true_iff], } }

def sections_decomposition_at (j : J) :
  F.sections ≃ Σ (x : F.obj j), {s : F.sections | s.val j = x} :=
{ to_fun := λ s, ⟨s.val j, s, by simp only [set.mem_set_of_eq]⟩,
  inv_fun := λ ss, ss.2.val,
  left_inv := by simp only [function.left_inverse, eq_self_iff_true, implies_true_iff],
  right_inv := by
    { simp only [function.right_inverse, function.left_inverse, subtype.val_eq_coe, sigma.forall],
      rintro x ⟨⟨s, sec⟩, h⟩,
      induction h,
      simp only [eq_self_iff_true, subtype.coe_mk, heq_iff_eq, subtype.mk_eq_mk, and_self], } }

lemma sections_eval_injective_of_functor_injective_above (j : J)
  (inj : ∀ i : {i | i ≤ j}, function.injective $ F.map (hom_of_le i.prop)) :
  function.injective (λ (s : F.sections), s.val j) :=
begin
  rintros ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ h,
  rw subtype.mk_eq_mk,
  suffices : ∀ i : {i | i ≤ j}, e₁ i.val = e₂ i.val,
  { ext k,
    obtain ⟨m,mk,mj⟩ := directed_of (≥) k j,
    rw [←h₁ (hom_of_le mk), ←h₂ (hom_of_le mk), this ⟨m,mj⟩], },
  refine λ ii, inj ii _,
  change F.map (hom_of_le _) (e₁ ↑ii) = F.map (hom_of_le _) (e₂ ↑ii),
  rw [h₁, h₂],
  exact h,
end

def sections_bijective (j : J)
  (bij : ∀ i : {i | i ≤ j}, function.bijective $ F.map (hom_of_le i.prop)) :
  function.bijective (λ (s :F.sections), s.val j) :=
begin
  let inj  := λ ii : {i | i ≤ j}, (bij ii).1,
  let eqv  := λ ii : {i | i ≤ j}, equiv.of_bijective (F.map (hom_of_le ii.prop)) (bij ii),
  refine ⟨sections_eval_injective_of_functor_injective_above F j inj, _⟩,

  rintro x,

  let s :  Π (i : J), {y : F.obj i | ∃ (k : J) (ik : k ≤ i) (jk : k ≤ j),
                                       F.map (hom_of_le ik) ((eqv ⟨k,jk⟩).inv_fun x) = y}, by
  { rintro i,
    obtain ⟨mi,mj⟩ := (directed_of (≥) i j).some_spec,
    exact ⟨F.map (hom_of_le mi) ((eqv ⟨_,mj⟩).inv_fun x), _, mi, mj, rfl⟩, },

  refine ⟨⟨λ i, (s i).val, _⟩, _⟩,
  { rintro i k ik',
    obtain ⟨m,mi,mj,meq⟩ := (s i).prop,
    obtain ⟨n,nk,nj,neq⟩ := (s k).prop,
    obtain ⟨l,lm,ln⟩ := (directed_of (≥) m n),

    have lmbij : function.bijective (F.map $ hom_of_le lm), by
    { refine (function.bijective.of_comp_iff' (bij ⟨m,mj⟩) (F.map $ hom_of_le lm)).mp _,
      rw [←category_theory.types_comp,←category_theory.functor.map_comp],
      exact bij ⟨l,lm.le.trans mj⟩, },
    have lnbij : function.bijective (F.map $ hom_of_le ln), by
    { refine (function.bijective.of_comp_iff' (bij ⟨n,nj⟩) (F.map $ hom_of_le ln)).mp _,
      rw [←category_theory.types_comp,←category_theory.functor.map_comp],
      exact bij ⟨l,ln.le.trans nj⟩, },

    simp only [subtype.val_eq_coe],
    rw [←meq,←neq,
        ←functor_to_types.map_comp_apply,
        ←(equiv.right_inv (equiv.of_bijective _ lmbij) ((eqv ⟨m,mj⟩).inv_fun x)),
        ←(equiv.right_inv (equiv.of_bijective _ lnbij) ((eqv ⟨n,nj⟩).inv_fun x))],
    simp_rw [equiv.inv_fun_as_coe, equiv.to_fun_as_coe, equiv.of_bijective_apply,
             functor_to_types.map_comp_apply, ←functor_to_types.map_comp_apply],
    rw [←equiv.symm_trans_apply,←equiv.symm_trans_apply, equiv.of_bijective_trans,
        equiv.of_bijective_trans, ←equiv.inv_fun_as_coe,←equiv.inv_fun_as_coe],
    simp_rw [←types_comp, ←functor.map_comp'],
    reflexivity, },
  { obtain ⟨m,mj,mj',meq⟩ := (s j).prop,
    simp only [subtype.val_eq_coe,←equiv.inv_fun_as_coe,←meq],
    apply equiv.of_bijective_apply_symm_apply, },
end

lemma is_directed_of_coinitial
  (I : set J) (Icof : ∀ j : J, ∃ i ∈ I, i ≤ j) : is_directed I ge :=
begin
  apply is_directed.mk,
  rintros ⟨i,iI⟩ ⟨k,kI⟩,
  obtain ⟨j,ij,kj⟩ := directed_of (ge) i k,
  obtain ⟨m,mI,jm⟩ := Icof j,
  use ⟨m,mI⟩,
  simp only [ge_iff_le, subtype.mk_le_mk],
  exact ⟨jm.trans ij.le, jm.trans kj.le⟩,
end

instance lower_directed
  (j : J) : is_directed {i : J | i ≤ j} ge :=
begin
  apply is_directed_of_coinitial,
  rintros i,
  obtain ⟨k,ik,jk⟩ := directed_of (ge) i j,
  exact ⟨k,jk,ik⟩,
end

/--
The inverse system obtained by restring `F` to the index set above `j` and only to values
that map to `x`
-/
def above_point (j : J) (x : F.obj j) : {i : J | i ≤ j} ⥤ Type v :=
{ obj := λ ii, set.preimage (F.map $ hom_of_le ii.prop) {x},
  map := λ ii kk ik, set.maps_to.restrict (F.map $ ik) _ _ $ λ y, eq.rec $ by
  { rw [set.mem_preimage, set.mem_singleton_iff, ←functor_to_types.map_comp_apply], refl, },
  map_id' := λ ii, funext $ λ ⟨x,xh⟩, by
  { simp only [types_id_apply, set.maps_to.restrict, subtype.map, subtype.coe_mk, subtype.mk_eq_mk],
    nth_rewrite_rhs 0 ←functor_to_types.map_id_apply F x,
    reflexivity, },
  map_comp' := λ ii kk ll ik kl, funext $ λ ⟨x,xh⟩, by
  { simp only [types_comp_apply, set.maps_to.restrict, subtype.map, subtype.coe_mk,
               subtype.mk_eq_mk, ←functor_to_types.map_comp_apply],
    reflexivity, } }


instance above_point.nonempty [Π (j : J), fintype (F.obj j)] [∀ (j : J), nonempty (F.obj j)]
  (j : J)
  (Fsurj : ∀ i (ij : i ≤ j), function.surjective (F.map $ hom_of_le ij))
  (x : F.obj j) :
  Π (i : {i : J | i ≤ j}), nonempty ((above_point F j x).obj i)  :=
begin
  rintro ii,
  obtain ⟨y,rfl⟩ := Fsurj ii.val ii.prop x,
  refine nonempty.intro ⟨y, _⟩,
  simp only [set.mem_preimage, set.mem_singleton],
end

instance above_point.fintype [Π (j : J), fintype (F.obj j)] [∀ (j : J), nonempty (F.obj j)]
  (j : J) (x : F.obj j) : Π (i : {i : J | i ≤ j}), fintype ((above_point F j x).obj i)  :=
λ ii, subtype.fintype _

lemma above_point.sections_nonempty (j : J)
  (Fsurj : ∀ i (ij : i ≤ j), function.surjective (F.map $ hom_of_le ij))
  [Π (j : J), fintype (F.obj j)] [∀ (j : J), nonempty (F.obj j)]
  (x : F.obj j) : nonempty (above_point F j x).sections :=
begin
  apply set.nonempty_coe_sort.mpr,
  exact @nonempty_sections_of_fintype_inverse_system' _ _ _ (above_point F j x)
    (above_point.fintype F j x)  (above_point.nonempty F j Fsurj x),
end

private def sections_at_point_fwd  (j : J) (x : F.obj j) :
  {s : F.sections | s.val j = x} → (above_point F j x).sections :=
λ ⟨⟨s, sec⟩, sjx⟩,
  ⟨λ ii, ⟨s ii.val, eq.rec_on sjx $ sec $ hom_of_le ii.prop⟩,
   λ ii kk ik, by simpa only [sjx, ←subtype.coe_inj, set.maps_to.coe_restrict_apply,
                              subtype.coe_mk] using sec ik⟩

private def sections_at_point_bwd_aux (j : J) (x : F.obj j) :
  Π (s : (above_point F j x).sections) (i : J),
                 {y : F.obj i | ∃ (k : J) (ik : k ≤ i) (jk : k ≤ j),
                                y =  F.map (hom_of_le ik) (s.val $  ⟨k,jk⟩).val} :=
λ ⟨s,sec⟩ i, let mm := (directed_of (≥) i j) in
  ⟨ F.map (hom_of_le mm.some_spec.1) (s ⟨mm.some,mm.some_spec.2⟩).val,
    mm.some, mm.some_spec.1, mm.some_spec.2, rfl ⟩

private def sections_at_point_bwd  (j : J) (x : F.obj j) :
  (above_point F j x).sections → {s : F.sections | s.val j = x} :=
λ ss,
⟨ ⟨ (λ i,  (sections_at_point_bwd_aux F j x ss i).val),
    by
    { rintro i k ik',
      obtain ⟨m,mi,mj,meq⟩ := (sections_at_point_bwd_aux F j x ss i).prop,
      obtain ⟨n,nk,nj,neq⟩ := (sections_at_point_bwd_aux F j x ss k).prop,
      obtain ⟨l,lm,ln⟩ := (directed_of (≥) m n),
      obtain ⟨s,sec⟩ := ss,
      simp_rw [subtype.val_eq_coe, meq, neq,
               ←(@sec  ⟨l, lm.le.trans mj⟩ ⟨m, mj⟩ (hom_of_le $ lm)),
               ←(@sec  ⟨l, ln.le.trans nj⟩ ⟨n, nj⟩ (hom_of_le $ ln))],
      dsimp [above_point],
      simp_rw [←functor_to_types.map_comp_apply],
      reflexivity,} ⟩,
  by
  { obtain ⟨s,sec⟩ := ss,
    simp only [subtype.val_eq_coe, set.mem_set_of_eq, subtype.coe_mk],
    obtain ⟨y,k,jk,jk',rfl⟩ := sections_at_point_bwd_aux F j x ⟨s, @sec⟩ j,
    simp only [subtype.val_eq_coe, subtype.coe_mk],
    exact (s ⟨k,jk⟩).prop, } ⟩

def sections_at_point (j : J) (x : F.obj j) :
  {s : F.sections | s.val j = x} ≃ (above_point F j x).sections :=
{ to_fun := sections_at_point_fwd F j x,
  inv_fun := sections_at_point_bwd F j x,
  left_inv := by
  { rintro ⟨⟨s, sec⟩, sjx⟩,
    simp only [set.mem_set_of_eq] at sjx,
    induction sjx,
    apply subtype.mk_eq_mk.mpr, apply subtype.mk_eq_mk.mpr,
    funext i,
    obtain ⟨a,k,ki,kj,e⟩ := sections_at_point_bwd_aux F j (s j)
                              (sections_at_point_fwd F j (s j) ⟨⟨s, λ _ _, sec⟩,rfl⟩) i,
    simpa only [←sec (hom_of_le ki)] using e, },
  right_inv := by
  { rintro ⟨s, sec⟩,
    simp only [sections_at_point_fwd, sections_at_point_bwd, subtype.val_eq_coe, subtype.mk_eq_mk],
    funext i,
    obtain ⟨k,ki,kj,e⟩ := (sections_at_point_bwd_aux F j x ⟨s, @sec⟩ i).prop,
    simp only [←sec (hom_of_le (by {exact ki} : (⟨k,kj⟩ : {i | i ≤ j}) ≤ i)),
               subtype.val_eq_coe, ←subtype.coe_inj,set.maps_to.coe_restrict_apply] at e ⊢,
    obtain ⟨_,_⟩ := s ⟨k,kj⟩,
    -- magic going on here ^: deconstructing `s ⟨k,kj⟩` reverts `e`, which is actually nice for us
    exact id, } }

lemma sections_decomposition_at'
  [Π (j : J), fintype (F.obj j)] [∀ (j : J), nonempty (F.obj j)] (j : J) :
  F.sections ≃ Σ (x : F.obj j), (above_point F j x).sections :=
(sections_decomposition_at F j).trans (equiv.sigma_congr_right (sections_at_point F j))

lemma sections_surjective [Π (j : J), fintype (F.obj j)]
  (j : J) (Fsurj : ∀ i (ij : i ≤ j), function.surjective (F.map $ hom_of_le ij)) :
  function.surjective (λ (s : F.sections), s.val j) :=
begin
  rintro x,
  haveI : Π (j : J), nonempty (F.obj j), by
  { rintro i,
    obtain ⟨li,lj⟩ := (directed_of (≥) i j).some_spec,
    exact ⟨F.map (hom_of_le li) (Fsurj _ lj x).some⟩, },
  obtain ⟨s_above⟩ := above_point.sections_nonempty F j Fsurj x,
  obtain ⟨s,sjx⟩ := (sections_at_point F j x).inv_fun s_above,
  exact ⟨s,sjx⟩,
end

lemma sections_surjective' [Π (j : J), fintype (F.obj j)]
  (j : J) (Fsurj : ∀ (i j : J) (ij : i ≤ j), function.surjective (F.map $ hom_of_le ij)) :
  function.surjective (λ (s : F.sections), s.val j) :=
begin
  apply sections_surjective F j,
  rintro i ij, exact Fsurj i j ij,
end

lemma sections_fintype_to_injective
  [nonempty J] [Π (j : J), fintype (F.obj j)] [fintype F.sections]
  (Fsur : ∀ (i j : J) (ij : i ≤ j), function.surjective (F.map $ hom_of_le ij)) :
  ∃ j : J, ∀ i (ij : i ≤ j), function.injective (F.map $ hom_of_le ij) :=
begin
  have : Π (j : J), fintype.card (F.obj j) ≤ fintype.card F.sections, from
    λ j, fintype.card_le_of_surjective _ (sections_surjective' F j Fsur),
  let cards := set.range (λ j, fintype.card $ F.obj j),
  haveI cardsnem : cards.nonempty := set.range_nonempty (λ (j : J), fintype.card (F.obj j)),
  haveI cardsfin : cards.finite := by
  { apply set.finite.subset,
    exact {n : ℕ | n ≤ fintype.card ↥(functor.sections F)}.to_finite,
    rintro jm ⟨j,rfl⟩,
    exact this j,},
  let m := cardsfin.to_finset.max' ((set.finite.nonempty_to_finset cardsfin).mpr cardsnem),
  let mmem := cardsfin.to_finset.max'_mem ((set.finite.nonempty_to_finset cardsfin).mpr cardsnem),
  rw [set.finite.mem_to_finset, set.mem_range] at mmem,
  obtain ⟨j, jm⟩ := mmem,
  refine ⟨j, λ i ij, function.bijective.injective _⟩,
  rw fintype.bijective_iff_surjective_and_card,
  refine ⟨Fsur i j ij, _⟩,
  symmetry,
  apply (fintype.card_le_of_surjective _ (Fsur i j ij)).antisymm,
  rw jm,
  apply cardsfin.to_finset.le_max' (fintype.card $ F.obj i),
  simp only [set.finite.mem_to_finset, set.mem_range, exists_apply_eq_apply],
end

end inverse_system
-/
