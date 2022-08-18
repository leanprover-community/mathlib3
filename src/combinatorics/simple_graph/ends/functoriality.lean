import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic
import category_theory.category.basic
import category_theory.full_subcategory
import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import set_theory.cardinal.basic
import data.fintype.basic
import data.opposite



import .mathlib
import .reachable_outside
import .bwd_map
import .end_limit_construction


open function
open finset
open category_theory
open set
open classical
open simple_graph.walk
open relation

universes u v w


noncomputable theory
local attribute [instance] prop_decidable

namespace inverse_system

variables {J : Type u} [preorder J] [is_directed J ge] (F : J ⥤ Type v)
variables {I : Type u} [preorder I] [is_directed I ge] (G : I ⥤ Type v)

-- Tried finding a suitable "general" notion, but it's probably misguided for now
def sections_map
  (φ : I → J)
  (ψ : Π i, F.obj (φ i) → G.obj i)
  --(∀ i : I, ∃ j ≤ φ i, )
  : F.sections → G.sections := sorry

end inverse_system


open simple_graph
open simple_graph.ro_component


variables  {V : Type u}
           (G : simple_graph V)
           (Gpc : preconnected G)

           {V' : Type v}
           (G' : simple_graph V')
           (Gpc' : preconnected G')

           {V'' : Type w}
           (G'' : simple_graph V'')
           (Gpc'' : preconnected G'')





def cofinite (f : V → V') := ∀ x : V', (set.preimage f {x}).finite

lemma cofinite.list_preimage (f : V → V') (cof : cofinite f) : ∀ l : list V', (set.preimage f l.to_finset).finite :=
begin
  intro l,
  induction l,
  { simp only [list.to_finset_nil, coe_empty, set.preimage_empty, finite_empty], },
  { simp only [list.to_finset_cons, coe_insert],
    rw [set.insert_eq, set.preimage_union],
    apply set.finite.union,
    {apply cof,},
    {assumption,} }
end

lemma cofinite.finite_preimage (f : V → V') (cof : cofinite f) : ∀ S : set V', S.finite → (set.preimage f S).finite :=
begin
  intros S Sfin,
  rcases set.finite.exists_finset_coe Sfin with ⟨fS, hcoefin⟩,
  rcases (list.to_finset_surjective fS) with ⟨l, hcoelst⟩,
  rw [← hcoefin, ← hcoelst],
  apply cofinite.list_preimage _ cof,
end

lemma cofinite.finite_preimage_iff (f : V → V') : cofinite f ↔ ∀ S : set V', S.finite → (set.preimage f S).finite :=
⟨cofinite.finite_preimage _, λ h x, h {x} (set.finite_singleton x)⟩

lemma cofinite.comp {f : V → V'} {f' : V' → V''} (cof : cofinite f) (cof' : cofinite f') : cofinite (f' ∘ f) :=
begin
  intro x,
  rw [set.preimage_comp],
  apply cofinite.finite_preimage _ cof,
  apply cof',
end


lemma cofinite.id : cofinite (@id V) := by {intro,simp only [set.preimage_id, finite_singleton]}
lemma cofinite.of_inj {f : V → V'} (inj : function.injective f) : cofinite f := by
{ intro,dsimp only [set.preimage], sorry } -- can we show it constructively?


def cofinite.preimage {f : V → V'} (cof : cofinite f) (K : finset V') : finset V :=
set.finite.to_finset (cofinite.finite_preimage f cof K (finset.finite_to_set K))

@[simp]
lemma cofinite.preimage.coe {f : V → V'} (cof : cofinite f) (K : finset V') : ↑(cof.preimage K) = set.preimage f K :=
begin
  show ↑(set.finite.to_finset (cofinite.finite_preimage f cof K (finset.finite_to_set K))) = f⁻¹' ↑K,
  simp,
end

lemma cofinite.image_infinite {f : V → V'} (cof : cofinite f) (S : set V) (Sinf : S.infinite) :
  (f '' S).infinite := sorry


structure good_finset (f : V → V') (cof : cofinite f) (K : finset V') (L : finset V) :=
(pre : cofinite.preimage cof K ⊆ L)
(good : ∀ D : inf_ro_components' G L, {C : inf_ro_components' G' K | f '' D.val ⊆ C.val})
--                                     ^ note that this C is necessarily unique

lemma good_finset.agree (f : V → V') (cof : cofinite f) (K : finset V')
  (L L' : finset V) (LL' : L ⊆ L')
  (HL : good_finset G G' f cof K L)   (HL' : good_finset G G' f cof K L') :
  ∀ D : inf_ro_components' G L', (HL'.good D).val = (HL.good (bwd_map.bwd_map_inf G Gpc LL' D)).val :=
begin
  rintro D,
  sorry,
end


lemma good_finset.id (K : finset V) : good_finset G G (@id V) (cofinite.id) K K := by
{ split,
  {dsimp only [cofinite.preimage], rw ←finset.coe_subset, simp,},
  {rintro D, use D, simp only [id.def, set.image_id', mem_set_of_eq], } }

include Gpc
lemma good_finset.mono (f : V → V') (cof : cofinite f) (K : finset V')
  (L : finset V) (HL : good_finset G G' f cof K L) (L' : finset V) (LL' : L ⊆ L') :  good_finset G G' f cof K L' :=
begin
  split,
  exact HL.pre.trans LL',
  rintro D',
  obtain ⟨C,Csub⟩ := HL.good (bwd_map.bwd_map_inf G Gpc LL' D'),
  use C,
  apply subset.trans _ Csub,
  apply image_subset f _,
  apply bwd_map.bwd_map_inf.sub,
end

lemma good_finset.comono (f : V → V') (cof : cofinite f) (K : finset V') (K' : finset V') (K'K : K' ⊆ K)
  (L : finset V)  (HL : good_finset G G' f cof K L) : good_finset G G' f cof K' L := sorry

lemma good_finset.comp (f : V → V') (cof : cofinite f) (f' : V' → V'') (cof' : cofinite f')
  (K : finset V'')
  (L' : finset V') (HL' :  good_finset G' G'' f' cof' K L')
  (L : finset V) (HL :  good_finset G G' f cof L' L) :
  good_finset G G'' (f' ∘ f) (cofinite.comp cof cof') K L :=
⟨ by
  { apply finset.subset.trans _ HL.1,
    let HL'' := HL'.1,
    simp only [←finset.coe_subset, cofinite.preimage.coe] at HL'' ⊢,
    rw set.preimage_comp,
    apply set.preimage_mono,
    exact HL''}
, λ D,
  ⟨(HL'.2 (HL.2 D).val).val
  , by
    { apply subset.trans _ ((HL'.2 (HL.2 D).val).prop),
      rw set.image_comp,
      apply image_subset f' (HL.2 D).prop,}
    ⟩
⟩

/- Not so sure it's true, actually
lemma good_finset.inter( f : V → V') (cof : cofinite f) (K : finset V')
  (L L' : finset V) (H : L ∈  good_finset G G' f cof K) (H' : L' ∈  good_finset G G' f cof K) :
  L ∩ L' ∈ good_finset G G' f cof K :=
begin
  split, exact finset.subset_inter H.1 H'.1,
  rintro D,
  obtain ⟨C,CD⟩ := H.2 D,
  obtain ⟨C',CD'⟩ := H'.2 D,


end
-/

structure coarse :=
  (to_fun : V → V')
  (cof : cofinite to_fun)
  (coarse : ∀ (K : finset V'), Σ (L : finset V), good_finset G G' to_fun cof K L)

def coarse.id : (coarse G Gpc G) :=
{ to_fun := id
, cof := cofinite.id
, coarse := λ K, ⟨K, good_finset.id G K⟩ }

def coarse.comp (φ : coarse G Gpc G') (φ' : coarse G' Gpc' G'' ) : (coarse G Gpc G'') :=
{ to_fun := φ'.to_fun ∘ φ.to_fun
, cof := cofinite.comp φ.cof φ'.cof
, coarse := λ K,
  let
    ⟨L,HL⟩ := (φ'.coarse K)
  , ⟨L',HL'⟩ := (φ.coarse L)
  in
    ⟨L',good_finset.comp G Gpc G' G'' φ.to_fun φ.cof φ'.to_fun φ'.cof K L HL L' HL'⟩}


def coarse_to_ends [locally_finite G] [locally_finite G'] (φ : coarse G Gpc G') :
  Endsinfty G Gpc → Endsinfty G' Gpc' :=
begin
  rintro ⟨s,sec⟩,
  fsplit,
  { exact λ K, ((φ.coarse K).2.2 (s (φ.coarse K).1)).val, },
  { rintro K K' KK',                          -- Ugly proof, not sure how to have less haves and lets…
    have KsubK' : K' ⊆ K, from le_of_hom KK',
    --simp only [subtype.val_eq_coe, set.image_subset_iff],
    obtain ⟨L,HL⟩ := (φ.coarse K),
    obtain ⟨L',HL'⟩ := (φ.coarse K'),

    let L'' := L ∪ L',
    have LL : L ⊆ L'' := subset_union_left L L',
    have LL' : L' ⊆ L'' := subset_union_right L L',

    let D := s L,
    let D' := s L',
    let D'' := s L'',

    obtain ⟨C,HC⟩ := (HL.2 D),
    obtain ⟨C',HC'⟩ := (HL'.2 D'),

    symmetry,
    apply (bwd_map.bwd_map_inf.iff G' Gpc' KsubK' C' C).mpr,
    apply ro_component_subset_of_inter _ Gpc' K' K (KsubK') C'.val.val C'.val.prop C.val.val C.val.prop,

    have DC :  φ.to_fun '' D''.val.val ⊆ C.val.val, by
    { refine (image_subset φ.to_fun _).trans HC,
      exact (bwd_map.bwd_map_inf.iff G Gpc LL D D'').mp (sec (hom_of_le LL)).symm,},
    have DC' :  φ.to_fun '' D''.val.val ⊆ C'.val.val, by
    { refine  (image_subset φ.to_fun _).trans HC',
      exact (bwd_map.bwd_map_inf.iff G Gpc LL' D' D'').mp (sec (hom_of_le LL')).symm,},

    haveI : nonempty ↥(D''.val.val) := set.nonempty_coe_sort.mpr (set.infinite.nonempty D''.prop),
    let d := some (set.nonempty_coe_sort.mp $ set.image.nonempty φ.to_fun D''.val.val),
    let dD := some_spec (set.nonempty_coe_sort.mp $ set.image.nonempty φ.to_fun D''.val.val),
    use d, split, exact DC' dD, exact DC dD,},
end

def coarse_to_ends.id [locally_finite G] : coarse_to_ends G Gpc G Gpc (coarse.id G Gpc) = id :=
begin
  apply funext,
  rintro ⟨s,sec⟩,
  dsimp only [coarse_to_ends],
  simp only [id.def, set.image_id', subtype.val_eq_coe, subtype.mk_eq_mk],
  apply funext,
  rintro K,
  obtain ⟨L,HL⟩ := (coarse.id G Gpc).coarse K,
  have KL : K ⊆ L, by {have lol := HL.1,rw ←finset.coe_subset at lol, rw cofinite.preimage.coe at lol, dsimp [coarse.id] at lol, exact lol,},
  let HC := (HL.2 (s L)).2,

  apply subtype.ext, apply subtype.ext,
  apply ro_component.eq_of_common_subset G K
    ((HL.2 (s L))).val.val.val (s K).val.val
    ((HL.2 (s L))).val.val.prop (s K).val.prop,
  show (s L).val.val ⊆ ((HL.2 (s L))).val.val.val, by { dsimp [coarse.id] at HC, simp at HC,simp,exact HC,},
  show (s L).val.val ⊆ (s K).val.val, by
  { dsimp only [ComplInfComp] at *,
    apply (bwd_map.bwd_map_inf.iff G Gpc KL (s K) (s L)).mp _,
    let lol := sec (hom_of_le KL),
    exact lol.symm, -- strangely I can't do without the intermediate `let`
  },
  exact set.infinite.nonempty (s L).prop,
end

def coarse_to_ends.comp [locally_finite G] [locally_finite G'] [locally_finite G'']
  (φ : coarse G Gpc G')  (φ' : coarse G' Gpc' G'') :
  (coarse_to_ends G' Gpc' G'' Gpc'' φ') ∘ (coarse_to_ends G Gpc G' Gpc' φ) =
  coarse_to_ends G Gpc G'' Gpc'' (coarse.comp G Gpc G' Gpc' G'' φ φ') :=
begin
  apply funext,
  rintro ⟨s,sec⟩,

  dsimp only [coarse_to_ends],
  simp only [subtype.val_eq_coe, set.image_subset_iff, subtype.mk_eq_mk],
  apply funext,
  rintro K,
  apply subtype.ext, apply subtype.ext,
  dsimp only [subtype.val_eq_coe, set.image_subset_iff] at *,


  obtain ⟨L,HL⟩ := (φ'.coarse K),
  obtain ⟨M,HM⟩ := (φ.coarse L),

  obtain ⟨N,HN⟩ := ((coarse.comp G Gpc G' Gpc' G'' φ φ').coarse K),

  obtain ⟨C,HC⟩ := (HM.2 (s M)),
  obtain ⟨D,HD⟩ := (HL.2 C),

  obtain ⟨E,HE⟩ :=  (HN.2 (s N)),

  have HMN : (s (M ∪ N)).val.val ⊆ (s M).val.val, by
  { let lol := sec (hom_of_le (subset_union_left M N)),
    dsimp only [ComplInfComp] at lol, rw ←lol,
    apply bwd_map.bwd_map_inf.sub,},
  have HNM : (s (M ∪ N)).val.val ⊆ (s N).val.val, by
  { let lol := sec (hom_of_le (subset_union_right M N)),
    dsimp only [ComplInfComp] at lol, rw ←lol,
    apply bwd_map.bwd_map_inf.sub,},

  have : ↑↑D = ↑↑E, by {
    fapply ro_component.eq_of_common_subset G'' K ↑↑D ↑↑E D.val.prop E.val.prop,
    { exact (φ'.to_fun ∘ φ.to_fun) '' (s (M ∪ N)).val.val,},
    { rw set.image_comp,
      refine (image_subset φ'.to_fun _).trans _,rotate 3,
      exact φ.to_fun '' (s M).val.val,
      exact image_subset φ.to_fun HMN,
      apply subset.trans _ HD,
      apply image_subset φ'.to_fun HC, },
    { rw set.image_comp,
      refine (image_subset φ'.to_fun _).trans _,rotate 3,
      exact φ.to_fun '' (s N).val.val,
      exact image_subset φ.to_fun HNM,
      --dsimp only [coarse.comp] at HE,
      simp only [subtype.val_eq_coe],
      rw ←set.image_comp, exact HE, },
    { rw set.nonempty_image_iff,
      apply set.infinite.nonempty,
      apply (λ (C : inf_ro_components' G _), C.prop), },
  },
  exact this,

end


-- A function f is "coarse" if it has a good common finset with itself for each K if I'm not mistaken
structure good_common_finset {f g : V → V'} (cof : cofinite f) (cog : cofinite g) (K : finset V') (L : finset V) :=
(pref : cofinite.preimage cof K ⊆ L)
(preg : cofinite.preimage cof K ⊆ L)
(good : ∀ D : inf_ro_components' G L, {C : inf_ro_components' G' K | f '' D.val ⊆ C.val
                                                                   ∧ g '' D.val ⊆ C.val})

def coarse.close (φ ψ : coarse G Gpc G') :=
  Π (K : finset V'), Σ (L : finset V), good_common_finset G Gpc G' φ.cof ψ.cof K L

lemma coarse.close.eq_ends [locally_finite G] [locally_finite G']
 (φ ψ : coarse G Gpc G') (cl : coarse.close G Gpc G' φ ψ) :
  coarse_to_ends G Gpc G' Gpc' φ = coarse_to_ends G Gpc G' Gpc' ψ :=
begin
  dsimp only [coarse_to_ends],
  simp,
  apply funext,
  rintro ⟨s,sec⟩,
  simp,
  apply funext,
  rintro K,

  obtain ⟨L,HL⟩ := (φ.coarse K),
  obtain ⟨M,HM⟩ := (ψ.coarse K),
  obtain ⟨N,HN⟩ := (cl K),

  obtain ⟨C,HC⟩ := (HL.2 (s L)),
  obtain ⟨D,HD⟩ := (HM.2 (s M)),
  obtain ⟨E,HE⟩ := (HN.3 (s N)),

  let O := s (L ∪ M ∪ N),


  sorry, -- check that everything agrees
end



lemma coarse.close.refl (φ : coarse G Gpc G') : coarse.close G Gpc G' φ φ := sorry

/-
  Any map which is cofinite and coarsely Lipschitz
  (in the case for graphs, this means simply ∃m, ∀ (u v), G.adj u v → dist (f u) (f v) ≤ m)
  is coarse in the present sense.
  So, assume f is coarsely Lipschitz with constant m as above, and cofinite.
  Given K, we must find a good_finset L for K.
  We choose `K' = {x : V | exists k : K, d k x ≤ m}`, i.e. the m-neighborhood of K, and `L := f⁻¹ K'`
  Now, clearly f '' L contains K.
  Fix D an infinite ro component for L, since D does not intersect L, f '' D does not intersect K'.
  Thus, f '' D is contained in the union of all ro components for K', and a fortiori for K.
  If f '' D is entirely contained in one such C, then C must be infinite, since f '' D is infinite (f being cofinite and D infinite).
  It remains to check that f '' D really is contained in one such C.
  Assume that f '' D intersects C and C' (assumed unequal). Since D is connected, f '' D is "m-connected" in the sense that
  any two elements of f '' D can be joined by a sequence of elements of f '' D each at a distance at most k from its successor/predecessor.
  Fix c ∈ C ∩ (f '' D) and c' ∈ C' ∩ (f '' D) and take such an "m-path" c = c₀ , c₁ , …, cₙ = c'.
  There is a last cᵢ contained in C, and necessarily cᵢ₊₁ is not contained in C, and not in K either, thus
  wlog is contained in C'.
  In summary, we have some c ∈ C ∩ (f'' D) and c' ∈ C' ∩ (f'' D) joined by a path w of length at most m.
  Then w must pass through K, since otherwise we'd have a path outside of K joining C and C', hence they would be equal ro components.
  But now note that c c' ∉ K', obviously, meaning that c and c' are "far" from K, and the existence of this path w intersecting K is a contradiction.


-/


/-
def qi_embedding (f : V → V') : Prop := sorry -- ∃ (K : ℕ), ∀ (u v : V), dist (f u) (f v) ≤ K * (dist u v) + K ∧ dist u v ≤ K * (dist (f u) (f v)) + K

def coarse.of_qi_embedding (f : V → V') (qie : qi_embedding f) : coarse G G' f := sorry

def coarse.comp {f : V → V'} {f' : V' → V''} (coa : coarse G G' f) (coa' : coarse G' G'' f') : coarse G G'' (f' ∘ f) := sorry

def ends_map {f : V → V'} (coa : coarse G G' f) : @ends V G → @ends V' G' := sorry


-/
