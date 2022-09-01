import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import data.setoid.partition
import category_theory.filtered
import topology.category.Top.limits
import data.finset.basic
import category_theory.category.basic
import category_theory.full_subcategory
import data.fintype.basic
import data.opposite
import combinatorics.simple_graph.metric


import .comp_out
import .mathlib
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

lemma cofinite.image_infinite {f : V → V'} (cof : cofinite f) {S : set V} (Sinf : S.infinite) :
  (f '' S).infinite := sorry


def good_finset (f : V → V') (K : finset V') (L : finset V) :=
  Π D : inf_comp_out G L, {C : inf_comp_out G' K | f '' (D : set V) ⊆ C}


lemma good_finset.eq {f : V → V'} {K : finset V'} {L : finset V}
  (HL HL' : good_finset G G' f K L)  : HL = HL' :=
begin
  apply funext,
  rintro D,
  ext,
  apply comp_out.eq_of_not_disjoint,
  rw set.not_disjoint_iff,
  apply comp_out.eq_of_common_subset G' K (HL D).val.val.val (HL' D).val.val.val
    (HL D).val.val.prop (HL' D).val.val.prop (f '' D.val.val) (HL D).prop (HL' D).prop,
  exact set.nonempty.image f (set.infinite.nonempty D.prop),
end

lemma good_finset.agree_up {f : V → V'} {K : finset V'}
  {L L' : finset V} {LL' : L ⊆ L'}
  (HL : good_finset G G' f K L)   (HL' : good_finset G G' f K L') :
  ∀ D : inf_ro_components' G L', (HL' D).val = (HL (bwd_map_inf G Gpc LL' D)).val :=
begin
  rintro D,
  apply subtype.ext, apply subtype.ext,
  --↑↑((HL' D).val) = ↑↑((HL (bwd_map_inf G Gpc LL' D)).val)
  apply ro_component.eq_of_common_subset G' K (HL' D).val.val.val (HL (bwd_map_inf G Gpc LL' D)).val.val.val
    (HL' D).val.val.prop (HL (bwd_map_inf G Gpc LL' D)).val.val.prop (f '' D.val.val),
  { exact (HL' D).prop,},
  { refine subset.trans _ (HL (bwd_map_inf G Gpc LL' D)).prop,
    apply set.image_subset,
    apply bwd_map_inf.sub,},
  { exact set.nonempty.image f (set.infinite.nonempty D.prop) },
end

lemma good_finset.agree_down {f : V → V'} {K K': finset V'} {KK' : K ⊆ K'}
  {L : finset V}   (HK : good_finset G G' f K L) (HK' : good_finset G G' f K' L) :
   ∀ D : inf_ro_components' G L, (HK D).val = bwd_map_inf G' Gpc' KK' (HK' D).val :=
  begin
    rintro D,
    apply subtype.ext, apply subtype.ext,

    apply ro_component.eq_of_common_subset G' K
      (HK D).val.val.val
      (bwd_map_inf G' Gpc' KK' (HK' D).val).val.val
      (HK D).val.val.prop
      (bwd_map_inf G' Gpc' KK' (HK' D).val).val.prop
      (f '' D.val.val),
      { exact (HK D).prop, },
      { refine subset.trans _ (bwd_map_inf.sub G' Gpc' KK' (HK' D).val), exact (HK' D).prop},
      { exact set.nonempty.image f (set.infinite.nonempty D.prop) },
  end


lemma good_finset.up {f : V → V'} {K : finset V'}
  {L L' : finset V}   (HL : good_finset G G' f K L) (LL' : L ⊆ L') : good_finset G G' f K L' :=
λ D, ⟨(HL (bwd_map_inf G Gpc LL' D)).val,  sorry⟩
-- a component for L' is containd in one for L and thus the image is also contained and thus in blah

lemma good_finset.down {f : V → V'} {K K': finset V'}
  {L : finset V}   (HL : good_finset G G' f K' L) (KK' : K ⊆ K') : good_finset G G' f K L :=
λ D, ⟨(bwd_map_inf G' Gpc' KK' (HL D).val), sorry⟩


def good_finset.id (K : finset V) : good_finset G G (@id V) K K :=
λ D, ⟨D,by { rw (set.image_id ↑(D.val)), exact set.subset.refl ↑(D.val), }⟩


def good_finset.comp (f : V → V') (f' : V' → V'')
  (K : finset V'') (L' : finset V') (HL' :  good_finset G' G'' f' K L')
  (L : finset V)  (HL :  good_finset G G' f  L' L) :
  good_finset G G'' (f' ∘ f) K L :=
 λ D,
  ⟨(HL' (HL D).val).val
  , by
    { apply subset.trans _ ((HL' (HL D).val).prop),
      rw set.image_comp,
      apply image_subset f' (HL D).prop,}
  ⟩


def coarse (f : V → V') := ∀ (K : finset V'), Σ (L : finset V), good_finset G G' f K L

def coarse.id : coarse G G (@id V) := λ K, ⟨K, good_finset.id G K⟩

def coarse.comp' {f : V → V'} {f' : V' → V''} (fc : coarse G G' f) (fc' : coarse G' G'' f') :
 coarse G G'' (f' ∘ f) := λ K,
  let
    ⟨L,H⟩ := fc' K
  , ⟨L',H'⟩ := fc L
  in
    ⟨L',good_finset.comp G  G' G'' f f' K L H L' H'⟩

def coarse.comp {f : V → V'} {f' : V' → V''} (fc : coarse G G' f) (fc' : coarse G' G'' f') :
 coarse G G'' (f' ∘ f) := λ K,
  ⟨ (fc (fc' K).1).1
  , good_finset.comp G  G' G'' f f' K (fc' K).1 (fc' K).2 (fc (fc' K).1).1 (fc (fc' K).1).2
  ⟩

def coarse.Endsinfty [locally_finite G] [locally_finite G'] {f : V → V'} (fc : coarse G G' f) :
  Endsinfty G Gpc → Endsinfty G' Gpc' :=
begin
  rintro ⟨s,sec⟩,
  fsplit,
  { exact λ K, ((fc K).2 (s (fc K).1)).val, },
  { rintro K K' KK',                          -- Ugly proof, not sure how to have less haves and lets…
    have KsubK' : K' ⊆ K, from le_of_hom KK',
    --simp only [subtype.val_eq_coe, set.image_subset_iff],
    obtain ⟨L,H⟩ := (fc K),
    obtain ⟨L',H'⟩ := (fc K'),

    let L'' := L ∪ L',
    have LL : L ⊆ L'' := subset_union_left L L',
    have LL' : L' ⊆ L'' := subset_union_right L L',

    let dG := bwd_map_inf G Gpc LL,
    let dG' := bwd_map_inf G Gpc LL',
    let d := bwd_map_inf G' Gpc' KsubK',

    let uH := good_finset.up G Gpc G' H LL,
    let uH' := good_finset.up G Gpc G' H' LL',

    dsimp [ComplInfComp] at sec ⊢,
    symmetry,
    calc (H' (s L')).val
       = (H' (dG' (s L''))).val : congr_arg (λ x, (H' x).val) (sec (hom_of_le LL')).symm
    ...= (uH' (s L'')).val      : by {symmetry, apply good_finset.agree_up,}
    ...= d (uH (s L'')).val     : by {apply good_finset.agree_down,}
    ...= d (H (dG (s L''))).val : by {apply congr_arg d, apply good_finset.agree_up,}
    ...= d (H (s L)).val        : by {apply congr_arg (λ x, d (H x).val), exact(sec (hom_of_le LL))},
  },
end

def coarse.Endsinfty.ext [locally_finite G] [locally_finite G'] {f : V → V'}
  (c c' : coarse G G' f) :
  coarse.Endsinfty G Gpc G' Gpc' c = coarse.Endsinfty G Gpc G' Gpc' c' :=
begin
  apply funext, rintro ⟨s,sec⟩,
  dsimp only [coarse.Endsinfty],
  simp only [subtype.val_eq_coe, subtype.mk_eq_mk],
  apply funext, rintro K,
  obtain ⟨L,H⟩ := (c K),
  obtain ⟨L',H'⟩ := (c' K),
  let L'' := L ∪ L',
  have LL : L ⊆ L'' := subset_union_left L L',
  have LL' : L' ⊆ L'' := subset_union_right L L',
  let uH := good_finset.up G Gpc G' H LL,
  let uH' := good_finset.up G Gpc G' H' LL',

  simp only,
  calc    (H (s L)).val
        = (H (bwd_map_inf G Gpc LL (s L''))).val   : congr_arg (λ x, (H x).val) (sec (hom_of_le LL)).symm
  ...   = (uH (s L'')).val                         : by {symmetry, apply good_finset.agree_up,}
  ...   = (uH' (s L'')).val                        : by {rw good_finset.eq G G' uH uH',}
  ...   = (H' (bwd_map_inf G Gpc LL' (s L''))).val : by {apply good_finset.agree_up}
  ...   = (H' (s L')).val                          : congr_arg (λ x, (H' x).val) (sec (hom_of_le LL')),


end

def coarse.Endsinfty_comp [locally_finite G] [locally_finite G'] [locally_finite G'']
  {f : V → V'} {f' : V' → V''} (fc : coarse G G' f ) (fc' : coarse G' G'' f') :
  coarse.Endsinfty G Gpc G'' Gpc'' (coarse.comp G G' G'' fc fc') = (coarse.Endsinfty G' Gpc' G'' Gpc'' fc') ∘ (coarse.Endsinfty G Gpc G' Gpc' fc) :=
begin
  apply funext,
  rintro ⟨s,sec⟩,
  refl,
end

def coarse.Endsinfty_id [locally_finite G] : coarse.Endsinfty G Gpc G Gpc (coarse.id G) = id :=
begin
  apply funext,
  rintro ⟨s,sec⟩,
  refl,
end

def good_common_finset (f g : V → V') (K : finset V') (L : finset V) :=
  Π D : inf_ro_components' G L, {C : inf_ro_components' G' K | f '' D.val ∪ g '' D.val ⊆ C.val}

def good_common_finset.left {f g : V → V'} {K : finset V'} {L : finset V} :
  (good_common_finset G G' f g K L) → good_finset G G' f K L :=
λ c D, ⟨(c D).1,(subset_union_left (f '' D) (g '' D)).trans (c D).2⟩

def good_common_finset.right {f g : V → V'} {K : finset V'} {L : finset V} :
  (good_common_finset G G' f g K L) → good_finset G G' g K L :=
λ c D, ⟨(c D).1,(subset_union_right (f '' D) (g '' D)).trans (c D).2⟩

def good_common_finset.refl {f : V → V'} {K : finset V'} {L : finset V} :
  (good_finset G G' f K L) → good_common_finset G G' f f K L :=
λ c D, ⟨(c D).1,by {simp only [subtype.val_eq_coe, set.union_self, mem_set_of_eq], exact (c D).2, }⟩



def good_common_finset.symm {f g : V → V'} {K : finset V'} {L : finset V} :
  (good_common_finset G G' f g K L) → good_common_finset G G' g f K L :=
λ c D, ⟨(c D).1,by {simp only [subtype.val_eq_coe, mem_set_of_eq],rw set.union_comm, exact (c D).2, }⟩

def good_common_finset.trans {f g h : V → V'} {K : finset V'} {L : finset V} :
  (good_common_finset G G' f g K L) → good_common_finset G G' g h K L → good_common_finset G G' f h K L :=
λ cfg cgh D,
begin
  have : (cfg D).1 = (cgh D).1, by
  { have : cfg.right G G' = cgh.left G G', by apply good_finset.eq,
    change (cfg.right G G' D).1 = (cgh.left G G' D).1,
    rw this,},
  use (cfg D).1,
  let subfg := (cfg D).2,
  let subgh := (cgh D).2, rw ←this at subgh,
  simp only [subtype.val_eq_coe, mem_set_of_eq,set.union_subset_iff] at subfg subgh ⊢,
  exact ⟨subfg.left,subgh.right⟩,
end

def good_common_finset.up {f g : V → V'} {K : finset V'}  {L L' : finset V} (LL' : L ⊆ L') :
  (good_common_finset G G' f g K L) → good_common_finset G G' f g K L'  :=
λ c D,
  ⟨ (c (bwd_map_inf G Gpc LL' D)).1
  , by
    { refine subset.trans _ (c (bwd_map_inf G Gpc LL' D)).2,
      apply set.union_subset_union; apply image_subset; apply bwd_map_inf.sub, }
  ⟩

-- Probably we also need versions of the `agree_up` `agree_down` and `up` `down` constructions for `good_finset`.


def coarse_close (f g : V → V') :=
  Π (K : finset V'), Σ (L : finset V), good_common_finset G G' f g K L

def coarse_close.left {f g : V → V'} :
  coarse_close G G' f g → coarse G G' f :=
λ icc K, ⟨(icc K).1, good_common_finset.left G G' (icc K).2⟩

def coarse_close.right {f g : V → V'} :
  coarse_close G G' f g → coarse G G' g :=
λ icc K, ⟨(icc K).1, good_common_finset.right G G' (icc K).2⟩

def coarse_close.refl {f : V → V'} :
  coarse G G' f → coarse_close G G' f f :=
λ ic K, ⟨(ic K).1, good_common_finset.refl G G' (ic K).2 ⟩

def coarse_close.symm (f g : V → V') :
  coarse_close G G' f g → coarse_close G G' g f :=
λ icc K, ⟨(icc K).1, good_common_finset.symm G G' (icc K).2 ⟩

def coarse_close.trans (f g h : V → V') :
  coarse_close G G' f g → coarse_close G G' g h → coarse_close G G' f h :=
λ iccfg iccgh K,
  ⟨ (iccfg K).1 ∪ (iccgh K).1
  , good_common_finset.trans G G'
      (good_common_finset.up G Gpc G' (subset_union_left (iccfg K).1 (iccgh K).1) (iccfg K).2)
      (good_common_finset.up G Gpc G' (subset_union_right (iccfg K).1 (iccgh K).1) (iccgh K).2)
  ⟩


lemma coarse_close.Endsinfty.eq [locally_finite G] [locally_finite G']
  {f g : V → V'} (icc : coarse_close G G' f g) :
  coarse.Endsinfty G Gpc G' Gpc' (coarse_close.left G G' icc) = coarse.Endsinfty G Gpc G' Gpc' (coarse_close.right G G' icc) :=
begin
  apply funext, rintro ⟨s,sec⟩,
  refl,
end

lemma coarse_close.Endsinfty.eq' [locally_finite G] [locally_finite G']
  {f g : V → V'}
  (icc : coarse_close G G' f g) (fc : coarse G G' f) (gc : coarse G G' g) :
  fc.Endsinfty G Gpc G' Gpc' = gc.Endsinfty G Gpc G' Gpc' :=
  (coarse.Endsinfty.ext G Gpc G' Gpc' fc (icc.left G G')).trans
  ( (coarse_close.Endsinfty.eq G Gpc G' Gpc' icc).trans
      (coarse.Endsinfty.ext G Gpc G' Gpc' gc (icc.right G G')).symm)



def coarse_Lipschitz (f : V → V') (K : ℕ) := ∀ (x y : V) (a : G.adj x y), (G'.dist (f x) (f y)) ≤ K



private def thicken (G : simple_graph V) (K : finset V) (m : ℕ) : finset V :=
begin
  let K'set := {v : V | ∃ k ∈ K, G.dist v k ≤ m},
  have : K'set.finite := sorry, -- locally finite TODO: WIP approach in `.mathlib.lean`
  exact this.to_finset,
end

private lemma thicken.sub (G : simple_graph V) (K : finset V) (m : ℕ) :
  K ⊆ thicken G K m :=
begin
  rintro k kK,
  dsimp [thicken],
  simp only [finite.mem_to_finset, mem_set_of_eq, exists_prop],
  use k, split, exact kK,
  rw (dist_self : G.dist k k = 0),
  apply zero_le,
end

private lemma thicken.eq (G : simple_graph V) (K : finset V) (m : ℕ) :
  (thicken G K m : set V) = {v : V | ∃ k ∈ K, G.dist v k ≤ m} := sorry

private lemma well_separated (G : simple_graph V) (Gpc : G.preconnected) (K : finset V) (m : ℕ)
  (C : ro_components G K)
  (c : V) (cC : c ∈ C.val) (c' : V) :
  c ∉ (thicken G K m) → G.dist c c' ≤ m → c' ∈ C.val :=
begin
  rintro cnK,
  obtain ⟨w,wm⟩ := reachable.exists_walk_of_dist (Gpc c c'), rw ←wm,
  rintro hwm,
  have wdisK : disjoint w.support.to_finset K, by {
    by_contradiction h, rw finset.not_disjoint_iff at h,
    obtain ⟨x,xw,xK⟩ := h,
    rw [list.mem_to_finset,walk.mem_support_iff_exists_append] at xw,
    obtain ⟨cx,_,rfl⟩ := xw,
    apply cnK,
    dsimp only [thicken],
    simp only [finite.mem_to_finset, mem_set_of_eq, exists_prop],
    use [x,xK],
    apply (dist_le cx).trans,
    refine le_trans _ hwm,
    simp only [length_append, le_add_iff_nonneg_right, zero_le'],
  },
  apply mem_of_mem_of_ro G K C.val C.prop c c' cC ⟨w,wdisK.symm⟩,
end


include Gpc'
def coarse.of_coarse_Lipschitz_of_cofinite (f : V → V') (m : ℕ)
  (fcl : coarse_Lipschitz G G' f m) (cof : cofinite f) : coarse G G' f :=
λ K,
⟨ cof.preimage $ thicken G' K m
, by {

  let K' := thicken G' K m,
  let L := cof.preimage K',

  rintro D,
  have disDK' : disjoint (f '' D.val) K', by
  { rw set.disjoint_iff,
    rintro x ⟨⟨y,⟨yD,rfl⟩⟩,xK⟩,
    have : y ∈ L, by {rw ←set.mem_preimage at xK, rw ←cofinite.preimage.coe cof at xK, exact xK},
    apply not_in_of_in_comp G L D.val.val D.val.prop y yD this,},

  have disDK : disjoint (f '' D.val) K := set.disjoint_of_subset_right (thicken.sub G' K m) disDK',
  have  fDinf: (f '' D.val.val : set V').infinite := cofinite.image_infinite cof D.prop,
  let d := fDinf.nonempty.some,
  have dfD := fDinf.nonempty.some_spec,
  have dnK : d ∉ K := λ dK, (disDK.ne_of_mem dfD dK) (refl d),
  have dnK'' : d ∉ K' := λ dK', (disDK'.ne_of_mem dfD dK') (refl d),

  let C := ro_component.of G' K d,
  have Ccomp := ro_component.of_in_components G' K d dnK,
  have dC := ro_component.mem_of G' K d dnK,

  suffices : f '' D.val ⊆ C,
  { use [C,ro_component.of_in_components G' K d dnK, set.infinite.mono this fDinf, this], },

  rintro d' ⟨e',⟨heD',hed'⟩⟩,
  rcases dfD with ⟨e,⟨heD,hed⟩⟩,
  obtain ⟨w,wD⟩ := ro_component.to_subconnected G L D.val.val D.val.prop e heD e' heD',

  by_contradiction,
  have efC : e ∈ set.preimage f C, by {simp only [set.mem_preimage],rw hed,exact dC},
  have efC' : e' ∉ set.preimage f C, by {simp only [set.mem_preimage],rw hed', exact h},
  obtain ⟨x,y,_,a,_,rfl,xC,yC⟩ := w.split_along_set (set.preimage f C) efC efC',
  suffices : y ∈ set.preimage f C, { exact yC this, },
  apply well_separated G' Gpc' K m (⟨C,Ccomp⟩) (f x) _ (f y) _ (fcl x y a),
  { change x ∈ set.preimage f C, apply mem_of_subset_of_mem xC, simp only [mem_coe, list.mem_to_finset, end_mem_support],  }, -- x is containde in a path containde in f⁻¹ C
  have xD : x ∈ D.val.val, by {apply mem_of_subset_of_mem wD,simp only [mem_coe, list.mem_to_finset, mem_support_append_iff, end_mem_support, true_or],}, -- x lies in w, w is containde in D
  have fxnK' : f x ∉ K' := λ fxK', (disDK'.ne_of_mem (mem_image_of_mem f xD) fxK') (refl (f x)),
  exact fxnK',
}⟩


include Gpc
def coarse_close.of_close_of_coarse_Lipschitz_of_cofinite (f g : V → V')
  (m : ℕ) (clf : coarse_Lipschitz G G' f m) (clg : coarse_Lipschitz G G' g m)
  (cof : cofinite f) (cog : cofinite g) (close : ∀ v, G'.dist (f v) (g v) ≤ m) : coarse_close G G' f g :=
begin
  rintro K,

  let K' := thicken G' K m,

  let Lf := (coarse.of_coarse_Lipschitz_of_cofinite G G' Gpc' f m clf cof K).1,
  let Hf := (coarse.of_coarse_Lipschitz_of_cofinite G G' Gpc' f m clf cof K).2,
  have Lfdef : (Lf : set V) = set.preimage f K', by {
    rw [←cofinite.preimage.coe cof K', finset.coe_inj], refl,},
  -- If I do `obtain ⟨Lf,Hf⟩ := …` the proof of `Lfdef` doesn't work anymore.
  -- I believe that's because `obtain` uses `have` which doesn't allow "unfolding" the defs.
  obtain ⟨Lg,Hg⟩ := coarse.of_coarse_Lipschitz_of_cofinite G G' Gpc' g m clg cog K,

  use Lf ∪ Lg,
  let Hf' := good_finset.up G Gpc G' Hf (finset.subset_union_left Lf Lg),
  let Hg' := good_finset.up G Gpc G' Hg (finset.subset_union_right Lf Lg),

  rintro D,
  suffices hh : (Hf' D).val = (Hg' D).val,
  { use (Hf' D).val,
    simp only [subtype.val_eq_coe, set.union_subset_iff, set.image_subset_iff, mem_set_of_eq],
    split,
    { have := (Hf' D).prop,
      simp only [subtype.val_eq_coe, set.image_subset_iff, mem_set_of_eq] at this,
      exact this, },
    { have := (Hg' D).prop,
      simp only [subtype.val_eq_coe, set.image_subset_iff, mem_set_of_eq] at this hh,
      rw ←hh at this,
      exact this, }
  },


  let d := D.prop.nonempty.some,
  have dD := D.prop.nonempty.some_spec,
  let c := f d,
  let c' := g d,
  have cC : c ∈ (Hf' D).val.val.val, by {refine mem_of_mem_of_subset _ (Hf' D).prop, exact ⟨d,dD,refl c⟩,},
  have cC' : c' ∈ (Hg' D).val.val.val, by {refine mem_of_mem_of_subset _ (Hg' D).prop, exact ⟨d,dD,refl c'⟩,},
  have cnK : c ∉ K', by
  { rintro cK',
    have : d ∈ Lf ∪ Lg, by
    { simp only [finset.mem_union],
      left,
      rw [←finset.mem_coe, Lfdef, set.mem_preimage],
      exact cK', },
    apply not_in_comp_of_in G (Lf ∪ Lg) D.val.val D.val.prop d this dD,
  },

  apply subtype.ext, apply subtype.ext,
  apply eq_of_common_mem G' K _ _ (Hf' D).val.val.prop (Hg' D).val.val.prop c' _ cC',
  apply well_separated G' Gpc' K m (Hf' D).val.val c cC c' cnK (close d),

end

/-
def qi_embedding (f : V → V') : Prop := sorry -- ∃ (K : ℕ), ∀ (u v : V), dist (f u) (f v) ≤ K * (dist u v) + K ∧ dist u v ≤ K * (dist (f u) (f v)) + K

def coarse.of_qi_embedding (f : V → V') (qie : qi_embedding f) : coarse G G' f := sorry

def coarse.comp {f : V → V'} {f' : V' → V''} (coa : coarse G G' f) (coa' : coarse G' G'' f') : coarse G G'' (f' ∘ f) := sorry

def ends_map {f : V → V'} (coa : coarse G G' f) : @ends V G → @ends V' G' := sorry


-/
