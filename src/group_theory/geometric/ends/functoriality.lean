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
import .for_mathlib.misc
import .ends
import .for_mathlib.cofinite


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
  obtain ⟨d,dD⟩ := set.nonempty.image f (set.infinite.nonempty D.prop),
  use [d,(HL D).prop dD,(HL' D).prop dD],
end

lemma good_finset.agree_up {f : V → V'} {K : finset V'}
  {L L' : finset V} {LL' : L ⊆ L'}
  (HL : good_finset G G' f K L)   (HL' : good_finset G G' f K L') :
  ∀ D : G.inf_comp_out L', (HL' D).val = (HL (D.back LL')).val :=
begin
  rintro D,
  ext,
  apply comp_out.eq_of_not_disjoint, rw set.not_disjoint_iff,
  obtain ⟨d,dD⟩ := set.nonempty.image f (set.infinite.nonempty D.prop),
  use [d,(HL' D).prop dD],
  apply (HL (D.back LL')).prop,
  apply set.image_subset f,
  apply comp_out.back_sub, exact dD,
end

lemma good_finset.agree_down {f : V → V'} {K K': finset V'} {KK' : K ⊆ K'}
  {L : finset V}   (HK : good_finset G G' f K L) (HK' : good_finset G G' f K' L) :
   ∀ D : G.inf_comp_out L, (HK D).val = (HK' D).val.back KK' :=
begin
  rintro D,
  ext,
  apply comp_out.eq_of_not_disjoint, rw set.not_disjoint_iff,
  obtain ⟨d,dD⟩ := set.nonempty.image f (set.infinite.nonempty D.prop),
  use [d,(HK D).prop dD],
  apply comp_out.back_sub,
  apply (HK' D).prop,
  exact dD,
end


lemma good_finset.up {f : V → V'} {K : finset V'}
  {L L' : finset V}   (HL : good_finset G G' f K L) (LL' : L ⊆ L') : good_finset G G' f K L' :=
λ D, ⟨(HL (D.back LL')).val,  sorry⟩
-- a component for L' is containd in one for L and thus the image is also contained and thus in blah

lemma good_finset.down {f : V → V'} {K K': finset V'}
  {L : finset V}   (HL : good_finset G G' f K' L) (KK' : K ⊆ K') : good_finset G G' f K L :=
λ D, ⟨(HL D).val.back KK', sorry⟩


def good_finset.id (K : finset V) : good_finset G G (@id V) K K :=
λ D, ⟨D,by { rw set.image_id ↑D, exact set.subset.refl ↑(D.val), }⟩


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

def coarse.Endsinfty {f : V → V'} (fc : coarse G G' f) :
  Endsinfty G → Endsinfty G' :=
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

    let dG := (λ C : G.inf_comp_out L'', C.back LL),
    let dG' := (λ C : G.inf_comp_out L'', C.back LL'),
    let d := (λ C : G'.inf_comp_out K, C.back KsubK'),

    let uH := good_finset.up G G' H LL,
    let uH' := good_finset.up G G' H' LL',

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

def coarse.Endsinfty.ext {f : V → V'} (c c' : coarse G G' f) :
  coarse.Endsinfty G G' c = coarse.Endsinfty G G' c' :=
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
  let uH := good_finset.up G G' H LL,
  let uH' := good_finset.up G G' H' LL',

  simp only,
  calc (H (s L)).val
     = (H (inf_comp_out.back LL (s L''))).val   : congr_arg (λ x, (H x).val) (sec (hom_of_le LL)).symm
  ...= (uH (s L'')).val                         : by {symmetry, apply good_finset.agree_up,}
  ...= (uH' (s L'')).val                        : by {rw good_finset.eq G G' uH uH',}
  ...= (H' (inf_comp_out.back LL' (s L''))).val : by {apply good_finset.agree_up}
  ...= (H' (s L')).val                          : congr_arg (λ x, (H' x).val) (sec (hom_of_le LL')),


end

def coarse.Endsinfty_comp_apply {f : V → V'} {f' : V' → V''}
  (fc : coarse G G' f ) (fc' : coarse G' G'' f') (e : Endsinfty G) :
  coarse.Endsinfty G G'' (coarse.comp G G' G'' fc fc') e
  = (coarse.Endsinfty G' G'' fc') ( (coarse.Endsinfty G G' fc) e) :=
by { rcases e with ⟨s,sec⟩, refl, }

def coarse.Endsinfty_comp {f : V → V'} {f' : V' → V''}
  (fc : coarse G G' f ) (fc' : coarse G' G'' f') :
  coarse.Endsinfty G G'' (coarse.comp G G' G'' fc fc')
  = (coarse.Endsinfty G' G'' fc') ∘ (coarse.Endsinfty G G' fc) :=
by { funext, apply coarse.Endsinfty_comp_apply, }

def coarse.Endsinfty_id_apply [locally_finite G] (e : Endsinfty G) :
  coarse.Endsinfty G G (coarse.id G) e = e :=
by { rcases e with ⟨s,sec⟩, refl, }

def coarse.Endsinfty_id [locally_finite G] : coarse.Endsinfty G G (coarse.id G) = id :=
by { funext, apply coarse.Endsinfty_id_apply, }

def good_common_finset (f g : V → V') (K : finset V') (L : finset V) :=
  Π D : G.inf_comp_out L, {C : G'.inf_comp_out K | f '' D.val ∪ g '' D.val ⊆ C.val}

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
  ⟨ (c (D.back LL')).1
  , by
    { refine subset.trans _ (c (D.back LL')).2,
      apply set.union_subset_union; apply image_subset; apply comp_out.back_sub, }
  ⟩


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
      (good_common_finset.up G G' (subset_union_left (iccfg K).1 (iccgh K).1) (iccfg K).2)
      (good_common_finset.up G G' (subset_union_right (iccfg K).1 (iccgh K).1) (iccgh K).2)
  ⟩


lemma coarse_close.Endsinfty.eq
  {f g : V → V'} (icc : coarse_close G G' f g) :
  coarse.Endsinfty G G' (coarse_close.left G G' icc)
  = coarse.Endsinfty G G' (coarse_close.right G G' icc) :=
begin
  apply funext, rintro ⟨s,sec⟩,
  refl,
end

lemma coarse_close.Endsinfty.eq' {f g : V → V'}
  (icc : coarse_close G G' f g) (fc : coarse G G' f) (gc : coarse G G' g) :
  fc.Endsinfty G G' = gc.Endsinfty G G' :=
  (coarse.Endsinfty.ext G G' fc (icc.left G G')).trans
  ( (coarse_close.Endsinfty.eq G G' icc).trans
      (coarse.Endsinfty.ext G G' gc (icc.right G G')).symm)



def coarse_Lipschitz (f : V → V') (K : ℕ) := ∀ (x y : V) (a : G.adj x y), (G'.dist (f x) (f y)) ≤ K
lemma coarse_Lipschitz.id (K : ℕ) (Kge : K ≥ 1) : coarse_Lipschitz G G id K := sorry
lemma coarse_Lipschitz.comp (K L : ℕ) (f : V → V') (g : V' → V'') :
  coarse_Lipschitz G G' f K → coarse_Lipschitz G' G'' g L → coarse_Lipschitz G G'' (g ∘ f) (K*L) := sorry
lemma coarse_Lipschitz.mono (f : V → V') (K L : ℕ) (h : K ≤ L) :
  coarse_Lipschitz G G' f K → coarse_Lipschitz G G' f L := sorry

private lemma well_separated (G : simple_graph V) (Gpc : G.preconnected) (K : finset V) (m : ℕ)
  (C : G.comp_out K)
  (c : V) (cC : c ∈ C) (c' : V) :
  c ∉ (thicken_ G K m) → G.dist c c' ≤ m → c' ∈ C :=
begin
  rintro cnK,
  obtain ⟨w,wm⟩ := reachable.exists_walk_of_dist (Gpc c c'), rw ←wm,
  rintro hwm,
  have wdisK : disjoint (w.support.to_finset : set V) K, by {
    rw finset.disjoint_coe,
    by_contradiction h, rw finset.not_disjoint_iff at h,
    obtain ⟨x,xw,xK⟩ := h,
    rw [list.mem_to_finset,walk.mem_support_iff_exists_append] at xw,
    obtain ⟨cx,_,rfl⟩ := xw,
    apply cnK,
    dsimp only [thicken_],
    simp only [finite.mem_to_finset, mem_set_of_eq, exists_prop],
    use [x,xK],
    apply (dist_le cx).trans,
    refine le_trans _ hwm,
    simp only [length_append, le_add_iff_nonneg_right, zero_le'],},

  let Cw := comp_out.of_connected_disjoint (w.support.to_finset : set V) (connected.walk_support w) wdisK.symm,
  have : C = Cw, by
  { apply comp_out.eq_of_not_disjoint,
    rw set.not_disjoint_iff,
    use [c,cC],
    apply comp_out.of_connected_disjoint_sub,
    simp only [mem_coe, list.mem_to_finset, start_mem_support],},
  rw this,
  apply comp_out.of_connected_disjoint_sub,
  simp only [mem_coe, list.mem_to_finset, end_mem_support],
end

include Gpc'
def coarse.of_coarse_Lipschitz_of_cofinite (f : V → V') (m : ℕ)
  (fcl : coarse_Lipschitz G G' f m) (cof : cofinite f) : coarse G G' f :=
λ K,
⟨ cof.preimage $ thicken_ G' K m
, by {

  let K' := thicken_ G' K m,
  let L := cof.preimage K',

  rintro D,
  have disDK' : disjoint (f '' D.val) (K' : set V'), by
  { apply disjoint.preimage',
    rw ←cofinite.preimage.coe cof,
    apply (comp_out.dis_of_inf D.val.val D.prop).symm, },

  have disDK : disjoint (f '' D.val) K := set.disjoint_of_subset_right (thicken_.sub G' K m) disDK',
  have  fDinf: (f '' D.val.val : set V').infinite := cofinite.image_infinite cof D.prop,
  let d := fDinf.nonempty.some,
  have dfD := fDinf.nonempty.some_spec,
  have dnK : d ∉ K := λ dK, (disDK.ne_of_mem dfD dK) (refl d),
  have dnK'' : d ∉ K' := λ dK', (disDK'.ne_of_mem dfD dK') (refl d),

  let C := comp_out.of_vertex G' K d,
  have dC : d ∈ C := comp_out.of_vertex_mem d,

  suffices : f '' D.val ⊆ C,
  { let Cinf := set.infinite.mono this fDinf,
    use [C,comp_out.dis_of_inf C Cinf, Cinf, this],},

  rintro d' ⟨e',⟨heD',hed'⟩⟩,
  rcases dfD with ⟨e,⟨heD,hed⟩⟩,
  obtain ⟨w'⟩ := comp_out.connected D.val.val  ⟨e,heD⟩ ⟨e',heD'⟩,
  let w : G.walk e e' := w'.from_induced,
  have wD : (w.support.to_finset : set V) ⊆ D.val.val := w'.from_induced_contained,

  by_contradiction,
  have efC : e ∈ set.preimage f C, by {simp only [set.mem_preimage],rw hed,exact dC},
  have efC' : e' ∉ set.preimage f C, by {simp only [set.mem_preimage],rw hed', exact h},
  clear_value w, -- `obtain` (below) asked me to do that, presumably because `w` is a `let` and not a `have`
  obtain ⟨x,y,_,a,_,rfl,xC,yC⟩ := w.split_along_set (set.preimage f C) efC efC',
  suffices : y ∈ set.preimage f C, { exact yC this, },
  apply well_separated G' Gpc' K m C (f x) _ (f y) _ (fcl x y a),
  { change x ∈ set.preimage f C, apply mem_of_subset_of_mem xC, simp only [mem_coe, list.mem_to_finset, end_mem_support],  }, -- x is containde in a path containde in f⁻¹ C
  have xD : x ∈ (D : set V), by
  { apply wD,
    simp only [mem_coe, list.mem_to_finset, mem_support_append_iff, end_mem_support, true_or],},
  have fxnK' : f x ∉ K' := λ fxK', (disDK'.ne_of_mem (mem_image_of_mem f xD) fxK') (refl (f x)),
  exact fxnK',
}⟩


include Gpc
def coarse_close.of_close_of_coarse_Lipschitz_of_cofinite (f g : V → V')
  (m : ℕ) (clf : coarse_Lipschitz G G' f m) (clg : coarse_Lipschitz G G' g m)
  (cof : cofinite f) (cog : cofinite g) (close : ∀ v, G'.dist (f v) (g v) ≤ m) : coarse_close G G' f g :=
begin
  rintro K,

  let K' := thicken_ G' K m,

  let Lf := (coarse.of_coarse_Lipschitz_of_cofinite G G' Gpc' f m clf cof K).1,
  let Hf := (coarse.of_coarse_Lipschitz_of_cofinite G G' Gpc' f m clf cof K).2,
  have Lfdef : (Lf : set V) = set.preimage f K', by {
    rw [←cofinite.preimage.coe cof K', finset.coe_inj], refl,},
  -- If I do `obtain ⟨Lf,Hf⟩ := …` the proof of `Lfdef` doesn't work anymore.
  -- I believe that's because `obtain` uses `have` which doesn't allow "unfolding" the defs.
  obtain ⟨Lg,Hg⟩ := coarse.of_coarse_Lipschitz_of_cofinite G G' Gpc' g m clg cog K,

  use Lf ∪ Lg,
  let Hf' := good_finset.up G G' Hf (finset.subset_union_left Lf Lg),
  let Hg' := good_finset.up G G' Hg (finset.subset_union_right Lf Lg),

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
  have cC : c ∈ ((Hf' D) : set V') := (Hf' D).prop ⟨d,dD,refl c⟩,
  have cC' : c' ∈ ((Hg' D) : set V') := (Hg' D).prop ⟨d,dD,refl c'⟩,
  have cnK : c ∉ K', by
  { rintro cK',
    have : d ∈ Lf ∪ Lg, by
    { simp only [finset.mem_union],
      left,
      rw [←finset.mem_coe, Lfdef, set.mem_preimage],
      exact cK', },
    exact comp_out.dis_of_inf D.val.val D.prop ⟨this,dD⟩, },
  ext,
  apply comp_out.eq_of_not_disjoint, -- G' K _ _ (Hf' D).val.val.prop (Hg' D).val.val.prop c' _ cC',
  rw set.not_disjoint_iff,
  use c', refine ⟨_,cC'⟩,
  apply well_separated G' Gpc' K m (Hf' D) c cC c' cnK (close d),
end

/-
def qi_embedding (f : V → V') : Prop := sorry -- ∃ (K : ℕ), ∀ (u v : V), dist (f u) (f v) ≤ K * (dist u v) + K ∧ dist u v ≤ K * (dist (f u) (f v)) + K

def coarse.of_qi_embedding (f : V → V') (qie : qi_embedding f) : coarse G G' f := sorry

def coarse.comp {f : V → V'} {f' : V' → V''} (coa : coarse G G' f) (coa' : coarse G' G'' f') : coarse G G'' (f' ∘ f) := sorry

def ends_map {f : V → V'} (coa : coarse G G' f) : @ends V G → @ends V' G' := sorry


-/
