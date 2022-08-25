import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import category_theory.functor.basic
import .mathlib

open function finset set classical simple_graph.walk relation

local attribute [instance] prop_decidable

universes u v w

noncomputable theory

namespace simple_graph


variables  {V : Type u}


def compl (G : simple_graph V) (S : set V) : subgraph G := (⊤ : subgraph G).delete_verts S

lemma outside_to_compl (G : simple_graph V) {S : set V} {v : V} (h : v ∉ S) : v ∈ (G.compl S).verts := by simp [compl, h]


section coercions

  variables {K L : set V} {G : simple_graph V} (h : K ⊆ L)

  -- `def` rather than `instance` because of typeclass problems
  def vertex_coe : (G.compl L).verts → (G.compl K).verts :=
  λ ⟨v, ⟨htop, hnL⟩⟩, ⟨v, ⟨htop, λ hK, hnL (h hK)⟩⟩

  def compl_coe : (set ↥((G.compl L).verts)) → (set ↥((G.compl K).verts)) := λ S, (vertex_coe h) '' S

  def compl_rev : (set ↥((G.compl K).verts)) → (set ↥((G.compl L).verts)) := λ S v, S (vertex_coe h v)

  @[simp] lemma compl_rev_mem_iff_vert_coe {v : (G.compl L).verts} {S : set (G.compl K).verts} : v ∈ compl_rev h S ↔ vertex_coe h v ∈ S := by refl

  @[simp] lemma compl_coe_mem_iff_vert_coe {v : (G.compl L).verts} {S : set (G.compl L).verts} : (vertex_coe h v) ∈ (compl_coe h S) ↔ v ∈ S := by {
  unfold compl_coe, apply function.injective.mem_set_image,
  rintros ⟨v, _, _⟩ ⟨w, _, _⟩ h,
  apply subtype.mk_eq_mk.mpr, dsimp [vertex_coe] at h,
  apply subtype.mk_eq_mk.mp, assumption, }

  lemma compl_galois_connection {S : set ↥(G.compl L).verts} {T : set ↥(G.compl K).verts} : compl_coe h S ⊆ T ↔ S ⊆ compl_rev h T :=
  begin
    split,
    { intros h v hvS,
      rw [compl_rev_mem_iff_vert_coe], apply h,
      rw [compl_coe_mem_iff_vert_coe], exact hvS,
    }, {
      intros h v hvcS,
      dsimp [compl_coe] at hvcS, rcases hvcS with ⟨v', hv'S, hv'coe⟩,
      have := h hv'S, rw [compl_rev_mem_iff_vert_coe, hv'coe] at this,
      assumption, }
  end

  lemma vertex_coe_self (S : set ↥(G.compl K).verts) {h : K ⊆ K} : ∀ (v : (G.compl K).verts), vertex_coe h v = v := λ ⟨v, _, _⟩, rfl

  lemma vertex_coe_trans {M : set V} {h' : L ⊆ M} : ∀ (v : (G.compl M).verts),
  vertex_coe h (vertex_coe h' v) = vertex_coe (h.trans h') v := λ ⟨v, _, _⟩, rfl

  lemma compl_coe_set_self (S : set ↥(G.compl K).verts) {h : K ⊆ K} : compl_coe h S = S := by {ext, conv {to_lhs, rw [← vertex_coe_self S x, compl_coe_mem_iff_vert_coe],},}

  lemma compl_rev_set_self {S : set ↥(G.compl K).verts} {h : K ⊆ K} : compl_rev h S = S := by {ext, rw [compl_rev_mem_iff_vert_coe, vertex_coe_self S x], }

end coercions


def conn_comp_outside (G : simple_graph V) (K : set V) : Type u :=
  (G.compl K).coe.connected_component

/- The vertices in the compl of `K` that lie in the component `C` -/
@[reducible, simp] def conn_comp_outside.verts {G : simple_graph V} {K : set V} (C : conn_comp_outside G K) :=
  {v : (G.compl K).verts | connected_component_mk _ v = C}

@[ext] lemma conn_comp_eq_of_eq_verts {G : simple_graph V} {K : set V} (C D : conn_comp_outside G K) : C = D ↔ C.verts = D.verts :=
begin
  split,
  { intro h, subst h, },
  { refine connected_component.ind₂ _ C D,
    intros v w, dsimp [conn_comp_outside.verts],
    intro h, simp_rw [set.ext_iff] at h,
    apply (h v).mp, apply congr_arg, refl,}
end


@[reducible, simp] def conn_comp_outside.supp {G : simple_graph V} {K : set V} (C : conn_comp_outside G K) :=
  {v : V | ∃ h : v ∈ (@set.univ V) \ K, connected_component_mk _ (by {dsimp only [compl], exact ⟨v,h⟩}) = C}

instance {G : simple_graph V} {K : set V} : set_like (conn_comp_outside G K) V :=
⟨ conn_comp_outside.supp
, by
  { rintro C D, refine connected_component.ind₂ _ C D,
    rintros ⟨v,vh⟩ ⟨w,wh⟩, dsimp [conn_comp_outside.supp],
    intro h, simp_rw [set.ext_iff] at h,
    have := (h v).mp ⟨vh,rfl⟩, simp only [mem_set_of_eq] at this,
    obtain ⟨_,_⟩ := this,
    assumption, }, ⟩

def inf_conn_comp_outside (G : simple_graph V) (K : set V) :=
 {C : G.conn_comp_outside K // C.verts.infinite}

def fin_conn_comp_outside (G : simple_graph V) (K : set V) :=
  {C : G.conn_comp_outside K // C.verts.finite}

instance inf_coe (G : simple_graph V) (K : set V) :
  has_coe (inf_conn_comp_outside G K) (conn_comp_outside G K) := ⟨λ x, x.val⟩

instance fin_coe (G : simple_graph V) (K : set V) :
  has_coe (fin_conn_comp_outside G K) (conn_comp_outside G K) := ⟨λ x, x.val⟩

namespace conn_comp_outside

lemma disjoint_supp {G : simple_graph V} {K : set V} (C : conn_comp_outside G K) :
  disjoint (C : set V) K := sorry

lemma pairwise_disjoint_supp {G : simple_graph V} {K : set V} (C D : conn_comp_outside G K) :
  disjoint (C : set V) (D : set V) := sorry

lemma nonempty_supp {G : simple_graph V} {K : set V} (C : conn_comp_outside G K) :
  (C : set V).nonempty := sorry

lemma connected_supp  {G : simple_graph V} {K : set V} (C : conn_comp_outside G K) :
   (G.induce (C : set V)).connected := sorry

lemma of_connected_disjoint {G : simple_graph V} {K : set V} (S : set V)
  (Sconn : (G.induce S).connected) (Sdis : disjoint S K) : {C  : conn_comp_outside G K | S ⊆ C} := sorry

lemma of_vertex {G : simple_graph V} {K : set V} (v : V)
   (hv : v ∉ K) : {C  : conn_comp_outside G K | v ∈ C} := sorry

@[reducible, simp] def component_of {G : simple_graph V} {K : set V} (v : (G.compl K).verts) :
  conn_comp_outside G K := connected_component_mk _ v

lemma reachable_empty_compl {G : simple_graph V} {u v : V} (hreach : G.reachable u v) :
  (G.compl ∅).coe.reachable ⟨u, G.outside_to_compl id⟩ ⟨v, G.outside_to_compl id⟩ := sorry

lemma reachable_coe {G : simple_graph V} {K L : set V} (h : K ⊆ L)
{v a: ↥((G.compl L).verts)} (hreach: (G.compl L).coe.reachable a v) : (G.compl K).coe.reachable (vertex_coe h a) (vertex_coe h v) := sorry

lemma of_empty_is_subsingleton  {G : simple_graph V} (Gpc : G.preconnected) : subsingleton (conn_comp_outside G (∅ : finset V)) := sorry

lemma component_subset_iff_eq {G : simple_graph V} {K : set V} {C D : conn_comp_outside G K} : C.verts ⊆ D.verts ↔ C = D :=
begin
  split,
  { refine connected_component.ind₂ _ C D,
    intros v w, dsimp [verts],
    intro h, apply h, refl,},
  {intro h, subst h,},
end

lemma comp_sub_compl_rev_coe {G : simple_graph V} {K L : set V} (h : K ⊆ L) (v : (G.compl L).verts) : (component_of v).verts ⊆ compl_rev h (component_of (vertex_coe h v)).verts :=
begin
  intros x h, simp [component_of] at *,
  apply reachable_coe, exact h,
end


section finite_components

  variables (G : simple_graph V) [Gpc : preconnected G] (K : finset V)

  /- The boundary of a set, consisting of all adjacent vertices not in the set -/
  def bdry (S : set V) := {v : (G.compl S).verts | ∃ x ∈ S, G.adj v x}

  /- This is the portion of the connected component that is a part of the boundary -/
  def border {G : simple_graph V} {K : finset V} (C : conn_comp_outside G K) : set (compl G K).verts := C.verts ∩ (bdry G K)

  lemma components_cover : set.Union (λ C : conn_comp_outside G K, C.verts) = ⊤ :=
  begin
    ext, simp [verts], use component_of x,
  end

  lemma components_nonempty : ∀ (C : conn_comp_outside G K), nonempty (C.verts) :=
  begin
    apply connected_component.ind,
    rintro v, apply nonempty.intro,
    use v, dsimp [verts], refl,
  end

  -- TODO: Show that the boundary is precisely the union of all the borders.
  lemma bdry_eq_border_union : (bdry G K) = set.Union (λ C : conn_comp_outside G K, C.border) :=
    calc bdry G K = ⊤ ∩ (bdry G K) : by simp
    ... = (set.Union (λ C : conn_comp_outside G K, C.verts)) ∩ (bdry G K) : by rw [components_cover]
    ... = set.Union (λ C : conn_comp_outside G K, C.verts ∩ (bdry G K)) : (bdry G K).Union_inter (λ (i : conn_comp_outside G K), i.verts)
    ... = set.Union (λ C : conn_comp_outside G K, C.border) : by refl

  -- for mathlib:
  lemma symm_iff {X : Type u} (P : X → X → Prop) : (∀ {a b}, P a b → P b a) → (∀ {a b}, P a b ↔ P b a) := by tidy

  lemma bdry.iff : bdry G K = set.Union (λ k : K, {v : (G.compl K).verts | v.val ∈ G.neighbor_set k}) :=
  begin
    ext, unfold bdry, simp,
    conv in (G.adj ↑_ _)
      {rw [symm_iff G.adj (λ _ _, G.adj_symm)],},
  end

  lemma bdry.iso : ↥(bdry G K) ≃ Σ C : conn_comp_outside G K, ↥(border C) := {
    to_fun := λ ⟨v, h⟩, ⟨component_of v, v, rfl, h⟩,
    inv_fun := λ ⟨C, v, h⟩, ⟨v, h.2⟩,
    left_inv := by {simp [left_inverse],},
    right_inv := by {simp [function.right_inverse, left_inverse],
      dsimp [conn_comp_outside, border],
      intro a, rintro ⟨b, _, _⟩,
      tidy,
    } }

  lemma bdry_finite [locally_finite G] : (bdry G K).finite :=
  begin
    rw [bdry.iff], refine finite_Union _, rintro k,
    apply set.finite.preimage,
    { apply injective.inj_on, tidy, },
    { exact (neighbor_set G k).to_finite, }
  end

  -- for mathlib
  lemma fintype.iso {A B : Type u} (hA : fintype A) (hiso : A ≃ B) : fintype B :=
  begin
    fsplit,
    { refine finset.map ⟨hiso.to_fun, _⟩ hA.elems,
      unfold injective, intros _ _ h,
      have := congr_arg hiso.inv_fun h,
      simp at this, assumption,
    },
    intro b,
    let a := hiso.inv_fun b,
    have : hiso.to_fun a = b := by {show hiso.to_fun (hiso.inv_fun b) = id b, simp,},
    rw ← this,
    refine mem_map.mpr _,
    use a, split,
    apply hA.complete,
    refl,
  end

  instance border_sum_fin [locally_finite G] : fintype (Σ C : conn_comp_outside G K, ↥(border C)) :=
  begin
    apply fintype.iso, rotate,
    exact (bdry.iso G K),
    refine finite.fintype _,
    apply bdry_finite,
  end

  lemma border_finite [locally_finite G] (C : conn_comp_outside G K) :  (border C).finite :=
  begin
    refine finite.inter_of_right _ C.verts, apply bdry_finite,
  end


  #check @walk.rec

  -- for mathlib
  lemma reachable_of_adj {u v : V} : G.adj u v → G.reachable u v := sorry

  lemma good_path {V : Type u} {G : simple_graph V} :
  ∀ (u v : V) (p : G.walk u v) (S : set V) (uS : u ∈ S) (vS : v ∉ S),
    ∃ (x y : V) (w : G.walk u x), G.adj x y ∧  (w.support.to_finset : set V) ⊆ S ∧ y ∉ S
  | _ _ nil p up vnp := (vnp up).elim
  | _ _ (cons' u x v a q) p up vnp := by {
    by_cases h : p x,
    { obtain ⟨xx,yy,ww,aa,dd,mm⟩ := good_path x v q p h vnp,
      use [xx,yy,cons a ww,aa],split,rotate, exact mm,
      simp, rw set.insert_subset,exact ⟨up,dd⟩,
    },
    { use [u,x,nil,a],simp,exact ⟨up,h⟩, }
  }

  lemma walk.compl {G : simple_graph V} (S : set V)
    (x y : V)  (hx : x ∉ S) (hy : y ∉ S)
    (w : G.walk x y) (hw : disjoint (w.support.to_finset : set V) S) :
    (G.compl S).coe.reachable ⟨x, outside_to_compl G hx⟩ ⟨y, outside_to_compl G hy⟩ := sorry

  lemma walk.to_boundary {G : simple_graph V} (S : set V) (src : (G.compl S).verts) (tgt : S) (w : G.walk ↑src tgt) :
    ∃ b ∈ bdry G S, (G.compl S).coe.reachable src b :=
  begin
    dsimp [simple_graph.compl],
    obtain ⟨s,hs⟩ := src, simp [compl] at hs,
    obtain ⟨t,ht⟩ := tgt,
    obtain ⟨a,b,w,adj,sub,mem⟩ := good_path s t w (Sᶜ) (hs : s ∈ Sᶜ) (by {simp, exact ht} : t ∉ Sᶜ),
    have : a ∉ S, by {sorry},
    simp,
    use [a,this],
    unfold bdry,simp,
    split,
    { use [b], simp at mem, exact ⟨mem,adj⟩, },
    { unfold simple_graph.reachable,
      fapply walk.compl S s a hs this w,
      rw subset_compl_iff_disjoint_right at sub,
      exact sub,}
  end

  lemma border_nonempty (Gpc : preconnected G) (Knempty : K.nonempty) : ∀ (C : conn_comp_outside G K), nonempty (border C) :=
  begin
    apply connected_component.ind,
    intro v, rcases Knempty with ⟨k, kK⟩,
    let w := (Gpc ↑v k).some,
    rcases (walk.to_boundary ↑K v ⟨k, kK⟩ w) with ⟨b, hbdry, hreach⟩,
    apply nonempty.intro,
    use b, unfold border, simp,
    exact ⟨reachable.symm hreach, hbdry⟩,
  end

  def to_border (Gpc : preconnected G) (Knempty : K.nonempty) : Π (C : conn_comp_outside G K), ↥(border C) := λ C, nonempty.some $ @border_nonempty _ G K Gpc Knempty C

  -- for mathlib
  lemma sigma.fintype_of_nonempty_fintype {α : Type u} (β : Π (a : α), Type v) (fin_sigma : fintype Σ a : α, β a) (hnonempty : Π a : α, nonempty (β a)) : fintype α :=
  begin
    refine fintype_of_not_infinite _,
    intro hinf,
    refine infinite.false (_ : infinite Σ a : α, β a),

    let φ : α → Σ a : α, β a := λ a, ⟨a, nonempty.some (hnonempty a)⟩,
    refine @infinite.of_injective _ _ hinf φ _,

    rintros _ _ hφ,
    cases hφ, simp [φ] at hφ,
  end

  lemma finite_components [Glf : locally_finite G] (Gpc : preconnected G) :
    fintype (conn_comp_outside G K) :=
  begin
    by_cases Knempty : K.nonempty,
    {
      have border_map_fin : fintype (Σ C : conn_comp_outside G K, ↥(border C)) := by {apply_instance}, -- needed for some reason
      refine sigma.fintype_of_nonempty_fintype _ _ _, rotate,
      apply border_map_fin,
      apply border_nonempty,
      assumption, assumption,
    },
    { rw [finset.not_nonempty_iff_eq_empty] at Knempty,
      subst Knempty,
      -- refine ⟨{_}, _⟩,
      by_cases nonempty V, {
        refine ⟨{_}, _⟩,

        exact component_of ⟨nonempty.some h, outside_to_compl G (by simp)⟩,

        apply connected_component.ind,
        rintro ⟨v', _⟩, dsimp [component_of],
        simp, apply reachable_empty_compl, apply Gpc,},

      { refine ⟨∅, _⟩, dsimp [conn_comp_outside],
        apply connected_component.ind, rintro ⟨v, _⟩,
        apply (not_nonempty_iff.mp h).elim v, }}
  end

  lemma nonempty_components (Vinf : (univ : set V).infinite) : nonempty (conn_comp_outside G K) :=
  begin
    suffices inh : nonempty (G.compl K).verts, from nonempty.intro (component_of (nonempty.some inh)),
    suffices inf : ((univ : set V) \ ↑K).infinite, from by { rcases set.nonempty_def.mp (set.infinite.nonempty inf) with ⟨v, h⟩, exact nonempty.intro ⟨v, h⟩,},
    apply set.infinite.diff,
    exact Vinf, exact K.finite_to_set,
  end

end finite_components

section back_map

variables (G : simple_graph V) (K : set V)

-- this is the `bwd_map`
def conn_comp_outside_back {K L : set V} {G : simple_graph V} (h : K ⊆ L) : conn_comp_outside G L → conn_comp_outside G K :=
  connected_component.lift
  (λ (v : ↥((compl G L).verts)), component_of (vertex_coe h v))
  (λ v w p _, connected_component.eq.mpr (reachable_coe h (nonempty.intro p)))

@[simp] lemma conn_comp_outside_back_of_vert {K L : set V} (h : K ⊆ L) (v : (G.compl L).verts) : conn_comp_outside_back h ((G.compl L).coe.connected_component_mk v) = connected_component_mk _ (vertex_coe h v) :=
begin
  dsimp [conn_comp_outside_back], refl,
end

lemma conn_comp_outside_back.unique {K L : set V} (h : K ⊆ L) (C : conn_comp_outside G L) : ∀ D : conn_comp_outside G K, conn_comp_outside_back h C = D ↔ C.verts ⊆ compl_rev h D.verts :=
begin
  refine connected_component.ind _ C, intros v D,
  rw [conn_comp_outside_back_of_vert], split,
  { intro h, subst h, apply comp_sub_compl_rev_coe,},
  { intro h, apply h, exact @rfl _ (connected_component_mk _ v),}
end

lemma conn_comp_outside_back.unique' {K L : set V} (h : K ⊆ L) (C : conn_comp_outside G L) : ∀ D : conn_comp_outside G K, conn_comp_outside_back h C = D ↔ compl_coe h C.verts ⊆ D.verts := by {intro _, rw [conn_comp_outside_back.unique, compl_galois_connection],}

lemma conn_comp_outside_back.refl (K : set V) (C : conn_comp_outside G K) :
  conn_comp_outside_back (set.subset.refl K) C = C :=
begin
  rw [conn_comp_outside_back.unique, compl_rev_set_self],
end

lemma conn_comp_outside_back.trans {J K L : set V} (k : J ⊆ K) (h : K ⊆ L) (C : conn_comp_outside G L) :
  conn_comp_outside_back k (conn_comp_outside_back h C) = conn_comp_outside_back (k.trans h) C :=
begin
  apply eq.symm, rw [conn_comp_outside_back.unique],
  refine connected_component.ind _ C,
  simp_rw [conn_comp_outside_back_of_vert, vertex_coe_trans],
  apply comp_sub_compl_rev_coe,
end


def conn_comp_outside_back.inf_to_inf {K L : set V} {G : simple_graph V} (h : K ⊆ L) (C : conn_comp_outside G L) (hinf : C.verts.infinite) : (conn_comp_outside_back h C).verts.infinite :=
begin
  apply infinite.mono, rw [← conn_comp_outside_back.unique'],
  refine (infinite_image_iff _).mpr hinf,
  refine inj_on_of_injective _ _,
  obviously,
end

lemma inf_conn_comp_outside.iff_in_all_range : ∀ (K : (finset V)) (C : conn_comp_outside G K),
    C.verts.infinite ↔ ∀ (L : finset V) (h : K ⊆ L), C ∈ set.range (@conn_comp_outside_back _ _ _ G h) := sorry

def inf_conn_comp_outside_back {K L : set V} {G : simple_graph V} (h : K ⊆ L) : G.inf_conn_comp_outside L → G.inf_conn_comp_outside K :=
  λ ⟨C, hinf⟩, ⟨conn_comp_outside_back h C, conn_comp_outside_back.inf_to_inf h C hinf⟩

lemma inf_conn_comp_outside_back.def {K L : set V} {G : simple_graph V} (h : K ⊆ L) : ∀ (C : G.inf_conn_comp_outside L), (inf_conn_comp_outside_back h C).val = conn_comp_outside_back h C.val := by {rintro ⟨_, _⟩, refl,}

lemma inf_conn_comp_outside_back.comp_apply {K L M : set V} {G : simple_graph V} (hKL : K ⊆ L) (hLM : L ⊆ M) :
  ∀ (C : G.inf_conn_comp_outside M), inf_conn_comp_outside_back hKL (inf_conn_comp_outside_back hLM C) = inf_conn_comp_outside_back (hKL.trans hLM) C := sorry



-- TODO: An infinite graph has at least one infinite connected component
lemma inf_graph_has_inf_conn_comp [infinite V] : nonempty (inf_conn_comp_outside G K) := sorry

-- TODO: A locally finite graph has finitely many infinite connected components
lemma inf_graph_fin_inf_conn_comp [locally_finite G] : finite (inf_conn_comp_outside G K) := sorry

end back_map

-- def ends_system := category_theory.functor.mk (conn_comp_outside G) (conn_comp_outside_back G)

-- TODO: Mapping of connected sets under homomorphisms
-- TODO: Show that components are preserved under isomorphisms

def conn_comp_outside.extend_to_connected
  (G : simple_graph V) [Glf : locally_finite G] (K : finset V) (Knempty : K.nonempty):
  { K' : finset V // K ⊆ K' ∧ (G.induce ↑K').connected } := sorry

def conn_comp_outside.extend_connected_with_fin_components
  (G : simple_graph V) [Glf : locally_finite G] (K : finset V)
  (Kconn : (G.induce ↑K).connected) :
  { K' : finset V // K ⊆ K' ∧  (G.induce ↑K').connected ∧ (∀ C : conn_comp_outside G K', C.verts.infinite) } := sorry

-- TODO: Build all the associated lemmas. Mainly prove that the resulting set of connected components are precisely the infinite connected components of the original graph.

-- TODO: Prove lemmas about cofinite infinite components

lemma nicely_arranged {G : simple_graph V} [locally_finite G] (Gpc : G.preconnected) (H K : finset V)
  (Hnempty : H.nonempty) (Knempty : K.nonempty)
  (E E' : inf_conn_comp_outside G H) (En : E ≠ E')
  (F : inf_conn_comp_outside G K)
  (H_F : (H : set V) ⊆ F)
  (K_E : (K : set V) ⊆ E) : (E : set V) ⊆ (F : set V) :=
begin

  by_cases h : ((E' : set V) ∩ K).nonempty,
  { rcases h with ⟨v,v_in⟩,
    have vE' : v ∈ (E' : set V), from ((set.mem_inter_iff v E' K).mp v_in).left,
    have vE : v ∈ (E : set V), from  K_E ((set.mem_inter_iff v E' K).mp v_in).right,
    exfalso,
    apply En, -- common element, hence equal: needs a lemma
    sorry,
    --exact ro_component.eq_of_common_mem G H EE EE' Ecomp Ecomp' v vE vE'
    },
  {
    have : ∃ F' : inf_conn_comp_outside G K, (E' : set V) ⊆ F', by {
      rcases ro_component.of_subconnected_disjoint G K EE'
             (set.infinite.nonempty Einf')
             (by {unfold disjoint, rw [le_bot_iff], rw [set.not_nonempty_iff_eq_empty] at h, assumption,}) -- empty intersection means disjoint
             (ro_component.to_subconnected G H EE' Ecomp') with ⟨F',F'comp,sub⟩,
      have F'inf : F'.infinite, from set.infinite.mono sub Einf',
      use ⟨⟨F',F'comp⟩,F'inf⟩,
      exact sub,
    },
    rcases this with ⟨⟨⟨FF',Fcomp'⟩,Finf'⟩,E'_sub_F'⟩,
    by_cases Fe : FF' = FF,
    { exact Fe ▸ E'_sub_F',},
    { rcases ro_component.adjacent_to G Gpc H Hnempty EE' Ecomp' with ⟨v,vh,vhH,vF',adj⟩,
      have : vh ∈ FF, from H_F vhH,
      have : FF = FF',
        from ro_component.eq_of_adj_mem G K FF Fcomp FF' Fcomp' vh v this (E'_sub_F' vF') adj,
      exfalso,
      exact Fe (this.symm),},
  },
end


end conn_comp_outside

end simple_graph
