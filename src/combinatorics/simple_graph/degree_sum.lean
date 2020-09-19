import combinatorics.simple_graph.basic
import algebra.big_operators.basic
open finset

open_locale big_operators

namespace simple_graph
universes u v
variables (G : simple_graph.{v}) [fintype (V G)] [decidable_eq (V G)] [decidable_rel G.adj]

/--
A dart is an ordered pair of adjacent vertices, thought of as a little arrow from the
first vertex along an edge. (It is `uncurry (adj G)` as a subtype.)
-/
def darts : Type v := {d : V G × V G // d.1 ~g d.2}

/--
Gives the dart's edge.
-/
def dart_to_edge : darts G → G.edge_set := λ d, ⟨⟦d.val⟧, d.property⟩
/--
Gives the dart's vertex.  This is the first vertex of the pair.
-/
def dart_to_vert : darts G → V G := λ d, d.val.1
/--
Reverses the dart: the new vertex is the vertex across the edge.
-/
def dart_reverse : darts G → darts G := λ d, ⟨(d.val.2, d.val.1), symm G d.property⟩

@[simp]
lemma dart_to_edge_of_dart_reverse (d : darts G) : dart_to_edge G (dart_reverse G d) = dart_to_edge G d :=
by { rcases d with ⟨⟨x, y⟩, h⟩,
     dsimp [dart_to_edge, dart_reverse], rw [subtype.mk_eq_mk, sym2.eq_swap] }


lemma dart_reverse_invol : function.involutive (dart_reverse G) :=
by { rintro ⟨⟨x, y⟩, h⟩, dsimp [dart_reverse], rw subtype.mk_eq_mk }

lemma dart_reverse_no_fixedpoint (d : darts G) : d ≠ dart_reverse G d :=
begin
  rcases d with ⟨⟨x, y⟩, h⟩,
  dsimp [dart_reverse],
  rw subtype.mk_eq_mk,
  intro heq, rw prod.mk.inj_iff at heq,
  rw [heq.1] at h,
  exact loopless G _ h,
end

lemma dart_edge_preimage (d₁ d₂ : darts G) :
  dart_to_edge G d₁ = dart_to_edge G d₂ ↔ d₁ = d₂ ∨ d₁ = dart_reverse G d₂ :=
begin
  rcases d₁ with ⟨⟨x₁, y₁⟩, h₁⟩,
  rcases d₂ with ⟨⟨x₂, y₂⟩, h₂⟩,
  dsimp [dart_to_edge, dart_reverse],
  repeat { rw subtype.mk_eq_mk },
  repeat { rw prod.mk.inj_iff },
  exact sym2.eq_iff,
end

instance : fintype (darts G) :=
by { dunfold darts, apply_instance }

lemma dart_to_edge_prop (e : G.edge_set) (d : darts G) (h : dart_to_edge G d = e) : dart_to_vert G d ∈ e.1 :=
by tidy

lemma dart_to_edge_surj : function.surjective (dart_to_edge G) :=
begin
  rintro ⟨e, he⟩,
  refine quotient.rec_on_subsingleton e (λ e he, _) he,
  rcases e with ⟨x, y⟩,
  rw mem_edge_set at he,
  exact ⟨⟨(x, y), he⟩, rfl⟩,
end

lemma dart_to_edge_surj' : image (dart_to_edge G) univ = univ :=
begin
  ext e,
  simp only [mem_image, mem_univ, iff_true, exists_prop_of_true],
  exact dart_to_edge_surj G e,
end

lemma dart_to_vert_preimage_card_eq_degree (v : V G):
  (univ.filter (λ (x : darts G), dart_to_vert G x = v)).card = degree v :=
begin
  dunfold degree, rw neighbor_finset_eq_filter,
  let f := λ (x : darts G), dart_to_vert G (dart_reverse G x),
  let s := univ.filter (λ (x : darts G), dart_to_vert G x = v),
  have H : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y, {
    rintros ⟨⟨x₁, y₁⟩, h₁⟩ hd₁ ⟨⟨x₂, y₂⟩, h₂⟩ hd₂ heq,
    dsimp [f, dart_reverse, dart_to_vert] at heq,
    rw [subtype.mk_eq_mk, prod.mk.inj_iff],
    simp only [dart_to_vert, true_and, mem_filter, mem_univ] at hd₁ hd₂,
    subst x₁, subst x₂, subst y₂, simp,
  },
  rw ←card_image_of_inj_on H,
  congr,
  ext w,
  simp only [mem_image, true_and, exists_prop, mem_filter, mem_univ],
  split,
  { rintros ⟨⟨⟨x, y⟩, h⟩, hd, hw⟩,
    dsimp [dart_to_vert] at hd, subst v,
    dsimp [f, dart_reverse, dart_to_vert] at hw, subst w,
    exact h, },
  { intro a,
    use ⟨(v, w), a⟩, simp [dart_to_vert, f, dart_reverse], },
end

lemma dart_to_edge_two_to_one (e : G.edge_set) : (univ.filter (λ x, dart_to_edge G x = e)).card = 2 :=
begin
  cases e with e he,
  rcases dart_to_edge_surj G ⟨e, he⟩ with ⟨d, hd⟩,
  have key : univ.filter (λ (x : darts G), dart_to_edge G x = ⟨e, he⟩) = {d, dart_reverse G d},
  { ext d',
    simp only [true_and, mem_filter, mem_insert, mem_univ, mem_singleton],
    rw [←hd, dart_edge_preimage], },
  rw key,
  have key' : d ∉ {dart_reverse G d},
  { rw not_mem_singleton, apply dart_reverse_no_fixedpoint, },
  rw card_insert_of_not_mem key',
  simp,
end

lemma dart_card_twice_edges : fintype.card (darts G) = 2 * (edge_finset G).card :=
begin
  change univ.card = _,
  rw card_eq_sum_card_image (dart_to_edge G),
  rw dart_to_edge_surj',
  simp only [dart_to_edge_two_to_one, edge_set_univ_card, nat.cast_id, nsmul_eq_mul, sum_const],
  rw mul_comm,
end

lemma dart_card_sum_degrees : fintype.card (darts G) = ∑ v : V G, degree v :=
begin
  change univ.card = _,
  rw card_eq_sum_card_image (dart_to_vert G),
  have key' := @sum_filter_of_ne (V G) ℕ univ (λ (v : V G), degree v) _ (λ x, x ∈ univ.image (dart_to_vert G)) _ begin
    intros v _ hd,
    rcases (degree_pos_iff_exists_adj v).mp (nat.pos_of_ne_zero hd) with ⟨w, hw⟩,
    simp only [mem_image, mem_univ, exists_prop_of_true],
    use ⟨(v, w), hw⟩,
    simp [dart_to_vert],
  end,
  rw ←key',
  have key'' : univ.filter (λ (x : V G), x ∈ univ.image (dart_to_vert G)) = univ.image (dart_to_vert G),
  { ext v, simp, },
  rw key'',
  congr,
  ext v,
  rw dart_to_vert_preimage_card_eq_degree,
end

lemma degree_sum : ∑ v : V G, degree v = 2 * (edge_finset G).card :=
by { rw [←dart_card_sum_degrees, ←dart_card_twice_edges] }

end simple_graph
