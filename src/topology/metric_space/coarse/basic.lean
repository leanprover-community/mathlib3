/-
Copyright (c) 2022 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors
-/
import topology.metric_space.emetric_space
/-!
# Basic definitions of coarse geometry on metric space

This file defines some basic definitions of coarse geometry on metric spaces.
The main themes are:

* Local finiteness of a space `α`:
  `finite_balls` and `uniformly_finite_balls`, stating that `α` has finite (respectively uniformly finite) balls of any radius.
* Coarse connectedness and geodesicity of `α`:
  `coarsely_connected_with` and `coarsely_geodesic_with`, stating that any pair of points of `α` can be connected by a “coarse walk”, respectively a “coarse geodesic”.
* Coarse density of a subset `s` of `α` in a subset `t` of `α`:
  `coarsely_dense_with_in` (and variants) stating that any point of `t` is at distance at most `δ` (for a given `δ`) from some point of `s`.
* Coarse separation of a subset `s` of `α`:
  `coarsely_separated_with` stating that any two distinct points of `s` have distance at least `δ` (for a given `δ`).
* Closeness of two maps `f g` with codomain `α`:
  `close_maps_with` stating that for any `x` in the domain of `f` and `g`, the distance between `f x` and `g x` is at most `C` (for a given `C`).

## Main result

* `exists_coarsely_separated_net_in_with`:
  Given a subset `S` of the pseudo-emetric space `α` and some `δ : ℝ≥0`, there exists a set `s ⊆ S` that is both `δ`-dense in `S` and `δ`-separated.

## Notation

 * `∥` is a short-hand for `close_maps`.

## References

* [C. Druțu and M. Kapovich **Geometric group theory**][MR3753580]

## Tags

coarse geometry, metric space
-/


universes u v w

open function set fintype function pseudo_emetric_space
open_locale nnreal ennreal

section space

variables (α : Type u) [pseudo_emetric_space α]

/--
The pseudo-emetric space `α` has balls of finite cardinality.
-/
class finite_balls :=
(fintype_ball : ∀ x : α, ∀ r : ℝ≥0, fintype (emetric.ball x r))

attribute [instance] finite_balls.fintype_ball

/--
Assuming that the space `α` satisfies `finite_balls`, and given a function `k : ℝ≥0 → ℕ`, all balls of radius `r` in `α` have cardinality at most `k r`.
-/
def uniformly_finite_balls_with [finite_balls α] (k : ℝ≥0 → ℕ) :=
∀ x : α, ∀ r : ℝ≥0,  card (emetric.ball x r) ≤ k r

/--
Assuming that the space `α` satisfies `finite_balls`, there exists a function `k : ℝ≥0 → ℕ` such that  all balls of radius `r` in `α` have cardinality at most `k r`.
-/
def uniformly_finite_balls [finite_balls α] :=
∃ k : ℝ≥0 → ℕ, uniformly_finite_balls_with α k

/--
The set of sequences of `n` points in the space `α` at successive distance at most `K`.
This is interpreted as a “coarse” version of a walk in a graph.
-/
def coarse_walks_with_of_length (K : ℝ≥0) (n : ℕ) (x y : α) :=
{w : fin (n+1) → α | w (0 : fin $ n+1) = x
                    ∧ w  (fin.last n)= y
                    ∧ ∀ (i j : fin n), edist (w i) (w j) ≤ K * | j-i | }

/--
The set of sequences `w` of `n` points in the space `α` such that the distance between `w i` and `w j` is bounded from below by `k * |j-i|` and from above by `K * |j-i|`.
This is interpreted as a “coarse” version of a geodesic in a graph.
-/
def coarse_geods_with_of_length (K k: ℝ≥0) (n : ℕ) (x y : α) :=
{w : fin (n+1) → α | w (0 : fin $ n+1) = x
                    ∧ w  (fin.last n)= y
                    ∧ ∀ (i j : fin n), edist (w i) (w j) ≤ K * | j-i |
                    ∧ ∀ (i j : fin n), ↑|j-i| ≤ ↑k * edist (w i) (w j) }

/--
The space `α` has a coarse walk joining any pair of points.
-/
def coarsely_connected_with (K : ℝ≥0) :=
∀ x y : α, ∃ n : ℕ, ∃ w, w ∈ coarse_walks_with_of_length α K n x y

/--
The space `α` has a coarse geodesic joining any pair of points.
-/
def coarsely_geodesic_with (K k : ℝ≥0) :=
∀ x y : α, ∃ n : ℕ, ∃ w, w ∈ coarse_geods_with_of_length α K k n x y

end space


section subspace

variables {α : Type u} [pseudo_emetric_space α]

/--
Given a pseudo-emetric space `α`, the subset `s` is `ε`-coarsely dense in the subset `t` if any point of `t` is at distance at most `ε` from some point of `s`.
-/
def coarsely_dense_with_in (ε : ℝ≥0) (s t : set α) :=
∀ ⦃x⦄ (hx : x ∈ t), ∃ ⦃y⦄ (hy : y ∈ s), edist x y ≤ ε

/--
Given a pseudo-emetric space `α`, the subset `s` is `ε`-coarsely dense in `α` if any point of `α ` is at distance at most `ε` from some point of `s`.
-/
def coarsely_dense_with (ε : ℝ≥0) (s : set α) := coarsely_dense_with_in ε s (univ)

/--
The set `s` is coarsely dense in `t` if there exists some `ε` such that `s` is `ε`-coarsely dense in `t`.
-/
def coarsely_dense_in (s t : set α)  := ∃ ε : ℝ≥0 , coarsely_dense_with_in ε s t

/--
The set `s` is coarsely dense in `α` if there exists some `ε` such that it is `ε`coarsely dense.
-/
def coarsely_dense (s : set α)  := ∃ ε : ℝ≥0 , coarsely_dense_with ε s

/--
A coarsely dense subset is sometimes called a net.
-/
alias coarsely_dense ← is_net

/--
The set `s` is `δ`-coarsely separated if pair of distinct points of `s` is at distance greater than `δ`.
-/
def coarsely_separated_with  (δ : ℝ≥0) (s : set α)  :=
∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), x ≠ y → edist x y > δ

/--
The set `s` is coarsely separated if there exists some `δ>0` such that `s` is `δ`-coarsely separated.
-/
def coarsely_separated  (s : set α) :=
∃ δ : ℝ≥0 , δ > 0 ∧  coarsely_separated_with δ s

/--
The set `s` is a `δ`-coarsely separated `ε`-net in `t` if it is both `δ`-coarsely separated and `ε`-coarsely dense in `t`.
-/
def coarsely_separated_net_in_with  (δ ε : ℝ≥0) (s t : set α) :=
coarsely_separated_with δ s ∧ coarsely_dense_with_in ε s t

/--
The set `s` is a coarsely separated net with constants `δ,ε` if it is both coarsely separated with constant `δ` and coarsely dense constant `ε`.
-/
def coarsely_separated_net_with  (δ ε : ℝ≥0) (s : set α) :=
coarsely_separated_with δ s ∧ coarsely_dense_with ε s

/--
The constant-less version of `coarsely_separated_net_in_with`.
-/
def coarsely_separated_net_in (s t : set α) :=
(coarsely_separated s) ∧ (coarsely_dense_in s t)

/--
The constant-less version of `coarsely_separated_net_with`.
-/
def coarsely_separated_net (s : set α) :=
(coarsely_separated s) ∧ (coarsely_dense s)


namespace coarsely_dense_with_in

/--
A set is always 0-coarsely dense in itself.
-/
lemma refl (s : set α) : coarsely_dense_with_in 0 s s :=
λ x xs, ⟨x, xs, by simp⟩

/--
If `r` is `ε`-coarsely dense in `s`, and `s` is `ε'`-coarsely dense in `t`, then `r` is `(ε+ε')`-coarsely dense in `t`.
-/
lemma trans {ε ε' : ℝ≥0} {r s t : set α}
  (r_in_s : coarsely_dense_with_in ε r s) (s_in_t : coarsely_dense_with_in ε' s t) :
  coarsely_dense_with_in (ε + ε') r t :=
begin
  rintros z z_in_t,
  rcases s_in_t z_in_t with ⟨y,y_in_s,yd⟩,
  rcases r_in_s y_in_s with ⟨x,x_in_r,xd⟩,
  use [x, x_in_r],
  calc edist z x ≤ (edist z y) + (edist y x) : edist_triangle z y x
             ... ≤ ε'          + (edist y x) : add_le_add yd (le_refl $ edist y x)
             ... ≤ ε'          + ε           : add_le_add (le_refl ε') xd
             ... = ε + ε'                    : by ring
end

/--
If
* `s` is `ε`-coarsely dense in `t`;
* `s ⊆ s'`;
* `t' ⊆ t`;
* `ε ≤ ε'`;
then `s'` is `ε'`-coarsely dense in `t'`.
-/
lemma weaken {ε ε' : ℝ≥0} {s s' t t' : set α }
  (s_in_t : coarsely_dense_with_in ε s t)
  (s_sub_s' : s ⊆ s') (t'_sub_t : t' ⊆ t) (ε_le_ε' : ε ≤ ε') :
  coarsely_dense_with_in ε' s' t' :=
begin
  rintros z z_in_t',
  have z_in_t : z ∈ t, from t'_sub_t z_in_t',
  rcases s_in_t z_in_t with ⟨x,x_in_s,xd⟩,
  have x_in_s' : x ∈ s', from s_sub_s' x_in_s,
  use [x,x_in_s'],
  calc edist z x ≤ ε  : xd
             ... ≤ ε' : ennreal.coe_le_coe.mpr ε_le_ε',
end

lemma of_coarsely_dense_with {ε : ℝ≥0} {s : set α}
  (dense : coarsely_dense_with ε s) :
  coarsely_dense_with_in ε s univ := dense

end coarsely_dense_with_in

namespace coarsely_dense_with

lemma refl (α : Type u) [pseudo_emetric_space α] : coarsely_dense_with 0 (@univ α) :=
assume (x : α) (_ : x ∈ @univ α) ,
  begin
    use [x, mem_univ x],
    have : edist x x = 0, from edist_self x,
    simp,
  end

lemma of_coarsely_dense_with_in_univ {ε : ℝ≥0} {s : set α}
  (dense : coarsely_dense_with_in ε s univ) :
  coarsely_dense_with ε s := dense

end coarsely_dense_with

namespace coarsely_dense_in

lemma refl (α : Type u) [pseudo_emetric_space α] : coarsely_dense (@univ α) :=
⟨0, coarsely_dense_with.refl α⟩

lemma trans {r s t : set α}
  (r_in_s : coarsely_dense_in r s) (s_in_t : coarsely_dense_in  s t) :
  coarsely_dense_in r t :=
begin
  rcases r_in_s with ⟨rε,r_with⟩,
  rcases s_in_t with ⟨sε,s_with⟩,
  exact ⟨rε+sε,coarsely_dense_with_in.trans r_with s_with⟩,
end

end coarsely_dense_in

namespace coarsely_separated_net

/--
The set `s` is a maximal (with respect to `⊆`) `δ`-coarsely separated subset of `S`.
-/
def max_coarsely_separated_in_with (δ : ℝ≥0) (s S : set α) : Prop :=
s ⊆ S ∧
coarsely_separated_with δ s  ∧
(∀ t : set α, s ⊆ t → t ⊆ S →  coarsely_separated_with δ t → s = t)

/--
If the set `s` is a maximal `δ`-coarsely separated subset of `S`, then it is `δ`-dense.
-/
theorem max_coarsely_separated_in_is_net {δ : ℝ≥0} {s S: set α}
  (H : max_coarsely_separated_in_with δ s S) : coarsely_separated_net_in_with δ δ s S :=
begin
  rcases H with ⟨s_sub_S, s_sep, s_max⟩,
  refine ⟨s_sep, _⟩ ,
  rintros x xS,
  let t := s.insert x,
  by_contradiction H,
  push_neg at H,
  have x_notin_s : x ∉ s,
  { intro x_in_s,
    have : edist x x > 0, from gt_of_gt_of_ge (H x_in_s) (zero_le ↑δ),
    exact (ne_of_gt this) (edist_self x)}, -- use h telling us that x is far from all elements of s
  have s_sub_t : s ⊆ t , from subset_insert x s,
  have s_ne_t : s ≠ t , from ne_insert_of_not_mem s x_notin_s,
  have t_sub_S : t ⊆ S, from insert_subset.mpr ⟨xS, s_sub_S⟩,
  have : coarsely_separated_with δ t,
  { rintros z (rfl | zs) y (rfl | ys), -- Thanks Patrick Massot
    { exact λ h, (h rfl).elim },
    { exact λ hzy, H ys },
    { intro hzy,
      rw edist_comm,
      exact H zs },
    { exact s_sep zs ys }},
  exact s_ne_t (s_max t s_sub_t t_sub_S this),
end

/--
The set of all `δ`-coarsely separated subsets of `S`.
This is only used in the proof of `exists_max_coarsely_separated_in_with`
-/
def all_coarsely_separated_in_with (δ : ℝ≥0) (S : set α) : set (set α) :=
{t : set α | t ⊆ S ∧ coarsely_separated_with δ t}

/--
Any `⊆`-chain of `δ`-coarsely separated subsets of `S` has an upper bound: their union.
This is only used in the proof of `exists_max_coarsely_separated_in_with`
-/
lemma chain_of_coarsely_separated_in_with (δ : ℝ≥0)
  (S : set α) (𝒸 ⊆ all_coarsely_separated_in_with δ S) :
zorn.chain has_subset.subset 𝒸 →
  (∃ (ub : set α) (H : ub ∈ all_coarsely_separated_in_with δ S),
    ∀ (s : set α), s ∈ 𝒸 → s ⊆ ub) :=
begin
  intro 𝒸chain,
  unfold zorn.chain at 𝒸chain,
  let 𝒞 : set α := 𝒸.sUnion,
  have : 𝒞 ⊆ S, by
  { apply set.sUnion_subset ,
    rintros s s_in_𝒸,
    have : s ⊆ S, from (set.mem_of_subset_of_mem H s_in_𝒸).left,
    exact ‹s ⊆ S›,},
  have : coarsely_separated_with δ 𝒞, by
  { rintros x x_in_𝒞,
    rcases set.mem_sUnion.mp x_in_𝒞 with ⟨t,t_in_𝒸,x_in_t⟩,
    let t_coarse := set.mem_of_subset_of_mem H t_in_𝒸,
    rintros y y_in_𝒞,
    rcases set.mem_sUnion.mp y_in_𝒞 with ⟨r,r_in_𝒸,y_in_r⟩,
    let r_coarse := set.mem_of_subset_of_mem H r_in_𝒸,
    intro x_ne_y,
    cases (classical.em (t = r)) with t_eq_r t_ne_r,
    { have y_in_t : y ∈ t, from  t_eq_r.symm ▸ y_in_r,
      exact t_coarse.right x_in_t y_in_t x_ne_y},
    { cases 𝒸chain t_in_𝒸 r_in_𝒸 t_ne_r with t_sub_r r_sub_t,
      { have x_in_r : x ∈ r, from set.mem_of_subset_of_mem t_sub_r x_in_t,
        exact r_coarse.right x_in_r y_in_r x_ne_y,},
      { have y_in_t : y ∈ t, from set.mem_of_subset_of_mem r_sub_t y_in_r,
        exact t_coarse.right x_in_t y_in_t x_ne_y,},},},
  have H' : 𝒞 ∈ all_coarsely_separated_in_with δ S, from ⟨‹𝒞 ⊆ S›, this⟩,
  use [𝒞,H'],
  rintros s s_in_𝒸,
  exact set.subset_sUnion_of_mem s_in_𝒸,

end

/--
Given any `δ` and subset `S` of `α`, there exists a maximal `δ`-coarsely separated subset of `S`.
-/
theorem exists_max_coarsely_separated_in_with (δ : ℝ≥0) (S : set α) :
  ∃ s : set α, max_coarsely_separated_in_with δ s S :=
begin
  let 𝒮 : set (set α) := all_coarsely_separated_in_with δ S,
  rcases zorn.zorn_subset 𝒮 (chain_of_coarsely_separated_in_with δ S) with ⟨M,M_in_𝒮,M_max⟩,
  use [M,M_in_𝒮.left,M_in_𝒮.right],
  rintros t M_sub_t t_sub_S t_coarse,
  exact (M_max t ⟨t_sub_S, t_coarse⟩ M_sub_t).symm,
end

/--
Given any `δ` and subset `S` of `α`, there exists a `δ`-coarsely separated `δ`-coarsely dense subset of `S`.
-/
theorem exists_coarsely_separated_net_in_with (δ : ℝ≥0) (S : set α) :
  ∃ s ⊆ S, coarsely_separated_net_in_with δ δ s S :=
begin
  rcases exists_max_coarsely_separated_in_with δ S with ⟨s, s_sub_S, s_sep, s_max_sep⟩,
  use s,
  split,
  { exact s_sub_S },
  { exact max_coarsely_separated_in_is_net ⟨s_sub_S, s_sep, s_max_sep⟩ },
end

end coarsely_separated_net

end subspace


section map_closeness

variables {α: Type u} {β : Type v} {ι : Type w} [pseudo_emetric_space α] [pseudo_emetric_space β]

/--
Two maps `f g` from `ι` to a pseudo-emetric space `β` are `K`-close if for all `x : ι`, the distance between `f x` and `g x` is at most `K`.
-/
def close_maps_with (K : ℝ≥0) (f g : ι → β) :=
∀ x : ι , edist (f x) (g x) ≤ K

namespace close_maps_with

/--
Any map `f` is `0`-close to itself.
-/
lemma refl (f : ι → β) : close_maps_with 0 f f := λ x, by simp

/--
Being `K`-close in symmetric.
-/
lemma symm {K : ℝ≥0} {f g : ι → β} :
  close_maps_with K f g →  close_maps_with K g f :=
begin
  intros acw x,
  rw ←edist_comm,
  exact acw x,
end

/--
If `f` is `K`-close to `g`, which is `L`-close to `h`, then `f` is `(K+L)`-close to `h`.
-/
lemma trans {K L : ℝ≥0} {f g h: ι → β} (c : close_maps_with K f g) (d : close_maps_with L g h) :
  close_maps_with (K + L) f h :=
λ x, calc edist (f x) (h x) ≤ edist (f x) (g x) + edist (g x) (h x) : edist_triangle _ _ _
                        ... ≤ ↑K        + ↑L                        : add_le_add (c x) (d x)

/--
If `s` is `ε`-coarsely dense in `α`, there exists a map `ret: α → s` such that the two composites of `ret` with `coe: s → α` are `ε`-close to the identities.
-/
lemma of_dense_subset_with {ε : ℝ≥0} {s : set α} (cdw : coarsely_dense_with ε s) :
∃ retract : α → subtype s,
  close_maps_with ε (coe ∘ retract) id ∧
  close_maps_with ε (retract ∘ coe) id :=
begin
    -- First we restate `cdw` in terms the axiom of choice likes:
  have cdw' : ∀ x : α, ∃ y : subtype s, edist x ↑y ≤ ε, by {
    intro x,
    rcases cdw (mem_univ x) with ⟨y,ys,yd⟩,
    exact ⟨⟨y,ys⟩,yd⟩,
    },
  rcases classical.axiom_of_choice cdw' with ⟨ret, good⟩,
  use ret,
  split ;
  { intros x,
    dsimp,
    specialize good x,
    rw edist_comm,
    exact good,},
end

end close_maps_with

/--
The maps `f` and `g` are close if there exists some `K` such that they are `K`-close.
-/
def close_maps  (f g : ι → β) := ∃ K : ℝ≥0, close_maps_with K f g

namespace close_maps

infix `∥`:50 := close_maps

lemma refl (f : ι → β) : f ∥ f := ⟨0, close_maps_with.refl f⟩

lemma symm  {f g : ι → β} : f ∥ g →  g ∥ f :=
λ ⟨K,cw⟩, ⟨K,close_maps_with.symm cw⟩

lemma trans {f g h : ι → β} :  f ∥ g → g  ∥  h →  f ∥ h :=
λ ⟨K,cwf⟩ ⟨L,cwg⟩, ⟨K+L,close_maps_with.trans cwf cwg⟩

/--
If `s` is coarsely dense in `α`, there exists a map `ret: α → s` such that the two composites of `ret` with `coe: s → α` are close to the identities.
-/
lemma of_dense_subset_with  {s : set α} (cd : coarsely_dense s) :
  ∃ retract : α → subtype s, (coe ∘ retract) ∥ id ∧ (retract ∘ coe) ∥ id :=
let
  ⟨ε,cdw⟩ := cd,
  ⟨ret,back,forth⟩ := close_maps_with.of_dense_subset_with

 cdw
in
  ⟨ret,⟨ε,back⟩,⟨ε,forth⟩⟩

end close_maps

namespace coarsely_dense_with

/--
The range of an endomorphism `f : α → α` that is `C`-close to the identity is `C`-coarsely dense in `α`.
-/
lemma of_range_of_coarse_identity {C : ℝ≥0} {f : α → α}
  (close_maps : close_maps_with C id f) :
coarsely_dense_with C (range f) :=
λ x hx, ⟨(f x), mem_range_self x , (close_maps x)⟩

/--
Given `f : α → β` and `g : β → α` such that `g∘f`  is `C`-close to the identity, the range of `g` is `C`-coarsely dense in `α`.
-/
lemma of_range_of_coarse_retract
  {C : ℝ≥0}  {g : β → α} {f : α → β}  (retract : close_maps_with C (g ∘ f) id ) :
  coarsely_dense_with C (range g) :=
let
  comp_dense := coarsely_dense_with.of_range_of_coarse_identity retract.symm,
  dense := comp_dense.weaken (range_comp_subset_range f g) (rfl.subset) (le_rfl)
in
  coarsely_dense_with.of_coarsely_dense_with_in_univ dense

end coarsely_dense_with

namespace coarsely_dense

lemma of_range_of_coarse_identity {f : α → α} (close_maps : id ∥ f) :
  coarsely_dense (range f) :=
let ⟨C,close⟩ := close_maps in ⟨C,coarsely_dense_with.of_range_of_coarse_identity close⟩

lemma of_range_of_coarse_retract
   {g : β → α} {f : α → β}  (coarse_retract : (g ∘ f) ∥ id ) :
  coarsely_dense (range g) :=
let ⟨C,rr⟩ := coarse_retract in ⟨C,coarsely_dense_with.of_range_of_coarse_retract rr⟩

end coarsely_dense


end map_closeness
