import analysis.normed.group.basic
import group_theory.free_group
import order.well_founded

/-! marked groups.
-/

noncomputable theory
open set function real

namespace geometric_group_theory

section marked_group

--  an S-generated group
structure marking (S : Type*) (G : Type*) [decidable_eq S] [group G] :=
(marking : free_group S →* G)
(is_surjective : function.surjective marking)

variables {S : Type*} [decidable_eq S]

def free_group_norm (f : free_group S) : ℕ := (free_group.to_word f).length

lemma empty_list {α : Type*} (l : list α) : l.length = 0 → l = list.nil := 
list.length_eq_zero.mp

lemma free_group_norm_zero (f : free_group S) : free_group_norm f = 0 → f = 1 := begin
  intro h,
  have fempty : free_group.to_word f = list.nil, { exact empty_list (free_group.to_word f) h },
  have h : free_group.mk (free_group.to_word f) = free_group.mk list.nil, {
    rw fempty,
  },
  rw free_group.to_word.mk at h,
  exact h
end

variables {G : Type*} [group G] (m : marking S G)

-- suggestion to use nat.find instead of nat.lt.is_well_order.wf.min
def group_norms (g : G) : set ℕ := (free_group_norm '' {x | m.marking x = g})

def group_norms_nonempty (g : G) : (group_norms m g).nonempty := 
  (by { apply set.nonempty.image, exact m.is_surjective g })

def group_norm (g : G) : ℕ := nat.lt.is_well_order.wf.min
  (group_norms m g) (group_norms_nonempty m g)

lemma to_word_inv_length (x : free_group S) : x⁻¹.to_word.length ≤ x.to_word.length :=
begin
  let xi := x⁻¹,
  let xw := x.to_word,
  let xiw := x⁻¹.to_word,
  let xwi := (x.to_word.map (λ (y : S × bool), (y.fst, !y.snd))).reverse,

  have xi_eq_mk_xwi : xi = free_group.mk xwi, by rw [←free_group.inv_mk, free_group.to_word.mk],
  have : free_group.reduce xwi = (free_group.mk xwi).to_word, by simpa only,
  have : free_group.reduce xwi = xiw, by rw [this, ←xi_eq_mk_xwi],
  have : free_group.red xwi xiw , from this ▸ free_group.reduce.red,

  have : xwi.length ≥ xiw.length, by {
    rcases free_group.red.length this with ⟨n,p⟩,
    exact le_iff_exists_add.mpr ⟨2*n,p⟩,
  },
  rw [list.length_reverse,list.length_map] at this,
  exact this,
end

lemma to_word_mul_length (x y : free_group S) : (x*y).to_word.length ≤ x.to_word.length + y.to_word.length :=
begin
  let xy := x*y,
  let xyw := xy.to_word,
  let xwyw := x.to_word ++ y.to_word,

  have xy_eq_mk_xyw : xy = free_group.mk xwyw, by rw [←free_group.mul_mk,free_group.to_word.mk,free_group.to_word.mk],
  have : free_group.reduce xwyw = (free_group.mk xwyw).to_word, by simpa only,
  have : free_group.reduce xwyw = xyw, by rw [this,←xy_eq_mk_xyw],
  have : free_group.red xwyw xyw, from this ▸ free_group.reduce.red,

  have : xwyw.length ≥ xyw.length, by {
    rcases free_group.red.length this with ⟨n,p⟩,
    exact le_iff_exists_add.mpr ⟨2*n,p⟩,
  },
  rw list.length_append at this,
  exact this,
end

lemma group_norm_one (x : G) : group_norm m x = 0 ↔ x = 1 := begin
  split,
  { intro hzero,
    have h : (group_norm m x) ∈ (group_norms m x) := nat.lt.is_well_order.wf.min_mem (group_norms m x) (group_norms_nonempty m x),
    rw hzero at h,
    rcases h with ⟨y,ymem,normzero⟩,
    have yone : y = 1, { 
      exact free_group_norm_zero y normzero,
    },
    rw yone at ymem,
    finish -- can we replace it by a simple command?
  },
  { intro h, rw h,
    have h : 0 ∈ group_norms m 1 := begin
      rw group_norms,
      rw mem_image,
      use 1; finish
    end,
-- well_founded.min_le seems inaccessible
  let normzero := well_founded.not_lt_min nat.lt.is_well_order.wf (group_norms m 1) (group_norms_nonempty m 1) h,
  norm_num at normzero,
  exact normzero
  },
end

lemma group_norm_comm_le (x : G) : group_norm m x⁻¹ ≤ group_norm m x :=
begin
  have h : (group_norm m x) ∈ (group_norms m x) := nat.lt.is_well_order.wf.min_mem (group_norms m x) (group_norms_nonempty m x),
  rcases set.mem_image_iff_bex.1 h with ⟨y,ytox,yneqxn⟩,

  have yitoxi : m.marking y⁻¹ = x⁻¹, by
  { rw map_inv,simp only [inv_inj],exact ytox },

  have mon : (y⁻¹).to_word.length ≤ y.to_word.length, from to_word_inv_length y,
  have : (y⁻¹).to_word.length ∈ (group_norms m x⁻¹),
    from set.mem_image_iff_bex.2 ⟨y⁻¹, yitoxi, rfl⟩,
  apply le_trans (well_founded.min_le nat.lt.is_well_order.wf this (group_norms_nonempty m x⁻¹)),
  rw [←yneqxn],
  exact mon,
end

lemma group_norm_comm (x : G) : group_norm m x = group_norm m x⁻¹ := begin
  apply has_le.le.antisymm,
  { have := group_norm_comm_le m x⁻¹,
    rw (inv_inv x) at this,
    assumption, },
  { exact group_norm_comm_le m x, },
end

lemma group_norm_ineq (x y : G) : group_norm m (x*y) ≤ group_norm m x + group_norm m y := begin
  -- extract reps for x, y, use product for x*y
  have h : (group_norm m x) ∈ (group_norms m x) := nat.lt.is_well_order.wf.min_mem (group_norms m x) (group_norms_nonempty m x),
  rcases set.mem_image_iff_bex.1 h with ⟨z,ztox,zneqxn⟩,
  have k : (group_norm m y) ∈ (group_norms m y) := nat.lt.is_well_order.wf.min_mem (group_norms m y) (group_norms_nonempty m y),
  rcases set.mem_image_iff_bex.1 k with ⟨w,wtoy,wneqyn⟩,
  have one : m.marking w = y, from wtoy,
  have two : m.marking z = x, from ztox,

  have zwtoxy : m.marking (z*w) = x * y, by { rw map_mul, rw [one,two],},
  have mon : (z*w).to_word.length ≤ z.to_word.length + w.to_word.length, from to_word_mul_length z w,

  have : (z*w).to_word.length ∈ (group_norms m (x*y)),
    from set.mem_image_iff_bex.2 ⟨z*w, zwtoxy, rfl⟩,

  apply le_trans (well_founded.min_le nat.lt.is_well_order.wf this (group_norms_nonempty m (x * y))),
  rw [←zneqxn,←wneqyn],
  exact mon,
end

-- this is definitely not what we want... it should be for a [marked_group G], not a [group G]
instance : has_norm G := { norm := λ g, group_norm m g }

-- the library cybersquats normed_group, defining it for additive groups!
class normed_mul_group (m G : Type*) extends group G, has_norm G :=
(to_metric_space : metric_space G)
(dist_eq : ∀ (x y : G), has_dist.dist x y = ∥x⁻¹*y∥)

class marked_group (m G : Type*) := (group := G) (marking := m)
-- @[derive] ... group structure on G, norm coming from m

/- comments by Sébastien Gouëzel:

If you want to register your group as a metric space (where the distance depends on S), you will need to embrace the type synonym trick. Instead of a class, define a structure marking S G as you did. And then given a group G and a marking m, define a new type marked_group m G := G. On this new type, you can register the same group structure as on G, but you can also register a distance as m is now available to the system when you consider x y : marked_group m G.

    First, work with normed groups, and prove whatever you like here. Possibly adding new typeclass assumptions that say that the distance is proper or hyperbolic or whatever.
    Then, to construct instances of such normed groups, do it on type synonyms. For instance, given two types S and G with [group G], define marking S G as the space of markings of G parameterized by S. Then, given a group G and a marking m, define a typemarked_group G m := G as a copy of G, then define on it the group structure coming from G (with @[derive ...]) and the norm associated to m. Then marked_group G m will be an instance of a normed group.

-/

end marked_group

end geometric_group_theory
