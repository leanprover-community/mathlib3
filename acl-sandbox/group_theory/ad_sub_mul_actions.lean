import data.finset.pointwise
import group_theory.group_action.sub_mul_action
import group_theory.group_action.fixing_subgroup

import tactic

-- import .mathlib
-- import .pairs

open_locale pointwise

section sub_mul_action

open mul_action

section monoid
variables {G : Type*} [monoid G] {X : Type*} [mul_action G X]

/-- Stabilizers in monoid sub_mul_action coincide with stabilizer -/
lemma stabilizer_submonoid_of_sub_mul { Y : sub_mul_action G X } (y : Y) :
  stabilizer.submonoid G y = stabilizer.submonoid G (y : X) :=
  begin
    ext g,
    simp only [mem_stabilizer_submonoid_iff,
      ← sub_mul_action.coe_smul, set_like.coe_eq_coe]
  end

/-- Orbits in sub_mul_action coincide with orbits -/
-- useful ?
lemma orbit_of_sub_mul {Y : sub_mul_action G X} (y : Y) :
  (orbit G y : set X) = orbit G (y : X) := rfl

end monoid

section group

open mul_action
variables {G : Type*} [group G] {X : Type*} [mul_action G X]

/-- Stabilizers in sub_mul_action coincide with stabilizer -/
lemma stabilizer_of_sub_mul { Y : sub_mul_action G X } (y : Y) :
  stabilizer G y = stabilizer G (y : X) :=
  begin
    ext g,
    simp only [mem_stabilizer_iff,
      ← sub_mul_action.coe_smul, set_like.coe_eq_coe]
  end


end group

end sub_mul_action


section Actions_on_subsets
open_locale pointwise

section scalar
variables {G : Type*} {X : Type*} [has_scalar G X]

/- Remove subpairs
/-- If G acts on X, explicit action on subpairs of X -/
@[simp]
def has_scalar.subpair_apply (g : G) (x y : X) :
  g • ({x,y} : set X) = {g • x, g • y} :=
begin
  change (λ w, g • w) '' {x, y} = {g • x, g • y},
  rw set.image_pair,
end
-/

/-- If G acts on X, then G acts on lists of X -/
instance : has_scalar G (list X) := { smul := λ g s, list.map (λ x, g • x) s }

lemma smul_take (l : list X) (n : ℕ) (g : G) :
  (g • l).take n = g • l.take n :=
begin
  change (list.map (λ x, g • x) l).take n = list.map (λ x, g • x) (l.take n),
  rw list.map_take
end

lemma smul_drop (l : list X) (n : ℕ) (g : G) :
  (g • l).drop n = g • l.drop n :=
begin
  change (list.map (λ x, g • x) l).drop n = list.map (λ x, g • x) (l.drop n),
  rw list.map_drop
end

lemma smul_append (l1 l2 : list X)  (g : G) :
  g • (l1 ++ l2) = g • l1 ++ g • l2 :=
begin
  change list.map (λ x, g • x) (l1 ++ l2) =
    (list.map (λ x, g • x) l1) ++ (list.map (λ x, g • x) l2),
  rw list.map_append,
end

@[simp]
lemma smul_cons (a : X) (l : list X) (g : G) :
  g • (a :: l) = (g • a) :: (g • l) :=
begin
  change list.map (λ x, g • x) (a :: l) =
    (g • a) :: (list.map (λ x, g • x) l),
  rw list.map_cons
end

@[simp]
lemma smul_nil (g : G) : g • (list.nil : list X) = list.nil :=
begin
  change list.map (λ x, g • x) (list.nil : list X) = list.nil,
  rw list.map_nil,
end

-- Useless : in data.finset.pointwise
/-
/-- If G acts on X, then G acts on finite subsets of X -/
instance [decidable_eq X] : has_scalar G (finset X) :=
{ smul := λ g s, finset.image (λ x, g • x) s }
-/

/- Inutile grâce à finset.mem_smul_finset
lemma mem_smul_finset_iff [decidable_eq X] (a : X) (s : finset X) (g : G) :
  a ∈ g • s ↔ a ∈ g • (s : set X) :=
begin
  split,
  { intro h,
    change a ∈ set.image (λ x, g • x) (s : set X),
    rw ← finset.coe_image,
    exact h },
  { intro h,
    change a ∈ finset.image (λ x , g • x) s,
    rw [← finset.mem_coe,  finset.coe_image],
    exact h }
end
-/
end scalar

section mul_action

section monoid

variables (G : Type*) [monoid G] (X : Type*) [mul_action G X]

/- instance : -- (G : Type*) [monoid G] (X : Type*) [mul_action G X] :
  mul_action G (set X) :=  -- let ssGX := scalar_on_set_of G X in
{ one_smul := λ b, begin  simp only [one_smul, set.image_id'], end,
  mul_smul := λ g h s,
begin
  change (λ x, (g * h) • x)'' s = (λ x, g • x) '' ((λ x, h • x) '' s),
  rw set.image_image,
  funext x,
  simp only [function.comp_app, mul_smul],
end  }
-/

instance : mul_action G (list X) :=
{ one_smul := λ l,
begin
  conv_rhs { rw ← list.map_id l,  },
  apply list.map_congr,
  intros x hx, rw one_smul, refl
end,
mul_smul := λ g h l,
begin
  change list.map (λ x, (g * h) • x) l = list.map (λ x, g • x) (list.map (λ x, h • x) l),
  rw list.map_map,
  funext x,
  simp only [function.comp_app, mul_smul],
end }


/- lemma finset.image_congr {α β : Type*} [decidable_eq α] [decidable_eq β]
  {f g : α → β} {s : finset α} (h : ∀ (a : α), a ∈ s → f a = g a) :
  finset.image f s = finset.image g s :=
by safe [finset.ext_iff, iff_def]
 -/

instance mul_action.finset_of [decidable_eq X]:
  mul_action G (finset X) :=
{ one_smul := λ s,
begin
  conv_rhs { rw ← @finset.image_id _ s },
  change finset.image (λ x, (1 : G) • x) s = finset.image id s,
  apply finset.image_congr,
  intros a _, apply one_smul,
end,
mul_smul := λ g h s,
begin
  change finset.image (λ x, (g * h) • x) s = finset.image (λ x, g • x) (finset.image (λ x, h • x) s),
  rw finset.image_image,
  funext x,
  simp only [function.comp_app, mul_smul],
end,
}


/- Use has_scalar.subpair_apply
/-- If a monoid G acts on X, it acts on subpairs of X -/
def action_on_subpairs_of_apply : -- {G : Type*} [monoid G] {X : Type*} [mul_action G X] :
  ∀ (g : G) (x y : X), g • ({x,y} : set X) = {g • x, g • y} :=
  begin
    intros g x y,
    change (λ w, g • w) '' {x, y} = {g • x, g • y},
    ext a, split,

    { intro ha,
    obtain ⟨w, hw⟩ := ha,
    simp only [set.mem_insert_iff, set.mem_singleton_iff] at hw ⊢,
    cases hw.left with hx hy,
    rw ← hx, rw hw.right, apply or.intro_left, exact rfl,
    rw ← hy, rw hw.right, apply or.intro_right, exact rfl,
     },

    intro ha,
    simp only [set.mem_insert_iff, set.mem_singleton_iff] at ha,
    cases ha with hx hy,
    rw hx, use x,  split,
    simp only [set.mem_insert_iff, true_or, eq_self_iff_true],
    rw hy, use y, split,
    simp only [set.mem_insert_iff, set.mem_singleton, or_true],
  end
-/

end monoid

section group

variables {G : Type*} [group G] {X : Type*} [mul_action G X]

open mul_action

/-
subtype.coe_mk : ∀ (a : ?M_1) (h : ?M_2 a), ↑⟨a, h⟩ = a

set_like.coe_mk : ∀ (x : ?M_2) (hx : x ∈ ?M_4), ↑⟨x, hx⟩ = x
set_like.mem_coe : ?M_5 ∈ ↑?M_4 ↔ ?M_5 ∈ ?M_4
set_like.coe_mem : ∀ (x : ↥?M_4), ↑x ∈ ?M_4

set_like.eta : ∀ (x : ↥?M_4) (hx : ↑x ∈ ?M_4), ⟨↑x, hx⟩ = x
-/

variables (G X)

/- Remomve pairs
/-- If a *group* G acts on X, it acts on pairs of X -/
def action_on_pairs_of : sub_mul_action G (set X) :=
{ carrier := pair.pairs_of X,
  smul_mem' := λ g s hs,
  begin
    change (λ x, g • x) '' s ∈ pair.pairs_of X,
    rw ← subtype.coe_mk s hs,
    apply pair.map  (mul_action.injective g),
  end }
-/

/-- If a *group* G acts on X, it acts on nodup_list of X -/
def mul_action.nodup_list_of : sub_mul_action G (list X) :=
{ carrier := { l : list X | l.nodup },
  smul_mem' := λ g b hb, list.nodup.map (mul_action.injective g) hb }

def mul_action.nodup_list_of.has_coe :
  has_coe (mul_action.nodup_list_of G X) (list X) :=
  { coe := begin rintro ⟨l, hl⟩, exact l, end }

/-- Action on the complement of an invariant subset -/
def sub_mul_action_of_compl (Y : sub_mul_action G X) : sub_mul_action G X := {
carrier := Yᶜ,
smul_mem' := λ g x,
  by simp only [set_like.mem_coe, set.mem_compl_eq, sub_mul_action.smul_mem_iff', imp_self] }

lemma sub_mul_action_of_compl_def (Y : sub_mul_action G X) :
  (sub_mul_action_of_compl G X Y).carrier = Yᶜ := rfl

/-- Action of stabilizer of a point on the complement -/
def sub_mul_action_of_stabilizer (a : X) : sub_mul_action (stabilizer G a) X := {
carrier := { a }ᶜ,
smul_mem' := λ g x,
begin
  simp only [set.mem_compl_eq, set.mem_singleton_iff],
  rw not_imp_not,
  rw smul_eq_iff_eq_inv_smul,
  intro hgx, rw hgx,
  apply symm, rw ← smul_eq_iff_eq_inv_smul,
  conv_rhs { rw ← mem_stabilizer_iff.mp (set_like.coe_mem g) },
  refl,
end }

lemma sub_mul_action_of_stabilizer_def (a : X) :
  (sub_mul_action_of_stabilizer G X a).carrier = { a }ᶜ := rfl

lemma sub_mul_action_of_stabilizer_neq (a : X) (x : ↥(sub_mul_action_of_stabilizer G X a)) :
  ↑x ≠ a :=
begin
  let hx := sub_mul_action.mem_carrier.mpr (set_like.mem_coe.mpr (set_like.coe_mem x)),
  rw sub_mul_action_of_stabilizer_def at hx,
  simp at hx,
  exact hx
end

variables (M α : Type*) [group M] [mul_action M α]

variable {α}
def sub_mul_action_of_fixing_subgroup (s : set α) :
  sub_mul_action (fixing_subgroup M s) α := {
carrier := sᶜ,
smul_mem' :=
begin
  intros c x,
  simp only [set.mem_compl_iff],
  intros hx hcx, apply hx,
  rw [← one_smul M x, ← inv_mul_self ↑c, mul_smul],

  change ↑(c⁻¹) • c • x ∈ s,
  rw (mem_fixing_subgroup_iff M).mp (set_like.coe_mem c⁻¹) (c • x) hcx,
  exact hcx,
end }

lemma sub_mul_action_of_fixing_subgroup_def {s : set α} :
  (sub_mul_action_of_fixing_subgroup M s).carrier = sᶜ := rfl

lemma sub_mul_action_of_fixing_subgroup_not_mem {s : set α}
  (x : sub_mul_action_of_fixing_subgroup M s) :
  ↑x ∉ s :=
begin
  suffices : ↑x ∈ (sub_mul_action_of_fixing_subgroup M s).carrier,
  refine set.mem_compl this,
  rw sub_mul_action.mem_carrier,
  simp only [set_like.mem_coe, set_like.coe_mem]
end

lemma sub_mul_action_of_fixing_subgroup_of_fixing_subgroup_def (s t : set α) :
  coe '' (sub_mul_action_of_fixing_subgroup
    (fixing_subgroup M s)
    (coe ⁻¹' t : set (sub_mul_action_of_fixing_subgroup M s))).carrier
    = (sub_mul_action_of_fixing_subgroup M (s ∪ t)).carrier :=
begin
  ext x,
  simp only [sub_mul_action_of_fixing_subgroup_def,
    set.mem_compl_iff, set.mem_union_eq,
    set.mem_image, set.mem_preimage],
  split,
  { rintro ⟨x, hx, rfl⟩,
    exact not_or (sub_mul_action_of_fixing_subgroup_not_mem _ _) hx },
  { intro hx,
    have hx' : x ∈ (sub_mul_action_of_fixing_subgroup M s).carrier,
    { rw sub_mul_action_of_fixing_subgroup_def,
      refine set.mem_compl _,
      exact mt (or.inl) hx },
    use ⟨x, hx'⟩,
    split,
    { simp only [set.mem_preimage, subtype.coe_mk],
      exact mt (or.inr) hx },
    { simp only [subtype.coe_mk] } }
end

lemma sub_mul_action_of_fixing_subgroup_of_stabilizer_def (a : α) (s : set α) :
  coe '' (sub_mul_action_of_fixing_subgroup
    (stabilizer M a)
    (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a))).carrier
    = (sub_mul_action_of_fixing_subgroup M (insert a s)).carrier :=
begin
  ext x,
  simp only [sub_mul_action_of_fixing_subgroup_def,
    set.mem_compl_iff, set.mem_insert_iff,
    set.mem_preimage,
    set.mem_image],
  split,
  { rintro ⟨x, hx, rfl⟩,
    apply not_or _ hx,
    { apply  sub_mul_action_of_stabilizer_neq } },
  { intro hx,
    have hx' : x ∈ (sub_mul_action_of_stabilizer M α a).carrier,
    { rw sub_mul_action_of_stabilizer_def,
      simp only [set.mem_compl_eq, set.mem_singleton_iff],
      exact mt (or.inl) hx },
    use ⟨x, hx'⟩,
    simp only [subtype.coe_mk],
    exact and.intro (mt (or.inr) hx) rfl }
end

end group

end mul_action

end Actions_on_subsets

variables (G : Type*) [group G] (X : Type*) [decidable_eq X] [mul_action G X]

-- lemma test (s : finset X) (g : G) : g • (s : set X) = (g • s : set X) := rfl


-- At least one of the next two lemmas is redundant
/- Unused
lemma action_on_pairs_of.ne (G : Type*) [group G] (X : Type*) [mul_action G X]
  (a b : X) (h_ab : ({a, b} : set X) ∈ action_on_pairs_of G X) : a ≠ b :=
begin
  obtain ⟨a', b', h, hp ⟩ := h_ab,
  cases em (a' = a) with ha ha',
  { rw ha at hp h,
    have hb : b' = b,
    { let w : b' ∈ {a, b'} := is_in_subpair_right,
      rw ← hp at w,
      cases (is_in_subpair_iff.mp w) with hb' hb',
      exfalso, exact h hb'.symm, exact hb' },
    rw hb at h, exact h,  },
  { have ha : a' = b,
    { let w : a' ∈ {a', b'} := is_in_subpair_left,
      rw ← hp at w,
      cases (is_in_subpair_iff.mp w) with ha'' ha'',
      exfalso, exact ha' ha'', exact ha'' },
    rw ha at ha' h,
    intro h, exact ha' h.symm }
end
-/

/- Unused
lemma action_on_pairs_of.mem_of (G : Type*) [group G] (X : Type*) [mul_action G X]
  (a b : X) (hab : a ≠ b) :
  ({a, b} : set X) ∈ action_on_pairs_of G X :=
begin
  split,
  use b, swap, use a,
  split, exact hab,  refl,
end
-/
/- Does not type and Unusable
lemma action_on_pairs_of.mem_of
  (a b : X) (hab : a ≠ b) :
  ({a, b} : set X) ∈ action_on_pairs_of G X :=
begin
  refine pair.is_mem, exact hab,
end
-/


/- Unused, see .pairs

lemma action_on_pairs_of.mk₀ {G X : Type*} [group G] [mul_action G X]
  (a b : X) (hab : a ≠ b) : action_on_pairs_of G X :=
⟨({a,b} : set X), action_on_pairs_of.mem_of G X a b hab⟩

lemma action_on_pairs_of.mk {G X : Type*} [group G] [mul_action G X]
  {a b : X} (hab : a ≠ b) : action_on_pairs_of G X :=
  pair.mk hab

lemma action_on_pairs_of.def {G : Type*} [group G] {X : Type*} [mul_action G X]
  {a b : X} (hab : a ≠ b) :
  ({a, b} : set X) = ↑(pair.mk hab) := pair.is_def hab
-/

/-
lemma action_on_pairs_of.def₀ (G : Type*) [group G] (X : Type*) [mul_action G X]
  (a b : X) (hab : a ≠ b) : ({a, b} : set X) = (action_on_pairs_of.mk₀ a b  hab : set X) :=
begin
  -- have h : action_on_pairs_of.mk G X a b hab = ⟨({a,b} : set X), action_on_pairs_of.mem_of G X a b hab⟩,
  let x : action_on_pairs_of G X := action_on_pairs_of.mk G X a b hab,
  let hx : ({a,b} : set X) ∈ action_on_pairs_of G X := action_on_pairs_of.mem_of G X a b hab,
  let hx' := x.prop,
  type_check sub_mul_action.carrier  ,
  type_check x.val,
  type_check (↑x : set X),

  have h : (x.val : set X) = {a,b},
    {  simp,  },

--   let h := set_like.coe_mk ({a, b} : set X) hx,

  rw ← set_like.coe_mk ({a, b} : set X)  hx,
  apply subtype.mk_eq_mk.mpr ,

  -- rw ← subtype.val_eq_coe,
  apply set_like.coe_eq_coe.mpr,
  refl,

end -/
