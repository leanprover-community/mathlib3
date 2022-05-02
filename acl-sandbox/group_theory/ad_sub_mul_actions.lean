import data.finset.pointwise
import group_theory.group_action.sub_mul_action
import group_theory.group_action.fixing_subgroup

import .mul_action_bihom

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

def sub_mul_action_of_stabilizer.inclusion (a : X) :
  mul_action_bihom (stabilizer G a) (sub_mul_action_of_stabilizer G X a) G X := {
to_fun := λ x, id x,
to_monoid_hom := subgroup.subtype (stabilizer G a),
map_smul' := λ g x,
begin
  simp only [subgroup.coe_subtype, id.def, sub_mul_action.coe_smul_of_tower],
  refl,
end }

lemma sub_mul_action_of_stabilizer_def (a : X) :
  (sub_mul_action_of_stabilizer G X a).carrier = { a }ᶜ := rfl

lemma mem_sub_mul_action_of_stabilizer_iff (a : X) (x : X) :
  x ∈ sub_mul_action_of_stabilizer G X a ↔ x ≠ a := iff.rfl

/-
begin
  change (x ∈ (sub_mul_action_of_stabilizer G X a).carrier) ↔ _,
  rw sub_mul_action_of_stabilizer_def,
  simp only [set.mem_compl_eq, set.mem_singleton_iff],
end
-/

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

lemma sub_mul_action_smul (s : set α) (m : fixing_subgroup M s) (a : sub_mul_action_of_fixing_subgroup M s) :
  (coe (m • a) : α) = m • a :=
begin
  refl,
end

def sub_mul_action_of_fixing_subgroup_inclusion' (s : set α) :
  mul_action_bihom (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s) M α := {
to_fun := λ a, id a,
to_monoid_hom := subgroup.subtype (fixing_subgroup M s),
map_smul' := λ m a,
begin
  simp only [subgroup.coe_subtype, id.def, sub_mul_action.coe_smul_of_tower],
  refl,
end
}

lemma sub_mul_action_of_fixing_subgroup_def {s : set α} :
  (sub_mul_action_of_fixing_subgroup M s).carrier = sᶜ := rfl

lemma mem_sub_mul_action_of_fixing_subgroup_iff {s : set α} {x : α} :
  x ∈ sub_mul_action_of_fixing_subgroup M s ↔ x ∉ s := iff.rfl

lemma sub_mul_action_of_fixing_subgroup_not_mem {s : set α}
  (x : sub_mul_action_of_fixing_subgroup M s) :
  ↑x ∉ s :=
begin
  suffices : ↑x ∈ (sub_mul_action_of_fixing_subgroup M s).carrier,
  refine set.mem_compl this,
  rw sub_mul_action.mem_carrier,
  simp only [set_like.mem_coe, set_like.coe_mem]
end

def sub_mul_action_of_fixing_subgroup_inclusion {s t : set α} (hst : s ⊇ t) :
  mul_action_bihom (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s)
   (fixing_subgroup M t) (sub_mul_action_of_fixing_subgroup M t) :=
let h : fixing_subgroup M s ≤ fixing_subgroup M t :=
begin intro m, simp only [mem_fixing_subgroup_iff],
  intros hs y hyt, exact hs y (hst hyt)
end
in let h' : (sub_mul_action_of_fixing_subgroup M s).carrier ≤ (sub_mul_action_of_fixing_subgroup M t).carrier :=
begin intro x, simp only [sub_mul_action_of_fixing_subgroup_def M],
  simp only [set.mem_compl_eq, not_imp_not],
  intro hxt, exact hst hxt,
end
in sub_mul_action_of_leq_bihom M α h h'

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

def sub_mul_action_of_fixing_subgroup_id (s : set α) :
  mul_action_bihom (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s)
    (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s) := {
to_fun := id,
to_monoid_hom := monoid_hom.id ↥(fixing_subgroup M s),
map_smul' := λ m a, rfl }


def sub_mul_action_of_fixing_subgroup_id_def (s : set α) :
let j := sub_mul_action_of_fixing_subgroup_id M s in
∀ (x : (sub_mul_action_of_fixing_subgroup M s)), (coe (j.to_fun x) : α) = x :=
begin
  intros j x,
  exact rfl
end

def sub_mul_action_of_fixing_subgroup_eq_bihom {s t : set α} (hst : s = t) :
  mul_action_bihom (fixing_subgroup M s) (sub_mul_action_of_fixing_subgroup M s)
    (fixing_subgroup M t) (sub_mul_action_of_fixing_subgroup M t) :=
let aux_fun : ∀ (x : sub_mul_action_of_fixing_subgroup M s), ↑x ∈ sub_mul_action_of_fixing_subgroup M t :=
begin intro x, rw ← hst, exact x.prop end
in let aux_hom : ∀ (m : fixing_subgroup M s), ↑m ∈ fixing_subgroup M t :=
begin intro m, rw ← hst, exact m.prop end
in {
to_fun := λ x, ⟨↑x, aux_fun x⟩,
to_monoid_hom := {
  to_fun := λm, ⟨↑m, aux_hom m⟩,
  map_one' := rfl,
  map_mul' := λ m m', rfl },
map_smul' := λ m x, rfl }

lemma sub_mul_action_of_fixing_subgroup_eq_bihom_def {s t : set α} (hst : s = t) :
  ∀ (x : sub_mul_action_of_fixing_subgroup M s),
  (((sub_mul_action_of_fixing_subgroup_eq_bihom M hst).to_fun x) : α) = x := λ x, rfl

def sub_mul_action_of_fixing_subgroup_union_bihom (s t : set α) : mul_action_bihom
  (fixing_subgroup M (s ∪ t)) (sub_mul_action_of_fixing_subgroup M (s ∪ t))
  (fixing_subgroup (fixing_subgroup M s) (coe ⁻¹' t : set (sub_mul_action_of_fixing_subgroup M s)))
    (sub_mul_action_of_fixing_subgroup (fixing_subgroup M s)
      (coe ⁻¹' t : set(sub_mul_action_of_fixing_subgroup M s))) := {
to_fun := λ x,
let px : ↑x ∉ s ∧ ↑x ∉ t :=
begin
  let px' : ↑x ∈ (sub_mul_action_of_fixing_subgroup M (s ∪ t)).carrier := x.prop,
  rw sub_mul_action_of_fixing_subgroup_def at px',
  simp only [set.compl_union, set.mem_inter_eq, set.mem_compl_eq] at px',
  exact px'
end
in let hx : ↑x ∈ sub_mul_action_of_fixing_subgroup M s :=
begin
  change ↑x ∈ (sub_mul_action_of_fixing_subgroup M s).carrier,
  rw sub_mul_action_of_fixing_subgroup_def,
  simp only [set.mem_compl_eq],
  exact px.left
end
in let hx' : (⟨↑x, hx⟩ : sub_mul_action_of_fixing_subgroup M s) ∈ sub_mul_action_of_fixing_subgroup (fixing_subgroup M s)
  (coe ⁻¹' t : set (sub_mul_action_of_fixing_subgroup M s)) :=
begin
  change (⟨↑x, hx⟩ : sub_mul_action_of_fixing_subgroup M s) ∈
    (sub_mul_action_of_fixing_subgroup (fixing_subgroup M s)
      (coe ⁻¹' t : set (sub_mul_action_of_fixing_subgroup M s))).carrier,
  rw sub_mul_action_of_fixing_subgroup_def ↥(fixing_subgroup M s),
  simp only [set.mem_compl_eq, set.mem_preimage, sub_mul_action.coe_mk],
  exact px.right
end
in ⟨⟨↑x, hx⟩, hx'⟩,
to_monoid_hom := {
  to_fun := λ m,
let pm : ↑m ∈ fixing_subgroup M s ∧ ↑m ∈ fixing_subgroup M t :=
  by simpa only [fixing_subgroup_union M, subgroup.mem_inf] using m.prop
in let hm' : (⟨↑m, pm.left⟩ : fixing_subgroup M s) ∈
  fixing_subgroup (fixing_subgroup M s)
    (coe ⁻¹' t : set ((sub_mul_action_of_fixing_subgroup M s))) :=
begin
  rw mem_fixing_subgroup_iff ↥(fixing_subgroup M s),
  intros x hx,
  simp only [set.mem_preimage] at hx,
  rw ← set_like.coe_eq_coe,
  conv_rhs { rw ← ((mem_fixing_subgroup_iff _).mp pm.right ↑x hx) },
  refl
end
in ⟨⟨↑m, pm.left⟩, hm'⟩,
  map_one' := by refl,
  map_mul' := λ m n, by refl },
map_smul' := λ m x, by refl }

lemma sub_mul_action_of_fixing_subgroup_union_bihom_def (s t : set α) :
  ∀ (x : (sub_mul_action_of_fixing_subgroup M (s ∪ t))),
  (((sub_mul_action_of_fixing_subgroup_union_bihom M s t).to_fun x) : α) = x := λ x, rfl

lemma fixing_subgroup_of_insert (a : α) (s : set (sub_mul_action_of_stabilizer M α a)) :
  fixing_subgroup M (set.insert a (coe '' s)) =
  (subgroup.map (subgroup.subtype _) (fixing_subgroup ↥(stabilizer M a) s) : subgroup M) :=
begin
  ext m,
  split,
  { intro hm,
    use m,
    { rw mem_stabilizer_iff,
      rw mem_fixing_subgroup_iff at hm,
      apply hm a (set.mem_insert a _) },
    { split,
      simp only [set_like.mem_coe , mem_fixing_subgroup_iff],
      intros y hy,
      rw mem_fixing_subgroup_iff at hm,

      let t : set α := set.insert a (coe '' s),
      suffices : ↑y ∈ t,
      { rw ← set_like.coe_eq_coe,
        conv_rhs { rw ← hm ↑y this},
        refl },
      apply set.mem_insert_of_mem,
      use ⟨y, hy, rfl⟩,
      refl } } ,
  { rintro ⟨n, hn, rfl⟩,
    simp only [subgroup.coe_subtype, set_like.mem_coe, mem_fixing_subgroup_iff] at hn ⊢,
    intros y hy,
    cases set.mem_insert_iff.mp hy with hy hy,
      -- y = a
      rw hy, simpa using n.prop,
      -- y ∈ s
      simp only [set.mem_image] at hy,
      obtain ⟨y, hy1, rfl⟩ := hy,
      conv_rhs { rw ← hn y hy1 },
      refl },
end

lemma sub_mul_action_of_fixing_subgroup_of_insert_eq (a : α) (s : set (sub_mul_action_of_stabilizer M α a)) :
  (sub_mul_action_of_fixing_subgroup M (set.insert a (coe '' s))).carrier =
  coe '' (sub_mul_action_of_fixing_subgroup (stabilizer M a) s).carrier :=
begin
  ext,
  simp only [set.mem_image, sub_mul_action.mem_carrier, set_like.mem_coe],
  split,
  { intro hx,
    rw mem_sub_mul_action_of_fixing_subgroup_iff M at hx,
    suffices : x ≠ a,
    { use x,
      split,
      { rw mem_sub_mul_action_of_fixing_subgroup_iff,
        intro h, apply hx, apply set.mem_insert_of_mem,
        use x,
        apply and.intro h, refl },
      refl } ,
    intro h, apply hx, rw h, apply set.mem_insert  },
    { rintro ⟨y, hy, rfl⟩,
    rw mem_sub_mul_action_of_fixing_subgroup_iff,
    intro hy',
    cases set.mem_insert_iff.mp hy' with h h,
    -- ↑y = a
    exact sub_mul_action_of_stabilizer_neq M α a y h,
    -- ↑y ∈ coe '' s
    simp only [set.mem_image, set_like.coe_eq_coe, exists_eq_right] at h,
    exact (mem_sub_mul_action_of_fixing_subgroup_iff (stabilizer M a)).mp hy h },
end

lemma mem_fixing_subgroup_of_mem {K : subgroup M} {m : K} {s t : set α} (hst : s ≤ t):
  m ∈ fixing_subgroup K t → ↑m ∈ fixing_subgroup M s := λ h x,
  begin
    conv_rhs { rw ← (mem_fixing_subgroup_iff M).mp h x (hst x.prop), },
    refl
  end

def sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom
  (a : α) (s : set (sub_mul_action_of_stabilizer M α a)) :
  mul_action_bihom
    (fixing_subgroup M (set.insert a (coe '' s) : set α))
      (sub_mul_action_of_fixing_subgroup M (insert a (coe '' s : set α)))
    (fixing_subgroup (stabilizer M a) s)
      (sub_mul_action_of_fixing_subgroup (stabilizer M a) s) := {
to_fun := λ x, ⟨⟨(x : α), begin
  rintro (h : (x : α) = a),
  apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
  rw h, apply set.mem_insert,
  end⟩,
  λ h, (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop $
    set.mem_insert_of_mem _ ⟨⟨(x : α), _⟩, ⟨h, rfl⟩⟩⟩,
-- Second golfing by KB
/- to_fun := λ x, ⟨⟨(x : α), begin
  rw mem_sub_mul_action_of_stabilizer_iff,
  intro h,
  apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
  rw h, apply set.mem_insert,
  end⟩,
  begin { intro h,
    apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
    apply set.mem_insert_of_mem,
    refine ⟨⟨(x : α), _⟩, ⟨h, rfl⟩⟩, }
  end⟩, -/
-- First golfing by KB
/- to_fun := λ x, ⟨⟨(x : α), begin
  rw mem_sub_mul_action_of_stabilizer_iff,
  intro h,
  apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
  rw h, apply set.mem_insert,
  end⟩,
  begin { rw mem_sub_mul_action_of_fixing_subgroup_iff (stabilizer M a),
    intro h,
    apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
    apply set.mem_insert_of_mem,
    refine ⟨⟨(x : α), _⟩, ⟨h, rfl⟩⟩, }
  end⟩,
-/
-- Initial version
/- to_fun := λ x,
begin
  suffices : ↑x ∈ sub_mul_action_of_stabilizer M α a,
  use x,
  { rw mem_sub_mul_action_of_fixing_subgroup_iff (stabilizer M a),
    intro h,
    apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
    apply set.mem_insert_of_mem,
    use x, apply and.intro h, simp only [sub_mul_action.coe_mk] },

  rw mem_sub_mul_action_of_stabilizer_iff,
  intro h,
  apply (mem_sub_mul_action_of_fixing_subgroup_iff M).mp x.prop,
  rw h, apply set.mem_insert
end, -/
to_monoid_hom := {
  to_fun := λ m, ⟨⟨(m : M), begin
    -- rw mem_stabilizer_iff,
    apply (mem_fixing_subgroup_iff M).mp m.prop,
    apply set.mem_insert
  end ⟩, λ ⟨x, hx⟩,
    begin
    simp only [← set_like.coe_eq_coe],
    refine (mem_fixing_subgroup_iff M).mp m.prop _ _,
    apply set.mem_insert_of_mem,
    exact ⟨x, hx, rfl⟩, end ⟩,
  -- Initial version
 /-  to_fun := λ m, begin
    suffices hm : ↑m ∈ stabilizer M a,
    { use ⟨m, hm⟩,
      rw mem_fixing_subgroup_iff,
      intros x hx,
      let hm' := (mem_fixing_subgroup_iff M).mp m.prop,
      rw ← set_like.coe_eq_coe,
      suffices : ↑x ∈ set.insert a (coe '' s),
      conv_rhs { rw ← (mem_fixing_subgroup_iff M).mp m.prop ↑x this },
      refl,
      apply set.mem_insert_of_mem,
      use x, exact ⟨hx, rfl⟩ },
    rw mem_stabilizer_iff,
    apply (mem_fixing_subgroup_iff M).mp m.prop,
    apply set.mem_insert,
  end, -/
  map_one' := rfl,
  map_mul' := λ m n, rfl },
map_smul' := λ m x, rfl
}

lemma sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_bijective
  (a : α) (s : set (sub_mul_action_of_stabilizer M α a)) :
  function.bijective (sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s).to_fun :=
begin
  split,
  { intros x y h,
    rw ← set_like.coe_eq_coe,
    suffices hx : (↑x : α) = ↑((sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s).to_fun x),
    suffices hy : (↑y : α) = ↑((sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s).to_fun y),
    rw hx, rw hy, rw h,
    refl, refl },
  { rintro ⟨⟨x, hx1⟩, hx2⟩,
    refine ⟨⟨x, _⟩, rfl⟩,
    -- ⊢ x ∈ sub_mul_action_of_fixing_subgroup M (insert a (coe '' s))
    rw mem_sub_mul_action_of_fixing_subgroup_iff,
    intro h, cases set.mem_insert_iff.mp h,
    { rw mem_sub_mul_action_of_stabilizer_iff at hx1, exact hx1 h_1 },
    { rw mem_sub_mul_action_of_fixing_subgroup_iff at hx2,
      apply hx2,
      obtain ⟨x1, hx1', rfl⟩ := h_1,
      simp only [set_like.eta],
      exact hx1' } },
end


def sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom'
  (a : α) (s : set (sub_mul_action_of_stabilizer M α a)) :
  mul_action_bihom
    (fixing_subgroup (stabilizer M a) s)
      (sub_mul_action_of_fixing_subgroup (stabilizer M a) s)
    (fixing_subgroup M (set.insert a (coe '' s) : set α))
      (sub_mul_action_of_fixing_subgroup M (insert a (coe '' s : set α))) := {
to_fun := λ x, ⟨(x : α), begin
  intro h,
  cases (set.mem_insert_iff).mp h with h h,
  { apply (mem_sub_mul_action_of_stabilizer_iff _ _ _ _).mp x.val.prop,
    simpa only using h, },
  { apply (mem_sub_mul_action_of_fixing_subgroup_iff _).mp x.prop,
    obtain ⟨y, hy, hy'⟩ := h,
    simp only [coe_coe, set_like.coe_eq_coe] at hy',
    rw ← hy', exact hy },
  end⟩,
to_monoid_hom := {
  to_fun := λ m, ⟨(m : M), λ ⟨y, hy⟩,  begin
    simp only [coe_coe, subtype.coe_mk],
    cases (set.mem_insert_iff).mp hy with hy hy,
    { rw hy,
      conv_rhs { rw ← (mem_stabilizer_iff).mp m.val.prop },
      refl },
    { obtain ⟨z, hz, rfl⟩ := hy,
      conv_rhs { rw ← (mem_fixing_subgroup_iff (stabilizer M a)).mp m.prop z hz },
      refl } end ⟩,
  map_one' := rfl,
  map_mul' := λ m n, rfl },
map_smul' := λ m x, rfl
}


lemma sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_bijective'
  (a : α) (s : set (sub_mul_action_of_stabilizer M α a)) :
  function.bijective (sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom' M a s).to_fun :=
begin
  split,
  { intros x y h,
    suffices hx : (↑x : α) = ((sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom' M a s).to_fun x),
    suffices hy : (↑y : α) = ↑((sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom' M a s).to_fun y),
    simp only [← set_like.coe_eq_coe, ← coe_coe],
    rw hx, rw hy, rw h,
    refl, refl },
  { rintro ⟨x,hx⟩, -- ⟨x, hx1⟩, hx2⟩,
    suffices : x ∈ sub_mul_action_of_stabilizer M α a,
    use x,
    { intro h, apply hx, apply set.mem_insert_of_mem,
      use x, apply and.intro h, refl },
    refl,
    { intro h, simp only [set.mem_singleton_iff] at h,
      apply hx, rw h, apply set.mem_insert } },
end

#exit

def sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom (a : α) (s : set α) : mul_action_bihom
  (fixing_subgroup M (set.insert a s : set α)) (sub_mul_action_of_fixing_subgroup M (insert a s))
  (fixing_subgroup (stabilizer M a) (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a)))
    (sub_mul_action_of_fixing_subgroup (stabilizer M a) (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a))) := {
to_fun := λ x,
let px : ↑x ≠ a ∧ ↑x ∉ s :=
begin
  let Hx : ↑x ∈ (sub_mul_action_of_fixing_subgroup M (insert a s)).carrier := x.prop,
  rw sub_mul_action_of_fixing_subgroup_def at Hx,
  simp only [set.mem_compl_eq, set.mem_insert_iff] at Hx,
  push_neg at Hx, exact Hx,
end
in let hx : ↑x ∈ sub_mul_action_of_stabilizer M α a :=
begin
  change ↑x ∈ (sub_mul_action_of_stabilizer M α a).carrier,
  rw sub_mul_action_of_stabilizer_def,
  simp only [set.mem_compl_eq, set.mem_singleton_iff],
  exact px.left
end
in let hx' : (⟨↑x, hx⟩ : sub_mul_action_of_stabilizer M α a) ∈
  sub_mul_action_of_fixing_subgroup
    (stabilizer M a)
    (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a)) :=
begin
  change _ ∈ (sub_mul_action_of_fixing_subgroup ↥(stabilizer M a) (coe ⁻¹' s)).carrier,
  rw sub_mul_action_of_fixing_subgroup_def ,
  simp only [set.mem_compl_eq, set.mem_preimage, sub_mul_action.coe_mk],
  exact px.right
end
in ⟨⟨↑x, hx⟩, hx'⟩,
to_monoid_hom := {
  to_fun := λ m,
  let pm : m • a = a ∧ ↑m ∈ fixing_subgroup M s :=
  begin
    let Hm := m.prop,
    rw mem_fixing_subgroup_iff at Hm ⊢,
    split,
    { refine Hm a _, apply set.mem_insert },
    { intros y hy, refine Hm y _,
      change y ∈ insert a s,
      rw set.mem_insert_iff,
      exact or.intro_right _ hy } end
  in let hm : ↑m ∈ stabilizer M a := mem_stabilizer_iff.mp pm.left
  in let hm' : (⟨↑m, hm⟩ : stabilizer M a) ∈ fixing_subgroup (stabilizer M a)
    (coe ⁻¹' s : set ((sub_mul_action_of_stabilizer M α a))) :=
  begin
    rw mem_fixing_subgroup_iff ↥(stabilizer M a),
    intros y hy,
    simp only [set.mem_preimage] at hy,
    rw ← set_like.coe_eq_coe,
    conv_rhs { rw ← ((mem_fixing_subgroup_iff _).mp pm.right ↑y hy) },
    refl
  end
  in ⟨⟨↑m, hm⟩, hm'⟩,
  map_one' := by refl,
  map_mul' := λ m m', by refl },
map_smul' := λ m a, by refl }


#exit


lemma sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_def (a : α) (s : set α) :
  ∀ (x : (sub_mul_action_of_fixing_subgroup M (insert a s))),
  (((sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s).to_fun x) : α) = x := λ x, rfl


def sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom' (a : α) (s : set α) : mul_action_bihom
  (fixing_subgroup (stabilizer M a) (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a)))
    (sub_mul_action_of_fixing_subgroup (stabilizer M a) (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a)))
    (fixing_subgroup M (set.insert a s : set α)) (sub_mul_action_of_fixing_subgroup M (insert a s))
:= {
to_fun := λ x,
let px : ↑x ≠ a ∧ ↑x ∉ s :=
begin
  split,
  { let Hxx : ↑↑x ∈ (sub_mul_action_of_stabilizer M α a).carrier := (x : sub_mul_action_of_stabilizer M α a).prop,
    rw sub_mul_action_of_stabilizer_def at Hxx,
    simpa using Hxx },
  { let Hx : ↑x ∈ (sub_mul_action_of_fixing_subgroup ↥(stabilizer M a) (coe ⁻¹' s)).carrier := x.prop,
    rw sub_mul_action_of_fixing_subgroup_def at Hx,
    simpa only [set.mem_compl_eq, set.mem_preimage] using Hx }
end
in let hx : ↑x ∈ sub_mul_action_of_stabilizer M α a :=
begin
  change ↑x ∈ (sub_mul_action_of_stabilizer M α a).carrier,
  rw sub_mul_action_of_stabilizer_def,
  simp only [set.mem_compl_eq, set.mem_singleton_iff],
  exact px.left
end
in let hx' : (⟨↑x, hx⟩ : sub_mul_action_of_stabilizer M α a) ∈
  sub_mul_action_of_fixing_subgroup
    (stabilizer M a)
    (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a)) :=
begin
  change _ ∈ (sub_mul_action_of_fixing_subgroup ↥(stabilizer M a) (coe ⁻¹' s)).carrier,
  rw sub_mul_action_of_fixing_subgroup_def ,
  simp only [set.mem_compl_eq, set.mem_preimage, sub_mul_action.coe_mk],
  exact px.right
end
in ⟨⟨↑x, hx⟩, hx'⟩,
to_monoid_hom := {
  to_fun := λ m,
  let pm : m • a = a ∧ ↑m ∈ fixing_subgroup M s :=
  begin
    let Hm := m.prop,
    rw mem_fixing_subgroup_iff at Hm ⊢,
    split,
    { refine Hm a _, apply set.mem_insert },
    { intros y hy, refine Hm y _,
      change y ∈ insert a s,
      rw set.mem_insert_iff,
      exact or.intro_right _ hy } end
  in let hm : ↑m ∈ stabilizer M a := mem_stabilizer_iff.mp pm.left
  in let hm' : (⟨↑m, hm⟩ : stabilizer M a) ∈ fixing_subgroup (stabilizer M a)
    (coe ⁻¹' s : set ((sub_mul_action_of_stabilizer M α a))) :=
  begin
    rw mem_fixing_subgroup_iff ↥(stabilizer M a),
    intros y hy,
    simp only [set.mem_preimage] at hy,
    rw ← set_like.coe_eq_coe,
    conv_rhs { rw ← ((mem_fixing_subgroup_iff _).mp pm.right ↑y hy) },
    refl
  end
  in ⟨⟨↑m, hm⟩, hm'⟩,
  map_one' := by refl,
  map_mul' := λ m m', by refl },
map_smul' := λ m a, by refl }

lemma sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom_def (a : α) (s : set α) :
  ∀ (x : (sub_mul_action_of_fixing_subgroup M (insert a s))),
  (((sub_mul_action_of_fixing_subgroup_of_stabilizer_bihom M a s).to_fun x) : α) = x := λ x, rfl


/-
let hm : ∀ (m : fixing_subgroup M (set.insert a s : set α)), ↑m ∈ stabilizer M a := λ m,
begin
  simp only [mem_stabilizer_iff],
  let Hm := m.prop,
  rw mem_fixing_subgroup_iff at Hm,
  refine Hm a (set.mem_insert a _)
end in
let hm': ∀ (m : fixing_subgroup M (set.insert a s : set α)),
  (⟨↑m, hm m⟩ : stabilizer M a) ∈ fixing_subgroup (stabilizer M a)
    (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a)) := λ m,
begin
  refine (mem_fixing_subgroup_iff ↥(stabilizer M a)).mpr _,
  intros x hx,
  let Hm := m.prop, rw mem_fixing_subgroup_iff at Hm,
  simp at hx,
  let Hmx := Hm x _,
  { rw ← set_like.coe_eq_coe,
    simp only [sub_mul_action.coe_smul_of_tower],
    conv_rhs { rw ← Hmx },
    refl },
  { apply set.mem_insert_of_mem, exact hx },
end in
λ m, ( ⟨⟨↑m, hm m⟩, hm' m⟩ : fixing_subgroup (stabilizer M a) (coe ⁻¹' s)),

to_fun :=
let ha : ∀ (x : sub_mul_action_of_fixing_subgroup M (insert a s : set α)),
  (x : α) ∈ coe '' (sub_mul_action_of_fixing_subgroup
    (stabilizer M a)
    (coe ⁻¹' s : set (sub_mul_action_of_stabilizer M α a))).carrier := sorry in
let ha' : ∀ (x : sub_mul_action_of_fixing_subgroup M (insert a s : set α)),

  sorry,
map_smul' := sorry,
  }
-/

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
