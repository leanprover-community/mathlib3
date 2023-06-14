/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import .sub_mul_actions
import .multiple_transitivity
import group_theory.group_action.defs


-- import group_theory.group_action.fixing_subgroup
-- import group_theory.group_action.sub_mul_action

open_locale pointwise

open mul_action

variables  (G : Type*) [group G] {α : Type*} [mul_action G α]

/- The goal is to easify the proof of the following result and,
above all, make it useful :
namely, if we know something about the action of (stabilizer G s) on s,
for example that it is (pre)primitive.
-/

example (s : set α) (B : set α) (hB : is_block G B) :
  is_block (stabilizer G s) (B ∩ s)  :=
begin
  rw is_block.def_one at hB ⊢,
  rintro ⟨g, hg : g • s = s⟩,
  change g • (B ∩ s) = B ∩ s ∨ disjoint (g • (B ∩ s)) (B ∩ s),
  rw [set.smul_set_inter, hg],
  cases hB g with  hB_eq hB_dis,
  { apply or.intro_left, rw hB_eq, },
  { apply or.intro_right,
    apply disjoint.inter_right, apply disjoint.inter_left, exact hB_dis, },
end

-- In a first try, I had used this lemma which seems to be useful.
lemma stabilizer_smul_mem_iff (s : set α) (g : G) (hg : g ∈ stabilizer G s) (x : α) :
  g • x ∈ s ↔ x ∈ s :=
begin
  rw mem_stabilizer_iff at hg,
  rw [← hg, set.smul_mem_smul_set_iff, hg],
end



/- However, it does not seem easy to use this result later on,
because (stabilizer G s) has not be given its action on s.
An intermediate step is the following example. -/

example (s : set α) [decidable_pred s] (B : set α) (hB : is_block (equiv.perm α) B) :
  is_block (equiv.perm s) (coe ⁻¹' B : set s) :=
begin
  rw is_block.def_one at hB ⊢,
  intro g,
  suffices : ∃ (k : stabilizer (equiv.perm α) s),
    (∀ (x : s) , coe(g • x) = (k : equiv.perm α) • (x : α)),
  obtain ⟨k, hk⟩ := this,
  suffices : g • (coe ⁻¹' B) = coe ⁻¹' (k • B), rw this,
  cases hB k with hB_eq hB_dis,
  { change k • B = B at hB_eq,
    apply or.intro_left, rw hB_eq, },
  { apply or.intro_right,
    refine disjoint.preimage coe hB_dis, },
  -- g • (coe ⁻¹' B) = coe ⁻¹' (k • B),
  { ext,
    simp only [set.mem_preimage, set.mem_smul_set_iff_inv_smul_mem],
    suffices : ↑(g⁻¹ • x) = k⁻¹ • ↑x, rw this,
    set y := g⁻¹ • x,
    have hy : x = g • y, by rw smul_inv_smul,
    rw [eq_inv_smul_iff, hy, hk y],
    refl, },
  -- ∃ (k : stabilizer G s), ∀ (x : s) , coe(g • x) = (k : equiv.perm α) • (x : α))
  { have : g.of_subtype ∈ stabilizer (equiv.perm α) s,
    { rw mem_stabilizer_iff,
      ext x,
      split,
      { rintro ⟨y, hy, rfl⟩,
        simp only [equiv.perm.smul_def],
        rw ← subtype.coe_mk y hy,
        rw equiv.perm.of_subtype_apply_coe ,
        rw ← equiv.perm.smul_def, simp only [subtype.coe_prop] },
      { intro hx,
        let y := g⁻¹ • (⟨x, hx⟩ : s),
        use y,
        split,
        exact y.prop,
        rw [equiv.perm.smul_def, equiv.perm.of_subtype_apply_coe, ←equiv.perm.smul_def],
        rw smul_inv_smul,
        refl, } },
    use g.of_subtype,
    { exact this, },
    { intro x,
      simp only [equiv.perm.smul_def, subgroup.coe_mk],
      change _ = g.of_subtype • ↑x,
      rw equiv.perm.smul_def,
      rw equiv.perm.of_subtype_apply_coe }, },
end

/- This is not so satisfactory. In fact, what the previous proofs do, is emulating
the proof of
`is_block_preimage :
  ∀ (j : α →ₑ[φ] β) {B : set β}, is_block H β → is_block G (⇑j ⁻¹' B)`
in the presence of `mul_action G α` and `mul_action H β`,
with `φ : G → H`.
Let us try to use it, rather than reproving it.
We need to introduce adequate equivariant maps between `mul_action`s.

The point is that we don't have a natural map
`equiv.perm s → G`, but we have obvious maps
`stabilizer G s → equiv.perm s` and `stabilizer G s → G`
so we'll have to do it in two steps.

The second, `stabilizer G s → G` is just inclusion, but
the first map is best done via the natural `mul_action` of
`stabilizer G s` on `s` and `to_perm`  -/

/-- The instance that makes the stabilizer of a set acting on that set -/
instance has_smul.stabilizer (s : set α) :
  has_smul ↥(stabilizer G s) ↥s := {
smul := λ ⟨g, hg⟩ ⟨x, hx⟩, ⟨g • x,
  begin
    rw ← mem_stabilizer_iff.mp hg,
    exact set.smul_mem_smul_set hx,
  end⟩, }

@[simp]
lemma has_smul.stabilizer_def  (s : set α)
  (g : stabilizer G s) (x : s) : coe (g • x)  = (g : G) • (x : α) :=
begin
  rw ← subtype.coe_eta g g.prop,
  rw ← subtype.coe_eta x x.prop,
  refl,
end

/-- The mul_action of stabilizer a set on that set -/
instance mul_action.of_stabilizer' (s : set α) :
  mul_action (stabilizer G s) s := {
one_smul := λ ⟨x, hx⟩,
by  rw [← subtype.coe_inj, has_smul.stabilizer_def, subgroup.coe_one, one_smul],
mul_smul := λ ⟨g, hg⟩ ⟨k, hk⟩ ⟨x, hx⟩,
begin
  rw [← subtype.coe_inj, submonoid.mk_mul_mk],
  simp only [has_smul.stabilizer_def, subtype.coe_mk, mul_action.mul_smul],
end }

lemma mul_action.of_stabilizer_def' (s : set α) (g : stabilizer G s) (x : s) :
  (g : G) • (x : α) = g • (x : α) := rfl

lemma mul_action.of_stabilizer_set_def' (s : set α) (g : stabilizer G s) (t : set α) :
  (g : G) • t = g • t :=
begin
refl,
end

lemma equiv.perm.of_subtype.mem_stabilizer (s : set α) [decidable_pred s] (g : equiv.perm ↥s) :
  equiv.perm.of_subtype g ∈ stabilizer (equiv.perm α) s :=
begin
  rw mem_stabilizer_iff,
  ext, split,
  { rintro ⟨y, hy, rfl⟩,
    simp only [equiv.perm.smul_def],
    rw equiv.perm.of_subtype_apply_of_mem g hy,
    simp only [subtype.coe_prop] },
  { intro hx,
    suffices : ∃ (y : s), (⟨x, hx⟩ : ↥s) = g • y,
    obtain ⟨⟨y, hy⟩, hxy⟩ := this,
    use (⟨y, hy⟩ : ↥s),
    rw [← subtype.coe_mk x hx, hxy],
    simp only [hy, equiv.perm.of_subtype_apply_of_mem,
      subtype.coe_mk, equiv.perm.smul_def, eq_self_iff_true, and_self],
    obtain ⟨y⟩ := equiv.surjective g (⟨x, hx⟩ : ↥s),
    use y, simp only [← h, equiv.perm.smul_def], },
end


/- So let's do it ! -/
example (s : set α) [decidable_pred s] (B : set α) (hB : is_block (equiv.perm α) B) :
  is_block (equiv.perm s) (coe ⁻¹' B : set s) :=
begin
  let φ : stabilizer (equiv.perm α) s → equiv.perm s := to_perm,
  let j : s →ₑ[φ] s := {
  to_fun := id,
  map_smul' := λ g x, rfl
  },
  rw ← set.image_id (coe ⁻¹' B),
  apply is_block_image j,
  -- surjectivity of φ,
  { intro g,
    use equiv.perm.of_subtype g,
    apply equiv.perm.of_subtype.mem_stabilizer,
    { ext ⟨x, hx⟩,
      simp only [hx, equiv.perm.of_subtype_apply_of_mem, to_perm_apply,
        has_smul.stabilizer_def, subtype.coe_mk, equiv.perm.smul_def], }, },
  apply function.bijective.injective,
  apply function.bijective_id,

  let ψ : stabilizer (equiv.perm α) s → equiv.perm α := coe,
  let k : s →ₑ[ψ] α := {
  to_fun := coe,
  map_smul' := λ g x, by simp,},
  apply is_block_preimage k hB,
end

/- To prove the required surjectivity -/
variable (α)
def equivariant_map_id : α →[G] α := {
to_fun := id,
map_smul' := λ g x, rfl }

variable {α}
def equivariant_map_of_stabilizer_coe (s : set α) [decidable_pred s] :
  let φ: stabilizer G s → G := coe in s →ₑ[φ] α := {
to_fun := coe,
map_smul' := λ g x, by simp,}

def equivariant_map_of_stabilizer_to_perm (s : set α) [decidable_pred s] :
let φ : stabilizer G s → equiv.perm s := to_perm in
  s →ₑ[φ] s := {
to_fun := id,
map_smul' := λ g x, rfl }

lemma surjective_of_stabilizer_smul (s : set α) [decidable_pred s] :
  function.surjective (equivariant_map_of_stabilizer_to_perm (equiv.perm α) s).to_smul_map :=
begin
  intro g,
  use g.of_subtype,
  { rw mem_stabilizer_iff,
    ext x,
    split,
    { rintro ⟨y, hy, rfl⟩,
      simp only [equiv.perm.smul_def],
      rw ← subtype.coe_mk y hy,
      rw equiv.perm.of_subtype_apply_coe ,
      rw ← equiv.perm.smul_def, simp only [subtype.coe_prop] },
    { intro hx,
      let y := g⁻¹ • (⟨x, hx⟩ : s),
      use y,
      split,
      exact y.prop,
      rw [equiv.perm.smul_def, equiv.perm.of_subtype_apply_coe, ←equiv.perm.smul_def],
      rw smul_inv_smul,
      refl, } },
 { ext,
   rw [equivariant_map_of_stabilizer_to_perm, equivariant_map.to_smul_map],
    simp only [equiv.perm.smul_def, equiv.perm.of_subtype_apply_coe, to_perm_apply,
      has_smul.stabilizer_def, subgroup.coe_mk], },
end


example (s : set α) [decidable_pred s] (B : set α) (hB : is_block (equiv.perm α) B) :
  is_block (equiv.perm s) (coe ⁻¹' B : set s) :=
begin
  rw ← set.image_id (coe ⁻¹' B),
  apply is_block_image (equivariant_map_of_stabilizer_to_perm (equiv.perm α) s),
  apply surjective_of_stabilizer_smul,
  apply function.bijective.injective,
  apply function.bijective_id,
  apply is_block_preimage (equivariant_map_of_stabilizer_coe (equiv.perm α) s) hB,
end


/- This is much clearer.
But we want a general purpose lemma that can serve for
other groups than `equiv.perm s`
 -/

lemma le.is_block {H K : subgroup G} (hHK : H ≤ K) {B : set α} (hfB : is_block K B) :
  is_block H B :=
begin
  rw is_block.def_one, rintro ⟨g, hg⟩,
  simpa only using is_block.def_one.mp hfB ⟨g, hHK hg⟩,
end

lemma is_block_of_top (H : subgroup G) {B : set α}
  (hB : is_block H B) (hH : H = ⊤): is_block G B :=
begin
  rw is_block.def_one at hB ⊢,
  intro g,
  refine hB ⟨g, _⟩,
  rw hH, apply subgroup.mem_top,
end

lemma is_block_preimage_coe (s : set α) [decidable_pred s]
  (H : subgroup (equiv.perm s))
  -- (hH : ∀ g ∈ H, ∃ (k : stabilizer G s), (to_perm k: equiv.perm s) = g)
  (hH : H ≤ subgroup.map (mul_action.to_perm_hom (stabilizer G s) s) ⊤)
  (B : set α) (hB : is_block G B) :
  is_block H (coe ⁻¹' B : set s) :=
begin
  apply le.is_block,
  exact hH,
  let φ : stabilizer G s → (subgroup.map (mul_action.to_perm_hom (stabilizer G s) s) ⊤) := λ u,
  (⟨to_perm_hom (stabilizer G s) s u,
    by simp only [subgroup.mem_map, subgroup.mem_top, exists_true_left, exists_apply_eq_apply]⟩),
  let j : s →ₑ[φ] s := {
  to_fun := id,
  map_smul' := λ g x, rfl
  },
  rw ← set.image_id (coe ⁻¹' B),
  apply is_block_image j,
  { rintro ⟨g, hg⟩,
    obtain ⟨k, hk, rfl⟩ := hg,
    use k, refl, },
  apply function.bijective.injective,
  apply function.bijective_id,

  let ψ: stabilizer G s → G := coe,
  let k : s →ₑ[ψ] α := {
    to_fun := coe, map_smul' := λ g x, by simp only [has_smul.stabilizer_def]},
  apply is_block_preimage k hB,
end

example (s : set α) [decidable_pred s] (B : set α) (hB : is_block (equiv.perm α) B) :
  is_block (equiv.perm s) (coe ⁻¹' B : set s) :=
begin
  apply is_block_of_top,
  refine is_block_preimage_coe (equiv.perm α) s (⊤) _  B hB,
  { intros g _,
    obtain ⟨k, hk⟩ := surjective_of_stabilizer_smul s  g,
    use k,
    rw ← hk,
    simp only [subgroup.coe_top, set.mem_univ, to_perm_hom_apply, true_and],
    refl, },
  refl,
end

lemma surjective_of_stabilizer_smul' [decidable_eq α] [fintype α]
  (s : set α) [decidable_pred s] (hsc : 2 ≤ fintype.card (sᶜ : set α))  :
  function.surjective (equivariant_map_of_stabilizer_to_perm (alternating_group α) s).to_smul_map :=
begin
  resetI,
  have : ∃ (a b : (sᶜ : set α)), a ≠ b,
  { rw ← fintype.one_lt_card_iff, exact hsc, },
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := this, simp at hab,
  let k := equiv.swap a b,
  have hk_sign : k.sign = -1,  simp only [equiv.perm.sign_swap', hab, if_false],
  have hk_apply : ∀ x ∈ s , k x = x,
  { intros x hx,
    refine equiv.swap_apply_of_ne_of_ne _ _,
    intro hxa, rw set.mem_compl_iff at  ha, apply ha, rw ← hxa, exact hx,
    intro hxb, rw set.mem_compl_iff at  hb, apply hb, rw ← hxb, exact hx, },
  have hk_mem : k ∈ stabilizer (equiv.perm α) s,
  { rw mem_stabilizer_iff,
    suffices : k • s ≤ s,
    { apply le_antisymm,
      exact this,
      intros x hx,
      rw set.mem_smul_set_iff_inv_smul_mem,
      simp only [equiv.swap_inv], -- equiv.perm.smul_def],
      apply this,
      simp [hx],
      use x, apply and.intro hx, simp, },
    { intro x, rintro ⟨y, hy, rfl⟩,
      rw [equiv.perm.smul_def, hk_apply y hy],
      exact hy, } },

  intro g,
  have hg : g.of_subtype ∈ stabilizer (equiv.perm α) s,
  { rw mem_stabilizer_iff,
    ext x,
    split,
    { rintro ⟨y, hy, rfl⟩,
      simp only [equiv.perm.smul_def],
      rw ← subtype.coe_mk y hy,
      rw equiv.perm.of_subtype_apply_coe ,
      rw ← equiv.perm.smul_def, simp only [subtype.coe_prop] },
    { intro hx,
      let y := g⁻¹ • (⟨x, hx⟩ : s),
      use y,
      split,
      exact y.prop,
      rw [equiv.perm.smul_def, equiv.perm.of_subtype_apply_coe, ←equiv.perm.smul_def],
      rw smul_inv_smul,
      refl, } },
   use ite (g.sign = 1) (g.of_subtype) (g.of_subtype * k),
   {  simp only [equiv.perm.mem_alternating_group],
      by_cases hg_sign : g.sign = 1,
      simp only [hg_sign, eq_self_iff_true, if_true, equiv.perm.sign_of_subtype],

      simp only [hg_sign, hk_sign, if_false, equiv.perm.sign_mul, equiv.perm.sign_of_subtype,
        mul_neg, mul_one],
      { cases int.units_eq_one_or (equiv.perm.sign g),
        exfalso, exact hg_sign h,
        rw h, apply neg_neg, } },
    { by_cases hg_sign : g.sign = 1,
      simp only [hg_sign, eq_self_iff_true, if_true],
      exact hg,
      simp only [hg_sign, if_false],
      dsimp at hk_mem hg ⊢,
      change (g.of_subtype * k) • s = s,
      rw [mul_action.mul_smul, hk_mem, hg], },
    { ext,
      rw [equivariant_map_of_stabilizer_to_perm, equivariant_map.to_smul_map],
      simp only [to_perm_apply, has_smul.stabilizer_def, subgroup.coe_mk],
      by_cases hg_sign : g.sign = 1;
            simp only [hg_sign, eq_self_iff_true, if_true, if_false],
      -- ⟨⇑equiv.perm.of_subtype g, _⟩ • ↑x = ↑(⇑g x)
        change equiv.perm.of_subtype g ↑x = ↑(g x),
        rw equiv.perm.of_subtype_apply_coe ,
          -- ⟨⇑equiv.perm.of_subtype g * k, _⟩ • ↑x = ↑(⇑g x)
        change (equiv.perm.of_subtype g * k) • ↑x = ↑(g x),
        rw mul_action.mul_smul,
        simp only [equiv.perm.smul_def],
        rw [hk_apply, equiv.perm.of_subtype_apply_coe],
        exact x.prop, },
end


example [decidable_eq α] [fintype α]
  (s : set α) [decidable_pred s] (hsc : 2 ≤ fintype.card (sᶜ : set α))
  (B : set α) (hB : is_block (alternating_group α) B) :
  is_block (equiv.perm s) (coe ⁻¹' B : set s) :=
begin
  apply is_block_of_top,
  refine is_block_preimage_coe (alternating_group α) s (⊤) _  B hB,
  { intros g _,
    obtain ⟨k, hk⟩ := surjective_of_stabilizer_smul' s hsc g,
    use k,
    rw ← hk,
    simp only [subgroup.coe_top, set.mem_univ, to_perm_hom_apply, true_and],
    refl, },
  refl,
end

/- We might wish a more general lemma -/
variable {G}
lemma is_block_preimage_comap {H : Type*} [group H] {β : Type*} [mul_action H β]
  {φ : H →* G} (f : β →ₑ[φ] α)
  (K : subgroup G) (L : subgroup H)
  (hHK : L ≤ K.comap φ)
  {B : set α} (hB : is_block K B) :
  is_block L (f ⁻¹' B) :=
begin
  apply le.is_block,  exact hHK,
  let f' : β →ₑ[monoid_hom.subgroup_comap φ K] α := {
  to_fun := f,
  map_smul' := λ ⟨m, hm⟩ x,
  begin
    change f (m • x) = _, rw f.map_smul,
    apply congr_arg, refl,
  end },
  apply mul_action.is_block_preimage f' hB,
end


example (s : set α) [decidable_pred s] (B : set α) (hB : is_block (equiv.perm α) B) :
  is_block (equiv.perm s) (coe ⁻¹' B : set s) :=
begin
  rw ← set.image_id (coe ⁻¹' B),
  apply is_block_image (equivariant_map_of_stabilizer_to_perm (equiv.perm α) s),
  apply surjective_of_stabilizer_smul,
  apply function.bijective.injective,
  apply function.bijective_id,
  apply is_block_preimage (equivariant_map_of_stabilizer_coe (equiv.perm α) s) hB,
end

#exit




/- With the inclusion `φ : stabilizer G s →* G`,
we need an equivariant map `j s →ₑ[φ] α` such that `j ⁻¹' B = B ∩ s` -/



-- open_locale classical pointwise
/-- The instance that makes the stabilizer of a set acting on that set -/
instance has_smul.stabilizer (s : set α) :
  has_smul ↥(stabilizer G s) ↥s := {
smul := λ ⟨g, hg⟩ ⟨x, hx⟩, ⟨g • x,
  begin
    rw ← mem_stabilizer_iff.mp hg,
    exact set.smul_mem_smul_set hx,
  end⟩, }

@[simp]
lemma has_smul.stabilizer_def  (s : set α)
  (g : stabilizer G s) (x : s) : coe (g • x)  = (g : G) • (x : α) :=
begin
  rw ← subtype.coe_eta g g.prop,
  rw ← subtype.coe_eta x x.prop,
  refl,
end

/-- The mul_action of stabilizer a set on that set -/
instance mul_action.of_stabilizer (s : set α) :
  mul_action (stabilizer G s) s := {
one_smul := λ ⟨x, hx⟩,
by  rw [← subtype.coe_inj, has_smul.stabilizer_def, subgroup.coe_one, one_smul],
mul_smul := λ ⟨g, hg⟩ ⟨k, hk⟩ ⟨x, hx⟩,
begin
  rw [← subtype.coe_inj, submonoid.mk_mul_mk],
  simp only [has_smul.stabilizer_def, subtype.coe_mk, mul_action.mul_smul],
end }

lemma mul_action.of_stabilizer_def (s : set α) (g : stabilizer G s) (x : s) :
  (g : G) • (x : α) = g • (x : α) := rfl

lemma mul_action.of_stabilizer_set_def (s : set α) (g : stabilizer G s) (t : set α) :
  (g : G) • t = g • t :=
begin
refl,
end

def mul_action.of_stabilizer' (s : set α) :
  sub_mul_action ↥(stabilizer G s) α := {
carrier := s,
smul_mem' :=
begin
 rintro ⟨g, hg⟩, intros x hx,
 change g • x ∈ s,
 rw mem_stabilizer_iff at hg,
 rw [← hg, set.smul_mem_smul_set_iff],
 exact hx,
end }

def equivariant_inclusion (s : set α) : s →[stabilizer G s] α := {
to_fun := λ x, x,
map_smul' := λ g x, by simp only [has_smul.stabilizer_def, id.def, mul_action.of_stabilizer_def] }



section alternating


lemma stabilizer.is_preprimitive (s : set α) (hs : (sᶜ : set α).nontrivial):
  is_preprimitive (stabilizer (alternating_group α) s) s :=
begin
  let φ : stabilizer (alternating_group α) s → equiv.perm s := mul_action.to_perm,
  suffices hφ : function.surjective φ,

  let f : s →ₑ[φ] s := {
  to_fun := id,
  map_smul' := λ ⟨g, hg⟩ ⟨x, hx⟩,
  by simp only [id.def, equiv.perm.smul_def, to_perm_apply], },
  suffices hf : function.bijective f, --  := function.bijective_id,
  let this := is_preprimitive_of_bijective_map_iff',

  specialize this φ,
  rw is_preprimitive_of_bijective_map_iff hφ hf,
  exact equiv.perm.is_preprimitive s,

  sorry,

  suffices : ∃ k : equiv.perm (sᶜ : set α), equiv.perm.sign k = -1,
  obtain ⟨k, hk_sign⟩ := this,
  have hks : (equiv.perm.of_subtype k) • s = s,
  { rw ← mem_stabilizer_iff,
    apply equiv.perm.of_subtype.mem_stabilizer', },

  -- function.surjective φ
  have hφ : function.surjective φ,
  { intro g,
    have hgs : (equiv.perm.of_subtype g) • s = s,
    apply equiv.perm.of_subtype.mem_stabilizer,

    have hminus_one_ne_one : (-1 : units ℤ) ≠ 1,
    { intro h, rw [← units.eq_iff, units.coe_one, units.coe_neg_one] at h, norm_num at h, },

    let g' := ite (equiv.perm.sign g = 1)
      (equiv.perm.of_subtype g)
      (equiv.perm.of_subtype g * (equiv.perm.of_subtype k)),

    use g',

    rw equiv.perm.mem_alternating_group,
    cases int.units_eq_one_or (equiv.perm.sign g) with hsg hsg;
    { dsimp [g'], -- rw hsg,
      simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false,
        equiv.perm.sign_of_subtype,
        equiv.perm.sign_mul, mul_neg, mul_one, neg_neg, hsg, hk_sign], },

    rw mem_stabilizer_iff,
    change (ite (equiv.perm.sign g = 1)
      (equiv.perm.of_subtype g)
      (equiv.perm.of_subtype g * (equiv.perm.of_subtype k))) • s = s,
    cases int.units_eq_one_or (equiv.perm.sign g) with hsg hsg,
    { simp only [hsg,  eq_self_iff_true, if_true],
      exact hgs, },
    { simp only [hsg, hminus_one_ne_one, if_false],
      rw mul_smul, rw hks, exact hgs, },

    dsimp [φ],
    cases int.units_eq_one_or (equiv.perm.sign g) with hsg hsg,
    { dsimp [g'], simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false],
      ext,
      simp only [to_perm_apply, has_smul.stabilizer_def, subtype.coe_mk],
      change equiv.perm.of_subtype g ↑x = ↑(g x),
      exact equiv.perm.of_subtype_apply_coe g x, },
    { dsimp [g'], simp only [hsg, eq_self_iff_true, if_true, hminus_one_ne_one, if_false],
      ext,
      simp only [to_perm_apply, has_smul.stabilizer_def, subtype.coe_mk],
      change ((equiv.perm.of_subtype g) * (equiv.perm.of_subtype k)) ↑x = ↑(g x),
      rw equiv.perm.mul_apply ,
      rw equiv.perm.of_subtype_apply_of_not_mem k _,
      exact equiv.perm.of_subtype_apply_coe g x,
      rw set.not_mem_compl_iff, exact x.prop, }, },

  rw @is_preprimitive_of_bijective_map_iff _ _ _ _ _ _ _ _ φ f hφ hf,
  exact equiv.perm.is_preprimitive s,
  sorry,

  obtain ⟨a, ha, b, hb, hab⟩ := hs,
  use equiv.swap ⟨a, ha⟩ ⟨b, hb⟩,
  rw equiv.perm.sign_swap _,
  rw ← function.injective.ne_iff (subtype.coe_injective),
  simp only [subtype.coe_mk], exact hab,
end

example (s t : set α) (a : α) (ha : a ∈ s ⊓ t) : a ∈ s :=
begin
  apply @inf_le_left _ _ s t,  exact ha,
end

lemma stabilizer.is_preprimitive' (s : set α) (hsc : sᶜ.nontrivial)
  (G : subgroup (equiv.perm α)) (hG : stabilizer (equiv.perm α) s ⊓ alternating_group α ≤ G) :
  is_preprimitive (stabilizer G s) s :=
begin
  let φ : stabilizer (alternating_group α) s → stabilizer G s := λ g,
  begin
    use (g : alternating_group α), apply hG, rw subgroup.mem_inf,
    split,
    { let h := g.prop, rw mem_stabilizer_iff at h ⊢, exact h, },
    { exact set_like.coe_mem ↑g, },
    { rw mem_stabilizer_iff, let h := g.prop, rw mem_stabilizer_iff at h, exact h, },
  end,
  let f : s →ₑ[φ] s := {
    to_fun := id,
    map_smul' := λ ⟨⟨m, hm'⟩, hm⟩ ⟨a, ha⟩, rfl, },
  have hf : function.surjective f := function.surjective_id,
  apply is_preprimitive_of_surjective_map hf,
  apply stabilizer.is_preprimitive,
  exact hsc,
end

end alternating



#exit




def equivariant_map.inclusion' (α : Type*) [decidable_eq α] (s : set α):
  s →ₑ[λ u : equiv.perm s, (⟨u.of_subtype,
begin
  rw mem_fixing_subgroup_iff,
  intros x hx,
  rw set.mem_compl_iff at hx,
  simp only [equiv.perm.smul_def],
  rw equiv.perm.of_subtype_apply_of_not_mem,
  exact hx,
end⟩ : fixing_subgroup (equiv.perm α) sᶜ)]
    sub_mul_action.of_fixing_subgroup (equiv.perm α) sᶜ := {
to_fun := λ x, ⟨x,
begin
  rw [sub_mul_action.of_fixing_subgroup.mem_iff, set.not_mem_compl_iff],
  exact x.prop,
end⟩,
map_smul' := λ g x,
begin
  simp only [← subtype.coe_inj, sub_mul_action.coe_smul, equiv.perm.smul_def, sub_mul_action.coe_mk],
  change _ = (equiv.perm.of_subtype g) • ↑x,
  simp only [equiv.perm.smul_def, equiv.perm.of_subtype_apply_coe],
end }

/-- The instance that makes the stabilizer of a set acting on that set -/
instance has_smul.stabilizer (G : Type*) [group G] {α : Type*} [mul_action G α] (s : set α) :
  has_smul ↥(stabilizer G s) ↥s := {
smul := λ ⟨g, hg⟩ ⟨x, hx⟩, ⟨g • x,
  begin
    rw ← mem_stabilizer_iff.mp hg,
    exact set.smul_mem_smul_set hx,
  end⟩, }

lemma has_smul.stabilizer_def (G : Type*) [group G] {α : Type*} [mul_action G α] (s : set α)
  (g : stabilizer G s) (x : s) : coe (g • x)  = (g : G) • (x : α) :=
begin
  rw ← subtype.coe_eta g g.prop,
  rw ← subtype.coe_eta x x.prop,
  refl,
end

/-- The mul_action of stabilizer a set on that set -/
instance mul_action.of_stabilizer (G : Type*) [group G] {α : Type*} [mul_action G α] (s : set α) :
  mul_action (stabilizer G s) s := {
one_smul := λ ⟨x, hx⟩,
by  rw [← subtype.coe_inj, has_smul.stabilizer_def, subgroup.coe_one, one_smul],
mul_smul := λ ⟨g, hg⟩ ⟨k, hk⟩ ⟨x, hx⟩,
begin
  rw [← subtype.coe_inj, submonoid.mk_mul_mk],
  simp only [has_smul.stabilizer_def, subtype.coe_mk, mul_action.mul_smul],
end }

/- /-- The monoid morphism from the stabilizer of a set to the group of permutations of that set -/
def set_stabilizer_to_perm (G : Type*) [group G] {α : Type*} [mul_action G α] (s : set α) :
  (stabilizer G s) →* equiv.perm s := {
to_fun := λ (g : stabilizer G s), ({
  to_fun := λ x, ⟨g • x,
  begin
    convert set.smul_mem_smul_set x.prop,
    apply symm,
    exact mem_stabilizer_iff.mp g.prop,
  end⟩,
  inv_fun := λ x, ⟨g⁻¹ • x,
  begin
    convert set.smul_mem_smul_set x.prop,
    apply symm,
    exact mem_stabilizer_iff.mp (g⁻¹).prop,
  end⟩,
  left_inv :=
  begin
    unfold function.left_inverse,
    rintro ⟨x, hx⟩,
    simp only [subtype.coe_mk, inv_smul_smul],
  end,
  right_inv :=
  begin
    unfold function.right_inverse,
    rintro ⟨x, hx⟩,
    simp only [subtype.coe_mk, smul_inv_smul],
  end, } : equiv.perm s),
map_one' :=
begin
  ext,
  simp only [one_smul, subtype.coe_eta, equiv.coe_fn_mk, equiv.perm.coe_one, id.def],
end,
map_mul' := λ ⟨g, hg⟩ ⟨k, hk⟩,
begin
  ext,
  simp only [subtype.coe_mk, submonoid.mk_mul_mk, equiv.coe_fn_mk, equiv.perm.coe_mul],
  change (g * k) • ↑x = g • k • ↑x,
  rw mul_action.mul_smul,
end }
 -/

def equivariant_map.inclusion (G : Type*) [group G] {α : Type*} [mul_action G α] (s : set α) :
  s →[stabilizer G s] α := {
to_fun := λ x, x,
map_smul' := λ ⟨g, hg⟩ ⟨x, hx⟩ , rfl }
