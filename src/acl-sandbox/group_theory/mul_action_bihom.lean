import data.finset.pointwise
import group_theory.group_action.sub_mul_action
import group_theory.group_action.fixing_subgroup

import tactic

-- import .mathlib
-- import .pairs

/- On veut étudier la situation suivante :

M and N are monoids,
there are actions of M on α and of N on β,
and I wish to consider pairs (φ : M →*N , f : α → β)
such that φ(m) • f(a) = f(m • a) for all m, a.

-/

open_locale pointwise

section monoid

variables (M : Type*) [monoid M] (X : Type*) [mul_action M X]
variables (N : Type*) [monoid N] (Y : Type*) [mul_action N Y]

structure mul_action_bihom :=
(to_fun : X → Y)
(to_monoid_hom : M →* N)
(map_smul' : ∀ m x, to_monoid_hom (m) • to_fun (x)
  = to_fun (m • x))

def sub_mul_action_of_leq_bihom {H K : submonoid M} (hHK : H ≤ K)
  {αH : sub_mul_action H X} {αK : sub_mul_action K X} (hHK' : αH.carrier ≤ αK.carrier) :
    mul_action_bihom H αH K αK := {
to_fun := λ x,
let hx : (coe x : X) ∈ αK.carrier := begin apply hHK', exact x.prop end
in ⟨x, hx⟩,
to_monoid_hom := {
  to_fun := λ m,
  let hm : (coe m : M) ∈ K := begin apply hHK, exact m.prop end in ⟨m, hm⟩,
  map_one' := rfl,
  map_mul' := λm n, rfl },
map_smul' := λ m x, rfl }

lemma sub_mul_action_of_leq_bihom_def {H K : submonoid M} (hHK : H ≤ K)
  {αH : sub_mul_action H X} {αK : sub_mul_action K X} (hHK' : αH.carrier ≤ αK.carrier) :
  ∀ (x : αH), ((sub_mul_action_of_leq_bihom M X hHK hHK').to_fun x : X) = x := λ x, rfl

def sub_mul_action_of_eq_bihom {H K : submonoid M} (hHK : H = K)
  {αH : sub_mul_action H X} {αK : sub_mul_action K X} (hHK' : αH.carrier = αK.carrier) :=
  sub_mul_action_of_leq_bihom M X (le_of_eq hHK) (le_of_eq hHK')

lemma sub_mul_action_of_leq_bihom.injective {H K : submonoid M} (hHK : H ≤ K)
  {αH : sub_mul_action H X} {αK : sub_mul_action K X} (hHK' : αH.carrier ≤ αK.carrier) :
  function.injective (sub_mul_action_of_leq_bihom M X hHK hHK').to_fun := λ x y hxy,
  begin simpa only [← set_like.coe_eq_coe] using hxy end

lemma sub_mul_action_of_leq_bihom.injective' {H K : submonoid M} (hHK : H ≤ K)
  {αH : sub_mul_action H X} {αK : sub_mul_action K X} (hHK' : αH.carrier ≤ αK.carrier) :
  function.injective (sub_mul_action_of_leq_bihom M X hHK hHK').to_monoid_hom := λ m n hmn,
  begin simpa only [← set_like.coe_eq_coe] using hmn end

lemma sub_mul_action_of_eq_bihom_def {H K : submonoid M} (hHK : H = K)
  {αH : sub_mul_action H X} {αK : sub_mul_action K X} (hHK' : αH.carrier = αK.carrier) :
  ∀ (x : αH), (coe ((sub_mul_action_of_eq_bihom M X hHK hHK').to_fun x) : X) = x := λ x, rfl

lemma sub_mul_action_of_eq_bihom.bijective {H K : submonoid M} (hHK : H = K)
  {αH : sub_mul_action H X} {αK : sub_mul_action K X} (hHK' : αH.carrier = αK.carrier) :
  function.bijective (sub_mul_action_of_eq_bihom M X hHK hHK').to_fun :=
begin
  apply and.intro (sub_mul_action_of_leq_bihom.injective M X (le_of_eq hHK) (le_of_eq hHK')),
  { intro y, use ↑y,
    { change ↑y ∈ αH.carrier, rw hHK', exact y.prop },
    simpa only [← set_like.coe_eq_coe] }
end

def sub_mul_action_of_eq_bihom.bijective' {H K : submonoid M} (hHK : H = K)
  {αH : sub_mul_action H X} {αK : sub_mul_action K X} (hHK' : αH.carrier = αK.carrier) :
  function.bijective (sub_mul_action_of_eq_bihom M X hHK hHK').to_monoid_hom :=
begin
  apply and.intro (sub_mul_action_of_leq_bihom.injective' M X (le_of_eq hHK) (le_of_eq hHK')),
  { intro y, use ↑y,
    { change ↑y ∈ H.carrier, rw hHK, exact y.prop },
    simpa only [← set_like.coe_eq_coe] }
end

variables {M X N Y}
lemma is_pretransitive_of_bihom
  {j : mul_action_bihom M X N Y} (hj : function.surjective j.to_fun)
  (h : mul_action.is_pretransitive M X) : mul_action.is_pretransitive N Y :=
begin
  apply mul_action.is_pretransitive.mk,
  intros x y, let h_eq := h.exists_smul_eq,
  obtain ⟨x', rfl⟩ := hj x,
  obtain ⟨y', rfl⟩ := hj y,
  obtain ⟨g, hg⟩ := h_eq x' y',
  use j.to_monoid_hom g,
  rw [j.map_smul', hg]
end

end monoid

section group

variables (M : Type*) [group M] (X : Type*) [mul_action M X]
variables (N : Type*) [group N] (Y : Type*) [mul_action N Y]


def canonical_bihom : mul_action_bihom M X (equiv.perm X) X := {
  to_fun := λ x, x,
  to_monoid_hom := mul_action.to_perm_hom M X,
  map_smul' := λ m x, (by simp) }

lemma canonical_bihom_bijective : function.bijective (canonical_bihom M X).to_fun :=
function.bijective_id

def subcanonical_bihom : mul_action_bihom M X (monoid_hom.range (mul_action.to_perm_hom M X)) X := {
  to_fun := λ x, x,
  to_monoid_hom := {
    to_fun := λ m, ⟨mul_action.to_perm m,
    (by simp only [monoid_hom.mem_range, mul_action.to_perm_hom_apply, exists_apply_eq_apply])⟩,
    map_one' := begin
      ext, simp only [subgroup.coe_mk, mul_action.to_perm_apply,
        one_smul, subgroup.coe_one, equiv.perm.coe_one, id.def],
    end,
    map_mul' := λ m n, begin
      ext, simp, rw mul_smul, end },
  map_smul' := λ m x,  begin simp, refl end }

lemma subcanonical_bihom_bijective : function.bijective (subcanonical_bihom M X).to_fun :=
function.bijective_id

lemma subcanonical_bihom_monoid_hom_surjective :
  function.surjective (subcanonical_bihom M X).to_monoid_hom.to_fun :=
begin
  rintro ⟨f, m, rfl⟩, use m, refl
end

lemma mul_of_preimage_eq (f : mul_action_bihom M X N Y) (B : set Y) (m : M) :
  m • f.to_fun ⁻¹' B = f.to_fun ⁻¹' ((f.to_monoid_hom m) • B) :=
begin
  ext,
  simp only [set.mem_preimage],
  split,
  { intro h,
    obtain ⟨y, hy, rfl⟩ := h,
    simp only [set.mem_preimage] at hy,
    rw ← f.map_smul',
    exact set.smul_mem_smul_set hy },
  { rintro ⟨b,hb, hbx⟩,
    use m⁻¹ • x,
    split,
    { simp only [set.mem_preimage],
      rw [← f.map_smul', ← hbx],
      simp only [map_inv, inv_smul_smul],
      exact hb },
    simp only [smul_inv_smul], }
end

/--/
lemma is_pretransitive_of_bihom (f : mul_action_bihom M α N β) (hf : function.surjective f.to_fun) :
  is_pretransitive M α → is_pretransitive N β :=
begin
  intro h, let h_eq := h.exists_smul_eq,
  apply is_pretransitive.mk,
  intros x' y',
  obtain ⟨x, rfl⟩ := hf x',
  obtain ⟨y, rfl⟩ := hf y',
  obtain ⟨m, rfl⟩ := h_eq x y,
  use (f.to_monoid_hom m),
  refine f.map_smul' _ _,
end
-/

variables {M X N Y}

def bihom_of_map (j : mul_action_bihom M X N Y) (M' : subgroup M) :
  mul_action_bihom M' X (subgroup.map j.to_monoid_hom M') Y := {
to_fun := j.to_fun,
to_monoid_hom := (j.to_monoid_hom.restrict M').cod_restrict (subgroup.map j.to_monoid_hom M')
  (λ ⟨x, hx⟩,
  begin
    rw monoid_hom.restrict_apply,
    exact ⟨x, hx, rfl⟩
  end),
  map_smul' := λ ⟨m, hm⟩ x,
  begin
    simp only [monoid_hom.restrict_apply, subgroup.coe_mk, monoid_hom.cod_restrict_apply],
    change (j.to_monoid_hom m) • (j.to_fun x) = _,
    simp only [j.map_smul'],
    refl
  end }

lemma bihom_of_map_to_fun_eq (j : mul_action_bihom M X N Y) (M' : subgroup M) :
  (bihom_of_map j M').to_fun = j.to_fun := rfl

def bihom_of_comap (j : mul_action_bihom M X N Y) (N' : subgroup N) :
  mul_action_bihom (subgroup.comap j.to_monoid_hom N') X N' Y := {
to_fun := j.to_fun,
to_monoid_hom := (j.to_monoid_hom.restrict (subgroup.comap j.to_monoid_hom N')).cod_restrict N'
  (λ ⟨x, hx⟩,
  begin
    rw subgroup.mem_comap at hx,
    rw monoid_hom.restrict_apply,
    exact hx,
  end),
  map_smul' := λ ⟨m, hm⟩ x,
  begin
    simp only [monoid_hom.restrict_apply, subgroup.coe_mk, monoid_hom.cod_restrict_apply],
    change (j.to_monoid_hom m) • (j.to_fun x) = _,
    simp only [j.map_smul'],
    refl
  end }

lemma bihom_of_comap_to_fun_eq (j : mul_action_bihom M X N Y) (N' : subgroup N) :
  (bihom_of_comap j N').to_fun = j.to_fun := rfl

end group
