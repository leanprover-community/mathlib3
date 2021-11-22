import tactic.wlog order.zorn category_theory.conj

open category_theory

universe u

/-- A flag is a maximal chain. -/
@[reducible] def flag (α : Type u) [has_le α] : Type u :=
{c : set α // @zorn.is_max_chain α (≤) c}

namespace flag

instance (α : Type u) [has_le α] : has_mem α (flag α) :=
⟨λ a Φ, a ∈ Φ.val⟩

variables {α : Type u}

instance [has_le α] (Φ : flag α) : has_le Φ :=
⟨λ a b, a.val ≤ b.val⟩

instance [has_le α] [has_lt α] (Φ : flag α) : has_lt Φ :=
⟨λ a b, a.val < b.val⟩

/-- Any two elements of a flag are comparable. -/
protected theorem le_total [preorder α] : ∀ (Φ : flag α) (x y : Φ), x ≤ y ∨ y ≤ x :=
begin
  rintros ⟨_, hΦ, _⟩ x y,
  by_cases heq : x = y,
    { exact or.inl (le_of_eq heq) },
    { cases x with x hx, cases y with y hy,
      rw subtype.mk_eq_mk at heq,
      exact hΦ x hx y hy heq }
end

/-- `<` is trichotomous for partially ordered flags. -/
instance [partial_order α] (Φ : flag α) : is_trichotomous Φ (<) :=
begin
  refine ⟨λ x y, _⟩,
  by_cases heq : x = y, { exact or.inr (or.inl heq) },
  simp_rw lt_iff_le_and_ne,
  cases Φ.le_total x y with hle hle,
    { exact or.inl ⟨hle, heq⟩ },
    { exact or.inr (or.inr ⟨hle, ne.symm heq⟩) },
end

@[priority 900] -- lower priority in case subtype.linear_order comes up with something computable
noncomputable instance [partial_order α] (Φ : flag α) : linear_order Φ :=
{ le_total := Φ.le_total,
  decidable_le := classical.dec_rel (≤),
  ..subtype.partial_order _ }

/-- An element is in a flag iff it is comparable to everything in it. -/
lemma mem_flag_iff_comp [preorder α] (Φ : flag α) (a : α) : a ∈ Φ ↔ ∀ b : Φ, a ≤ ↑b ∨ ↑b ≤ a :=
begin
  refine ⟨λ ha _, Φ.le_total ⟨a, ha⟩ _, λ hh, _⟩,
  by_contra,
  refine Φ.prop.right ⟨set.insert a Φ, _, set.ssubset_insert h⟩,
  exact zorn.chain_insert Φ.prop.left (λ _ hbΦ _, hh ⟨_, hbΦ⟩)
end

lemma mem_flag_iff_comp' [preorder α] (Φ : flag α) {a : α} : a ∈ Φ ↔ ∀ b : Φ, a ≤ ↑b ∨ ↑b ≤ a :=
begin
  refine ⟨λ ha _, Φ.le_total ⟨a, ha⟩ _, λ hh, _⟩,
  by_contra,
  refine Φ.prop.right ⟨set.insert a Φ, _, set.ssubset_insert h⟩,
  exact zorn.chain_insert Φ.prop.left (λ _ hbΦ _, hh ⟨_, hbΦ⟩)
end

/-- `⊥` belongs to every flag. -/
theorem bot_in_flag [preorder α] [order_bot α] (Φ : flag α) : (⊥ : α) ∈ Φ :=
Φ.mem_flag_iff_comp'.mpr $ λ _, or.inl bot_le

instance [preorder α] [order_bot α] (Φ : flag α) : order_bot Φ :=
subtype.order_bot Φ.bot_in_flag

/-- `⊤` belongs to every flag. -/
theorem top_in_flag [preorder α] [order_top α] (Φ : flag α) : (⊤ : α) ∈ Φ :=
Φ.mem_flag_iff_comp'.mpr $ λ _, or.inr le_top

instance [preorder α] [order_top α] (Φ : flag α) : order_top Φ :=
subtype.order_top Φ.top_in_flag

instance [preorder α] [bounded_order α] (Φ : flag α) : bounded_order Φ :=
{ ..Φ.order_top, ..Φ.order_bot }

end flag

/-- The category of posets of type α. -/
@[instance]
private def Poset (α : Type u) [has_le α] : category (partial_order α) :=
{ hom  := λ a b, a.le →r b.le,
  id   := λ a, rel_hom.id a.le,
  comp := λ a b c hab hbc, rel_hom.comp hbc hab }

/-- The type of automorphisms of a poset. -/
def automorphism (α : Type u) [p : partial_order α] :=
@category_theory.Aut (partial_order α) (Poset α) p

namespace automorphism

/-- The automorphism group of a poset. -/
instance (α : Type u) [p : partial_order α] : group (automorphism α) :=
@category_theory.Aut.group (partial_order α) (Poset α) p

variables {α : Type u} [partial_order α]

/-- Any automorphism is a relation isomorphism. -/
def to_rel_iso (γ : automorphism α) : ((≤) : α → α → Prop) ≃r (≤) :=
{ to_fun := γ.hom,
  inv_fun := γ.inv,
  left_inv := λ x, by change (γ.hom ≫ _) _ = _; rw γ.hom_inv_id; refl,
  right_inv := λ x, by change (γ.inv ≫ _) _ = _; rw γ.inv_hom_id; refl,
  map_rel_iff' := begin
    intros,
    change γ.hom a ≤ γ.hom b ↔ a ≤ b,
    refine ⟨λ h, _, λ h, γ.hom.map_rel h⟩,
    have : (γ.hom ≫ γ.inv) a ≤ (γ.hom ≫ γ.inv) b := γ.inv.map_rel h,
    rwa γ.hom_inv_id at this
  end }

/-- Automorphisms preserve `≤`. -/
@[simp]
lemma hom_map_le (γ : automorphism α) (a b : α) : γ.hom a ≤ γ.hom b ↔ a ≤ b :=
γ.to_rel_iso.map_rel_iff

/-- Automorphisms preserve `=`. -/
@[simp]
lemma hom_map_eq (γ : automorphism α) (a b : α) : γ.hom a = γ.hom b ↔ a = b :=
γ.to_rel_iso.eq_iff_eq

/-- Automorphisms preserve `≠`. -/
@[simp]
lemma hom_map_ne (γ : automorphism α) (a b : α) : γ.hom a ≠ γ.hom b ↔ a ≠ b :=
by simp only [ne.def, hom_map_eq]

/-- Automorphisms and their inverses give the identity. -/
@[simp]
lemma hom_inv (γ : automorphism α) (a : α) : γ.hom (γ.inv a) = a :=
γ.to_rel_iso.right_inv a

/-- Inverse automorphisms preserve `≤`. -/
@[simp]
lemma inv_map_le (γ : automorphism α) (a b : α) : γ.inv a ≤ γ.inv b ↔ a ≤ b :=
γ.to_rel_iso.symm.map_rel_iff

/-- Inverse automorphisms preserve `=`. -/
@[simp]
lemma inv_map_eq (γ : automorphism α) (a b : α) : γ.inv a = γ.inv b ↔ a = b :=
γ.to_rel_iso.symm.eq_iff_eq

/-- Inverse automorphisms preserve `≠`. -/
@[simp]
lemma inv_map_ne (γ : automorphism α) (a b : α) : γ.inv a ≠ γ.inv b ↔ a ≠ b :=
by simp only [ne.def, inv_map_eq]

/-- Automorphisms and their inverses give the identity. -/
@[simp]
lemma inv_hom (γ : automorphism α) (a : α) : γ.inv (γ.hom a) = a :=
γ.to_rel_iso.left_inv a

/-- Scalar multiplication of automorphisms by flags. -/
@[reducible]
def smul_def (γ : automorphism α) (Φ : flag α) : set α :=
γ.hom '' Φ.val

/-- Definition of scalar multiplication of automorphisms by flags. -/
@[simp]
theorem smul_def.eq (γ : automorphism α) (Φ : flag α) : γ.smul_def Φ = γ.hom '' Φ.val :=
rfl

/-- Automorphisms map flags to chains. -/
lemma smul_is_chain (γ : automorphism α) (Φ : flag α) : zorn.chain (≤) (γ.smul_def Φ) :=
begin
  rcases Φ with ⟨Φf, hΦ, hΦ'⟩,
  rintros a ⟨aw, ha, ha'⟩ b ⟨bw, hb, hb'⟩,
  induction ha', induction hb',
  simp only [hom_map_le, hom_map_ne],
  exact hΦ _ ha _ hb
end

/-- Automorphisms map flags to flags. -/
theorem smul_is_max_chain (γ : automorphism α) (Φ : flag α) :
  @zorn.is_max_chain _ (≤) (γ.smul_def Φ) :=
begin
  refine ⟨γ.smul_is_chain Φ, _⟩,
  rcases Φ with ⟨Φf, hΦ, hΦ'⟩,
  rintros ⟨w, hwl, hwr⟩,
  rcases set.exists_of_ssubset hwr with ⟨a, ha, hna⟩,
  apply hΦ',
  use set.insert (γ.inv a) Φf,
  split,
    { rintros x (hx : _ ∨ _) y (hy : _ ∨ _) hne,
      have hxyne : x ≠ γ.inv a ∨ y ≠ γ.inv a,
        { rw ←not_and_distrib,
          rintro ⟨hl, hr⟩,
          exact hne (hl.trans hr.symm) },
      by_cases hxy : x ∈ Φf ∧ y ∈ Φf, { exact hΦ _ hxy.left _ hxy.right hne },
      wlog h : x = γ.inv a ∧ y ∈ Φf using [x y, y x],
        { cases hx,
            { exact or.inl ⟨hx, hy.resolve_left (hxyne.resolve_left $ not_not_intro hx)⟩ },
          cases hy,
            { exact or.inr ⟨hy, hx⟩ },
            { exact (hxy ⟨hx, hy⟩).elim } },
      cases h with hx' hy',
      replace hx' := hx'.symm,
      induction hx',
      rw [←γ.hom_map_le y, ←γ.hom_map_le, γ.hom_inv],
      replace hne : a ≠ γ.hom y := by rw ←γ.inv_map_ne; simpa,
      apply hwl _ ha _ _ hne,
      replace hy' := set.mem_image_of_mem γ.hom hy',
      exact hwr.left hy' },
    { apply set.ssubset_insert,
      intro h,
      replace h := set.mem_image_of_mem γ.hom h,
      rw γ.hom_inv at h,
      exact hna h },
end

instance : has_scalar (automorphism α) (flag α) :=
⟨λ γ Φ, ⟨γ.smul_def Φ, γ.smul_is_max_chain Φ⟩⟩

@[reducible, simp]
theorem smul_def.eq' (γ : automorphism α) (Φ : flag α) : (γ • Φ).val = γ.hom '' Φ.val :=
rfl

/-- The group action of the automorphism group of a poset on its flags. -/
instance : mul_action (automorphism α) (flag α) :=
{ one_smul := by rintro ⟨b, _⟩; apply subtype.eq; exact set.image_id b,
  mul_smul := begin
    rintros γ γ' ⟨b, _⟩,
    apply subtype.eq,
    change (γ'.hom ≫ γ.hom) '' b = γ.hom '' (γ'.hom '' b),
    rw ←set.image_comp,
    refl
  end }

end automorphism
