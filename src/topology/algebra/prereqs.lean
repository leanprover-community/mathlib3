import algebra.star.subalgebra
import ring_theory.adjoin.basic
import algebra.star.pointwise
import algebra.star.module

.

-- the result contained here need to move into `algebra/star/subalgebra`.

universes u v w u₁

open_locale pointwise

variables {F : Type u₁} {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [star_ring R]
variables [semiring A] [algebra R A] [star_ring A] [star_module R A]
variables [semiring B] [algebra R B] [star_ring B] [star_module R B]

namespace subalgebra

/-- The pointwise `star` of a subalgebra of a star algebra is a subalgebra. -/
instance : has_involutive_star (subalgebra R A) :=
{ star := λ S,
  { carrier := star S.carrier,
    mul_mem' := λ x y hx hy,
    begin
      simp only [set.mem_star, subalgebra.mem_carrier] at *,
      exact (star_mul x y).symm ▸ mul_mem hy hx,
    end,
    one_mem' := set.mem_star.mp ((star_one A).symm ▸ one_mem S : star (1 : A) ∈ S),
    add_mem' := λ x y hx hy,
    begin
      simp only [set.mem_star, subalgebra.mem_carrier] at *,
      exact (star_add x y).symm ▸ add_mem hx hy,
    end,
    zero_mem' := set.mem_star.mp ((star_zero A).symm ▸ zero_mem S : star (0 : A) ∈ S),
    algebra_map_mem' := λ r, by simpa only [set.mem_star, subalgebra.mem_carrier,
      ←algebra_map_star_comm] using S.algebra_map_mem (star r) },
  star_involutive := λ S, subalgebra.ext $ λ x, ⟨λ hx, (star_star x ▸ hx), λ hx,
    ((star_star x).symm ▸ hx : star (star x) ∈ S)⟩ }

@[simp] lemma mem_star_iff (S : subalgebra R A) (x : A) : x ∈ star S ↔ star x ∈ S := iff.rfl
@[simp] lemma star_mem_star_iff (S : subalgebra R A) (x : A) : star x ∈ star S ↔ x ∈ S :=
by simpa only [star_star] using mem_star_iff S (star x)
@[simp] lemma coe_star (S : subalgebra R A) : ((star S : subalgebra R A) : set A) = star S := rfl

lemma star_mono : monotone (star : subalgebra R A → subalgebra R A) := λ _ _ h _ hx, h hx

variables (R)

lemma star_adjoin_comm (s : set A) : star (algebra.adjoin R s) = algebra.adjoin R (star s) :=
have this : ∀ t : set A, algebra.adjoin R (star t) ≤ star (algebra.adjoin R t),
  from λ t, algebra.adjoin_le (λ x hx, algebra.subset_adjoin hx),
le_antisymm (by simpa only [star_star] using subalgebra.star_mono (this (star s))) (this s)

variables {R}

/-- The `star_subalgebra` obtained from `S : subalgebra R A` by taking the smallest subalgebra
containing both `S` and `star S`. -/
@[simps] def star_closure (S : subalgebra R A) : star_subalgebra R A :=
{ star_mem' := λ a ha,
  begin
    simp only [subalgebra.mem_carrier, ←(@algebra.gi R A _ _ _).l_sup_u _ _] at *,
    rw [←mem_star_iff _ a, star_adjoin_comm],
    convert ha,
    simp [set.union_comm],
  end,
  .. S ⊔ star S }

end subalgebra

namespace star_subalgebra

lemma ext_to_subalgebra {S₁ S₂ : star_subalgebra R A} (h : S₁.to_subalgebra = S₂.to_subalgebra) :
  S₁ = S₂ :=
by {ext, convert set_like.ext_iff.mp h x}

lemma to_subalgebra_le_iff {S₁ S₂ : star_subalgebra R A} :
  S₁.to_subalgebra ≤ S₂.to_subalgebra ↔ S₁ ≤ S₂ := iff.rfl

variables (R)

/-- The minimal star subalgebra that includes `s`. -/
@[simps] def adjoin (s : set A) : star_subalgebra R A :=
{ star_mem' := λ x hx, by rwa [subalgebra.mem_carrier, ←subalgebra.mem_star_iff,
    subalgebra.star_adjoin_comm, set.union_star, star_star, set.union_comm],
  .. (algebra.adjoin R (s ∪ star s)) }

lemma adjoin_eq_star_closure_adjoin (s : set A) : adjoin R s = (algebra.adjoin R s).star_closure :=
ext_to_subalgebra $
  show algebra.adjoin R (s ∪ star s) = algebra.adjoin R s ⊔ star (algebra.adjoin R s),
  from (subalgebra.star_adjoin_comm R s).symm ▸ algebra.adjoin_union s (star s)

lemma adjoin_to_subalgebra (s : set A) :
  (adjoin R s).to_subalgebra = (algebra.adjoin R (s ∪ star s)) := rfl

lemma subset_adjoin (s : set A) : s ⊆ adjoin R s :=
  (set.subset_union_left s (star s)).trans algebra.subset_adjoin

lemma star_subset_adjoin (s : set A) : star s ⊆ adjoin R s :=
  (set.subset_union_right s (star s)).trans algebra.subset_adjoin

lemma self_mem_adjoin_singleton (x : A) : x ∈ adjoin R ({x} : set A) :=
algebra.subset_adjoin $ set.mem_union_left _ (set.mem_singleton x)

lemma star_self_mem_adjoin_singleton (x : A) : star x ∈ adjoin R ({x} : set A) :=
star_mem $ self_mem_adjoin_singleton R x

lemma adjoin_induction {s : set A} {p : A → Prop} {a : A} (h : a ∈ adjoin R s)
  (Hs : ∀ (x : A), x ∈ s → p x) (Halg : ∀ (r : R), p (algebra_map R A r))
  (Hadd : ∀ (x y : A), p x → p y → p (x + y)) (Hmul : ∀ (x y : A), p x → p y → p (x * y))
  (Hstar : ∀ (x : A), p x → p (star x)) : p a :=
algebra.adjoin_induction h (λ x hx, hx.elim (λ hx, Hs x hx) (λ hx, star_star x ▸ Hstar _ (Hs _ hx)))
  Halg Hadd Hmul

lemma adjoin_induction₂ {s : set A} {p : A → A → Prop} {a b : A} (ha : a ∈ adjoin R s)
  (hb : b ∈ adjoin R s) (Hs : ∀ (x : A), x ∈ s → ∀ (y : A), y ∈ s → p x y)
  (Halg : ∀ (r₁ r₂ : R), p (algebra_map R A r₁) (algebra_map R A r₂))
  (Halg_left : ∀ (r : R) (x : A), x ∈ s → p (algebra_map R A r) x)
  (Halg_right : ∀ (r : R) (x : A), x ∈ s → p x (algebra_map R A r))
  (Hadd_left : ∀ (x₁ x₂ y : A), p x₁ y → p x₂ y → p (x₁ + x₂) y)
  (Hadd_right : ∀ (x y₁ y₂ : A), p x y₁ → p x y₂ → p x (y₁ + y₂))
  (Hmul_left : ∀ (x₁ x₂ y : A), p x₁ y → p x₂ y → p (x₁ * x₂) y)
  (Hmul_right : ∀ (x y₁ y₂ : A), p x y₁ → p x y₂ → p x (y₁ * y₂))
  (Hstar : ∀ (x y : A), p x y → p (star x) (star y))
  (Hstar_left : ∀ (x y : A), p x y → p (star x) y)
  (Hstar_right : ∀ (x y : A), p x y → p x (star y)) : p a b :=
begin
  refine algebra.adjoin_induction₂ ha hb (λ x hx y hy, _) Halg (λ r x hx, _) (λ r x hx, _)
    Hadd_left Hadd_right Hmul_left Hmul_right,
  { cases hx; cases hy,
    exacts [Hs x hx y hy, star_star y ▸ Hstar_right _ _ (Hs _ hx _ hy),
      star_star x ▸ Hstar_left _ _ (Hs _ hx _ hy),
      star_star x ▸ star_star y ▸ Hstar _ _ (Hs _ hx _ hy)] },
  { cases hx, exacts [Halg_left _ _ hx, star_star x ▸ Hstar_right _ _ (Halg_left r _ hx)] },
  { cases hx, exacts [Halg_right _ _ hx, star_star x ▸ Hstar_left _ _ (Halg_right r _ hx)] },
end

/-- The difference with `star_subalgebra.adjoin_induction` is that this acts on the subtype. -/
lemma adjoin_induction' {s : set A} {p : adjoin R s → Prop} (a : adjoin R s)
  (Hs : ∀ x (h : x ∈ s), p ⟨x, subset_adjoin R s h⟩)
  (Halg : ∀ r, p (algebra_map R _ r)) (Hadd : ∀ x y, p x → p y → p (x + y))
  (Hmul : ∀ x y, p x → p y → p (x * y)) (Hstar : ∀ x, p x → p (star x)) : p a :=
subtype.rec_on a $ λ b hb,
begin
  refine exists.elim _ (λ (hb : b ∈ adjoin R s) (hc : p ⟨b, hb⟩), hc),
  apply adjoin_induction R hb,
  exacts [λ x hx, ⟨subset_adjoin R s hx, Hs x hx⟩,
    λ r, ⟨star_subalgebra.algebra_map_mem _ r, Halg r⟩,
    (λ x y hx hy, exists.elim hx $ λ hx' hx,
      exists.elim hy $ λ hy' hy, ⟨add_mem hx' hy', Hadd _ _ hx hy⟩),
    (λ x y hx hy, exists.elim hx $ λ hx' hx,
      exists.elim hy $ λ hy' hy, ⟨mul_mem hx' hy', Hmul _ _ hx hy⟩),
    λ x hx, exists.elim hx (λ hx' hx, ⟨star_mem hx', Hstar _ hx⟩)]
end

/-- If all elements of `s : set A` commute pairwise and also commute pairwise with elements of
`star s`, then `star_subalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
@[reducible]
def adjoin_comm_semiring_of_comm {s : set A}
  (hcomm : ∀ (a : A), a ∈ s → ∀ (b : A), b ∈ s → a * b = b * a)
  (hcomm_star : ∀ (a : A), a ∈ s → ∀ (b : A), b ∈ s → a * star b = star b * a) :
comm_semiring (adjoin R s) :=
{ mul_comm :=
  begin
    rintro ⟨x, hx⟩ ⟨y, hy⟩,
    ext,
    simp only [set_like.coe_mk, mul_mem_class.mk_mul_mk],
    rw [←mem_to_subalgebra, adjoin_to_subalgebra] at hx hy,
    letI : comm_semiring (algebra.adjoin R (s ∪ star s)) := algebra.adjoin_comm_semiring_of_comm R
    begin
      intros a ha b hb,
      cases ha; cases hb,
      exacts [hcomm _ ha _ hb, star_star b ▸ hcomm_star _ ha _ hb,
        star_star a ▸ (hcomm_star _ hb _ ha).symm,
        by simpa only [star_mul, star_star] using congr_arg star (hcomm _ hb _ ha)],
    end,
    exact congr_arg coe (mul_comm (⟨x, hx⟩ : algebra.adjoin R (s ∪ star s)) ⟨y, hy⟩),
  end,
  ..(adjoin R s).to_subalgebra.to_semiring }

/-- If all elements of `s : set A` commute pairwise and also commute pairwise with elements of
`star s`, then `star_subalgebra.adjoin R s` is commutative. See note [reducible non-instances]. -/
@[reducible]
def adjoin_comm_ring_of_comm (R : Type u) {A : Type v} [comm_ring R] [star_ring R]
  [ring A] [algebra R A] [star_ring A] [star_module R A] {s : set A}
  (hcomm : ∀ (a : A), a ∈ s → ∀ (b : A), b ∈ s → a * b = b * a)
  (hcomm_star : ∀ (a : A), a ∈ s → ∀ (b : A), b ∈ s → a * star b = star b * a) :
comm_ring (adjoin R s) :=
{ ..star_subalgebra.adjoin_comm_semiring_of_comm R hcomm hcomm_star,
  ..(adjoin R s).to_subalgebra.to_ring }

/-- The star subalgebra `star_subalgebra.adjoin R {x}` generated by a single `x : A` is commutative
in the presence of `is_star_normal x`. -/
instance adjoin_comm_semiring_of_is_star_normal (x : A) [is_star_normal x] :
  comm_semiring (adjoin R ({x} : set A)) :=
adjoin_comm_semiring_of_comm R
  (λ a ha b hb, by { rw [set.mem_singleton_iff] at ha hb, rw [ha, hb] })
  (λ a ha b hb,
    by { rw [set.mem_singleton_iff] at ha hb, simpa only [ha, hb] using (star_comm_self' x).symm })

/-- The star subalgebra `star_subalgebra.adjoin R {x}` generated by a single `x : A` is commutative
in the presence of `is_star_normal x`. -/
instance adjoin_comm_ring_of_is_star_normal (R : Type u) {A : Type v} [comm_ring R] [star_ring R]
  [ring A] [algebra R A] [star_ring A] [star_module R A]  (x : A) [is_star_normal x] :
  comm_ring (adjoin R ({x} : set A)) :=
{ mul_comm := mul_comm, ..(adjoin R ({x} : set A)).to_subalgebra.to_ring }

variables {R}

end star_subalgebra

namespace star_alg_hom
open star_subalgebra

lemma ext_adjoin {s : set A} [star_alg_hom_class F R (adjoin R s) B] {f g : F}
  (h : ∀ x : adjoin R s, (x : A) ∈ s → f x = g x) : f = g :=
begin
  refine fun_like.ext f g (λ a, adjoin_induction' R a (λ x hx, _) (λ r, _) (λ x y hx hy, _)
    (λ x y hx hy, _) (λ x hx, _)),
  { exact h ⟨x, subset_adjoin R s hx⟩ hx },
  { simp only [alg_hom_class.commutes] },
  { rw [map_add, map_add, hx, hy] },
  { rw [map_mul, map_mul, hx, hy] },
  { rw [map_star, map_star, hx] },
end

lemma ext_adjoin_singleton {a : A} [star_alg_hom_class F R (adjoin R ({a} : set A)) B] {f g : F}
  (h : f ⟨a, self_mem_adjoin_singleton R a⟩ = g ⟨a, self_mem_adjoin_singleton R a⟩) : f = g :=
ext_adjoin $ λ x hx, (show x = ⟨a, self_mem_adjoin_singleton R a⟩,
  from subtype.ext $ set.mem_singleton_iff.mp hx).symm ▸ h

end star_alg_hom

namespace star_subalgebra

/-! ### Complete lattice structure -/

protected lemma gc : galois_connection (adjoin R : set A → star_subalgebra R A) coe :=
begin
  intros s S,
  rw [←to_subalgebra_le_iff, adjoin_to_subalgebra, algebra.adjoin_le_iff, coe_to_subalgebra],
  exact ⟨λ h, (set.subset_union_left s _).trans h,
    λ h, set.union_subset h $ λ x hx, star_star x ▸ star_mem (show star x ∈ S, from h hx)⟩,
end

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : galois_insertion (adjoin R : set A → star_subalgebra R A) coe :=
{ choice := λ s hs, (adjoin R s).copy s $ le_antisymm (star_subalgebra.gc.le_u_l s) hs,
  gc := star_subalgebra.gc,
  le_l_u := λ S, (star_subalgebra.gc (S : set A) (adjoin R S)).1 $ le_rfl,
  choice_eq := λ _ _, star_subalgebra.copy_eq _ _ _ }

instance : complete_lattice (star_subalgebra R A) :=
galois_insertion.lift_complete_lattice star_subalgebra.gi

@[simp]
lemma coe_top : (↑(⊤ : star_subalgebra R A) : set A) = set.univ := rfl

@[simp] lemma mem_top {x : A} : x ∈ (⊤ : star_subalgebra R A) :=
set.mem_univ x

@[simp] lemma top_to_subalgebra : (⊤ : star_subalgebra R A).to_subalgebra = ⊤ := rfl

@[simp] lemma to_subalgebra_eq_top {S : star_subalgebra R A} : S.to_subalgebra = ⊤ ↔ S = ⊤ :=
star_subalgebra.to_subalgebra_injective.eq_iff' top_to_subalgebra

lemma mem_sup_left {S T : star_subalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

lemma mem_sup_right {S T : star_subalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

lemma mul_mem_sup {S T : star_subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
  x * y ∈ S ⊔ T :=
mul_mem (mem_sup_left hx) (mem_sup_right hy)

lemma map_sup (f : A →⋆ₐ[R] B) (S T : star_subalgebra R A) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
(star_subalgebra.gc_map_comap f).l_sup

@[simp, norm_cast]
lemma coe_inf (S T : star_subalgebra R A) : (↑(S ⊓ T) : set A) = S ∩ T := rfl

@[simp]
lemma mem_inf {S T : star_subalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := iff.rfl

@[simp] lemma inf_to_subalgebra (S T : star_subalgebra R A) :
  (S ⊓ T).to_subalgebra = S.to_subalgebra ⊓ T.to_subalgebra := rfl

@[simp, norm_cast]
lemma coe_Inf (S : set (star_subalgebra R A)) : (↑(Inf S) : set A) = ⋂ s ∈ S, ↑s := Inf_image

lemma mem_Inf {S : set (star_subalgebra R A)} {x : A} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
by simp only [← set_like.mem_coe, coe_Inf, set.mem_Inter₂]

@[simp] lemma Inf_to_subalgebra (S : set (star_subalgebra R A)) :
  (Inf S).to_subalgebra = Inf (star_subalgebra.to_subalgebra '' S) :=
set_like.coe_injective $ by simp

@[simp, norm_cast]
lemma coe_infi {ι : Sort*} {S : ι → star_subalgebra R A} : (↑(⨅ i, S i) : set A) = ⋂ i, S i :=
by simp [infi]

lemma mem_infi {ι : Sort*} {S : ι → star_subalgebra R A} {x : A} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp] lemma infi_to_subalgebra {ι : Sort*} (S : ι → star_subalgebra R A) :
  (⨅ i, S i).to_subalgebra = ⨅ i, (S i).to_subalgebra :=
set_like.coe_injective $ by simp

lemma bot_to_subalgebra : (⊥ : star_subalgebra R A).to_subalgebra = ⊥ :=
by { change algebra.adjoin R (∅ ∪ star ∅) = algebra.adjoin R ∅, simp }

theorem mem_bot {x : A} : x ∈ (⊥ : star_subalgebra R A) ↔ x ∈ set.range (algebra_map R A) :=
by rw [←mem_to_subalgebra, bot_to_subalgebra, algebra.mem_bot]

@[simp] theorem coe_bot : ((⊥ : star_subalgebra R A) : set A) = set.range (algebra_map R A) :=
by simp [set.ext_iff, mem_bot]

theorem eq_top_iff {S : star_subalgebra R A} :
  S = ⊤ ↔ ∀ x : A, x ∈ S :=
⟨λ h x, by rw h; exact mem_top, λ h, by ext x; exact ⟨λ _, mem_top, λ _, h x⟩⟩

-- there are several missing lemmas here because we don't have `star_alg_hom.range`.
-- or `star_alg_hom.cod_restrict`

end star_subalgebra
