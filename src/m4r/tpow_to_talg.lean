import tpow

universe u
variables (R : Type u) [comm_semiring R] (M : Type u) [add_comm_monoid M] [semimodule R M]
open tpow

/-def talg_ring : ring (tensor_algebra R M) :=
algebra.semiring_to_ring R
def talg_acg : add_comm_group (tensor_algebra R M) :=
@ring.to_add_comm_group _ talg_ring
def talg_mod : @module R (tensor_algebra R M) _ talg_acg :=
{ smul := (•),
  one_smul := one_smul _,
  mul_smul := mul_smul,
  smul_add := smul_add,
  smul_zero := smul_zero,
  add_smul := add_smul,
  zero_smul := zero_smul _ }-/

def pow_to_alg (n : ℕ) : (tpow R M n) →ₗ[R] (tensor_algebra R M) :=
tpow.lift R n (tensor_algebra R M) $ tensor_algebra.mk R M

@[simp] lemma tensor_algebra.mk_default :
  tensor_algebra.mk R M (default (fin 0 → M)) = 1 :=
list.prod_nil

local attribute [semireducible] tensor_algebra tensor_algebra.lift free_algebra ring_quot.mk_ring_hom ring_quot.mk_alg_hom ring_quot free_algebra.lift
--#check ring_quot.mk
#check (ring_quot.mk_ring_hom (tensor_algebra.rel R M) (quot.mk (free_algebra.rel R M) $ free_algebra.pre.of_scalar 1 : free_algebra R M) : tensor_algebra R M)

#check quot.mk (tensor_algebra.rel R M) (quot.mk (free_algebra.rel R M) $ free_algebra.pre.of_scalar (1 : R))
#check algebra_map R (free_algebra R M)

--#check (quot.mk (ring_quot.rel (tensor_algebra.rel R M)) (algebra_map R (free_algebra R M) 1) : tensor_algebra R M)
lemma free_algebra_map_apply {x : R} :
  algebra_map R (free_algebra R M) x =
  quot.mk (free_algebra.rel R M) (free_algebra.pre.of_scalar x) :=
rfl

lemma tensor_algebra_map_apply {x : R} :
  algebra_map R (tensor_algebra R M) x = (quot.mk (ring_quot.rel $ tensor_algebra.rel R M) (algebra_map R (free_algebra R M) x) : tensor_algebra R M) :=
rfl

lemma fdk {A : Type*} (f : M →ₗ[R] R) {x : R} :
  tensor_algebra.lift R f (quot.mk (ring_quot.rel $ tensor_algebra.rel _ _) $ quot.mk (free_algebra.rel _ _) $ free_algebra.pre.of_scalar x) = x :=
begin
  erw ring_quot.lift_alg_hom_mk_alg_hom_apply,
  refl,
end
#check free_algebra.ι
#check ring_quot.mk_alg_hom


def jfdkjgkhgskre : R ≃ₐ[R] tensor_algebra R unit :=
{ to_fun := λ x, quot.mk (ring_quot.rel $ tensor_algebra.rel R unit) (algebra_map R (free_algebra R unit) x),
  inv_fun := tensor_algebra.lift R 0,
  left_inv := λ x, by {erw ring_quot.lift_alg_hom_mk_alg_hom_apply, refl,},
  right_inv := λ x, by {refine quot.induction_on x _, intro y,
    refine quot.induction_on y _, intro z, cases z,
    erw free_algebra.quot_mk_eq_ι,
    erw ring_quot.lift_alg_hom_mk_alg_hom_apply,
    erw free_algebra.lift_ι_apply,
    rw linear_map.zero_apply,
    simp only [ring_hom.map_zero],

    --show ring_quot.mk_alg_hom _ _ 0 = ring_quot.mk_alg_hom _ _
  --  erw tensor_algebra.ring_quot_mk_alg_hom_free_algebra_ι_eq_ι,

 },
  map_mul' := _,
  map_add' := _,
  commutes' := _ }
/-
def comap {α : Type*} {β : Type*} (f : α → β)
  (r : β → β → Prop) : α → α → Prop :=
λ x y, r (f x) (f y)
lemma eqv_gen_le_comap {α : Type*} {β : Type*} (f : α → β)
  (r : β → β → Prop) : eqv_gen.setoid (comap f r) ≤ setoid.comap f (eqv_gen.setoid r) :=
begin
  rw setoid.eqv_gen_eq,
  rw setoid.eqv_gen_eq,
  intros x y h s hs,
  apply h (s.comap f),
  intros x y hxy,
  exact hs hxy,
end

lemma idk
  (r : tensor_algebra R M → tensor_algebra R M → Prop) {x y : R} :
  (eqv_gen.setoid r).rel ((algebra_map R (tensor_algebra R M)) x) (algebra_map R (tensor_algebra R M) y)
  → (eqv_gen.setoid (comap (algebra_map R (tensor_algebra R M)) r)).rel x y :=
begin
  intro h,
  rw setoid.eqv_gen_eq at h ⊢,
  intros s hs,
  specialize h (eqv_gen.setoid r) eqv_gen.rel,


end



#exit
lemma eqv_gen.rec_one {α : Type*} {β : Type*} {f : α → β}
  (x : α) (r : β → β → Prop) {C : α → Prop}
  (Ho : ∀ y, r (f x) (f y) → C y)
  (Hr : C x) (Hs : ∀ y, eqv_gen r (f y) (f x) → C y) (Ht : ∀ y z, eqv_gen r (f x) (f y) → eqv_gen r (f y) (f z) → C z)
  (y : α)
  (H : eqv_gen r (f x) (f y)) : C y :=
begin
  refine @eqv_gen.rec_on _ (comap f r) _ x y _ _ _ _ _,
  have := eqv_gen_le_comap f r (show (eqv_gen.setoid (comap f r)).rel x y, by {}),

  /-cases H,
  exact Ho y H_a,
  exact Hr,
  exact Hs y H_a,
  exact Ht H_y y H_a H_a_1,-/
end

lemma ffs {S : Type*} [semiring S] (r : S → S → Prop) {x} :
  ring_quot.mk_ring_hom r x = quot.mk (ring_quot.rel r) x :=
rfl-/

#exit
#check eqv_gen
lemma tensor_algebra_map_inj {x : R}
  (h : algebra.linear_map R (tensor_algebra R M) x = 0) :
  x = 0 :=
begin
  rw ←(algebra.linear_map R (tensor_algebra R M)).map_zero at h,
  --change quot.mk (tensor_algebra.rel R M) x = quot.mk (tensor_algebra.rel R M) 0 at h,
 -- erw tensor_algebra_map_apply at h,
 -- conv_rhs at h {erw tensor_algebra_map_apply},
--  change quot.mk (ring_quot.rel (tensor_algebra.rel R M)) _ = (0 : tensor_algebra R M) at h,
--  erw tensor_algebra_map_apply at h,
--  erw tensor_algebra_map_apply at h,
--  unfold ring_quot.mk_ring_hom at h, simp at h,
  have := quot.exact _ h,
  refine eqv_gen.rec_one 0 _ _ _ _ _ x this,
  cases this,
  simp at h,

end


--@[simp] lemma smul_one
variables {R M}
--set_option pp.implicit true
theorem inj_of_pow_to_alg (n : ℕ) : (pow_to_alg R M n).ker = ⊥ :=
linear_map.ker_eq_bot'.2 $ λ x h,
begin
  induction n with n hn,
  unfold pow_to_alg at h,
  change linear_map.to_span_singleton R (tensor_algebra R M) _ _ = 0 at h,
  rw to_span_singleton_apply at h,
  rw tensor_algebra.mk_default at h,
  rw algebra.smul_def at h,
  erw @algebra.id.smul_eq_mul R _ (x : R) (1 : R) at h, rw mul_one at h,
end

