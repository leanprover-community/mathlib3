import group_theory.quotient_monoid ring_theory.ideal_operations

namespace ring_equiv

instance is_ring_hom_of_mul_equiv {R : Type*} {S : Type*} [ring R] [ring S]
  (h : R ≃* S) (H: ∀ x y : R, h (x + y) = h x + h y) : is_ring_hom h :=
@semiring_hom.is_ring_hom _ _ _ _ $ semiring_hom.mk' h.to_monoid_hom H

def of_mul_equiv {R : Type*} {S : Type*} [ring R] [ring S] (h : R ≃* S)
  (H: ∀ x y : R, h (x + y) = h x + h y) : R ≃r S :=
{hom := ring_equiv.is_ring_hom_of_mul_equiv h H, ..h.to_equiv}

def to_semiring_hom {R : Type*} {S : Type*} [ring R] [ring S] (h : R ≃r S) : R →+* S :=
⟨h.to_equiv, is_ring_hom.map_one _, λ x y, is_ring_hom.map_mul _,
is_ring_hom.map_zero _, λ x y, is_ring_hom.map_add _⟩

end ring_equiv

namespace semiring_hom

variables {α : Type*} {β : Type*} [semiring α] [semiring β]

lemma map_pow (f : α →+* β) (a : α) : ∀(n : ℕ), f (a ^ n) = (f a) ^ n
| 0            := f.map_one
| (nat.succ n) := by rw [pow_succ, semiring_hom.map_mul, map_pow n]; refl

end semiring_hom

variables (α : Type*) [comm_ring α] (S : submonoid α)

namespace localization

instance : has_add (localization α S) :=
⟨lift₂ S S
(λ x y : α × S, (mk ((y.2 : α) * x.1 + x.2 * y.1) (y.2 * x.2)))
$ λ x y w z ⟨s, hs⟩ ⟨t, ht⟩,
by { rw localization.eq, use (↑s*↑t),
     apply S.mul_mem s.2 t.2,
  calc
    ↑s * ↑t * ((↑y.2 * x.1 + ↑x.2 * y.1) * (↑z.2 * ↑w.2))
    = ↑s * (x.1 * ↑w.2) * ↑t * (↑y.2 * ↑z.2) + ↑s * (↑t * (y.1 * ↑z.2)) * (↑x.2 * ↑w.2) : by ring
... = ↑s * ↑t * ((↑z.2 * w.1 + ↑w.2 * z.1) * (↑y.2 * ↑x.2)) : by rw [hs, ht]; ring}⟩

instance : has_neg (localization α S) :=
⟨lift₁ S (λ x : α × S, (mk (-x.1) x.2)) $ λ ⟨r1, s1⟩ ⟨r2, s2⟩ ⟨v, hv⟩,
  by {rw localization.eq, use v, ring at hv ⊢, rw mul_neg_eq_neg_mul_symm, simp [hv]}⟩

instance : comm_ring (localization α S) :=
by refine
{ add            := has_add.add,
  add_assoc      := λ x y z, induction_on₃ x y z _,
  zero           := mk (0 : α) (1 : S),
  zero_add       := ind _,
  add_zero       := ind _,
  neg            := has_neg.neg,
  add_left_neg   := ind _,
  add_comm       := λ x y, induction_on₂ x y _,
  left_distrib   := λ x y z, induction_on₃ x y z _,
  right_distrib  := λ x y z, induction_on₃ x y z _,
  ..localization.comm_monoid};
{ intros,
  refine r_of_eq _,
  simp only [submonoid.coe_mul, prod.snd, prod.fst, pow_two],
  try {ring}}

variables {α S}

@[simp] lemma mk_add_mk (x y : α × S) :
  mk x.1 x.2 + mk y.1 y.2 = mk ((y.2 : α) * x.1 + x.2 * y.1) (y.2 * x.2) := rfl

@[simp] lemma neg_mk (x : α × S) : -(mk x.1 x.2) = mk (-x.1) x.2 := rfl

@[simp] lemma mk_sub_mk (x y : α × S) : mk x.1 x.2 - mk y.1 y.2 =
  mk ((y.2 : α) * x.1 - x.2 * y.1) (y.2 * x.2) :=
by rw [sub_eq_add_neg, neg_mk, mk_add_mk _ (-y.1, y.2), sub_eq_add_neg, ←mul_neg_eq_neg_mul_symm]

lemma mk_zero (y : S) : mk 0 y = 0 := localization.eq.2 ⟨1, by norm_num⟩

variables (S)

def of : α →+* localization α S :=
semiring_hom.mk' (monoid_hom.of S) $
λ x y, r_of_eq $ by {suffices : 1 * (1 * x + 1 * y) = 1 * _, by unfold_coes; simpa, ring}

variables {S} {β : Type*} [comm_ring β]

lemma of_eq_mk {a : α} : of S a = mk a 1 := rfl

@[simp] lemma of_mul_mk (x y : α) (v : S) :
  of S x * mk y v = mk (x * y) v := monoid_hom.of_mul_mk _ _ _

lemma mk_eq_mul_mk_one (x : α) (y : S) :
  mk x y = of S x * mk 1 y := monoid_hom.mk_eq_mul_mk_one _ _

@[simp] lemma mk_mul_cancel_left (x : α) (y : S) :
  mk ((y : α) * x) y = of S x := monoid_hom.mk_mul_cancel_left _ _

@[simp] lemma mk_mul_cancel_right (x : α) (y : S) :
  mk (x * y) y = of S x := monoid_hom.mk_mul_cancel_right _ _

@[simp] lemma of_is_unit (y : S) : is_unit (of S y) := monoid_hom.of_is_unit _

@[simp] lemma of_is_unit' (x : α) (hx : x ∈ S) : is_unit (of S x) :=
monoid_hom.of_is_unit' _ hx

lemma to_units_map (g : localization α S →+* β) (y : S) :
g (to_units S y) = g.to_monoid_hom.units_map (to_units S y) :=
monoid_hom.to_units_map g.to_monoid_hom _

lemma to_units_map_inv (g : localization α S →+* β) (y : S) :
g ((to_units S y)⁻¹ : _) = ((g.to_monoid_hom.units_map (to_units S y))⁻¹ : _) :=
monoid_hom.to_units_map_inv g.to_monoid_hom _

lemma mk_eq (x : α) (y : S) :
  mk x y = of S x * ((to_units S y)⁻¹ : _) := monoid_hom.mk_eq x y

variables {T : submonoid β} (f : α →+* β) (f' : S → units β)

lemma lift'_add (H : ∀ s : S, f s = f' s) (a b : localization α S) :
  (monoid_hom.lift' f.to_monoid_hom f' H) (a + b) =
  (monoid_hom.lift' f.to_monoid_hom f' H) a + (monoid_hom.lift' f.to_monoid_hom f' H) b :=
induction_on₂ a b $ λ x y, by
{ rw [monoid_hom.lift'_mk, monoid_hom.lift'_mk, mk_add_mk, monoid_hom.lift'_mk],
  change f _ * _ = f _ * _ + f _ * _,
  ring,
  rw [f.map_add, ←units.mul_left_inj (f' (y.2 * x.2)), ←mul_assoc, units.mul_inv, one_mul,
     ←monoid_hom.map_mul_restrict f.to_monoid_hom f' H, units.coe_mul, mul_comm ↑(f' y.2), mul_add,
     ←mul_assoc _ _ (f y.1), mul_assoc _ _ ↑(f' y.2)⁻¹, units.mul_inv, ←mul_assoc,
     mul_assoc ↑(f' x.2) ↑(f' y.2), mul_comm ↑(f' y.2), ←mul_assoc, units.mul_inv, ←H y.2, ←H x.2],
  simp}

@[elab_with_expected_type]
def lift' (H : ∀ s : S, f s = f' s) : (localization α S) →+* β :=
semiring_hom.mk' (monoid_hom.lift' f.to_monoid_hom f' H) $
λ a b, lift'_add _ _ _ _ _

noncomputable def lift (h : ∀ s : S, is_unit (f s)) :
  localization α S →+* β :=
lift' f (λ s, classical.some $ h s)
  (λ s, by rw [← classical.some_spec (h s)]; refl)

variables {f f'}

@[simp] lemma lift'_mk (H : ∀ (s : S), f.to_monoid_hom s = f' s) (r : α) (s : S) :
  lift' f f' H (mk r s) = f r * ↑(f' s)⁻¹ := rfl

@[simp] lemma lift'_of (H : ∀ (s : S), f.to_monoid_hom s = f' s) (a : α) :
  lift' f f' H (of S a) = f a :=
by convert monoid_hom.lift'_of H a

@[simp] lemma lift_of (h : ∀ s : S, is_unit (f s)) (a : α) :
  lift f h (of S a) = f a := lift'_of _ _

@[simp] lemma lift'_comp_of (H : ∀ (s : S), f.to_monoid_hom s = f' s) :
  (lift' f f' H).comp (of S) = f :=
semiring_hom.ext _ _ $ funext $ λ a, lift'_of H a

@[simp] lemma lift_comp_of (h : ∀ s : S, is_unit (f s)) :
  (lift f h).comp (of S) = f := lift'_comp_of _

@[simp] lemma lift'_apply_of (g : localization α S →+* β) (H : ∀ s : S, g.comp (of S) s = f' s) :
  lift' (g.comp (of S)) f' H = g :=
begin
  have h : _ := monoid_hom.lift'_apply_of g.to_monoid_hom (λ s, show _, by apply H s),
  ext,
  change _ = g.to_monoid_hom x,
  rw h.symm,
  refl,
end

@[simp] lemma lift_apply_of (g : localization α S →+* β) :
  lift (g.comp (of S)) (λ y, is_unit_unit (g.to_monoid_hom.units_map (to_units S y))) = g :=
by rw [lift, lift'_apply_of]

protected lemma funext (f g : localization α S →+* β)
  (h : ∀ a : α, f (of S a) = g (of S a)) : f = g :=
semiring_hom.ext f g $
  let h' := monoid_hom.funext f.to_monoid_hom g.to_monoid_hom h in by injections with h'

variables (f)

def map (hf : ∀ s : S, f s ∈ T) : localization α S →+* localization β T :=
semiring_hom.mk' (monoid_hom.lift' ((of T).comp f).to_monoid_hom
  ((to_units T).comp ((f.to_monoid_hom.comp S.subtype).subtype_mk T hf)) $ λ y, rfl)
$ λ a b, lift'_add _ _ _ _ _

variables {f}

lemma map_of (hf : ∀ s : S, f s ∈ T) (a : α) :
  map f hf (of S a) = of T (f a) := lift'_of _ _

@[simp] lemma map_comp_of (hf : ∀ s : S, f s ∈ T) :
  (map f hf).comp (of S) = (of T).comp f := lift'_comp_of _

@[simp] lemma map_id : map (semiring_hom.id α) (λ y, y.2) = semiring_hom.id (localization α S) :=
localization.funext _ _ $ map_of _

lemma map_comp_map {γ : Type*} [comm_ring γ] {U : submonoid γ} (g : β →+* γ)
  (hf : ∀ s : S, f s ∈ T) (hg : ∀ t : T, g t ∈ U) :
  (map g hg).comp (map f hf) = map (g.comp f) (λ y, hg ⟨f y, (hf y)⟩) :=
localization.funext _ _ $ λ x, by simp only [semiring_hom.comp_apply, map_of]

lemma map_map {γ : Type*} [comm_ring γ] {U : submonoid γ} (g : β →+* γ)
  (hf : ∀ s : S, f s ∈ T) (hg : ∀ t : T, g t ∈ U) (x : localization α S) :
  map g hg (map f hf x) = map (g.comp f) (λ s : S, hg (⟨f s, (hf s)⟩ : T)) x :=
by {rw ←(map_comp_map g hf hg), refl}

lemma map_ext (hf : ∀ s : S, f s ∈ T) (g : α →+* β) (hg : ∀ s : S, g s ∈ T) (h : f = g)
  (x : localization α S) :
  map f hf x = map g hg x := by tidy

namespace ring_equiv

variables (f)

def equiv_of_equiv (h₁ : α ≃r β) (h₂ : h₁.to_equiv '' S = T) :
  localization α S ≃r localization β T :=
let H1 : h₁.to_mul_equiv.to_monoid_hom.map S = T := by
 { ext, rw [←submonoid.mem_coe T, ←h₂], refl} in
{hom := ring_equiv.is_ring_hom_of_mul_equiv
  (mul_equiv.equiv_of_equiv h₁.to_mul_equiv H1) $
  λ (x y : localization α S), by convert lift'_add ((of T).comp h₁.to_semiring_hom) _ _ x y,
..(mul_equiv.equiv_of_equiv h₁.to_mul_equiv H1).to_equiv }

def char_pred (H : ∀ s : S, is_unit (f s)) :=
mul_equiv.char_pred f.to_monoid_hom H

lemma char_pred_of_equiv (H : ∀ s : S, is_unit (f s)) (h : (localization α S) ≃r β)
  (hf : lift f H = h.to_semiring_hom) : char_pred f H :=
by convert mul_equiv.char_pred_of_equiv f.to_monoid_hom H h.to_mul_equiv
(show monoid_hom.lift f.to_monoid_hom H = h.to_semiring_hom.to_monoid_hom, by {rw hf.symm, refl})

noncomputable def equiv_of_char_pred (H : ∀ s : S, is_unit (f s)) (Hp : char_pred f H) :
  (localization α S) ≃r β :=
ring_equiv.of_mul_equiv (mul_equiv.equiv_of_char_pred f.to_monoid_hom H Hp) $
λ x y, by convert lift'_add f _ _ _ _

end ring_equiv

section away

variables (f)

@[elab_with_expected_type]
noncomputable def away.lift {x : α} (hfx : is_unit (f x)) : away x →+* β :=
semiring_hom.mk' (away.monoid_hom.lift f.to_monoid_hom hfx) $
lift'_add f (λ s, classical.some hfx ^ classical.some s.2) $ λ s,
by rw [units.coe_pow, ← classical.some_spec hfx,
       ← f.map_pow, classical.some_spec s.2]; refl

@[simp] lemma away.lift_of {x : α} (hfx : is_unit (f x)) (a : α) :
  away.lift f hfx (of (submonoid.powers x) a) = f a := lift'_of _ _

@[simp] lemma away.lift_comp_of {x : α} (hfx : is_unit (f x)) :
  (away.lift f hfx).comp (of _) = f := lift'_comp_of _

noncomputable def away_to_away_right (x y : α) : away x →+* away (x * y) :=
away.lift (of (submonoid.powers (x*y))) $
  is_unit_of_mul_one _ (((of _).1 y) * away.inv_self (x * y)) $ by unfold_coes;
  rw [away.inv_self, ←mul_assoc, ←semiring_hom.map_mul',
      ←mk_self (show (x*y) ∈ submonoid.powers (x*y), from ⟨1, pow_one _⟩),
      monoid_hom.mk_eq_mul_mk_one (x*y) _]; refl

end away

section at_prime
variables {α} (P : ideal α) [hp : ideal.is_prime P]
include hp

/- I can't coerce ideals to sets at any point after the monoid instance for
   quotient monoids (line 204 in data/equiv/congruence.lean).
   I have no idea why. Changing the instance priority doesn't seem to help. -/
instance : has_coe_to_fun (ideal α) := ⟨_, λ I, I.1⟩

def prime.submonoid : submonoid α :=
{ carrier := (-P : set α),
  one_mem' := P.ne_top_iff_one.1 hp.1,
  mul_mem' := λ x y hnx hny hxy, or.cases_on (hp.2 hxy) hnx hny }

@[reducible] def at_prime := localization α (prime.submonoid P)

instance at_prime.local_ring : local_ring (at_prime P) :=
local_of_nonunits_ideal
  (λ hze,
    let ⟨t, ht⟩ := con.eq.1 hze in
    t.2 $ have htz : 0 = t.1, by simpa using ht,
      suffices (0:α) ∈ P, by rwa htz.symm,
      P.zero_mem)
  (begin
    rintro ⟨⟨r₁, s₁⟩⟩ ⟨⟨r₂, s₂⟩⟩ hx hy hu,
    rcases is_unit_iff_exists_inv.1 hu with ⟨⟨⟨r₃, s₃⟩⟩, hz⟩,
    rcases con.eq.1 hz with ⟨t, ht⟩,
    simp at ht,
    have : ∀ {r : α} {s : prime.submonoid P}, mk r s ∈ nonunits (at_prime P) → r ∈ P,
    { haveI := classical.dec,
      exact λ r s, not_imp_comm.1 (λ nr,
        is_unit_iff_exists_inv.2 ⟨mk (s : α) (⟨r, nr⟩ : prime.submonoid P),
          by {rw mk_mul_mk, exact (r_of_eq (by simp [mul_comm]))}⟩)},
    rw [←sub_eq_zero, ←mul_sub] at ht,
    have hr₃ := (hp.mem_or_mem_of_mul_eq_zero ht).resolve_left t.2,
    have := (ideal.neg_mem_iff _).1 ((ideal.add_mem_iff_right _ _).1 hr₃),
    { exact not_or (mt hp.mem_or_mem (not_or s₂.2 s₁.2)) s₃.2 (hp.mem_or_mem this)},
    { exact (P.mul_mem_right
        (P.add_mem (P.mul_mem_left (this hy)) (P.mul_mem_left (this hx)))) }
  end)

end at_prime

end localization

def non_zero_divisors' : set α := {x | ∀ z, z * x = 0 → z = 0}

def non_zero_divisors : submonoid α :=
{ carrier := non_zero_divisors' α,
  one_mem' := λ z hz, by rwa mul_one at hz,
  mul_mem' := λ x₁ x₂ hx₁ hx₂ z hz,
    have z * x₁ * x₂ = 0, by rwa mul_assoc,
    hx₁ z $ hx₂ (z * x₁) this }

@[reducible] def fraction_ring := localization α (non_zero_divisors α)

def fraction_ring.of : α →+* fraction_ring α := localization.of (non_zero_divisors α)

variables {α}

@[simp] lemma non_zero_divisors_one_val  : ((1 : non_zero_divisors α) : α) = 1 := rfl

namespace fraction_ring

open function localization

variables {β : Type*} [integral_domain β] [decidable_eq β]

lemma eq_zero_of_ne_zero_of_mul_eq_zero {x y : β} :
  x ≠ 0 → y * x = 0 → y = 0 :=
λ hnx hxy, or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

lemma mem_non_zero_divisors_iff_ne_zero {x : β} :
  x ∈ non_zero_divisors β ↔ x ≠ 0 :=
⟨λ hm hz, zero_ne_one (hm 1 $ by norm_num [hz]).symm,
 λ hnx z, eq_zero_of_ne_zero_of_mul_eq_zero hnx⟩

variable (β)

def inv_aux (x : β × (non_zero_divisors β)) : fraction_ring β :=
if h : x.1 = 0 then 0 else
  mk (x.2 : β) (⟨x.1, mem_non_zero_divisors_iff_ne_zero.mpr h⟩ : non_zero_divisors β)

instance : has_inv (fraction_ring β) :=
⟨lift₁ (non_zero_divisors β) (inv_aux β) $
λ ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨t, ht⟩,
begin
    have hrs : (s₁ : β) * r₂ = 0 + s₂ * r₁,
      by {rw [zero_add, ←domain.mul_left_inj (mem_non_zero_divisors_iff_ne_zero.1 t.2),
              mul_comm _ r₁, mul_comm _ r₂], convert ht.symm},
    by_cases hr₁ : r₁ = 0;
    by_cases hr₂ : r₂ = 0;
    simp [hr₁, hr₂] at hrs;
    simp only [inv_aux, hr₁, hr₂, dif_pos, dif_neg, not_false_iff, subtype.coe_mk, quotient.eq],
    { exfalso,
      exact mem_non_zero_divisors_iff_ne_zero.mp s₁.2 hrs },
    { exfalso,
      exact mem_non_zero_divisors_iff_ne_zero.mp s₂.2 hrs },
    { apply r_of_eq,
      simpa [mul_comm] using hrs.symm }
  end⟩

lemma mk_inv {r : β} {s : non_zero_divisors β} :
  (mk r s)⁻¹ =
  if h : r = 0 then 0 else
  mk (s : β) (⟨r, mem_non_zero_divisors_iff_ne_zero.mpr h⟩ : non_zero_divisors β) := rfl

lemma mk_inv' : ∀ (x : β × (non_zero_divisors β)), (mk x.1 x.2)⁻¹ =
  if h : x.1 = 0 then 0 else
  mk (x.2 : β) (⟨x.1, mem_non_zero_divisors_iff_ne_zero.mpr h⟩ : non_zero_divisors β)
| ⟨r,s,hs⟩ := rfl

instance (x y : β × (non_zero_divisors β)) : decidable ((non_zero_divisors β).r x y) :=
decidable_of_iff (x.1 * y.2 = y.1 * x.2)
⟨λ H, ⟨(1 : non_zero_divisors β), by simp [H]⟩,
λ ⟨t, ht⟩, (domain.mul_left_inj (mem_non_zero_divisors_iff_ne_zero.1 t.2)).1 ht⟩

instance : decidable_eq (fraction_ring β) :=
@con.decidable_eq _ _ (non_zero_divisors β).r (fraction_ring.decidable β)

instance : discrete_field (fraction_ring β) :=
by refine { inv := has_inv.inv,
  zero_ne_one := λ hzo,
  let ⟨t, ht⟩ := con.eq.1 hzo in
  absurd (show t.val = 0, by simpa using ht.symm) (mem_non_zero_divisors_iff_ne_zero.1 t.2),
  mul_inv_cancel := _,
  inv_mul_cancel := _,
  has_decidable_eq := fraction_ring.decidable_eq β,
  inv_zero := dif_pos rfl,
  ..localization.comm_ring β (non_zero_divisors β)};
{ intro a,
  exact induction_on a (λ x h, by {unfold has_inv.inv, rw [lift_mk, inv_aux, dif_neg
    (show x.1 ≠ 0, from λ hx, h (r_of_eq $ by simp [hx]))], exact (r_of_eq $ by simp [mul_comm])})}

@[simp] lemma mk_eq_div {r : β} {s : non_zero_divisors β} :
  mk r s = of β r / of β (s : β) :=
show mk r s = mk r 1 * dite (s.1 = 0) _ _, by
rw [dif_neg (mem_non_zero_divisors_iff_ne_zero.mp s.2)]; exact mk_eq_mul_mk_one _ _

variables {β}

@[simp] lemma mk_eq_div' (x : β × (non_zero_divisors β)) :
  mk x.1 x.2 = of β x.1 / of β ((x.2) : β) :=
by erw ← mk_eq_div; cases x; refl

lemma eq_zero_of (x : β) (h : (of β x : fraction_ring β) = 0) : x = 0 :=
let ⟨t, ht⟩ := con.eq.1 h in
or.resolve_left (show t.1 = 0 ∨ x = 0, by simpa using ht) (mem_non_zero_divisors_iff_ne_zero.1 t.2)

lemma of.injective' : injective (of β : β → fraction_ring β) :=
(semiring_hom.injective_iff _).2 (λ x h, eq_zero_of x (show of β x = 0, from h))

lemma of.injective :
  function.injective (localization.of (non_zero_divisors β) : β → fraction_ring β) :=
λ x y h, by convert of.injective' h

section map

open function
variables {A : Type*} [integral_domain A] [decidable_eq A]
variables {B : Type*} [integral_domain B] [decidable_eq B]
variables (g : A →+* B)

def map (hg : injective g) : fraction_ring A →+* fraction_ring B :=
map g $ λ s,
  by rw [mem_non_zero_divisors_iff_ne_zero, ← g.map_zero, ne.def, hg.eq_iff];
    exact mem_non_zero_divisors_iff_ne_zero.1 s.2

@[simp] lemma map_of (hg : injective g) (a : A) :
  (map g hg).1 (of A a) = (of B (g a) : fraction_ring B) :=
map_of _ _

@[simp] lemma map_comp_of (hg : injective g) : (map g hg).comp (of A) = (of B).comp g :=
map_comp_of _

instance map.is_field_hom (hg : injective g) : is_field_hom (map g hg) :=
semiring_hom.is_ring_hom

def equiv_of_equiv (h : A ≃r B) : fraction_ring A ≃r fraction_ring B :=
ring_equiv.equiv_of_equiv h
begin
  ext,
  rw [submonoid.mem_coe, equiv.image_eq_preimage, set.preimage, set.mem_set_of_eq,
     mem_non_zero_divisors_iff_ne_zero, submonoid.mem_coe,
     mem_non_zero_divisors_iff_ne_zero, ne.def],
  exact ⟨mt (λ h, h.symm ▸ is_ring_hom.map_zero _),
    mt ((is_add_group_hom.injective_iff _).1 h.to_equiv.symm.injective _)⟩
end

end map

end fraction_ring

section ideals

open localization

theorem map_comap (J : ideal (localization α S)) :
  ideal.map (of S) (ideal.comap (of S : α → localization α S) J) = J :=
le_antisymm (ideal.map_le_iff_le_comap.2 (le_refl _)) $ λ x,
localization.induction_on x $ λ x hJ, (submodule.mem_coe _).2 $
mul_one x.1 ▸ of_mul_mk x.1 1 x.2 ▸ (ideal.mul_mem_right _ $ ideal.mem_map_of_mem $
have _ := @ideal.mul_mem_left (localization α S) _ _ (of S x.2) _ hJ,
by rwa [of_mul_mk, mk_mul_cancel_left] at this)

def le_order_embedding :
  ((≤) : ideal (localization α S) → ideal (localization α S) → Prop) ≼o
  ((≤) : ideal α → ideal α → Prop) :=
{ to_fun := λ J, ideal.comap (of S) J,
  inj := function.injective_of_left_inverse (map_comap S),
  ord := λ J₁ J₂, ⟨ideal.comap_mono, λ hJ,
    map_comap S J₁ ▸ map_comap S J₂ ▸ ideal.map_mono hJ⟩ }

end ideals
