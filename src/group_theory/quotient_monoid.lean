import data.equiv.congruence algebra.associated data.equiv.algebra

/- Localizing monoids at submonoids.
   Everything is in the localization namespace to avoid having to duplicate things.

   In data/equiv/congruence and this file I've changed my induction_on', lift_on's and
   other quotienty lemmas around a lot and at some point they were a much smoother
   alternative to the corresponding quotient.foo lemmas, but I'm not sure they are anymore.
   I think some of them are pointless and will be removed. -/

variables {X : Type*} [comm_monoid X] (Y : submonoid X) {Z : Type*} [comm_monoid Z]

namespace submonoid

instance : comm_monoid Y :=
by refine {mul_comm := _, ..submonoid.to_monoid};
   {intros, rw subtype.ext, apply mul_comm}

def r : con (X × Y) :=
{ r := λ a b, ∃ c : Y, (c:X) * (a.1 * b.2) = c * (b.1 * a.2),
  r_iseqv := ⟨λ a, ⟨1, rfl⟩, λ a b ⟨c, hc⟩, ⟨c, hc.symm⟩,
           λ a b c ⟨m, hm⟩ ⟨n, hn⟩, ⟨n*m*b.2, by
    rw [mul_comm, mul_assoc] at hm hn;
    simp only [submonoid.coe_mul] at *;
    rw [mul_assoc ↑n,mul_comm ↑m,←mul_assoc _ a.1,mul_comm _ a.1,←mul_assoc a.1,mul_comm a.1,
        mul_assoc ↑n,hm,←mul_assoc ↑m,mul_comm ↑m,mul_comm _ ↑c.2,←mul_assoc,←mul_assoc,←mul_assoc,
        mul_comm _ b.1,hn,mul_assoc ↑n,mul_assoc c.1,mul_comm c.1,mul_assoc,mul_assoc,←mul_assoc]⟩⟩,
  r_mul := λ a b c d ⟨m, hm⟩ ⟨n, hn⟩,
    by {use (m*n),
        clear_aux_decl,
        dsimp only [submonoid.coe_mul, prod.fst, prod.snd] at *,
        rw [←mul_assoc _ ↑b.2, mul_assoc a.1, mul_comm c.1,mul_assoc a.1, mul_comm ↑m, ←mul_assoc,
            ←mul_assoc, mul_assoc ↑n, mul_assoc ↑n, ←mul_assoc (↑m*a.1), mul_assoc ↑m, hm,
            mul_comm _ c.1, mul_comm _ ↑d.2,←mul_assoc, ←mul_assoc, ←mul_assoc, mul_comm ↑d.2,
            mul_assoc ↑n, mul_comm ↑d.2, hn, mul_assoc,mul_assoc,mul_comm (d.1*↑c.2), mul_assoc ↑m,
            mul_assoc, ←mul_assoc ↑a.2, mul_comm _ d.1],
        simp only [mul_assoc]}}

end submonoid

variables (X)

@[reducible] def localization := Y.r.quotient

namespace localization

variables {X Y}

instance : has_coe (X × Y) (localization X Y) := infer_instance

@[reducible] def mk (x : X) (y : Y) : localization X Y := (x, y)

@[simp] lemma mk_apply (x : X) (y : Y) : mk x y = (x, y) := rfl

@[reducible] def of (x : X) : localization X Y := ((x, (1:Y)) : localization X Y)

instance of_coe : has_coe X (localization X Y) := ⟨λ x, ((x, (1 : Y)) : localization X Y)⟩

@[simp] lemma of_apply {x : X} : of x = ((x, (1 : Y)) : localization X Y) := rfl

lemma coe_apply (x : X) : (x : localization X Y) = ((x, (1 : Y)) : localization X Y) := rfl

@[simp] protected lemma eq {Y : submonoid X} {a b : X × Y} :
(a : localization X Y) = b ↔ ∃ c:Y, (c:X) * (a.1 * b.2) = (c:X) * (b.1 * a.2) :=
⟨λ h, exists.elim (con.eq.1 h) $ λ w hw, exists.intro w hw, λ ⟨w, hw⟩, con.eq.2 ⟨w, hw⟩⟩

variables (Y)

@[elab_as_eliminator, reducible]
def lift {β : Type*} (f : (X × Y) → β) (H : ∀ a b, Y.r a b → f a = f b) : localization X Y → β :=
λ q, con.lift_on' q f H

@[elab_as_eliminator, reducible]
def lift₂ (W : submonoid Z) {β : Type*} (f : (X × Y) → (Z × W) → β)
  (H : ∀ a b c d, Y.r a c → W.r b d → f a b = f c d) :
localization X Y → localization Z W → β := λ q r, con.lift_on₂' q r f H

variables {Y}

lemma r_of_eq {a b : X × Y} (h : (a.2 : X) * b.1 = b.2 * a.1) : (a : localization X Y) = b :=
localization.eq.2 $ ⟨1, by rw [mul_comm b.1, h, mul_comm a.1]⟩

@[simp] lemma mk_self' (x : Y) : mk (x : X) x = 1 :=
by {rw [←con.coe_one, con.eq], use 1, simp}

@[simp] lemma mk_self {x : X} (hx : x ∈ Y) : mk x ⟨x, hx⟩ = 1 :=
mk_self' ⟨x, hx⟩

@[simp] lemma of_one : (of 1 : localization X Y) = 1 := rfl

@[simp] lemma of_mul (a b : X) : of (a * b) = ((of a) * (of b) : localization X Y) :=
by simp; use 1

@[simp] lemma of_pow (x : X) : ∀ (n : ℕ), (of (x ^ n) : localization X Y) = (of x) ^ n
| 0 := pow_zero x
| (n + 1) := by rw [pow_succ, of_mul, of_pow n, ←pow_succ]

@[simp] lemma coe_one : ((1 : X) : localization X Y) = 1 := rfl

@[simp] lemma coe_mul (a b : X) :
  ((a * b : X) : localization X Y) = (a : localization X Y) * (b : localization X Y) := of_mul _ _

lemma coe_pow (x : X) : ∀ n : ℕ, (x ^ n : localization X Y) = (x : localization X Y) ^ n
| 0 := pow_zero x
| (n + 1) := pow_succ _ _

protected lemma mul_comm {Y : submonoid X} : ∀ x y : localization X Y, x * y = y * x :=
λ x y, con.induction_on₂' x y (λ a b, by
 { rw [con.coe_mul, con.coe_mul, con.eq], use 1, simp [mul_comm]})

instance : comm_monoid (localization X Y) :=
by refine { mul_comm := localization.mul_comm, ..Y.r.monoid}

def to_units (y : Y) : units (localization X Y) :=
by refine { val := (y : X), inv := ((1 : X), y), ..};
 { rw [coe_apply, con.coe_mul, prod.mk_mul_mk, ←mk_apply], simp [-mk_apply]}

def to_units_hom : Y →* units (localization X Y) :=
⟨to_units, rfl, λ x y, by ext; apply of_mul⟩

@[simp] lemma to_units_coe (y : Y) : ((to_units y) : localization X Y) = (y : X) := rfl

@[simp] lemma of_is_unit (y : Y) : is_unit (of y : localization X Y) :=
is_unit_unit $ to_units y

@[simp] lemma of_is_unit' (x : X) (hx : x ∈ Y) : is_unit (of x : localization X Y) :=
is_unit_unit $ to_units ⟨x, hx⟩

@[simp] lemma coe_is_unit (y : Y) : is_unit ((y : X) : localization X Y) :=
of_is_unit _

@[simp] lemma coe_is_unit' (x : X) (hx : x ∈ Y) : is_unit (x : localization X Y) :=
of_is_unit' x hx

lemma to_units_inv {y : Y} : mk 1 y = ((to_units y)⁻¹ : units (localization X Y)) := rfl

lemma to_units_map (g : localization X Y →* Z) (y : Y) :
g (to_units y) = g.units_map (to_units y) :=
by simp

lemma to_units_map_inv (g : localization X Y →* Z) (y : Y) :
g ((to_units y)⁻¹ : units (localization X Y)) = ((g.units_map (to_units y))⁻¹ : units Z) :=
by rw [←monoid_hom.coe_units_map, monoid_hom.map_inv]

@[simp] lemma coe_mul_mk (x y : X) (v : Y) :
  ↑x * mk y v = mk (x * y) v :=
r_of_eq $ by simp

lemma mk_eq_mul_mk_one (x : X) (y : Y) :
  mk x y = x * mk 1 y :=
by rw [coe_mul_mk, mul_one]

@[simp] lemma mk_mul_mk (x y : X) (s t : Y) :
  mk x s * mk y t = mk (x * y) (s * t) := rfl

@[simp] lemma mk_mul_cancel_left (x : X) (y : Y) :
  mk ((y : X) * x) y = x :=
by rw [mk_eq_mul_mk_one, mul_comm ↑y, coe_mul,
       mul_assoc, ← mk_eq_mul_mk_one, mk_self', mul_one]

@[simp] lemma mk_mul_cancel_right (x : X) (y : Y) :
  mk (x * y) y = x :=
by rw [mul_comm, mk_mul_cancel_left]

lemma mk_eq (x : X) (y : Y) :
  mk x y = x * ((to_units y)⁻¹ : units _) :=
by simp [to_units_inv.symm]; use 1

variables {X Y}

@[simp] lemma lift_beta {β : Type*} (f : (X × Y) → β)
  (H : ∀ a b, Y.r a b → f a = f b) {x : X × Y} :
lift Y f H x = f x := rfl

namespace monoid_hom

variables {X} (Y)

def of : X →* localization X Y := ⟨localization.of, by tidy, localization.of_mul⟩

variables {Y}

@[simp] lemma of_apply {x : X} : of Y x = (x : localization X Y) := rfl

variables (f : X →* Z) (f' : Y → units Z)

@[simp] lemma map_one_restrict (H : ∀ y : Y, f y = f' y) : f' 1 = 1 :=
by {ext, rw ←H 1, simp}

@[simp] lemma map_mul_restrict (H : ∀ y : Y, f y = f' y) {x y : Y} : (f' x) * (f' y) = f' (x*y) :=
by {ext, rw [units.coe_mul, ←H x, ←H y, ←H (x*y)], simp}

variables {f f'}

def aux_lift (H : ∀ y : Y, f y = f' y) : X × Y →* Z :=
{ to_fun := λ x, (f x.1)*((f' x.2)⁻¹ : units Z),
  map_one' := by rw [prod.snd_one, map_one_restrict f f' H]; simp,
  map_mul' := λ a b, by
    {suffices : _ * _ * _ = _ * _ * _, by simpa,
     rw [←map_mul_restrict f f' H, mul_inv_rev, units.coe_mul, mul_assoc,
         ←mul_assoc (f b.1), mul_comm _ ↑(f' a.2)⁻¹],
     simp only [mul_assoc]}}

variables (f f')

def lift' (H : ∀ y : Y, f y = f' y) : localization X Y →* Z :=
(aux_lift H).lift Y.r $ λ a b ⟨v, hv⟩, show _ * _ = _ * _, by
   rw [mul_comm (f a.1), mul_comm (f b.1), ←mul_one (f a.1), ←(f' b.2).mul_inv,
       mul_comm ↑(f' b.2)⁻¹, ←mul_assoc (f a.1), ←H b.2, ←f.map_mul, ←one_mul (f (a.1*↑b.2)),
       ←(f' v).inv_mul, mul_assoc ↑(f' v)⁻¹, ←H v, ←f.map_mul, hv, f.map_mul,
       ←mul_assoc ↑(f' v)⁻¹, H v, (f' v).inv_mul, one_mul, f.map_mul, mul_comm (f b.1),
       ←mul_assoc, ←mul_assoc, H a.2, (f' a.2).inv_mul, one_mul]

noncomputable def lift (H : ∀ y : Y, is_unit (f y)) : localization X Y →* Z :=
lift' f (λ y, classical.some $ H y)
  (λ y, by rw [← classical.some_spec (H y)]; refl)

variables {f f'}

@[simp] lemma lift'_mk (H : ∀ y : Y, f y = f' y) (x : X) (y : Y) :
  lift' f f' H (mk x y) = f x * ↑(f' y)⁻¹ := rfl

@[simp] lemma lift'_of (H : ∀ y : Y, f y = f' y) (x : X) :
  lift' f f' H (localization.of x) = f x :=
by rw [lift'_mk H x 1]; simp [map_one_restrict f f' H]

@[simp] lemma lift'_coe (H : ∀ y : Y, f y = f' y) (x : X) :
  lift' f f' H x = f x := lift'_of _ _

@[simp] lemma lift_of (H : ∀ y : Y, is_unit (f y)) (x : X) :
  lift f H (localization.of x) = f x := lift'_of _ _

@[simp] lemma lift_coe (H : ∀ y : Y, is_unit (f y)) (x : X) :
  lift f H x = f x := lift'_of _ _

lemma lift'_comp_of (H : ∀ y : Y, f y = f' y)  :
  (lift' f f' H).comp (of Y) = f := monoid_hom.ext _ _ $ funext $ λ a, lift'_of H a

@[simp] lemma lift_comp_of (h : ∀ y : Y, is_unit (f y)) :
  (lift f h).comp (of Y) = f := lift'_comp_of _

@[simp] lemma lift'_apply_coe (g : localization X Y →* Z) (H : ∀ y : Y, g.comp (of Y) y = f' y) :
  lift' (g.comp (of Y)) f' H = g :=
begin
  ext x,
  apply con.induction_on' x,
  intro y,
  rw [(@prod.mk.eta _ _ y).symm, ←mk_apply, lift'_mk, ←units.mul_right_inj (f' y.2), mul_assoc,
      units.inv_mul, ←H y.2, mul_one, mk_eq_mul_mk_one, g.map_mul, to_units_inv, mul_assoc,
      to_units_map_inv],
  change _ = _ * ( _ * g (of Y (y.2 : X))),
  rw [of_apply, ←to_units_coe y.2, to_units_map, units.inv_mul],
  show g (of Y y.1) = _, by simp,
end

@[simp] lemma lift_apply_coe (g : localization X Y →* Z) :
  lift (g.comp (of Y)) (λ y, is_unit_unit (g.units_map (to_units y))) = g :=
by rw [lift, lift'_apply_coe]

protected lemma funext (f g : localization X Y →* Z)
  (h : ∀ a : X, f a = g a) : f = g :=
begin
  rw [← lift_apply_coe f, ← lift_apply_coe g],
  congr' 1,
  ext,
  convert h x,
end

variables {W : submonoid Z}

variables (f)

def map (hf : ∀ y : Y, f y ∈ W) : localization X Y →* localization Z W :=
lift' ((of W).comp f) (to_units_hom.comp ((f.comp Y.subtype).subtype_mk W hf)) $ λ y, rfl

variables {f}

@[simp] lemma map_of (hf : ∀ y : Y, f y ∈ W) (x : X) :
  map f hf (localization.of x) = localization.of (f x) := lift'_of _ _

@[simp] lemma map_coe (hf : ∀ y : Y, f y ∈ W) (x : X) :
  map f hf x = (f x) := lift'_of _ _

@[simp] lemma map_comp_of (hf : ∀ y : Y, f y ∈ W) :
  (map f hf).comp (of Y) = (of W).comp f := lift'_comp_of _

@[simp] lemma map_id : map (monoid_hom.id X) (λ y, y.2) = monoid_hom.id (localization X Y) :=
monoid_hom.funext _ _ $ map_coe _

lemma map_comp_map {A : Type*} [comm_monoid A] {V : submonoid A} (g : Z →* A)
  (hf : ∀ y : Y, f y ∈ W) (hg : ∀ w : W, g w ∈ V) :
  (map g hg).comp (map f hf) = map (g.comp f) (λ y, hg ⟨f y, (hf y)⟩) :=
monoid_hom.funext _ _ $ λ x, by simp only [map_coe, monoid_hom.comp_apply]

lemma map_map {A : Type*} [comm_monoid A] {V : submonoid A} (g : Z →* A)
  (hf : ∀ y : Y, f y ∈ W) (hg : ∀ w : W, g w ∈ V) (x : localization X Y) :
  map g hg (map f hf x) = map (g.comp f) (λ y : Y, hg (⟨f y, (hf y)⟩ : W)) x :=
by {rw ←(map_comp_map g hf hg), refl}

variables (f)

lemma map_ext (g : X →* Z) (hf : ∀ y : Y, f y ∈ W) (hg : ∀ y : Y, g y ∈ W) (h : f = g)
  (x : localization X Y) :
map f hf x = map g hg x := by tidy

end monoid_hom

end localization

namespace mul_equiv

open localization

variables {X Y} (f : X →* Y) {W : submonoid Z}

@[reducible] def equiv_of_equiv_aux (h : X ≃* Z) (H : h.to_monoid_hom.map Y = W) :
  localization X Y ≃ localization Z W :=
let H1 : ∀ y : Y, h y ∈ W :=
by { intro y, rw [←H, ←submonoid.mem_coe], change _ ∈ (h '' Y), exact ⟨(y: X), y.2, rfl⟩} in
let H2 : ∀ w : W, h.symm w ∈ Y :=
by { intro w, rcases (show (w : Z) ∈ h.to_monoid_hom.map Y, by {rw H, apply w.2}) with ⟨y, hym, hy⟩,
   rw [hy.symm, (show h.to_monoid_hom y = h y, from rfl), mul_equiv.symm_apply_apply],
   exact (submonoid.mem_coe Y).1 hym} in
{ to_fun := @localization.monoid_hom.map _ _ Y _ _ h.to_monoid_hom W $ H1,
  inv_fun := @localization.monoid_hom.map _ _ W _ _ h.symm.to_monoid_hom Y $ H2,
  left_inv := λ x, by {erw [monoid_hom.map_map,
    monoid_hom.map_ext (h.symm.to_monoid_hom.comp h.to_monoid_hom) (monoid_hom.id X)
    (λ (y : Y), show _ ∈ Y, by {convert (submonoid.mem_coe _).1 y.2, simp, refl})
    (λ (y : Y), show (y : X) ∈ Y, from y.2) (by {simp, }) x, monoid_hom.map_id], refl},
  right_inv := λ x, by {erw [monoid_hom.map_map,
    monoid_hom.map_ext (h.to_monoid_hom.comp h.symm.to_monoid_hom) (monoid_hom.id Z)
    (λ (w : W), show _ ∈ W, by {convert (submonoid.mem_coe _).1 w.2, simp, refl})
    (λ (w : W), show (w : Z) ∈ W, from w.2) (by simp) x, monoid_hom.map_id], refl}}

def equiv_of_equiv (h : X ≃* Z) (H : h.to_monoid_hom.map Y = W) :
  (localization X Y) ≃* (localization Z W) :=
{map_mul' := monoid_hom.map_mul _, ..equiv_of_equiv_aux h H}

end mul_equiv

namespace submonoid

variables {X} (Y)

def r_restrict : con X :=
{ r := λ a b, Y.r (a,1) (b,1),
  r_iseqv := ⟨λ x, Y.r.refl (x,1), λ _ _ h, Y.r.symm h,
            λ _ _ _ hm hn, Y.r.trans hm hn⟩,
  r_mul := λ _ _ _ _ h1 h2, by convert Y.r.mul h1 h2; simp}

end submonoid

namespace localization

namespace mul_equiv

variables {X Y}

variables (f : X →* Z)

def char_pred' (f' : Y → units Z) (hf : ∀ y:Y, f y = f' y) :=
function.surjective (monoid_hom.lift' f f' hf) ∧ con.ker f = Y.r_restrict

def char_pred (H : ∀ y : Y, is_unit (f y)) :=
function.surjective (monoid_hom.lift f H) ∧ con.ker f = Y.r_restrict

lemma char_pred_of_equiv (H : ∀ y : Y, is_unit (f y)) (h : (localization X Y) ≃* Z)
  (hf : monoid_hom.lift f H = h.to_monoid_hom) : char_pred f H :=
⟨λ x, let ⟨p, hp⟩ := h.to_equiv.surjective x in ⟨p, by {rw [←hp, hf], refl}⟩,
con.ext $ λ x y, ⟨λ h', let ⟨c, hc⟩ := con.eq.1 (h.to_equiv.injective $
  show h.to_monoid_hom x = h.to_monoid_hom y, by
    rwa [←hf, monoid_hom.lift_coe, monoid_hom.lift_coe]) in ⟨c, hc⟩,
λ ⟨w, hw⟩, let ⟨v, hv⟩ := H w in by
rw [con.ker_rel, ←one_mul (f x), ←one_mul (f y), ←units.inv_mul v, ←hv,
    mul_assoc, mul_assoc, ←f.map_mul, ←f.map_mul, show (↑w * x = ↑w * y), by simp * at *]⟩⟩

noncomputable def equiv_of_char_pred'_aux (f' : Y → units Z) (hf : ∀ y : Y, f y = f' y)
  (Hp : char_pred' f f' hf) : localization X Y ≃ Z :=
@equiv.of_bijective _ _ (monoid_hom.lift' f f' hf) $ and.intro
begin
  intros x y,
  apply con.induction_on₂' x y,
  intros w z h,
  change monoid_hom.lift' f f' hf (mk w.1 w.2) = monoid_hom.lift' f f' hf (mk z.1 z.2) at h,
  rw [monoid_hom.lift'_mk, monoid_hom.lift'_mk] at h,
  have : f (w.1*z.2) = f (z.1*w.2), by
    rw [f.map_mul, f.map_mul, hf z.2, hf w.2, ←mul_one (f w.1), ←units.inv_mul (f' w.2), ←mul_assoc,
        h, mul_assoc, mul_comm ↑(f' w.2), mul_assoc, ←mul_assoc _ ↑(f' z.2), units.inv_mul, one_mul],
  rw [←con.ker_rel, Hp.2] at this,
  cases this with c hc,
  rw localization.eq, exact ⟨c, by simpa using hc⟩,
end
Hp.1

noncomputable def equiv_of_char_pred' (f' : Y → units Z) (hf : ∀ y:Y, f y = f' y)
  (Hp : char_pred' f f' hf) : (localization X Y) ≃* Z :=
{map_mul' := (monoid_hom.lift' f f' hf).map_mul, ..equiv_of_char_pred'_aux f f' hf Hp}

noncomputable def equiv_of_char_pred (H : ∀ y : Y, is_unit (f y)) (Hp : char_pred f H) :
(localization X Y) ≃* Z :=
equiv_of_char_pred' f (λ y, classical.some $ H y)
  (λ y, by rw [← classical.some_spec (H y)]; refl) Hp

end mul_equiv

section away

variables {X Y}

@[reducible] def away (x : X) := (submonoid.powers x).r.quotient

@[simp] def away.inv_self (x : X) : away x :=
mk 1 ⟨x, 1, pow_one x⟩

variables (f : X →* Z)

@[elab_with_expected_type]
noncomputable def away.monoid_hom.lift {x : X} (hfx : is_unit (f x)) : away x →* Z :=
monoid_hom.lift' f (λ s, classical.some hfx ^ classical.some s.2) $ λ s,
by rw [units.coe_pow, ← classical.some_spec hfx,
       ← f.map_pow, classical.some_spec s.2]; refl

variables {f}

@[simp] lemma away.monoid_hom.lift_of {x : X} (hfx : is_unit (f x)) (a : X) :
  away.monoid_hom.lift f hfx (of a) = f a := monoid_hom.lift'_of _ _

@[simp] lemma away.monoid_hom.lift_coe {x : X} (hfx : is_unit (f x)) (a : X) :
  away.monoid_hom.lift f hfx a = f a := monoid_hom.lift'_of _ _

@[simp] lemma away.monoid_hom.lift_comp_of {x : X} (hfx : is_unit (f x)) :
  (away.monoid_hom.lift f hfx).comp (monoid_hom.of (submonoid.powers x)) = f :=
monoid_hom.lift'_comp_of _

noncomputable def monoid_hom.away_to_away_right (x y : X) : away x →* away (x * y) :=
away.monoid_hom.lift (monoid_hom.of (submonoid.powers (x*y))) $
is_unit_of_mul_one x (y * away.inv_self (x * y)) $
by {rw [monoid_hom.of_apply, away.inv_self, coe_mul_mk, coe_mul_mk, mul_one, mk_apply,
        ←con.coe_one, localization.eq], use 1, simp}
end away

end localization
