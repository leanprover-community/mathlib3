import data.equiv.congruence algebra.associated data.equiv.algebra

/- Localizing monoids at submonoids.
   Everything is in the localization namespace to avoid having to duplicate things. -/

variables {X : Type*} [comm_monoid X] (Y : submonoid X) {Z : Type*} [comm_monoid Z]

namespace submonoid

instance : comm_monoid Y :=
by refine {mul_comm := _, ..submonoid.to_monoid};
  { intros, rw subtype.ext, apply mul_comm }

def r : con (X × Y) :=
{ r := λ a b, ∃ c : Y, (c:X) * (a.1 * b.2) = c * (b.1 * a.2),
  r_iseqv :=
    ⟨λ a, ⟨1, rfl⟩, λ a b ⟨c, hc⟩, ⟨c, hc.symm⟩,
     λ a b c ⟨m, hm⟩ ⟨n, hn⟩, ⟨n*m*b.2,
       by rw [mul_comm, mul_assoc] at hm hn; simp only [submonoid.coe_mul] at *;
          rw [mul_assoc ↑n, mul_comm ↑m, ←mul_assoc _ a.1, mul_comm _ a.1, ←mul_assoc a.1,
              mul_comm a.1, mul_assoc ↑n, hm, ←mul_assoc ↑m, mul_comm ↑m, mul_comm _ ↑c.2,
              ←mul_assoc, ←mul_assoc, ←mul_assoc, mul_comm _ b.1, hn, mul_assoc ↑n, mul_assoc c.1,
              mul_comm c.1, mul_assoc, mul_assoc, ←mul_assoc]⟩⟩,
  r_mul := λ a b c d ⟨m, hm⟩ ⟨n, hn⟩,
    by { use (m*n),
         clear_aux_decl,
         dsimp only [submonoid.coe_mul, prod.fst, prod.snd] at *,
         rw [←mul_assoc _ ↑b.2, mul_assoc a.1, mul_comm c.1,mul_assoc a.1, mul_comm ↑m, ←mul_assoc,
             ←mul_assoc, mul_assoc ↑n, mul_assoc ↑n, ←mul_assoc (↑m*a.1), mul_assoc ↑m, hm,
             mul_comm _ c.1, mul_comm _ ↑d.2,←mul_assoc, ←mul_assoc, ←mul_assoc, mul_comm ↑d.2,
             mul_assoc ↑n, mul_comm ↑d.2, hn, mul_assoc,mul_assoc,mul_comm (d.1*↑c.2), mul_assoc ↑m,
             mul_assoc, ←mul_assoc ↑a.2, mul_comm _ d.1],
         simp only [mul_assoc] }}

end submonoid

variables (X)

def localization := Y.r.quotient

variables {X Y}
namespace localization
instance : monoid (localization X Y) := con.monoid Y.r

def mk : X → Y → localization X Y := λ x y, Y.r.mk' (x, y)

@[elab_as_eliminator]
theorem ind {p : localization X Y → Prop} (H : ∀ (y : X × Y), p (mk y.1 y.2))
  (x : localization X Y) : p x :=
by rcases x; convert H x; exact prod.mk.eta.symm

@[elab_as_eliminator]
theorem induction_on {p : localization X Y → Prop} (x : localization X Y)
  (H : ∀ (y : X × Y), p (mk y.1 y.2)) : p x := ind H x

section
variables {W : submonoid Z} {A : Type*} [comm_monoid A] {B : submonoid A}

@[elab_as_eliminator]
theorem induction_on₂ {p : localization X Y → localization Z W → Prop}
  (x : localization X Y) (z : localization Z W)
  (H : ∀ (a : X × Y) (b : Z × W), p (mk a.1 a.2) (mk b.1 b.2)) : p x z :=
induction_on x $ λ a, induction_on z $ λ b, H a b

@[elab_as_eliminator]
theorem induction_on₃ {p : localization X Y → localization Z W → localization A B → Prop}
  (x : localization X Y) (z : localization Z W) (a : localization A B)
  (H : ∀ (a : X × Y) (b : Z × W) (c : A × B), p (mk a.1 a.2) (mk b.1 b.2) (mk c.1 c.2)) : p x z a :=
induction_on₂ x z $ λ p q, induction_on a $ λ r, H p q r

end
protected lemma mul_comm : ∀ x y : localization X Y, x * y = y * x :=
λ x y, con.induction_on₂ x y (λ a b, by rw [con.coe_mul, con.coe_mul, mul_comm])

instance : comm_monoid (localization X Y) :=
by refine { mul_comm := localization.mul_comm, ..localization.monoid}

protected lemma eq {a₁ b₁ : X} {a₂ b₂ : Y} :
  mk a₁ a₂ = mk b₁ b₂ ↔ ∃ c:Y, (c:X) * (a₁ * b₂) = (c:X) * (b₁ * a₂) :=
⟨λ h, exists.elim (con.eq.1 h) $ λ w hw, exists.intro w hw, λ ⟨w, hw⟩, con.eq.2 ⟨w, hw⟩⟩

variables (Y)

@[elab_as_eliminator, reducible]
def lift₁ {β : Type*} (f : X × Y → β) (H : ∀ (a b : X × Y), Y.r a b → f a = f b) :
  localization X Y → β := λ q, con.lift_on' q f H

@[elab_as_eliminator, reducible]
def lift₂ (W : submonoid Z) {β : Type*} (f : X × Y → Z × W → β)
  (H : ∀ (a : X × Y) (b : Z × W) (c : X × Y) (d : Z × W), Y.r a c → W.r b d → f a b = f c d) :
  localization X Y → localization Z W → β :=
λ q r, con.lift_on₂' q r (λ x y, f x y) (λ x y w z, H x y w z)

variables {Y}

lemma r_of_eq {a₁ b₁ : X} {a₂ b₂ : Y} (h : (a₂ : X) * b₁ = b₂ * a₁) :
  mk a₁ a₂ = mk b₁ b₂ :=
localization.eq.2 $ ⟨1, by rw [mul_comm b₁, h, mul_comm a₁]⟩

@[simp] lemma mk_self' (x : Y) : mk (x : X) x = 1 :=
con.eq.2 ⟨1, by {dsimp, rw [mul_comm ↑x, ←Y.coe_one], refl}⟩

@[simp] lemma mk_self {x : X} (hx : x ∈ Y) : mk x ⟨x, hx⟩ = 1 :=
mk_self' ⟨x, hx⟩

@[simp] lemma mk_mul_mk (x y : X) (s t : Y) :
  mk x s * mk y t = mk (x * y) (s * t) := rfl

@[simp] lemma lift_mk {β : Type*} (f : (X × Y) → β)
  (H : ∀ a b, Y.r a b → f a = f b) {x : X} {y : Y} :
lift₁ Y f H (mk x y) = f (x, y):= rfl

def monoid_hom.of (Y : submonoid X) : X →* localization X Y :=
Y.r.mk'.comp ⟨λ x, (x,1), refl 1, λ x y, by simp only [prod.mk_mul_mk, one_mul]⟩

def to_units (Y : submonoid X) : Y →* units (localization X Y) :=
⟨λ y, ⟨mk y 1, mk 1 y, by simp, by simp⟩, rfl,
 λ x y, by ext; convert (monoid_hom.of Y).map_mul x y⟩

variables {Y}

@[simp] lemma to_units_mk (y : Y) : (to_units Y y : localization X Y) = mk y 1 := rfl

@[simp] lemma mk_is_unit (y : Y) : is_unit (mk (y : X) (1:Y)) :=
is_unit_unit $ to_units Y y

@[simp] lemma mk_is_unit' (x : X) (hx : x ∈ Y) : is_unit (mk x (1 : Y)) :=
is_unit_unit $ to_units Y ⟨x, hx⟩

lemma to_units_inv {y : Y} : mk 1 y = ((to_units Y y)⁻¹ : _) := rfl

namespace monoid_hom

lemma of_eq_mk (x : X) : of Y x = mk x 1 := rfl

@[simp] lemma of_mul_mk (x y : X) (v : Y) :
  of Y x * mk y v = mk (x * y) v :=
by rw [of_eq_mk, mk_mul_mk, one_mul]

lemma mk_eq_mul_mk_one (x : X) (y : Y) :
  mk x y = of Y x * mk 1 y :=
by rw [of_mul_mk, mul_one]

@[simp] lemma mk_mul_cancel_left (x : X) (y : Y) :
  mk ((y : X) * x) y = of Y x :=
by rw [mk_eq_mul_mk_one, mul_comm ↑y, (of Y).map_mul, mul_assoc,
       ←mk_eq_mul_mk_one, mk_self', mul_one]

@[simp] lemma mk_mul_cancel_right (x : X) (y : Y) :
  mk (x * y) y = of Y x :=
by rw [mul_comm, mk_mul_cancel_left]

@[simp] lemma of_is_unit (y : Y) : is_unit (of Y y) :=
is_unit_unit $ to_units Y y

@[simp] lemma of_is_unit' (x : X) (hx : x ∈ Y) : is_unit (of Y x) :=
is_unit_unit $ to_units Y ⟨x, hx⟩

lemma to_units_map (g : localization X Y →* Z) (y : Y) :
g (to_units Y y) = g.units_map (to_units Y y) :=
by simp only [g.coe_units_map, to_units_mk]

lemma to_units_map_inv (g : localization X Y →* Z) (y : Y) :
g ((to_units Y y)⁻¹ : _) = ((g.units_map (to_units Y y))⁻¹ : _) :=
by rw [←g.coe_units_map, g.units_map.map_inv]

lemma mk_eq (x : X) (y : Y) :
  mk x y = of Y x * ((to_units Y y)⁻¹ : _) :=
by rw ←to_units_inv; simp only [of_eq_mk, mk_mul_mk, mul_one, one_mul]

variables (f : X →* Z) (f' : Y → units Z)

@[simp] lemma map_one_restrict (H : ∀ y : Y, f y = f' y) : f' 1 = 1 :=
by ext; rw ←H 1; simp only [units.coe_one, Y.coe_one, f.map_one]

@[simp] lemma map_mul_restrict (H : ∀ y : Y, f y = f' y) {x y : Y} : (f' x) * (f' y) = f' (x*y) :=
by ext; rw [units.coe_mul, ←H x, ←H y, ←H (x*y)]; simp only [f.map_mul, Y.coe_mul]

variables {f f'}

def aux_lift (H : ∀ y : Y, f y = f' y) : X × Y →* Z :=
{ to_fun := λ x, (f x.1)*((f' x.2)⁻¹ : units Z),
  map_one' := by rw [prod.snd_one, map_one_restrict f f' H, one_inv]; simp,
  map_mul' := λ a b, by
    {suffices : _ * _ * _ = _ * _ * _, by simpa,
     rw [←map_mul_restrict f f' H, mul_inv_rev, units.coe_mul, mul_assoc,
         ←mul_assoc (f b.1), mul_comm _ ↑(f' a.2)⁻¹],
     simp only [mul_assoc]}}

variables (f f')

def lift' (H : ∀ y : Y, f y = f' y) : localization X Y →* Z :=
Y.r.lift (aux_lift H) $ λ a b ⟨v, hv⟩, show _ * _ = _ * _, by
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

@[simp] lemma lift_mk (H : ∀ y : Y, is_unit (f y)) (x : X) (y : Y) :
  lift f H (mk x y) = f x * ((classical.some (H y))⁻¹ : _) := rfl

@[simp] lemma lift'_of (H : ∀ y : Y, f y = f' y) (x : X) :
  lift' f f' H (of Y x) = f x :=
by rw [of_eq_mk, lift'_mk H x 1]; simp [map_one_restrict f f' H]

@[simp] lemma lift_of (H : ∀ y : Y, is_unit (f y)) (x : X) :
  lift f H (of Y x) = f x := lift'_of _ _

lemma lift'_comp_of (H : ∀ y : Y, f y = f' y)  :
  (lift' f f' H).comp (of Y) = f := monoid_hom.ext _ _ $ funext $ λ a, lift'_of H a

@[simp] lemma lift_comp_of (h : ∀ y : Y, is_unit (f y)) :
  (lift f h).comp (of Y) = f := lift'_comp_of _

@[simp] lemma lift'_apply_of (g : localization X Y →* Z) (H : ∀ y : Y, g.comp (of Y) y = f' y) :
  lift' (g.comp (of Y)) f' H = g :=
begin
  ext x,
  apply induction_on x,
  intros,
  rw [lift'_mk, ←units.mul_right_inj (f' y.2), mul_assoc,
      units.inv_mul, ←H y.2, mul_one, mk_eq_mul_mk_one],
  simp [of_eq_mk, (g.map_mul _ _).symm, mk_mul_mk],
end

@[simp] lemma lift_apply_of (g : localization X Y →* Z) :
  lift (g.comp (of Y)) (λ y, is_unit_unit (g.units_map (to_units Y y))) = g :=
by rw [lift, lift'_apply_of]

protected lemma funext (f g : localization X Y →* Z)
  (h : ∀ a : X, f.comp (of Y) a = g.comp (of Y) a) : f = g :=
begin
  rw [← lift_apply_of f, ← lift_apply_of g],
  congr' 1,
  ext,
  convert h x,
end

variables {W : submonoid Z}

variables (f)

def map (hf : ∀ y : Y, f y ∈ W) : localization X Y →* localization Z W :=
lift' ((of W).comp f) ((to_units W).comp ((f.comp Y.subtype).subtype_mk W hf)) $ λ y, rfl

variables {f}

@[simp] lemma map_of (hf : ∀ y : Y, f y ∈ W) (x : X) :
  map f hf (of Y x) = of W (f x) := lift'_of _ _

@[simp] lemma map_comp_of (hf : ∀ y : Y, f y ∈ W) :
  (map f hf).comp (of Y) = (of W).comp f := lift'_comp_of _

@[simp] lemma map_mk (hf : ∀ y : Y, f y ∈ W) (x : X) (y : Y) :
  map f hf (mk x y) = of W (f x) * ((to_units W ⟨(f y), hf y⟩)⁻¹ : _) := lift'_mk _ _ _

@[simp] lemma map_id : map (monoid_hom.id X) (λ y, y.2) = monoid_hom.id (localization X Y) :=
monoid_hom.funext _ _ $ map_of _

lemma map_comp_map {A : Type*} [comm_monoid A] {V : submonoid A} (g : Z →* A)
  (hf : ∀ y : Y, f y ∈ W) (hg : ∀ w : W, g w ∈ V) :
  (map g hg).comp (map f hf) = map (g.comp f) (λ y, hg ⟨f y, (hf y)⟩) :=
monoid_hom.funext _ _ $ λ x, by simp only [monoid_hom.comp_apply, map_of]

lemma map_map {A : Type*} [comm_monoid A] {V : submonoid A} (g : Z →* A)
  (hf : ∀ y : Y, f y ∈ W) (hg : ∀ w : W, g w ∈ V) (x : localization X Y) :
  map g hg (map f hf x) = map (g.comp f) (λ y : Y, hg (⟨f y, (hf y)⟩ : W)) x :=
by rw ←(map_comp_map g hf hg); refl

variables (f)

lemma map_ext (g : X →* Z) (hf : ∀ y : Y, f y ∈ W) (hg : ∀ y : Y, g y ∈ W) (h : f = g)
  (x : localization X Y) : map f hf x = map g hg x :=
induction_on x $ λ a, by {rw [map_mk, ←to_units_inv], congr; rw h; refl}

end monoid_hom

namespace mul_equiv

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
    (λ (y : Y), show (y : X) ∈ Y, from y.2) (by simp) x, monoid_hom.map_id], refl},
  right_inv := λ x, by {erw [monoid_hom.map_map,
    monoid_hom.map_ext (h.to_monoid_hom.comp h.symm.to_monoid_hom) (monoid_hom.id Z)
    (λ (w : W), show _ ∈ W, by {convert (submonoid.mem_coe _).1 w.2, simp, refl})
    (λ (w : W), show (w : Z) ∈ W, from w.2) (by simp) x, monoid_hom.map_id], refl }}

def equiv_of_equiv (h : X ≃* Z) (H : h.to_monoid_hom.map Y = W) :
  (localization X Y) ≃* (localization Z W) :=
{ map_mul' := monoid_hom.map_mul _,
  ..equiv_of_equiv_aux h H}

end mul_equiv
end localization
namespace submonoid

variables {X} (Y)

def r_restrict : con X :=
{ r := λ a b, Y.r (a,1) (b,1),
  r_iseqv := ⟨λ x, Y.r.refl (x,1), λ _ _ h, Y.r.symm h,
            λ _ _ _ hm hn, Y.r.trans hm hn⟩,
  r_mul := λ _ _ _ _ h1 h2, by convert Y.r.mul h1 h2; simp }

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
  show h.to_monoid_hom (monoid_hom.of Y x) = h.to_monoid_hom (monoid_hom.of Y y), by
    rwa [←hf, monoid_hom.lift_of, monoid_hom.lift_of]) in ⟨c, hc⟩,
λ ⟨w, hw⟩, let ⟨v, hv⟩ := H w in show f x = f y, by
rw [←one_mul (f x), ←one_mul (f y), ←units.inv_mul v, ←hv, mul_assoc, mul_assoc, ←f.map_mul,
    ←f.map_mul, show (↑w * x = ↑w * y), by simp only [*, mul_one, Y.coe_one] at *]⟩⟩

noncomputable def equiv_of_char_pred'_aux (f' : Y → units Z) (hf : ∀ y : Y, f y = f' y)
  (Hp : char_pred' f f' hf) : localization X Y ≃ Z :=
@equiv.of_bijective _ _ (monoid_hom.lift' f f' hf) $ and.intro
begin
  intros x y,
  apply induction_on x,
  apply induction_on y,
  intros a b h,
  rw [monoid_hom.lift'_mk, monoid_hom.lift'_mk] at h,
  have : f (a.1*b.2) = f (b.1*a.2), by
    rw [f.map_mul, f.map_mul, hf b.2, hf a.2, ←mul_one (f a.1), ←units.inv_mul (f' a.2), ←mul_assoc,
        ←h, mul_assoc, mul_comm ↑(f' a.2), mul_assoc, ←mul_assoc _ ↑(f' b.2), units.inv_mul, one_mul],
  cases (show Y.r_restrict _ _, by rw ←Hp.2; exact this) with c hc,
  rw localization.eq, exact ⟨c, by simpa using hc.symm⟩,
end
Hp.1

noncomputable def equiv_of_char_pred' (f' : Y → units Z) (hf : ∀ y:Y, f y = f' y)
  (Hp : char_pred' f f' hf) : (localization X Y) ≃* Z :=
{ map_mul' := (monoid_hom.lift' f f' hf).map_mul,
  ..equiv_of_char_pred'_aux f f' hf Hp}

noncomputable def equiv_of_char_pred (H : ∀ y : Y, is_unit (f y)) (Hp : char_pred f H) :
  (localization X Y) ≃* Z :=
equiv_of_char_pred' f (λ y, classical.some $ H y)
  (λ y, by rw [← classical.some_spec (H y)]; refl) Hp

end mul_equiv

section away

variables {X Y}

@[reducible] def away (x : X) := localization X (submonoid.powers x)
@[simp] def away.inv_self (x : X) : away x := mk 1 ⟨x, 1, pow_one x⟩

variables (f : X →* Z)

@[elab_with_expected_type]
noncomputable def away.monoid_hom.lift {x : X} (hfx : is_unit (f x)) : away x →* Z :=
monoid_hom.lift' f (λ s, classical.some hfx ^ classical.some s.2) $ λ s,
by rw [units.coe_pow, ← classical.some_spec hfx,
       ← f.map_pow, classical.some_spec s.2]; refl

variables {f}

@[simp] lemma away.monoid_hom.lift_of {x : X} (hfx : is_unit (f x)) (a : X) :
  away.monoid_hom.lift f hfx (monoid_hom.of (submonoid.powers x) a) = f a :=
monoid_hom.lift'_of _ _

@[simp] lemma away.monoid_hom.lift_coe {x : X} (hfx : is_unit (f x)) (a : X) :
  away.monoid_hom.lift f hfx (monoid_hom.of (submonoid.powers x) a) = f a :=
monoid_hom.lift'_of _ _

@[simp] lemma away.monoid_hom.lift_comp_of {x : X} (hfx : is_unit (f x)) :
  (away.monoid_hom.lift f hfx).comp (monoid_hom.of (submonoid.powers x)) = f :=
monoid_hom.lift'_comp_of _

noncomputable def monoid_hom.away_to_away_right (x y : X) : away x →* away (x * y) :=
away.monoid_hom.lift (monoid_hom.of (submonoid.powers (x*y))) $
is_unit_of_mul_one _ (((monoid_hom.of _).1 y) * away.inv_self (x * y)) $ by unfold_coes;
  rw [away.inv_self, ←mul_assoc, ←monoid_hom.map_mul',
      ←mk_self (show (x*y) ∈ submonoid.powers (x*y), from ⟨1, pow_one _⟩),
      monoid_hom.mk_eq_mul_mk_one (x*y) _]; refl

end away

end localization
