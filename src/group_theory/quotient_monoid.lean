import data.equiv.congruence algebra.associated data.equiv.algebra

/- Localizing monoids and rings at submonoids.
   I've left random nonsensical docstrings in.
   Everything is in the localization namespace to avoid having to duplicate things.
   Some things work more smoothly than before, and some things don't,
   but I'm not finished messing with the majority of those things.

   I've found naming very difficult

   I've marked lemmas simp for others' usability so they don't have to stick to
   whatever conventions I had in mind writing this and can easily switch between ↑, of,
   etc. This is instead of 'lemmas I found I needed along the way'. I've removed a
   lot of old simp lemmas that helped *me* for longer proofs because they were often
   just helpful for breaking things up and could ultimately be replaced with a 'show'.
   But I have a lot of questions about what simp lemmas should be in here and I'm
   gonna get some advice tomorrow/later today.

   In data/equiv/congruence and this file I've changed my induction_on', lift_on's and
   other quotienty lemmas around a lot and at some point they were a much smoother
   alternative to the corresponding quotient.foo lemmas, but I'm not sure they are anymore.
   I think some of them are pointless and will be removed. -/

namespace ring_equiv

instance is_ring_hom_of_monoid_equiv {R : Type*} {S : Type*} [ring R] [ring S]
  (h : monoid_equiv R S) (H: ∀ x y : R, h (x + y) = h x + h y) : is_ring_hom h :=
@semiring_hom.is_ring_hom _ _ _ _ $ semiring_hom.mk' h.to_monoid_hom H

def of_monoid_equiv {R : Type*} {S : Type*} [ring R] [ring S] (h : monoid_equiv R S)
  (H: ∀ x y : R, h (x + y) = h x + h y) : R ≃r S :=
{hom := ring_equiv.is_ring_hom_of_monoid_equiv h H, ..h.to_equiv}

def to_semiring_hom {R : Type*} {S : Type*} [ring R] [ring S] (h : R ≃r S) : R →+* S :=
⟨h.to_equiv, is_ring_hom.map_one _, λ x y, is_ring_hom.map_mul _,
is_ring_hom.map_zero _, λ x y, is_ring_hom.map_add _⟩

def to_monoid_equiv {R : Type*} {S : Type*} [ring R] [ring S] (h : R ≃r S) :
  monoid_equiv R S := mul_equiv.to_monoid_equiv h.to_equiv $ h.hom.map_mul

end ring_equiv

namespace semiring_hom
variables {α : Type*} {β : Type*} [semiring α] [semiring β]

/-pows in semirings are currently broken in some way. They're the reason ring_theory.ideals
  data.polynomial etc don't compile; I think they'll compile when group_theory.subgroup
  does. -/

instance : has_pow α ℕ := ⟨monoid.pow⟩

lemma map_pow (f : α →+* β) (a : α) : ∀(n : ℕ), f (a ^ n) = (f a) ^ n
| 0            := f.map_one
| (nat.succ n) := by rw [pow_succ, semiring_hom.map_mul, map_pow n]; refl

end semiring_hom

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

/-- The natural map mapping an element r of a commutative ring and an element s of a submonoid
    to the equivalence class of (r, s) in the ring's localization at the submonoid. -/

@[reducible] def mk (x : X) (y : Y) : localization X Y := (x, y)

@[simp] lemma mk_apply (x : X) (y : Y) : mk x y = (x, y) := rfl

@[reducible] def of (x : X) : localization X Y := ((x, (1:Y)) : localization X Y)

instance of_coe : has_coe X (localization X Y) := ⟨λ x, ((x, (1 : Y)) : localization X Y)⟩

@[simp] lemma of_apply {x : X} : of x = ((x, (1 : Y)) : localization X Y) := rfl

@[simp] lemma coe_apply (x : X) : (x : localization X Y) = ((x, (1 : Y)) : localization X Y) := rfl

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

/-- The map from α × S, α a commutative ring and S a submonoid, to the localization preserves
    multiplication in the first argument. -/
@[simp] lemma coe_mul_mk (x y : X) (v : Y) :
  ↑x * mk y v = mk (x * y) v :=
r_of_eq $ by simp

/-- The equivalence class of (r, s) ∈ α × S, α a commutative ring and S a submonoid, factors as
    the product of the equivalence classes of (r, 1) and (1, s) in the localization of α at S. -/
lemma mk_eq_mul_mk_one (x : X) (y : Y) :
  mk x y = x * mk 1 y :=
by rw [coe_mul_mk, mul_one]

/-- The natural map from α × S, α a commutative ring and S a submonoid, to the localization
    preserves multiplication in both arguments. -/
@[simp] lemma mk_mul_mk (x y : X) (s t : Y) :
  mk x s * mk y t = mk (x * y) (s * t) := rfl

/-- The natural map from α × S, α a commutative ring and S a submonoid, to the localization of α at
    S, is left cancellative. -/
@[simp] lemma mk_mul_cancel_left (x : X) (y : Y) :
  mk ((y : X) * x) y = x :=
by rw [mk_eq_mul_mk_one, mul_comm ↑y, coe_mul,
       mul_assoc, ← mk_eq_mul_mk_one, mk_self', mul_one]

/-- The natural map from α × S, α a commutative ring and S a submonoid, to the localization
    is right cancellative. -/
@[simp] lemma mk_mul_cancel_right (x : X) (y : Y) :
  mk (x * y) y = x :=
by rw [mul_comm, mk_mul_cancel_left]

/-- The equivalence class of (r, s) ∈ α × S, α a commutative ring and S a submonoid, factors as
    the product of the equivalence class of (r, 1) and the inverse of the equivalence class of
    (s, 1) in the localization. -/
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

/-- Simplification lemmas for the definition of the natural ring homomorphism from the localization
    of a commutative ring α at a submonoid S to a commutative ring β, given a map g from S to β
    whose image is contained in the unit group of β and a ring homomorphism f from α to β such that
    g and f are equal on S. -/
@[simp] lemma lift'_mk (H : ∀ y : Y, f y = f' y) (x : X) (y : Y) :
  lift' f f' H (mk x y) = f x * ↑(f' y)⁻¹ := rfl

@[simp] lemma lift'_of (H : ∀ y : Y, f y = f' y) (x : X) :
  lift' f f' H (localization.of x) = f x :=
by rw [lift'_mk H x 1]; simp [map_one_restrict f f' H]

@[simp] lemma lift'_coe (H : ∀ y : Y, f y = f' y) (x : X) :
  lift' f f' H x = f x := lift'_of _ _

/-- Simplification lemmas for the natural ring homomorphism from the localization of a commutative
    ring α at a submonoid S to a commutative ring β, given a ring homomorphism f from α to β mapping
    elements of S to units in β. -/
@[simp] lemma lift_of (H : ∀ y : Y, is_unit (f y)) (x : X) :
  lift f H (localization.of x) = f x := lift'_of _ _

@[simp] lemma lift_coe (H : ∀ y : Y, is_unit (f y)) (x : X) :
  lift f H x = f x := lift'_of _ _

/-- Given a map g from a submonoid S of a commutative ring α whose image is contained in the unit
    group of another commutative ring β, and a ring homomorphism f from α to β, if g and f are
    equal on S, the natural ring homomorphism we can construct from the localization to β makes
    the obvious diagram for α, β and the localization commute. -/

lemma lift'_comp_of (H : ∀ y : Y, f y = f' y)  :
  (lift' f f' H).comp (of Y) = f := monoid_hom.ext _ _ $ funext $ λ a, lift'_of H a

--/-- Given a ring homomorphism f between commutative rings α and β mapping elements of a submonoid S
  --  to units in β, the natural ring homomorphism we can construct from the localization to β makes
  --  the obvious diagram for α, β and the localization commute. -/
@[simp] lemma lift_comp_of (h : ∀ y : Y, is_unit (f y)) :
  (lift f h).comp (of Y) = f := lift'_comp_of _

--This one was nicer originally.
/-- Given a map g from a submonoid S of a commutative ring α whose image is contained in the unit
    group of another commutative ring β, and a ring homomorphism f from the localization to β, if
    g and f are equal on S, the natural ring homomorphism from the localization to β constructed
    from g and f composed with the coercion from the ring to the localization is just f. -/
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

/-- Given a ring homomorphism f from the localization of a commutative ring α at a submonoid S to a
    commutative ring β, the natural ring homomorphism from the localization to β constructed from
    f composed with the coercion from the ring to the localization is just f.-/
@[simp] lemma lift_apply_coe (g : localization X Y →* Z) :
  lift (g.comp (of Y)) (λ y, is_unit_unit (g.units_map (to_units y))) = g :=
by rw [lift, lift'_apply_coe]

/-- Function extensionality for localisations:
 two functions are equal if they agree on elements that are coercions.-/

protected lemma funext (f g : localization X Y →* Z)
  (h : ∀ a : X, f a = g a) : f = g :=
begin
  rw [← lift_apply_coe f, ← lift_apply_coe g],
  congr' 1,
  ext,
  convert h x,
end

variables {W : submonoid Z}

/-- Given a ring homomorphism f between commutative rings α and β, if f's image on a submonoid S is
    contained in a submonoid T, we can construct a natural map between the respective
    localizations. -/
variables (f)

def map (hf : ∀ y : Y, f y ∈ W) : localization X Y →* localization Z W :=
lift' ((of W).comp f) (to_units_hom.comp ((f.comp Y.subtype).subtype_mk W hf)) $ λ y, rfl

variables {f}
/-- Given a ring homomorphism f between commutative rings α and β, if f's image on a submonoid S is
    contained in a submonoid T, the natural ring homomorphism we can construct between the
    respective localizations makes the obvious diagram for α, β and the localizations commute. -/
@[simp] lemma map_of (hf : ∀ y : Y, f y ∈ W) (x : X) :
  map f hf (localization.of x) = localization.of (f x) := lift'_of _ _

/-- Given a ring homomorphism f between commutative rings α and β, if f's image on a submonoid S is
    contained in a submonoid T, the natural ring homomorphism we can construct between the
    respective localizations makes the obvious diagram for α, β and the localizations commute. -/
@[simp] lemma map_coe (hf : ∀ y : Y, f y ∈ W) (x : X) :
  map f hf x = (f x) := lift'_of _ _

/-- Given a ring homomorphism f between commutative rings α and β, if f's image on a submonoid S is
    contained in a submonoid T, the natural ring homomorphism we can construct between the
    respective localizations makes the obvious diagram for α, β and the localizations commute. -/
@[simp] lemma map_comp_of (hf : ∀ y : Y, f y ∈ W) :
  (map f hf).comp (of Y) = (of W).comp f := lift'_comp_of _

/-- Lifting the identity map on a commutative ring α to a map gives an identity map on a
    localization. -/
@[simp] lemma map_id : map (monoid_hom.id X) (λ y, y.2) = monoid_hom.id (localization X Y) :=
monoid_hom.funext _ _ $ map_coe _

/-- Given ring homomorphisms f, g between commutative rings α, β and γ, if f's image on a submonoid
    S is contained in a submonoid T and g's image on T is contained in a submonoid U, composition of
    the natural ring homomorphisms we can construct between the respective localizations commutes
    with composition of f and g. -/
lemma map_comp_map {A : Type*} [comm_monoid A] (hf : ∀ y : Y, f y ∈ W) (V : submonoid A)
(g : Z →* A) (hg : ∀ w : W, g w ∈ V) :
  (map g hg).comp (map f hf) = map (g.comp f) (λ y, hg ⟨f y, (hf y)⟩) :=
monoid_hom.funext _ _ $ λ x, by simp only [map_coe, monoid_hom.comp_apply]

/-- Given ring homomorphisms f, g between commutative rings α, β and γ, if f's image on a submonoid
    S is contained in a submonoid T and g's image on T is contained in a submonoid U, composition of
    the natural ring homomorphisms we can construct between the respective localizations commutes
    with composition of f and g. -/
lemma map_map {A : Type*} [comm_monoid A] (hf : ∀ y : Y, f y ∈ W) (V : submonoid A)
(g : Z →* A) (hg : ∀ w : W, g w ∈ V) (x : localization X Y) :
  map g hg (map f hf x) = map (g.comp f) (λ y : Y, hg (⟨f y, (hf y)⟩ : W)) x :=
by {rw ←(map_comp_map hf V g hg), refl}

variables (f)

lemma map_ext (g : X →* Z) (hf : ∀ y : Y, f y ∈ W) (hg : ∀ y : Y, g y ∈ W) (h : f = g)
  (x : localization X Y) :
map f hf x = map g hg x := by tidy

end monoid_hom

end localization

namespace monoid_equiv

open localization

variables {X Y} (f : X →* Y) {W : submonoid Z}

/-- Given a ring isomorphism h₁ between commutative rings α and β, if h₁'s image on a submonoid S is
    a submonoid T, we can construct a natural isomorphism between the respective localizations. -/
@[reducible] def equiv_of_equiv_aux (h : monoid_equiv X Z) (H : h.to_monoid_hom.map Y = W) :
  localization X Y ≃ localization Z W :=
let H1 : ∀ y : Y, h y ∈ W :=
by { intro y, rw [←H, ←submonoid.mem_coe], change _ ∈ (h '' Y), exact ⟨(y: X), y.2, rfl⟩} in
let H2 : ∀ w : W, h.symm w ∈ Y :=
by { intro w, rcases (show (w : Z) ∈ h.to_monoid_hom.map Y, by {rw H, apply w.2}) with ⟨y, hym, hy⟩,
   rw [hy.symm, h.to_monoid_hom_apply, h.left_inv_apply], exact (submonoid.mem_coe Y).1 hym} in
{ to_fun := @localization.monoid_hom.map _ _ Y _ _ h.to_monoid_hom W $ H1,
  inv_fun := @localization.monoid_hom.map _ _ W _ _ h.symm.to_monoid_hom Y $ H2,
  left_inv := λ x, by {erw [monoid_hom.map_map,
    monoid_hom.map_ext (h.symm.to_monoid_hom.comp h.to_monoid_hom) (monoid_hom.id X)
    (λ (y : Y), show _ ∈ Y, by {convert (submonoid.mem_coe _).1 y.2, simp, refl})
    (λ (y : Y), show (y : X) ∈ Y, from y.2) (by simp) x, monoid_hom.map_id], refl},
  right_inv := λ x, by {erw [monoid_hom.map_map,
    monoid_hom.map_ext (h.to_monoid_hom.comp h.symm.to_monoid_hom) (monoid_hom.id Z)
    (λ (w : W), show _ ∈ W, by {convert (submonoid.mem_coe _).1 w.2, simp, refl})
    (λ (w : W), show (w : Z) ∈ W, from w.2) (by simp) x, monoid_hom.map_id], refl}}

def equiv_of_equiv (h : monoid_equiv X Z) (H : h.to_monoid_hom.map Y = W) :
  monoid_equiv (localization X Y) (localization Z W) :=
mul_equiv.to_monoid_equiv (equiv_of_equiv_aux h H) $
λ x y, monoid_hom.map_mul _ x y

end monoid_equiv

namespace submonoid

variables {X} (Y)

def r_restrict : con X :=
{ r := λ a b, Y.r (a,1) (b,1),
  r_iseqv := ⟨λ x, Y.r.refl (x,1), λ _ _ h, Y.r.symm h,
            λ _ _ _ hm hn, Y.r.trans hm hn⟩,
  r_mul := λ _ _ _ _ h1 h2, by convert Y.r.mul h1 h2; simp}

end submonoid

namespace localization

namespace monoid_equiv

variables {X Y}

variables (f : X →* Z)

def char_pred' (f' : Y → units Z) (hf : ∀ y:Y, f y = f' y) :=
function.surjective (monoid_hom.lift' f f' hf) ∧ con.ker f = Y.r_restrict

def char_pred (H : ∀ y : Y, is_unit (f y)) :=
function.surjective (monoid_hom.lift f H) ∧ con.ker f = Y.r_restrict

lemma char_pred_of_equiv (H : ∀ y : Y, is_unit (f y)) (h : monoid_equiv (localization X Y) Z)
  (hf : monoid_hom.lift f H = h.to_monoid_hom) : char_pred f H :=
begin
  split,
  intro x,
    cases h.to_equiv.surjective x with p hp,
    exact ⟨p, by {rw ←hp, tidy}⟩,
  ext x y,
  split,
    intro h',
    rw con.ker_rel at h',
    cases (con.eq.1 (h.to_equiv.injective
          (show h.to_monoid_hom x = h.to_monoid_hom y, by
            {rwa [←hf, monoid_hom.lift_coe, monoid_hom.lift_coe]}))) with c hc,
    exact ⟨c, hc⟩,
  rintro ⟨w, hw⟩,
  cases H w with v hv,
  rw [con.ker_rel, ←one_mul (f x), ←one_mul (f y), ←units.inv_mul v, ←hv,
      mul_assoc, mul_assoc, ←f.map_mul, ←f.map_mul, show (↑w * x = ↑w * y), by simp * at *],
end

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
  rw localization.eq, exact ⟨c, by {simp at hc, exact hc}⟩,
end
Hp.1

noncomputable def equiv_of_char_pred' (f' : Y → units Z) (hf : ∀ y:Y, f y = f' y)
  (Hp : char_pred' f f' hf) : monoid_equiv (localization X Y) Z :=
mul_equiv.to_monoid_equiv (equiv_of_char_pred'_aux f f' hf Hp) $
(monoid_hom.lift' f f' hf).map_mul

noncomputable def equiv_of_char_pred (H : ∀ y : Y, is_unit (f y)) (Hp : char_pred f H) :
monoid_equiv (localization X Y) Z :=
equiv_of_char_pred' f (λ y, classical.some $ H y)
  (λ y, by rw [← classical.some_spec (H y)]; refl) Hp

end monoid_equiv

section away

variables {X Y}
/-- The localization of a commutative ring α at the submonoid generated by some x ∈ α. -/
@[reducible] def away (x : X) := (submonoid.powers x).r.quotient

/-- The inverse of an element x of a commutative ring α in the localization of α at the submonoid
    generated by x. -/
@[simp] def away.inv_self (x : X) : away x :=
mk 1 ⟨x, 1, pow_one x⟩

variables (f : X →* Z)
/-- Given a homomorphism f of commutative rings α and β, if f(x) is invertible in β for some x ∈ α,
    we can construct a natural map from the localization of α at the submonoid generated by x
    to β. -/

@[elab_with_expected_type]
noncomputable def away.monoid_hom.lift {x : X} (hfx : is_unit (f x)) : away x →* Z :=
monoid_hom.lift' f (λ s, classical.some hfx ^ classical.some s.2) $ λ s,
by rw [units.coe_pow, ← classical.some_spec hfx,
       ← f.map_pow, classical.some_spec s.2]; refl

variables {f}
/-- Simplification lemmas for the natural ring homomorphism from the localization
    of a commutative ring α at the submonoid generated by some x ∈ α to a commutative ring β, given
    a ring homomorphism f such that f(x) is invertible in β. -/
@[simp] lemma away.monoid_hom.lift_of {x : X} (hfx : is_unit (f x)) (a : X) :
  away.monoid_hom.lift f hfx (of a) = f a := monoid_hom.lift'_of _ _

@[simp] lemma away.monoid_hom.lift_coe {x : X} (hfx : is_unit (f x)) (a : X) :
  away.monoid_hom.lift f hfx a = f a := monoid_hom.lift'_of _ _

/-- Given a ring homomorphism f between commutative rings α and β such that f(x) is invertible in β
    for some x ∈ α, the natural ring homomorphism we can construct from the localization of α to the
    submonoid generated by x to β makes the obvious diagram for α, β and the localization commute. -/
@[simp] lemma away.monoid_hom.lift_comp_of {x : X} (hfx : is_unit (f x)) :
  (away.monoid_hom.lift f hfx).comp (monoid_hom.of (submonoid.powers x)) = f :=
monoid_hom.lift'_comp_of _

/-- The natural map from a commutative ring α localized at the submonoid generated by some
    x ∈ α to the localization at the submonoid generated by x*y for some y ∈ α. -/
noncomputable def monoid_hom.away_to_away_right (x y : X) : away x →* away (x * y) :=
away.monoid_hom.lift (monoid_hom.of (submonoid.powers (x*y))) $
is_unit_of_mul_one x (y * away.inv_self (x * y)) $
by {rw [monoid_hom.of_apply, away.inv_self, coe_mul_mk, coe_mul_mk, mul_one, mk_apply,
        ←con.coe_one, localization.eq], use 1, simp}
end away

variables (α : Type*) [comm_ring α] (S : submonoid α)

/-- Instance defining addition in a commutative ring localized at a submonoid. -/
instance : has_add (localization α S) :=
⟨lift₂ S S
(λ x y : α × S, (((x.2 : α) * y.1 + y.2 * x.1, x.2 * y.2) : localization α S))
$ λ ⟨r1, s1⟩ ⟨r2, s2⟩ ⟨r3, s3⟩ ⟨r4, s4⟩ ⟨v, hv⟩ ⟨w, hw⟩,
by { rw localization.eq, use (↑w*↑v),
     apply S.mul_mem w.2 v.2,
     calc
       ↑w * ↑v * ((↑s1 * r2 + ↑s2 * r1) * (↑s3 * ↑s4))
         = ↑w * (r2 * ↑s4) * ↑v * (↑s1 * ↑s3) + ↑w * (↑v * (r1 * ↑s3)) * (↑s2 * ↑s4) : by ring
     ... = ↑w * ↑v * ((↑s3 * r4 + ↑s4 * r3) * (↑s1 * ↑s2)) : by rw [hv, hw]; ring}⟩

--/-- Instance defining additive inverse in a commutative ring localized at a submonoid. -/
instance : has_neg (localization α S) :=
⟨lift S (λ x : α × S, ((-x.1, x.2) : localization α S)) $
λ ⟨r1, s1⟩ ⟨r2, s2⟩ ⟨v, hv⟩,
by {rw localization.eq, use v, ring at hv ⊢, rw mul_neg_eq_neg_mul_symm, simp [hv]}⟩

instance : comm_ring (localization α S) :=
by refine
{ add            := has_add.add,
  add_assoc      := λ m n k, quotient.induction_on₃' m n k _,
  zero           := (((0 : α), (1 : S)) : localization α S),
  zero_add       := quotient.ind' _,
  add_zero       := quotient.ind' _,
  neg            := has_neg.neg,
  add_left_neg   := quotient.ind' _,
  add_comm       := quotient.ind₂' _,
  left_distrib   := λ m n k, quotient.induction_on₃' m n k _,
  right_distrib  := λ m n k, quotient.induction_on₃' m n k _,
  ..localization.comm_monoid};
{ intros,
  try {rcases a with ⟨r₁, s₁⟩},
  try {rcases b with ⟨r₂, s₂⟩},
  try {rcases c with ⟨r₃, s₃⟩},
  refine r_of_eq _,
  norm_num,
  try {ring}}

variables {α S}

variables (x y : α)

@[simp] lemma of_zero : of 0 = (0 : localization α S) := rfl

@[simp] lemma of_neg : (of (-x) : localization α S) = -of x := rfl

@[simp] lemma of_add : (of (x + y) : localization α S) = of x + of y :=
show _ = (↑(1 * y + 1 * x, (1 : S) * 1) : localization α S), by norm_num; use 1

@[simp] lemma of_sub : (of (x - y) : localization α S) = of x - of y :=
by simp; use 1

@[simp] lemma coe_zero : ((0 : α) : localization α S) = 0 := of_zero

@[simp] lemma coe_add : (↑(x + y) : localization α S) = x + y := of_add _ _

@[simp] lemma coe_sub : (↑(x - y) : localization α S) = x - y := of_sub _ _

@[simp] lemma coe_neg : (↑(-x) : localization α S) = -x := of_neg _

namespace semiring_hom

variables {β : Type*} [comm_ring β] {T : submonoid β} (f : α →+* β) (f' : S → units β) (S)

def of : α →+* localization α S :=
semiring_hom.mk' (monoid_hom.of S) $
λ x y, show ↑((x+y), (1 : S)) = ↑(1 * y + 1 * x, (1 : S) * 1), by norm_num; use 1

variables {S}

@[simp] lemma of_apply {a : α} : of S a = (a : localization α S) := rfl

lemma lift'_add (H : ∀ s : S, f s = f' s) (a b : localization α S) :
(monoid_hom.lift' f.to_monoid_hom f' H) (a + b) =
(monoid_hom.lift' f.to_monoid_hom f' H) a + (monoid_hom.lift' f.to_monoid_hom f' H) b :=
con.induction_on₂' a b $ λ x y, by
{ change (monoid_hom.lift' _ f' _) ↑(_ + _, _) = _,
  rw [monoid_hom.lift', con.lift_coe, con.lift_coe, con.lift_coe],
  change f ((x.2 : α) * _ + y.2 * _) * ((f' (_ * _))⁻¹ : _) = _*((f' _)⁻¹ : _) + _*((f' _)⁻¹ : _),
  ring,
  rw [f.map_add, ←units.mul_left_inj (f' (x.2 * y.2)), ←mul_assoc, units.mul_inv, one_mul,
     ←monoid_hom.map_mul_restrict f.to_monoid_hom f' H, units.coe_mul, mul_comm ↑(f' x.2), mul_add,
     ←mul_assoc, mul_assoc ↑(f' y.2), units.mul_inv, ←mul_assoc, mul_assoc ↑(f' y.2) ↑(f' x.2),
     mul_comm ↑(f' x.2), ←mul_assoc, units.mul_inv, ←H x.2, ←H y.2],
  change _ =  f _ * _ * f _ + _ * f _ * f _,
  simp}

@[elab_with_expected_type]
def lift' (H : ∀ s : S, f s = f' s) : (localization α S) →+* β :=
semiring_hom.mk' (monoid_hom.lift' f.to_monoid_hom f' H) $
λ a b, lift'_add _ _ _ _ _

noncomputable def lift (h : ∀ s : S, is_unit (f s)) :
  localization α S →+* β :=
lift' f (λ s, classical.some $ h s)
  (λ s, by rw [← classical.some_spec (h s)]; refl)

/-- Simplification lemmas for the definition of the natural ring homomorphism from the localization
    of a commutative ring α at a submonoid S to a commutative ring β, given a map g from S to β
    whose image is contained in the unit group of β and a ring homomorphism f from α to β such that
    g and f are equal on S. -/
variables {f f'}

@[simp] lemma lift'_mk (H : ∀ (s : S), f.to_monoid_hom s = f' s) (r : α) (s : S) :
  lift' f f' H (mk r s) = f r * ↑(f' s)⁻¹ := rfl

@[simp] lemma lift'_of (H : ∀ (s : S), f.to_monoid_hom s = f' s) (a : α) :
  lift' f f' H (localization.of a) = f a :=
by convert monoid_hom.lift'_of H a

@[simp] lemma lift'_coe (H : ∀ (s : S), f.to_monoid_hom s = f' s) (a : α) :
  lift' f f' H a = f a := lift'_of _ _

/-- Simplification lemmas for the natural ring homomorphism from the localization of a commutative
    ring α at a submonoid S to a commutative ring β, given a ring homomorphism f from α to β mapping
    elements of S to units in β. -/
@[simp] lemma lift_hom_of (h : ∀ s : S, is_unit (f s)) (a : α) :
  lift f h (localization.of a) = f a := lift'_of _ _

@[simp] lemma lift_coe (h : ∀ s : S, is_unit (f s)) (a : α) :
  lift f h a = f a := lift'_of _ _

/-- Given a map f' from a submonoid S of a commutative ring α whose image is contained in the unit
    group of another commutative ring β, and a ring homomorphism f from α to β, if f' and f are
    equal on S, the natural ring homomorphism we can construct from the localization to β makes
    the obvious diagram for α, β and the localization commute. -/
@[simp] lemma lift'_comp_of (H : ∀ (s : S), f.to_monoid_hom s = f' s) :
  (lift' f f' H).comp (of S) = f :=
semiring_hom.ext _ _ $ funext $ λ a, lift'_of H a

/-- Given a ring homomorphism f between commutative rings α and β mapping elements of a submonoid S
    to units in β, the natural ring homomorphism we can construct from the localization to β makes
    the obvious diagram for α, β and the localization commute. -/
@[simp] lemma lift_comp_of (h : ∀ s : S, is_unit (f s)) :
  (lift f h).comp (of S) = f := lift'_comp_of _

/-- Given a map f' from a submonoid S of a commutative ring α whose image is contained in the unit
    group of another commutative ring β, and a ring homomorphism f from the localization to β, if
    f' and f are equal on S, the natural ring homomorphism from the localization to β constructed
    from f' and f composed with the coercion from the ring to the localization is just f. -/
@[simp] lemma lift'_apply_coe (g : localization α S →+* β) (H : ∀ s : S, g.comp (of S) s = f' s) :
  lift' (g.comp (of S)) f' H = g :=
begin
  have h : _ := monoid_hom.lift'_apply_coe g.to_monoid_hom (λ s, show _, by apply H s),
  ext,
  change _ = g.to_monoid_hom x,
  rw h.symm,
  refl,
end

 /-- Given a ring homomorphism f from the localization of a commutative ring α at a submonoid S to a
    commutative ring β, the natural ring homomorphism from the localization to β constructed from
    f composed with the coercion from the ring to the localization is just f.-/
@[simp] lemma lift_apply_coe (g : localization α S →+* β) :
  lift (g.comp (of S)) (λ y, is_unit_unit (g.to_monoid_hom.units_map (to_units y))) = g :=
by rw [lift, lift'_apply_coe]

/-- Function extensionality for localisations:
 two functions are equal if they agree on elements that are coercions.-/
protected lemma funext (f g : localization α S →+* β)
  (h : ∀ a : α, f a = g a) : f = g :=
begin
  rw [← lift_apply_coe f, ← lift_apply_coe g],
  congr' 1,
  ext,
  convert h x,
end

/-- Given a ring homomorphism f between commutative rings α and β, if f's image on a submonoid S is
    contained in a submonoid T, we can construct a natural map between the respective
    localizations. -/
variables (f)

def map (hf : ∀ s : S, f s ∈ T) : localization α S →+* localization β T :=
semiring_hom.mk' (monoid_hom.lift' ((of T).comp f).to_monoid_hom
  (to_units_hom.comp ((f.to_monoid_hom.comp S.subtype).subtype_mk T hf)) $ λ y, rfl)
$ λ a b, lift'_add _ _ _ _ _

variables {f}

/-- Given a ring homomorphism f between commutative rings α and β, if f's image on a submonoid S is
    contained in a submonoid T, the natural ring homomorphism we can construct between the
    respective localizations makes the obvious diagram for α, β and the localizations commute. -/
lemma map_of (hf : ∀ s : S, f s ∈ T) (a : α) :
  map f hf (localization.of a) = localization.of (f a) := lift'_of _ _

/-- Given a ring homomorphism f between commutative rings α and β, if f's image on a submonoid S is
    contained in a submonoid T, the natural ring homomorphism we can construct between the
    respective localizations makes the obvious diagram for α, β and the localizations commute. -/
lemma map_coe (hf : ∀ s : S, f s ∈ T) (a : α) :
  map f hf a = (f a) := lift'_of _ _

/-- Given a ring homomorphism f between commutative rings α and β, if f's image on a submonoid S is
    contained in a submonoid T, the natural ring homomorphism we can construct between the
    respective localizations makes the obvious diagram for α, β and the localizations commute. -/
@[simp] lemma map_comp_of (hf : ∀ s : S, f s ∈ T) :
  (map f hf).comp (of S) = (of T).comp f := lift'_comp_of _

/-- Lifting the identity map on a commutative ring α to a map gives an identity map on a
    localization. -/
@[simp] lemma map_id : map (semiring_hom.id α) (λ y, y.2) = semiring_hom.id (localization α S) :=
semiring_hom.funext _ _ $ map_coe _

/-- Given ring homomorphisms f, g between commutative rings α, β and γ, if f's image on a submonoid
    S is contained in a submonoid T and g's image on T is contained in a submonoid U, composition of
    the natural ring homomorphisms we can construct between the respective localizations commutes
    with composition of f and g. -/
lemma map_comp_map {γ : Type*} [comm_ring γ] (hf : ∀ s : S, f s ∈ T) (U : submonoid γ)
(g : β →+* γ) (hg : ∀ t : T, g t ∈ U) :
  (map g hg).comp (map f hf) = map (g.comp f) (λ y, hg ⟨f y, (hf y)⟩) :=
semiring_hom.funext _ _ $ λ x, by simp only [semiring_hom.comp_apply, map_coe]

/-- Given ring homomorphisms f, g between commutative rings α, β and γ, if f's image on a submonoid
    S is contained in a submonoid T and g's image on T is contained in a submonoid U, composition of
    the natural ring homomorphisms we can construct between the respective localizations commutes
    with composition of f and g. -/
lemma map_map {γ : Type*} [comm_ring γ] (hf : ∀ s : S, f s ∈ T) (U : submonoid γ)
(g : β →+* γ) (hg : ∀ t : T, g t ∈ U) (x : localization α S) :
  map g hg (map f hf x) = map (g.comp f) (λ s : S, hg (⟨f s, (hf s)⟩ : T)) x :=
by {rw ←(map_comp_map hf U g hg), refl}

lemma map_ext (hf : ∀ s : S, f s ∈ T) (g : α →+* β) (hg : ∀ s : S, g s ∈ T) (h : f = g)
  (x : localization α S) :
  map f hf x = map g hg x := by tidy

end semiring_hom

namespace ring_equiv

variables {β : Type*} [comm_ring β] {T : submonoid β} (f : α →+* β)

def equiv_of_equiv (h₁ : α ≃r β) (h₂ : h₁.to_equiv '' S = T) :
  localization α S ≃r localization β T :=
let H1 : h₁.to_monoid_equiv.to_monoid_hom.map S = T := by
 { ext, rw [←submonoid.mem_coe T, ←h₂], refl} in
{hom := ring_equiv.is_ring_hom_of_monoid_equiv
  (h₁.to_monoid_equiv.equiv_of_equiv H1) $
  λ (x y : localization α S), by
  convert semiring_hom.lift'_add ((semiring_hom.of T).comp h₁.to_semiring_hom) _ _ x y,
..(h₁.to_monoid_equiv.equiv_of_equiv H1).to_equiv }

def char_pred (H : ∀ s : S, is_unit (f s)) :=
monoid_equiv.char_pred f.to_monoid_hom H

lemma char_pred_of_equiv (H : ∀ s : S, is_unit (f s)) (h : (localization α S) ≃r β)
  (hf : semiring_hom.lift f H = h.to_semiring_hom) : char_pred f H :=
by convert monoid_equiv.char_pred_of_equiv f.to_monoid_hom H h.to_monoid_equiv
(show monoid_hom.lift f.to_monoid_hom H = h.to_semiring_hom.to_monoid_hom, by {rw hf.symm, refl})

noncomputable def equiv_of_char_pred (H : ∀ s : S, is_unit (f s)) (Hp : char_pred f H) :
  (localization α S) ≃r β :=
ring_equiv.of_monoid_equiv (monoid_equiv.equiv_of_char_pred f.to_monoid_hom H Hp) $
λ x y, by convert semiring_hom.lift'_add f _ _ _ _

end ring_equiv

section
variables {β : Type*} [comm_ring β] {T : submonoid β} (f : α →+* β)

@[elab_with_expected_type]
noncomputable def away.lift {x : α} (hfx : is_unit (f x)) : away x →+* β :=
semiring_hom.mk' (away.monoid_hom.lift f.to_monoid_hom hfx) $
semiring_hom.lift'_add f (λ s, classical.some hfx ^ classical.some s.2) $ λ s,
by rw [units.coe_pow, ← classical.some_spec hfx,
       ← f.map_pow, classical.some_spec s.2]; refl

@[simp] lemma away.lift_of {x : α} (hfx : is_unit (f x)) (a : α) :
  away.lift f hfx (localization.of a) = f a := semiring_hom.lift'_of _ _

@[simp] lemma away.lift_coe {x : α} (hfx : is_unit (f x)) (a : α) :
  away.lift f hfx a = f a := semiring_hom.lift'_of _ _

/-- Given a ring homomorphism f between commutative rings α and β such that f(x) is invertible in β
    for some x ∈ α, the natural ring homomorphism we can construct from the localization of α to the
    submonoid generated by x to β makes the obvious diagram for α, β and the localization commute. -/
@[simp] lemma away.lift_comp_of {x : α} (hfx : is_unit (f x)) :
  (away.lift f hfx).comp (semiring_hom.of _) = f := semiring_hom.lift'_comp_of _

/-- The natural map from a commutative ring α localized at the submonoid generated by some
    x ∈ α to the localization at the submonoid generated by x*y for some y ∈ α. -/

noncomputable def away_to_away_right (x y : α) : away x →+* away (x * y) :=
away.lift (semiring_hom.of _) $ is_unit_of_mul_one x (y * away.inv_self (x * y)) $
by rw [away.inv_self, coe_mul_mk, semiring_hom.of_apply, coe_mul_mk, mul_one,
       mk_self (show (x*y) ∈ submonoid.powers (x*y), from ⟨1, pow_one (x*y)⟩)]

end
/- Needs ring_theory.ideals to compile
section at_prime

variables (P : ideal α) [hp : ideal.is_prime P]
include hp
/- From here onwards I've translated the old file very lazily, just changing enough so that it
    compiles. I'm going to try and golf it and make better use of the rest of the file. -/

/-- The submonoid of a commutative ring α whose underlying set is the complement of a prime
    ideal. -/
def prime.submonoid : submonoid α :=
{ carrier := (-P : set α),
  one_mem' := P.ne_top_iff_one.1 hp.1,
  mul_mem' := λ x y hnx hny hxy, or.cases_on (hp.2 hxy) hnx hny }

/-- The localization of a commutative ring α at the complement of a prime ideal. -/
@[reducible] def at_prime := localization α (prime.submonoid P)

/-- The localization of a commutative ring α at the complement of a prime ideal is a local
    ring. -/
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
    have : ∀ {r : α} {s : prime.submonoid P}, ((r, s) : at_prime P) ∈ nonunits (at_prime P) → r ∈ P,
    { haveI := classical.dec,
      exact λ r s, not_imp_comm.1 (λ nr,
        is_unit_iff_exists_inv.2 ⟨(((s : α), (⟨r, nr⟩ : prime.submonoid P)) : at_prime P),
          by {rw con.coe_mul, exact (r_of_eq (by simp [mul_comm]))}⟩)},
    rw [←sub_eq_zero, ←mul_sub] at ht,
    have hr₃ := (hp.mem_or_mem_of_mul_eq_zero ht).resolve_left t.2,
    have := (ideal.neg_mem_iff _).1 ((ideal.add_mem_iff_right _ _).1 hr₃),
    { exact not_or (mt hp.mem_or_mem (not_or s₁.2 s₂.2)) s₃.2 (hp.mem_or_mem this) },
    { exact (P.mul_mem_right
        (P.add_mem (P.mul_mem_left (this hy)) (P.mul_mem_left (this hx)))) }
  end)

end at_prime
-/
variable (α)

/-- The set of non zero divisors of a commutative ring α. -/
def non_zero_divisors' : set α := {x | ∀ z, z * x = 0 → z = 0}

/-- The submonoid of non zero divisors of a commutative ring α. -/
def non_zero_divisors : submonoid α :=
{ carrier := non_zero_divisors' α,
  one_mem' := λ z hz, by rwa mul_one at hz,
  mul_mem' := λ x₁ x₂ hx₁ hx₂ z hz,
    have z * x₁ * x₂ = 0, by rwa mul_assoc,
    hx₁ z $ hx₂ (z * x₁) this }

@[simp] lemma non_zero_divisors_one_val : ((1 : non_zero_divisors α) : α) = 1 := rfl

/-- The field of fractions of an integral domain.-/
@[reducible] def fraction_ring := localization α (non_zero_divisors α)

namespace fraction_ring

open function

variables {β : Type*} [integral_domain β] [decidable_eq β]

/-- For a non-zero element x of an integral domain β, ∀ y ∈ β, y*x = 0 implies y is zero. -/
lemma eq_zero_of_ne_zero_of_mul_eq_zero {x y : β} :
  x ≠ 0 → y * x = 0 → y = 0 :=
λ hnx hxy, or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

/-- In an integral domain β, x ∈ β is a non zero divisor iff x is nonzero. -/
lemma mem_non_zero_divisors_iff_ne_zero {x : β} :
  x ∈ non_zero_divisors β ↔ x ≠ 0 :=
⟨λ hm hz, zero_ne_one (hm 1 $ by norm_num [hz]).symm,
 λ hnx z, eq_zero_of_ne_zero_of_mul_eq_zero hnx⟩

variable (β)

/-- Auxiliary function for the definition of inverses in the field of fractions of an integral
    domain.-/
def inv_aux (x : β × (non_zero_divisors β)) : fraction_ring β :=
if h : x.1 = 0 then 0 else ((x.2 : β), (⟨x.1, mem_non_zero_divisors_iff_ne_zero.mpr h⟩ : non_zero_divisors β))

/-- An instance defining inverses in the field of fractions of an integral domain. -/
instance : has_inv (fraction_ring β) :=
⟨lift (non_zero_divisors β) (inv_aux β) $
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

/-- The definition of the inverse of the equivalence class of (r, s) in the field of fractions of
    an integral domain β for some r, s≠0 ∈ β. -/
lemma mk_inv {r : β} {s : non_zero_divisors β} :
  (mk r s : fraction_ring β)⁻¹ =
  if h : r = 0 then 0 else
  ((s : β), (⟨r, mem_non_zero_divisors_iff_ne_zero.mpr h⟩ : non_zero_divisors β)) := rfl

/-- The definition of the inverse of the equivalence class of x in the field of fractions of
    an integral domain β for some x ∈ β × β/{0}. -/
lemma mk_inv' : ∀ (x : β × (non_zero_divisors β)), (x⁻¹ : fraction_ring β) =
  if h : x.1 = 0 then 0 else
  ((x.2 : β), (⟨x.1, mem_non_zero_divisors_iff_ne_zero.mpr h⟩ : non_zero_divisors β))
| ⟨r,s,hs⟩ := rfl

/-- Equality is decidable in the field of fractions of an integral domain with decidable equality. -/
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
  exact con.induction_on' a (λ x h, by {unfold has_inv.inv, rw [lift_beta, inv_aux, dif_neg
    (show x.1 ≠ 0, from λ hx, h (r_of_eq $ by simp [hx]))], exact (r_of_eq $ by simp [mul_comm])})}

/-- The equivalence class of (r, s) in the field of fractions of an integral domain β for some
    r, s≠0 ∈ β equals r/s. -/
@[simp] lemma mk_eq_div {r : β} {s : non_zero_divisors β} :
  (mk r s : fraction_ring β) = (r / (s : β) : fraction_ring β) :=
show mk r s = r * dite (s.1 = 0) _ _, by rw [dif_neg (mem_non_zero_divisors_iff_ne_zero.mp s.2)];
exact mk_eq_mul_mk_one _ _

variables {β}

/-- The equivalence class of x in the field of fractions of an integral domain β for some
    x ∈ β × β/{0} equals the first component of x divided by the second component. -/
@[simp] lemma mk_eq_div' (x : β × (non_zero_divisors β)) :
  (x : fraction_ring β) = ((x.1) / ((x.2) : β) : fraction_ring β) :=
by erw ← mk_eq_div; cases x; refl

/-- If an element x of an integral domain β is zero in the field of fractions of β, x is zero in β. -/
lemma eq_zero_of (x : β) (h : (localization.of x : fraction_ring β) = 0) : x = 0 :=
begin
  rcases con.eq.1 h with ⟨t, ht⟩,
  exact or.resolve_left
    (show t.1 = 0 ∨ _, by simpa using ht) (mem_non_zero_divisors_iff_ne_zero.1 t.2),
end

variables (β)
def of : β →+* fraction_ring β := semiring_hom.of (non_zero_divisors β)
variables {β}

/-- The natural map from an integral domain to its field of fractions if injective. -/
lemma of.injective : injective (of β : β → fraction_ring β) :=
(semiring_hom.injective_iff _).2 (λ x h, eq_zero_of x (show localization.of x = 0, from h))

section map

open function
variables {A : Type*} [integral_domain A] [decidable_eq A]
variables {B : Type*} [integral_domain B] [decidable_eq B]
variables (g : A →+* B)

/-- Given an injective homomorphism of integral domains, we can construct a natural map of
    fields of fractions. -/
def map (hg : injective g) : fraction_ring A →+* fraction_ring B :=
semiring_hom.map g $ λ s,
  by rw [mem_non_zero_divisors_iff_ne_zero, ← g.map_zero, ne.def, hg.eq_iff];
    exact mem_non_zero_divisors_iff_ne_zero.1 s.2

/-- Given an injective homomorphism of integral domains, the natural map we can construct of the
    respective fields of fractions makes the obvious diagram commute. -/
@[simp] lemma map_of (hg : injective g) (a : A) :
  (map g hg).1 (localization.of a) = (localization.of (g a) : fraction_ring B) :=
semiring_hom.map_of _ _

/-- Given an injective homomorphism of integral domains, the natural map we can construct of the
    respective fields of fractions makes the obvious diagram commute. -/
@[simp] lemma map_coe (hg : injective g) (a : A) : (map g hg).1 a = g a :=
semiring_hom.map_coe _ _

/-- Given an injective homomorphism of integral domains, the natural map we can construct of the
    respective fields of fractions makes the obvious diagram commute. -/
@[simp] lemma map_comp_of (hg : injective g) : (map g hg).comp (of A) = (of B).comp g :=
semiring_hom.map_comp_of _

/-- Given an injective homomorphism of integral domains, the natural map we can construct of the
    respective fields of fractions is a field homomorphism. -/
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

end localization
/-
section ideals

/--The image of the preimage of an ideal of a localization of a commutative ring under the natural
   map from the ring to the localization equals the original ideal. -/
theorem map_comap (J : ideal (localization α S)) :
  ideal.map coe (ideal.comap (coe : α → localization α S) J) = J :=
le_antisymm (ideal.map_le_iff_le_comap.2 (le_refl _)) $ λ x,
localization.induction_on x $ λ r s hJ, (submodule.mem_coe _).2 $
mul_one r ▸ coe_mul_mk r 1 s ▸ (ideal.mul_mem_right _ $ ideal.mem_map_of_mem $
have _ := @ideal.mul_mem_left (localization α S) _ _ s _ hJ,
by rwa [coe_coe, coe_mul_mk, mk_mul_cancel_left] at this)

/-- There is an order embedding between the ideals of a localization of a commutative ring and the
    ideals of the ring, ordered by inclusion. -/
def le_order_embedding :
  ((≤) : ideal (localization α S) → ideal (localization α S) → Prop) ≼o
  ((≤) : ideal α → ideal α → Prop) :=
{ to_fun := λ J, ideal.comap coe J,
  inj := function.injective_of_left_inverse (map_comap α),
  ord := λ J₁ J₂, ⟨ideal.comap_mono, λ hJ,
    map_comap α J₁ ▸ map_comap α J₂ ▸ ideal.map_mono hJ⟩ }

end ideals-/
