import data.equiv.congruence algebra.associated

variables {X : Type*} [comm_monoid X] (Y : submonoid X)
          {Z : Type*} [comm_monoid Z]

namespace submonoid

instance : comm_monoid Y :=
by refine {mul_comm := _, ..submonoid.to_monoid};
   {intros, rw subtype.ext, apply mul_comm}

def fracr : con (X × Y) :=
{ r := λ a b, ∃ c : Y, (c:X) * (a.1 * b.2) = c * (b.1 * a.2),
  iseqv := ⟨λ a, ⟨1, rfl⟩, λ a b ⟨c, hc⟩, ⟨c, hc.symm⟩,
           λ a b c ⟨m, hm⟩ ⟨n, hn⟩, ⟨ n*m*b.2, by
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

namespace frac
variables {Y}
instance frac_coe : has_coe (X × Y) Y.fracr.quotient := infer_instance
/-- The natural map mapping an element r of a commutative ring and an element s of a submonoid
    to the equivalence class of (r, s) in the ring's localization at the submonoid. -/
@[reducible] def mk (x : X) (y : Y) : Y.fracr.quotient := (x, y)
@[simp] lemma mk_apply (x : X) (y : Y) : mk x y = (x, y) := rfl
@[reducible] def of (r : X) : Y.fracr.quotient := ((r, (1:Y)) : Y.fracr.quotient)

variables (Y)

instance of_coe : has_coe X Y.fracr.quotient := ⟨λ x, ((x, (1 : Y)) : Y.fracr.quotient)⟩

@[simp] lemma of_apply {x : X} : (x : Y.fracr.quotient) = ((x, (1 : Y)) : Y.fracr.quotient) := rfl

@[simp] protected lemma eq {Y : submonoid X} {a b : X × Y} :
(a : Y.fracr.quotient) = b ↔ ∃ c:Y, (c:X) * (a.1 * b.2) = (c:X) * (b.1 * a.2) :=
⟨λ h, exists.elim (con.quotient.eq.1 h) $ λ w hw, exists.intro w hw,
λ ⟨w, hw⟩, con.quotient.eq.2 ⟨w, hw⟩⟩

@[elab_as_eliminator, reducible]
def lift {β : Type*} (f : (X × Y) → β) (H : ∀ a b, Y.fracr a b → f a = f b) : Y.fracr.quotient → β :=
λ q, con.quotient.lift_on' q f H

@[elab_as_eliminator, reducible]
def lift₂ (W : submonoid X) {β : Type*} (f : (X × Y) → (X × W) → β)
  (H : ∀ a b c d, Y.fracr a c → W.fracr b d → f a b = f c d) :
Y.fracr.quotient → W.fracr.quotient → β := λ q r, con.quotient.lift_on₂' q r f H

variables {Y}

lemma fracr_of_eq {a b : X × Y} (h : (a.2 : X) * b.1 = b.2 * a.1) : (a : Y.fracr.quotient) = b :=
frac.eq.2 $ ⟨1, by rw [mul_comm b.1, h, mul_comm a.1]⟩

@[simp] lemma mk_self' (x : Y) : (((x : X), x) : Y.fracr.quotient) = 1 :=
by {rw [←con.quotient.coe_one, con.quotient.eq], use 1, simp}

@[simp] lemma mk_self {x : X} (hx : x ∈ Y) : ((x, (⟨x, hx⟩ : Y)) : Y.fracr.quotient) = 1 :=
mk_self' ⟨x, hx⟩

@[simp] lemma mk_mul (a b : X × Y) :
  ((a * b : X × Y) : Y.fracr.quotient) = (a : Y.fracr.quotient) * (b : Y.fracr.quotient) := rfl

@[simp] lemma of_mul (a b : X) :
  ((a * b : X) : Y.fracr.quotient) = (a : Y.fracr.quotient) * (b : Y.fracr.quotient) :=
by simp; use 1

protected lemma mul_comm {Y : submonoid X} : ∀ x y : Y.fracr.quotient, x * y = y * x :=
λ x y, con.quotient.induction_on₂' x y (λ a b, by
 { rw [con.quotient.coe_mul, con.quotient.coe_mul, con.quotient.eq], use 1, simp [mul_comm]})

instance : comm_monoid Y.fracr.quotient :=
by refine { mul_comm := frac.mul_comm, ..Y.fracr.monoid}

def to_units (y : Y) : units Y.fracr.quotient :=
⟨of y, ((1 : X), y), by norm_num, by norm_num⟩

def to_units_hom : Y →* units Y.fracr.quotient :=
⟨to_units, rfl, λ x y, by ext; apply of_mul⟩

@[simp] lemma to_units_coe (y : Y) : ((to_units y) : Y.fracr.quotient) = (y : X) := rfl

lemma to_units_inv {y : Y} : mk 1 y = ((to_units y)⁻¹ : units Y.fracr.quotient) := rfl

lemma to_units_map (g : Y.fracr.quotient →* Z) (y : Y) :
g (to_units y) = g.units_map (to_units y) :=
by simp

lemma to_units_map_inv (g : Y.fracr.quotient →* Z) (y : Y) :
g ((to_units y)⁻¹ : units Y.fracr.quotient) = ((g.units_map (to_units y))⁻¹ : units Z) :=
by rw [←monoid_hom.coe_units_map, monoid_hom.map_inv]

variables (Y) --of_hom can't infer this otherwise :/

def of_hom : X →* Y.fracr.quotient := ⟨of, by tidy, of_mul⟩

variables {Y}

@[simp] lemma of_hom_apply {x : X} : of_hom Y x = (x : Y.fracr.quotient) := rfl

/-- The map from α × S, α a commutative ring and S a submonoid, to the localization preserves
    multiplication in the first argument. -/
@[simp] lemma coe_mul_mk (x y : X) (v : Y) :
  ↑x * mk y v = mk (x * y) v :=
fracr_of_eq $ by simp

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
by rw [mk_eq_mul_mk_one, mul_comm ↑y, of_mul,
       mul_assoc, ← mk_eq_mul_mk_one, mk_apply, mk_self', mul_one]

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
  (H : ∀ a b, Y.fracr a b → f a = f b) {x : X × Y} :
lift Y f H x = f x := rfl

variables {f : X →* Z} (f' : Y → units Z) (H : ∀ y : Y, f y = f' y)

@[simp] lemma map_one_restrict (H : ∀ y : Y, f y = f' y) : f' 1 = 1 :=
by {ext, rw ←H 1, simp}

@[simp] lemma map_mul_restrict (H : ∀ y : Y, f y = f' y) {x y : Y} : (f' x) * (f' y) = f' (x*y) :=
by {ext, rw [units.coe_mul, ←H x, ←H y, ←H (x*y)], simp}

variables {f f'}

def aux_hom' (H : ∀ y : Y, f y = f' y) : X × Y →* Z :=
{ to_fun := λ x, (f x.1)*((f' x.2)⁻¹ : units Z),
  map_one' := by rw [prod.snd_one, map_one_restrict f' H]; simp,
  map_mul' := λ a b, by
    {suffices : _ * _ * _ = _ * _ * _, by simpa,
     rw [←map_mul_restrict f' H, mul_inv_rev, units.coe_mul, mul_assoc,
         ←mul_assoc (f b.1), mul_comm _ ↑(f' a.2)⁻¹],
     simp only [mul_assoc]}}

variables (f f')

def lift_hom' (H : ∀ y : Y, f y = f' y) : Y.fracr.quotient →* Z :=
(aux_hom' H).lift Y.fracr $ λ a b ⟨v, hv⟩, show _ * _ = _ * _, by
   rw [mul_comm (f a.1), mul_comm (f b.1), ←mul_one (f a.1), ←(f' b.2).mul_inv,
       mul_comm ↑(f' b.2)⁻¹, ←mul_assoc (f a.1), ←H b.2, ←f.map_mul, ←one_mul (f (a.1*↑b.2)),
       ←(f' v).inv_mul, mul_assoc ↑(f' v)⁻¹, ←H v, ←f.map_mul, hv, f.map_mul,
       ←mul_assoc ↑(f' v)⁻¹, H v, (f' v).inv_mul, one_mul, f.map_mul, mul_comm (f b.1),
       ←mul_assoc, ←mul_assoc, H a.2, (f' a.2).inv_mul, one_mul]

noncomputable def lift_hom (H : ∀ y : Y, is_unit (f y)) : Y.fracr.quotient →* Z :=
lift_hom' f (λ y, classical.some $ H y)
  (λ y, by rw [← classical.some_spec (H y)]; refl)

variables {f f'}
/-- Simplification lemmas for the definition of the natural ring homomorphism from the localization
    of a commutative ring α at a submonoid S to a commutative ring β, given a map g from S to β
    whose image is contained in the unit group of β and a ring homomorphism f from α to β such that
    g and f are equal on S. -/
@[simp] lemma lift_hom'_mk (H : ∀ y : Y, f y = f' y) (x : X) (y : Y) :
  lift_hom' f f' H (mk x y) = f x * ↑(f' y)⁻¹ := rfl

@[simp] lemma lift_hom'_of (H : ∀ y : Y, f y = f' y) (x : X) :
  lift_hom' f f' H (of x) = f x :=
by rw [lift_hom'_mk H x 1]; simp [map_one_restrict f' H]

@[simp] lemma lift_hom'_coe (H : ∀ y : Y, f y = f' y) (x : X) :
  lift_hom' f f' H x = f x := lift_hom'_of _ _

/-- Simplification lemmas for the natural ring homomorphism from the localization of a commutative
    ring α at a submonoid S to a commutative ring β, given a ring homomorphism f from α to β mapping
    elements of S to units in β. -/
@[simp] lemma lift_hom_of (H : ∀ y : Y, is_unit (f y)) (x : X) :
  lift_hom f H (of x) = f x := lift_hom'_of _ _

@[simp] lemma lift_hom_coe (H : ∀ y : Y, is_unit (f y)) (x : X) :
  lift_hom f H x = f x := lift_hom'_of _ _

/-- Given a map g from a submonoid S of a commutative ring α whose image is contained in the unit
    group of another commutative ring β, and a ring homomorphism f from α to β, if g and f are
    equal on S, the natural ring homomorphism we can construct from the localization to β makes
    the obvious diagram for α, β and the localization commute. -/
lemma lift_hom'_comp_of_hom (H : ∀ y : Y, f y = f' y)  :
  (lift_hom' f f' H).comp (of_hom Y) = f := monoid_hom.ext _ _ $ funext $ λ a, lift_hom'_of H a

--/-- Given a ring homomorphism f between commutative rings α and β mapping elements of a submonoid S
  --  to units in β, the natural ring homomorphism we can construct from the localization to β makes
  --  the obvious diagram for α, β and the localization commute. -/
--@[simp] lemma lift_comp_of (h : ∀ s ∈ S, is_unit (f s)) :
  --lift f h ∘ of = f := lift'_comp_of _ _ _

/-- Given a map g from a submonoid S of a commutative ring α whose image is contained in the unit
    group of another commutative ring β, and a ring homomorphism f from the localization to β, if
    g and f are equal on S, the natural ring homomorphism from the localization to β constructed
    from g and f composed with the coercion from the ring to the localization is just f. -/
@[simp] lemma lift_hom'_apply_coe (g : Y.fracr.quotient →* Z) (H : ∀ y : Y, g.comp (of_hom Y) y = f' y) :
  lift_hom' (g.comp (of_hom Y)) f' H = g :=
begin
  ext x,
  apply con.quotient.induction_on' x,
  intro y,
  rw [(@prod.mk.eta _ _ y).symm, ←mk_apply, lift_hom'_mk, ←units.mul_right_inj (f' y.2), mul_assoc,
      units.inv_mul, ←H y.2, mul_one, mk_eq_mul_mk_one, g.map_mul, to_units_inv, mul_assoc,
      to_units_map_inv],
  change _ = _ * ( _ * g (of_hom Y (y.2 : X))),
  rw [of_hom_apply, ←to_units_coe y.2, to_units_map, units.inv_mul],
  show g (of_hom Y y.1) = _, by simp,
end

/-- Given a ring homomorphism f from the localization of a commutative ring α at a submonoid S to a
    commutative ring β, the natural ring homomorphism from the localization to β constructed from
    f composed with the coercion from the ring to the localization is just f.-/
@[simp] lemma lift_hom_apply_coe (g : Y.fracr.quotient →* Z) :
  lift_hom (g.comp (of_hom Y)) (λ y, is_unit_unit (g.units_map (to_units y))) = g :=
by rw [lift_hom, lift_hom'_apply_coe]

/-- Function extensionality for localisations:
 two functions are equal if they agree on elements that are coercions.-/
protected lemma funext (f g : Y.fracr.quotient →* Z)
  (h : ∀ a : X, f a = g a) : f = g :=
begin
  rw [← lift_hom_apply_coe f, ← lift_hom_apply_coe g],
  congr' 1,
  ext,
  convert h x,
end

variables {W : submonoid Z}

/-- Given a ring homomorphism f between commutative rings α and β, if f's image on a submonoid S is
    contained in a submonoid T, we can construct a natural map between the respective
    localizations. -/
variables (f)

def map (hf : ∀ y : Y, f y ∈ W) : Y.fracr.quotient →* W.fracr.quotient :=
lift_hom' ((of_hom W).comp f) (to_units_hom.comp ((f.comp Y.subtype).subtype_mk W hf)) $
λ y, rfl

variables {f}
/-- Given a ring homomorphism f between commutative rings α and β, if f's image on a submonoid S is
    contained in a submonoid T, the natural ring homomorphism we can construct between the
    respective localizations makes the obvious diagram for α, β and the localizations commute. -/
@[simp] lemma map_of (hf : ∀ y : Y, f y ∈ W) (x : X) :
  map f hf (of x) = of (f x) := lift_hom'_of _ _

/-- Given a ring homomorphism f between commutative rings α and β, if f's image on a submonoid S is
    contained in a submonoid T, the natural ring homomorphism we can construct between the
    respective localizations makes the obvious diagram for α, β and the localizations commute. -/
@[simp] lemma map_coe (hf : ∀ y : Y, f y ∈ W) (x : X) :
  map f hf x = (f x) := lift_hom'_of _ _

/-- Given a ring homomorphism f between commutative rings α and β, if f's image on a submonoid S is
    contained in a submonoid T, the natural ring homomorphism we can construct between the
    respective localizations makes the obvious diagram for α, β and the localizations commute. -/
@[simp] lemma map_comp_of (hf : ∀ y : Y, f y ∈ W) :
  map f hf ∘ of = of ∘ f := funext $ λ a, map_of _ _

/-- Lifting the identity map on a commutative ring α to a map gives an identity map on a
    localization. -/
@[simp] lemma map_id : map (monoid_hom.id X) (λ y, y.2) = monoid_hom.id Y.fracr.quotient :=
frac.funext _ _ $ map_coe _

/-- Given ring homomorphisms f, g between commutative rings α, β and γ, if f's image on a submonoid
    S is contained in a submonoid T and g's image on T is contained in a submonoid U, composition of
    the natural ring homomorphisms we can construct between the respective localizations commutes
    with composition of f and g. -/
lemma map_comp_map {A : Type*} [comm_monoid A] (hf : ∀ y : Y, f y ∈ W) (V : submonoid A)
(g : Z →* A) (hg : ∀ w : W, g w ∈ V) :
  (map g hg).comp (map f hf) = map (g.comp f) (λ y, hg ⟨f y, (hf y)⟩) :=
frac.funext _ _ $ λ x, by simp only [map_coe, monoid_hom.comp_apply]

/-- Given ring homomorphisms f, g between commutative rings α, β and γ, if f's image on a submonoid
    S is contained in a submonoid T and g's image on T is contained in a submonoid U, composition of
    the natural ring homomorphisms we can construct between the respective localizations commutes
    with composition of f and g. -/
lemma map_map {A : Type*} [comm_monoid A] (hf : ∀ y : Y, f y ∈ W) (V : submonoid A)
(g : Z →* A) (hg : ∀ w : W, g w ∈ V) (x : Y.fracr.quotient) :
  map g hg (map f hf x) = map (g.comp f) (λ y : Y, hg (⟨f y, (hf y)⟩ : W)) x :=
by {rw ←(map_comp_map hf V g hg), refl}

variables (f)
lemma map_ext (hf : ∀ y : Y, f y ∈ W) (g : X →* Z) (hg : ∀ y : Y, g y ∈ W) (h : f = g)
  (x : Y.fracr.quotient) :
  map f hf x = map g hg x := by tidy
/-- Given a ring isomorphism h₁ between commutative rings α and β, if h₁'s image on a submonoid S is
    a submonoid T, we can construct a natural isomorphism between the respective localizations. -/

def equiv_of_equiv_aux (h : X ≃* Z) (H : h.to_monoid_hom.map Y = W) :
  Y.fracr.quotient ≃ W.fracr.quotient :=
let H1 : ∀ y:Y, h y ∈ W := by
 { intro y, rw [←H, ←submonoid.mem_coe], change _ ∈ (h '' Y), exact ⟨(y: X), y.2, rfl⟩} in
let H2 : ∀ w : W, h.symm w ∈ Y := by
 { intro w, rcases (show (w : Z) ∈ h.to_monoid_hom.map Y, by {rw H, apply w.2}) with ⟨y, hym, hy⟩,
   rw [hy.symm, h.to_monoid_hom_apply, h.left_inv_apply], exact (submonoid.mem_coe Y).1 hym} in
{ to_fun := @map _ _ Y _ _ h.to_monoid_hom W $ H1,
  inv_fun := @map _ _ W _ _ h.symm.to_monoid_hom Y $ H2,
  left_inv := λ x, by {rw map_map,
    conv {to_rhs, rw (show x = (monoid_hom.id Y.fracr.quotient : _ → Y.fracr.quotient) x, from rfl),
    rw ←map_id}, refine map_ext (h.symm.to_monoid_hom.comp h.to_monoid_hom)
      (λ (y : Y), H2 (⟨_, H1 y⟩)) (monoid_hom.id X) (λ y, y.2) _ x,
    apply h.left_inv_hom},
  right_inv := λ x, by {rw map_map,
    conv {to_rhs, rw (show x = (monoid_hom.id W.fracr.quotient : _ → W.fracr.quotient) x, from rfl),
    rw ←map_id}, refine map_ext (h.to_monoid_hom.comp h.symm.to_monoid_hom)
      (λ (y : W), H1 (⟨_, H2 y⟩)) (monoid_hom.id Z) (λ y, y.2) _ x,
    apply h.right_inv_hom}}

def equiv_of_equiv (h : X ≃* Z) (H : h.to_monoid_hom.map Y = W) :
  Y.fracr.quotient ≃* W.fracr.quotient :=
monoid_equiv.mul_equiv_to_monoid_equiv (equiv_of_equiv_aux h H) $
λ x y, monoid_hom.map_mul _ x y

end frac

namespace submonoid

variables (Y)

def fracr_restrict : con X :=
{ r := λ a b, Y.fracr (a,1) (b,1),
  iseqv := ⟨λ x, Y.fracr.refl (x,1), λ _ _ h, Y.fracr.symm h,
            λ _ _ _ hm hn, Y.fracr.trans hm hn⟩,
  r_mul := λ _ _ _ _ h1 h2, by convert Y.fracr.mul h1 h2; simp}

end submonoid

namespace frac

variables {Y}

variables (f : X →* Z)

def char_pred' (f' : Y → units Z) (hf : ∀ y:Y, f y = f' y) :=
function.surjective (lift_hom' f f' hf) ∧ con.ker f = Y.fracr_restrict

def char_pred (H : ∀ y : Y, is_unit (f y)) :=
function.surjective (lift_hom f H) ∧ con.ker f = Y.fracr_restrict

variables {f}
lemma char_pred_of_equiv (H : ∀ y : Y, is_unit (f y)) (h : Y.fracr.quotient ≃* Z)
  (hf : lift_hom f H = h.to_monoid_hom) : char_pred f H :=
begin
  split,
  intro x,
    cases h.to_equiv.surjective x with p hp,
    exact ⟨p, by {rw ←hp, tidy}⟩,
  ext x y,
  split,
    intro h',
    rw con.ker_rel at h',
    cases (con.quotient.eq.1 (h.to_equiv.injective
          (show h.to_monoid_hom x = h.to_monoid_hom y, by
            {rwa [←hf, lift_hom_coe, lift_hom_coe]}))) with c hc,
    exact ⟨c, hc⟩,
  rintro ⟨w, hw⟩,
  rw [con.ker_rel, ←one_mul (f x), ←one_mul (f y)],
  cases H w with v hv,
  rw [←units.inv_mul v, ←hv, mul_assoc, mul_assoc, ←f.map_mul, ←f.map_mul],
  simp only [mul_one, submonoid.coe_one] at hw, rw hw,
end

variables (f)

noncomputable def equiv_of_char_pred'_aux (f' : Y → units Z) (hf : ∀ y:Y, f y = f' y)
  (Hp : char_pred' f f' hf) : Y.fracr.quotient ≃ Z :=
@equiv.of_bijective _ _ (lift_hom' f f' hf) $ and.intro
begin
  intros x y,
  apply con.quotient.induction_on₂' x y,
  intros w z h,
  change lift_hom' f f' hf (mk w.1 w.2) = lift_hom' f f' hf (mk z.1 z.2) at h,
  rw [lift_hom'_mk, lift_hom'_mk] at h,
  have : f (w.1*z.2) = f (z.1*w.2), by
    rw [f.map_mul, f.map_mul, hf z.2, hf w.2, ←mul_one (f w.1), ←units.inv_mul (f' w.2), ←mul_assoc,
        h, mul_assoc, mul_comm ↑(f' w.2), mul_assoc, ←mul_assoc _ ↑(f' z.2), units.inv_mul, one_mul],
  rw [←con.ker_rel, Hp.2] at this,
  cases this with c hc,
  rw frac.eq, exact ⟨c, by simp at hc; exact hc⟩,
end
Hp.1

noncomputable def equiv_of_char_pred' (f' : Y → units Z) (hf : ∀ y:Y, f y = f' y)
  (Hp : char_pred' f f' hf) : Y.fracr.quotient ≃* Z :=
monoid_equiv.mul_equiv_to_monoid_equiv
(equiv_of_char_pred'_aux f f' hf Hp) $
(lift_hom' f f' hf).map_mul


noncomputable def equiv_of_char_pred (H : ∀ y : Y, is_unit (f y)) (Hp : char_pred f H) :
Y.fracr.quotient ≃* Z :=
equiv_of_char_pred' f (λ y, classical.some $ H y)
  (λ y, by rw [← classical.some_spec (H y)]; refl) Hp

section away

/-- The localization of a commutative ring α at the submonoid generated by some x ∈ α. -/
@[reducible] def away (x : X) := (submonoid.powers x).fracr.quotient

/-- The inverse of an element x of a commutative ring α in the localization of α at the submonoid
    generated by x. -/
@[simp] def away.inv_self (x : X) : away x :=
mk 1 ⟨x, 1, pow_one x⟩

/-- Given a homomorphism f of commutative rings α and β, if f(x) is invertible in β for some x ∈ α,
    we can construct a natural map from the localization of α at the submonoid generated by x
    to β. -/
@[elab_with_expected_type]
noncomputable def away.lift {x : X} (hfx : is_unit (f x)) : away x →* Z :=
lift_hom' f (λ s, classical.some hfx ^ classical.some s.2) $ λ s,
by rw [units.coe_pow, ← classical.some_spec hfx,
       ← f.map_pow, classical.some_spec s.2]; refl

/-- Simplification lemmas for the natural ring homomorphism from the localization
    of a commutative ring α at the submonoid generated by some x ∈ α to a commutative ring β, given
    a ring homomorphism f such that f(x) is invertible in β. -/
@[simp] lemma away.lift_of {x : X} (hfx : is_unit (f x)) (a : X) :
  away.lift f hfx (of a) = f a := lift_hom'_of _ _

@[simp] lemma away.lift_coe {x : X} (hfx : is_unit (f x)) (a : X) :
  away.lift f hfx a = f a := lift_hom'_of _ _

/-- Given a ring homomorphism f between commutative rings α and β such that f(x) is invertible in β
    for some x ∈ α, the natural ring homomorphism we can construct from the localization of α to the
    submonoid generated by x to β makes the obvious diagram for α, β and the localization commute. -/
@[simp] lemma away.lift_comp_of {x : X} (hfx : is_unit (f x)) :
  (away.lift f hfx).comp (of_hom (submonoid.powers x)) = f := lift_hom'_comp_of_hom _

/-- The natural map from a commutative ring α localized at the submonoid generated by some
    x ∈ α to the localization at the submonoid generated by x*y for some y ∈ α. -/
noncomputable def away_to_away_right (x y : X) : away x →* away (x * y) :=
frac.away.lift (of_hom (submonoid.powers (x*y))) $
is_unit_of_mul_one x (y * away.inv_self (x * y)) $
by {rw [of_hom_apply, away.inv_self, coe_mul_mk, coe_mul_mk, mul_one, mk_apply,
        ←con.quotient.coe_one, frac.eq], use 1, simp}


end away
end frac

namespace localization
variables (α : Type*) [comm_ring α] (S : submonoid α)
def localization (S : submonoid α) := S.fracr.quotient

instance : has_coe (α × S) (localization α S) := @frac.frac_coe α _ S

/-- Instance defining addition in a commutative ring localized at a submonoid. -/
instance : has_add (localization α S) :=
⟨frac.lift₂ S S
(λ x y : α × S, (((x.2 : α) * y.1 + y.2 * x.1, x.2 * y.2) : localization α S))
$ λ ⟨r1, s1⟩ ⟨r2, s2⟩ ⟨r3, s3⟩ ⟨r4, s4⟩ ⟨v, hv⟩ ⟨w, hw⟩,
by { rw frac.eq, use (↑w*↑v),
     apply S.mul_mem w.2 v.2,
     calc
       ↑w * ↑v * ((↑s1 * r2 + ↑s2 * r1) * (↑s3 * ↑s4))
         = ↑w * (r2 * ↑s4) * ↑v * (↑s1 * ↑s3) + ↑w * (↑v * (r1 * ↑s3)) * (↑s2 * ↑s4) : by ring
     ... = ↑w * ↑v * ((↑s3 * r4 + ↑s4 * r3) * (↑s1 * ↑s2)) : by rw [hv, hw]; ring}⟩

--/-- Instance defining additive inverse in a commutative ring localized at a submonoid. -/
instance : has_neg (localization α S) :=
⟨frac.lift S (λ x : α × S, ((-x.1, x.2) : localization α S)) $
λ ⟨r1, s1⟩ ⟨r2, s2⟩ ⟨v, hv⟩,
by {rw frac.eq, use v, ring at hv ⊢, rw mul_neg_eq_neg_mul_symm, simp [hv]}⟩

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
  ..frac.comm_monoid};
{ intros,
  try {rcases a with ⟨r₁, s₁⟩},
  try {rcases b with ⟨r₂, s₂⟩},
  try {rcases c with ⟨r₃, s₃⟩},
  refine frac.fracr_of_eq _,
  norm_num,
  try {ring}}


def of_hom : α →+* localization α S :=
semiring_hom.mk' (frac.of_hom S) $
λ x y, show _ = ↑(1 * y + 1 * x, (1 : S) * 1), by norm_num; use 1

@[elab_as_eliminator]
protected theorem induction_on {C : localization α S → Prop} (x : localization α S)
  (ih : ∀ r s, C (frac.mk r s : localization α S)) : C x :=
by rcases x with ⟨r, s⟩; exact ih r s

section
variables {β : Type*} [comm_ring β] {T : submonoid β} (f : α →+* β)

@[elab_with_expected_type]
def lift_hom' (g : S → units β) (hg : ∀ s : S, f s = g s) : (localization α S) →+* β :=
semiring_hom.mk' (frac.lift_hom' f.to_monoid_hom g hg) $
sorry


#exit
/-
section at_prime

variables (P : ideal α) [hp : ideal.is_prime P]
include hp

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
    let ⟨t, hts, ht⟩ := quotient.exact hze in
    hts $ have htz : t = 0, by simpa using ht,
      suffices (0:α) ∈ P, by rwa htz,
      P.zero_mem)
  (begin
    rintro ⟨⟨r₁, s₁, hs₁⟩⟩ ⟨⟨r₂, s₂, hs₂⟩⟩ hx hy hu,
    rcases is_unit_iff_exists_inv.1 hu with ⟨⟨⟨r₃, s₃, hs₃⟩⟩, hz⟩,
    rcases quotient.exact hz with ⟨t, hts, ht⟩,
    simp at ht,
    have : ∀ {r s hs}, (⟦⟨r, s, hs⟩⟧ : at_prime P) ∈ nonunits (at_prime P) → r ∈ P,
    { haveI := classical.dec,
      exact λ r s hs, not_imp_comm.1 (λ nr,
        is_unit_iff_exists_inv.2 ⟨⟦⟨s, r, nr⟩⟧,
          quotient.sound $ r_of_eq $ by simp [mul_comm]⟩) },
    have hr₃ := (hp.mem_or_mem_of_mul_eq_zero ht).resolve_right hts,
    have := (ideal.add_mem_iff_left _ _).1 hr₃,
    { exact not_or (mt hp.mem_or_mem (not_or hs₁ hs₂)) hs₃ (hp.mem_or_mem this) },
    { exact P.neg_mem (P.mul_mem_right
        (P.add_mem (P.mul_mem_left (this hy)) (P.mul_mem_left (this hx)))) }
  end)

end at_prime

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
variables {β : Type u} [integral_domain β] [decidable_eq β]

/-- For a non-zero element x of an integral domain β, ∀ y ∈ β, y*x = 0 implies y is zero. -/
lemma eq_zero_of_ne_zero_of_mul_eq_zero {x y : β} :
  x ≠ 0 → y * x = 0 → y = 0 :=
λ hnx hxy, or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hnx

/-- In an integral domain β, x ∈ β is a non zero divisor iff x is nonzero. -/
lemma mem_non_zero_divisors_iff_ne_zero {x : β} :
  x ∈ non_zero_divisors β ↔ x ≠ 0 :=
⟨λ hm hz, zero_ne_one (hm 1 $ by rw [hz, one_mul]).symm,
 λ hnx z, eq_zero_of_ne_zero_of_mul_eq_zero hnx⟩

variable (β)

/-- Auxilliary function for the definition of inverses in the field of fractions of an integral
    domain.-/
def inv_aux (x : β × (non_zero_divisors β)) : fraction_ring β :=
if h : x.1 = 0 then 0 else ⟦⟨x.2, x.1, mem_non_zero_divisors_iff_ne_zero.mpr h⟩⟧

/-- An instance defining inverses in the field of fractions of an integral domain. -/
instance : has_inv (fraction_ring β) :=
⟨quotient.lift (inv_aux β) $
  λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩ ⟨t, hts, ht⟩,
  begin
    have hrs : s₁ * r₂ = 0 + s₂ * r₁,
      from sub_eq_iff_eq_add.1 (hts _ ht),
    by_cases hr₁ : r₁ = 0;
    by_cases hr₂ : r₂ = 0;
    simp [hr₁, hr₂] at hrs;
    simp only [inv_aux, hr₁, hr₂, dif_pos, dif_neg, not_false_iff, subtype.coe_mk, quotient.eq],
    { exfalso,
      exact mem_non_zero_divisors_iff_ne_zero.mp hs₁ hrs },
    { exfalso,
      exact mem_non_zero_divisors_iff_ne_zero.mp hs₂ hrs },
    { apply r_of_eq,
      simpa [mul_comm] using hrs.symm }
  end⟩

/-- The definition of the inverse of the equivalence class of (r, s) in the field of fractions of
    an integral domain β for some r, s≠0 ∈ β. -/
lemma mk_inv {r s} :
  (mk r s : fraction_ring β)⁻¹ =
  if h : r = 0 then 0 else ⟦⟨s, r, mem_non_zero_divisors_iff_ne_zero.mpr h⟩⟧ := rfl

/-- The definition of the inverse of the equivalence class of x in the field of fractions of
    an integral domain β for some x ∈ β × β/{0}. -/
lemma mk_inv' :
  ∀ (x : β × (non_zero_divisors β)), (⟦x⟧⁻¹ : fraction_ring β) =
  if h : x.1 = 0 then 0 else ⟦⟨x.2.val, x.1, mem_non_zero_divisors_iff_ne_zero.mpr h⟩⟧
| ⟨r,s,hs⟩ := rfl

/-- Equality is decidable in the field of fractions of an integral domain with decidable equality. -/
instance : decidable_eq (fraction_ring β) :=
@quotient.decidable_eq (β × non_zero_divisors β) (localization.setoid β (non_zero_divisors β)) $
λ ⟨r₁, s₁, hs₁⟩ ⟨r₂, s₂, hs₂⟩, show decidable (∃ t ∈ non_zero_divisors β, (s₁ * r₂ - s₂ * r₁) * t = 0),
from decidable_of_iff (s₁ * r₂ - s₂ * r₁ = 0)
⟨λ H, ⟨1, λ y, (mul_one y).symm ▸ id, H.symm ▸ zero_mul _⟩,
λ ⟨t, ht1, ht2⟩, or.resolve_right (mul_eq_zero.1 ht2) $ λ ht,
  one_ne_zero (ht1 1 ((one_mul t).symm ▸ ht))⟩

/-- The field of fractions of an integral domain with decidable equality is a field with
    decidable equality. -/
instance : discrete_field (fraction_ring β) :=
by refine
{ inv            := has_inv.inv,
  zero_ne_one    := λ hzo,
    let ⟨t, hts, ht⟩ := quotient.exact hzo in
    zero_ne_one (by simpa using hts _ ht : 0 = 1),
  mul_inv_cancel := quotient.ind _,
  inv_mul_cancel := quotient.ind _,
  has_decidable_eq := fraction_ring.decidable_eq β,
  inv_zero := dif_pos rfl,
  .. localization.comm_ring };
{ intros x hnx,
  rcases x with ⟨x, z, hz⟩,
  have : x ≠ 0,
    from assume hx, hnx (quotient.sound $ r_of_eq $ by simp [hx]),
  simp only [has_inv.inv, inv_aux, quotient.lift_beta, dif_neg this],
  exact (quotient.sound $ r_of_eq $ by simp [mul_comm]) }

/-- The equivalence class of (r, s) in the field of fractions of an integral domain β for some
    r, s≠0 ∈ β equals r/s. -/
@[simp] lemma mk_eq_div {r s} : (mk r s : fraction_ring β) = (r / s : fraction_ring β) :=
show _ = _ * dite (s.1 = 0) _ _, by rw [dif_neg (mem_non_zero_divisors_iff_ne_zero.mp s.2)];
exact localization.mk_eq_mul_mk_one _ _

variables {β}

/-- The equivalence class of x in the field of fractions of an integral domain β for some
    x ∈ β × β/{0} equals the first component of x divided by the second component. -/
@[simp] lemma mk_eq_div' (x : β × (non_zero_divisors β)) :
  (⟦x⟧ : fraction_ring β) = ((x.1) / ((x.2).val) : fraction_ring β) :=
by erw ← mk_eq_div; cases x; refl

/-- If an element x of an integral domain β is zero in the field of fractions of β, x is zero in β. -/
lemma eq_zero_of (x : β) (h : (of x : fraction_ring β) = 0) : x = 0 :=
begin
  rcases quotient.exact h with ⟨t, ht, ht'⟩,
  simpa [mem_non_zero_divisors_iff_ne_zero.mp ht] using ht'
end

/-- The natural map from an integral domain to its field of fractions if injective. -/
lemma of.injective : function.injective (of : β → fraction_ring β) :=
(is_add_group_hom.injective_iff _).mpr eq_zero_of

section map
open function is_ring_hom
variables {A : Type u} [integral_domain A] [decidable_eq A]
variables {B : Type v} [integral_domain B] [decidable_eq B]
variables (f : A → B) [is_ring_hom f]

/-- Given an injective homomorphism of integral domains, we can construct a natural map of
    fields of fractions. -/
def map (hf : injective f) : fraction_ring A → fraction_ring B :=
localization.map f $ λ s h,
  by rw [mem_non_zero_divisors_iff_ne_zero, ← map_zero f, ne.def, hf.eq_iff];
    exact mem_non_zero_divisors_iff_ne_zero.1 h

/-- Given an injective homomorphism of integral domains, the natural map we can construct of the
    respective fields of fractions makes the obvious diagram commute. -/
@[simp] lemma map_of (hf : injective f) (a : A) : map f hf (of a) = of (f a) :=
localization.map_of _ _ _

/-- Given an injective homomorphism of integral domains, the natural map we can construct of the
    respective fields of fractions makes the obvious diagram commute. -/
@[simp] lemma map_coe (hf : injective f) (a : A) : map f hf a = f a :=
localization.map_coe _ _ _

/-- Given an injective homomorphism of integral domains, the natural map we can construct of the
    respective fields of fractions makes the obvious diagram commute. -/
@[simp] lemma map_comp_of (hf : injective f) :
  map f hf ∘ (of : A → fraction_ring A) = (of : B → fraction_ring B) ∘ f :=
localization.map_comp_of _ _

/-- Given an injective homomorphism of integral domains, the natural map we can construct of the
    respective fields of fractions is a field homomorphism. -/
instance map.is_field_hom (hf : injective f) : is_field_hom (map f hf) :=
localization.map.is_ring_hom _ _

/-- Given an isomorphism of integral domains, we can construct a natural isomorphism of the
    respective fields of fractions. -/
def equiv_of_equiv (h : A ≃r B) : fraction_ring A ≃r fraction_ring B :=
localization.equiv_of_equiv h
begin
  ext b,
 rw [submonoid.mem_coe, equiv.image_eq_preimage, set.preimage, set.mem_set_of_eq,
    mem_non_zero_divisors_iff_ne_zero, submonoid.mem_coe,
    mem_non_zero_divisors_iff_ne_zero, ne.def],
  exact ⟨mt (λ h, h.symm ▸ is_ring_hom.map_zero _),
    mt ((is_add_group_hom.injective_iff _).1 h.to_equiv.symm.injective _)⟩
end

end map

end fraction_ring

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

end ideals

end localization
-/
