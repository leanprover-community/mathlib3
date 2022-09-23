import category_theory.category.basic
import category_theory.functor.basic
import category_theory.groupoid
import logic.relation
import tactic.nth_rewrite

open set classical function relation
local attribute [instance] prop_decidable

namespace category_theory
namespace groupoid
namespace free

universes u v u' v'

variable {V : Type u}
variable [quiver.{v+1} V]

inductive word : V → V → Sort*
| nil {c : V} : word c c
| cons_p {c d e : V} (p : c ⟶ d) (w : word d e) : word c e
| cons_n {c d e : V} (p : d ⟶ c) (w : word d e) : word c e

def word.length : Π {c d : V}, word c d → ℕ
| _ _ word.nil := 0
| _ _ (word.cons_p _ t) := t.length.succ
| _ _ (word.cons_n _ t) := t.length.succ

@[pattern]
def letter_p {c d : V} (p : c ⟶ d) : word c d := (word.cons_p p word.nil)
@[pattern]
def letter_n {c d : V} (p : c ⟶ d) : word d c := (word.cons_n p word.nil)

def word.append  : Π {c d e : V}, word c d → word d e → word c e
| _ _ _ (word.nil) w := w
| _ _ _ (word.cons_p p u) w := word.cons_p p (u.append w)
| _ _ _ (word.cons_n p u) w := word.cons_n p (u.append w)

@[simp] lemma word.nil_append {c d : V} {p : word c d} : word.nil.append p = p := rfl

@[simp] lemma word.append_nil {c d : V} {p : word c d} : p.append word.nil = p := by
{ induction p, refl, all_goals { dsimp only [word.append], rw p_ih, }, }

@[simp] lemma word.cons_p_append {c d e b : V} (f : c ⟶ d) (u : word d e) (w : word e b) :
  (word.cons_p f u).append w = word.cons_p f (u.append w) := rfl

@[simp] lemma word.cons_n_append {c d e b : V} (f : d ⟶ c) (u : word d e) (w : word e b) :
  (word.cons_n f u).append w = word.cons_n f (u.append w) := rfl

@[simp] lemma word.append_assoc {c d e f : V} {p : word c d} {q : word d e} {r : word e f} :
  (p.append q).append r = p.append (q.append r) := by
{ induction p, refl, all_goals { dsimp only [word.append], rw p_ih, }, }

infix ` ≫* `:100 := word.append

def word.reverse : Π {c d : V}, word c d → word d c
| _ _ (word.nil) := word.nil
| _ _ (word.cons_p p u) := (u.reverse.append (letter_n p))
| _ _ (word.cons_n p u) := (u.reverse.append (letter_p p))

@[simp] lemma word.reverse_nil (c : V) : (word.nil : word c c).reverse = word.nil := rfl

@[simp] lemma word.reverse_letter_p {c d : V} (p : c ⟶ d) : (letter_p p).reverse = letter_n p := by
{ dsimp only [letter_p, letter_n, word.reverse], simp, }

@[simp] lemma word.reverse_letter_n {c d : V} (p : d ⟶ c) : (letter_n p).reverse = letter_p p := by
{ dsimp only [letter_p, letter_n, word.reverse], simp, }

@[simp] lemma word.reverse_cons_p {c d e : V} (p : c ⟶ d) (w : word d e) :
  (word.cons_p p w).reverse =  w.reverse.append (letter_n p) := rfl

@[simp] lemma word.reverse_cons_n {c d e : V} (p : d ⟶ c) (w : word d e) :
  (word.cons_n p w).reverse =  w.reverse.append (letter_p p) := rfl

@[simp] lemma word.reverse_append {c d e : V} (u : word c d) (w : word d e) :
  (u.append w).reverse =  w.reverse.append (u.reverse) :=
begin
  induction u,
  { simp only [word.nil_append, word.reverse_nil, word.append_nil], },
  { simp only [word.cons_p_append, u_ih, word.reverse_cons_p, word.append_assoc], },
  { simp only [word.cons_n_append, u_ih, word.reverse_cons_n, word.append_assoc], },
end

@[simp] lemma word.reverse_reverse  {c d : V} (w : word c d) : w.reverse.reverse = w :=
begin
  induction w,
  { dsimp only [word.reverse], refl, },
  { simp only [w_ih, word.reverse_cons_p, word.reverse_append, word.reverse_letter_n], refl, },
  { simp only [w_ih, word.reverse_cons_n, word.reverse_append, word.reverse_letter_p], refl, },
end

def red_step {c  d : V} (p : word c d) (q : word c d) : Prop :=
  (∃ (a b : V) (q₀ : word c a) (q₁ : word a d) (f : a ⟶ b),
     p = q₀ ≫*  (letter_p f) ≫* (letter_n f) ≫* q₁ ∧ q = q₀ ≫* q₁)
∨ (∃ (a b : V) (q₀ : word c a) (q₁ : word a d) (f : b ⟶ a),
     p = q₀ ≫* (letter_n f) ≫* (letter_p f) ≫* q₁ ∧ q = q₀ ≫* q₁)

@[simp]
lemma red_step.reverse {c d : V} (p₀ p₁ : word c d) : red_step p₀.reverse p₁.reverse ↔ red_step p₀ p₁ :=
begin
  suffices : ∀ c d (p₀ p₁ : word c d),  red_step p₀ p₁ → red_step p₀.reverse p₁.reverse,
  { split, rotate, exact this c d p₀ p₁,
    rintro h,
    rw  [←word.reverse_reverse p₀, ←word.reverse_reverse p₁],
    exact this d c _ _ h, },
  rintro c d p₀ p₁ (⟨u,v,r₀,r₁,f,rfl,rfl⟩|⟨u,v,r₀,r₁,f,rfl,rfl⟩),
  { left, use [u,v,r₁.reverse,r₀.reverse,f], simp, },
  { right, use [u,v,r₁.reverse,r₀.reverse,f], simp, },
end

@[simp]
lemma red_step.append_left_congr  {c d e : V} {p₀ p₁ : word c d} {q : word d e} :
  red_step p₀ p₁ → red_step (p₀ ≫* q) (p₁ ≫* q) :=
begin
  rintro (⟨u,v,r₀,r₁,f,rfl,rfl⟩|⟨u,v,r₀,r₁,f,rfl,rfl⟩),
  { left, use [u,v,r₀,r₁.append q,f],simp, },
  { right, use [u,v,r₀,r₁.append q,f],simp, },
end

@[simp]
lemma red_step.append_right_congr  {c d e : V} {p : word c d} {q₀ q₁ : word d e} :
  red_step q₀ q₁ → red_step (p ≫* q₀) (p ≫* q₁) :=
begin
  rintro (⟨u,v,r₀,r₁,f,rfl,rfl⟩|⟨u,v,r₀,r₁,f,rfl,rfl⟩),
  { left, use [u,v,p.append r₀,r₁,f],simp, },
  { right, use [u,v,p.append r₀,r₁,f],simp, },
end

def free_groupoid (V : Type u) := V
instance free_groupoid_quiver : quiver (free_groupoid V) :=
{ hom := λ c d, quot (@red_step V _ c d) }

def quot_comp { c d e : free_groupoid V} (p : c ⟶ d) (q : d ⟶ e) : c ⟶ e :=
quot.lift_on
  p
  (λ pp, quot.lift_on q
    (λ qq, quot.mk _ (pp ≫* qq))
    (λ q₀ q₁ redq, quot.sound $ red_step.append_right_congr redq))
  (λ p₀ p₁ redp, quot.induction_on q $ λ qq, quot.sound $ red_step.append_left_congr redp)

def quot_id (c : free_groupoid V)  := quot.mk (@red_step V _ c c) (word.nil)

instance free_groupoid_category_struct : category_struct (free_groupoid V)  :=
{ to_quiver := free.free_groupoid_quiver
, id := quot_id
, comp := λ a b c p q, quot_comp p q }

lemma id_quot_comp { c d : free_groupoid V} (p : c ⟶ d) : quot_comp (𝟙 c) p = p :=
quot.induction_on p $ λ pp, quot.eqv_gen_sound $ eqv_gen.refl pp

lemma quot_comp_id { c d : free_groupoid V} (p : c ⟶ d) : quot_comp p (𝟙 d) = p :=
quot.induction_on p $ λ pp, quot.eqv_gen_sound $  by {simp, exact eqv_gen.refl pp}

lemma quot_comp_assoc { c d e f : free_groupoid V}
  (p : c ⟶ d) (q : d ⟶ e)  (r : e ⟶ f) :
  quot_comp (quot_comp p q) r = quot_comp p (quot_comp q r) :=
quot.induction_on₃ p q r $ λ pp qq rr, by {dsimp [quot_comp], simp,}

instance free_groupoid_category : category (free_groupoid V)  :=
{ to_category_struct := free.free_groupoid_category_struct
  , id_comp' := λ a b p, id_quot_comp p
  , comp_id' := λ a b p, quot_comp_id p
  , assoc' := λ a b c d p q r, quot_comp_assoc p q r }

def quot_inv {c d : free_groupoid V} (p : c ⟶ d) : d  ⟶ c :=
quot.lift_on p
  (λ pp, quot.mk (@red_step V (_inst_1) d c) pp.reverse)
  (λ p₀ p₁ redp , quot.sound $ by {simp only [red_step.reverse], exact redp })

lemma quot_inv_inv {c d : free_groupoid V} (p : c ⟶ d) : (quot_inv $ quot_inv p) = p :=
begin
  apply quot.induction_on p,
  rintro pp,
  apply quot.eqv_gen_sound,
  simp only [word.reverse_reverse],
  exact eqv_gen.refl _,
end

lemma quot_comp_inv {c d : free_groupoid V} (p : c ⟶ d)  : (quot_inv p) ≫ p = 𝟙 d :=
begin
  apply quot.induction_on p,
  rintro pp,
  dsimp only [quot_comp, quot_inv],
  simp only [quot.lift_on_mk],
  apply quot.eqv_gen_sound,
  induction pp with _ c d e f w ih c d e f w ih,
  { exact eqv_gen.refl _ },
  { refine eqv_gen.trans _ (w.reverse ≫* w) _ _ _,
    { apply eqv_gen.rel,
      right,
      use [d,c,w.reverse,w,f],
      unfold letter_p,
      simp only [word.reverse_cons_p, word.append_assoc, word.cons_p_append, word.nil_append,
                 eq_self_iff_true, and_self], },
    { apply ih (quot.mk _ w) }, },
  { refine eqv_gen.trans _ (w.reverse ≫* w) _ _ _,
    { apply eqv_gen.rel,
      left,
      use [d,c,w.reverse,w,f],
      unfold letter_n,
      simp only [word.append_assoc, word.nil_append, eq_self_iff_true, word.reverse_cons_n,
                 and_true, word.cons_n_append], },
    { apply ih (quot.mk _ w) }, },

end

lemma quot_inv_comp {c d : free_groupoid V} (p : c ⟶ d)  : quot_comp p (quot_inv p) = 𝟙 c :=
begin
  nth_rewrite 0 ←quot_inv_inv p,
  apply quot_comp_inv,
end

/-- The free groupoid instance on `free_groupoid V`. -/
instance : groupoid (free_groupoid V) :=
{ to_category := free.free_groupoid_category
, inv := λ a b, quot_inv
, inv_comp' := λ a b, quot_comp_inv
, comp_inv' := λ a b, quot_inv_comp }

@[simp]
lemma quot_cons_p {c d e : V} (f : c ⟶ d) (w : word d e) :
  (quot.mk (@red_step V _ c e) (word.cons_p f w)) =
  quot_comp (quot.mk (@red_step V _ c d) (letter_p f )) (quot.mk (@red_step V _ d e) w) := rfl

@[simp]
lemma quot_cons_n {c d e : V} (f : d ⟶ c) (w : word d e) :
  (quot.mk (@red_step V _ c e) (word.cons_n f w)) =
  quot_comp (quot.mk (@red_step V _ c d) (letter_n f )) (quot.mk (@red_step V _ d e) w) := rfl

def ι : prefunctor V (free_groupoid V) :=
{ obj := λ x, x
, map := λ x y p, quot.mk _ (letter_p p)}

def lift_word {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : Π {x y : V} (w : word x y), (φ.obj x) ⟶ (φ.obj y)
| x _ (word.nil) := 𝟙 (φ.obj x)
| x z (@word.cons_p _ _ _ y _ p w) := (φ.map p) ≫ (lift_word w)
| x z (@word.cons_n _ _ _ y _ p w) := (G'.inv $ φ.map p) ≫ (lift_word w)

@[simp]
lemma lift_word_nil {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : Π (x : V),  (lift_word φ (word.nil : word x x)) = 𝟙 (φ.obj x) :=
by { rintro x, dsimp only [lift_word], refl, }

@[simp]
lemma lift_word_cons_p {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') {x y z : V} (f : x ⟶ y) (w : word y z) :
  (lift_word φ $ word.cons_p f w) = (φ.map f) ≫ (lift_word φ w) := rfl

@[simp]
lemma lift_word_cons_n {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') {x y z : V} (f : y ⟶ x) (w : word y z) :
  (lift_word φ $ word.cons_n f w) = (inv $ φ.map f) ≫ (lift_word φ w) := rfl


@[simp]
lemma lift_word_letter_p {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') (x y : V) (u : x ⟶ y) :
  (lift_word φ ( letter_p u : word x y)) = φ.map u :=
by { dsimp [lift_word, letter_p, lift_word_nil], simp, }

@[simp]
lemma lift_word_letter_n {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') (x y : V) (u : y ⟶ x) :
  (lift_word φ (letter_n u : word x y)) = G'.inv (φ.map u) :=
by { dsimp [lift_word, letter_n, lift_word_nil], simp, }


@[simp]
lemma lift_word_append {V' : Type u'} [G' : groupoid V'] (φ : prefunctor V V')
  {x y z : V} (u : word x y) (w : word y z) :
  lift_word φ (u ≫* w) = (lift_word φ u) ≫ (lift_word φ w) :=
begin
  induction u,
  { simp only [word.nil_append, lift_word_nil, category.id_comp], },
  { simp only [u_ih, word.cons_p_append, lift_word_cons_p, category.assoc], },
  { simp only [u_ih, word.cons_n_append, lift_word_cons_n, category.assoc], },
end

--mathlib
@[simp] lemma _root_.category_theory.groupoid.inv_id {V : Type*} [G : groupoid V] (v : V) : G.inv (𝟙 v) = 𝟙 v := sorry
@[simp] lemma _root_.category_theory.groupoid.inv_comp'' {V : Type*} [G : groupoid V]
  {u v w : V} (f : u ⟶ v) (g : v ⟶ w) : G.inv (f ≫ g) = (G.inv g) ≫ (G.inv f) := sorry
@[simp] lemma _root_.category_theory.groupoid.inv_inv {V : Type*} [G : groupoid V] (u v : V) (f : u ⟶ v) : G.inv (G.inv f) = f :=
  calc G.inv (G.inv f) = (G.inv (G.inv f)) ≫ (𝟙 v) : by rw category.comp_id
                  ... = (G.inv (G.inv f)) ≫ (G.inv f ≫ f) : by rw ←groupoid.inv_comp
                  ... = (G.inv (G.inv f) ≫ G.inv f) ≫ f : by rw ←category.assoc
                  ... = (𝟙 u) ≫ f : by rw groupoid.inv_comp
                  ... = f : by rw category.id_comp



@[simp]
lemma lift_word_reverse {V' : Type u'} [G' : groupoid V'] (φ : prefunctor V V')
  {x y : V} (u : word x y) : lift_word φ (u.reverse) = G'.inv (lift_word φ u) :=
begin
  induction u,
  { simp only [word.reverse_nil, lift_word_nil, inv_id], },
  { simp only [u_ih, word.reverse_cons_p, lift_word_append, lift_word_letter_n,
               lift_word_cons_p, inv_comp''], },
  { simp only [u_ih, word.reverse_cons_n, lift_word_append, lift_word_letter_p,
               lift_word_cons_n, inv_comp'', inv_inv], },
end

lemma lift_word_congr {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') {x y : V} (w₀ w₁ : word x y) (redw : red_step w₀ w₁) :
  lift_word φ w₀ = lift_word φ w₁ :=
begin
  dsimp [red_step] at redw,
  rcases redw with (⟨u,v,r₀,r₁,p,rfl,rfl⟩|⟨u,v,r₀,r₁,p,rfl,rfl⟩),
  { rw [←word.reverse_letter_p p],
    simp only [word.append_assoc, lift_word_append, lift_word_reverse],
    nth_rewrite_lhs 1 ←category.assoc,
    rw groupoid.comp_inv, simp only [category.id_comp], },
  { rw [←word.reverse_letter_n p],
    simp only [word.append_assoc, lift_word_append, lift_word_reverse],
    nth_rewrite_lhs 1 ←category.assoc,
    rw groupoid.comp_inv, simp only [category.id_comp], },
end

def lift {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : free_groupoid V ⥤ V' :=
{ obj := φ.obj
, map := λ x y, quot.lift (λ p, lift_word φ p)
                          (λ p₀ p₁ (redp : red_step p₀ p₁), lift_word_congr φ p₀ p₁ redp)
, map_id' := λ x, by { dsimp only [lift_word,category_struct.id], refl,  }
, map_comp' := λ x y z f g, by
  { refine quot.induction_on₂ f g _,
    rintro ff gg,
    dsimp only [lift_word,category_struct.comp,quot_comp], simp only [lift_word_append], }, }

--mathlib (stolen from functor.ext)
lemma _root_.category_theory.functor.ext' {C D : Type*} [category C] [category D] {F G : C ⥤ D}
  (h_obj : ∀ X, F.obj X = G.obj X)
  (h_map : ∀ (X Y : C) (f : X ⟶ Y), F.map f = by {rw [h_obj X, h_obj Y], exact G.map f}) :
  F = G :=
begin
  cases F with F_obj _ _ _, cases G with G_obj _ _ _,
  obtain rfl : F_obj = G_obj, by { ext X, apply h_obj },
  congr,
  funext X Y f,
  simpa using h_map X Y f
end

--mathlib (stolen from functor.ext),
@[ext] lemma ext {V : Type u} [Q : quiver.{v+1} V] {V' : Type u'} [Q' : quiver.{v'+1} V']
  {F G : prefunctor V V'}
  (h_obj : ∀ X, F.obj X = G.obj X)
  (h_map : ∀ (X Y : V) (f : X ⟶ Y), F.map f = by {rw [h_obj X, h_obj Y], exact G.map f}) : F = G :=
begin
  cases F with F_obj _, cases G with G_obj _,
  obtain rfl : F_obj = G_obj, by { ext X, apply h_obj },
  congr,
  funext X Y f,
  simpa using h_map X Y f,
end

lemma lift_spec {V : Type u} [Q : quiver.{v+1} V] {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : ι.comp (lift φ).to_prefunctor = φ :=
begin
  ext, rotate,
  rcases φ with ⟨φo,φm⟩,
  { rintro x, dsimp only, refl, },
  { subst_vars, apply lift_word_letter_p, },
end

-- mathlib?
@[simp]
lemma _root_.category_theory.functor.groupoid_map_inv  {C D : Type*} [G : groupoid C] [H : groupoid D] (φ : C ⥤ D)
  {c d : C} (f : c ⟶ d) :
  φ.map (G.inv f) = H.inv (φ.map f) :=
calc φ.map (G.inv f) = (φ.map $ G.inv f) ≫ (𝟙 $ φ.obj c) : by rw [category.comp_id]
                 ... = (φ.map $ G.inv f) ≫ ((φ.map f) ≫ (H.inv $ φ.map f)) : by rw [comp_inv]
                 ... = ((φ.map $ G.inv f) ≫ (φ.map f)) ≫ (H.inv $ φ.map f) : by rw [category.assoc]
                 ... = (φ.map $ G.inv f ≫ f) ≫ (H.inv $ φ.map f) : by rw [functor.map_comp']
                 ... = (H.inv $ φ.map f) : by rw [inv_comp,functor.map_id,category.id_comp]


lemma lift_unique (V' : Type u') [G' : groupoid V']
  (φ : prefunctor V V') (Φ : free_groupoid V ⥤ V') : (ι.comp Φ.to_prefunctor) = φ → Φ = (lift φ) :=
begin
  rintro h, subst h,
  fapply functor.ext',
  { rintro x, dsimp [lift,ι], refl, },
  { rintro X Y f,
    simp only [eq_mpr_eq_cast, cast_eq],
    refine quot.induction_on f _,
    refine word.rec _ _ _,
    { rintro x, convert functor.map_id Φ x, },
    { rintro x y z p w IHw,
      rw [quot_cons_p],
      have : Φ.map (quot_comp (quot.mk red_step  $ letter_p p ) (quot.mk red_step w)) = Φ.map ((quot.mk red_step  $ letter_p p ) ≫  (quot.mk red_step w)), by refl,
      simp only [this, functor.map_comp, IHw],
      congr, },
    { rintro x y z p w IHw,
      rw [quot_cons_n],
      have : Φ.map (quot_comp (quot.mk red_step  $ letter_n p ) (quot.mk red_step w)) = Φ.map ((quot.mk red_step $ letter_n p ) ≫  (quot.mk red_step w)), by refl,
      simp only [this, functor.map_comp, IHw, functor.map_comp],
      apply congr_arg2,
      { dsimp [lift,ι], rw ←word.reverse_letter_p,
        convert functor.groupoid_map_inv Φ (quot.mk red_step  $ letter_p p ) , },
      { refl, }, }, },

end

end free
end groupoid
end category_theory
