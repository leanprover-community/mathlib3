import data.qpf.univariate.basic
import control.bifunctor

universes u
variables {F : Type u → Type u} [functor F]

namespace qpf

section box
variables (F)

/-- apply a functor to a set of values. taken from
 [Basil Fürer, Andreas Lochbihler, Joshua Schneider, Dmitriy Traytel *Quotients of Bounded Natural Functors*][fuerer-lochbihler-schneider-traytel2020]
henceforth referred to as the QBNF paper
 -/
def box {α} (A : set α) : set (F α) :=
{ x | ∀ β (f g : α → β), (∀ a ∈ A, f a = g a) → f <$> x = g <$> x }

variables {F}

/--
Alternate notion of support set based on `box`.
Taken from the QBNF paper
-/
def supp' {α} (x : F α) : set α :=
⋂ A ∈ { A : set α | x ∈ box F A}, A

/--
Alternate notion of predicate lifting based on `box`.
Taken from the QBNF paper
-/
def liftp' {α} (x : F α) (p : α → Prop) : Prop :=
∀ a ∈ supp' x, p a

end box

end qpf


namespace ex

/-- polynomial functor isomorph to `α × _` for some `α` -/
def prod.pfunctor (α : Type) : pfunctor :=
⟨ α, λ _, unit ⟩

instance {α} : qpf (prod α) :=
{ P := prod.pfunctor α,
  abs := λ β ⟨a,f⟩, (a, f ()),
  repr := λ β ⟨x,y⟩, ⟨x, λ _, y⟩,
  abs_repr := λ β ⟨x,y⟩, rfl,
  abs_map := λ β γ f ⟨a,g⟩, rfl }

/-- example relation for products -/
def foo.R (α : Type) (x y : bool × α) : Prop :=
x.1 = y.1 ∧ (x.1 → x.2 = y.2)

lemma equivalence_foo.R (α) : equivalence (foo.R α) :=
begin
  refine ⟨_,_,_⟩,
  { intro, exact ⟨rfl,λ _, rfl⟩ },
  { intros x y h, refine ⟨h.1.symm, λ _, (h.2 _).symm⟩,
    rwa h.1 },
  { rintros x y z ⟨ha,ha'⟩ ⟨hb,hb'⟩,
    refine ⟨ha.trans hb, λ hh, _⟩,
    refine (ha' hh).trans (hb' _),
    rwa ← ha }
end

/-- example of a qpf -/
def foo (α : Type) :=
quot $ foo.R α

instance {α} [inhabited α] : inhabited (foo α) := ⟨ quot.mk _ (default _) ⟩

/-- functor operation of `foo` -/
def foo.map {α β} (f : α → β) (x : foo α) : foo β :=
quot.lift_on x (λ x : bool × α, quot.mk (foo.R β) $ f <$> x)
  (λ ⟨a₀,a₁⟩ ⟨b₀,b₁⟩ h, quot.sound ⟨h.1,λ h', show f a₁ = f b₁, from congr_arg f (h.2 h')⟩)

instance : functor foo :=
{ map := @foo.map }

@[simp]
lemma foo.map_mk {α β : Type} (f : α → β) (x : bool × α) :
  (f <$> quot.mk _ x : foo β) = quot.mk _ (f <$> x) :=
by simp [(<$>),foo.map]

noncomputable instance qpf.foo : qpf foo :=
@qpf.quotient_qpf (prod bool) _ ex.prod.qpf foo _ (λ α, quot.mk _) (λ α, quot.out)
  (by simp)
  (by intros; simp)

/-- constructor for `foo` -/
def foo.mk {α} (b : bool) (x : α) : foo α := quot.mk _ (b, x)

@[simp]
lemma foo.map_mk' {α β : Type} (f : α → β) (b : bool) (x : α) :
  f <$> foo.mk b x = foo.mk b (f x) :=
by simp only [foo.mk, foo.map_mk]; refl

@[simp]
lemma foo.map_tt {α : Type} (x y : α) :
  foo.mk tt x = foo.mk tt y ↔ x = y :=
by simp [foo.mk]; split; intro h; [replace h := quot.exact _ h, rw h];
   rw (equivalence_foo.R _).eqv_gen_iff at h;
   exact h.2 rfl

/-- consequence of original definition of `supp`. If there exists more than
one value of type `α`, then the support of `foo.mk ff x` is empty -/
lemma supp_mk_ff₀ {α} (x y : α) (h : ¬ x = y) : functor.supp (foo.mk ff x) = {} :=
begin
  dsimp [functor.supp], ext z, simp, -- split; intro h,
  classical, by_cases x = z,
  { use (λ a, ¬ z = a), subst z,
    dsimp [functor.liftp],
    simp, refine ⟨foo.mk ff ⟨y,h⟩,_⟩,
    simp, apply quot.sound, simp [foo.R] },
  { use (λ a, x = a),
    dsimp [functor.liftp],
    simp [h], use foo.mk ff ⟨x,rfl⟩,
    simp }
end

/-- consequence of original definition of `supp`. If there exists only
one value of type `α`, then the support of `foo.mk ff x` contains that value -/
lemma supp_mk_ff₁ {α} (x : α) (h : ∀ z, x = z) : functor.supp (foo.mk ff x) = {x} :=
begin
  dsimp [functor.supp], ext y, simp, split; intro h',
  { apply @h' (= x), dsimp [functor.liftp],
    use foo.mk ff ⟨x,rfl⟩, refl },
  { introv hp, simp [functor.liftp] at hp,
    rcases hp with ⟨⟨z,z',hz⟩,hp⟩,
    simp at hp, convert hz,
    rw [h'], apply h },
end

/--
Such a QPF is not uniform
-/
lemma foo_not_uniform : ¬ @qpf.is_uniform foo _ qpf.foo :=
begin
  simp only [qpf.is_uniform, foo, qpf.foo, set.image_univ, not_forall, not_imp],
  existsi [bool,ff,ff,λ a : unit, tt,λ a : unit, ff], split,
  { apply quot.sound, simp [foo.R, qpf.abs, prod.qpf._match_1] },
  { simp! only [set.range, set.ext_iff],
    simp only [not_exists, false_iff, bool.forall_bool, eq_self_iff_true, exists_false, not_true,
      and_self, set.mem_set_of_eq, iff_false],
    exact λ h, h () }
end

/-- intuitive consequence of original definition of `supp`. -/
lemma supp_mk_tt {α} (x : α) : functor.supp (foo.mk tt x) = {x} :=
begin
  dsimp [functor.supp], ext y, simp, split; intro h',
  { apply @h' (= x), dsimp [functor.liftp],
    use foo.mk tt ⟨x,rfl⟩, refl },
  { introv hp, simp [functor.liftp] at hp,
    rcases hp with ⟨⟨z,z',hz⟩,hp⟩,
    simp at hp, replace hp := quot.exact _ hp,
    rw (equivalence_foo.R _).eqv_gen_iff at hp,
    rcases hp with ⟨⟨⟩,hp⟩, subst y,
    replace hp := hp rfl, cases hp,
    exact hz }
end

/-- simple consequence of the definition of `supp` from the QBNF paper -/
lemma supp_mk_ff' {α} (x : α) : qpf.supp' (foo.mk ff x) = {} :=
begin
  dsimp [qpf.supp'], ext, simp, dsimp [qpf.box],
  use ∅, simp [foo.mk], intros, apply quot.sound,
  dsimp [foo.R], split, refl, rintro ⟨ ⟩
end

/-- simple consequence of the definition of `supp` from the QBNF paper -/
lemma supp_mk_tt' {α} (x : α) : qpf.supp' (foo.mk tt x) = {x} :=
begin
  dsimp [qpf.supp'], ext, simp, dsimp [qpf.box], split; intro h,
  { specialize h {x} _,
    { clear h, introv hfg, simp, rw hfg, simp },
    { simp at h, assumption }, },
  { introv hfg, subst x_1, classical,
    let f : α → α ⊕ bool := λ x, if x ∈ i then sum.inl x else sum.inr tt,
    let g : α → α ⊕ bool := λ x, if x ∈ i then sum.inl x else sum.inr ff,
    specialize hfg _ f g _,
    { intros, simp [*,f,g,if_pos] },
    { simp [f,g] at hfg, split_ifs at hfg,
      assumption, cases hfg } }
end
end ex
