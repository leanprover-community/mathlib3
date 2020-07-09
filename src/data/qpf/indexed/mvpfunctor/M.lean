/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Mario Carneiro

The M construction as a multivariate polynomial functor.
-/
import data.qpf.indexed.mvpfunctor.basic data.qpf.indexed.pfunctor
universe u

namespace mvpfunctor

variables {I J : Type u} (P : mvpfunctor (I ⊕ J) J)

inductive M_path : Π {i : J}, pfunctor.M P.last i → I → Type u
| root {i} (x : pfunctor.M P.last i) (a : P.A i) (f : P.last.B i a ⟶ P.last.M) (h : pfunctor.M_dest x = ⟨a, f⟩)
       (j : I) (c : P.drop.B i a j) :
    M_path x j
| child {i} (x : pfunctor.M P.last i) (a : P.A i) (f : P.last.B i a ⟶ P.last.M)
        (h : pfunctor.M_dest x = ⟨a, f⟩)
        (j : J) (a : P.last.B i a j) {i'} (c : M_path (f a) i') :
    M_path x i'

def Mp : mvpfunctor I J :=
{ A := P.last.M, B := λ _, P.M_path }

def M (α : fam I) : fam J := P.Mp.obj α

-- instance mvfunctor_M : mvfunctor P.M := by delta M; apply_instance

def M_corec_shape {β : fam J}
    (g₀ : β ⟶ P.A)
    (g₂ : Π {i} (b : β i), P.last.B i (g₀ b) ⟶ β) :
  β ⟶ pfunctor.M P.last :=
pfunctor.M_corec (λ j b, ⟨g₀ b, g₂ _⟩)

def cast_dropB {i} : Π {a a' : P.A i} (h : a = a'), P.drop.B i a ⟶ P.drop.B i a'
| _ _ rfl i b := b

def cast_lastB {i} : Π {a a' : P.A i} (h : a = a'), P.last.B i a ⟶ P.last.B i a'
| _ _ rfl i b := b

def M_corec_contents {α : fam I} {β : fam J}
    (g₀ : β ⟶ P.A)
    (g₁ : Π ⦃i⦄ (b : β i), P.drop.B i (g₀ b) ⟶ α)
    (g₂ : Π ⦃i⦄ (b : β i), P.last.B i (g₀ b) ⟶ β) :
  Π {j} x (b : β j), x = P.M_corec_shape g₀ g₂ b → (P.M_path x ⟶ α)
| j ._ b h ._ (M_path.root x a f h' i c)    :=
  have a = g₀ b,
    by { rw [h, M_corec_shape, pfunctor.M_dest_corec] at h', cases h', refl },
  g₁ b (P.cast_dropB this c)
| j ._ b h ._ (M_path.child x a f h' j' i c) :=
  have h₀ : a = g₀ b,
    by { rw [h, M_corec_shape, pfunctor.M_dest_corec] at h', cases h', refl },
  have h₁ : f i = M_corec_shape P g₀ g₂ (g₂ b (cast_lastB P h₀ i)),
    by { rw [h, M_corec_shape, pfunctor.M_dest_corec] at h', cases h', refl },
  M_corec_contents (f i) (g₂ b (P.cast_lastB h₀ _)) h₁ c

def M_corec' {α : fam I} {β : fam J}
    (g₀ : β ⟶ P.A)
    (g₁ : Π ⦃i⦄ (b : β i), P.drop.B i (g₀ b) ⟶ α) :
  Π (g₂ : Π ⦃i⦄ (b : β i), P.last.B i (g₀ b) ⟶ β),
  β ⟶ P.M α
| g₂ j b := ⟨M_corec_shape P g₀ g₂ b, M_corec_contents P g₀ g₁ g₂ _ _ rfl⟩

open fam

def M_corec {α : fam I} {β : fam J} (g : β ⟶ P.obj (α.append1 β)) :
  β ⟶ P.M α :=
M_corec' P
  (λ i b, (g b).fst)
  (λ i b, drop_fun (g b).snd)
  (λ i b, last_fun (g b).snd)

def M_path_dest_left {α : fam I} {j} {x : pfunctor.M P.last j}
    {a : P.A j} {f : P.last.B j a ⟶ P.last.M} (h : pfunctor.M_dest x = ⟨a, f⟩)
    (f' : P.M_path x ⟶ α) :
  P.drop.B j a ⟶ α :=
λ i c, f' (M_path.root x a f h i c)

def M_path_dest_right {α : fam I} {j} {x : pfunctor.M P.last j}
    {a : P.A j} {f : P.last.B j a ⟶ P.last.M} (h : pfunctor.M_dest x = ⟨a, f⟩)
    (f' : P.M_path x ⟶ α) :
  Π {i} j : P.last.B _ a i, P.M_path (f j) ⟶ α :=
λ j i k c, f' (M_path.child x a f h j i c)

def M_dest' {α : fam I}
    {i} {x : pfunctor.M P.last i} {a : P.A i}
    {f : P.last.B i a ⟶ P.last.M} (h : pfunctor.M_dest x = ⟨a, f⟩)
    (f' : P.M_path x ⟶ α) :
  P.obj (α.append1 (P.M α)) _ :=
⟨a, split_fun (P.M_path_dest_left h f') (λ j x, ⟨f x, P.M_path_dest_right h f' x⟩)⟩

def M_dest : Π {α : fam I}, P.M α ⟶ P.obj (α.append1 (P.M α))
| α i x := P.M_dest' (sigma.eta $ pfunctor.M_dest x.fst).symm x.snd

def M_mk : Π {α : fam I}, P.obj (α.append1 (P.M α)) ⟶ P.M α
| α := M_corec _ (P.map $ append_fun (𝟙 _) $ M_dest P)

theorem M_dest'_eq_dest' {α : fam I} {i} {x : pfunctor.M P.last i}
    {a₁ : P.A i} {f₁ : P.last.B _ a₁ ⟶ P.last.M} (h₁ : pfunctor.M_dest x = ⟨a₁, f₁⟩)
    {a₂ : P.A i} {f₂ : P.last.B _ a₂ ⟶ P.last.M} (h₂ : pfunctor.M_dest x = ⟨a₂, f₂⟩)
    (f' : P.M_path x ⟶ α) : M_dest' P h₁ f' = M_dest' P h₂ f' :=
by cases h₁.symm.trans h₂; refl

theorem M_dest_eq_dest' {α : fam I} {i} {x : pfunctor.M P.last i}
    {a : P.A i} {f : P.last.B i a ⟶ P.last.M} (h : pfunctor.M_dest x = ⟨a, f⟩)
    (f' : P.M_path x ⟶ α) : M_dest P ⟨x, f'⟩ = M_dest' P h f' :=
M_dest'_eq_dest' _ _ _ _

theorem M_dest_corec' {α : fam I} {β : fam J}
    (g₀ : β ⟶ P.A)
    (g₁ : Π ⦃i⦄ (b : β i), P.drop.B i (g₀ b) ⟶ α)
    (g₂ : Π ⦃i⦄ (b : β i), P.last.B i (g₀ b) ⟶ β)
    {i} (x : β i) :
  P.M_dest (P.M_corec' g₀ g₁ g₂ x) =
    ⟨g₀ x, split_fun (g₁ x) (g₂ x ≫ P.M_corec' g₀ g₁ g₂)⟩ :=
rfl

theorem M_dest_corec {α : fam I} {β : fam J}
  (g : β ⟶ P.obj (α.append1 β)) {i} (x : β i) :
  P.M_dest (P.M_corec g x) = P.map (append_fun (𝟙 _) (P.M_corec g)) (g x) :=
begin
  transitivity, apply M_dest_corec',
  cases g x with a f, dsimp,
  rw pfunctor.map_eq', congr,
  conv { to_rhs, rw [←split_drop_fun_last_fun f, mvfunctor.append_fun_comp_split_fun] },
  refl
end

@[reassoc]
theorem M_dest_corec'' {α : fam I} {β : fam J}
  (g : β ⟶ P.obj (α.append1 β)) :
  P.M_corec g ≫ P.M_dest = g ≫ P.map (append_fun (𝟙 _) (P.M_corec g)) :=
by ext : 2; simp [M_dest_corec]

lemma M_bisim_lemma {α : fam I}
  {i} {a₁ : (Mp P).A i} {f₁ : (Mp P).B _ a₁ ⟶ α}
  {a' : P.A i} {f' : (P.B _ a').drop ⟶ α} {f₁' : (P.B _ a').last ⟶ M P α}
  (e₁ : M_dest P ⟨a₁, f₁⟩ = ⟨a', split_fun f' f₁'⟩) :
  ∃ g₁' (e₁' : pfunctor.M_dest a₁ = ⟨a', g₁'⟩),
    f' = M_path_dest_left P e₁' f₁ ∧
    f₁' = λ i (x : (last P).B _ a' _),
      ⟨g₁' x, M_path_dest_right P e₁' f₁ x⟩ :=
begin
  generalize_hyp ef : @split_fun _ _ _ (append1 α (M P α)) f' f₁' = ff at e₁,
  cases e₁' : pfunctor.M_dest a₁ with a₁' g₁',
  rw M_dest_eq_dest' _ e₁' at e₁,
  cases e₁, exact ⟨_, e₁', mvfunctor.split_fun_inj ef⟩,
end

theorem M_bisim {α : fam I} (R : Π ⦃j⦄, P.M α j → P.M α j → Prop)
  (h : ∀ j (x y : P.M α j), R x y → ∃ a f f₁ f₂,
    P.M_dest x = ⟨a, split_fun f f₁⟩ ∧
    P.M_dest y = ⟨a, split_fun f f₂⟩ ∧
    ∀ i x, @R i (f₁ x) (f₂ x))
  {j} (x y) (r : @R j x y) : x = y :=
begin
  cases x with a₁ f₁,
  cases y with a₂ f₂,
  dsimp [Mp] at *,
  have : a₁ = a₂, {
    refine pfunctor.M_bisim
      (λ i (a₁ a₂ : pfunctor.M (last P) i), ∃ x y, @R i x y ∧ x.1 = a₁ ∧ y.1 = a₂) _ _ _ _
      ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩,
    rintro _ _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩,
    rcases h _ _ _ r with ⟨a', f', f₁', f₂', e₁, e₂, h'⟩,
    rcases M_bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩,
    rcases M_bisim_lemma P e₂ with ⟨g₂', e₂', _, rfl⟩,
    rw [e₁', e₂'],
    exact ⟨_, _, _, rfl, rfl, λ i b, ⟨_, _, h' _ b, rfl, rfl⟩⟩ },
  subst this, congr, ext i p,
  induction p with x i' a f h' i j c x a f h' i j c p IH generalizing f₁ f₂,
  all_goals {
    rcases h _ _ _ r with ⟨i, a', f', f₁', e₁, e₂, h''⟩,
    rcases M_bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩,
    rcases M_bisim_lemma P e₂ with ⟨g₂', e₂', e₃, rfl⟩,
    cases h'.symm.trans e₁',
    cases h'.symm.trans e₂' },
  { exact (congr_fun (congr_fun e₃ i) _ : _) },
  { exact IH _ _ (h'' _ _) }
end

open pfunctor mvfunctor

@[reassoc]
theorem M_dest_map {α β : fam I} (g : α ⟶ β) :
  P.Mp.map g ≫ P.M_dest = P.M_dest ≫ P.map (append_fun g (P.Mp.map g)) :=
begin
  ext i x : 2,
  cases x with a f,
  simp [map_eq],
  conv { to_rhs, rw [M_dest, M_dest', map_eq', append_fun_comp_split_fun] },
  reflexivity,
end

end mvpfunctor
