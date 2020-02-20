import tactic.rw_hint

structure cat :=
  (O : Type)
  (H : O → O → Type)
  (i : Π o : O, H o o)
  (c : Π {X Y Z : O} (f : H X Y) (g : H Y Z), H X Z)
  (li : Π {X Y : O} (f : H X Y), c (i X) f = f)
  (ri : Π {X Y : O} (f : H X Y), c f (i Y) = f)
  (a : Π {W X Y Z : O} (f : H W X) (g : H X Y) (h : H Y Z), c (c f g) h = c f (c g h))

open tactic

example (C : cat) (W X Y Z : C.O) (f : C.H X Y) (g : C.H W X) (h k : C.H Y Z) : C.c (C.c g f) h = C.c g (C.c f h) :=
begin
  (do s ← tactic.rw_hint, guard $ "rw cat.a" ∈ s, guard $ "rw cat.ri" ∉ s),
  rw cat.a,
end

example (C : cat) (X Y : C.O) (f : C.H X Y) : C.c f (C.i Y) = f :=
begin
  (do s ← tactic.rw_hint, guard $ "rw cat.ri" ∈ s),
  rw cat.ri,
end

example : 2 * (3 + 4) = 2 * 3 + 2 * 4 :=
begin
  (do s ← tactic.rw_hint, guard $ "rw left_distrib" ∈ s),
  rw left_distrib,
end

example (P Q : Prop) (h : P ↔ Q) (p : P) : Q :=
begin
  (do s ← tactic.rw_hint, guard $ "rw ←h" ∈ s),
  rw ←h, exact p,
end
