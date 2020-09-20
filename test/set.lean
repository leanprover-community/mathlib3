import data.matrix.notation

example (x : ℕ) (h : x = 3)  : x + x + x = 9 :=
begin
  set y := x with ←h_xy,
  guard_hyp y : ℕ := x,
  guard_hyp h_xy : x = y,
  guard_hyp h : y = 3,
  guard_target y + y + y = 9,
  set! z : ℕ := y,
  guard_target y + y + y = 9,
  simp [h]
end

example : true :=
let X1 := (![![1, 0], ![0, 0]] : matrix (fin 2) (fin 2) ℕ), -- X1 : fin 1.succ → fin 2 → ℕ
    X2 : matrix (fin 2) (fin 2) ℕ := ![![1, 0], ![0, 0]] in -- X2 : matrix (fin 2) (fin 2) ℕ
begin
  set Y1 := (![![1, 0], ![0, 0]] : matrix (fin 2) (fin 2) ℕ),
  set Y2 : matrix (fin 2) (fin 2) ℕ := ![![1, 0], ![0, 0]],
  let Z1 := (![![1, 0], ![0, 0]] : matrix (fin 2) (fin 2) ℕ),
  let Z2 : matrix (fin 2) (fin 2) ℕ := ![![1, 0], ![0, 0]],
  guard_hyp Y2 : matrix (fin 2) (fin 2) ℕ := (![![1, 0], ![0, 0]] : matrix (fin 2) (fin 2) ℕ),
  trivial
end

def T {α : Type} := ℕ
def v : @T ℕ := nat.zero

def S := @T ℕ
def u : S := nat.zero

def p : true :=
begin
  set a : T := v,
  set b : T := u, -- the type `T` can't be fully elaborated without the body but this is fine
  trivial
end
