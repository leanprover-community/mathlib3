/-
Copyright (c) 2020 Dan Stanescu.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Stanescu and Yuri G. Kudryashov.
-/

import tactic

/-!
# Six logic puzzles.
-/

/-- 
The first six puzzles from:
    "The Lady or the Tiger? And Other Logic Puzzles"
        by Raymond Smullyan.
First three contributed to the Lean Zulip chat by Yury G. Kudryashov
but apparently set up by his seven-years-old son.
Slightly modified in appearance (for readability) but not in content by D. Stanescu.

A king has prisoners choose between two rooms. The signs on the room doors offer enough information
to allow them to make the right choice between rooms with ladies (i.e. presumably happiness) 
and rooms with tigers (i.e. presumably death).
In the first three puzzles, the king explains that it is always the case that one of the door 
signs is true while the other one is false.
-/


inductive door_leads_to
| lady
| tiger

notation `y` := door_leads_to.lady
notation `n` := door_leads_to.tiger

structure Q := (d₁ d₂ : door_leads_to)

/--
First puzzle: 
Sign on the first door indicates that there's a lady in this room and a tiger in the other room.
Sign on second door indicates that in one of the rooms there's a lady and in one room a tiger.
-/

def Q1 := Q

namespace Q1

variables (q : Q1)

-- Sign on first door
def D1 := q.1 = y ∧ q.2 = n
-- Sign on second door
def D2 := (q.1 = y ∨ q.2 = y) ∧ (q.1 = n ∨ q.2 = n)

def H := q.D1 ∧ ¬q.D2 ∨ ¬q.D1 ∧ q.D2

-- Terse proof.
lemma answer_term : q.H → q.1 = n ∧ q.2 = y :=
  by rcases q with ⟨_|_,_|_⟩; simp [H, D1, D2]

-- Verbose proof. State changes can be seen by clicking after each comma.
lemma answer_tactic : q.H → q.1 = n ∧ q.2 = y :=
begin
  rcases q with ⟨_|_,_|_⟩,
  simp [H], simp [D1], simp [D2],
  simp[H], simp [D1], simp [D2],
  simp [H], 
  simp [H], simp [D1], simp [D2], 
  done
end

end Q1

/--
Second puzzle: 
Sign on the first door indicates that at least one room contains a lady.
Sign on second door indicates there's a tiger in the other room.
-/

def Q2 := Q

namespace Q2

variables (q : Q2)

-- Sign on first door
def D1 := q.1 = y ∨ q.2 = y
-- Sign on second door
def D2 := q.1 = n

def H := q.D1 ∧ q.D2 ∨ ¬q.D1 ∧ ¬q.D2

lemma answer : q.H → q.1 = n ∧ q.2 = y :=
  by rcases q with ⟨_|_,_|_⟩; simp [H, D1, D2]

end Q2

/--
Third puzzle: 
Sign on the first door indicates that there's either a tiger in this room or a lady in the other.
Sign on second door indicates there's a lady in the other room.
-/


def Q3 := Q

namespace Q3

variables (q : Q3)

-- Sign on first door
def D1 := q.1 = n ∨ q.2 = y
-- Sign on second door
def D2 := q.1 = y

def H := q.D1 ∧ q.D2 ∨ ¬q.D1 ∧ ¬q.D2

lemma answer : q.H → q.1 = y ∧ q.2 = y :=
  by rcases q with ⟨_|_,_|_⟩; simp [H, D1, D2]

end Q3

/-! Puzzles 4-7 from the same book:
    "The Lady or the Tiger? And Other Logic Puzzles"
        by Raymond Smullyan.
Solutions written by D. Stanescu in the same framework as above. 
In these puzzles, the king explains that the sign on the first door (D1) is true if a lady
is in in that room and is false if a tiger is in that room. The opposite is true for the sign on 
the second door (D2), which is true if a tiger is hidden behind it but false otherwise.
-/

/--
Puzzle number four: 
First door sign says that both rooms contain ladies.
Second door sign is identical.
-/

def Q4 := Q

namespace Q4

variables (q : Q4)

-- Sign on first door
def D1 := q.1 = y ∧ q.2 = y
-- Sign on second door
def D2 := q.1 = y ∧ q.2 = y

-- one way to set up this problem 
def H1 := q.1 = y ∧ q.D1 ∨ q.1 = n ∧ ¬ q.D1
def H2 := q.2 = y ∧ ¬ q.D2 ∨ q.2 = n ∧ q.D2
def H := q.H1 ∧ q.H2

-- Verbose proof
lemma answer1 : q.H → q.1 = n ∧ q.2 = y :=
begin
  rcases q with ⟨_|_,_|_⟩,
  simp [H], simp [H1], simp [D1], simp [H2], simp [D2], 
  simp [H], simp [H1], simp [D1], 
  simp [H], simp [H1], 
  simp [H], simp [H1], simp [D1], simp [H2], simp [D2], 
  done
end

-- Terse proof
lemma answer2 : q.H → q.1 = n ∧ q.2 = y :=
begin
  rcases q with ⟨_|_,_|_⟩;
  simp [H, H1, D1, H2, D2], 
  done
end

end Q4

/--
Puzzle number five: 
First door sign says that at least one room contains a lady.
Second door sign says : "In the other room there is a lady."
-/


def Q5 := Q

namespace Q5

variables (q : Q5)

-- Sign on first door
def D1 := q.1 = y ∨ q.2 = y ∨ q.1 = y ∧ q.2 = y
-- Sign on second door
def D2 := q.1 = y

-- same setup as Q4 above
def H1 := q.1 = y ∧ q.D1 ∨ q.1 = n ∧ ¬ q.D1
def H2 := q.2 = y ∧ ¬ q.D2 ∨ q.2 = n ∧ q.D2
def H := q.H1 ∧ q.H2

lemma answer : q.H → q.1 = y ∧ q.2 = n :=
begin
  rcases q with ⟨_|_,_|_⟩;
  simp [H, H1, D1, H2, D2], 
  done
end

end Q5

/--
Puzzle number six: 
First door sign says that it makes no difference which room the prisoner picks.
Second door sign is the same as in the previous puzzle.
Apparently the king is particularly fond of this puzzle.
-/

def Q6 := Q

namespace Q6

variables (q : Q6)

-- Sign on first door
def D1 := q.1 = q.2
-- Sign on second door
def D2 := q.1 = y

-- same setup as Q4 above
def H1 := q.1 = y ∧ q.D1 ∨ q.1 = n ∧ ¬ q.D1
def H2 := q.2 = y ∧ ¬ q.D2 ∨ q.2 = n ∧ q.D2
def H := q.H1 ∧ q.H2

lemma answer : q.H → q.1 = n ∧ q.2 = y :=
begin
  rcases q with ⟨_|_,_|_⟩;
  simp [H, H1, D1, H2, D2], 
  done
end


end Q6
