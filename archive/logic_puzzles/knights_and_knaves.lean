/-
Copyright (c) 2020 Dan Stanescu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Stanescu.
-/

import tactic

/-!
# Knights and knaves puzzles
Two puzzles from "Knights and Knaves" by Raymond Smullyan.
For an online description of these puzzles, see: http://mesosyn.com/mental1-6.html
More information on R. Smullyan: https://en.wikipedia.org/wiki/Raymond_Smullyan

There is an island where all inhabitants are either knights or knaves. 
Knights always tell the truth. Knaves always lie.
Joe and Bob are two inhabitants of this island.
-/

inductive islander
| knight
| knave

notation `y` := islander.knight
notation `n` := islander.knave

structure Q := (Joe Bob : islander)

/--
In this first puzzle, only Joe makes a statement.
He affirms that both protagonist (i.e. both Joe and Bob) are knaves.
Question: what kind of islanders are they in fact?
-/

def Q1 := Q

namespace Q1

variables (q : Q1)

-- Joe's statement
def S1 := q.Joe = n ∧ q.Bob = n
-- Stating that Joe can be a knight or a knave
def H := (q.Joe = y ∧ q.S1) ∨ (q.Joe = n ∧ ¬ q.S1)

lemma answer : q.H → q.Joe = n ∧ q.Bob = y :=
begin
   rcases q with ⟨_|_,_|_⟩;
   { simp [H, S1], },
   done
end

end Q1

/--
In the second puzzle, both Joe and Bob make a statement.
Joe states that he's a knave if and only if Bob is a knave.
Bob only states that they are different kinds. 
Question: again, what kind of islanders are our protagonists?
-/


def Q2 := Q

namespace Q2

variables (q : Q2)

-- Joe's statement
def S1 := q.Joe = n ↔ q.Bob = n
-- Bob's statement 
def S2 := q.Joe ≠ q.Bob
-- Stating that either one can be a knight or a knave
def H1 := (q.Joe = y ∧ q.S1) ∨ (q.Joe = n ∧ ¬ q.S1)
def H2 := (q.Bob = y ∧ q.S2) ∨ (q.Bob = n ∧ ¬ q.S2)
-- Again two forms here:
def H := q.H1 ∧ q.H2

lemma answer : q.H → q.Joe = n ∧ q.Bob = y :=
begin
   rcases q with ⟨_|_,_|_⟩;
   { simp [H, H1, S1, H2, S2], },
   done
end


end Q2
