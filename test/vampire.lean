/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek
-/

import tactic.vampire

#exit
section

/- Examples from finish. -/

variables {A B C D : Prop}

example : (A → B ∨ C) → (B → D) → (C → D) → A → D := by vampire
example : ¬ A → A → C := by vampire
example : (A ∧ A ∧ B) → (A ∧ C ∧ B) → A := by vampire
example : A → ¬ B → ¬ (A → B) := by vampire
example : A ∨ B → B ∨ A := by vampire
example : A ∧ B → B ∧ A := by vampire
example : A → (A → B) → (B → C) → C := by vampire
example : (A ∧ B) → (C ∧ B) → C := by vampire
example : A → B → C → D → (A ∧ B) ∧ (C ∧ D) := by vampire
example : (A ∧ B) → (B ∧ ¬ C) → A ∨ C := by vampire
example : (A → B) ∧ (B → C) → A → C := by vampire
example : (A → B) ∨ (B → A) := by vampire
example : ((A → B) → A) → A := by vampire
example : A → ¬ B → ¬ (A → B) := by vampire
example : ¬ (A ↔ ¬ A) := by vampire
example : (A ↔ B) → (A ∧ B → C) → (¬ A ∧ ¬ B → C) → C := by vampire
example : (A ↔ B) → ((A ∧ ¬ B) ∨ (¬ A ∧ B)) → C := by vampire
example : (A → B) → A → B := by vampire
example : (A → B) → (B → C) → A → C := by vampire
example : (A → B ∨ C) → (B → D) → (C → D) → A → D := by vampire
example : A ∨ B → B ∨ A := by vampire

variables (α : Type) [inhabited α]
variables (a b c : α) (p q : α → Prop) (r : α → α → Prop)
variables (P Q R : Prop)
variable  (g : bool → nat)

example : (∀ x, p x → q x) → (∀ x, p x) → q a := by vampire
example : (p a) → ∃ x, p x := by vampire
example : (p a) → (p b) → (q b) → ∃ x, p x ∧ q x := by vampire
example : (∃ x, p x ∧ r x x) → (∀ x, r x x → q x) → ∃ x, p x ∧ q x := by vampire
example : (∃ x, q x ∧ p x) → ∃ x, p x ∧ q x := by vampire
example : (∀ x, q x → p x) → (q a) → ∃ x, p x := by vampire
example : (∀ x, p x → q x → false) → (p a) → (p b) → (q b) → false := by vampire
example : (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x := by vampire
example : (∃ x, p x) → (∀ x, p x → q x) → ∃ x, q x := by vampire
example : (¬ ∀ x, ¬ p x) → (∀ x, p x → q x) → (∀ x, ¬ q x) → false := by vampire
example : (p a) → (p a → false) → false := by vampire
example : (¬ (P → Q ∨ R)) → (¬ (Q ∨ ¬ R)) → false := by vampire
example : (P → Q ∨ R) → (¬ Q) → P → R := by vampire
example : (∃ x, p x → P) ↔ (∀ x, p x) → P := by vampire
example : (∃ x, P → p x) ↔ (P → ∃ x, p x) := by vampire

end

section

  /- Some harder examples, from John Harrison's
     Handbook of Practical Logic and Automated Reasoning. -/

variables (α : Type) [inhabited α]


lemma gilmore_1 {F G H : α → Prop} :
  ∃ x, ∀ y z,
      ((F y → G y) ↔ F x) ∧
      ((F y → H y) ↔ G x) ∧
      (((F y → G y) → H y) ↔ H x)
      → F z ∧ G z ∧ H z :=
by vampire
"
1. s2(s1(X0)) | s2(X0) [input]
2. ~s3(s1(X0)) | s2(X0) [input]
3. ~s2(s1(X0)) | s3(s1(X0)) | ~s2(X0) [input]
4. s2(s1(X0)) | s3(X0) [input]
5. ~s4(s1(X0)) | s3(X0) [input]
6. ~s2(s1(X0)) | s4(s1(X0)) | ~s3(X0) [input]
7. ~s2(s1(X0)) | s3(s1(X0)) | s4(X0) [input]
8. ~s4(s1(X0)) | s4(X0) [input]
11. ~s4(s0(X0)) | ~s3(s0(X0)) | ~s2(s0(X0)) [input]
12. s3(s1(X0)) | ~s2(X0) | s3(X0) [resolution 3,4]
19. s3(s1(X0)) | s4(X0) | s3(X0) [resolution 7,4]
20. s3(s1(X1)) | s4(X1) | s2(X1) [resolution 7,1]
21. s4(X1) | s2(X1) [subsumption resolution 20,2]
22. s2(s1(X0)) | s4(X0) [resolution 21,8]
27. s4(X1) | s4(s1(X1)) | ~s3(X1) [resolution 22,6]
30. ~s3(X1) | s4(X1) [subsumption resolution 27,8]
33. s4(s1(X0)) | ~s2(X0) | s3(X0) [resolution 30,12]
34. ~s2(X0) | s3(X0) [subsumption resolution 33,5]
38. s3(s1(X2)) | s2(X2) [resolution 34,1]
39. s2(X2) [subsumption resolution 38,2]
42. s4(X2) | s3(X2) | s4(s1(X2)) [resolution 19,30]
43. s4(X2) | s4(s1(X2)) [subsumption resolution 42,30]
44. s4(X2) [subsumption resolution 43,8]
46. s3(X1) [resolution 44,5]
47. ~s3(s0(X2)) | ~s2(s0(X2)) [resolution 44,11]
48. ~s2(s0(X2)) [subsumption resolution 47,46]
49. $false [subsumption resolution 48,39]
"

lemma gilmore_6 {F G : α → α → Prop} {H : α → α → α → Prop} :
∀ x, ∃ y,
  (∃ u, ∀ v, F u x → G v u ∧ G u x)
   → (∃ u, ∀ v, F u y → G v u ∧ G u y) ∨
       (∀ u v, ∃ w, G v u ∨ H w y u → G u w) :=
by vampire
"
1. ~s5(s3(X0),s4) | s6(X1,s3(X0)) [input]
3. s5(X2,X0) [input]
6. ~s6(s1(X0),X3) [input]
7. s6(X0,s3(X1)) [resolution 1,3]
9. $false [resolution 7,6]
"

lemma gilmore_8 {G : α → Prop} {F : α → α → Prop} {H : α → α → α → Prop} :
  ∃ x, ∀ y z,
    ((F y z → (G y → (∀ u, ∃ v, H u v x))) → F x x) ∧
    ((F z x → G x) → (∀ u, ∃ v, H u v z)) ∧
    F x y → F z z :=
by vampire
"
2. s4(X0,X0) | s5(s3(X0)) [input]
3. ~s6(s1(X0),X1,X0) | s4(X0,X0) [input]
5. s6(X2,s0(X0,X2),s2(X0)) | ~s5(X0) [input]
7. ~s4(s2(X0),s2(X0)) [input]
8. s5(s3(s2(X0))) [resolution 2,7]
9. ~s5(X0) | s4(s2(X0),s2(X0)) [resolution 5,3]
10. ~s5(X0) [subsumption resolution 9,7]
13. $false [resolution 10,8]
"

lemma manthe_and_bry (agatha butler charles : α)
(lives : α → Prop) (killed hates richer : α → α → Prop) :
   lives agatha ∧ lives butler ∧ lives charles ∧
   (killed agatha agatha ∨ killed butler agatha ∨
    killed charles agatha) ∧
   (∀ x y, killed x y → hates x y ∧ ¬ richer x y) ∧
   (∀ x, hates agatha x → ¬ hates charles x) ∧
   (hates agatha agatha ∧ hates agatha charles) ∧
   (∀ x, lives(x) ∧ ¬ richer x agatha → hates butler x) ∧
   (∀ x, hates agatha x → hates butler x) ∧
   (∀ x, ¬ hates x agatha ∨ ¬ hates x butler ∨ ¬ hates x charles)
   → killed agatha agatha ∧
       ¬ killed butler agatha ∧
       ¬ killed charles agatha :=
by vampire
"
2. s0(s2) [input]
4. s4(s3,s1) | s4(s2,s1) | s4(s1,s1) [input]
5. ~s4(X0,X1) | s5(X0,X1) [input]
6. ~s6(X0,X1) | ~s4(X0,X1) [input]
7. ~s5(s3,X2) | ~s5(s1,X2) [input]
8. s5(s1,s1) [input]
9. s5(s1,s3) [input]
10. s6(X3,s1) | s5(s2,X3) | ~s0(X3) [input]
11. ~s5(s1,X4) | s5(s2,X4) [input]
12. ~s5(X5,s3) | ~s5(X5,s2) | ~s5(X5,s1) [input]
13. s4(s3,s1) | s4(s2,s1) | ~s4(s1,s1) [input]
14. s4(s3,s1) | s4(s2,s1) [subsumption resolution 13,4]
15. s5(s2,s1) [resolution 11,8]
16. s5(s2,s3) [resolution 11,9]
17. s5(s3,s1) | s4(s2,s1) [resolution 14,5]
18. ~s4(X0,s1) | ~s0(X0) | s5(s2,X0) [resolution 10,6]
20. s4(s2,s1) | ~s5(s1,s1) [resolution 17,7]
21. s4(s2,s1) [subsumption resolution 20,8]
23. ~s5(s2,s2) | ~s5(s2,s1) [resolution 12,16]
25. ~s5(s2,s2) [subsumption resolution 23,15]
28. ~s0(s2) | s5(s2,s2) [resolution 21,18]
30. s5(s2,s2) [subsumption resolution 28,2]
31. $false [subsumption resolution 30,25]
"

/- A logic puzzle by Raymond Smullyan. -/

lemma knights_and_knaves (me : α) (knight knave rich poor : α → α)
  (a_truth says : α → α → Prop) (and : α → α → α) :
  ( (∀ X Y, ¬ a_truth (knight X) Y ∨ ¬ a_truth (knave X) Y ) ∧
    (∀ X Y, a_truth (knight X) Y ∨ a_truth (knave X) Y ) ∧
    (∀ X Y, ¬ a_truth (rich X) Y ∨ ¬ a_truth (poor X) Y ) ∧
    (∀ X Y, a_truth (rich X) Y ∨ a_truth (poor X) Y ) ∧
    (∀ X Y Z, ¬ a_truth (knight X) Z ∨ ¬ says X Y ∨ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (knight X) Z ∨ says X Y ∨ ¬ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (knave X) Z ∨ ¬ says X Y ∨ ¬ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (knave X) Z ∨ says X Y ∨ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (and X Y) Z ∨ a_truth X Z ) ∧
    (∀ X Y Z, ¬ a_truth (and X Y) Z ∨ a_truth Y Z ) ∧
    (∀ X Y Z, a_truth (and X Y) Z ∨ ¬ a_truth X Z ∨ ¬ a_truth Y Z ) ∧
    (∀ X, ¬ says me X ∨ ¬ a_truth (and (knave me) (rich me)) X ) ∧
    (∀ X, says me X ∨ a_truth (and (knave me) (rich me)) X ) ) → false :=
by vampire
"
1. ~s0(s2(X0),X1) | ~s0(s1(X0),X1) [input]
2. s0(s2(X2),X3) | s0(s1(X2),X3) [input]
3. ~s0(s4(X4),X5) | ~s0(s3(X4),X5) [input]
4. s0(s4(X6),X7) | s0(s3(X6),X7) [input]
5. ~s0(s1(X8),X9) | ~s5(X8,X10) | s0(X10,X9) [input]
6. ~s0(s1(X11),X12) | s5(X11,X13) | ~s0(X13,X12) [input]
7. ~s0(s2(X14),X15) | ~s5(X14,X16) | ~s0(X16,X15) [input]
8. ~s0(s2(X17),X18) | s5(X17,X19) | s0(X19,X18) [input]
9. ~s0(s6(X20,X21),X22) | s0(X20,X22) [input]
10. ~s0(s6(X23,X24),X25) | s0(X24,X25) [input]
11. s0(s6(X26,X27),X28) | ~s0(X26,X28) | ~s0(X27,X28) [input]
12. ~s0(s6(s2(s7),s3(s7)),X29) | ~s5(s7,X29) [input]
13. s0(s6(s2(s7),s3(s7)),X30) | s5(s7,X30) [input]
16. ~s5(X0,X1) | ~s0(X1,X2) | s0(s1(X0),X2) [resolution 7,2]
17. s5(X0,X1) | s0(X1,X2) | s0(s1(X0),X2) [resolution 8,2]
18. s0(s3(s7),X0) | s5(s7,X0) [resolution 13,10]
19. s0(s2(s7),X1) | s5(s7,X1) [resolution 13,9]
23. ~s0(s3(s7),X6) | ~s0(s2(s7),X6) | ~s5(s7,X6) [resolution 11,12]
24. s5(s7,X0) | s5(s7,X1) | s0(X1,X0) [resolution 19,8]
35. s5(X26,s6(X27,X28)) | s0(s1(X26),X29) | s0(X27,X29) [resolution 17,9]
39. ~s5(X4,X7) | s0(X5,X6) | s5(X4,X5) | s0(X7,X6) [resolution 17,5]
59. s5(s7,X0) | s0(X0,X0) [factoring 24]
70. ~s0(s3(X5),s4(X5)) | s5(s7,s4(X5)) [resolution 59,3]
156. s5(X0,s6(s1(X0),X1)) | s0(s1(X0),X2) [factoring 35]
194. s0(X26,X27) | s5(s7,X26) | s0(X28,X27) | s0(X28,X28) [resolution 39,59]
216. s5(s7,s4(s7)) | s5(s7,s4(s7)) [resolution 70,18]
222. s5(s7,s4(s7)) [duplicate literal removal 216]
261. ~s0(s4(s7),X3) | s0(s1(s7),X3) [resolution 222,16]
321. s0(s3(s7),X0) | s0(s1(s7),X0) [resolution 261,4]
343. s0(s1(s7),X0) | ~s0(s2(s7),X0) | ~s5(s7,X0) [resolution 321,23]
350. ~s0(s2(s7),X0) | ~s5(s7,X0) [subsumption resolution 343,1]
362. s0(s1(s7),X1) | ~s5(s7,X1) [resolution 350,2]
386. ~s5(s7,X3) | s5(s7,X4) | ~s0(X4,X3) [resolution 362,6]
387. ~s5(s7,X6) | ~s5(s7,X5) | s0(X6,X5) [resolution 362,5]
1079. s5(s7,X18) | ~s0(X18,X19) | s0(X19,X19) [resolution 386,59]
1118. s5(s7,X18) | s0(X19,X19) [subsumption resolution 1079,194]
1794. ~s5(s7,X18) | s0(X19,X18) | s0(X19,X19) [resolution 387,59]
1845. s0(X19,X18) | s0(X19,X19) [subsumption resolution 1794,1118]
2009. s0(X0,X0) [factoring 1845]
2119. ~s0(s1(X41),s2(X41)) [resolution 2009,1]
2128. s0(X53,s6(X54,X53)) [resolution 2009,10]
2571. s5(X36,s6(s1(X36),X37)) [resolution 2119,156]
2803. ~s5(s7,s6(X1,s2(s7))) [resolution 2128,350]
3239. $false [resolution 2803,2571]
"

end
