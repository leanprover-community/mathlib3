/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek
-/


import .main

section

/- Examples from finish. -/

variables {A B C D : Prop}

example : (A → B ∨ C) → (B → D) → (C → D) → A → D :=
by vampire "n100ean1ean100ean10ean1n0ean11eartrrrr"

example : ¬ A → A → C :=
by vampire

example : (A ∧ A ∧ B) → (A ∧ C ∧ B) → A :=
by vampire

example : A → ¬ B → ¬ (A → B) :=
by vampire

example : A ∨ B → B ∨ A :=
by vampire

example : A ∧ B → B ∧ A :=
by vampire

example : A → (A → B) → (B → C) → C :=
by vampire

example : (A ∧ B) → (C ∧ B) → C :=
by vampire

example : A → B → C → D → (A ∧ B) ∧ (C ∧ D) :=
by vampire

example : (A ∧ B) → (B ∧ ¬ C) → A ∨ C :=
by vampire

example : (A → B) ∧ (B → C) → A → C :=
by vampire


example : (A → B) ∨ (B → A) :=
by vampire

example : ((A → B) → A) → A :=
by vampire

example : A → ¬ B → ¬ (A → B) :=
by vampire

example : ¬ (A ↔ ¬ A) :=
by vampire

example : (A ↔ B) → (A ∧ B → C) → (¬ A ∧ ¬ B → C) → C :=
by vampire

example : (A ↔ B) → ((A ∧ ¬ B) ∨ (¬ A ∧ B)) → C :=
by vampire

example : (A → B) → A → B :=
by vampire

example : (A → B) → (B → C) → A → C :=
by vampire

example : (A → B ∨ C) → (B → D) → (C → D) → A → D :=
by vampire

example : A ∨ B → B ∨ A :=
by vampire

variables (α : Type) [inhabited α]
variables (a b c : α) (p q : α → Prop) (r : α → α → Prop)
variables (P Q R : Prop)
variable  (g : bool → nat)

example : (∀ x, p x → q x) → (∀ x, p x) → q a :=
by vampire

example : (p a) → ∃ x, p x :=
by vampire

example : (p a) → (p b) → (q b) → ∃ x, p x ∧ q x :=
by vampire

example : (∃ x, p x ∧ r x x) → (∀ x, r x x → q x) → ∃ x, p x ∧ q x :=
by vampire

example : (∃ x, q x ∧ p x) → ∃ x, p x ∧ q x :=
by vampire

example : (∀ x, q x → p x) → (q a) → ∃ x, p x :=
by vampire

example : (∀ x, p x → q x → false) → (p a) → (p b) → (q b) → false :=
by vampire

example : (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x :=
by vampire

example : (∃ x, p x) → (∀ x, p x → q x) → ∃ x, q x :=
by vampire

example : (¬ ∀ x, ¬ p x) → (∀ x, p x → q x) → (∀ x, ¬ q x) → false :=
by vampire

example : (p a) → (p a → false) → false :=
by vampire

example : (¬ (P → Q ∨ R)) → (¬ (Q ∨ ¬ R)) → false :=
by vampire

example : (P → Q ∨ R) → (¬ Q) → P → R :=
by vampire

example : (∃ x, p x → P) ↔ (∀ x, p x) → P :=
by vampire

example : (∃ x, P → p x) ↔ (P → ∃ x, p x) :=
by vampire

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

lemma gilmore_6 {F G : α → α → Prop} {H : α → α → α → Prop} :
∀ x, ∃ y,
  (∃ u, ∀ v, F u x → G v u ∧ G u x)
   → (∃ u, ∀ v, F u y → G v u ∧ G u y) ∨
       (∀ u v, ∃ w, G v u ∨ H w y u → G u w) :=
by vampire

lemma gilmore_8 {G : α → Prop} {F : α → α → Prop} {H : α → α → α → Prop} :
  ∃ x, ∀ y z,
    ((F y z → (G y → (∀ u, ∃ v, H u v x))) → F x x) ∧
    ((F z x → G x) → (∀ u, ∃ v, H u v z)) ∧
    F x y → F z z := by vampire

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

#print knights_and_knaves
#exit
n10n0en11101n100sn0sn101sppn1sn101sppmn11110n101sman10n10n1n
1011en1n100sn0sn101sppn1sn101sppmatn1010en10n100sn0sn101sppn
1sn101sppmn11n10sn101spmn100n1sn101spmartn1n110en1110n100sn0
sn101sppn1sn101sppmn1111n11sn101spmn10000n101sman1n1en11011n
100sn0sn101sppn1sn101sppmn11100n101smatrn1n1n10en11001n11sn1
01spmn11010n101smatn1n10n111en1011n11sn101spmn1100n11sn101sp
mn1101n101sman1000en1000n11sn101spmn1010n1sn101spmn1001n10sn
101spman1n1100en0n11sn101spmatrrtctrn1001en101n11sn101spmn11
0n10sn101spmn111n1sn101spman1n1100en0n11sn101spmatrrtcrn1n11
en10111n100sn0sn101sppn1sn101sppmn11000n101smatrtrtrtcn1001e
n101n100sn0sn101sppn1sn101sppmn110n1sn101spmn111n0sn101spman
1n10n1n1n100en10100n100sn0sn101sppn1sn101sppmn10101n100sn0sn
101sppn1sn101sppmn10110n101sman1n10n0en11101n100sn0sn101sppn
1sn101sppmn11110n101sman10n10n1n1011en1n100sn0sn101sppn1sn10
1sppmatn1010en10n100sn0sn101sppn1sn101sppmn11n10sn101spmn100
n1sn101spmartn1n110en1110n100sn0sn101sppn1sn101sppmn1111n11s
n101spmn10000n101sman1n1en11011n100sn0sn101sppn1sn101sppmn11
100n101smatrn1n1n10en11001n11sn101spmn11010n101smatn1n10n111
en1011n11sn101spmn1100n11sn101spmn1101n101sman1000en1000n11s
n101spmn1010n1sn101spmn1001n10sn101spman1n1100en0n11sn101spm
atrrtctrn1001en101n11sn101spmn110n10sn101spmn111n1sn101spman
1n1100en0n11sn101spmatrrtcrn1n11en10111n100sn0sn101sppn1sn10
1sppmn11000n101smatrtrtrtcn1n1en11011n100sn0sn101sppn1sn101s
ppmn11100n101smatrtrn10n111en1011n100sn0sn101sppn1sn101sppmn
1100n100sn0sn101sppn1sn101sppmn1101n101sman1000en1000n100sn0
sn101sppn1sn101sppmn1010n1sn101spmn1001n10sn101spman1n1100en
0n100sn0sn101sppn1sn101sppmatrrtcrtn1n10n10n1n11n1n10n101en1
0001n100sn0sn101sppn1sn101sppmn10010n100sn0sn101sppn1sn101sp
pmn10011n101sman1n10n0en11101n100sn0sn101sppn1sn101sppmn1111
0n101sman10n10n1n1011en1n100sn0sn101sppn1sn101sppmatn1010en1
0n100sn0sn101sppn1sn101sppmn11n10sn101spmn100n1sn101spmartn1
n110en1110n100sn0sn101sppn1sn101sppmn1111n11sn101spmn10000n1
01sman1n1en11011n100sn0sn101sppn1sn101sppmn11100n101smatrn1n
1n10en11001n11sn101spmn11010n101smatn1n10n111en1011n11sn101s
pmn1100n11sn101spmn1101n101sman1000en1000n11sn101spmn1010n1s
n101spmn1001n10sn101spman1n1100en0n11sn101spmatrrtctrn1001en
101n11sn101spmn110n10sn101spmn111n1sn101spman1n1100en0n11sn1
01spmatrrtcrn1n11en10111n100sn0sn101sppn1sn101sppmn11000n101
smatrtrtrtcn1n1en11011n100sn0sn101sppn1sn101sppmn11100n101sm
atrtrtn10n111en1011n100sn0sn101sppn1sn101sppmn1100n100sn0sn1
01sppn1sn101sppmn1101n101sman1000en1000n100sn0sn101sppn1sn10
1sppmn1010n1sn101spmn1001n10sn101spman1n1100en0n100sn0sn101s
ppn1sn101sppmatrrtcrtn10n100en10100n100sn0sn101sppn1sn101spp
mn10101n100sn0sn101sppn1sn101sppmn10110n101sman10n111en1011n
100sn0sn101sppn1sn101sppmn1100n100sn0sn101sppn1sn101sppmn110
1n101sman1n1en11011n100sn0sn101sppn1sn101sppmn11100n101smatr
trn10n111en1011n100sn0sn101sppn1sn101sppmn1100n100sn0sn101sp
pn1sn101sppmn1101n101sman1000en1000n100sn0sn101sppn1sn101spp
mn1010n1sn101spmn1001n10sn101spman1n1100en0n100sn0sn101sppn1
sn101sppmatrrtcrtrtcttctctrttctcrrn1n0en11101n1sn101spmn1111
0n101smatn1n10n1n1n100en10100n1sn101spmn10101n1sn101spmn1011
0n101sman1n10n0en11101n1sn101spmn11110n101sman10n10n1n1011en
1n1sn101spmatn1010en10n1sn101spmn11n10sn101spmn100n1sn101spm
artn1n110en1110n1sn101spmn1111n11sn101spmn10000n101sman1n1en
11011n1sn101spmn11100n101smatrn1n1n10en11001n11sn101spmn1101
0n101smatn1n10n111en1011n11sn101spmn1100n11sn101spmn1101n101
sman1000en1000n11sn101spmn1010n1sn101spmn1001n10sn101spman1n
1100en0n11sn101spmatrrtctrn1001en101n11sn101spmn110n10sn101s
pmn111n1sn101spman1n1100en0n11sn101spmatrrtcrn1n11en10111n1s
n101spmn11000n101smatrtrtrtcn1n1en11011n1sn101spmn11100n101s
matrtrn10n111en1011n1sn101spmn1100n1sn101spmn1101n101sman100
0en1000n1sn101spmn1010n1sn101spmn1001n10sn101spman1n1100en0n
1sn101spmatrrtcrtn1n10n10n1n11n1n10n101en10001n1sn101spmn100
10n1sn101spmn10011n101sman1n10n0en11101n1sn101spmn11110n101s
man10n10n1n1011en1n1sn101spmatn1010en10n1sn101spmn11n10sn101
spmn100n1sn101spmartn1n110en1110n1sn101spmn1111n11sn101spmn1
0000n101sman1n1en11011n1sn101spmn11100n101smatrn1n1n10en1100
1n11sn101spmn11010n101smatn1n10n111en1011n11sn101spmn1100n11
sn101spmn1101n101sman1000en1000n11sn101spmn1010n1sn101spmn10
01n10sn101spman1n1100en0n11sn101spmatrrtctrn1001en101n11sn10
1spmn110n10sn101spmn111n1sn101spman1n1100en0n11sn101spmatrrt
crn1n11en10111n1sn101spmn11000n101smatrtrtrtcn1n1en11011n1sn
101spmn11100n101smatrtrtn10n111en1011n1sn101spmn1100n1sn101s
pmn1101n101sman1000en1000n1sn101spmn1010n1sn101spmn1001n10sn
101spman1n1100en0n1sn101spmatrrtcrtn10n100en10100n1sn101spmn
10101n1sn101spmn10110n101sman10n111en1011n1sn101spmn1100n1sn
101spmn1101n101sman1n1en11011n1sn101spmn11100n101smatrtrn10n
111en1011n1sn101spmn1100n1sn101spmn1101n101sman1000en1000n1s
n101spmn1010n1sn101spmn1001n10sn101spman1n1100en0n1sn101spma
trrtcrtrtcttctctrttctcrn10n1000en1000n1sn101spmn1010n0sn101s
pmn1001n1sn101spman1n111en1011n1sn101spmn1100n100sn0sn101spp
n1sn101sppmn1101n101sman1n1en11011n1sn101spmn11100n101smatrt
rtcrr




"
n10n0en11101n110sn1sn111sppn10sn111sppmn11110n111sman10n10n1
n1011en1n110sn1sn111sppn10sn111sppmatn1010en10n110sn1sn111sp
pn10sn111sppmn11n11sn111spmn100n10sn111spmartn1n110en1110n11
0sn1sn111sppn10sn111sppmn1111n100sn111spmn10000n111sman1n1en
11011n110sn1sn111sppn10sn111sppmn11100n111smatrn1n1n10en1100
1n100sn111spmn11010n111smatn1n10n111en1011n100sn111spmn1100n
100sn111spmn1101n111sman1000en1000n100sn111spmn1010n10sn111s
pmn1001n11sn111spman1n1100en0n100sn111spmatrrtctrn1001en101n
100sn111spmn110n11sn111spmn111n10sn111spman1n1100en0n100sn11
1spmatrrtcrn1n11en10111n110sn1sn111sppn10sn111sppmn11000n111
smatrtrtrtcn1001en101n110sn1sn111sppn10sn111sppmn110n10sn111
spmn111n1sn111spman1n10n1n1n100en10100n110sn1sn111sppn10sn11
1sppmn10101n110sn1sn111sppn10sn111sppmn10110n111sman1n10n0en
11101n110sn1sn111sppn10sn111sppmn11110n111sman10n10n1n1011en
1n110sn1sn111sppn10sn111sppmatn1010en10n110sn1sn111sppn10sn1
11sppmn11n11sn111spmn100n10sn111spmartn1n110en1110n110sn1sn1
11sppn10sn111sppmn1111n100sn111spmn10000n111sman1n1en11011n1
10sn1sn111sppn10sn111sppmn11100n111smatrn1n1n10en11001n100sn
111spmn11010n111smatn1n10n111en1011n100sn111spmn1100n100sn11
1spmn1101n111sman1000en1000n100sn111spmn1010n10sn111spmn1001
n11sn111spman1n1100en0n100sn111spmatrrtctrn1001en101n100sn11
1spmn110n11sn111spmn111n10sn111spman1n1100en0n100sn111spmatr
rtcrn1n11en10111n110sn1sn111sppn10sn111sppmn11000n111smatrtr
trtcn1n1en11011n110sn1sn111sppn10sn111sppmn11100n111smatrtrn
10n111en1011n110sn1sn111sppn10sn111sppmn1100n110sn1sn111sppn
10sn111sppmn1101n111sman1000en1000n110sn1sn111sppn10sn111spp
mn1010n10sn111spmn1001n11sn111spman1n1100en0n110sn1sn111sppn
10sn111sppmatrrtcrtn1n10n10n1n11n1n10n101en10001n110sn1sn111
sppn10sn111sppmn10010n110sn1sn111sppn10sn111sppmn10011n111sm
an1n10n0en11101n110sn1sn111sppn10sn111sppmn11110n111sman10n1
0n1n1011en1n110sn1sn111sppn10sn111sppmatn1010en10n110sn1sn11
1sppn10sn111sppmn11n11sn111spmn100n10sn111spmartn1n110en1110
n110sn1sn111sppn10sn111sppmn1111n100sn111spmn10000n111sman1n
1en11011n110sn1sn111sppn10sn111sppmn11100n111smatrn1n1n10en1
1001n100sn111spmn11010n111smatn1n10n111en1011n100sn111spmn11
00n100sn111spmn1101n111sman1000en1000n100sn111spmn1010n10sn1
11spmn1001n11sn111spman1n1100en0n100sn111spmatrrtctrn1001en1
01n100sn111spmn110n11sn111spmn111n10sn111spman1n1100en0n100s
n111spmatrrtcrn1n11en10111n110sn1sn111sppn10sn111sppmn11000n
111smatrtrtrtcn1n1en11011n110sn1sn111sppn10sn111sppmn11100n1
11smatrtrtn10n111en1011n110sn1sn111sppn10sn111sppmn1100n110s
n1sn111sppn10sn111sppmn1101n111sman1000en1000n110sn1sn111spp
n10sn111sppmn1010n10sn111spmn1001n11sn111spman1n1100en0n110s
n1sn111sppn10sn111sppmatrrtcrtn10n100en10100n110sn1sn111sppn
10sn111sppmn10101n110sn1sn111sppn10sn111sppmn10110n111sman10
n111en1011n110sn1sn111sppn10sn111sppmn1100n110sn1sn111sppn10
sn111sppmn1101n111sman1n1en11011n110sn1sn111sppn10sn111sppmn
11100n111smatrtrn10n111en1011n110sn1sn111sppn10sn111sppmn110
0n110sn1sn111sppn10sn111sppmn1101n111sman1000en1000n110sn1sn
111sppn10sn111sppmn1010n10sn111spmn1001n11sn111spman1n1100en
0n110sn1sn111sppn10sn111sppmatrrtcrtrtcttctctrttctcrrn1n0en1
1101n10sn111spmn11110n111smatn1n10n1n1n100en10100n10sn111spm
n10101n10sn111spmn10110n111sman1n10n0en11101n10sn111spmn1111
0n111sman10n10n1n1011en1n10sn111spmatn1010en10n10sn111spmn11
n11sn111spmn100n10sn111spmartn1n110en1110n10sn111spmn1111n10
0sn111spmn10000n111sman1n1en11011n10sn111spmn11100n111smatrn
1n1n10en11001n100sn111spmn11010n111smatn1n10n111en1011n100sn
111spmn1100n100sn111spmn1101n111sman1000en1000n100sn111spmn1
010n10sn111spmn1001n11sn111spman1n1100en0n100sn111spmatrrtct
rn1001en101n100sn111spmn110n11sn111spmn111n10sn111spman1n110
0en0n100sn111spmatrrtcrn1n11en10111n10sn111spmn11000n111smat
rtrtrtcn1n1en11011n10sn111spmn11100n111smatrtrn10n111en1011n
10sn111spmn1100n10sn111spmn1101n111sman1000en1000n10sn111spm
n1010n10sn111spmn1001n11sn111spman1n1100en0n10sn111spmatrrtc
rtn1n10n10n1n11n1n10n101en10001n10sn111spmn10010n10sn111spmn
10011n111sman1n10n0en11101n10sn111spmn11110n111sman10n10n1n1
011en1n10sn111spmatn1010en10n10sn111spmn11n11sn111spmn100n10
sn111spmartn1n110en1110n10sn111spmn1111n100sn111spmn10000n11
1sman1n1en11011n10sn111spmn11100n111smatrn1n1n10en11001n100s
n111spmn11010n111smatn1n10n111en1011n100sn111spmn1100n100sn1
11spmn1101n111sman1000en1000n100sn111spmn1010n10sn111spmn100
1n11sn111spman1n1100en0n100sn111spmatrrtctrn1001en101n100sn1
11spmn110n11sn111spmn111n10sn111spman1n1100en0n100sn111spmat
rrtcrn1n11en10111n10sn111spmn11000n111smatrtrtrtcn1n1en11011
n10sn111spmn11100n111smatrtrtn10n111en1011n10sn111spmn1100n1
0sn111spmn1101n111sman1000en1000n10sn111spmn1010n10sn111spmn
1001n11sn111spman1n1100en0n10sn111spmatrrtcrtn10n100en10100n
10sn111spmn10101n10sn111spmn10110n111sman10n111en1011n10sn11
1spmn1100n10sn111spmn1101n111sman1n1en11011n10sn111spmn11100
n111smatrtrn10n111en1011n10sn111spmn1100n10sn111spmn1101n111
sman1000en1000n10sn111spmn1010n10sn111spmn1001n11sn111spman1
n1100en0n10sn111spmatrrtcrtrtcttctctrttctcrn10n1000en1000n10
sn111spmn1010n1sn111spmn1001n10sn111spman1n111en1011n10sn111
spmn1100n110sn1sn111sppn10sn111sppmn1101n111sman1n1en11011n1
0sn111spmn11100n111smatrtrtcrr
"
