import Std

/-!
# The arithmetic additive subtraction game in Figure 17

Urban Larsson, Indrajit Saha and Makoto Yokoo, "Subtraction games in more
than one dimension", Definition 48 and Figure 17.
Proof note and formalization by BI1XLN and GPT-6.2 Astra, 2026-11-26.
Run: lean Figure17.lean (Lean 4.36.0, standard library only).

Entry points:
* original_quickTest provides a three-case modular test for any (x,y).
* original_figure17 gives the five parametric families.
* original_middle gives the exact recursively colored middle segment.
* scaled_figure17 covers every positive integer dilation of the three moves.
* generating_identity verifies the polynomial calculation in the written proof.

The formal proof reduces local game-rule consistency to a 64 by 64 box.
Four proved translation lemmas transfer the local rule on that box to the
whole first quadrant. Coordinate y in the rule is the original coordinate;
h in the parametrization, geometry and colors is floor(y/2).
-/

namespace Figure17

def pattern (x h : Int) : Prop :=
  (h % 4 = 0 ∧ 3*h ≤ 2*x) ∨
  (x % 7 = 0 ∧ 6*x ≤ 7*h) ∨
  (x % 7 = 2 ∧ 6*x+2 ≤ 7*h) ∨
  (2*x ≤ 3*h ∧ 7*h ≤ 6*x ∧ (6*x+h) % 8 = 0) ∨
  (2*x+2 ≤ 3*h ∧ 7*h ≤ 6*x+2 ∧ (6*x+h+2) % 8 = 0)

def accessibleP (x h : Int) : Prop := 0 ≤ x ∧ 0 ≤ h ∧ pattern x h

-- Moving towards the finite verification region preserves the outcome
-- predicate in each of the four angular sectors.
private theorem east (x h : Int) (hx : 1 ≤ x) (ha : 3*h-2*x ≤ -3) :
    accessibleP x h ↔ accessibleP (x-1) h := by
  unfold accessibleP pattern
  by_cases hh : 0 ≤ h <;> omega

private theorem north (x h : Int) (hh : 1 ≤ h) (hb : 6*x-7*h ≤ -10) :
    accessibleP x h ↔ accessibleP x (h-1) := by
  unfold accessibleP pattern
  by_cases hx : 0 ≤ x <;> omega

private theorem step76 (x h : Int) (hx : 7 ≤ x) (hh : 6 ≤ h) (ha : 6 ≤ 3*h-2*x) :
    accessibleP x h ↔ accessibleP (x-7) (h-6) := by
  have e1 : (x-7)%7 = x%7 := by omega
  have e2 : (6*(x-7)+(h-6))%8 = (6*x+h)%8 := by omega
  have e3 : (6*(x-7)+(h-6)+2)%8 = (6*x+h+2)%8 := by omega
  unfold accessibleP pattern
  rw [e1,e2,e3]
  omega

private theorem step64 (x h : Int) (hx : 6 ≤ x) (hh : 4 ≤ h) (hb : 9 ≤ 6*x-7*h) :
    accessibleP x h ↔ accessibleP (x-6) (h-4) := by
  have e1 : (h-4)%4 = h%4 := by omega
  have e2 : (6*(x-6)+(h-4))%8 = (6*x+h)%8 := by omega
  have e3 : (6*(x-6)+(h-4)+2)%8 = (6*x+h+2)%8 := by omega
  unfold accessibleP pattern
  rw [e1,e2,e3]
  omega


def rule (x h : Int) : Prop :=
  accessibleP x h ↔ ¬ accessibleP (x-1) (h-1) ∧
                    ¬ accessibleP (x-3) (h-2) ∧
                    ¬ accessibleP (x-4) (h-3)

private def offset (i j : Int) : Prop :=
  (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 1) ∨ (i = 3 ∧ j = 2) ∨ (i = 4 ∧ j = 3)

private theorem shiftRule (x h dx dh : Int)
    (H : ∀ i j, offset i j →
       (accessibleP (x-i) (h-j) ↔ accessibleP ((x-i)-dx) ((h-j)-dh))) :
    rule x h ↔ rule (x-dx) (h-dh) := by
  have align (i j : Int) (Hoff : offset i j) :
      accessibleP (x-i) (h-j) ↔ accessibleP ((x-dx)-i) ((h-dh)-j) := by
    rw [show x-dx-i = x-i-dx by omega, show h-dh-j = h-j-dh by omega]
    exact H i j Hoff
  have hz := align 0 0 (by unfold offset; decide)
  simp only [Int.sub_zero] at hz
  unfold rule
  rw [hz, align 1 1 (by unfold offset; decide), align 3 2 (by unfold offset; decide),
    align 4 3 (by unfold offset; decide)]

private theorem offsets_bounds (i j : Int) (hoff : offset i j) :
    0 ≤ i ∧ i ≤ 4 ∧ 0 ≤ j ∧ j ≤ 3 ∧ 0 ≤ 3*j-2*i ∧ 3*j-2*i ≤ 1 ∧
    -1 ≤ 6*i-7*j ∧ 6*i-7*j ≤ 4 := by
  unfold offset at hoff
  omega

private instance (x h : Int) : Decidable (rule x h) := by
  unfold rule accessibleP pattern
  infer_instance

private theorem finiteRule : ∀ x h : Fin 64, rule (x.val : Int) (h.val : Int) := by
  decide +kernel

set_option maxHeartbeats 500000 in
theorem local_rule (x h : Int) (hx : 0 ≤ x) (hh : 0 ≤ h) : rule x h := by
  by_cases E : 5 ≤ x ∧ 3*h-2*x ≤ -3
  · apply (shiftRule x h 1 0 ?_).2
    · exact local_rule (x-1) (h-0) (by omega) (by omega)
    · intro i j hoff
      have := offsets_bounds i j hoff
      simp only [Int.sub_zero]
      exact east (x-i) (h-j) (by omega) (by omega)
  by_cases N : 4 ≤ h ∧ 6*x-7*h ≤ -11
  · apply (shiftRule x h 0 1 ?_).2
    · exact local_rule (x-0) (h-1) (by omega) (by omega)
    · intro i j hoff
      have := offsets_bounds i j hoff
      simp only [Int.sub_zero]
      exact north (x-i) (h-j) (by omega) (by omega)
  by_cases D : 11 ≤ x ∧ 9 ≤ h ∧ 7 ≤ 3*h-2*x
  · apply (shiftRule x h 7 6 ?_).2
    · exact local_rule (x-7) (h-6) (by omega) (by omega)
    · intro i j hoff
      have := offsets_bounds i j hoff
      exact step76 (x-i) (h-j) (by omega) (by omega) (by omega)
  by_cases C : 10 ≤ x ∧ 7 ≤ h ∧ 13 ≤ 6*x-7*h
  · apply (shiftRule x h 6 4 ?_).2
    · exact local_rule (x-6) (h-4) (by omega) (by omega)
    · intro i j hoff
      have := offsets_bounds i j hoff
      exact step64 (x-i) (h-j) (by omega) (by omega) (by omega)
  let a : Fin 64 := ⟨x.toNat, by omega⟩
  let b : Fin 64 := ⟨h.toNat, by omega⟩
  have small := finiteRule a b
  have ha : (a.val : Int) = x := by dsimp [a]; omega
  have hb : (b.val : Int) = h := by dsimp [b]; omega
  rwa [ha,hb] at small
termination_by x.toNat+h.toNat
decreasing_by all_goals omega


/-- The proposed five families in their original coordinates. -/
def families (x h : Int) : Prop :=
  (∃ j : Int, 0 ≤ j ∧ h = 4*j ∧ 6*j ≤ x) ∨
  (∃ i k : Int, 0 ≤ i ∧ (k = 0 ∨ k = 1) ∧ x = 7*i+2*k ∧ 6*i+2*k ≤ h) ∨
  (∃ i j k : Int, 0 ≤ i ∧ 0 ≤ j ∧ (k = 0 ∨ k = 1) ∧
    x = 7*i+6*j+2*k ∧ h = 6*i+4*j+2*k)

theorem families_iff (x h : Int) (hx : 0 ≤ x) (hh : 0 ≤ h) :
    families x h ↔ accessibleP x h := by
  unfold families accessibleP pattern
  constructor
  · intro H
    refine ⟨hx, hh, ?_⟩
    rcases H with ⟨j,hj,e,ineq⟩ | ⟨i,k,hi,hk,e,ineq⟩ | ⟨i,j,k,hi,hj,hk,ex,eh⟩
    · left; omega
    · rcases hk with rfl | rfl
      · right; left; omega
      · right; right; left; omega
    · rcases hk with rfl | rfl
      · right; right; right; left; omega
      · right; right; right; right; omega
  · rintro ⟨_, _, H⟩
    rcases H with h₀ | h₁ | h₂ | h₃ | h₄
    · left; exact ⟨h/4, by omega⟩
    · right; left; exact ⟨x/7, 0, by omega⟩
    · right; left; exact ⟨x/7, 1, by omega⟩
    · right; right
      let Q := (6*x+h)/8
      exact ⟨6*Q-5*x, Q-h, 0, by dsimp [Q]; omega⟩
    · right; right
      let Q := (6*x+h+2)/8
      exact ⟨6*Q-5*x-2, Q-h, 1, by dsimp [Q]; omega⟩

/-- Normal play: the next player loses iff every legal option is winning. -/
def losing (x h : Nat) : Prop :=
  ((1 ≤ x ∧ 1 ≤ h) → ¬ losing (x-1) (h-1)) ∧
  ((3 ≤ x ∧ 2 ≤ h) → ¬ losing (x-3) (h-2)) ∧
  ((4 ≤ x ∧ 3 ≤ h) → ¬ losing (x-4) (h-3))
termination_by x
decreasing_by all_goals omega

theorem losing_iff_accessible (x h : Nat) :
    losing x h ↔ accessibleP (x : Int) (h : Int) := by
  induction x using Nat.strongRecOn generalizing h with
  | ind x ih =>
    have option (a b : Nat) (ha : 0 < a) :
        ((a ≤ x ∧ b ≤ h) → ¬ losing (x-a) (h-b)) ↔
        ¬ accessibleP ((x : Int) - a) ((h : Int) - b) := by
      by_cases ok : a ≤ x ∧ b ≤ h
      · have subx : ((x-a : Nat) : Int) = (x : Int)-a := by omega
        have subh : ((h-b : Nat) : Int) = (h : Int)-b := by omega
        have sub := ih (x-a) (by omega) (h-b)
        simp only [subx,subh] at sub
        simp [ok,sub]
      · have impossible : ¬ accessibleP ((x : Int)-a) ((h : Int)-b) := by
          unfold accessibleP
          omega
        simp [ok,impossible]
    have R := local_rule (x : Int) (h : Int) (by omega) (by omega)
    unfold rule at R
    rw [losing, R, option 1 1 (by decide), option 3 2 (by decide), option 4 3 (by decide)]
    rfl

/-- Complete characterization of normal-play losing positions on the reduced board. -/
theorem figure17 (x h : Nat) : losing x h ↔ families (x : Int) (h : Int) :=
  (losing_iff_accessible x h).trans (families_iff _ _ (by omega) (by omega)).symm


/-- The paper's original rule with coordinate decrements (1,2), (3,4), (4,6). -/
def originalLosing (x y : Nat) : Prop :=
  ((1 ≤ x ∧ 2 ≤ y) → ¬ originalLosing (x-1) (y-2)) ∧
  ((3 ≤ x ∧ 4 ≤ y) → ¬ originalLosing (x-3) (y-4)) ∧
  ((4 ≤ x ∧ 6 ≤ y) → ¬ originalLosing (x-4) (y-6))
termination_by x
decreasing_by all_goals omega

private theorem halve (x y : Nat) : originalLosing x y ↔ losing x (y/2) := by
  induction x using Nat.strongRecOn generalizing y with
  | ind x ih =>
    have option (a b : Nat) (ha : 0 < a) :
        ((a ≤ x ∧ 2*b ≤ y) → ¬ originalLosing (x-a) (y-2*b)) ↔
        ((a ≤ x ∧ b ≤ y/2) → ¬ losing (x-a) (y/2-b)) := by
      by_cases ok : a ≤ x ∧ 2*b ≤ y
      · have ok' : a ≤ x ∧ b ≤ y/2 := by omega
        have e : (y-2*b)/2 = y/2-b := by omega
        simp [ok,ok', ih (x-a) (by omega) (y-2*b), e]
      · have ok' : ¬ (a ≤ x ∧ b ≤ y/2) := by omega
        simp [ok,ok']
    rw [originalLosing, losing]
    exact and_congr (option 1 1 (by decide)) (and_congr (option 3 2 (by decide)) (option 4 3 (by decide)))

/-- Exact outcome on the original unbounded board, including both y parities. -/
theorem original_figure17 (x y : Nat) :
    originalLosing x y ↔ families (x : Int) ((y/2 : Nat) : Int) :=
  (halve x y).trans (figure17 x (y/2))


/-- A three-case test with no existential quantifiers. -/
def quickTest (x h : Int) : Prop :=
  let A := 3*h-2*x
  let B := 6*x-7*h
  if A < 0 then h%4 = 0
  else if B < 0 then x%7 = 0 ∨ x%7 = 2
  else B%8 = 0 ∨ B%8 = 6

theorem quickTest_iff (x h : Int) (hx : 0 ≤ x) (hh : 0 ≤ h) :
    quickTest x h ↔ accessibleP x h := by
  have c₀ : (6*x-7*h)%8 = (6*x+h)%8 := by omega
  have c₂ : (6*x-7*h)%8 = 6 ↔ (6*x+h+2)%8 = 0 := by omega
  have compat : (3*h-2*x + (6*x-7*h))%4 = 0 := by omega
  simp only [quickTest, accessibleP, pattern]
  split
  · omega
  · split <;> omega

theorem original_quickTest (x y : Nat) :
    originalLosing x y ↔ quickTest x (y/2 : Nat) :=
  (halve x y).trans ((losing_iff_accessible x (y/2)).trans (quickTest_iff _ _ (by omega) (by omega)).symm)

inductive Color where
  | purple | green | blue

/-- The middle coloring in half-height coordinates, generated from the origin. -/
inductive Marked : Color → Int → Int → Prop where
  | seed : Marked .purple 0 0
  | toGreen {x h} : Marked .purple x h → Marked .green (x+2) (h+2)
  | toPurple {x h} : Marked .green x h → Marked .purple (x+5) (h+4)
  | enterBlueP {x h} : Marked .purple x h → Marked .blue (x+6) (h+4)
  | enterBlueG {x h} : Marked .green x h → Marked .blue (x+6) (h+4)
  | continueBlue {x h} : Marked .blue x h → Marked .blue (x+6) (h+4)

private def markForm : Color → Int → Int → Prop
  | .purple, x, h => ∃ i : Nat, x = 7*(i:Int) ∧ h = 6*(i:Int)
  | .green, x, h => ∃ i : Nat, x = 7*(i:Int)+2 ∧ h = 6*(i:Int)+2
  | .blue, x, h => ∃ i j : Nat, ∃ k : Int, 1 ≤ j ∧ (k=0 ∨ k=1) ∧
      x = 7*(i:Int)+6*(j:Int)+2*k ∧ h = 6*(i:Int)+4*(j:Int)+2*k

private theorem sound {c x h} (m : Marked c x h) : markForm c x h := by
  induction m with
  | seed => exact ⟨0,by decide⟩
  | toGreen _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, by omega⟩
  | toPurple _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i+1, by omega⟩
  | enterBlueP _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i,1,0,by omega⟩
  | enterBlueG _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i,1,1,by omega⟩
  | continueBlue _ ih =>
    obtain ⟨i,j,k,H⟩ := ih
    exact ⟨i,j+1,k,by omega⟩

private theorem purple (i : Nat) : Marked .purple (7*(i:Int)) (6*(i:Int)) := by
  induction i with
  | zero => exact Marked.seed
  | succ i ih =>
    have m := Marked.toPurple (Marked.toGreen ih)
    rw [show (7*(i:Int)+2+5) = 7*((i+1:Nat):Int) by omega,
        show (6*(i:Int)+2+4) = 6*((i+1:Nat):Int) by omega] at m
    exact m

private theorem blue (i j : Nat) (k : Int) (hk : k=0 ∨ k=1) :
    Marked .blue (7*(i:Int)+6*((j+1:Nat):Int)+2*k)
      (6*(i:Int)+4*((j+1:Nat):Int)+2*k) := by
  induction j with
  | zero =>
    rcases hk with rfl | rfl
    · simpa using Marked.enterBlueP (purple i)
    · have m := Marked.enterBlueG (Marked.toGreen (purple i))
      rw [show 7*(i:Int)+6*((0+1:Nat):Int)+2*1 = 7*(i:Int)+2+6 by omega,
          show 6*(i:Int)+4*((0+1:Nat):Int)+2*1 = 6*(i:Int)+2+4 by omega]
      exact m
  | succ j ih =>
    have m := Marked.continueBlue ih
    rw [show 7*(i:Int)+6*((j+1+1:Nat):Int)+2*k = (7*(i:Int)+6*((j+1:Nat):Int)+2*k)+6 by omega,
        show 6*(i:Int)+4*((j+1+1:Nat):Int)+2*k = (6*(i:Int)+4*((j+1:Nat):Int)+2*k)+4 by omega]
    exact m

private theorem complete {c x h} (H : markForm c x h) : Marked c x h := by
  cases c with
  | purple => obtain ⟨i,rfl,rfl⟩ := H; exact purple i
  | green => obtain ⟨i,rfl,rfl⟩ := H; exact Marked.toGreen (purple i)
  | blue =>
    obtain ⟨i,j,k,hj,hk,rfl,rfl⟩ := H
    cases j with
    | zero => omega
    | succ j => exact blue i j k hk

/-- Lower and upper segment rays, with the original diagram's strict seed bounds. -/
def exterior (x h : Int) : Prop :=
  (∃ j : Int, 0 ≤ j ∧ h=4*j ∧ 6*j < x) ∨
  (∃ i k : Int, 0 ≤ i ∧ (k=0 ∨ k=1) ∧ x=7*i+2*k ∧ 6*i+2*k < h)

private theorem mid {x h : Int} (i j k : Int) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (hk : k=0 ∨ k=1) (ex : x=7*i+6*j+2*k) (eh : h=6*i+4*j+2*k) :
    ∃ c, Marked c x h := by
  by_cases hj₀ : j=0
  · rcases hk with rfl | rfl
    · exact ⟨.purple, complete (show markForm .purple x h from ⟨i.toNat, by omega⟩)⟩
    · exact ⟨.green, complete (show markForm .green x h from ⟨i.toNat, by omega⟩)⟩
  · exact ⟨.blue, complete (show markForm .blue x h from ⟨i.toNat,j.toNat,k,by omega⟩)⟩

theorem coloring_iff (x h : Int) :
    (exterior x h ∨ ∃ c, Marked c x h) ↔ families x h := by
  constructor
  · rintro (he | ⟨c,m⟩)
    · rcases he with ⟨j,H⟩ | ⟨i,k,H⟩
      · left; exact ⟨j,by omega⟩
      · right; left; exact ⟨i,k,by omega⟩
    · right; right
      have spec := sound m
      cases c with
      | purple => obtain ⟨i,H⟩ := spec; exact ⟨i,0,0,by omega⟩
      | green => obtain ⟨i,H⟩ := spec; exact ⟨i,0,1,by omega⟩
      | blue => obtain ⟨i,j,k,H⟩ := spec; exact ⟨i,j,k,by omega⟩
  · rintro (⟨j,hj,eh,hx⟩ | ⟨i,k,hi,hk,ex,hh⟩ | ⟨i,j,k,hi,hj,hk,ex,eh⟩)
    · by_cases H : 6*j < x
      · left; left; exact ⟨j,hj,eh,H⟩
      · right; exact mid 0 j 0 (by omega) hj (by omega) (by omega) (by omega)
    · by_cases H : 6*i+2*k < h
      · left; right; exact ⟨i,k,hi,hk,ex,H⟩
      · right; exact mid i 0 k hi (by omega) hk (by omega) (by omega)
    · right; exact mid i j k hi hj hk ex eh

/-- The original unbounded game loses exactly at the outer rays and at points
generated by the middle segment's three-color transition rules. -/
theorem original_coloring (x y : Nat) :
    originalLosing x y ↔ exterior x (y/2 : Nat) ∨ ∃ c, Marked c x (y/2 : Nat) :=
  (original_figure17 x y).trans (coloring_iff _ _).symm

private theorem disjoint (x h : Int) (H : exterior x h) (c : Color) :
    ¬ Marked c x h := by
  intro m
  have z := sound m
  have outside : 3*h-2*x < 0 ∨ 6*x-7*h < -2 := by
    rcases H with ⟨j, hj, eh, hx⟩ | ⟨i,k,hi,hk,ex,hh⟩ <;> omega
  cases c with
  | purple => obtain ⟨i,H⟩ := z; omega
  | green => obtain ⟨i,H⟩ := z; omega
  | blue => obtain ⟨i,j,k,H⟩ := z; omega

/-- Exactly the losing positions outside the two exterior ray families are
generated by the three middle-color rules. -/
theorem original_middle (x y : Nat) :
    (∃ c, Marked c (x : Int) (y/2 : Nat)) ↔
    originalLosing x y ∧ ¬ exterior x (y/2 : Nat) := by
  rw [original_coloring]
  constructor
  · rintro ⟨c,m⟩
    exact ⟨Or.inr ⟨c,m⟩, fun ext => disjoint _ _ ext c m⟩
  · rintro ⟨ext | m, noext⟩
    · exact False.elim (noext ext)
    · exact m

end Figure17


namespace Figure17

/-- The positive scaling of each of the paper's three moves. -/
def scaledLosing (d : Nat) (hd : 0 < d) (x y : Nat) : Prop :=
  ((d*1 ≤ x ∧ d*2 ≤ y) → ¬ scaledLosing d hd (x-d*1) (y-d*2)) ∧
  ((d*3 ≤ x ∧ d*4 ≤ y) → ¬ scaledLosing d hd (x-d*3) (y-d*4)) ∧
  ((d*4 ≤ x ∧ d*6 ≤ y) → ¬ scaledLosing d hd (x-d*4) (y-d*6))
termination_by x
decreasing_by all_goals omega

theorem scaled_iff_original (d : Nat) (hd : 0 < d) (x y : Nat) :
    scaledLosing d hd x y ↔ originalLosing (x/d) (y/d) := by
  induction x using Nat.strongRecOn generalizing y with
  | ind x ih =>
    have option (a b : Nat) (ha : 0 < a) :
        ((d*a ≤ x ∧ d*b ≤ y) → ¬ scaledLosing d hd (x-d*a) (y-d*b)) ↔
        ((a ≤ x/d ∧ b ≤ y/d) → ¬ originalLosing (x/d-a) (y/d-b)) := by
      have legalX : a ≤ x/d ↔ d*a ≤ x := by
        simpa only [Nat.mul_comm a d] using (Nat.le_div_iff_mul_le (x := a) (y := x) hd)
      have legalY : b ≤ y/d ↔ d*b ≤ y := by
        simpa only [Nat.mul_comm b d] using (Nat.le_div_iff_mul_le (x := b) (y := y) hd)
      rw [legalX,legalY]
      by_cases ok : d*a ≤ x ∧ d*b ≤ y
      · have positive : 0 < d*a := Nat.mul_pos hd ha
        have smaller := ih (x-d*a) (by omega) (y-d*b)
        rw [Nat.sub_mul_div, Nat.sub_mul_div] at smaller
        simp [ok, smaller]
      · simp [ok]
    rw [scaledLosing, originalLosing]
    exact and_congr (option 1 2 (by decide))
      (and_congr (option 3 4 (by decide)) (option 4 6 (by decide)))

theorem scaled_figure17 (d : Nat) (hd : 0 < d) (x y : Nat) :
    scaledLosing d hd x y ↔ families ((x/d : Nat) : Int) (((y/d)/2 : Nat) : Int) :=
  (scaled_iff_original d hd x y).trans (original_figure17 (x/d) (y/d))

/-- The polynomial identity in the independent generating-function proof,
    after clearing its four denominators. -/
theorem generating_identity {R : Type u} [Lean.Grind.CommRing R] (x y : R) :
    (1 + x*y) * (1 + x^3*y^2) *
      (x*(1-y)*(1-x^7*y^6) +
       y*(1+x^2*y^2)*(1-x)*(1-x^6*y^4) +
       (1+x^2*y^2)*(1-x)*(1-y)) =
    (1-x^7*y^6)*(1-x^6*y^4) + x^3*y^3*(1-x)*(1-x^6*y^4) := by
  grind

end Figure17

#print axioms Figure17.original_middle
#print axioms Figure17.original_quickTest
#print axioms Figure17.scaled_figure17
#print axioms Figure17.generating_identity
