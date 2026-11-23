module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.Fin.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

/-!
# The Shift-and-Rebuild Game: Definitions

This file formalizes the definitions of Section 7.1 (pages 31–35) of the paper
(*A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow*, arXiv:2309.16629v1):

- **Definition 7.1** (`ValidStretch`, page 32): valid stretch values for a level.
- **Definition 7.2** (`GameParams`, `GameState`, `Move`, `ValidStep`, `Play`, pages 33–34):
  the shift-and-rebuild game, its five stages in order, its hidden weights `W`, representative
  rounds `repT`, stretches `str`, and game value `(s_0, ..., s_d)` and `(r_0, ..., r_d)`.
- **Algorithm 3** (`stepPasses`, `passesAt`, `FollowsStrategy`, page 34): the player's strategy
  using the counters `passes_i`.
- **Definition 7.4** (page 36): lemmas characterizing how `repT`, `bran`, `str`, and `passes`
  update across each game step.

Notes on faithful readings and minor typos in the paper:
1. Definition 7.1 writes `≤ O~(1)` and condition (14) writes `> Ω~(1)`. Both are represented by a
   single threshold parameter `σ : ℝ` in `GameParams`.
2. In Definition 7.2, Stage 4 (page 34), when the updated `bran_i` wraps around to `0`, the paper
   writes `str_{i', j} ≥ 0` with unbound `i'`; we read this as `i` (the level whose `repT_i`
   updated, matching Lemma 6.5 and the data structure's `hstr_{i, j}`).
3. The game tuples `(s_0, ..., s_d)` and `(r_0, ..., r_d)` live in `ℕ^(d + 1)` (`Fin (d + 1) → ℕ`),
   since level indices run over `[[d]] = {0, ..., d}`.
-/

namespace MinCostFlow.Game

@[expose] public section

/-- Parameters of the shift-and-rebuild game (Section 7, pages 32–33):
integer depth `d > 0` (levels `0, ..., d`), branching factor `k > 0` (branches `0, ..., k - 1`),
weight range `Ψ ≥ 1`, and stretch threshold `σ` (representing both `O~(1)` in Definition 7.1
and `Ω~(1)` in condition (14)). -/
structure GameParams where
  d : ℕ
  k : ℕ
  Ψ : ℝ
  σ : ℝ
  hd : 0 < d
  hk : 0 < k
  hΨ : 1 ≤ Ψ

/-- **Definition 7.1** (*Valid* stretch values, page 32).
Stretch values `str : Fin k → ℝ` for a level are valid if there exists a branch `j : Fin k`
satisfying `str j ≤ σ` (where `σ` stands for the paper's `O~(1)` bound). -/
def ValidStretch {k : ℕ} (σ : ℝ) (str : Fin k → ℝ) : Prop :=
  ∃ j : Fin k, str j ≤ σ

/-- Whether the current position in a round is Stage 2 (adversary rebuild step) or
Stages 3–5 (adversary round-completion test, player step, and round-end check). -/
inductive Phase where
  | stage2
  | stage34
  deriving DecidableEq, Repr

/-- Adversary's choice in Stage 3 (Definition 7.2, page 33). -/
inductive RoundChoice where
  | roundCompleting
  | roundContinuing
  deriving DecidableEq, Repr

/-- Player's step choice in Stage 4 (Definition 7.2, page 33). -/
inductive PlayerMove (d : ℕ) where
  | doNothing
  | shift (i : Fin (d + 1))
  deriving DecidableEq, Repr

/-- One step of the game, transitioning from step `s` to step `s + 1`.
In Stage 2, the adversary chooses `advDoNothing` or `advRebuild i newStr`.
In Stages 3–5, the adversary chooses `adv : RoundChoice`, the player chooses
`player : PlayerMove d`, and (when `player = shift i`) the adversary supplies new
stretch values `newStr` for updated levels. -/
inductive Move (d k : ℕ) where
  | advDoNothing
  | advRebuild (i : Fin (d + 1)) (newStr : Fin (d + 1) → Fin k → ℝ)
  | roundStep (adv : RoundChoice) (player : PlayerMove d)
      (newStr : Fin (d + 1) → Fin k → ℝ)

/-- State of all game variables at the start of a step `s` (Definition 7.2, pages 32–34). -/
structure GameState (d k : ℕ) where
  round : ℕ
  phase : Phase
  bran : Fin (d + 1) → Fin k
  repT : Fin (d + 1) → ℕ
  str : Fin (d + 1) → Fin k → ℝ

/-- Circularly increment a branch index `(b + 1) mod k`. -/
def nextBranch {k : ℕ} (hk : 0 < k) (b : Fin k) : Fin k :=
  ⟨(b.val + 1) % k, Nat.mod_lt _ hk⟩

/-- Auxiliary recursion for `argminRound`. -/
noncomputable def argminAux (W : ℕ → ℝ) (lo : ℕ) : ℕ → ℕ
  | 0 => lo
  | n + 1 =>
    let best := argminAux W lo n
    if W (lo + n + 1) < W best then lo + n + 1 else best

/-- Representative round achieving `argmin_{lo ≤ x ≤ hi} W x` (used in Definition 7.2, Stage 4,
and Definition 7.4 equation (15)). Defaults to `lo` when `hi < lo`. -/
noncomputable def argminRound (W : ℕ → ℝ) (lo hi : ℕ) : ℕ :=
  argminAux W lo (hi - lo)

/-- Initial game state at `t = 1` and `s = 0` (Definition 7.2, page 33):
`bran_i = 0`, `repT_i = 1`, and adversary initial stretches `initStr`. -/
def initState (d k : ℕ) (hk : 0 < k) (initStr : Fin (d + 1) → Fin k → ℝ) : GameState d k where
  round := 1
  phase := .stage2
  bran := fun _ => ⟨0, hk⟩
  repT := fun _ => 1
  str := initStr

/-- Update the game state across one move (Definition 7.2, Stages 2–5, pages 33–34). -/
noncomputable def stepState {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (st : GameState d k) (m : Move d k) : GameState d k :=
  match m with
  | .advDoNothing => { st with phase := .stage34 }
  | .advRebuild i newStr =>
    { st with
      phase := .stage34
      bran := fun i' => if i ≤ i' then ⟨0, hk⟩ else st.bran i'
      repT := fun i' => if i ≤ i' then st.round else st.repT i'
      str := fun i' => if i ≤ i' then newStr i' else st.str i' }
  | .roundStep adv player newStr =>
    let nextRound := match adv with
      | .roundCompleting => st.round + 1
      | .roundContinuing => st.round
    let nextPhase := match adv with
      | .roundCompleting => .stage2
      | .roundContinuing => .stage34
    match player with
    | .doNothing => { st with round := nextRound, phase := nextPhase }
    | .shift i =>
      let nextB := nextBranch hk (st.bran i)
      let wrapped := nextB.val = 0
      { round := nextRound
        phase := nextPhase
        bran := fun i' =>
          if i < i' then ⟨0, hk⟩
          else if i' = i then nextB
          else st.bran i'
        repT := fun i' =>
          if i < i' then st.round
          else if i' = i then
            if wrapped then argminRound W (st.repT i) st.round else st.repT i
          else st.repT i'
        str := fun i' =>
          if i < i' then newStr i'
          else if i' = i then
            if wrapped then newStr i else st.str i
          else st.str i' }

/-- Game state after executing the first `s` moves (`s = 0` gives the initial state). -/
noncomputable def stateAt {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k)) : ℕ → GameState d k
  | 0 => initState d k hk initStr
  | s + 1 =>
    match moves[s]? with
    | some m => stepState W hk (stateAt W hk initStr moves s) m
    | none => stateAt W hk initStr moves s

/-- Legality of a round's weight `W^{(t)}`: positive and `log₂ W^{(t)} ∈ (-Ψ, Ψ)`
(Definition 7.2, Stage 1, page 33). -/
def WeightValid (Ψ w : ℝ) : Prop :=
  0 < w ∧ -Ψ < Real.logb 2 w ∧ Real.logb 2 w < Ψ

/-- Condition (13) of Definition 7.2, Stage 3 (page 33):
`∑_{i=0}^d W^{(repT_i)} > 2 (d + 1) W^{(t)}`. -/
def LossSumCond {d k : ℕ} (W : ℕ → ℝ) (st : GameState d k) : Prop :=
  2 * ((d : ℝ) + 1) * W st.round < ∑ i : Fin (d + 1), W (st.repT i)

/-- Condition (14) of Definition 7.2, Stage 3 (page 33):
some level `i` has `str_{i, bran_i} > σ` (where `σ` stands for `Ω~(1)`). -/
def BadStretchCond {d k : ℕ} (σ : ℝ) (st : GameState d k) : Prop :=
  ∃ i : Fin (d + 1), σ < st.str i (st.bran i)

/-- Legality of a single move `m` from state `st` according to Definition 7.2 (pages 33–34). -/
def ValidStep (params : GameParams) (W : ℕ → ℝ)
    (st : GameState params.d params.k) (m : Move params.d params.k) : Prop :=
  match st.phase with
  | .stage2 =>
    WeightValid params.Ψ (W st.round) ∧
    match m with
    | .advDoNothing => True
    | .advRebuild i newStr =>
      ∀ i' : Fin (params.d + 1), i ≤ i' →
        (∀ j, 0 ≤ newStr i' j) ∧ ValidStretch params.σ (newStr i')
    | .roundStep _ _ _ => False
  | .stage34 =>
    match m with
    | .roundStep adv player newStr =>
      (adv = .roundContinuing → LossSumCond W st ∨ BadStretchCond params.σ st) ∧
      match player with
      | .doNothing => True
      | .shift i =>
        (∀ i' : Fin (params.d + 1), i < i' →
          (∀ j, 0 ≤ newStr i' j) ∧ ValidStretch params.σ (newStr i')) ∧
        ((nextBranch params.hk (st.bran i)).val = 0 →
          (∀ j, 0 ≤ newStr i j) ∧ ValidStretch params.σ (newStr i))
    | _ => False

/-- A valid prefix of moves starting from valid initial stretches `initStr`. -/
def ValidPlayPrefix (params : GameParams) (W : ℕ → ℝ)
    (initStr : Fin (params.d + 1) → Fin params.k → ℝ)
    (moves : List (Move params.d params.k)) : Prop :=
  ((∀ i j, 0 ≤ initStr i j) ∧ (∀ i, ValidStretch params.σ (initStr i))) ∧
  ∀ s (hs : s < moves.length),
    ValidStep params W (stateAt W params.hk initStr moves s) moves[s]

/-- **Definition 7.2** (*Shift-and-Rebuild Game* play, pages 33–34).
A completed play over `T` rounds together with the hidden weights `W` and stretches `str`. -/
structure Play (params : GameParams) where
  T : ℕ
  W : ℕ → ℝ
  initStr : Fin (params.d + 1) → Fin params.k → ℝ
  moves : List (Move params.d params.k)
  hInit : (∀ i j, 0 ≤ initStr i j) ∧ (∀ i, ValidStretch params.σ (initStr i))
  hMoves : ∀ s (hs : s < moves.length),
    ValidStep params W (stateAt W params.hk initStr moves s) moves[s]
  hComplete :
    (stateAt W params.hk initStr moves moves.length).phase = .stage2 ∧
    (stateAt W params.hk initStr moves moves.length).round = T + 1

/-- Number of `shift-step(i)` steps taken by the player (Definition 7.2, `s_i`, pages 32–34). -/
def shiftCount {d k : ℕ} (moves : List (Move d k)) (i : Fin (d + 1)) : ℕ :=
  moves.countP fun
    | .roundStep _ (.shift i') _ => i' == i
    | _ => false

/-- Number of `rebuild-step(i)` steps taken by the adversary (Definition 7.2, `r_i`, pages 32–34). -/
def rebuildCount {d k : ℕ} (moves : List (Move d k)) (i : Fin (d + 1)) : ℕ :=
  moves.countP fun
    | .advRebuild i' _ => i' == i
    | _ => false

/-- Update of the player's `passes` counters across one move (**Algorithm 3**, page 34). -/
def stepPasses {d k : ℕ} (hk : 0 < k) (st : GameState d k)
    (ps : Fin (d + 1) → ℕ) (m : Move d k) : Fin (d + 1) → ℕ :=
  match m with
  | .advDoNothing => ps
  | .advRebuild i _ => fun i' => if i ≤ i' then 0 else ps i'
  | .roundStep _ .doNothing _ => ps
  | .roundStep _ (.shift i) _ =>
    let wrapped := (nextBranch hk (st.bran i)).val = 0
    fun i' =>
      if i < i' then 0
      else if i' = i then
        if wrapped then ps i + 1 else ps i
      else ps i'

/-- Player's `passes` counters at the start of step `s` (**Algorithm 3**, page 34). -/
noncomputable def passesAt {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k)) :
    ℕ → (Fin (d + 1) → ℕ)
  | 0 => fun _ => 0
  | s + 1 =>
    match moves[s]? with
    | some m => stepPasses hk (stateAt W hk initStr moves s) (passesAt W hk initStr moves s) m
    | none => passesAt W hk initStr moves s

/-- **Algorithm 3** (page 34) condition for a single step `s`:
in Stages 3–5, if the adversary chose `roundContinuing`, the player picks `shift i` for the
largest level `i` with `passes_i < 2Ψ`; if `roundCompleting`, the player picks `doNothing`. -/
def StrategyStep (params : GameParams) (st : GameState params.d params.k)
    (ps : Fin (params.d + 1) → ℕ) (m : Move params.d params.k) : Prop :=
  match st.phase with
  | .stage2 => True
  | .stage34 =>
    match m with
    | .roundStep .roundCompleting player _ => player = .doNothing
    | .roundStep .roundContinuing player _ =>
      ∃ i : Fin (params.d + 1),
        (ps i : ℝ) < 2 * params.Ψ ∧
        (∀ j : Fin (params.d + 1), (ps j : ℝ) < 2 * params.Ψ → j ≤ i) ∧
        player = .shift i
    | _ => False

/-- Prefix predicate for following **Algorithm 3** (page 34) on every step `< moves.length`. -/
def FollowsStrategyPrefix (params : GameParams) (W : ℕ → ℝ)
    (initStr : Fin (params.d + 1) → Fin params.k → ℝ)
    (moves : List (Move params.d params.k)) : Prop :=
  ∀ s (hs : s < moves.length),
    StrategyStep params
      (stateAt W params.hk initStr moves s)
      (passesAt W params.hk initStr moves s)
      moves[s]

/-- Predicate that a completed play `p` follows **Algorithm 3** (page 34) at every step. -/
def FollowsStrategy (params : GameParams) (p : Play params) : Prop :=
  FollowsStrategyPrefix params p.W p.initStr p.moves

end

public section

lemma nextBranch_val {k : ℕ} (hk : 0 < k) (b : Fin k) :
    (nextBranch hk b).val = (b.val + 1) % k := rfl

lemma nextBranch_val_eq_zero_iff {k : ℕ} (hk : 0 < k) (b : Fin k) :
    (nextBranch hk b).val = 0 ↔ b.val + 1 = k := by
  rw [nextBranch_val]
  have hb : b.val + 1 ≤ k := b.isLt
  constructor
  · intro h
    rcases Nat.lt_or_eq_of_le hb with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt] at h
      omega
    · exact heq
  · intro h
    rw [h, Nat.mod_self]

private lemma argminAux_bounds (W : ℕ → ℝ) (lo : ℕ) :
    ∀ n : ℕ, lo ≤ argminAux W lo n ∧ argminAux W lo n ≤ lo + n
  | 0 => by simp [argminAux]
  | n + 1 => by
    have ih := argminAux_bounds W lo n
    dsimp [argminAux]
    split_ifs <;> omega

private lemma argminAux_le (W : ℕ → ℝ) (lo : ℕ) :
    ∀ n x : ℕ, lo ≤ x → x ≤ lo + n → W (argminAux W lo n) ≤ W x
  | 0, x, h1, h2 => by
    have hx : x = lo := by omega
    subst hx
    simp [argminAux]
  | n + 1, x, h1, h2 => by
    dsimp [argminAux]
    split_ifs with hlt
    · rcases Nat.lt_or_eq_of_le h2 with hlt' | rfl
      · have ih := argminAux_le W lo n x h1 (by omega)
        exact le_trans (le_of_lt hlt) ih
      · exact le_rfl
    · rcases Nat.lt_or_eq_of_le h2 with hlt' | rfl
      · exact argminAux_le W lo n x h1 (by omega)
      · exact not_lt.mp hlt

lemma argminRound_bounds (W : ℕ → ℝ) {lo hi : ℕ} (h : lo ≤ hi) :
    lo ≤ argminRound W lo hi ∧ argminRound W lo hi ≤ hi := by
  have hb := argminAux_bounds W lo (hi - lo)
  rw [argminRound]
  omega

lemma argminRound_le (W : ℕ → ℝ) {lo hi x : ℕ} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    W (argminRound W lo hi) ≤ W x := by
  have hle : lo ≤ hi := le_trans h1 h2
  rw [argminRound]
  refine argminAux_le W lo (hi - lo) x h1 ?_
  omega

lemma stateAt_zero {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k)) :
    stateAt W hk initStr moves 0 = initState d k hk initStr := rfl

lemma stateAt_succ {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    {s : ℕ} (hs : s < moves.length) :
    stateAt W hk initStr moves (s + 1) =
      stepState W hk (stateAt W hk initStr moves s) moves[s] := by
  rw [stateAt, List.getElem?_eq_getElem hs]

lemma passesAt_zero {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k)) :
    passesAt W hk initStr moves 0 = fun _ => 0 := rfl

lemma passesAt_succ {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    {s : ℕ} (hs : s < moves.length) :
    passesAt W hk initStr moves (s + 1) =
      stepPasses hk (stateAt W hk initStr moves s) (passesAt W hk initStr moves s) moves[s] := by
  rw [passesAt, List.getElem?_eq_getElem hs]

lemma Play.toValidPlayPrefix {params : GameParams} (p : Play params) :
    ValidPlayPrefix params p.W p.initStr p.moves :=
  ⟨p.hInit, p.hMoves⟩

lemma stateAt_take {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k)) (m : ℕ) :
    ∀ s ≤ m, stateAt W hk initStr (moves.take m) s = stateAt W hk initStr moves s
  | 0, _ => rfl
  | s + 1, hs => by
    have hsm : s < m := by omega
    have hprev := stateAt_take W hk initStr moves m s (by omega)
    rw [stateAt, stateAt, List.getElem?_take_of_lt hsm, hprev]

lemma passesAt_take {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k)) (m : ℕ) :
    ∀ s ≤ m, passesAt W hk initStr (moves.take m) s = passesAt W hk initStr moves s
  | 0, _ => rfl
  | s + 1, hs => by
    have hsm : s < m := by omega
    have hs1 := stateAt_take W hk initStr moves m s (by omega)
    have hp1 := passesAt_take W hk initStr moves m s (by omega)
    rw [passesAt, passesAt, List.getElem?_take_of_lt hsm, hs1, hp1]

lemma validPlayPrefix_take {params : GameParams} {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves) (m : ℕ) :
    ValidPlayPrefix params W initStr (moves.take m) := by
  refine ⟨hv.1, fun s hs => ?_⟩
  have hslen : s < moves.length := lt_of_lt_of_le hs (List.length_take_le' m moves)
  have hsm : (moves.take m).length ≤ m := List.length_take_le m moves
  rw [stateAt_take W params.hk initStr moves m s (by omega), List.getElem_take]
  exact hv.2 s hslen

lemma followsStrategyPrefix_take {params : GameParams} {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hf : FollowsStrategyPrefix params W initStr moves) (m : ℕ) :
    FollowsStrategyPrefix params W initStr (moves.take m) := by
  intro s hs
  have hslen : s < moves.length := lt_of_lt_of_le hs (List.length_take_le' m moves)
  have hsm : (moves.take m).length ≤ m := List.length_take_le m moves
  rw [stateAt_take W params.hk initStr moves m s (by omega),
      passesAt_take W params.hk initStr moves m s (by omega),
      List.getElem_take]
  exact hf s hslen

lemma round_le_step {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (st : GameState d k) (m : Move d k) :
    st.round ≤ (stepState W hk st m).round := by
  cases m with
  | advDoNothing => simp [stepState]
  | advRebuild _ _ => simp [stepState]
  | roundStep adv player _ =>
    cases adv <;> cases player <;> simp [stepState]

lemma round_pos {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k)) :
    ∀ s, 1 ≤ (stateAt W hk initStr moves s).round
  | 0 => by simp [stateAt, initState]
  | s + 1 => by
    have ih := round_pos W hk initStr moves s
    rw [stateAt]
    cases h : moves[s]? with
    | none => exact ih
    | some m => exact le_trans ih (round_le_step W hk _ m)

lemma round_mono {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) :
    (stateAt W hk initStr moves s₁).round ≤ (stateAt W hk initStr moves s₂).round := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rename_i n _
    refine le_trans ih ?_
    rw [stateAt]
    cases moves[n]? with
    | none => exact le_rfl
    | some m => exact round_le_step W hk _ m

lemma repT_bounds {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k)) :
    ∀ s (i : Fin (d + 1)),
      1 ≤ (stateAt W hk initStr moves s).repT i ∧
      (stateAt W hk initStr moves s).repT i ≤ (stateAt W hk initStr moves s).round
  | 0, i => by simp [stateAt, initState]
  | s + 1, i => by
    have ih := repT_bounds W hk initStr moves s
    have hr := round_pos W hk initStr moves s
    rw [stateAt]
    cases h : moves[s]? with
    | none => exact ih i
    | some m =>
      cases m with
      | advDoNothing => simpa [stepState] using ih i
      | advRebuild i₀ newStr =>
        dsimp [stepState]
        split_ifs
        · exact ⟨hr, le_rfl⟩
        · exact ih i
      | roundStep adv player newStr =>
        have hnr : (stateAt W hk initStr moves s).round ≤
            (stepState W hk (stateAt W hk initStr moves s) (.roundStep adv player newStr)).round :=
          round_le_step W hk _ _
        cases player with
        | doNothing =>
          dsimp [stepState]
          exact ⟨(ih i).1, le_trans (ih i).2 hnr⟩
        | shift i₀ =>
          dsimp [stepState]
          split_ifs with hlt heq hwrap
          · exact ⟨hr, le_trans le_rfl (by cases adv <;> simp)⟩
          · have hb := argminRound_bounds W (ih i₀).2
            exact ⟨le_trans (ih i₀).1 hb.1, le_trans hb.2 (by cases adv <;> simp)⟩
          · exact ⟨(ih i₀).1, le_trans (ih i₀).2 (by cases adv <;> simp)⟩
          · exact ⟨(ih i).1, le_trans (ih i).2 (by cases adv <;> simp)⟩

lemma str_nonneg_and_valid {params : GameParams} {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves) :
    ∀ s, s ≤ moves.length → ∀ i : Fin (params.d + 1),
      (∀ j, 0 ≤ (stateAt W params.hk initStr moves s).str i j) ∧
      ValidStretch params.σ ((stateAt W params.hk initStr moves s).str i)
  | 0, _, i => ⟨hv.1.1 i, hv.1.2 i⟩
  | s + 1, hs, i => by
    have hslt : s < moves.length := by omega
    have ih := str_nonneg_and_valid hv s (by omega)
    have hstep := hv.2 s hslt
    rw [stateAt_succ W params.hk initStr moves hslt]
    dsimp only [ValidStep] at hstep
    cases hph : (stateAt W params.hk initStr moves s).phase <;> rw [hph] at hstep
    · cases hm : moves[s] <;> rw [hm] at hstep
      · simpa [stepState] using ih i
      · rename_i i₀ newStr
        dsimp [stepState]
        split_ifs with hle
        · exact hstep.2 i hle
        · exact ih i
      · exact False.elim hstep.2
    · cases hm : moves[s] <;> rw [hm] at hstep
      · exact False.elim hstep
      · exact False.elim hstep
      · rename_i adv player newStr
        cases player with
        | doNothing => simpa [stepState] using ih i
        | shift i₀ =>
          dsimp [stepState]
          split_ifs with hlt heq hwrap
          · exact hstep.2.1 i hlt
          · exact hstep.2.2 hwrap
          · exact ih i₀
          · exact ih i

private lemma weightValid_invariants {params : GameParams} {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves) (hmne : moves ≠ []) :
    ∀ s, s ≤ moves.length →
      (∀ t, 1 ≤ t → t < (stateAt W params.hk initStr moves s).round → WeightValid params.Ψ (W t)) ∧
      ((stateAt W params.hk initStr moves s).phase = .stage34 →
        WeightValid params.Ψ (W (stateAt W params.hk initStr moves s).round)) ∧
      (∀ i : Fin (params.d + 1),
        WeightValid params.Ψ (W ((stateAt W params.hk initStr moves s).repT i)))
  | 0, _ => by
    have hpos : 0 < moves.length := List.length_pos_of_ne_nil hmne
    have h0 := hv.2 0 hpos
    simp only [stateAt_zero, initState, ValidStep] at h0
    refine ⟨?_, ?_, ?_⟩
    · intro t ht1 ht2
      simp only [stateAt_zero, initState] at ht2
      omega
    · intro h
      cases h
    · intro i
      exact h0.1
  | s + 1, hs => by
    have hslt : s < moves.length := by omega
    have ih := weightValid_invariants hv hmne s (by omega)
    have hstep := hv.2 s hslt
    have hrpos := round_pos W params.hk initStr moves s
    have hrepb := repT_bounds W params.hk initStr moves s
    rw [stateAt_succ W params.hk initStr moves hslt]
    dsimp only [ValidStep] at hstep
    cases hph : (stateAt W params.hk initStr moves s).phase <;> rw [hph] at hstep
    · have hcur : WeightValid params.Ψ (W (stateAt W params.hk initStr moves s).round) := hstep.1
      cases hm : moves[s] <;> rw [hm] at hstep
      · refine ⟨ih.1, fun _ => hcur, ih.2.2⟩
      · rename_i i₀ newStr
        refine ⟨ih.1, fun _ => hcur, fun i => ?_⟩
        dsimp [stepState]
        split_ifs
        · exact hcur
        · exact ih.2.2 i
      · exact False.elim hstep.2
    · have hcur : WeightValid params.Ψ (W (stateAt W params.hk initStr moves s).round) := ih.2.1 hph
      cases hm : moves[s] <;> rw [hm] at hstep
      · exact False.elim hstep
      · exact False.elim hstep
      · rename_i adv player newStr
        have hlt_all : ∀ t, 1 ≤ t →
            t < (stepState W params.hk (stateAt W params.hk initStr moves s)
              (.roundStep adv player newStr)).round →
            WeightValid params.Ψ (W t) := by
          intro t ht1 ht2
          have hround_eq :
              (stepState W params.hk (stateAt W params.hk initStr moves s)
                (.roundStep adv player newStr)).round =
              match adv with
              | .roundCompleting => (stateAt W params.hk initStr moves s).round + 1
              | .roundContinuing => (stateAt W params.hk initStr moves s).round := by
            cases adv <;> cases player <;> rfl
          rw [hround_eq] at ht2
          cases adv
          · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ht2) with hlt' | rfl
            · exact ih.1 t ht1 hlt'
            · exact hcur
          · exact ih.1 t ht1 ht2
        have hph34 :
            (stepState W params.hk (stateAt W params.hk initStr moves s)
              (.roundStep adv player newStr)).phase = .stage34 →
            WeightValid params.Ψ
              (W (stepState W params.hk (stateAt W params.hk initStr moves s)
                (.roundStep adv player newStr)).round) := by
          intro hnext
          cases adv <;> cases player <;> simp [stepState] at hnext ⊢
          all_goals exact hcur
        refine ⟨hlt_all, hph34, fun i => ?_⟩
        cases player with
        | doNothing => exact ih.2.2 i
        | shift i₀ =>
          dsimp [stepState]
          split_ifs with hlt heq hwrap
          · exact hcur
          · have hrb := argminRound_bounds W (hrepb i₀).2
            rcases Nat.lt_or_eq_of_le hrb.2 with hlt' | heq'
            · exact ih.1 _ (le_trans (hrepb i₀).1 hrb.1) hlt'
            · rw [heq']
              exact hcur
          · exact ih.2.2 i₀
          · exact ih.2.2 i

lemma weightValid_round_of_lt {params : GameParams} {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves) {s : ℕ} (hs : s < moves.length) :
    WeightValid params.Ψ (W (stateAt W params.hk initStr moves s).round) := by
  have hmne : moves ≠ [] := List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hs)
  have hstep := hv.2 s hs
  dsimp only [ValidStep] at hstep
  cases hph : (stateAt W params.hk initStr moves s).phase <;> rw [hph] at hstep
  · exact hstep.1
  · exact (weightValid_invariants hv hmne s (le_of_lt hs)).2.1 hph

lemma weightValid_repT {params : GameParams} {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves) (hmne : moves ≠ [])
    {s : ℕ} (hs : s ≤ moves.length) (i : Fin (params.d + 1)) :
    WeightValid params.Ψ (W ((stateAt W params.hk initStr moves s).repT i)) :=
  (weightValid_invariants hv hmne s hs).2.2 i

lemma Play.weightValid {params : GameParams} (p : Play params)
    {t : ℕ} (ht1 : 1 ≤ t) (ht2 : t ≤ p.T) :
    WeightValid params.Ψ (p.W t) := by
  have hmne : p.moves ≠ [] := by
    intro hnil
    have hcomp := p.hComplete
    rw [hnil] at hcomp
    simp [stateAt, initState] at hcomp
    omega
  have hinv := weightValid_invariants p.toValidPlayPrefix hmne p.moves.length le_rfl
  refine hinv.1 t ht1 ?_
  rw [p.hComplete.2]
  omega

/-- **Definition 7.4** (page 36) and state/passes transitions on `advDoNothing`. -/
lemma state_passes_advDoNothing {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (st : GameState d k) (ps : Fin (d + 1) → ℕ) :
    (stepState W hk st .advDoNothing).bran = st.bran ∧
    (stepState W hk st .advDoNothing).repT = st.repT ∧
    (stepState W hk st .advDoNothing).str = st.str ∧
    stepPasses hk st ps .advDoNothing = ps := by
  simp [stepState, stepPasses]

/-- **Definition 7.4** (page 36) and state/passes transitions on `advRebuild i`:
levels `i' ≥ i` reset `bran_{i'} = 0`, `repT_{i'} = t`, `str_{i'} = newStr i'`, `passes_{i'} = 0`;
levels `i' < i` are unchanged. -/
lemma state_passes_advRebuild {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (st : GameState d k) (ps : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (newStr : Fin (d + 1) → Fin k → ℝ) :
    (∀ i', i ≤ i' →
      (stepState W hk st (.advRebuild i newStr)).bran i' = ⟨0, hk⟩ ∧
      (stepState W hk st (.advRebuild i newStr)).repT i' = st.round ∧
      (stepState W hk st (.advRebuild i newStr)).str i' = newStr i' ∧
      stepPasses hk st ps (.advRebuild i newStr) i' = 0) ∧
    (∀ i', i' < i →
      (stepState W hk st (.advRebuild i newStr)).bran i' = st.bran i' ∧
      (stepState W hk st (.advRebuild i newStr)).repT i' = st.repT i' ∧
      (stepState W hk st (.advRebuild i newStr)).str i' = st.str i' ∧
      stepPasses hk st ps (.advRebuild i newStr) i' = ps i') := by
  constructor
  · intro i' hi'
    simp [stepState, stepPasses, hi']
  · intro i' hi'
    have hnot : ¬ (i ≤ i') := not_le.mpr hi'
    simp [stepState, stepPasses, hnot]

lemma state_passes_roundDoNothing {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (st : GameState d k) (ps : Fin (d + 1) → ℕ)
    (adv : RoundChoice) (newStr : Fin (d + 1) → Fin k → ℝ) :
    (stepState W hk st (.roundStep adv .doNothing newStr)).bran = st.bran ∧
    (stepState W hk st (.roundStep adv .doNothing newStr)).repT = st.repT ∧
    (stepState W hk st (.roundStep adv .doNothing newStr)).str = st.str ∧
    stepPasses hk st ps (.roundStep adv .doNothing newStr) = ps := by
  simp [stepState, stepPasses]

/-- **Definition 7.4** (page 36) and state/passes transitions on `shift i`:
levels `i' > i` reset `bran_{i'} = 0`, `repT_{i'} = t`, `str_{i'} = newStr i'`, `passes_{i'} = 0`;
levels `i' < i` are unchanged; level `i` increments `bran_i`, and if `bran_i` wraps to `0`
updates `repT_i := argmin_{repT_i ≤ x ≤ t} W^{(x)}`, `str_i := newStr i`, and `passes_i := passes_i + 1`. -/
lemma state_passes_shift {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (st : GameState d k) (ps : Fin (d + 1) → ℕ)
    (adv : RoundChoice) (i : Fin (d + 1)) (newStr : Fin (d + 1) → Fin k → ℝ) :
    (∀ i', i < i' →
      (stepState W hk st (.roundStep adv (.shift i) newStr)).bran i' = ⟨0, hk⟩ ∧
      (stepState W hk st (.roundStep adv (.shift i) newStr)).repT i' = st.round ∧
      (stepState W hk st (.roundStep adv (.shift i) newStr)).str i' = newStr i' ∧
      stepPasses hk st ps (.roundStep adv (.shift i) newStr) i' = 0) ∧
    ((stepState W hk st (.roundStep adv (.shift i) newStr)).bran i = nextBranch hk (st.bran i)) ∧
    ((nextBranch hk (st.bran i)).val = 0 →
      (stepState W hk st (.roundStep adv (.shift i) newStr)).repT i =
        argminRound W (st.repT i) st.round ∧
      (stepState W hk st (.roundStep adv (.shift i) newStr)).str i = newStr i ∧
      stepPasses hk st ps (.roundStep adv (.shift i) newStr) i = ps i + 1) ∧
    ((nextBranch hk (st.bran i)).val ≠ 0 →
      (stepState W hk st (.roundStep adv (.shift i) newStr)).repT i = st.repT i ∧
      (stepState W hk st (.roundStep adv (.shift i) newStr)).str i = st.str i ∧
      stepPasses hk st ps (.roundStep adv (.shift i) newStr) i = ps i) ∧
    (∀ i', i' < i →
      (stepState W hk st (.roundStep adv (.shift i) newStr)).bran i' = st.bran i' ∧
      (stepState W hk st (.roundStep adv (.shift i) newStr)).repT i' = st.repT i' ∧
      (stepState W hk st (.roundStep adv (.shift i) newStr)).str i' = st.str i' ∧
      stepPasses hk st ps (.roundStep adv (.shift i) newStr) i' = ps i') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i' hi'
    simp [stepState, stepPasses, hi']
  · simp [stepState]
  · intro hwrap
    simp [stepState, stepPasses, hwrap]
  · intro hnowrap
    simp [stepState, stepPasses, hnowrap]
  · intro i' hi'
    have hnot : ¬ (i < i') := not_lt.mpr (le_of_lt hi')
    have hne : i' ≠ i := ne_of_lt hi'
    simp [stepState, stepPasses, hnot, hne]

lemma shift_repT_weight_le {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (st : GameState d k) (adv : RoundChoice) (i : Fin (d + 1))
    (newStr : Fin (d + 1) → Fin k → ℝ) (hrep : st.repT i ≤ st.round) :
    W ((stepState W hk st (.roundStep adv (.shift i) newStr)).repT i) ≤ W (st.repT i) := by
  dsimp [stepState]
  split_ifs with hlt heq hwrap
  · exact absurd rfl (ne_of_gt hlt)
  · exact argminRound_le W le_rfl hrep
  · exact le_rfl
  · exact absurd rfl heq

@[simp]
lemma shiftCount_nil {d k : ℕ} (i : Fin (d + 1)) :
    shiftCount ([] : List (Move d k)) i = 0 := rfl

@[simp]
lemma rebuildCount_nil {d k : ℕ} (i : Fin (d + 1)) :
    rebuildCount ([] : List (Move d k)) i = 0 := rfl

lemma shiftCount_cons {d k : ℕ} (m : Move d k) (ms : List (Move d k)) (i : Fin (d + 1)) :
    shiftCount (m :: ms) i =
      (match m with
      | .roundStep _ (.shift i') _ => if i' = i then 1 else 0
      | _ => 0) + shiftCount ms i := by
  unfold shiftCount
  rw [List.countP_cons]
  cases m with
  | advDoNothing => simp
  | advRebuild _ _ => simp
  | roundStep _ player _ =>
    cases player with
    | doNothing => simp
    | shift i' =>
      by_cases h : i' = i
      · subst h
        simp [Nat.add_comm]
      · simp [h, beq_iff_eq]

lemma rebuildCount_cons {d k : ℕ} (m : Move d k) (ms : List (Move d k)) (i : Fin (d + 1)) :
    rebuildCount (m :: ms) i =
      (match m with
      | .advRebuild i' _ => if i' = i then 1 else 0
      | _ => 0) + rebuildCount ms i := by
  unfold rebuildCount
  rw [List.countP_cons]
  cases m with
  | advDoNothing => simp
  | advRebuild i' _ =>
    by_cases h : i' = i
    · subst h
      simp [Nat.add_comm]
    · simp [h, beq_iff_eq]
  | roundStep _ _ _ => simp

lemma shiftCount_append {d k : ℕ} (ms₁ ms₂ : List (Move d k)) (i : Fin (d + 1)) :
    shiftCount (ms₁ ++ ms₂) i = shiftCount ms₁ i + shiftCount ms₂ i := by
  unfold shiftCount
  exact List.countP_append

lemma rebuildCount_append {d k : ℕ} (ms₁ ms₂ : List (Move d k)) (i : Fin (d + 1)) :
    rebuildCount (ms₁ ++ ms₂) i = rebuildCount ms₁ i + rebuildCount ms₂ i := by
  unfold rebuildCount
  exact List.countP_append

end

end MinCostFlow.Game
