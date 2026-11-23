module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.EdgeColor
public import MinCostFlow.ExpanderDecomp.ProgRelabel
public import MinCostFlow.ExpanderDecomp.ProgRemoveFakeBase

import Mathlib.Tactic.Linarith

/-!
# Word-RAM Greedy 17-Edge-Colouring — Base Definitions and Colour-Search Stage (`ProgEdgeColorBase`)

Implements and verifies `edgeColor17Proc`, a deterministic (`NoRand`) Word-RAM procedure computing
`edgeColor17 G` (`EdgeColor.lean`) in `O(|G.edges| + 1)` time without scanning `range G.n`.

Using a pre-zeroed reusable table `usedAddr` of size `17 * G.n` (indexed as `17 * x + c` for
vertex `x < G.n` and colour `c < 17`):
1. Pass 1 scans `G.edges`, skips self-loops (`u = v`), scans `c = 0 .. 16` to find the smallest
   colour unused at both `u` and `v` (matching `pickColor 17`), marks `used[17 * u + c] := 1` and
   `used[17 * v + c] := 1`, and writes the triple `(u, v, c)` at `outAddr + 3 * outM`.
2. Pass 2 scans the `outM` written triples and resets `used[17 * u + c] := 0` and
   `used[17 * v + c] := 0`, restoring `usedAddr` to all zeros without touching `range G.n`.

The contract postcondition delivers `readColoredEdges mem' outAddr v = edgeColor17 G`,
`v = (edgeColor17 G).length ≤ G.m`, and `MemFrame mem mem' outAddr (outAddr + 3 * G.m)`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Flat Memory Representation and Pure Greedy Colouring Lemmas -/

/-- Flat layout of a coloured edge list `colored : List ((ℕ × ℕ) × ℕ)` at `addr` (3 words per
entry: `u, v, c`). -/
def ColoredEdgesAt (mem : ℕ → ℕ) (addr : ℕ) (colored : List ((ℕ × ℕ) × ℕ)) : Prop :=
  ∀ i (h : i < colored.length),
    mem (addr + 3 * i) = colored[i].1.1 ∧
    mem (addr + 3 * i + 1) = colored[i].1.2 ∧
    mem (addr + 3 * i + 2) = colored[i].2

/-- Read `m` coloured edges `(u, v, c)` from `[addr, addr + 3 * m)`. -/
def readColoredEdges (mem : ℕ → ℕ) (addr m : ℕ) : List ((ℕ × ℕ) × ℕ) :=
  (List.range m).map fun i =>
    ((mem (addr + 3 * i), mem (addr + 3 * i + 1)), mem (addr + 3 * i + 2))

lemma readColoredEdges_eq_of_coloredEdgesAt {mem : ℕ → ℕ} {addr : ℕ}
    {colored : List ((ℕ × ℕ) × ℕ)} (h : ColoredEdgesAt mem addr colored) :
    readColoredEdges mem addr colored.length = colored := by
  refine List.ext_getElem (by simp [readColoredEdges]) fun i hi _ => ?_
  have hi' : i < colored.length := by simpa [readColoredEdges] using hi
  rcases h i hi' with ⟨h1, h2, h3⟩
  simp only [readColoredEdges, List.getElem_map, List.getElem_range]
  exact Prod.ext (Prod.ext h1 h2) h3

/-- Whether colour `c` is already used on an edge in `colored` incident to vertex `x`. -/
def colorUsedAtVert (colored : List ((ℕ × ℕ) × ℕ)) (x c : ℕ) : Bool :=
  colored.any fun ec => decide (ec.2 = c) && decide (ec.1.1 = x ∨ ec.1.2 = x)

lemma colorUsedAt_eq_or (colored : List ((ℕ × ℕ) × ℕ)) (e : ℕ × ℕ) (c : ℕ) :
    colorUsedAt colored e c = (colorUsedAtVert colored e.1 c || colorUsedAtVert colored e.2 c) := by
  induction colored with
  | nil => simp [colorUsedAt, colorUsedAtVert]
  | cons ec rest ih =>
    simp only [colorUsedAt, colorUsedAtVert, List.any_cons] at ih ⊢
    rw [ih]
    unfold sharesEndpoint
    cases decide (ec.2 = c) <;>
    · by_cases h1 : ec.1.1 = e.1 <;> by_cases h2 : ec.1.2 = e.1 <;>
      by_cases h3 : ec.1.1 = e.2 <;> by_cases h4 : ec.1.2 = e.2 <;>
      simp [h1, h2, h3, h4]

lemma colorUsedAt_reverse (colored : List ((ℕ × ℕ) × ℕ)) (e : ℕ × ℕ) (c : ℕ) :
    colorUsedAt colored.reverse e c = colorUsedAt colored e c := by
  unfold colorUsedAt
  simp [List.any_reverse]

lemma pickColor_reverse (numColors : ℕ) (colored : List ((ℕ × ℕ) × ℕ)) (e : ℕ × ℕ) :
    pickColor numColors colored.reverse e = pickColor numColors colored e := by
  unfold pickColor
  simp [colorUsedAt_reverse]

lemma pickColor_lt {numColors : ℕ} (hpos : 0 < numColors) (colored : List ((ℕ × ℕ) × ℕ))
    (e : ℕ × ℕ) : pickColor numColors colored e < numColors := by
  unfold pickColor
  cases h : (List.range numColors).find? (fun c => !colorUsedAt colored e c) with
  | none => simpa using hpos
  | some c =>
    have hc := List.mem_of_find?_eq_some h
    simpa [List.mem_range] using hc

private lemma greedyColorAux_append (k : ℕ) (l₁ l₂ : List (ℕ × ℕ)) (acc : List ((ℕ × ℕ) × ℕ)) :
    greedyColorAux k (l₁ ++ l₂) acc =
      greedyColorAux k l₂ (greedyColorAux k l₁ acc).reverse := by
  induction l₁ generalizing acc with
  | nil => simp [greedyColorAux]
  | cons a t ih =>
    simp only [List.cons_append, greedyColorAux]
    exact ih ((a, pickColor k acc a) :: acc)

/-- Appending one edge to `greedyColorEdges` appends `(e, pickColor k prev e)`. -/
lemma greedyColorEdges_append_singleton (k : ℕ) (es : List (ℕ × ℕ)) (e : ℕ × ℕ) :
    greedyColorEdges k (es ++ [e]) =
      greedyColorEdges k es ++ [(e, pickColor k (greedyColorEdges k es) e)] := by
  unfold greedyColorEdges
  rw [greedyColorAux_append, greedyColorAux, greedyColorAux, List.reverse_cons,
    List.reverse_reverse, pickColor_reverse]

lemma colorUsedAtVert_append_singleton (colored : List ((ℕ × ℕ) × ℕ)) (e : ℕ × ℕ) (c x c' : ℕ) :
    colorUsedAtVert (colored ++ [(e, c)]) x c' =
      (colorUsedAtVert colored x c' || (decide (c = c') && decide (e.1 = x ∨ e.2 = x))) := by
  unfold colorUsedAtVert
  simp [List.any_append]

/-- Prefix of `edgeColor17 G` after processing the first `j` edges of `G.edges`. -/
def edgeColor17Prefix (G : Graph) (j : ℕ) : List ((ℕ × ℕ) × ℕ) :=
  greedyColorEdges 17 ((G.edges.take j).filter fun e => decide (e.1 ≠ e.2))

lemma edgeColor17Prefix_zero (G : Graph) : edgeColor17Prefix G 0 = [] := by
  simp [edgeColor17Prefix, greedyColorEdges, greedyColorAux]

lemma edgeColor17Prefix_full (G : Graph) : edgeColor17Prefix G G.m = edgeColor17 G := by
  simp [edgeColor17Prefix, edgeColor17, removeLoops, Graph.m]

lemma edgeColor17Prefix_length_le (G : Graph) (j : ℕ) :
    (edgeColor17Prefix G j).length ≤ j := by
  unfold edgeColor17Prefix
  have h1 : (greedyColorEdges 17 ((G.edges.take j).filter fun e => decide (e.1 ≠ e.2))).length =
      ((G.edges.take j).filter fun e => decide (e.1 ≠ e.2)).length := by
    have h := congrArg List.length
      (greedyColorEdges_map_fst 17 ((G.edges.take j).filter fun e => decide (e.1 ≠ e.2)))
    simpa [List.length_map] using h
  rw [h1]
  calc ((G.edges.take j).filter _).length ≤ (G.edges.take j).length := List.length_filter_le _ _
    _ ≤ j := by rw [List.length_take]; exact Nat.min_le_left _ _

lemma edgeColor17Prefix_succ {G : Graph} {j : ℕ} (hj : j < G.edges.length) :
    let e := G.edges[j]'hj
    edgeColor17Prefix G (j + 1) =
      if e.1 = e.2 then edgeColor17Prefix G j
      else edgeColor17Prefix G j ++ [(e, pickColor 17 (edgeColor17Prefix G j) e)] := by
  intro e
  unfold edgeColor17Prefix
  rw [List.take_succ_eq_append_getElem hj, List.filter_append, List.filter_cons, List.filter_nil]
  by_cases heq : e.1 = e.2
  · simp [e, heq]
  · simp only [e, ne_eq, heq, not_false_eq_true, decide_true, ↓reduceIte]
    exact greedyColorEdges_append_singleton 17 _ e

/-- Helper connecting the 17-step linear scan to `List.find?` on `List.range 17`. -/
private lemma range_find?_succ (p : ℕ → Bool) (c : ℕ) :
    (List.range (c + 1)).find? p =
      match (List.range c).find? p with
      | some x => some x
      | none => if p c then some c else none := by
  rw [List.range_succ, List.find?_append]
  cases (List.range c).find? p with
  | some x => simp
  | none =>
    simp only [Option.none_or, List.find?_cons, List.find?_nil]
    cases p c <;> rfl

/-! ## 2. Registers, Statements, and `NoRand` -/

def ecG : ℕ := 0
def ecUsed : ℕ := 1
def ecOut : ℕ := 2
def ecM : ℕ := 3
def ecOutM : ℕ := 4
def ecI : ℕ := 5
def ecU : ℕ := 6
def ecV : ℕ := 7
def ecC : ℕ := 8
def ecChosen : ℕ := 9
def ecFound : ℕ := 10
def ecFU : ℕ := 11
def ecFV : ℕ := 12

/-- Inner 17-step loop finding `pickColor 17` for edge `(ecU, ecV)` using `usedAddr`. -/
def ecFindColorStmt : Stmt :=
  seqStmts [
    .assign ecChosen (.const 0),
    .assign ecFound (.const 0),
    forRange ecC (.const 0) (.const 17) (
      .cond (.bin .eq (.reg ecFound) (.const 0))
        (seqStmts [
          .assign ecFU (.load (.bin .add (.bin .add (.reg ecUsed) (.bin .mul (.const 17) (.reg ecU))) (.reg ecC))),
          .assign ecFV (.load (.bin .add (.bin .add (.reg ecUsed) (.bin .mul (.const 17) (.reg ecV))) (.reg ecC))),
          .cond (.bin .eq (.bin .add (.reg ecFU) (.reg ecFV)) (.const 0))
            (seqStmts [
              .assign ecChosen (.reg ecC),
              .assign ecFound (.const 1)
            ])
            .nop
        ])
        .nop
    )
  ]

/-- Pass 1: greedy 17-edge-colouring of `removeLoops G`. -/
def ecColorLoopStmt : Stmt :=
  seqStmts [
    .assign ecOutM (.const 0),
    forRange ecI (.const 0) (.reg ecM) (
      seqStmts [
        .assign ecU (.load (.bin .add (.bin .add (.reg ecG) (.const 2)) (.bin .mul (.const 2) (.reg ecI)))),
        .assign ecV (.load (.bin .add (.bin .add (.reg ecG) (.const 3)) (.bin .mul (.const 2) (.reg ecI)))),
        .cond (.bin .eq (.reg ecU) (.reg ecV))
          .nop
          (seqStmts [
            ecFindColorStmt,
            .store (.bin .add (.bin .add (.reg ecUsed) (.bin .mul (.const 17) (.reg ecU))) (.reg ecChosen)) (.const 1),
            .store (.bin .add (.bin .add (.reg ecUsed) (.bin .mul (.const 17) (.reg ecV))) (.reg ecChosen)) (.const 1),
            .store (.bin .add (.reg ecOut) (.bin .mul (.const 3) (.reg ecOutM))) (.reg ecU),
            .store (.bin .add (.bin .add (.reg ecOut) (.bin .mul (.const 3) (.reg ecOutM))) (.const 1)) (.reg ecV),
            .store (.bin .add (.bin .add (.reg ecOut) (.bin .mul (.const 3) (.reg ecOutM))) (.const 2)) (.reg ecChosen),
            .assign ecOutM (.bin .add (.reg ecOutM) (.const 1))
          ])
      ]
    )
  ]

/-- Pass 2: clear `usedAddr` entries touched by the `ecOutM` coloured edges. -/
def ecClearUsedStmt : Stmt :=
  forRange ecI (.const 0) (.reg ecOutM) (
    seqStmts [
      .assign ecU (.load (.bin .add (.reg ecOut) (.bin .mul (.const 3) (.reg ecI)))),
      .assign ecV (.load (.bin .add (.bin .add (.reg ecOut) (.bin .mul (.const 3) (.reg ecI))) (.const 1))),
      .assign ecChosen (.load (.bin .add (.bin .add (.reg ecOut) (.bin .mul (.const 3) (.reg ecI))) (.const 2))),
      .store (.bin .add (.bin .add (.reg ecUsed) (.bin .mul (.const 17) (.reg ecU))) (.reg ecChosen)) (.const 0),
      .store (.bin .add (.bin .add (.reg ecUsed) (.bin .mul (.const 17) (.reg ecV))) (.reg ecChosen)) (.const 0)
    ]
  )

/-- Standalone procedure for `edgeColor17`: `args = [gAddr, usedAddr, outAddr]`. -/
def edgeColor17Proc : Stmt :=
  seqStmts [
    .assign ecM (.load (.bin .add (.reg ecG) (.const 1))),
    ecColorLoopStmt,
    ecClearUsedStmt,
    .ret (.reg ecOutM)
  ]

theorem edgeColor17Proc_noRand : edgeColor17Proc.NoRand := by
  simp [edgeColor17Proc, ecColorLoopStmt, ecFindColorStmt, ecClearUsedStmt,
    seqStmts, forRange, forUp, Stmt.NoRand]

/-! ## 3. Word Bounds, Disjointness, Cost, and Contract -/

structure EcRegs (gAddr usedAddr outAddr mG : ℕ) (st : State) : Prop where
  r_g : st.regs ecG = gAddr
  r_used : st.regs ecUsed = usedAddr
  r_out : st.regs ecOut = outAddr
  r_m : st.regs ecM = mG

lemma ecRegs_update_ge {ga ua oa mG r val : ℕ} {st : State}
    (hr : 4 ≤ r) (hR : EcRegs ga ua oa mG st) :
    EcRegs ga ua oa mG { st with regs := Function.update st.regs r val } :=
  ⟨by dsimp only; rw [Function.update_of_ne (by unfold ecG; omega)]; exact hR.r_g,
   by dsimp only; rw [Function.update_of_ne (by unfold ecUsed; omega)]; exact hR.r_used,
   by dsimp only; rw [Function.update_of_ne (by unfold ecOut; omega)]; exact hR.r_out,
   by dsimp only; rw [Function.update_of_ne (by unfold ecM; omega)]; exact hR.r_m⟩

lemma ecRegs_update_mem {ga ua oa mG a val : ℕ} {st : State}
    (hR : EcRegs ga ua oa mG st) :
    EcRegs ga ua oa mG { st with mem := Function.update st.mem a val } :=
  ⟨hR.r_g, hR.r_used, hR.r_out, hR.r_m⟩

/-- Word-size bounds for `edgeColor17Proc`. -/
def EdgeColorWordBound (w n mG gAddr usedAddr outAddr : ℕ) : Prop :=
  gAddr + 2 + 2 * mG < 2 ^ w ∧
  usedAddr + 17 * n < 2 ^ w ∧
  outAddr + 3 * mG < 2 ^ w ∧
  32 < 2 ^ w

/-- Buffer disjointness for `edgeColor17Proc`. -/
def EdgeColorDisjoint (n mG gAddr usedAddr outAddr : ℕ) : Prop :=
  DisjointRange usedAddr (17 * n) gAddr (2 + 2 * mG) ∧
  DisjointRange usedAddr (17 * n) outAddr (3 * mG) ∧
  DisjointRange outAddr (3 * mG) gAddr (2 + 2 * mG)

/-- Explicit local deterministic time bound `O(|G.edges| + 1)` (independent of `G.n`). -/
def edgeColor17Cost (mG : ℕ) : ℕ :=
  1100 * mG + 80

/-- Contract for `edgeColor17Proc`: `args = [gAddr, usedAddr, outAddr]`.
Writes `edgeColor17 G` (3 words `(u, v, c)` per edge) at `outAddr`, returns `(edgeColor17 G).length`,
restores `usedAddr` to all zeros, and preserves all memory outside `[outAddr, outAddr + 3 * G.m)`. -/
noncomputable def edgeColor17Contract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (gAddr usedAddr outAddr : ℕ) (G : Graph),
      args = [gAddr, usedAddr, outAddr] ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      (∀ idx < 17 * G.n, mem (usedAddr + idx) = 0) ∧
      EdgeColorWordBound w G.n G.m gAddr usedAddr outAddr ∧
      EdgeColorDisjoint G.n G.m gAddr usedAddr outAddr
  post args mem v mem' :=
    let gAddr := args.getD 0 0
    let outAddr := args.getD 2 0
    let G := Cited.readGraph mem gAddr
    v = (edgeColor17 G).length ∧
    v ≤ G.m ∧
    ColoredEdgesAt mem' outAddr (edgeColor17 G) ∧
    readColoredEdges mem' outAddr v = edgeColor17 G ∧
    MemFrame mem mem' outAddr (outAddr + 3 * G.m)
  cost args mem :=
    edgeColor17Cost (Cited.readGraph mem (args.getD 0 0)).m

/-! ## 4. Stage Triples -/

/-- Inner 17-step colour selection triple: computes `pickColor 17 colored (u, v)` into `ecChosen`. -/
lemma ecFindColor_triple {w n mG ga ua oa u v i outM : ℕ}
    (p : Program) (mem : ℕ → ℕ) (colored : List ((ℕ × ℕ) × ℕ)) (st₀ : State)
    (hu : u < n) (hv : v < n)
    (hused : ∀ x < n, ∀ c < 17, mem (ua + 17 * x + c) = if colorUsedAtVert colored x c then 1 else 0)
    (hw : EdgeColorWordBound w n mG ga ua oa)
    (hregs : EcRegs ga ua oa mG st₀)
    (hri : st₀.regs ecI = i) (hroutM : st₀.regs ecOutM = outM)
    (hru : st₀.regs ecU = u) (hrv : st₀.regs ecV = v) (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) ecFindColorStmt
      (normalPost fun st' =>
        EcRegs ga ua oa mG st' ∧ st'.regs ecI = i ∧ st'.regs ecOutM = outM ∧
        st'.regs ecU = u ∧ st'.regs ecV = v ∧
        st'.regs ecChosen = pickColor 17 colored (u, v) ∧
        st'.mem = mem ∧ st'.pos = st₀.pos)
      (fun _ => 880) := by
  rcases hw with ⟨_, hua_w, _, hw32⟩
  intro st ω hst; subst st
  refine runs_start_le ?_
  dsimp only [ecFindColorStmt, seqStmts]
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let st1 : State :=
    { mem := st₀.mem,
      regs := Function.update (Function.update st₀.regs ecChosen 0) ecFound 0,
      pos := st₀.pos }
  let Pfind : ℕ → Bool := fun c => !colorUsedAt colored (u, v) c
  let Inv : ℕ → State → Prop := fun c st =>
    EcRegs ga ua oa mG st ∧ st.regs ecI = i ∧ st.regs ecOutM = outM ∧
    st.regs ecU = u ∧ st.regs ecV = v ∧ st.regs ecC = c ∧
    st.regs ecChosen = ((List.range c).find? Pfind).getD 0 ∧
    st.regs ecFound = (if ((List.range c).find? Pfind).isSome then 1 else 0) ∧
    st.mem = mem ∧ st.pos = st₀.pos
  have hloop := Triple.forRange_const (w := w) (p := p) (r := ecC) (lo := .const 0) (hi := .const 17)
    (body :=
      .cond (.bin .eq (.reg ecFound) (.const 0))
        (seqStmts [
          .assign ecFU (.load (.bin .add (.bin .add (.reg ecUsed) (.bin .mul (.const 17) (.reg ecU))) (.reg ecC))),
          .assign ecFV (.load (.bin .add (.bin .add (.reg ecUsed) (.bin .mul (.const 17) (.reg ecV))) (.reg ecC))),
          .cond (.bin .eq (.bin .add (.reg ecFU) (.reg ecFV)) (.const 0))
            (seqStmts [.assign ecChosen (.reg ecC), .assign ecFound (.const 1)])
            .nop
        ])
        .nop)
    (P := fun st => st = st1) (Inv := Inv) 38 0 17 (Nat.zero_le 17) (by omega) (fun _ => by omega)
    (fun st hs => by
      subst hs
      refine ⟨Expr.eval_const (by omega),
        ecRegs_update_ge (r := ecC) (by decide)
          (ecRegs_update_ge (r := ecFound) (by decide)
            (ecRegs_update_ge (r := ecChosen) (by decide) hregs)),
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
             Function.update_of_ne (by decide), hri],
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
             Function.update_of_ne (by decide), hroutM],
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
             Function.update_of_ne (by decide), hru],
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
             Function.update_of_ne (by decide), hrv],
        by simp,
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
             Function.update_self]; simp,
        by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self]; simp,
        hmem, rfl⟩)
    (fun _ st _ _ hInv => hInv.2.2.2.2.2.1)
    (fun _ _ _ _ _ => Expr.eval_const (by omega))
    (fun c _ hclt => by
      intro st ω ⟨hr, hri', hroutM', hru', hrv', hrc, hch, hfnd, hstmem, hpos⟩
      refine runs_start_le ?_
      refine runs_cond_le (v := if (if ((List.range c).find? Pfind).isSome then 1 else 0) = 0 then 1 else 0)
        (Expr.eval_eq_op (Expr.eval_reg_of_eq hfnd) (Expr.eval_const (by omega)) (by omega))
        (fun hnf_ne => ?_) (fun hnf_0 => ?_)
      · -- Not found yet: `(List.range c).find? Pfind = none`
        have hnone : (List.range c).find? Pfind = none := by
          cases hf : (List.range c).find? Pfind with
          | none => rfl
          | some x => simp [hf] at hnf_ne
        set bu := colorUsedAtVert colored u c
        set bv := colorUsedAtVert colored v c
        have hmem_u : st.mem (ua + 17 * u + c) = if bu then 1 else 0 := by
          rw [hstmem]; exact hused u hu c hclt
        have hmem_v : st.mem (ua + 17 * v + c) = if bv then 1 else 0 := by
          rw [hstmem]; exact hused v hv c hclt
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := if bu then 1 else 0)
          (Expr.eval_load_of_eq
            (Expr.eval_add
              (Expr.eval_add (Expr.eval_reg_of_eq hr.r_used)
                (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hru') (by omega)) (by omega))
              (Expr.eval_reg_of_eq hrc) (by omega))
            hmem_u) ?_
        refine runs_seq_assign_le (v := if bv then 1 else 0)
          (Expr.eval_load_of_eq
            (Expr.eval_add
              (Expr.eval_add
                (Expr.eval_reg_of_eq (v := ua) (by dsimp only; rw [Function.update_of_ne (by decide), hr.r_used]))
                (Expr.eval_mul (Expr.eval_const (by omega))
                  (Expr.eval_reg_of_eq (v := v) (by dsimp only; rw [Function.update_of_ne (by decide), hrv'])) (by omega))
                (by omega))
              (Expr.eval_reg_of_eq (v := c) (by dsimp only; rw [Function.update_of_ne (by decide), hrc])) (by omega))
            hmem_v) ?_
        refine runs_cond_le (v := if (if bu then 1 else 0) + (if bv then 1 else 0) = 0 then 1 else 0)
          (Expr.eval_eq_op
            (Expr.eval_add
              (Expr.eval_reg_of_eq (v := if bu then 1 else 0)
                (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]))
              (Expr.eval_reg_of_eq (v := if bv then 1 else 0) (by simp))
              (by split_ifs <;> omega))
            (Expr.eval_const (by omega)) (by omega))
          (fun hfree_ne => ?_) (fun hfree_0 => ?_)
        · -- Free colour: `bu = false ∧ bv = false`, so `Pfind c = true`
          have hbu_f : bu = false := by cases h1 : bu <;> simp [h1] at hfree_ne ⊢
          have hbv_f : bv = false := by cases h1 : bv <;> simp [hbu_f, h1] at hfree_ne ⊢
          have hp_true : Pfind c = true := by
            simp [Pfind, colorUsedAt_eq_or, bu, bv, hbu_f, hbv_f]
          have hfind_succ : (List.range (c + 1)).find? Pfind = some c := by
            rw [range_find?_succ, hnone, hp_true]; rfl
          refine runs_seq_assign_le (v := c)
            (Expr.eval_reg_of_eq (v := c)
              (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hrc])) ?_
          refine runs_assign_le (v := 1) (Expr.eval_const (by omega)) ?_ (by simp [Expr.size])
          refine ⟨⟨ecRegs_update_ge (r := ecC) (by decide)
              (ecRegs_update_ge (r := ecFound) (by decide)
                (ecRegs_update_ge (r := ecChosen) (by decide)
                  (ecRegs_update_ge (r := ecFV) (by decide)
                    (ecRegs_update_ge (r := ecFU) (by decide) hr)))),
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), hri'],
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), hroutM'],
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), hru'],
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), hrv'],
            by simp,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_self, hfind_succ]; rfl,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self, hfind_succ]; rfl,
            hstmem, hpos⟩,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), Function.update_of_ne (by decide), hrc]⟩
        · -- Used colour: `bu = true ∨ bv = true`, so `Pfind c = false`
          have hp_false : Pfind c = false := by
            have hor : bu = true ∨ bv = true := by
              cases h1 : bu <;> cases h2 : bv <;> simp [h1, h2] at hfree_0 ⊢
            rcases hor with h1 | h1 <;> simp [Pfind, colorUsedAt_eq_or, bu, bv, h1]
          have hfind_succ : (List.range (c + 1)).find? Pfind = none := by
            rw [range_find?_succ, hnone, hp_false]; rfl
          refine runs_nop_le ?_ (by simp [Expr.size])
          refine ⟨⟨ecRegs_update_ge (r := ecC) (by decide)
              (ecRegs_update_ge (r := ecFV) (by decide)
                (ecRegs_update_ge (r := ecFU) (by decide) hr)),
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), hri'],
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), hroutM'],
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), hru'],
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), hrv'],
            by simp,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), hch, hnone, hfind_succ],
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                 Function.update_of_ne (by decide), hfnd, hnone, hfind_succ],
            hstmem, hpos⟩,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hrc]⟩
      · -- Already found: `(List.range c).find? Pfind = some x`
        have hsome : ∃ x, (List.range c).find? Pfind = some x := by
          cases hf : (List.range c).find? Pfind with
          | none => simp [hf] at hnf_0
          | some x => exact ⟨x, rfl⟩
        rcases hsome with ⟨x, hfx⟩
        have hfind_succ : (List.range (c + 1)).find? Pfind = some x := by
          rw [range_find?_succ, hfx]
        refine runs_nop_le ?_ (by simp [Expr.size])
        refine ⟨⟨ecRegs_update_ge (r := ecC) (by decide) hr,
          by dsimp only; rw [Function.update_of_ne (by decide), hri'],
          by dsimp only; rw [Function.update_of_ne (by decide), hroutM'],
          by dsimp only; rw [Function.update_of_ne (by decide), hru'],
          by dsimp only; rw [Function.update_of_ne (by decide), hrv'],
          by simp,
          by dsimp only; rw [Function.update_of_ne (by decide), hch, hfx, hfind_succ],
          by dsimp only; rw [Function.update_of_ne (by decide), hfnd, hfx, hfind_succ],
          hstmem, hpos⟩, hrc⟩)
  rcases hloop st1 ω rfl with ⟨o, st', c, hr, hq, hc⟩
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨hr', hri', hroutM', hru', hrv', _, hch', _, hstmem', hpos'⟩
    exact ⟨.normal, st', c, hr, ⟨hr', hri', hroutM', hru', hrv', hch', hstmem', hpos'⟩,
      by simp [Expr.size] at hc ⊢; omega⟩


end MinCostFlow.ExpanderDecomp
