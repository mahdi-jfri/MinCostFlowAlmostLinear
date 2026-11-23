module

public import MinCostFlow.HierPaths.InitVals
public import MinCostFlow.HierPaths.InitOwner

/-!
# Word procedures for the header

The header of the block is `[n, m, numTerm, numConn, numPairs, x, b, depth, ξ, κ, λ, phiNum,
phiDen, M, 0]`. Most of its words are one expression of the arguments and the static output:
`retProc e` returns the value of `e`, and `retProc_meetsContract` proves `ValContract` for it
from the value of `e`. This file gives the word procedures for `n`, `m`, `2^x`, `x`, `b`,
`phiNum`, `phiDen`, `M` and `0`.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- **A word procedure `ret e`** meets `ValContract` when `e` has the value `val base` in the
start state of every call that meets the precondition. -/
theorem retProc_meetsContract {w : ℕ} {p : Program} {Inv : List ℕ → (ℕ → ℕ) → Prop}
    {e : Expr} {q : ValProc} (hp : p.procs[q.f]? = some (.ret e))
    (he : ∀ base c mem pos, base.length = 6 → Inv base mem → (∀ v ∈ base ++ [c], v < 2 ^ w) →
      e.eval w (startState (base ++ [c]) mem pos) = some (q.val base))
    (hcost : e.size + 1 ≤ q.cost) :
    MeetsContract w p q.f (ValContract Inv q) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, c, rfl, hl, hI⟩ := hpre
  exact runs_start_le (runs_ret_le (he base c mem pos hl hI hw) ⟨base, c, rfl, rfl, rfl⟩
    (by simpa [ValContract] using hcost))

/-- The arguments in the start state of a call. -/
theorem startState_regs_build (gAddr phiNum phiDen M h h₁ c : ℕ) (mem : ℕ → ℕ) (pos : ℕ) :
    (startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem pos).regs 0 = gAddr ∧
    (startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem pos).regs 1 = phiNum ∧
    (startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem pos).regs 2 = phiDen ∧
    (startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem pos).regs 3 = M ∧
    (startState ([gAddr, phiNum, phiDen, M, h, h₁] ++ [c]) mem pos).regs 4 = h :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The word `base[i]` for `i ∈ {1, 2, 3}` (`phiNum`, `phiDen`, `M`): `ret (reg i)`. -/
def argVal (i f : ℕ) : ValProc := ⟨f, fun base => base.getD i 0, 2⟩

theorem argVal_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program} {i f : ℕ}
    (hi : i < 6) (hp : p.procs[f]? = some (.ret (.reg i))) :
    MeetsContract w p f (ValContract (buildInv w S a G) (argVal i f)) := by
  refine retProc_meetsContract (q := argVal i f) hp ?_ (by simp [argVal, Expr.size])
  intro base c mem pos hl _ _
  simp only [Expr.eval, startState, argVal]
  rw [List.getD_append _ _ _ _ (by omega)]

/-- The word `0`. -/
def zeroVal (f : ℕ) : ValProc := ⟨f, fun _ => 0, 2⟩

theorem zeroVal_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some (.ret (.const 0))) :
    MeetsContract w p f (ValContract (buildInv w S a G) (zeroVal f)) := by
  refine retProc_meetsContract (q := zeroVal f) hp ?_ (by simp [zeroVal, Expr.size])
  intro base c mem pos _ _ hw
  have : (0 : ℕ) < 2 ^ w := Nat.two_pow_pos w
  simp [Expr.eval, zeroVal, this]

/-- The word `G.encode[off]` (`n` for `off = 0`, `m` for `off = 1`): `ret (load (r0 + off))`. -/
def graphVal (G : Graph) (off f : ℕ) : ValProc := ⟨f, fun _ => (Graph.encode G).getD off 0, 5⟩

theorem graphVal_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program} {off f : ℕ}
    (hoff : off < 2) (hp : p.procs[f]? = some (.ret (.load (.bin .add (.reg 0) (.const off))))) :
    MeetsContract w p f (ValContract (buildInv w S a G) (graphVal G off f)) := by
  refine retProc_meetsContract (q := graphVal G off f) hp ?_ (by simp [graphVal, Expr.size])
  intro base c mem pos _ hI hw
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, hG, hgh, -, -, -, -⟩ := hI
  have hglen : 2 ≤ (Graph.encode G).length := by simp [Graph.encode]
  have hh1 : h₁ < 2 ^ w := hw h₁ (by simp)
  have hread : mem (gAddr + off) = (Graph.encode G).getD off 0 := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hG off (by omega)
  exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := gAddr) rfl)
    (Expr.eval_const (by omega)) (by omega)) hread

/-- The word `x` (`off = 7`) or `b` (`off = 8`) of the static output: `ret (load (r4 + off))`. -/
def staticVal (S : StaticData) (off f : ℕ) : ValProc :=
  ⟨f, fun _ => if off = 7 then S.x else S.b, 5⟩

theorem staticVal_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program} {off f : ℕ}
    (hoff : off = 7 ∨ off = 8)
    (hp : p.procs[f]? = some (.ret (.load (.bin .add (.reg 4) (.const off))))) :
    MeetsContract w p f (ValContract (buildInv w S a G) (staticVal S off f)) := by
  refine retProc_meetsContract (q := staticVal S off f) hp ?_ (by simp [staticVal, Expr.size])
  intro base c mem pos _ hI hw
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, -, -, -, -, -, -⟩ := hI
  obtain ⟨hx, -, henc⟩ := staticOut_owner_facts hSO
  have hb := staticOut_b hSO
  have hh1 : h₁ < 2 ^ w := hw h₁ (by simp)
  have hpos : 0 < 2 ^ S.x := Nat.two_pow_pos S.x
  have hoff8 : off ≤ 8 := by omega
  have hread : mem (h + off) = if off = 7 then S.x else S.b := by
    rcases hoff with rfl | rfl
    · simpa using hx
    · simpa using hb
  exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl)
    (Expr.eval_const (by omega)) (by omega)) hread

/-- The word `2^x` (the number of terminals): `ret (1 <<< load (r4 + 7))`. -/
def numTermVal (S : StaticData) (f : ℕ) : ValProc := ⟨f, fun _ => 2 ^ S.x, 7⟩

theorem numTermVal_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some
      (.ret (.bin .shiftLeft (.const 1) (.load (.bin .add (.reg 4) (.const 7)))))) :
    MeetsContract w p f (ValContract (buildInv w S a G) (numTermVal S f)) := by
  refine retProc_meetsContract (q := numTermVal S f) hp ?_ (by simp [numTermVal, Expr.size])
  intro base c mem pos _ hI hw
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, -, -, -, -, -, -⟩ := hI
  obtain ⟨hx, -, henc⟩ := staticOut_owner_facts hSO
  have hh1 : h₁ < 2 ^ w := hw h₁ (by simp)
  have hpos : 0 < 2 ^ S.x := Nat.two_pow_pos S.x
  have e := Expr.eval_shiftLeft (w := w) (st := startState ([gAddr, phiNum, phiDen, M, h, h₁] ++
      [c]) mem pos) (a := .const 1) (b := .load (.bin .add (.reg 4) (.const 7))) (x := 1)
    (y := S.x) (Expr.eval_const (by omega))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl)
      (Expr.eval_const (by omega)) (by omega)) hx)
    (by rw [Nat.shiftLeft_eq, one_mul]; omega)
  rw [Nat.shiftLeft_eq, one_mul] at e
  exact e

/-! ### The depth, the number of pairs and `κ` -/

/-- The leaf depth from the static output at `r4`: `(x − 1) / b + [0 < x]`. -/
def depthExpr : Expr :=
  .bin .add (.bin .div (.bin .sub (.load (.bin .add (.reg 4) (.const 7))) (.const 1))
      (.load (.bin .add (.reg 4) (.const 8))))
    (.bin .lt (.const 0) (.load (.bin .add (.reg 4) (.const 7))))

theorem eval_xExpr {w h : ℕ} {st : State} {S : StaticData} (h4 : st.regs 4 = h)
    (hx : st.mem (h + 7) = S.x) (hh : h + 8 < 2 ^ w) :
    (Expr.load (.bin .add (.reg 4) (.const 7))).eval w st = some S.x :=
  Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_const (by omega))
    (by omega)) hx

theorem eval_bExpr {w h : ℕ} {st : State} {S : StaticData} (h4 : st.regs 4 = h)
    (hb : st.mem (h + 8) = S.b) (hh : h + 8 < 2 ^ w) :
    (Expr.load (.bin .add (.reg 4) (.const 8))).eval w st = some S.b :=
  Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_const (by omega))
    (by omega)) hb

theorem eval_depthExpr {w h : ℕ} {st : State} {S : StaticData} (h4 : st.regs 4 = h)
    (hx : st.mem (h + 7) = S.x) (hb : st.mem (h + 8) = S.b) (hh : h + 8 < 2 ^ w)
    (hxw : S.x < 2 ^ w) (hb0 : 0 < S.b) :
    depthExpr.eval w st = some (leafDepth S.x S.b) := by
  have hq : (S.x - 1) / S.b ≤ S.x - 1 := Nat.div_le_self _ _
  rw [leafDepth_eq_sub_div hb0]
  refine Expr.eval_add (Expr.eval_div (Expr.eval_sub (eval_xExpr h4 hx hh)
    (Expr.eval_const (by omega)) hxw) (eval_bExpr h4 hb hh) (by omega))
    (Expr.eval_lt_op (Expr.eval_const (by omega)) (eval_xExpr h4 hx hh) (by omega)) ?_
  split_ifs <;> omega

/-- The facts about a call of a header word procedure under `buildInv`. -/
theorem header_facts {w a : ℕ} {S : StaticData} {G : Graph} {base : List ℕ} {c : ℕ}
    {mem : ℕ → ℕ} (hI : buildInv w S a G base mem) (hw : ∀ v ∈ base ++ [c], v < 2 ^ w) :
    ∃ h, base.getD 4 0 = h ∧ mem (h + 7) = S.x ∧ mem (h + 8) = S.b ∧ h + 8 < 2 ^ w ∧
      S.x < 2 ^ w ∧ 0 < S.b ∧ numPairsOf S.x S.b < 2 ^ w := by
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, -, -, -, -, hgood, hbw, -, -⟩ := hI
  obtain ⟨hx, -, henc⟩ := staticOut_owner_facts hSO
  have hpos : 0 < 2 ^ S.x := Nat.two_pow_pos S.x
  have hh1 : h₁ < 2 ^ w := hw h₁ (by simp)
  have hxw : S.x < 2 ^ S.x := Nat.lt_two_pow_self
  have hsec : numPairsOf S.x S.b ≤ (initBlock S a G phiNum phiDen M).length := by
    rw [initBlock_eq_layoutList, length_layoutList]
    have h21 := initConcrete_section_pairCur S a (initAbs phiNum phiDen M G)
    have hle : ((initConcrete S a (initAbs phiNum phiDen M G)).sections.getD 21 []).length ≤
        ((initConcrete S a (initAbs phiNum phiDen M G)).sections.map List.length).sum := by
      rw [List.getD_eq_getElem _ _ (by simp [HierConcrete.sections])]
      exact List.le_sum_of_mem (List.mem_map_of_mem (List.getElem_mem _))
    rw [h21, List.length_replicate] at hle
    omega
  exact ⟨h, rfl, hx, staticOut_b hSO, by omega, by omega, hgood.b_pos, by omega⟩

/-- The word `leafDepth x b`: `ret depthExpr`. -/
def depthVal (S : StaticData) (f : ℕ) : ValProc := ⟨f, fun _ => leafDepth S.x S.b, 30⟩

theorem depthVal_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some (.ret depthExpr)) :
    MeetsContract w p f (ValContract (buildInv w S a G) (depthVal S f)) := by
  refine retProc_meetsContract (q := depthVal S f) hp ?_ (by simp [depthVal, depthExpr, Expr.size])
  intro base c mem pos hl hI hw
  obtain ⟨h, hh, hx, hb, hh8, hxw, hb0, -⟩ := header_facts hI hw
  refine eval_depthExpr (h := h) ?_ hx hb hh8 hxw hb0
  rw [← hh]
  simp only [startState]
  rw [List.getD_append _ _ _ _ (by omega)]

/-- The number of pairs `leafDepth · 2^x · 2^b`: `ret ((depthExpr <<< x) <<< b)`. -/
def numPairsExpr : Expr :=
  .bin .shiftLeft (.bin .shiftLeft depthExpr (.load (.bin .add (.reg 4) (.const 7))))
    (.load (.bin .add (.reg 4) (.const 8)))

def numPairsVal (S : StaticData) (f : ℕ) : ValProc := ⟨f, fun _ => numPairsOf S.x S.b, 60⟩

theorem eval_numPairsExpr {w h : ℕ} {st : State} {S : StaticData} (h4 : st.regs 4 = h)
    (hx : st.mem (h + 7) = S.x) (hb : st.mem (h + 8) = S.b) (hh : h + 8 < 2 ^ w)
    (hxw : S.x < 2 ^ w) (hb0 : 0 < S.b) (hP : numPairsOf S.x S.b < 2 ^ w) :
    numPairsExpr.eval w st = some (numPairsOf S.x S.b) := by
  have hb1 : 1 ≤ 2 ^ S.b := Nat.one_le_two_pow
  have hP' : numPairsOf S.x S.b = leafDepth S.x S.b * 2 ^ S.x * 2 ^ S.b := rfl
  have hDx : leafDepth S.x S.b * 2 ^ S.x ≤ numPairsOf S.x S.b := by
    rw [hP']; exact Nat.le_mul_of_pos_right _ hb1
  have e1 := Expr.eval_shiftLeft (eval_depthExpr h4 hx hb hh hxw hb0) (eval_xExpr h4 hx hh)
    (by rw [Nat.shiftLeft_eq]; omega)
  have e2 := Expr.eval_shiftLeft e1 (eval_bExpr h4 hb hh)
    (by rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, ← hP']; exact hP)
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, ← hP'] at e2
  exact e2

theorem numPairsVal_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some (.ret numPairsExpr)) :
    MeetsContract w p f (ValContract (buildInv w S a G) (numPairsVal S f)) := by
  refine retProc_meetsContract (q := numPairsVal S f) hp ?_
    (by simp [numPairsVal, numPairsExpr, depthExpr, Expr.size])
  intro base c mem pos hl hI hw
  obtain ⟨h, hh, hx, hb, hh8, hxw, hb0, hP⟩ := header_facts hI hw
  refine eval_numPairsExpr (h := h) ?_ hx hb hh8 hxw hb0 hP
  rw [← hh]
  simp only [startState]
  rw [List.getD_append _ _ _ _ (by omega)]

/-- `κ = leafDepth · (2^b − 1)`, as `(numPairs >>> x) − leafDepth`. -/
def kappaVal (S : StaticData) (f : ℕ) : ValProc :=
  ⟨f, fun _ => leafDepth S.x S.b * (2 ^ S.b - 1), 100⟩

theorem kappaVal_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some (.ret (.bin .sub (.bin .shiftRight numPairsExpr
      (.load (.bin .add (.reg 4) (.const 7)))) depthExpr))) :
    MeetsContract w p f (ValContract (buildInv w S a G) (kappaVal S f)) := by
  refine retProc_meetsContract (q := kappaVal S f) hp ?_
    (by simp [kappaVal, numPairsExpr, depthExpr, Expr.size])
  intro base c mem pos hl hI hw
  obtain ⟨h, hh, hx, hb, hh8, hxw, hb0, hP⟩ := header_facts hI hw
  have h4 : (startState (base ++ [c]) mem pos).regs 4 = h := by
    rw [← hh]
    simp only [startState]
    rw [List.getD_append _ _ _ _ (by omega)]
  have e1 := Expr.eval_shiftRight (eval_numPairsExpr h4 hx hb hh8 hxw hb0 hP)
    (eval_xExpr h4 hx hh8) hP
  have hshr : numPairsOf S.x S.b >>> S.x = leafDepth S.x S.b * 2 ^ S.b := by
    rw [Nat.shiftRight_eq_div_pow, show numPairsOf S.x S.b =
      leafDepth S.x S.b * 2 ^ S.b * 2 ^ S.x by simp [numPairsOf]; ring]
    exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)
  rw [hshr] at e1
  have hle : leafDepth S.x S.b * 2 ^ S.b ≤ numPairsOf S.x S.b := by
    rw [show numPairsOf S.x S.b = leafDepth S.x S.b * 2 ^ S.b * 2 ^ S.x by
      simp [numPairsOf]; ring]
    exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have e2 := Expr.eval_sub e1 (eval_depthExpr h4 hx hb hh8 hxw hb0) (by omega)
  rw [show leafDepth S.x S.b * 2 ^ S.b - leafDepth S.x S.b =
    leafDepth S.x S.b * (2 ^ S.b - 1) by rw [Nat.mul_sub_one]] at e2
  exact e2

end MinCostFlow.HierPaths

end
