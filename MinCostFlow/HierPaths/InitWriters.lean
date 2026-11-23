module

public import MinCostFlow.HierPaths.InitBuildProc
public import MinCostFlow.HierPaths.InitHeader

/-!
# The writers done so far, as relocatable writers

`ownerW` (section 1), `zeroPowW` (sections 13, 14), `zeroGraphW` (sections 16, 17, 20, 22),
`pairCurW` (section 21) and `stackW` (section 23), for `buildProc`.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- The owner section: `ownerWriter` with `copyUp` as its helper. -/
def ownerW (a : ℕ) : SecW a where
  body k := ownerWriter k
  helpers _ := [copyUp]
  l S _ _ := S.sections.getD 1 []
  cost S _ _ := 17 * 2 ^ S.x + 60
  noRand _ := ⟨by simp [ownerWriter, Stmt.NoRand], by simpa using copyUp_noRand⟩
  spec w p f k hp hh S G :=
    ownerWriter_meetsContract (S := S) (G := G) hp (by simpa using hh 0 (by simp))

/-- A section of `2^x` zeros. -/
def zeroPowW (a : ℕ) : SecW a where
  body _ := zeroPowWriter
  helpers _ := []
  l S _ _ := List.replicate (2 ^ S.x) 0
  cost _ _ _ := 30
  noRand _ := ⟨by simp [zeroPowWriter, Stmt.NoRand], by simp⟩
  spec w p f k hp _ S G := zeroPowWriter_meetsContract (S := S) (G := G) hp

/-- A section of `n` (`off = 0`) or `m` (`off = 1`) zeros. -/
def zeroGraphW (a off : ℕ) (hoff : off < 2) : SecW a where
  body _ := zeroGraphWriter off
  helpers _ := []
  l _ G _ := List.replicate ((Graph.encode G).getD off 0) 0
  cost _ _ _ := 30
  noRand _ := ⟨by simp [zeroGraphWriter, Stmt.NoRand], by simp⟩
  spec w p f k hp _ S G := zeroGraphWriter_meetsContract (S := S) (G := G) hoff hp

/-- The pair cursors. -/
def pairCurW (a : ℕ) : SecW a where
  body _ := pairCurWriter
  helpers _ := []
  l S _ _ := List.replicate (numPairsOf S.x S.b) 0
  cost _ _ _ := 60
  noRand _ := ⟨by simp [pairCurWriter, Stmt.NoRand], by simp⟩
  spec w p f k hp _ S G := pairCurWriter_meetsContract (S := S) (G := G) hp

/-- The stack area. -/
def stackW (a : ℕ) : SecW a where
  body _ := stackWriter
  helpers _ := []
  l S _ _ := List.replicate ((leafDepth S.x S.b + 2) * 8) 0
  cost _ _ _ := 60
  noRand _ := ⟨by simp [stackWriter, Stmt.NoRand], by simp⟩
  spec w p f k hp _ S G := stackWriter_meetsContract (S := S) (G := G) hp

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- A relocatable word procedure (no helpers). -/
structure ValW (a : ℕ) where
  body : Stmt
  val : StaticData → Graph → List ℕ → ℕ
  cost : Graph → ℕ
  noRand : body.NoRand
  spec : ∀ w p f, p.procs[f]? = some body → ∀ S G,
    MeetsContract w p f (ValContract (buildInv w S a G) ⟨f, val S G, cost G⟩)

/-- The word procedures placed at `k, k + 1, …`. -/
def placedVals {a : ℕ} (S : StaticData) (G : Graph) : List (ValW a) → ℕ → List ValProc
  | [], _ => []
  | V :: Vs, k => ⟨k, V.val S G, V.cost G⟩ :: placedVals S G Vs (k + 1)

/-- The procedure numbers of the placed word procedures. -/
def placedValNums {a : ℕ} : List (ValW a) → ℕ → List ValProc
  | [], _ => []
  | _ :: Vs, k => ⟨k, fun _ => 0, 0⟩ :: placedValNums Vs (k + 1)

theorem writeVals_congr : ∀ (qs qs' : List ValProc) (i : ℕ),
    qs.map ValProc.f = qs'.map ValProc.f → writeVals qs i = writeVals qs' i
  | [], [], _, _ => rfl
  | q :: qs, q' :: qs', i, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [writeVals, h.1, writeVals_congr qs qs' (i + 1) h.2]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem placedVals_map_f {a : ℕ} (S : StaticData) (G : Graph) :
    ∀ (Vs : List (ValW a)) (k : ℕ),
      (placedVals S G Vs k).map ValProc.f = (placedValNums Vs k).map ValProc.f
  | [], _ => rfl
  | _ :: Vs, k => by simp [placedVals, placedValNums, placedVals_map_f S G Vs (k + 1)]

theorem placedVals_spec {a w : ℕ} {p : Program} (S : StaticData) (G : Graph) :
    ∀ (Vs : List (ValW a)) (k : ℕ), p.HasAt k (Vs.map ValW.body) →
      ∀ q ∈ placedVals S G Vs k, MeetsContract w p q.f (ValContract (buildInv w S a G) q)
  | [], _, _ => by simp [placedVals]
  | V :: Vs, k, hb => by
    intro q hq
    simp only [placedVals, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact V.spec w p k (by simpa using hb 0 (by simp)) S G
    · exact placedVals_spec S G Vs (k + 1) (hasAt_tail (by simpa using hb)) q hq

theorem placedVals_map_val {a : ℕ} (S : StaticData) (G : Graph) (base : List ℕ) :
    ∀ (Vs : List (ValW a)) (k : ℕ),
      (placedVals S G Vs k).map (fun q => q.val base) = Vs.map fun V => V.val S G base
  | [], _ => rfl
  | _ :: Vs, k => by simp [placedVals, placedVals_map_val S G base Vs (k + 1)]

theorem placedVals_map_cost {a : ℕ} (S : StaticData) (G : Graph) :
    ∀ (Vs : List (ValW a)) (k : ℕ),
      (placedVals S G Vs k).map (fun q => q.cost + 20) = Vs.map fun V => V.cost G + 20
  | [], _ => rfl
  | _ :: Vs, k => by simp [placedVals, placedVals_map_cost S G Vs (k + 1)]

theorem writeVals_noRand : ∀ (qs : List ValProc) (i : ℕ), (writeVals qs i).NoRand
  | [], _ => by simp [writeVals, Stmt.NoRand]
  | _ :: qs, i => by simp [writeVals, Stmt.NoRand, writeVals_noRand qs (i + 1)]

/-- **A short section word by word, as a relocatable writer**: the body `writeVals` with the
word procedures as its helpers. -/
def valsW {a : ℕ} (Vs : List (ValW a)) : SecW a where
  body k := writeVals (placedValNums Vs k) 0
  helpers _ := Vs.map ValW.body
  l S G base := Vs.map fun V => V.val S G base
  cost _ G _ := (Vs.map fun V => V.cost G + 20).sum + 5
  noRand k := ⟨writeVals_noRand _ 0, by
    intro s hs
    simp only [List.mem_map] at hs
    obtain ⟨V, _, rfl⟩ := hs
    exact V.noRand⟩
  spec w p f k hp hh S G := by
    have hp' : p.procs[f]? = some (writeVals (placedVals S G Vs k) 0) := by
      rw [hp, writeVals_congr _ _ 0 (placedVals_map_f S G Vs k).symm]
    have h := valsWriter_meetsContract (buildInv_stable w S a G)
      (placedVals_spec (w := w) S G Vs k hh) hp'
    have hl : (valsSec (placedVals S G Vs k) f).l = fun base => Vs.map fun V => V.val S G base :=
      funext fun base => placedVals_map_val S G base Vs k
    have hc : (valsSec (placedVals S G Vs k) f).cost =
        fun _ => (Vs.map fun V => V.cost G + 20).sum + 5 :=
      funext fun _ => by simp only [valsSec, placedVals_map_cost]
    have e : valsSec (placedVals S G Vs k) f =
        ⟨f, fun base => Vs.map fun V => V.val S G base,
          fun _ => (Vs.map fun V => V.cost G + 20).sum + 5, fun _ => 0⟩ := by
      rw [← hl, ← hc]; rfl
    rw [e] at h
    exact h


/-! ### The header -/

def argW (a i : ℕ) (hi : i < 6) : ValW a where
  body := .ret (.reg i)
  val _ _ base := base.getD i 0
  cost _ := 2
  noRand := by simp [Stmt.NoRand]
  spec w p f hp S G := argVal_meetsContract (S := S) (G := G) hi hp

def zeroW (a : ℕ) : ValW a where
  body := .ret (.const 0)
  val _ _ _ := 0
  cost _ := 2
  noRand := by simp [Stmt.NoRand]
  spec w p f hp S G := zeroVal_meetsContract (S := S) (G := G) hp

def graphW (a off : ℕ) (hoff : off < 2) : ValW a where
  body := .ret (.load (.bin .add (.reg 0) (.const off)))
  val _ G _ := (Graph.encode G).getD off 0
  cost _ := 5
  noRand := by simp [Stmt.NoRand]
  spec w p f hp S G := graphVal_meetsContract (S := S) (G := G) hoff hp

def staticW (a off : ℕ) (hoff : off = 7 ∨ off = 8) : ValW a where
  body := .ret (.load (.bin .add (.reg 4) (.const off)))
  val S _ _ := if off = 7 then S.x else S.b
  cost _ := 5
  noRand := by simp [Stmt.NoRand]
  spec w p f hp S G := staticVal_meetsContract (S := S) (G := G) hoff hp

def numTermW (a : ℕ) : ValW a where
  body := .ret (.bin .shiftLeft (.const 1) (.load (.bin .add (.reg 4) (.const 7))))
  val S _ _ := 2 ^ S.x
  cost _ := 7
  noRand := by simp [Stmt.NoRand]
  spec w p f hp S G := numTermVal_meetsContract (S := S) (G := G) hp

def depthW (a : ℕ) : ValW a where
  body := .ret depthExpr
  val S _ _ := leafDepth S.x S.b
  cost _ := 30
  noRand := by simp [Stmt.NoRand]
  spec w p f hp S G := depthVal_meetsContract (S := S) (G := G) hp

def numPairsW (a : ℕ) : ValW a where
  body := .ret numPairsExpr
  val S _ _ := numPairsOf S.x S.b
  cost _ := 60
  noRand := by simp [Stmt.NoRand]
  spec w p f hp S G := numPairsVal_meetsContract (S := S) (G := G) hp

def kappaW (a : ℕ) : ValW a where
  body := .ret (.bin .sub (.bin .shiftRight numPairsExpr
    (.load (.bin .add (.reg 4) (.const 7)))) depthExpr)
  val S _ _ := leafDepth S.x S.b * (2 ^ S.b - 1)
  cost _ := 100
  noRand := by simp [Stmt.NoRand]
  spec w p f hp S G := kappaVal_meetsContract (S := S) (G := G) hp

/-- Read the connector count from the third word of the static header. -/
def numConnW (a : ℕ) : ValW a where
  body := .ret (.load (.bin .add (.reg 4) (.const 9)))
  val S _ _ := S.numConn
  cost _ := 5
  noRand := by simp [Stmt.NoRand]
  spec w p f hp S G := by
    refine retProc_meetsContract (q := ⟨f, fun _ => S.numConn, 5⟩) hp ?_ (by simp [Expr.size])
    intro base c mem pos _ hI hw
    obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, rfl, hSO, hlen, -, -, -, -, -, -⟩ := hI
    have hh₁ : h₁ < 2 ^ w := hw h₁ (by simp)
    obtain ⟨-, -, henc⟩ := staticOut_owner_facts hSO
    have hs := listAt_csrList_get (k := 6) (f := fun i => S.sections.getD i []) hSO (i := 0)
      (by decide)
    have hread : mem (h + 9) = S.numConn := by
      simpa [StaticData.sections, Nat.add_assoc] using hs 2 (by simp [StaticData.sections])
    have hsmall : 9 ≤ S.encode.length :=
      (by decide : 9 ≤ 10).trans ((Nat.le_add_right 10 _).trans henc)
    have haddr := ((Nat.add_le_add_left hsmall h).trans hlen).trans_lt hh₁
    have hoff := (Nat.le_add_left 9 h).trans_lt haddr
    exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := h) rfl)
      (Expr.eval_const hoff) haddr) hread

/-- The static header and the initial model count the same connector records. -/
theorem numConnW_init (S : StaticData) (a : ℕ) (s : PathDSAbsState) (base : List ℕ) :
    (numConnW a).val S s.G base = (initConcrete S a s).H.A.C.numConn := rfl

/-- The header writer, from word procedures for `numConn`, `ξ` and `λ`. -/
def headerW {a : ℕ} (VC VX VL : ValW a) : SecW a :=
  valsW [graphW a 0 (by norm_num), graphW a 1 (by norm_num), numTermW a, VC, numPairsW a,
    staticW a 7 (by norm_num), staticW a 8 (by norm_num), depthW a, VX, kappaW a, VL,
    argW a 1 (by norm_num), argW a 2 (by norm_num), argW a 3 (by norm_num), zeroW a]

/-- **The header writer writes section 0** of the initial block, when the three word procedures
give `numConn`, `ξ` and `λ`. -/
theorem headerW_l {a : ℕ} {VC VX VL : ValW a} {S : StaticData} {G : Graph}
    {gAddr phiNum phiDen M h h₁ : ℕ}
    (hC : VC.val S G [gAddr, phiNum, phiDen, M, h, h₁] =
      (initConcrete S a (initAbs phiNum phiDen M G)).H.A.C.numConn)
    (hX : VX.val S G [gAddr, phiNum, phiDen, M, h, h₁] =
      (initConcrete S a (initAbs phiNum phiDen M G)).H.ξ)
    (hL : VL.val S G [gAddr, phiNum, phiDen, M, h, h₁] =
      (initConcrete S a (initAbs phiNum phiDen M G)).H.lam) :
    (headerW VC VX VL).l S G [gAddr, phiNum, phiDen, M, h, h₁] =
      (initConcrete S a (initAbs phiNum phiDen M G)).sections.getD 0 [] := by
  simp only [headerW, valsW, List.map_cons, List.map_nil, hC, hX, hL]
  simp [HierConcrete.sections, HierConcrete.header, HierConcrete.n, HierConcrete.m,
    HierConcrete.depth, initConcrete, initAbs, StaticData.model, staticArrays, connSystem,
    graphW, numTermW, numPairsW, staticW, depthW, kappaW, argW, zeroW, Graph.encode,
    DelState.init]

end MinCostFlow.HierPaths

end
