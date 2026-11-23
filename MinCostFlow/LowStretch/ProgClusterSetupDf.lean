module

public import MinCostFlow.LowStretch.ProgClusterSetupEn
public import MinCostFlow.LowStretch.ProgClusterSetupBk

/-!
# The setup of a cluster: the setting that it leaves

The setup leaves the setting `W` of the petal searches (`suPW`), the arrays `A` of the tree
(`suTA`) and the outputs `Q` of the loop (`suLA`), all at the addresses of the layout `SuN`. The
pair of entry `j` is the word at `ACT + 2 j`, and the weight of a pair `p` is
`1 <<< (Es - EXP[p])`. The words of the block at `h` are the words that `setupBlock` asks
(`setupBlock_eq`).

The memory after the stores of the block is described by `SuFin`: the block at `h` and the
memory `P3` of `SuAt` elsewhere.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The arrays of the tree: `PP, PF, PA, PB` of `treeP` and the distances `FD` of the first
run. -/
def suTA (N : SuN) : PW.TA :=
  ⟨N.z 0 1 0 1, N.z 0 2 0 1, N.z 0 3 0 1, N.z 0 4 0 1, N.H + 16 * N.nS + 4 * N.s + 5⟩

/-- The outputs of the loop, after `RR`. -/
def suLA (N : SuN) : PW.LA := ⟨N.r 1 13, N.r 2 13, N.r 3 14, N.r 4 15, N.r 5 16⟩

/-- The layout of the runs of Dijkstra of the petal searches. -/
def suDL (N : SuN) (INF nA : ℕ) : DL :=
  ⟨N.D, N.J + 5, N.A2, INF, N.z 10 12 0 2, N.z 10 12 0 3, N.z 12 15 0 5, N.z 14 16 0 5,
    N.z 16 17 0 5, N.z 18 18 0 5, 0, N.z 23 21 2 11, N.s + 1, 1, 2 * nA + N.s⟩

/-- **The setting of the petal searches** that the setup leaves, for the layout `N`, `INF`, `m`,
`n`, `nA` active entries, the largest exponent `Es`, the exponents `EXP` of the global block,
the memory `M4` after `actP` (for the pairs of the entries) and the memory `mem` at the start
(for the exponents). -/
noncomputable def suPW (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (N : SuN)
    (INF m n nA Es EXP : ℕ) (M4 mem : ℕ → ℕ) : PW where
  T := T
  G := G
  P := P
  c := c
  R := R
  L := suDL N INF nA
  RR := N.RR
  ORD := N.z 18 20 0 7
  AS := N.z 20 21 0 7
  EXP := N.z 22 21 0 7
  Es := Es
  SUM := N.r 0 6
  M := 2 ^ Es
  κ := m / (n * n) + 1
  nact := nA
  bw := c.Δ G / 8 / P.L
  Lb := P.L
  SQ := N.z 23 21 0 7
  P2 := N.z 23 21 1 9
  NXT := N.z 18 19 0 6
  SL := N.r 0 11
  CTL := N.r 0 2
  nA := nA
  pr := fun j => M4 (N.z 0 8 0 2 + 2 * j)
  wtP := fun p => 1 <<< (Es - mem (EXP + p))
  Sm := 2 ^ 2 ^ P.L + c.Δ G
  Rm := 2 * c.Δ G - 1

/-- **The block holds the words of `setupBlock`.** -/
theorem setupBlock_eq {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {N : SuN}
    {INF m n nA Es EXP dt ts t : ℕ} {M4 mem : ℕ → ℕ} (hs : R.nodes.length = N.s)
    (hts : R.sv T c c.t = ts) (hdt : c.d G c.x0 c.t = dt) (ht : c.t = t) (hL : N.L = P.L) :
    setupBlock (suPW T G P c R N INF m n nA Es EXP M4 mem) (suTA N) (suLA N) =
      (suBlkL N INF m n nA Es (c.Δ G) dt ts t).take 47 := by
  subst ht hdt hts
  simp only [setupBlock, PW.LReg, suPW, suDL, suTA, suLA, suBlkL, PW.s, PW.sv, hs, hL, Cl.loS,
    Nat.one_shiftLeft]
  rfl

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State}

namespace SuAt

/-- The setting that the setup leaves. -/
noncomputable def W (a : SuAt w T G P c R GB RB h mem st) : PW :=
  suPW T G P c R ((suVOf GB RB h mem).N P.L) (suVOf GB RB h mem).INF (suVOf GB RB h mem).m
    (suVOf GB RB h mem).n a.hM.nA a.Es (suVOf GB RB h mem).EXP a.M4 mem

end SuAt

/-- **The memory after the stores of the block**: the words `suBlkL` at `h`, and the memory
before the stores elsewhere. -/
structure SuFin (a : SuAt w T G P c R GB RB h mem st) (F : ℕ → ℕ) : Prop where
  blk : ∀ i < 51, F (h + i) = (suBlkL ((suVOf GB RB h mem).N P.L) (suVOf GB RB h mem).INF
    (suVOf GB RB h mem).m (suVOf GB RB h mem).n a.hM.nA a.Es (c.Δ G) (c.d G c.x0 c.t)
    (suVOf GB RB h mem).ts (suVOf GB RB h mem).t).getD i 0
  fr : ∀ x, (x < h ∨ h + 51 ≤ x) → F x = a.P3 x

end MinCostFlow.LowStretch
