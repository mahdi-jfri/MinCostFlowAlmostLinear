module

public import MinCostFlow.LowStretch.ProgClusterSetupO8

/-!
# The setup of a cluster: the tree and the state between petals

After the setup, the memory `F` holds the tree of the first run (`SuFin.tree`): the arrays of
`treeP` and `hwFix` hold it (`SuMem.ptree`), `NXT` copies the parents, and the cost of the slot
of a node is the cost of its parent arc. It also holds what holds between two petals with the
first stamp `1` (`SuFin.btw`): empty queues (`SuAt.pq`), zero stamps and the slots off.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State} {a : SuAt w T G P c R GB RB h mem st} {F : ℕ → ℕ}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

/-- The node of the center, as loaded. -/
theorem ClPre.x0_eq (hp : ClPre w A T G P c R GB RB h mem) :
    (suVOf GB RB h mem).x0 = R.sv T c c.x0 := by
  show mem ((GlobL.read mem GB).LOC + mem ((GlobL.read mem GB).LAB + (RecL.read mem RB).x0)) = _
  rw [hp.recAt.x0]; exact hp.recAt.arcs.loc c.x0 hp.ok.inv.good.conn.1

namespace SuFin

variable (hf : SuFin a F) (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
include hf hp hX

set_option maxHeartbeats 2000000 in
/-- **The tree of the first run, after the setup.** -/
theorem tree : a.W.Tree (suTA 𝔑) F := by
  have hs : (RecL.read mem RB).s = R.nodes.length := hp.recAt.arcs.s
  have vs : SuN.s 𝔑 = (RecL.read mem RB).s := rfl
  have hZ := suN_hZ GB RB h mem P.L
  have hWs : a.W.s = SuN.s 𝔑 := SuAt.W_s hp
  have vh : SuN.h 𝔑 = h := rfl
  have hr : R.sv T c c.x0 < R.nodes.length := hp.ok.sv_lt hp.ok.inv.good.conn.1
  have hT := a.hM.ptree hp hX
  set Z := SuN.Z 𝔑 with hZd
  set s := (RecL.read mem RB).s with hsd
  have lowF : ∀ x, h + 51 ≤ x → x < SuN.z 𝔑 2 8 0 2 → F x = a.M4 x := fun x h1 h2 =>
    hf.low h1 h2
  have hT' : PTree T G c R s (R.sv T c c.x0) Z (Z + s + 1) (Z + 2 * s + 1) (Z + 3 * s + 1)
      (Z + 4 * s + 1) (Z + 5 * s + 1) F := by
    refine PTree.congr hT (fun v hv => ?_) (by omega)
    have := fun k (hk : k ≤ 5) => lowF (Z + k * s + 1 + v) (by omega)
      (by simp only [SuN.z]; nlinarith)
    refine ⟨lowF _ (by omega) (by simp only [SuN.z]; omega), ?_, ?_, ?_, ?_, ?_⟩
    · have := this 1 (by omega); rw [one_mul] at this; exact this
    all_goals first
      | exact this 2 (by omega)
      | exact this 3 (by omega)
      | exact this 4 (by omega)
      | exact this 5 (by omega)
  have e : ∀ k, SuN.z 𝔑 0 k 0 1 = Z + k * s + 1 := fun k => by
    simp only [SuN.z, vs, Nat.zero_mul, Nat.add_zero]; rfl
  have hT2 : PTree T G c R R.nodes.length (R.sv T c c.x0) Z (SuN.z 𝔑 0 1 0 1)
      (SuN.z 𝔑 0 2 0 1) (SuN.z 𝔑 0 3 0 1) (SuN.z 𝔑 0 4 0 1) (SuN.z 𝔑 0 5 0 1) F := by
    rw [e, e, e, e, e, one_mul, ← hs]; exact hT'
  refine PW.PTree.tree (W := a.W) (A := suTA 𝔑) (PAR := Z) (SC := SuN.z 𝔑 0 5 0 1) hT2
    (fun v hv => ?_) (fun v hv hvr => ?_) (fun x hx => ?_) hr
  · have hv' : v < SuN.s 𝔑 := by omega
    show F (SuN.z 𝔑 18 19 0 6 + v) = F (Z + v)
    rw [hf.nxt hv', lowF _ (by omega) (by simp only [SuN.z]; omega)]
  · have hv' : v < SuN.s 𝔑 := by omega
    have hvr' : v ≠ (suVOf GB RB h mem).x0 := by rw [hp.x0_eq]; exact hvr
    show F (SuN.z 𝔑 14 16 0 5 + (F (SuN.z 𝔑 10 12 0 3 + v) - 1)) = F (SuN.z 𝔑 0 5 0 1 + v)
    rw [hf.hi (by omega), hf.cs (slot_lt (a := a) hv'), (a.suPg.slot v hv').2.2.1,
      lowF _ (by simp only [SuN.z]; omega) (by simp only [SuN.z]; omega)]
    unfold SF.sc
    have hvr'' : ¬ v = (suPGA (suVOf GB RB h mem) P.L a.hM.nA).toSF.x0 := hvr'
    simp only [hvr'', ↓reduceIte]
    have e1 : (suPGA (suVOf GB RB h mem) P.L a.hM.nA).toSF.PC + v = Z + 7 * s + 1 + v := by
      show SuN.z 𝔑 0 7 0 1 + v = _; simp only [SuN.z]; omega
    rw [e1, a.hM.pci hp hv']
    rfl
  · have hsv : R.sv T c x < s := hs ▸ hp.ok.sv_lt hx
    show F (SuN.H 𝔑 + 16 * SuN.nS 𝔑 + 4 * SuN.s 𝔑 + 5 + R.sv T c x) = c.d G c.x0 x
    rw [lowF _ (by simp only [SuN.H]; omega) (by simp only [SuN.z, SuN.Z, SuN.H]; omega)]
    exact hp.fdM4 a.hM hx

/-- **Between two petals, after the setup**, with the next stamp `1`. -/
theorem btw (hP : P = par G.n G.m) : a.W.Btw w F 1 := by
  have hok := hf.ok hp hX hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, l12⟩ := hok.lay
  refine ⟨hok, ?_, fun c' hc' => ?_, fun v hv => ?_, hf.sl hp⟩
  · exact DL.PQRep.congr a.pq fun x hx _ => hf.queue hx
  · have eD : a.W.L.D = SuN.D 𝔑 := rfl
    rw [hf.queue (by unfold pqT; omega)]; exact a.pqT0 c' hc'
  · have hv' : v < a.W.L.NN := hv
    have e : a.W.L.TS = SuN.z 𝔑 23 21 2 11 := rfl
    have eD : a.W.L.D = SuN.D 𝔑 := rfl
    rw [hf.zero hp (Or.inl ⟨by omega, by omega⟩), hf.zero hp (Or.inl ⟨by omega, by omega⟩)]
    omega

end SuFin

end MinCostFlow.LowStretch
