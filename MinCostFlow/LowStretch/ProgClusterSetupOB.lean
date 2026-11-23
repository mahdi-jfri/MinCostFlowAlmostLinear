module

public import MinCostFlow.LowStretch.ProgClusterSetupOA

/-!
# The setup of a cluster: what the setup leaves

The memory `F` after the stores of the block meets `SetupOut` (`SuFin.out`), with the setting
`a.W`, the tree arrays `suTA`, the outputs `suLA`, the end `hS` of the heap, the number `nH` of
steps of the highway and the array `ACT = Z + 8 s + 2` of the active entries. Each part comes
from a file before this one. The product `wT1` needs the room `SuRoom3`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State} {a : SuAt w T G P c R GB RB h mem st} {F : ℕ → ℕ}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

/-- The target and its node, as loaded. -/
theorem ClPre.t_eq (hp : ClPre w A T G P c R GB RB h mem) :
    (suVOf GB RB h mem).t = c.t ∧ (suVOf GB RB h mem).ts = R.sv T c c.t := by
  have ht : (RecL.read mem RB).t = c.t := hp.recAt.t
  refine ⟨ht, ?_⟩
  show mem ((GlobL.read mem GB).LOC + mem ((GlobL.read mem GB).LAB + (RecL.read mem RB).t)) = _
  rw [ht]; exact hp.recAt.arcs.loc c.t hp.ok.inv.t_mem

namespace SuFin

variable (hf : SuFin a F) (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
  (hP : P = par G.n G.m)
include hf hp hX hP

set_option maxHeartbeats 4000000 in
/-- **What the setup leaves.** -/
theorem out (h3 : SuRoom3 w T G h) : SetupOut w ⟨T, G, P, c, R⟩ h mem F := by
  have hZ := suN_hZ GB RB h mem P.L
  have hs := SuAt.W_s (a := a) hp
  have hnA := SuAt.nA_le (a := a)
  have vs : SuN.s 𝔑 = (RecL.read mem RB).s := rfl
  have vh : SuN.h 𝔑 = h := rfl
  have vnS : SuN.nS 𝔑 = (RecL.read mem RB).nS := rfl
  have hsl : (RecL.read mem RB).s = R.nodes.length := hp.recAt.arcs.s
  have hnS : (RecL.read mem RB).nS = R.S.length := hp.recAt.arcs.nS
  obtain ⟨ht, hts⟩ := hp.t_eq
  have htX : c.t ∈ c.X := hp.ok.inv.t_mem
  have htS : R.sv T c c.t < R.nodes.length := hp.ok.sv_lt htX
  have hS := hp.hS_lt hX
  have hok := hf.ok hp hX hP
  have hL := a.lLay hp hX
  obtain ⟨b1, b2, b3, b4, b5⟩ := a.loS_w hp hX hP
  have wT1 := a.wT1 hp hX h3
  obtain ⟨hpath, hdec⟩ := hf.path hp
  have hblk : ∀ i < 51, F (h + i) = (suBlkL 𝔑 (suVOf GB RB h mem).INF (suVOf GB RB h mem).m
      (suVOf GB RB h mem).n a.hM.nA a.Es (c.Δ G) (c.d G c.x0 c.t) (R.sv T c c.t) c.t).getD i 0 :=
    fun i hi => by rw [hf.blk i hi, ht, hts]
  have hbe := setupBlock_eq (T := T) (G := G) (P := P) (c := c) (R := R) (N := 𝔑)
    (INF := (suVOf GB RB h mem).INF) (m := (suVOf GB RB h mem).m) (n := (suVOf GB RB h mem).n)
    (nA := a.hM.nA) (Es := a.Es) (EXP := (suVOf GB RB h mem).EXP) (M4 := a.M4) (mem := mem)
    (dt := c.d G c.x0 c.t) (ts := R.sv T c c.t) (t := c.t) (hsl ▸ vs).symm rfl rfl rfl rfl
  refine ⟨⟨a.W, suTA 𝔑, suLA 𝔑, SuN.hS 𝔑, (RecL.read mem RB).nH, SuN.z 𝔑 0 8 0 2,
    ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩⟩
  -- the classes
  · show (GlobL.read mem GB).J + 5 = _; rw [hp.J_eq]
  -- the active entries
  · intro i hi
    have hi' : i < a.hM.nA := hi
    have e := (hp.actEnt a.hM hi').1.fl
    refine ⟨hf.low (by simp only [SuN.z]; omega) (by simp only [SuN.z]; omega), ?_⟩
    rw [hf.low (by simp only [SuN.z]; omega) (by simp only [SuN.z]; omega)]
    exact e
  -- the words of the block after the registers
  · rw [hblk 47 (by omega)]; rfl
  · rw [hblk 48 (by omega)]; rfl
  · rw [hblk 49 (by omega)]; rfl
  · rw [hblk 50 (by omega)]; rfl
  -- where the arrays lie
  all_goals try (simp only [SuAt.W, suTA, suLA, suPW, suDL, PW.s, SuN.z, SuN.H, SuN.hS,
    SuN.r, SuN.Z, SuN.A2, SuN.RR, SuN.D, SuN.Jq]; omega)
  -- the block
  · intro i hi
    rw [show setupBlock a.W (suTA 𝔑) (suLA 𝔑) = _ from hbe, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt hi, ← List.getD_eq_getElem?_getD]
    exact hblk i (by omega)
  · exact fun x hx => hf.lowh hx
  · exact fun x hx => hf.zero hp (Or.inr (by
      simp only [SuN.hS, SuN.r] at hx; omega))
  · have e1 : SuN.J 𝔑 = rootJ G.n := hp.J_eq
    have e2 : SuN.L 𝔑 = P.L := rfl
    have := SuN.hS_le 𝔑
    rw [e1, e2, vh, vnS, vs, hnS, hsl] at this
    exact this
  · exact fun sp st' hm hr h13 h32 h41 => hf.linv hp hX hP sp st' hm hr h13 h32 h41
  · exact hL
  · exact a.lw hp hX hP h3
  · exact htS
  · exact hf.ok_os hp _ htS
  · exact hpath
  · exact hdec
  · exact b1
  · exact wT1
  · exact b2
  · exact b3
  · exact b4
