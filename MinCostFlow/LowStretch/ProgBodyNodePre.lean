module

public import MinCostFlow.LowStretch.ProgBodyNodePet
public import MinCostFlow.LowStretch.ProgBodyKids

/-!
# The precondition of the child step in the node part

After the loop, the node part writes `CC[0]`, `CT[0]` and the petal block at `hS`, and calls the
child step at `hS + 16`. `PW.nodeChildPre` shows that the memory `M1` it calls on meets
`ChildPre`: the cells below `h` are those of the setup's input (the loop keeps them), the block
meets `PetL.Ok` (`PW.LInv.petOk`), its arrays lie in `[h, hS)`, and the memory from `hS + 16` on
is zero (the setup leaves it zero and the loop writes only below `hS`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace PW

variable {W : PW} {w : ℕ} {A : TA} {Q : LA}

open Classical in
/-- **The memory of the call of the child step meets `ChildPre`.** Here `M0` is the memory after
the setup, `st` the state after the loop, and `M1` the memory after the stores of `CC[0]`,
`CT[0]` and the block `X` at `hS`. The bound `hACT` (the active entries lie below the heads) comes
from the setup. -/
theorem nodeChildPre {A0 GB RB h hS ACT k0 : ℕ} {mem M0 M1 : ℕ → ℕ} {sp : Bool} {a : LG}
    {st : State}
    (hpre : ClPre w A0 W.T W.G W.P W.c W.R GB RB h mem) (hX2 : 2 ≤ W.c.X.card)
    (hOk0 : W.Ok w M0) (hT0 : W.Tree A M0)
    (hI : W.LInv A Q sp k0 M0 w a st) (hL : W.LLay A Q w) (hend : a.u = W.s)
    (hdec : W.c.DecOk W.G W.P ⟨sp, a.ps⟩)
    (hlow0 : ∀ x < h, M0 x = mem x) (hz0 : ZeroFrom M0 hS)
    (hHD : h + 51 ≤ W.L.HD)
    (hTA : h + 51 ≤ A.PP ∧ h + 51 ≤ A.PF ∧ h + 51 ≤ A.PA ∧ h + 51 ≤ A.PB) (hACTh : h + 51 ≤ ACT) (hACT : ACT + 2 * W.nA ≤ W.L.HD)
    (hPTs : Q.PT + W.s ≤ hS) (hNXTs : W.NXT + W.s + 1 ≤ hS)
    (hact : ∀ i < W.nA, M0 (ACT + 2 * i) = W.pr i ∧
      M0 (ACT + 2 * i + 1) = if W.pr i ∈ W.c.half then 1 else 0)
    (hpath : sp = false → ∃ n, W.Path M0 (W.sv W.c.t) n ∧
      W.c.HwDec W.G W.c.t (W.stp A M0 (W.sv W.c.t) n) W.c.hw)
    (hspec : sp = true → 0 < a.ps.length ∧ ((⟨sp, a.ps⟩ : Cl.Dec).pd 0).tj = W.c.t ∧
      ((⟨sp, a.ps⟩ : Cl.Dec).pd 0).hw = W.c.hw)
    (hM : ∀ x < hS, x ≠ Q.CT → x ≠ Q.CC → M1 x = st.mem x)
    (hMz : ∀ x, hS + 16 ≤ x → M1 x = st.mem x)
    (hct0 : M1 Q.CT = (W.c.raw W.G ⟨sp, a.ps⟩ 0).t)
    (hcc0 : M1 Q.CC = (W.c.raw W.G ⟨sp, a.ps⟩ 0).x0)
    (hblk : PetL.read M1 hS = ⟨a.ps.length, if sp then 1 else 0, Q.PL, Q.PO, W.L.OK, W.L.os,
      Q.CT, Q.CC, W.NXT, A.PP, A.PF, A.PA, A.PB, W.nA, ACT, W.c.Δ W.G⟩)
    (hroom : hS + 16 ≤ h + ((GlobL.read mem GB).J + 2) * recCost w A0 W.T W.G W.P W.c W.R) :
    ChildPre w W.T W.G W.P W.c W.R ⟨sp, a.ps⟩ GB RB hS (hS + 16) M1 := by
  have hWk := hI.btw.ok
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := hWk.lay
  have hES := hWk.lES; have hNN := hWk.hNN; have hR := hWk.hR; have hCTL := hWk.hCTL
  have hSUM := hWk.hSUM; have hSL := hWk.hSL
  obtain ⟨t1, t2, t3, t4, t5⟩ := hL.ta
  have hpl := hL.pl; have hpo := hL.po; have hct := hL.ct; have hcc := hL.cc
  have hpt := hL.pt
  have hout := fun {x : ℕ} (hx : W.Out Q x) => hL.out_ge hx
  have hroomP := hI.room; have hkle := hI.kle
  set X := PetL.read M1 hS with hXd
  have hOf : X.Of W A Q := by
    rw [hblk]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsafe : ∀ x, x < W.L.HD → M1 x = M0 x := fun x hx => by
    rw [hM x (by omega) (by omega) (by omega)]
    exact hI.safe x (Or.inl hx) fun ho => by have := hout ho; omega
  have hlow : ∀ x < h, M1 x = mem x := fun x hx => by rw [hsafe x (by omega), hlow0 x hx]
  have hkeep := hI.keepM0 hL hPTs hM
  have h5 : X.PAR = W.NXT ∧ X.PP = A.PP ∧ X.PF = A.PF ∧ X.PA = A.PA ∧ X.PB = A.PB :=
    ⟨hOf.PAR, hOf.PP, hOf.PF, hOf.PA, hOf.PB⟩
  have hw0 : X.WalkAt W.T W.G W.c W.R M1 (W.c.raw W.G ⟨sp, a.ps⟩ 0).t
      (W.c.raw W.G ⟨sp, a.ps⟩ 0).hw (W.c.raw W.G ⟨sp, a.ps⟩ 0).x0 := by
    cases sp
    · obtain ⟨n, hp, hd⟩ := hpath rfl
      exact walk0 hOk0 hT0 rfl hp hd X h5 hkeep
    · obtain ⟨hlen, htj, hhw⟩ := hspec rfl
      obtain ⟨-, -, -, -, -, n, m, hp0, -, hd0, hmn, e0, e1, e2⟩ := hI.out 0 hlen
      have hi := (hdec.2.1 rfl).2.2.2.2.2.1
      rw [htj] at hp0 hd0 e0 e1 e2
      rw [hhw] at hd0 e0 e1 e2 hi
      exact walk0_sp hOk0 hT0 rfl htj hhw hp0 hd0 hmn hi e0 e1 e2 X h5 hkeep
  have hactM : ∀ i < W.nA, M1 (ACT + 2 * i) = W.pr i ∧
      M1 (ACT + 2 * i + 1) = if W.pr i ∈ W.c.half then 1 else 0 := fun i hi => by
    rw [hsafe _ (by omega), hsafe _ (by omega)]; exact hact i hi
  have hXACT : X.ACT = ACT := by rw [hblk]
  have hXnA : X.nA = W.nA := by rw [hblk]
  have hpet : X.Ok W.T W.G W.P W.c W.R ⟨sp, a.ps⟩ M1 :=
    hI.petOk hL hend hdec hPTs hM X hOf (by rw [hblk]) (by rw [hblk])
      (hOk0.act_facts hactM X hXACT hXnA) (by rw [hblk]) hct0 hcc0 hw0
  have hs : (RecL.read mem RB).s = W.s := hpre.recAt.arcs.s
  have hPOn : M1 (X.PO + X.nP) ≤ W.s := by
    have e1 : X.PO = Q.PO := hOf.PO
    have e2 : X.nP = a.ps.length := by rw [hblk]
    rw [e1, e2, hM _ (by omega) (by omega) (by omega)]
    omega
  obtain ⟨Mw, hMw1, hMw2, hMw3⟩ := hpre.room_sq
  refine childPre_of hpre hX2 hdec hlow hpet (by omega) le_rfl (fun r hr => ?_)
    (fun x hx => by rw [hMz x hx]; rw [hI.safe x (Or.inr (by omega)) fun ho => by
        unfold Out at ho; omega]; exact hz0 x (by omega))
    ⟨Mw, hMw1, hMw2, by
      generalize 2 ^ (2 * (GlobL.read mem GB).J + 20) * (W.T.N + W.G.m + 2) ^ 2 * (Mw + 2) ^ 2
        = Z at hMw3 ⊢
      omega⟩
  have hnP : X.nP = a.ps.length := by rw [hblk]
  rw [hs] at hr
  simp only [PetL.regs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [hOf.PL, hOf.PO, hOf.OK, hOf.CT, hOf.CC, hOf.PAR, hOf.PP, hOf.PF, hOf.PA, hOf.PB, hXACT, hXnA,
    hnP] at hr
  rw [hOf.PO, hnP] at hPOn
  obtain ⟨u1, u2, u3, u4⟩ := hTA
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only <;> omega

end PW

end MinCostFlow.LowStretch
