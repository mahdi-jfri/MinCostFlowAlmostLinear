module

public import MinCostFlow.LowStretch.ProgBodyNodeWalk
public import MinCostFlow.LowStretch.ProgBodyNodeAct
public import MinCostFlow.LowStretch.ProgClusterPetL

/-!
# The petal block meets `PetL.Ok`

After the loop, the node part writes `CC[0]`, `CT[0]` and the `16` words of the petal block at
`hS`. The memory `M` that the child step sees differs from the memory after the loop only at
`CT[0]`, `CC[0]` and from `hS` on. All the cells that the facts of `PetL.Ok` read lie below `hS`,
so the facts of `PW.LInv.petl` (petals `1, …`) carry over to `M` (`PW.LInv.petOk`). The walk of
child `0` comes from the path of the setup (`PW.walk0`, `PW.walk0_sp`), whose cells the loop keeps
(`PW.LInv.keepM0`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- The walk facts of `PetL.Ok` for a raw child with target `e`, highway `hw` and center `x`. -/
def PetL.WalkAt (T : KT) (G : PG) (c : Cl) (R : Rec) (X : PetL) (mem : ℕ → ℕ) (e : ℕ)
    (hw : List ℕ) (x : ℕ) : Prop :=
  (parWalk mem X.PAR (R.sv T c e) (Cl.hwE G e hw c.θ c.half).length).map (X.ent mem) =
    Cl.hwE G e hw c.θ c.half ∧
  (∀ u ∈ parWalk mem X.PAR (R.sv T c e) (Cl.hwE G e hw c.θ c.half).length,
    u = R.sv T c (mem (X.PA + u))) ∧
  parEnd mem X.PAR (R.sv T c e) (Cl.hwE G e hw c.θ c.half).length = R.sv T c x ∧
  R.sv T c x ∉ parWalk mem X.PAR (R.sv T c e) (Cl.hwE G e hw c.θ c.half).length ∧
  (parWalk mem X.PAR (R.sv T c e) (Cl.hwE G e hw c.θ c.half).length).Nodup

/-- The walk facts read only the five arrays at the nodes of the walk. -/
theorem PetL.WalkAt.congr {T : KT} {G : PG} {c : Cl} {R : Rec} {X : PetL} {M M' : ℕ → ℕ}
    {e x : ℕ} {hw : List ℕ} (h : X.WalkAt T G c R M' e hw x)
    (hm : ∀ u ∈ parWalk M' X.PAR (R.sv T c e) (Cl.hwE G e hw c.θ c.half).length,
      M (X.PAR + u) = M' (X.PAR + u) ∧ M (X.PP + u) = M' (X.PP + u) ∧
      M (X.PF + u) = M' (X.PF + u) ∧ M (X.PA + u) = M' (X.PA + u) ∧
      M (X.PB + u) = M' (X.PB + u)) :
    X.WalkAt T G c R M e hw x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hw' := parWalk_congrW (M := M') (M' := M) _ _ fun v hv => (hm v hv).1
  have he := parEnd_congrW (M := M') (M' := M) _ _ fun v hv => (hm v hv).1
  unfold PetL.WalkAt
  rw [hw', he]
  refine ⟨?_, fun u hu => ?_, h3, h4, h5⟩
  · refine (List.map_congr_left fun u hu => ?_).trans h1
    obtain ⟨-, a, b, c, d⟩ := hm u hu
    simp [PetL.ent, a, b, c, d]
  · rw [(hm u hu).2.2.2.1]; exact h2 u hu

open WordRAM

namespace PW

variable {W : PW} {w : ℕ} {A : TA} {Q : LA}

/-- **The loop keeps the tree arrays.** A memory `M` that agrees with the memory after the loop
below `hS`, except at `CT[0]` and `CC[0]`, agrees with the memory `M0` before the loop on the
parent array and the arc arrays of the nodes. -/
theorem LInv.keepM0 {sp : Bool} {k0 : ℕ} {M0 : ℕ → ℕ} {a : LG} {st : State}
    (hI : W.LInv A Q sp k0 M0 w a st) (hL : W.LLay A Q w) {hS : ℕ} (hPT : Q.PT + W.s ≤ hS)
    {M : ℕ → ℕ} (hM : ∀ x < hS, x ≠ Q.CT → x ≠ Q.CC → M x = st.mem x) :
    ∀ v < W.s, M (W.NXT + v) = M0 (W.NXT + v) ∧ M (A.PP + v) = M0 (A.PP + v) ∧
      M (A.PF + v) = M0 (A.PF + v) ∧ M (A.PA + v) = M0 (A.PA + v) ∧
      M (A.PB + v) = M0 (A.PB + v) := by
  have h := hI.btw.ok
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES; have hNN := h.hNN; have hR := h.hR; have hCTL := h.hCTL
  have hSUM := h.hSUM; have hSL := h.hSL
  obtain ⟨t1, t2, t3, t4, t5⟩ := hL.ta
  have hpl := hL.pl; have hpo := hL.po; have hct := hL.ct; have hcc := hL.cc
  have hpt := hL.pt
  have hout := fun {x : ℕ} (hx : W.Out Q x) => hL.out_ge hx
  intro v hv
  have hs : ∀ x, x < W.L.HD → M x = M0 x := fun x hx => by
    rw [hM x (by omega) (by omega) (by omega)]
    exact hI.safe x (Or.inl hx) fun ho => by have := hout ho; omega
  refine ⟨?_, hs _ (by omega), hs _ (by omega), hs _ (by omega), hs _ (by omega)⟩
  rw [hM _ (by omega) (by omega) (by omega)]
  exact hI.low _ (by omega) (Or.inr (by omega)) (by omega)

/-- **The walk of child `0` without a special petal**, in a memory `M` that agrees with the
memory `M0` of the setup on the tree arrays. -/
theorem walk0 {M0 M : ℕ → ℕ} (h : W.Ok w M0) (hT : W.Tree A M0) {D : Cl.Dec}
    (hsp : D.sp = false) {n : ℕ} (hp : W.Path M0 (W.sv W.c.t) n)
    (hd : W.c.HwDec W.G W.c.t (W.stp A M0 (W.sv W.c.t) n) W.c.hw)
    (X : PetL) (hX : X.PAR = W.NXT ∧ X.PP = A.PP ∧ X.PF = A.PF ∧ X.PA = A.PA ∧ X.PB = A.PB)
    (hM : ∀ v < W.s, M (W.NXT + v) = M0 (W.NXT + v) ∧ M (A.PP + v) = M0 (A.PP + v) ∧
      M (A.PF + v) = M0 (A.PF + v) ∧ M (A.PA + v) = M0 (A.PA + v) ∧
      M (A.PB + v) = M0 (A.PB + v)) :
    X.WalkAt W.T W.G W.c W.R M (W.c.raw W.G D 0).t (W.c.raw W.G D 0).hw
      (W.c.raw W.G D 0).x0 := by
  have e1 : (W.c.raw W.G D 0).t = W.c.t := by simp [Cl.raw, hsp]
  have e2 : (W.c.raw W.G D 0).hw = W.c.hw := by simp [Cl.raw, hsp]
  have e3 : (W.c.raw W.G D 0).x0 = W.c.x0 := by simp [Cl.raw, hsp]
  rw [e1, e2, e3]
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := walk_stem h hT hp hd X hX
  refine PetL.WalkAt.congr ⟨w1, w2, w3, w4, w5⟩ fun u hu => ?_
  obtain ⟨a1, a2, a3, a4, a5⟩ := hM u (w6 u hu)
  rw [hX.1, hX.2.1, hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2]
  exact ⟨a1, a2, a3, a4, a5⟩

/-- **The walk of child `0` with a special petal**: petal `0` has target `c.t` and highway
`c.hw`, and its portal is the parent arc of node `m` of the path of the setup. -/
theorem walk0_sp {M0 M : ℕ → ℕ} (h : W.Ok w M0) (hT : W.Tree A M0) {D : Cl.Dec}
    (hsp : D.sp = true) (htj : (D.pd 0).tj = W.c.t) (hhw : (D.pd 0).hw = W.c.hw) {n m : ℕ}
    (hp : W.Path M0 (W.sv W.c.t) n)
    (hd : W.c.HwDec W.G W.c.t (W.stp A M0 (W.sv W.c.t) n) W.c.hw) (hmn : m < n)
    (hi : (D.pd 0).i < W.c.hw.length)
    (e0 : W.c.hw.getD (D.pd 0).i 0 = M0 (A.PP + W.pe M0 (W.sv W.c.t) m))
    (e1 : hv W.G W.c.t W.c.hw (D.pd 0).i = M0 (A.PA + W.pe M0 (W.sv W.c.t) m))
    (e2 : hv W.G W.c.t W.c.hw ((D.pd 0).i + 1) = M0 (A.PB + W.pe M0 (W.sv W.c.t) m))
    (X : PetL) (hX : X.PAR = W.NXT ∧ X.PP = A.PP ∧ X.PF = A.PF ∧ X.PA = A.PA ∧ X.PB = A.PB)
    (hM : ∀ v < W.s, M (W.NXT + v) = M0 (W.NXT + v) ∧ M (A.PP + v) = M0 (A.PP + v) ∧
      M (A.PF + v) = M0 (A.PF + v) ∧ M (A.PA + v) = M0 (A.PA + v) ∧
      M (A.PB + v) = M0 (A.PB + v)) :
    X.WalkAt W.T W.G W.c W.R M (W.c.raw W.G D 0).t (W.c.raw W.G D 0).hw
      (W.c.raw W.G D 0).x0 := by
  have f1 : (W.c.raw W.G D 0).t = hv W.G W.c.t W.c.hw ((D.pd 0).i + 1) := by
    simp [Cl.raw, hsp, Cl.Dec.yc, htj, hhw]
  have f2 : (W.c.raw W.G D 0).hw = W.c.hw.drop ((D.pd 0).i + 1) := by simp [Cl.raw, hsp]
  have f3 : (W.c.raw W.G D 0).x0 = W.c.x0 := by simp [Cl.raw, hsp]
  rw [f1, f2, f3]
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := walk_stem_sp h hT hp hd hmn hi e0 e1 e2 X hX
  refine PetL.WalkAt.congr ⟨w1, w2, w3, w4, w5⟩ fun u hu => ?_
  obtain ⟨a1, a2, a3, a4, a5⟩ := hM u (w6 u hu)
  rw [hX.1, hX.2.1, hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2]
  exact ⟨a1, a2, a3, a4, a5⟩

open Classical in
/-- **The petal block meets `PetL.Ok`.** At the end of the loop, take a memory `M` that agrees
with the memory of the loop below `hS`, except at `CT[0]` and `CC[0]`, which hold the target and
the center of child `0`. A block `X` with the arrays of the loop, the number of petals, the flag,
the active pairs, the radius and the walk of child `0` then meets `PetL.Ok` in `M`. -/
theorem LInv.petOk {sp : Bool} {k0 : ℕ} {M0 : ℕ → ℕ} {a : LG} {st : State}
    (hI : W.LInv A Q sp k0 M0 w a st) (hL : W.LLay A Q w) (hend : a.u = W.s)
    (hdec : W.c.DecOk W.G W.P ⟨sp, a.ps⟩) {hS : ℕ} (hPT : Q.PT + W.s ≤ hS) {M : ℕ → ℕ}
    (hM : ∀ x < hS, x ≠ Q.CT → x ≠ Q.CC → M x = st.mem x)
    (X : PetL) (hX : X.Of W A Q) (hnP : X.nP = a.ps.length) (hsp : X.sp = if sp then 1 else 0)
    (hact : (X.actL M).Nodup ∧ (∀ p, p ∈ X.actL M ↔ p ∈ W.c.act W.G W.P) ∧
      ∀ i < X.nA, M (X.ACT + 2 * i + 1) = if M (X.ACT + 2 * i) ∈ W.c.half then 1 else 0)
    (hDc : X.Dc = W.c.Δ W.G)
    (hct0 : M Q.CT = (W.c.raw W.G ⟨sp, a.ps⟩ 0).t)
    (hcc0 : M Q.CC = (W.c.raw W.G ⟨sp, a.ps⟩ 0).x0)
    (hw0 : X.WalkAt W.T W.G W.c W.R M (W.c.raw W.G ⟨sp, a.ps⟩ 0).t
      (W.c.raw W.G ⟨sp, a.ps⟩ 0).hw (W.c.raw W.G ⟨sp, a.ps⟩ 0).x0) :
    X.Ok W.T W.G W.P W.c W.R ⟨sp, a.ps⟩ M := by
  have h := hI.btw.ok
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES; have hNN := h.hNN; have hR := h.hR; have hCTL := h.hCTL
  have hSUM := h.hSUM; have hSL := h.hSL
  obtain ⟨t1, t2, t3, t4, t5⟩ := hL.ta
  have hpl := hL.pl; have hpo := hL.po; have hct := hL.ct; have hcc := hL.cc
  have hpt := hL.pt
  have hroom := hI.room; have hkle := hI.kle
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hI.petl hL hend hdec X hX hnP
  have xPL := hX.PL; have xPO := hX.PO; have xOK := hX.OK; have xCT := hX.CT
  have xCC := hX.CC; have xPAR := hX.PAR; have xPP := hX.PP; have xPF := hX.PF
  have xPA := hX.PA; have xPB := hX.PB
  have hnPs : X.nP ≤ W.s := by omega
  have hpoM : ∀ k ≤ X.nP, M (X.PO + k) = st.mem (X.PO + k) := fun k hk =>
    hM _ (by omega) (by omega) (by omega)
  have hpoS : ∀ k ≤ X.nP, st.mem (X.PO + k) ≤ W.s := fun k hk => by
    have := f2 k hk; rw [← xPO, ← hnP] at hroom; omega
  have hnodes : ∀ k < X.nP, X.nodesOf M k = X.nodesOf st.mem k := fun k hk => by
    unfold PetL.nodesOf
    rw [hpoM k hk.le, hpoM (k + 1) hk]
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.mp hj
    have := f1 k hk; have := hpoS (k + 1) hk
    exact hM _ (by omega) (by omega) (by omega)
  have hctk : ∀ k < (⟨sp, a.ps⟩ : Cl.Dec).nch, M (X.CT + k) = (W.c.raw W.G ⟨sp, a.ps⟩ k).t :=
    fun k hk => by
      rcases k with _ | k
      · rw [Nat.add_zero, xCT, hct0]
      · have hk' : k < a.ps.length := by simp [Cl.Dec.nch] at hk; omega
        rw [hM _ (by omega) (by omega) (by omega)]
        exact (f6 k hk').1
  have hcck : ∀ k < (⟨sp, a.ps⟩ : Cl.Dec).nch, M (X.CC + k) = (W.c.raw W.G ⟨sp, a.ps⟩ k).x0 :=
    fun k hk => by
      rcases k with _ | k
      · rw [Nat.add_zero, xCC, hcc0]
      · have hk' : k < a.ps.length := by simp [Cl.Dec.nch] at hk; omega
        rw [hM _ (by omega) (by omega) (by omega)]
        exact (f6 k hk').2.1
  refine ⟨hnP, hsp, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk u => ?_,
    fun u hu => ?_, hctk, hcck, fun k hk => ?_, hact.1, hact.2.1, hact.2.2, hDc⟩
  · rw [hpoM k hk.le, hpoM (k + 1) hk]; exact f1 k hk
  · rw [hpoM k hk, hpoM _ le_rfl]; exact f2 k hk
  · rw [hnodes k hk]; exact f3 k hk
  · rw [hnodes k hk]; exact f4 k hk u
  · have hu' : u < W.s := hu
    rw [hM _ (by omega) (by omega) (by omega)]; exact f5 u hu
  · have hwk : X.WalkAt W.T W.G W.c W.R M (W.c.raw W.G ⟨sp, a.ps⟩ k).t
        (W.c.raw W.G ⟨sp, a.ps⟩ k).hw (W.c.raw W.G ⟨sp, a.ps⟩ k).x0 := by
      rcases k with _ | k
      · exact hw0
      · have hk' : k < a.ps.length := by simp [Cl.Dec.nch] at hk; omega
        obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := f6 k hk'
        rw [g1] at g3 g4 g5 g6 g7
        rw [g2] at g5 g6
        refine PetL.WalkAt.congr (M' := st.mem) ⟨g3, g4, g5, g6, g7⟩ fun u hu => ?_
        have hus : u ≤ W.s := by rw [g4 u hu]; exact Rec.sv_le _ _ _ _
        exact ⟨hM _ (by omega) (by omega) (by omega), hM _ (by omega) (by omega) (by omega),
          hM _ (by omega) (by omega) (by omega), hM _ (by omega) (by omega) (by omega),
          hM _ (by omega) (by omega) (by omega)⟩
    rw [hctk k hk, hcck k hk]
    exact hwk

end PW

end MinCostFlow.LowStretch
