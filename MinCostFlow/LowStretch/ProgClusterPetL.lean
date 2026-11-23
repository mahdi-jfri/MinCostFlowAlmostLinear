module

public import MinCostFlow.LowStretch.ProgClusterLoop6
public import MinCostFlow.LowStretch.ProgClusterWalk2

/-!
# From the end of the petal loop to the rules of a decomposition step

At the end of the loop (`u = s`) the invariant `PW.LInv` gives:
* `PW.LInv.decOk`: the petals meet the rules `DecOk`, given the rule of the special petal;
* `PW.LInv.petl`: the facts of `PetL.Ok` about the petals (their lists, the marks of the stem,
  the targets, centers and walks of the raw children `k + 1`), for a petal block whose arrays are
  those of the loop.

The facts about child `0`, the active pairs and the radius come from the rest of the cluster
procedure.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The petal block has the arrays of the loop. -/
structure PetL.Of (X : PetL) (W : PW) (A : PW.TA) (Q : PW.LA) : Prop where
  PL : X.PL = Q.PL
  PO : X.PO = Q.PO
  OK : X.OK = W.L.OK
  os : X.os = W.L.os
  CT : X.CT = Q.CT
  CC : X.CC = Q.CC
  PAR : X.PAR = W.NXT
  PP : X.PP = A.PP
  PF : X.PF = A.PF
  PA : X.PA = A.PA
  PB : X.PB = A.PB

namespace PW

variable {W : PW} {w : ℕ} {A : TA} {Q : LA}

/-- **The rules of a decomposition step** at the end of the loop. -/
theorem LInv.decOk {sp : Bool} {k0 : ℕ} {M0 : ℕ → ℕ} {a : LG} {st : State}
    (hI : W.LInv A Q sp k0 M0 w a st) (hend : a.u = W.s) (hk0 : k0 = if sp then 1 else 0)
    (hsp : sp = true ↔ 5 * W.c.Δ W.G < 8 * W.c.d W.G W.c.x0 W.c.t)
    (hspec : sp = true → 0 < a.ps.length ∧ ((⟨sp, a.ps⟩ : Cl.Dec).pd 0).tj = W.c.t ∧
      ((⟨sp, a.ps⟩ : Cl.Dec).pd 0).hw = W.c.hw ∧
      W.c.PetalOk W.G W.P W.c.X (W.c.loS W.G) ((⟨sp, a.ps⟩ : Cl.Dec).pd 0)) :
    W.c.DecOk W.G W.P ⟨sp, a.ps⟩ := by
  refine ⟨hsp, hspec, fun k hk hne => hI.reg k ?_ hk, fun z hz => ?_⟩
  · cases sp
    · simp at hk0; omega
    · simp at hk0; have := hne rfl; omega
  · have h := hI.btw.ok
    unfold Cl.stem at hz
    rw [← hI.Y, mem_Y] at hz
    have hv := h.sv_lt hz.1
    have := hI.scan _ (by omega) hv hz.2
    rw [hI.tree.fd z hz.1] at this
    exact this

open Classical in
/-- **The facts of `PetL.Ok` about the petals**, at the end of the loop. -/
theorem LInv.petl {sp : Bool} {k0 : ℕ} {M0 : ℕ → ℕ} {a : LG} {st : State}
    (hI : W.LInv A Q sp k0 M0 w a st) (hL : W.LLay A Q w) (hend : a.u = W.s)
    (hdec : W.c.DecOk W.G W.P ⟨sp, a.ps⟩) (X : PetL) (hX : X.Of W A Q) (hnP : X.nP = a.ps.length) :
    (∀ k < X.nP, st.mem (X.PO + k) ≤ st.mem (X.PO + (k + 1))) ∧
    (∀ k ≤ X.nP, st.mem (X.PO + k) ≤ st.mem (X.PO + X.nP)) ∧
    (∀ k < X.nP, (X.nodesOf st.mem k).Nodup) ∧
    (∀ k < X.nP, ∀ u, u ∈ X.nodesOf st.mem k ↔
      ∃ v ∈ W.c.W W.G ⟨sp, a.ps⟩ k, W.R.sv W.T W.c v = u) ∧
    (∀ u < W.R.nodes.length, st.mem (X.OK + u) = X.os ↔
      ∃ v ∈ W.c.stem W.G ⟨sp, a.ps⟩, W.R.sv W.T W.c v = u) ∧
    (∀ k < a.ps.length, st.mem (X.CT + (k + 1)) = (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).t ∧
      st.mem (X.CC + (k + 1)) = (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).x0 ∧
      (parWalk st.mem X.PAR (W.R.sv W.T W.c (st.mem (X.CT + (k + 1))))
        (Cl.hwE W.G (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).t (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).hw
          W.c.θ W.c.half).length).map (X.ent st.mem) =
        Cl.hwE W.G (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).t (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).hw
          W.c.θ W.c.half ∧
      (∀ u ∈ parWalk st.mem X.PAR (W.R.sv W.T W.c (st.mem (X.CT + (k + 1))))
          (Cl.hwE W.G (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).t (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).hw
            W.c.θ W.c.half).length,
        u = W.R.sv W.T W.c (st.mem (X.PA + u))) ∧
      parEnd st.mem X.PAR (W.R.sv W.T W.c (st.mem (X.CT + (k + 1))))
          (Cl.hwE W.G (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).t (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).hw
            W.c.θ W.c.half).length =
        W.R.sv W.T W.c (st.mem (X.CC + (k + 1))) ∧
      W.R.sv W.T W.c (st.mem (X.CC + (k + 1))) ∉
        parWalk st.mem X.PAR (W.R.sv W.T W.c (st.mem (X.CT + (k + 1))))
          (Cl.hwE W.G (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).t (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).hw
            W.c.θ W.c.half).length ∧
      (parWalk st.mem X.PAR (W.R.sv W.T W.c (st.mem (X.CT + (k + 1))))
        (Cl.hwE W.G (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).t (W.c.raw W.G ⟨sp, a.ps⟩ (k + 1)).hw
          W.c.θ W.c.half).length).Nodup) := by
  have h := hI.btw.ok
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES; have hNN := h.hNN; have hR := h.hR; have hCTL := h.hCTL
  have hSUM := h.hSUM; have hSL := h.hSL
  obtain ⟨t1, t2, t3, t4, t5⟩ := hL.ta
  have hout := fun {x : ℕ} (hx : W.Out Q x) => hL.out_ge hx
  have hnl : ∀ k, X.nodesOf st.mem k = nl Q st.mem k := fun k => by
    unfold PetL.nodesOf nl; rw [hX.PL, hX.PO]
  rw [hnP, hX.PO]
  refine ⟨fun k hk => hI.po k hk, fun k hk => hI.po_mono hk le_rfl,
    fun k hk => by rw [hnl]; exact (hI.out k hk).1,
    fun k hk u => by rw [hnl]; exact (hI.out k hk).2.1 u, fun u hu => ?_, fun k hk => ?_⟩
  · rw [hX.OK, hX.os]
    unfold Cl.stem
    rw [← hI.Y]
    constructor
    · intro hok
      obtain ⟨v, hv, rfl⟩ := h.sv_surj hu
      exact ⟨v, mem_Y.mpr ⟨hv, hok⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (mem_Y.mp hv).2
  · obtain ⟨-, -, hct, hcc, -, n, m, hp0, htX, hd0, hmn, e0, e1, -⟩ := hI.out k hk
    have hi : ((⟨sp, a.ps⟩ : Cl.Dec).pd k).i < ((⟨sp, a.ps⟩ : Cl.Dec).pd k).hw.length := by
      by_cases hs : sp = true ∧ k = 0
      · obtain ⟨hs1, rfl⟩ := hs
        exact (hdec.2.1 hs1).2.2.2.2.2.1
      · exact (hdec.2.2.1 k hk (fun h1 h2 => hs ⟨h1, h2⟩)).2.2.2.1
    set pd := (⟨sp, a.ps⟩ : Cl.Dec).pd k with hpd
    have hvlt : W.sv pd.tj < W.L.NN := by have := h.sv_lt htX; omega
    have hm0 : ∀ v < W.L.NN, M0 (W.NXT + v) = st.mem (W.NXT + v) := fun v hv =>
      (hI.low _ (by omega) (Or.inr (by omega)) (by omega)).symm
    have hAM : ∀ v < W.s, st.mem (A.PP + v) = M0 (A.PP + v) ∧ st.mem (A.PA + v) = M0 (A.PA + v) ∧
        st.mem (A.PB + v) = M0 (A.PB + v) := fun v hv =>
      ⟨hI.safe _ (Or.inl (by omega)) fun ho => by have := hout ho; omega,
        hI.safe _ (Or.inl (by omega)) fun ho => by have := hout ho; omega,
        hI.safe _ (Or.inl (by omega)) fun ho => by have := hout ho; omega⟩
    have hp : W.Path st.mem (W.sv pd.tj) n := (Path_congr h hm0 hvlt).mp hp0
    have hpe : ∀ j, W.pe M0 (W.sv pd.tj) j = W.pe st.mem (W.sv pd.tj) j :=
      pe_congr h hm0 hvlt
    have hst : W.stp A M0 (W.sv pd.tj) n = W.stp A st.mem (W.sv pd.tj) n :=
      stp_congr h hm0 hvlt fun j hj => by
        have := hp.lt h.root_lt hj.le
        exact ⟨(hAM _ this).1.symm, (hAM _ this).2.1.symm, (hAM _ this).2.2.symm⟩
    have hpm := hp.lt h.root_lt hmn.le
    rw [hst] at hd0
    rw [hpe, ← (hAM _ hpm).1] at e0
    rw [hpe, ← (hAM _ hpm).2.1] at e1
    have hW := walk_of_dec h hI.tree hp hd0 hmn hi e0 e1 X
      ⟨hX.PAR, hX.PP, hX.PF, hX.PA, hX.PB⟩
    have hct' : st.mem (X.CT + (k + 1)) = pd.tj := by rw [hX.CT]; exact hct
    have hcc' : st.mem (X.CC + (k + 1)) = hv W.G pd.tj pd.hw pd.i := by rw [hX.CC]; exact hcc
    refine ⟨hct', hcc', ?_⟩
    rw [hct', hcc']
    exact hW

end PW

end MinCostFlow.LowStretch
