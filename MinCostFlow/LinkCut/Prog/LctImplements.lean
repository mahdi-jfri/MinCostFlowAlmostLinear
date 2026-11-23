module

public import MinCostFlow.LinkCut.Prog.LctModule
public import MinCostFlow.Num.ModulePlacement

/-!
# The link-cut tree implements its specification

The main result is `lctDataStructure_implements`: if a program holds the procedures
`lctBodies h L P b0` from index `b0` on, then procedure `b0` and procedures
`(LctProcs.atBase b0).op i` implement `lctDataStructure h L P` with the representation
`lctDSRep w h L P`. Each case applies the run theorem of one procedure, such as
`lctCutBody_runs`. The only work left here is to match the arguments, the space bound and the
cost bound to the form that `DSRep.Implements` asks for.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section LctImplements

variable {w h L P b0 : ℕ} {p : Program}

/-- The eleven procedures before the splay procedures, at their indices. -/
theorem lctBodies_procs (hp : p.HasAt b0 (lctBodies h L P b0)) :
    p.procs[b0]? = some (lctInitBody L P) ∧
    p.procs[b0 + 1]? = some (lctFindRootBody (LctProcs.atBase b0)) ∧
    p.procs[b0 + 2]? = some (lctLinkBody (LctProcs.atBase b0)) ∧
    p.procs[b0 + 3]? = some (lctCutBody (LctProcs.atBase b0)) ∧
    p.procs[b0 + 4]? = some (lctPathAddBody (LctProcs.atBase b0)) ∧
    p.procs[b0 + 5]? = some (lctPathMinBody (LctProcs.atBase b0)) ∧
    p.procs[b0 + 6]? = some (lctPathSumBody (LctProcs.atBase b0)) ∧
    p.procs[b0 + 7]? = some (lctConnectedBody (LctProcs.atBase b0)) ∧
    p.procs[b0 + 8]? = some copyWords ∧
    p.procs[b0 + 9]? = some (exposeBody (LctProcs.atBase b0).splay) ∧
    p.procs[b0 + 10]? = some (lctRerootBody (LctProcs.atBase b0)) := by
  have hf := hasAt_append_left hp
  have g : ∀ i (hi : i < 11), _ := fun i hi => hf i (by simpa using hi)
  exact ⟨by simpa using g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide),
    g 4 (by decide), g 5 (by decide), g 6 (by decide), g 7 (by decide), g 8 (by decide),
    g 9 (by decide), g 10 (by decide)⟩

/-- The word bounds and the placed procedures give `LctBaseOk`. -/
theorem lctBaseOk_of_hasAt (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (hL : L < 2 ^ w)
    (hP : P < 2 ^ w) (hp : p.HasAt b0 (lctBodies h L P b0)) :
    LctBaseOk w h L P p (LctProcs.atBase b0) := by
  have hsplay : p.HasAt (b0 + 11) (splayBodies (SplayProcs.atBase (b0 + 11)) h) := by
    have h' : p.HasAt (b0 + 11) (splayBodies (LctProcs.atBase b0).splay h) := by
      simpa using hasAt_append_right hp
    exact h'
  have hcopy : p.HasAt (b0 + 8) [copyWords] := by
    intro i hi
    obtain rfl : i = 0 := by simpa using hi
    simpa using (lctBodies_procs hp).2.2.2.2.2.2.2.2.1
  exact ⟨hh, hw, hL, hP, hsplay, splayProgramOk_of_hasAt hh hw hsplay,
    copyWords_meetsContract hcopy⟩

private theorem room_of {a b c d e W : ℕ} (hr : a + (b + c + d + e) < W) :
    a + b + c + d + e < W := by omega

private theorem room_of₂ {a b c d e f W : ℕ} (hr : a + (b + c + d + (e + f)) < W) :
    a + b + c + d + e + f < W := by omega

private theorem space_of₂ {b c d e f : ℕ} : b + c + e + f ≤ b + c + d + (e + f) := by omega

private theorem space_of {b c d e : ℕ} : b + c + e ≤ b + c + d + e := by omega

private theorem cost_of {c d phi' phi C : ℕ} (hc : c + d + phi' ≤ phi + C) :
    c + phi' ≤ C + phi := by omega

/-- The link-cut tree implements `lctDataStructure h L P`. The initialization is procedure `b0`
and operation `i` is procedure `(LctProcs.atBase b0).op i`. -/
theorem lctDataStructure_implements (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (hL : L < 2 ^ w)
    (hP : P < 2 ^ w) (hp : p.HasAt b0 (lctBodies h L P b0)) :
    (lctDSRep w h L P).Implements w p b0 (LctProcs.atBase b0).op (lctDataStructure h L P) := by
  have hbase := lctBaseOk_of_hasAt hh hw hL hP hp
  have hsp : ∃ spB, (LctProcs.atBase b0).splay = SplayProcs.atBase spB := ⟨b0 + 11, rfl⟩
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, -, h9, h10⟩ := lctBodies_procs hp
  refine ⟨lctDSRep_local w h L P, ?_, ?_⟩
  · intro args mem pos ω _ hpre hz hroom
    obtain ⟨n, b, rfl⟩ := hpre
    obtain ⟨o, st', c, xI, hrun, -, hrep, hresp, hc⟩ :=
      lctInit_runs (n := n) (b := b) p mem pos hh hw hL hP hz hroom ω
    have hxn : xI.n = n := hrep.2.2.2.2.1
    refine ⟨_, h0, o, st', c, hrun, _, xI, hrep, rfl, hresp, ?_⟩
    show c + lctPhi L st'.mem b xI.n ≤ C_LCT_INIT * (n + 1)
    rw [hxn]
    exact hc
  · intro i b s x args mem pos ω hargs hhead hrep hpre hfoot hz hroom
    have hxn : x.n = s.n := hrep.2.2.2.2.1
    rcases i with _ | _ | _ | _ | _ | _ | _ | i
    · -- findRoot
      obtain ⟨b', v, hpc, rfl, hv⟩ := hpre
      obtain rfl : b' = b := Option.some.inj hhead
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hans, hlt, -, -, hc⟩ :=
        lctFindRootBody_runs p _ mem hbase hsp h9 hrep hv hfoot hz (room_of hroom) space_of ω
      have hx'n : x'.n = s.n := hrep'.2.2.2.2.1
      refine ⟨_, h1, _, st', c, hrun, s, x', hrep', ⟨rfl, hlt, ?_⟩, hresp, ?_⟩
      · have hs := (hrep.lctCanonRoot_spec hv).2.2.1
        rw [← hans] at hs
        exact hs
      · show c + lctPhi L st'.mem _ x'.n ≤ _ + lctPhi L mem _ x.n
        rw [hx'n, hxn]
        exact cost_of hc
    · -- link
      obtain ⟨b', u, v, eid, cPtr, fPtr, afPtr, abPtr, hpc, rfl, hu, hv, hdisc, hfresh, hfit,
        hcv, hcb, hfv, hfb, hafv, hafb, habv, habb⟩ := hpre
      obtain rfl : b' = b := Option.some.inj hhead
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, -⟩ :=
        lctLinkBody_runs (e := lctArgEdge h L P [b', u, v, eid, cPtr, fPtr, afPtr, abPtr, hpc] mem)
          p _ mem hbase hsp h9 h10 hrep hu hv hdisc hfresh (hargs eid (by simp)) hfit
          hcv hcb rfl hfv hfb rfl hafv hafb rfl habv habb rfl hfoot hz (room_of₂ hroom) space_of₂ ω
      have hx'n := hrep'.2.2.2.2.1
      refine ⟨_, h2, _, st', c, hrun, _, x', hrep', rfl, hresp, ?_⟩
      show c + lctPhi L st'.mem _ x'.n ≤ _ + lctPhi L mem _ x.n
      rw [hx'n, hxn]
      exact cost_of hc
    · -- cut
      obtain ⟨b', u, v, hpc, rfl⟩ := hpre
      obtain rfl : b' = b := Option.some.inj hhead
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, -⟩ :=
        lctCutBody_runs (x := u) (y := v) p _ mem hbase hsp h9 h10 hrep hfoot hz (room_of hroom)
          space_of ω
      have hx'n := hrep'.2.2.2.2.1
      refine ⟨_, h3, _, st', c, hrun, _, x', hrep', rfl, hresp, ?_⟩
      show c + lctPhi L st'.mem _ x'.n ≤ _ + lctPhi L mem _ x.n
      rw [hx'n, hxn]
      exact cost_of hc
    · -- pathAdd
      obtain ⟨b', u, v, dPtr, dNeg, hpc, rfl, hu, hv, hsc, hdNeg, hdv, hdb, hfit⟩ := hpre
      obtain rfl : b' = b := Option.some.inj hhead
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, -⟩ :=
        lctPathAddBody_runs p _ mem hbase hsp h9 h10 hrep hu hv hsc hdNeg hdv hdb rfl hfit hfoot
          hz (room_of₂ hroom) space_of₂ ω
      have hx'n := hrep'.2.2.2.2.1
      refine ⟨_, h4, _, st', c, hrun, _, x', hrep', rfl, hresp, ?_⟩
      show c + lctPhi L st'.mem _ x'.n ≤ _ + lctPhi L mem _ x.n
      rw [hx'n, hxn]
      exact cost_of hc
    · -- pathMin
      obtain ⟨b', u, v, hpc, rfl, hu, hv, hsc⟩ := hpre
      obtain rfl : b' = b := Option.some.inj hhead
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hans, hc, -⟩ :=
        lctPathMinBody_runs p _ mem hbase hsp h9 h10 hrep hu hv hsc hfoot hz (room_of₂ hroom)
          space_of₂ ω
      have hx'n : x'.n = s.n := hrep'.2.2.2.2.1
      refine ⟨_, h5, _, st', c, hrun, s, x', hrep', ⟨rfl, hans⟩, hresp, ?_⟩
      show c + lctPhi L st'.mem _ x'.n ≤ _ + lctPhi L mem _ x.n
      rw [hx'n, hxn]
      exact cost_of hc
    · -- pathSum
      obtain ⟨b', u, v, hpc, rfl, hu, hv, hsc, hfits⟩ := hpre
      obtain rfl : b' = b := Option.some.inj hhead
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hvalid, hval, hc, -⟩ :=
        lctPathSumBody_runs p _ mem hbase hsp h9 h10 hrep hu hv hsc hfoot hz (room_of₂ hroom)
          space_of₂ ω
      have hx'n : x'.n = s.n := hrep'.2.2.2.2.1
      refine ⟨_, h6, _, st', c, hrun, s, x', hrep', ⟨rfl, hvalid, ?_⟩, hresp, ?_⟩
      · exact hval.trans (wrap_of_fits hfits)
      · show c + lctPhi L st'.mem _ x'.n ≤ _ + lctPhi L mem _ x.n
        rw [hx'n, hxn]
        exact cost_of hc
    · -- connected
      obtain ⟨b', u, v, hpc, rfl, hu, hv⟩ := hpre
      obtain rfl : b' = b := Option.some.inj hhead
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hiff, hle, hc⟩ :=
        lctConnectedBody_runs p _ mem hbase hsp h1 h9 hrep hu hv hfoot hz (room_of hroom)
          space_of ω
      have hx'n : x'.n = s.n := hrep'.2.2.2.2.1
      refine ⟨_, h7, _, st', c, hrun, s, x', hrep', ⟨rfl, hle, hiff⟩, hresp, ?_⟩
      show c + lctPhi L st'.mem _ x'.n ≤ _ + lctPhi L mem _ x.n
      rw [hx'n, hxn]
      exact cost_of hc
    · exact hpre.elim

end LctImplements

end MinCostFlow.LinkCut.Prog
