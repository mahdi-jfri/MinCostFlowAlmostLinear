module

public import MinCostFlow.HierPaths.DelProgOutputScan

/-!
# Reporting vertices of a connector walk

The procedure reads the walk interval from section 10 and reports its vertices in order.
Only the pruned bits and the next output slots can change.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Read a connector's walk (connector in register 63) and report the pruned vertices. -/
def delOutputWalk : Stmt :=
  .seq (delCsrSetup 10 63 64 65 (readHdr 3))
    (forRange 66 (.reg 64) (.reg 65) (delReportRead (readSec numSec 0 10 (.reg 66))))

theorem delOutputWalk_noRand : delOutputWalk.NoRand := by
  simp [delOutputWalk, Stmt.NoRand, delCsrSetup_noRand, delReportRead_noRand, forRange, forUp]

theorem delOutputWalk_writesBelow : Stmt.WritesBelow 67 delOutputWalk := by
  simp [delOutputWalk, Stmt.WritesBelow, delCsrSetup, forRange, forUp, delReportRead,
    delReportVertex, delReportTest, delCursorSetup, delVhatSet, delVertexPush]

/-- Report the previously unpruned ends of support lists found on one connector walk. -/
theorem delOutputWalk_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base c : ℕ} {L : List ℕ} {mem0 R : ℕ → ℕ}
    (h0 : R 0 = b) (h58 : R 58 = base) (h59 : R 59 = L.length) (h63 : R 63 = c)
    (hb : b + x.encode.length ≤ base) (hw : base + L.length + x.n + 1 < 2 ^ w)
    (hc : c < x.H.A.C.numConn) (hv : ∀ v ∈ (x.H.A.C.walk c).verts, v < x.n) :
    let vs := (x.H.A.C.walk c).verts
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem base L ∧ s.mem = mem0) delOutputWalk
      (normalPost fun s =>
        let out := L ++ x.delReports vs
        s.regs 0 = b ∧ s.regs 58 = base ∧ s.regs 59 = out.length ∧
        ListAt s.mem b (x.afterReports vs).encode ∧ ListAt s.mem base out ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j)
      (fun _ => 200 * vs.length + 100) := by
  dsimp only
  let f := fun d => (x.H.A.C.walk d).verts
  let vs := f c
  let lo := delCsrStart x.H.A.C.numConn f c
  let hi := delCsrStart x.H.A.C.numConn f (c + 1)
  let R' := Function.update (Function.update R 64 lo) 65 hi
  let M := fun mem => ListAt mem b x.encode ∧ ListAt mem base L ∧ mem = mem0
  have hbw : b + x.encode.length < 2 ^ w := by omega
  have hsec : x.sections.getD 10 [] = csrList x.H.A.C.numConn f := rfl
  have hhi : hi = lo + vs.length := delCsrStart_succ ..
  have hhiw : lo + vs.length < 2 ^ w := by
    have hs : hi ≤ (x.sections.getD 10 []).length := by
      rw [hsec]
      exact delCsrStart_le _ _ hc
    have hpos : 0 < (x.sections.getD 10 []).length := by rw [hsec]; simp [csrList]
    have H := lt_length_of_sec (bs := x.sections) (i := 10)
      (by rw [x.length_sections']; decide)
      (k := (x.sections.getD 10 []).length - 1) (by omega)
    change _ < x.encode.length at H
    omega
  have hsetup := delCsrSetup_triple (w := w) (p := p) (r := 63) (lo := 64) (hi := 65)
    (M := M) (count := readHdr 3) (by decide) hsec hc h0 h63 (by decide) (by decide)
    (fun _ h => h.1) hbw (fun s hm hr => by
      simpa [HierConcrete.header] using x.eval_readHdr hbw hr hm.1 (k := 3) (by decide))
  have H := delReportScan_triple (w := w) (p := p) (r := 66) (rhi := 65) (lo := lo)
    (vs := vs) (L := L) (R := R') (mem0 := mem0) x (.reg 64)
    (readSec numSec 0 10 (.reg 66)) (by decide) (by decide) (by decide) hb hw hhiw
    (by simp [R', hhi]) hv (fun s hs _ => Expr.eval_reg_of_eq (by rw [hs]; simp [R']))
    ?_ (by simpa [R'] using h0) (by simpa [R'] using h58) (by simpa [R'] using h59)
  · refine ((Triple.seq_normal_const hsetup H).strengthen_post ?_).mono_cost ?_
    · intro o s h
      cases o <;> try contradiction
      obtain ⟨h0', h58', h59', _, hB, hL, hf⟩ := h
      exact ⟨h0', h58', h59', hB, hL, hf⟩
    · intro s _
      simp only [readHdr, readSec, secAddr, Expr.size]
      dsimp only [vs, f]
      omega
  · intro i hlo hi' s hs
    have hk : i - lo < vs.length := by omega
    have he : lo + (i - lo) = i := by omega
    let y := x.afterReports (vs.take (i - lo))
    obtain ⟨hs0, _, _, hext, hmem, _, _⟩ := hs
    have hy : b + y.encode.length < 2 ^ w := by
      rw [show y.encode.length = x.encode.length from x.length_encode_withVhat _]
      exact hbw
    have hsec' : y.sections.getD 10 [] = csrList x.H.A.C.numConn f := rfl
    have hword : i < (y.sections.getD 10 []).length := by
      rw [hsec', ← he]
      exact csrList_data_lt f hc hk
    have hval : (y.sections.getD 10 [])[i] = vs[i - lo] := by
      rw [← List.getD_eq_getElem _ 0 hword, hsec']
      conv_lhs => rw [← he]
      change (csrList x.H.A.C.numConn f).getD
        (x.H.A.C.numConn + 1 + ((List.range c).map fun j => (f j).length).sum + (i - lo)) 0 = _
      rw [csrList_getD_data _ hc hk, List.getD_eq_getElem _ _ hk]
    have hr : s.regs 66 = i := by rw [hext 66 (by decide), Function.update_self]
    have h := eval_readSec (w := w) (show ListAt s.mem b (layoutList y.sections) from hmem)
      hy (r := 0) hs0 (i := 10) (by rw [y.length_sections']; decide)
      (Expr.eval_reg_of_eq hr) hword
    rwa [y.length_sections', hval, ← List.getD_eq_getElem _ 0 hk] at h

end MinCostFlow.HierPaths

end
