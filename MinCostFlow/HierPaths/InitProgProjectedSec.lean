module

public import MinCostFlow.HierPaths.InitProgProjectedWriter

/-!
# Relocatable projected walk writers

Both walk sections use the same address traversal and flattening routines.
The last projection selects which column to write.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

/-- Shared helpers of each projected section, indexed by their final addresses. -/
def initProjectedHelpers (verts : Bool) (k : ℕ) : List Stmt :=
  [initEndpointWriter 2 (k + 22), initEndpointWriter 3 (k + 22),
    initFlatSeek 3 (k + 18), initCSRWrite (k + 5), moveDown,
    initProjectedRowProc (k + 6), initProjectAt (k + 7) (k + 8), initConnSeek (k + 18),
    initConnProject (k + 16) (k + 9) (k + 19) (k + 4),
    initFlatChain (k + 9) (k + 10), initFlatLevel (k + 2) (k + 11) (k + 12),
    initFlatSeek 4 (k + 18), initFlatPass (k + 13) (k + 14),
    initFlatEdge (k + 18) (k + 15), initFlatEnd, initFlatCopy (k + 16) (k + 17),
    copyUp, revCopyBody, initCSRSeek, initProject verts (k + 20),
    initProjectPass (k + 21) (k + 14), initProjectEmit verts] ++
    endpointHelpers (k + 22)

/-- The two relocatable writers for sections 10 and 11. -/
def projectedW (a : ℕ) (verts : Bool) : SecW a where
  body k := initProjectedWriter k (k + 1) (k + 2) (k + 3) (k + 4)
  helpers := initProjectedHelpers verts
  l S _ _ := initProjectedSection S verts
  cost S G _ := initProjectedWriterCost S G verts
  scratch S _ _ := initProjectedWriterScratch S verts
  noRand k := ⟨by simp [initProjectedWriter, storeSeq, initProjectedFinish, Stmt.NoRand], by
    simp [initProjectedHelpers, endpointHelpers, initEndpointWriter, Stmt.NoRand,
      initFlatSeek_noRand, initCSRWrite_noRand, moveDown, forRange, forUp,
      initProjectedRowProc_noRand, initProjectAt_noRand, initConnSeek_noRand, initConnProject_noRand,
      initFlatChain_noRand, initFlatLevel_noRand, initFlatPass_noRand, initFlatEdge_noRand,
      initFlatEnd_noRand, initFlatCopy_noRand, copyUp_noRand, revCopyBody, initCSRSeek_noRand,
      initProject_noRand, initProjectPass_noRand, initProjectEmit_noRand, initEndpointDepth_noRand,
      initEndpointLevel_noRand, initEndpointChild_noRand, initEndpointRange_noRand,
      initEndpointRow_noRand, initCSRCount_noRand, initEndpointCopy_noRand, initFillWord_noRand]⟩
  spec w p f k hp hh S G := by
    have hE (field idx : ℕ) (hfield : field < 4)
        (hidx : p.procs[idx]? = some (initEndpointWriter field (k + 22))) :
        MeetsContract w p idx (SecContract w (buildInv w S a G)
          ⟨idx, fun _ => initEndpointWords S field, fun _ => initEndpointSectionCost S, fun _ => 0⟩) :=
      initEndpointWriter_meetsContract hfield hidx
        (hh 22 (by simp [initProjectedHelpers, endpointHelpers]))
        (hh 23 (by simp [initProjectedHelpers, endpointHelpers]))
        (hh 24 (by simp [initProjectedHelpers, endpointHelpers]))
        (hh 25 (by simp [initProjectedHelpers, endpointHelpers]))
        (hh 26 (by simp [initProjectedHelpers, endpointHelpers]))
        (hh 27 (by simp [initProjectedHelpers, endpointHelpers]))
        (hh 28 (by simp [initProjectedHelpers, endpointHelpers]))
        (hh 29 (by simp [initProjectedHelpers, endpointHelpers]))
        (hh 30 (by simp [initProjectedHelpers, endpointHelpers]))
    have hSlots := hh 0 (by simp [initProjectedHelpers])
    have hIndices := hh 1 (by simp [initProjectedHelpers])
    have hRoot := hh 2 (by simp [initProjectedHelpers])
    have hCSR := hh 3 (by simp [initProjectedHelpers])
    have hMove := moveDown_meetsContract (w := w) (hh 4 (by simp [initProjectedHelpers]))
    have hRow := hh 5 (by simp [initProjectedHelpers])
    have hAt := hh 6 (by simp [initProjectedHelpers])
    have hSeek := hh 7 (by simp [initProjectedHelpers])
    have hConn := hh 8 (by simp [initProjectedHelpers])
    have hChain := hh 9 (by simp [initProjectedHelpers])
    have hLevel := hh 10 (by simp [initProjectedHelpers])
    have hEmb := hh 11 (by simp [initProjectedHelpers])
    have hPass := hh 12 (by simp [initProjectedHelpers])
    have hEdge := hh 13 (by simp [initProjectedHelpers])
    have hEnd := hh 14 (by simp [initProjectedHelpers])
    have hFlatCopy := hh 15 (by simp [initProjectedHelpers])
    have hCopy := hh 16 (by simp [initProjectedHelpers])
    have hRev := hh 17 (by simp [initProjectedHelpers])
    have hs := hh 18 (by simp [initProjectedHelpers])
    have hProj := hh 19 (by simp [initProjectedHelpers])
    have hProjPass := hh 20 (by simp [initProjectedHelpers])
    have hEmit := hh 21 (by simp [initProjectedHelpers])
    have hHostC := initFlatSeek_meetsContract (S := S) (w := w)
      (D := leafDepth S.x S.b + 1) (f := initHostRow S) hRoot hs
    have hEmbC := initFlatSeek_meetsContract (S := S) (w := w)
      (D := leafDepth S.x S.b) (f := initEmbRow S) hEmb hs
    have hChainC := initFlatChain_meetsContract (w := w) (S := S) hChain fun _ _ _ _ =>
      initFlatLevel_meetsContract hLevel hHostC hEmbC
        (initFlatPass_meetsContract hPass
          (fun _ _ => initFlatEdge_meetsContract hEdge hs hFlatCopy hCopy hRev)
          (fun _ _ => initFlatEnd_meetsContract hEnd))
    have hProjC := fun u v es =>
      initProject_meetsContract (w := w) (S := S) (G := G) (u := u) (v := v) (es := es)
        hProj (initProjectPass_meetsContract hProjPass
          (fun _ _ => initProjectEmit_meetsContract hEmit)
          (fun _ _ => initFlatEnd_meetsContract hEnd))
    refine initProjectedWriter_meetsContract (verts := verts) hp
      (hE 2 _ (by decide) (by simpa [initProjectedHelpers] using hSlots))
      (hE 3 _ (by decide) hIndices) hHostC (fun _ => ?_) hMove
    exact initProjectedCSR_meetsContract hCSR hRow fun q =>
      initProjectAt_meetsContract (q := q) hAt (fun _ => initConnSeek_meetsContract hSeek hs)
        (fun _ _ _ _ _ => initConnProject_meetsContract hConn (copyUp_meetsContract hCopy)
          (hChainC _ _ _ _ _) (hProjC _ _ _) hMove)

end MinCostFlow.HierPaths

end
