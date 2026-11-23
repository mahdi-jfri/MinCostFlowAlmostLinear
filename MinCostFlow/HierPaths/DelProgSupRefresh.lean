module

public import MinCostFlow.HierPaths.DelProgCursorSetup

/-!
# Refreshing a support cursor

The program loads the old cursor, advances across invalid support entries, and writes it back.
Only the cursor word can change.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Refresh the support cursor of the vertex in register 39. -/
def delSupRefresh : Stmt :=
  .seq (delCursorSetup 9 20 3 (readHdr 0))
    (.seq (advanceStmt (supTestStmt 39 43 44 47 46) 43 42 45 46) (delCursorStore 20))

theorem delSupRefresh_noRand : delSupRefresh.NoRand := by
  simp [delSupRefresh, Stmt.NoRand, delCursorSetup_noRand, delCursorStore_noRand,
    advanceStmt_noRand (supTestStmt_noRand ..)]

/-- The support cursor refresh model changes just one index of the support cursor table. -/
def HierConcrete.refreshSup (x : HierConcrete) (q : ℕ) : HierConcrete :=
  let next := advance (x.H.A.supValid (x.H.A.surv x.ms.st) q) (x.H.A.C.supportArray q).length
    (x.ms.st.supCur q)
  x.withSt { x.ms.st with supCur := Function.update x.ms.st.supCur q next }

/-- Refresh one support cursor with a cost linear in the number of entries skipped, plus a constant. -/
theorem delSupRefresh_triple {w : ℕ} {p : Program} (x : HierConcrete) {b q : ℕ}
    {mem0 R : ℕ → ℕ} (h0 : R 0 = b) (h39 : R 39 = q)
    (hq : q < x.n) (hb : b + x.encode.length < 2 ^ w)
    (hN : (x.H.A.C.supportArray q).length + 1 < 2 ^ w)
    (hold : x.ms.st.supCur q ≤ (x.H.A.C.supportArray q).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun c =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) c)
    :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ s.mem = mem0)
      delSupRefresh (normalPost fun s => s.regs 0 = b ∧ s.regs 39 = q ∧
        ListAt s.mem b (x.refreshSup q).encode ∧
        ∀ i, (i < b ∨ b + x.encode.length ≤ i) → s.mem i = mem0 i)
      (fun _ => 150 + (advance (x.H.A.supValid (x.H.A.surv x.ms.st) q)
        (x.H.A.C.supportArray q).length (x.ms.st.supCur q) - x.ms.st.supCur q + 1) * 280) := by
  let n := (x.H.A.C.supportArray q).length
  let old := x.ms.st.supCur q
  let next := advance (x.H.A.supValid (x.H.A.surv x.ms.st) q) n old
  let M := fun mem => ListAt mem b x.encode ∧ mem = mem0
  let F := fun s : State => s.regs 0 = b ∧ s.regs 39 = q ∧ M s.mem ∧ s.regs 42 = n
  have hsec : x.sections.getD 20 [] = tabList x.n x.ms.st.supCur := rfl
  have hqc : q < (x.sections.getD 20 []).length := by rw [hsec]; simpa using hq
  have hword : (x.sections.getD 20 [])[q] = old := by
    rw [← List.getD_eq_getElem _ 0 hqc, hsec]
    simp [tabList, List.getD_eq_getElem?_getD, hq, old]
  have hone : 3 < 2 ^ w := by have := x.le_length_encode; omega
  have hsetup := delCursorSetup_triple (w := w) (p := p) x
    (lists := 9) (curs := 20) (width := 3) (count := readHdr 0) (M := M)
    (f := fun u => (x.H.A.C.supportArray u).flatMap entryWords)
    (by decide) (by decide) rfl hq h0 h39 hqc hword hone (fun _ hm => hm.1) hb
    (fun s hm hr => by
      simpa [HierConcrete.header, HierConcrete.n] using x.eval_readHdr hb hr hm.1 (k := 0) (by decide))
  have hadv := supAdvance_triple (w := w) (p := p) x (rw := 39) (rc := 43) (rN := 42)
    (rgo := 45) (rtag := 44) (rid := 47) (rv := 46)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hq hb hN hinel
    (F := F) (fun _ hs => ⟨hs.1, hs.2.1, hs.2.2.1.1⟩) (fun _ hs => hs.2.2.2)
    (fun _ _ hs => by simpa [F] using hs) (fun _ _ hs => by simpa [F] using hs)
    (fun _ _ hs => by simpa [F] using hs) (fun _ _ hs => by simpa [F] using hs)
    (fun _ _ hs => by simpa [F] using hs) hold
  have hstore := delCursorStore_triple (w := w) (p := p) x (x.refreshSup q)
    (sec := 20) (j := q) (next := next) (by decide) hqc (x.sections_setSupCur q next) hb
    (F := fun s => F s ∧ s.regs 43 = next)
    (fun _ hs => ⟨hs.1.1, hs.1.2.1, hs.2, hs.1.2.2.1.1⟩)
  have htail := Triple.seq_normal_const hadv hstore
  have hsetup' := hsetup.strengthen_post (Q' := normalPost fun s => F s ∧ s.regs 43 = old)
    (fun o s hp => by
      cases o <;> try contradiction
      obtain ⟨hr, hm'⟩ := hp
      refine ⟨⟨?_, ?_, hm', ?_⟩, ?_⟩
      · simpa [hr] using h0
      · simpa [hr] using h39
      · simp [hr, n, List.length_flatMap, length_entryWords]
      · simp [hr])
  unfold delSupRefresh
  refine ((Triple.seq_normal_const hsetup' htail).strengthen_post ?_).mono_cost ?_
  · intro o s hs
    cases o <;> try contradiction
    obtain ⟨s₀, hs₀, hr, hblock, hf⟩ := hs
    exact ⟨hr ▸ hs₀.1.1, hr ▸ hs₀.1.2.1, hblock,
      fun i hi => (hf i hi).trans (congrFun hs₀.1.2.2.1.2 i)⟩
  · intro s hs
    simp only [readHdr, readSec, secAddr, Expr.size]
    omega

end MinCostFlow.HierPaths

end
