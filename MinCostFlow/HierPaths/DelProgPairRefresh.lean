module

public import MinCostFlow.HierPaths.DelProgCursorSetup

/-!
# Refreshing a pair cursor

The program loads the old cursor, advances across ineligible connectors, and writes it back.
Only the cursor word can change.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Refresh the cursor of the pair in register 39. -/
def delPairRefresh : Stmt :=
  .seq (delCursorSetup 8 21 1 (readHdr 4))
    (.seq (advanceStmt (pairTestStmt 39 43 44 46) 43 42 45 46) (delCursorStore 21))

theorem delPairRefresh_noRand : delPairRefresh.NoRand := by
  simp [delPairRefresh, Stmt.NoRand, delCursorSetup_noRand, delCursorStore_noRand,
    advanceStmt_noRand (pairTestStmt_noRand ..)]

/-- The pair cursor refresh model changes just one index of the pair cursor table. -/
def HierConcrete.refreshPair (x : HierConcrete) (q : ℕ) : HierConcrete :=
  let next := advance (x.H.A.pairValid (x.H.A.surv x.ms.st) q) (x.H.A.pairConns q).length
    (x.ms.st.pairCur q)
  x.withSt { x.ms.st with pairCur := Function.update x.ms.st.pairCur q next }

/-- Refresh one pair with a cost linear in the number of entries skipped, plus a constant. -/
theorem delPairRefresh_triple {w : ℕ} {p : Program} (x : HierConcrete) {b q : ℕ}
    {mem0 R : ℕ → ℕ} (h0 : R 0 = b) (h39 : R 39 = q)
    (hq : q < x.H.A.numPairs) (hb : b + x.encode.length < 2 ^ w)
    (hN : (x.H.A.pairConns q).length + 1 < 2 ^ w)
    (hold : x.ms.st.pairCur q ≤ (x.H.A.pairConns q).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun c =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) c)
    (hmem : ∀ c ∈ x.H.A.pairConns q, c < x.H.A.C.numConn) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ s.mem = mem0)
      delPairRefresh (normalPost fun s => s.regs 0 = b ∧ s.regs 39 = q ∧
        ListAt s.mem b (x.refreshPair q).encode ∧
        ∀ i, (i < b ∨ b + x.encode.length ≤ i) → s.mem i = mem0 i)
      (fun _ => 150 + (advance (x.H.A.pairValid (x.H.A.surv x.ms.st) q)
        (x.H.A.pairConns q).length (x.ms.st.pairCur q) - x.ms.st.pairCur q + 1) * 90) := by
  let n := (x.H.A.pairConns q).length
  let old := x.ms.st.pairCur q
  let next := advance (x.H.A.pairValid (x.H.A.surv x.ms.st) q) n old
  let M := fun mem => ListAt mem b x.encode ∧ mem = mem0
  let F := fun s : State => s.regs 0 = b ∧ s.regs 39 = q ∧ M s.mem ∧ s.regs 42 = n
  have hsec : x.sections.getD 21 [] = tabList x.H.A.numPairs x.ms.st.pairCur := rfl
  have hqc : q < (x.sections.getD 21 []).length := by rw [hsec]; simpa using hq
  have hword : (x.sections.getD 21 [])[q] = old := by
    rw [← List.getD_eq_getElem _ 0 hqc, hsec]
    simp [tabList, List.getD_eq_getElem?_getD, hq, old]
  have hone : 1 < 2 ^ w := by omega
  have hsetup := delCursorSetup_triple (w := w) (p := p) x
    (lists := 8) (curs := 21) (width := 1) (count := readHdr 4) (M := M)
    (by decide) (by decide) rfl hq h0 h39 hqc hword hone (fun _ hm => hm.1) hb
    (fun s hm hr => by
      simpa [HierConcrete.header] using x.eval_readHdr hb hr hm.1 (k := 4) (by decide))
  have hadv := pairAdvance_triple (w := w) (p := p) x (rq := 39) (rc := 43) (rN := 42)
    (rgo := 45) (rcon := 44) (rv := 46)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hq hb hN hinel hmem
    (F := F) (fun _ hs => ⟨hs.1, hs.2.1, hs.2.2.1.1⟩) (fun _ hs => hs.2.2.2)
    (fun _ _ hs => by simpa [F] using hs) (fun _ _ hs => by simpa [F] using hs)
    (fun _ _ hs => by simpa [F] using hs) (fun _ _ hs => by simpa [F] using hs) hold
  have hstore := delCursorStore_triple (w := w) (p := p) x (x.refreshPair q)
    (sec := 21) (j := q) (next := next) (by decide) hqc (x.sections_setPairCur q next) hb
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
      · simp [hr, n]
      · simp [hr])
  unfold delPairRefresh
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
