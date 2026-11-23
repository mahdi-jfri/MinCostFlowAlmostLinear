module

public import MinCostFlow.HierPaths.InitProgProjectStep

/-!
# Scanning a flattened root walk

The scan writes the labels or the owners before labelled steps. Its state
keeps the current host terminal and the end of the output written so far.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Arguments are the host, labels, owners, input list and length, start
terminal and destination. -/
def initProjectPass (emit finish : ℕ) : Stmt :=
  .assign 7 (.reg 5) ;;
  forRange 8 (.const 0) (.reg 4)
    (.assign 9 (.load (.bin .add (.reg 3) (.reg 8))) ;;
      .call 6 emit [.reg 1, .reg 2, .reg 9, .reg 7, .reg 6] ;;
      .call 7 finish [.reg 0, .reg 9, .reg 7]) ;;
  .ret (.reg 6)

theorem initProjectPass_noRand (emit finish : ℕ) : (initProjectPass emit finish).NoRand := by
  simp [initProjectPass, forRange, forUp, Stmt.NoRand]

/-- The scan preserves the host, arrays and input walk and writes only the
selected projection words. -/
def initProjectPassContract (w : ℕ) (S : StaticData) (verts : Bool) (u : ℕ)
    (es : List ℕ) : Contract where
  pre args mem := ∃ g L O src dst, args = [g, L, O, src, es.length, u, dst] ∧
    GraphAt mem g (S.H.host 0 0) ∧ ListAt mem src es ∧
    g + (S.H.host 0 0).encode.length ≤ dst ∧ src + es.length ≤ dst ∧
    L + (S.H.host 0 0).m ≤ dst ∧ O + S.numTerm ≤ dst ∧
    (∀ e < (S.H.host 0 0).m, mem (L + e) = labelWord (S.label e)) ∧
    (∀ t < S.numTerm, mem (O + t) = S.owner t ∧ S.owner t < 2 ^ w) ∧
    (∀ e ∈ es, e < (S.H.host 0 0).m ∧ labelWord (S.label e) < 2 ^ w ∧
      (edgeAt (S.H.host 0 0).edges e).1 < S.numTerm ∧
      (edgeAt (S.H.host 0 0).edges e).2 < S.numTerm) ∧
    u < S.numTerm ∧ 1 < 2 ^ w ∧ dst + (initProjectWords S verts u es).length < 2 ^ w
  post args mem v mem' := ∃ g L O src dst, args = [g, L, O, src, es.length, u, dst] ∧
    v = dst + (initProjectWords S verts u es).length ∧
    ListAt mem' dst (initProjectWords S verts u es) ∧
    ∀ y, y < dst ∨ v ≤ y → mem' y = mem y
  cost _ _ := 100 * es.length + 25

private theorem initProjectTerminal_lt (S : StaticData) (u : ℕ) (es : List ℕ)
    (hu : u < S.numTerm)
    (he : ∀ e ∈ es, (edgeAt (S.H.host 0 0).edges e).1 < S.numTerm ∧
      (edgeAt (S.H.host 0 0).edges e).2 < S.numTerm) :
    ∀ i ≤ es.length, initFlatTerminal (S.H.host 0 0) u es i < S.numTerm := by
  intro i hi
  cases i with
  | zero => exact hu
  | succ i =>
    have hi' : i < es.length := hi
    rw [initFlatTerminal_succ _ _ _ _ hi']
    obtain ⟨h₁, h₂⟩ := he _ (List.getElem_mem hi')
    unfold otherEnd
    split
    · exact h₂
    · exact h₁

theorem initProjectPass_meetsContract {w f emit finish : ℕ} {p : Program} {S : StaticData}
    {verts : Bool} {u : ℕ} {es : List ℕ} (hp : p.procs[f]? = some (initProjectPass emit finish))
    (hEmit : ∀ e t, MeetsContract w p emit (initProjectEmitContract w S.owner (S.label e) verts e t))
    (hEnd : ∀ e t, MeetsContract w p finish (initFlatEndContract w (S.H.host 0 0) e t)) :
    MeetsContract w p f (initProjectPassContract w S verts u es) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨g, L, O, src, dst, rfl, hG, hsrc, hg, hs, hL, hO, hlabel, howner,
    hedges, hu, h1, hroom⟩ := hpre
  let G := S.H.host 0 0
  let chunks := initProjectChunk S verts u es
  let R := fun (i : ℕ) (s : State) => s.regs 0 = g ∧ s.regs 1 = L ∧ s.regs 2 = O ∧
    s.regs 3 = src ∧ s.regs 4 = es.length ∧ s.regs 7 = initFlatTerminal G u es i
  have heq : initAppendPrefix chunks es.length = initProjectWords S verts u es :=
    initProjectPrefix_eq S verts u es
  change g + G.encode.length ≤ dst at hg
  change L + G.m ≤ dst at hL
  have hGroom : g + G.encode.length < 2 ^ w := by omega
  have hP : S.numTerm < 2 ^ w := by omega
  have hM : G.m < 2 ^ w := by omega
  have hloop := initAppendIndexedLoop_triple (w := w) (p := p) (dstReg := 6) (idxReg := 8)
    (hi := .reg 4) (body := .assign 9 (.load (.bin .add (.reg 3) (.reg 8))) ;;
      .call 6 emit [.reg 1, .reg 2, .reg 9, .reg 7, .reg 6] ;;
      .call 7 finish [.reg 0, .reg 9, .reg 7]) R chunks (fun _ => 90) es.length dst mem
    (by decide) h1 (hw _ (by simp)) (fun s i hr => by simpa [R] using hr)
    (fun _ _ hr => Expr.eval_reg_of_eq hr.2.2.2.2.1) ?_
  · refine runs_start_le ?_
    unfold initProjectPass
    refine runs_seq_assign_le (v := u) (Expr.eval_reg_of_eq rfl) ?_
    refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩ ?_
    intro t ⟨_, hp, hwr, hf⟩
    rw [heq] at hp hwr hf
    refine runs_ret_le (v := t.regs 6) (Expr.eval_reg_of_eq rfl)
      ⟨g, L, O, src, dst, rfl, hp, hwr, fun y hy => hf y (by rwa [hp] at hy)⟩ ?_
    simp [initProjectPassContract, Expr.size]
    omega
  intro i hi s hr hidx hdst hbefore st ω' hst
  subst st
  obtain ⟨r0, r1, r2, r3, r4, r7⟩ := hr
  let e := es[i]
  let cur := initFlatTerminal G u es i
  let out := dst + (initAppendPrefix chunks i).length
  let words := initProjectEntry S.owner (S.label e) verts cur
  have hcur : cur < S.numTerm := initProjectTerminal_lt S u es hu
    (fun e he => (hedges e he).2.2) i hi.le
  have heqCur : initFlatTerminal G u es (i + 1) = otherEnd G.edges e cur :=
    initFlatTerminal_succ _ _ _ _ hi
  have hchunk : chunks i = words := by
    simp only [chunks, initProjectChunk, getElem!_pos es i hi, words, cur, G]
    rfl
  have hout : dst + (initAppendPrefix chunks (i + 1)).length = out + words.length := by
    rw [initAppendPrefix_succ, List.length_append, Nat.add_assoc, hchunk]
  have hword : out + words.length < 2 ^ w := by
    rw [← hout]
    apply lt_of_le_of_lt (Nat.add_le_add_left (initAppendPrefix_length_mono chunks hi) dst)
    simpa only [heq] using hroom
  have hdout : dst ≤ out := Nat.le_add_right _ _
  have hload : s.mem (src + i) = e := (hbefore _ (by omega)).trans (hsrc i hi)
  obtain ⟨he, hel, h₁, h₂⟩ := hedges e (List.getElem_mem hi)
  change e < G.m at he
  have hew : e < 2 ^ w := he.trans hM
  have hcw : cur < 2 ^ w := hcur.trans hP
  have hL' : L + e < dst := by omega
  have hO' : O + cur < dst := by omega
  have hLmem : s.mem (L + e) = labelWord (S.label e) :=
    (hbefore _ hL').trans (hlabel e he)
  have hOmem : s.mem (O + cur) = S.owner cur :=
    (hbefore _ hO').trans (howner cur hcur).1
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := e) (Expr.eval_load_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_reg_of_eq hidx) (by omega)) hload) ?_
  refine runs_seq_call_le (hEmit e cur) (vs := [L, O, e, cur, out])
    (by simp [evalArgs, Expr.eval, r1, r2, r7, hdst, out, cur]) ?_
    ⟨L, O, out, rfl, by omega, by omega, hLmem, hOmem, hel, (howner cur hcur).2, hword, h1⟩ ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | omega
  intro r mem₁ pos₁ hp₁
  obtain ⟨L', O', dst', hargs, hr, hwrite, hf⟩ := hp₁
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨_, _, _, _, hd⟩ := hargs
  subst dst' r
  have hG₁ : GraphAt mem₁ g G :=
    listAt_congr (fun k hk => ((hf _ (.inl (by omega))).trans (hbefore _ (by omega))).symm) hG
  refine runs_call_le (hEnd e cur) (vs := [g, e, cur])
    (by simp [evalArgs, Expr.eval, r0, r7, cur]) ?_
    ⟨g, rfl, hG₁, he, hGroom, h₁.trans hP, h₂.trans hP⟩ ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | assumption | omega
  · intro r mem₂ pos₂ hp₂
    obtain ⟨hr, hm⟩ := hp₂
    subst r mem₂
    refine ⟨⟨?_, by simpa using hidx, ?_, ?_, ?_⟩, ?_⟩
    · simp [R, r0, r1, r2, r3, r4, heqCur, G]
    · exact hout.symm
    · simpa only [hchunk] using hwrite
    · simpa only [hout] using hf
    · simp [initProjectEmitContract, initFlatEndContract, Expr.size, argsSize]

end MinCostFlow.HierPaths

end
