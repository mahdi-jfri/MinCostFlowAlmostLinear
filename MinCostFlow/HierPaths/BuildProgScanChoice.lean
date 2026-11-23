module

public import MinCostFlow.HierPaths.BuildProgPrepareChoice
public import MinCostFlow.HierPaths.BuildProgGameScan

/-!
# Scanning the active inputs with certified choices

The core reply is chosen at each call. The scan records its address and
keeps its certificate in the invariant. Equal graph inputs can therefore
have different valid answers.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Per-child heap advance upper bound under the bump core contract. -/
def scanStepSpace (sC : ℕ → ℕ) (J : BuildGameJobs) (s i : ℕ) : ℕ :=
  sC (J.graph i).encode.length + 3 * s

/-- A prefix of certified replies with its address table, bump sizes, and end. -/
structure ChoiceRepliesAt (J : BuildGameJobs) (M q h replies n top : ℕ)
    (mem : ℕ → ℕ) (sC : ℕ → ℕ) (answer : ℕ → CoreResult) (bump addr : ℕ → ℕ) : Prop where
  first : addr 0 = h
  last : addr n = top
  mono : ∀ i ≤ n, ∀ j ≤ n, i ≤ j → addr i ≤ addr j
  rows : ∀ i < n, mem (replies+i) = addr i ∧
    CoreOutcomeSpec ParamConfig.default M q (J.graph i) (answer i) ∧
    PreparedChildAt mem (addr i) (addr (i+1)) (J.graph i).n (J.offset i) (answer i) ∧
    addr (i+1) = preparedChildEnd (addr i) (J.graph i).n (answer i) + bump i ∧
    preparedChildEnd 0 (J.graph i).n (answer i) + bump i ≤
      sC (J.graph i).encode.length + 3 * (J.graph i).n

/-- Prepare all active children under the bump core contract. The space bound
accumulates `sC |G_i| + 3 * s` per child and does not depend on the choice made by the core. -/
def buildScanChoiceContract (w K M r q s : ℕ) (coreCost : ℕ → Graph → ℕ)
    (sC : ℕ → ℕ) (J : BuildGameJobs) : Contract where
  pre args mem := ∃ graphs offsets h replies,
    args = [q,M,r,J.count,graphs,offsets,h,replies] ∧
    graphs + J.count ≤ replies ∧ offsets + J.count ≤ replies ∧ replies + J.count + 1 ≤ h ∧
    1 < 2^w ∧ h < 2^w ∧ q ≤ r ∧ r ≤ ell M ∧ ZeroFrom mem h ∧
    ListAt mem graphs (tabList J.count J.addr) ∧ ListAt mem offsets (tabList J.count J.offset) ∧
    ∀ i < J.count, J.ChildFits w M r q replies mem i ∧ (J.graph i).n = s ∧
      h + rangeCost (scanStepSpace sC J s) 0 i + sC (J.graph i).encode.length + 3 * s < 2^w
  post args mem v mem' := ∃ graphs offsets h replies,
    args = [q,M,r,J.count,graphs,offsets,h,replies] ∧
    h ≤ v ∧ v ≤ h + rangeCost (scanStepSpace sC J s) 0 J.count ∧ ZeroFrom mem' v ∧
    (∀ a < replies, mem' a = mem a) ∧
    (∀ a, replies+J.count+1 ≤ a → a<h → mem' a = mem a) ∧
    mem' (replies + J.count) = v ∧
    ∃ answer bump addr, ChoiceRepliesAt J M q h replies J.count v mem' sC answer bump addr
  cost _ _ := rangeCost (prepGameStepCost J K q coreCost) 0 J.count + 9*J.count+28

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- A certified cut or expander uses four header words and at most one word per vertex. -/
theorem coreWord_bound {G : Graph} {M q : ℕ} {res : CoreResult}
    (h : CoreOutcomeSpec ParamConfig.default M q G res) :
    (coreResultWords res).length ≤ 4 + G.n := by
  cases res with
  | cut U =>
    have hh := Finset.card_le_card h.1
    simp [Graph.verts] at hh
    simp [coreResultWords,layoutList,csrList,csrOffsets,csrData,List.range_succ,finsetWords]
    omega
  | expander S =>
    have hh := Finset.card_le_card h.1
    simp [Graph.verts] at hh
    simp [coreResultWords,layoutList,csrList,csrOffsets,csrData,List.range_succ,finsetWords]
    omega

private def scanChoiceInv (J : BuildGameJobs) (sC : ℕ → ℕ) (M r q s graphs offsets h replies : ℕ)
    (mem : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = q ∧ st.regs 1 = M ∧ st.regs 2 = r ∧ st.regs 3 = J.count ∧
  st.regs 4 = graphs ∧ st.regs 5 = offsets ∧ st.regs 8 = i ∧ st.regs 7 = replies ∧
  h ≤ st.regs 6 ∧ st.regs 6 ≤ h + rangeCost (scanStepSpace sC J s) 0 i ∧ ZeroFrom st.mem (st.regs 6) ∧
  (∀ a < replies, st.mem a = mem a) ∧
  (∀ a, replies+i ≤ a → a<h → st.mem a = mem a) ∧
  ∃ ans bump addr, ChoiceRepliesAt J M q h replies i (st.regs 6) st.mem sC ans bump addr

private lemma rangeCost_succ_zero (f : ℕ → ℕ) (i : ℕ) :
    rangeCost f 0 (i + 1) = rangeCost f 0 i + f i := by
  rw [rangeCost_zero_eq_range, rangeCost_zero_eq_range, List.range_succ, List.map_append,
    List.sum_append, List.map_singleton, List.sum_singleton]

private theorem scanChoice_step {w K M r q s graphs offsets h replies f i : ℕ}
    {p : Program} {J : BuildGameJobs} {mem : ℕ → ℕ}
    {coreCost : ℕ → Graph → ℕ} {sC : ℕ → ℕ}
    (hProc : ∀ G, MeetsContract w p f (buildPrepareChoiceContract w K M r q coreCost sC G))
    (hArgs : ∀ a ∈ [q,M,r,J.count,graphs,offsets,h,replies], a < 2^w)
    (hq : q ≤ r) (hrl : r ≤ ell M) (hi : i < J.count) (hGO : graphs+J.count ≤ replies)
    (hOO : offsets+J.count ≤ replies) (hRO : replies+J.count+1 ≤ h)
    (hGraphs : ListAt mem graphs (tabList J.count J.addr))
    (hOffsets : ListAt mem offsets (tabList J.count J.offset))
    (hJob : ∀ j < J.count, J.ChildFits w M r q replies mem j ∧ (J.graph j).n = s ∧
      h + rangeCost (scanStepSpace sC J s) 0 j + sC (J.graph j).encode.length + 3*s < 2^w) :
    Triple w p (scanChoiceInv J sC M r q s graphs offsets h replies mem i) (buildGameScanStep f)
      (normalPost fun st => scanChoiceInv J sC M r q s graphs offsets h replies mem (i+1)
        { st with regs := Function.update st.regs 8 (i+1) } ∧ st.regs 8 = i)
      (fun _ => prepGameStepCost J K q coreCost i) := by
  intro st ω ⟨h0,h1,h2,h3,h4,h5,h8,h7,hTop,hMax,hZero,hBelow,hGap,ans,bump,addr,hPrev⟩
  let top := st.regs 6
  let G := J.graph i
  have hiTop : h ≤ top := hTop
  have hmax : top ≤ h + rangeCost (scanStepSpace sC J s) 0 i := hMax
  have hrTop : replies+i < top := by omega
  obtain ⟨⟨hGraph,hGE,hValid,hLoop,hn,hDeg,hs,ho⟩,hSize,hRoom⟩ := hJob i hi
  change G.n = s at hSize
  change J.addr i + G.encode.length ≤ replies at hGE
  have hFit : top+sC G.encode.length+3*G.n < 2^w := by
    rw [hSize]
    dsimp only [G]
    omega
  have hw : top < 2^w := by omega
  have hG' : GraphAt st.mem (J.addr i) G :=
    WordRAM.ListAt.congr hGraph (fun a _ ha => hBelow a (ha.trans_le hGE))
  have hga : graphs+i < 2^w := by omega
  have hoa : offsets+i < 2^w := by omega
  have hgRead : st.mem (graphs+i) = J.addr i :=
    (hBelow _ (by omega)).trans (listAt_tabList hGraphs hi)
  have hoRead : st.mem (offsets+i) = J.offset i :=
    (hBelow _ (by omega)).trans (listAt_tabList hOffsets hi)
  refine runs_start_le ?_
  unfold buildGameScanStep
  refine runs_seq_call_le (hProc G) (vs := [q,J.addr i,M,r,top,J.offset i]) ?_ ?_
    ⟨J.addr i,top,J.offset i,rfl,
      ⟨⟨J.addr i,top,rfl,hG',hGE.trans (by omega),hq,hrl,hValid,hLoop,hn,hDeg⟩,hZero,by
        change top+sC G.encode.length < 2^w; omega⟩,hs,ho,hFit⟩ ?_
  · simp [evalArgs,Expr.eval,h0,h1,h2,h4,h5,h8,hgRead,hoRead,hga,hoa,top]
  · have hwq := hArgs q (by simp)
    have hwM := hArgs M (by simp)
    have hwr := hArgs r (by simp)
    change J.offset i+G.n < 2^w at ho
    wram_words
  intro v after pos' hPost
  obtain ⟨_,_,_,eq,hLo,hHi,hFrame,hZ',res,hSpec,hReply⟩ := hPost
  simp only [List.cons.injEq,and_true,true_and] at eq
  obtain ⟨rfl,rfl,rfl⟩ := eq
  have hLeEnd : preparedChildEnd top G.n res ≤ v := hReply.le_end
  let bVal := v - preparedChildEnd top G.n res
  have hbEq : v = preparedChildEnd top G.n res + bVal := by omega
  have hbLe : preparedChildEnd 0 G.n res + bVal ≤ sC G.encode.length + 3 * G.n := by
    have hShift : preparedChildEnd top G.n res = top + preparedChildEnd 0 G.n res := by
      cases res <;> simp only [preparedChildEnd] <;> omega
    omega
  have hEnd : v ≤ top + scanStepSpace sC J s i := by
    have hHi' : v ≤ top + sC (J.graph i).encode.length + 3 * (J.graph i).n := hHi
    have hSize' : (J.graph i).n = s := hSize
    dsimp only [scanStepSpace]
    omega
  have hFit' : replies+i < 2^w := hrTop.trans hw
  refine runs_seq_store_le (x := replies+i) (v := top) ?_ ?_ ?_
  · simp [Expr.eval,Function.update,h7,h8,hFit']
  · simp [Expr.eval,Function.update,top]
  refine runs_assign_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · let next := Function.update after (replies+i) top
    refine ⟨⟨by simpa using h0,by simpa using h1,by simpa using h2,by simpa using h3,
      by simpa using h4,by simpa using h5,by simp,by simpa using h7,?_,?_,?_,?_,?_,?_⟩,
      by simpa using h8⟩
    · exact hTop.trans hLo
    · rw [rangeCost_succ_zero, ← Nat.add_assoc]
      exact hEnd.trans (Nat.add_le_add_right hMax _)
    · intro a ha
      change next a = 0
      have hc : a ≠ replies+i := by change v ≤ a at ha; omega
      exact (Function.update_of_ne hc ..).trans (hZ' a ha)
    · intro a ha
      change next a = mem a
      exact (Function.update_of_ne (by omega : a ≠ replies+i) ..).trans
        ((hFrame a (by omega)).trans (hBelow a ha))
    · intro a hlo hhi
      change next a = mem a
      exact (Function.update_of_ne (by omega : a ≠ replies+i) ..).trans
        ((hFrame a (by omega)).trans (hGap a (by omega) hhi))
    · change ∃ ans bump addr, ChoiceRepliesAt J M q h replies (i+1) v next sC ans bump addr
      let answers := Function.update ans i res
      let bumps := Function.update bump i bVal
      let cursors := Function.update addr (i+1) v
      have hCur (j : ℕ) (hj : j ≤ i) : cursors j = addr j := Function.update_of_ne (by omega) ..
      have hLast : addr i = top := hPrev.last
      refine ⟨answers,bumps,cursors, (hCur 0 (Nat.zero_le _)).trans hPrev.first,by simp [cursors],?_,?_⟩
      · intro a ha b hb hab
        by_cases hb' : b ≤ i
        · rw [hCur a (hab.trans hb'),hCur b hb']
          exact hPrev.mono a (hab.trans hb') b hb' hab
        · have hbEq' : b = i+1 := by omega
          subst b
          by_cases ha' : a ≤ i
          · rw [hCur a ha']
            have hm := hPrev.mono a ha' i le_rfl ha'
            exact (hm.trans (hLast.trans_le hLo)).trans (by simp [cursors])
          · have : a = i+1 := by omega
            subst a
            exact le_rfl
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · obtain ⟨hPtr,hSpec,hBlock,hAddrEq,hBumpLe⟩ := hPrev.rows j hj
          have hLower : h ≤ addr j := hPrev.first ▸ hPrev.mono 0 (Nat.zero_le _) j hj.le (Nat.zero_le _)
          have hUpper : addr (j+1) ≤ top :=
            (hPrev.mono _ (Nat.succ_le_of_lt hj) i le_rfl (Nat.succ_le_of_lt hj)).trans (hLast.le)
          have hjAnswer : answers j = ans j := Function.update_of_ne (Nat.ne_of_lt hj) ..
          have hjBump : bumps j = bump j := Function.update_of_ne (Nat.ne_of_lt hj) ..
          rw [hCur j hj.le,hCur (j+1) (Nat.succ_le_of_lt hj),hjAnswer,hjBump]
          refine ⟨(Function.update_of_ne (by omega : replies+j ≠ replies+i) ..).trans
            ((hFrame _ (by omega)).trans hPtr),hSpec,?_,hAddrEq,hBumpLe⟩
          refine hBlock.frame (fun a hlo hhi => ?_) (fun U he => ?_)
          · exact (Function.update_of_ne (by omega : a ≠ replies+i) ..).trans
              (hFrame a (hhi.trans_le hUpper))
          · rw [he] at hSpec
            exact hSpec.1
        · rw [hCur _ le_rfl,hLast]
          simp only [answers,bumps,cursors,Function.update_self]
          refine ⟨by simp [next],hSpec,?_,hbEq,hbLe⟩
          refine hReply.frame (fun a hlo _ => Function.update_of_ne (by omega : a ≠ replies+j) ..)
            (fun U he => ?_)
          rw [he] at hSpec
          exact hSpec.1
  · simp [prepGameStepCost,buildPrepareChoiceContract,Expr.size,argsSize,G]; omega

/-- The same active scan accepts the existential core contract and retains
one certified reply for every child, plus `replies[count] = top`. -/
theorem buildScanChoiceProc_meetsContract {w K M r q s f child : ℕ} {p : Program}
    {coreCost : ℕ → Graph → ℕ} {sC : ℕ → ℕ} {J : BuildGameJobs}
    (hf : p.procs[f]? = some (buildGameScanProc child))
    (hChild : ∀ G, MeetsContract w p child (buildPrepareChoiceContract w K M r q coreCost sC G)) :
    MeetsContract w p f (buildScanChoiceContract w K M r q s coreCost sC J) := by
  refine meetsContract_of_runs hf fun args mem pos ω hArgs hPre => ?_
  obtain ⟨graphs,offsets,h,replies,rfl,hGO,hOO,hRO,hw,hh,hq,hrl,hZero,hGraphs,hOffsets,hJob⟩ := hPre
  let st₀ := startState [q,M,r,J.count,graphs,offsets,h,replies] mem pos
  have hLoop := Triple.forRange_le (p := p) (r := 8) (lo := .const 0) (hi := .reg 3)
    (body := buildGameScanStep child) (P := fun st => st = st₀)
    (Inv := scanChoiceInv J sC M r q s graphs offsets h replies mem)
    (prepGameStepCost J K q coreCost) 0 J.count (Nat.zero_le _) hw
    (fun _ => hArgs J.count (by simp))
    (fun st he => by
      subst st
      exact ⟨Expr.eval_const (Nat.two_pow_pos _),rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
        le_rfl,by simp [st₀,startState,rangeCost],hZero,(fun _ _ => rfl),(fun _ _ _ => rfl),
        (fun _ => .cut ∅),(fun _ => 0),(fun _ => h),rfl,rfl,(fun _ _ _ _ _ => le_rfl),
        fun j hj => (Nat.not_lt_zero j hj).elim⟩)
    (fun _ _ _ _ hm => hm.2.2.2.2.2.2.1)
    (fun _ _ _ _ hm => Expr.eval_reg_of_eq hm.2.2.2.1)
    (fun _ _ hi => scanChoice_step hChild hArgs hq hrl hi hGO hOO hRO hGraphs hOffsets hJob)
  refine runs_start_le ?_
  unfold buildGameScanProc
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨_,_,_,hCnt,_,_,_,hRep,hLo,hHi,hZ,hFrame,hGap,ans,bump,addr,hChoices⟩
  have hRepCntW : replies + J.count < 2 ^ w := by omega
  refine runs_seq_store_le (x := replies + J.count) (v := st.regs 6)
    (by simp [Expr.eval, hRep, hCnt, hRepCntW])
    (Expr.eval_reg_of_eq rfl) ?_
  refine runs_ret_le (Expr.eval_reg_of_eq rfl) ?_ ?_
  · let mem' := Function.update st.mem (replies + J.count) (st.regs 6)
    refine ⟨graphs,offsets,h,replies,rfl,hLo,hHi,?_,?_,?_,by simp [Outcome.value],ans,bump,addr,?_,?_,?_,?_⟩
    · intro a ha
      simp only [Outcome.value] at ha
      dsimp only [mem']
      rw [Function.update_of_ne (by omega)]
      exact hZ a ha
    · intro a ha
      dsimp only [mem']
      rw [Function.update_of_ne (by omega)]
      exact hFrame a ha
    · intro a ha1 ha2
      dsimp only [mem']
      rw [Function.update_of_ne (by omega)]
      exact hGap a (by omega) ha2
    · exact hChoices.first
    · exact hChoices.last
    · exact hChoices.mono
    · intro i hi
      obtain ⟨hPtr,hSpec,hBlk,hAddrEq,hBumpLe⟩ := hChoices.rows i hi
      have hLower : h ≤ addr i := hChoices.first ▸ hChoices.mono 0 (Nat.zero_le _) i hi.le (Nat.zero_le _)
      refine ⟨by dsimp only [mem']; rw [Function.update_of_ne (by omega)]; exact hPtr,
        hSpec, ?_, hAddrEq, hBumpLe⟩
      refine hBlk.frame (fun a ha _ => Function.update_of_ne (by omega) _ _) (fun U he => ?_)
      rw [he] at hSpec
      exact hSpec.1
  · simp [buildScanChoiceContract,Expr.size]
    omega

end MinCostFlow.HierPaths
