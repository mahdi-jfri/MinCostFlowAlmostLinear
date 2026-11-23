module

public import MinCostFlow.HierPaths.QueryProgRead
public import MinCostFlow.HierPaths.QueryProgModel

/-!
# Filling the input step buffers

The two attachments and the route append three lists in order. Each call preserves the
earlier steps and the hierarchy block.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM Spanner

private theorem attach_frame {outE outY cap cnt k a : ℕ}
    (hc : cnt + k ≤ cap) (hd : outE + cap ≤ outY)
    (ha : a < outE + cnt ∨ (outE + cap ≤ a ∧ a < outY + cnt) ∨ outY + cap ≤ a) :
    CopyOutside outE outY cnt k a := by
  unfold CopyOutside
  omega

private theorem mem_block_of_below {X : HierConcrete} {b bound : ℕ} {mem mem' : ℕ → ℕ}
    (h : ListAt mem b X.encode) (hb : b + X.encode.length ≤ bound)
    (hf : ∀ a < bound, mem' a = mem a) : ListAt mem' b X.encode :=
  h.congr fun a _ ha => hf a (ha.trans_le hb)

private theorem section_of_below {b bound i : ℕ} {mem mem' : ℕ → ℕ}
    (hb : b + i < bound) (hf : ∀ a < bound, mem' a = mem a) :
    b + 25 + mem' (b + i) = b + 25 + mem (b + i) := by rw [hf _ hb]

private theorem scope_append {l₁ l₂ : List (ℕ × ℕ)} {mem : ℕ → ℕ} {base : ℕ}
    (h₁ : ListAt mem base (l₁.map Prod.fst))
    (h₂ : ListAt mem (base + l₁.length) (l₂.map Prod.fst)) :
    ListAt mem base ((l₁ ++ l₂).map Prod.fst) := by
  rw [List.map_append, listAt_append, List.length_map]
  exact ⟨h₁, h₂⟩

private theorem scope_append_snd {l₁ l₂ : List (ℕ × ℕ)} {mem : ℕ → ℕ} {base : ℕ}
    (h₁ : ListAt mem base (l₁.map Prod.snd))
    (h₂ : ListAt mem (base + l₁.length) (l₂.map Prod.snd)) :
    ListAt mem base ((l₁ ++ l₂).map Prod.snd) := by
  rw [List.map_append, listAt_append, List.length_map]
  exact ⟨h₁, h₂⟩

/-- The registers set before filling the step buffers. -/
structure QueryFillRegs (st : State) (X : HierConcrete) (b u v inE inY : ℕ) : Prop where
  block : st.regs 0 = b
  source : st.regs 1 = u
  target : st.regs 2 = v
  depth : st.regs 4 = X.depth
  inputE : st.regs 7 = inE
  inputY : st.regs 8 = inY

set_option maxHeartbeats 4000000 in
/-- The calls that fill the buffers implement the input walk and preserve the rest of memory. -/
theorem queryFill_triple {w a : ℕ} {p : Program} {f : ℕ} {X : HierConcrete} {b u v inE inY : ℕ}
    (hA : p.procs[f]? = some (attachProc (f + 1) (f + 2)))
    (hE : p.procs[f + 1]? = some entryWordProc)
    (hC : p.procs[f + 2]? = some copyProc)
    (hR : p.procs[f + 3]? = some (routeProc (f + 3) (f + 4) (f + 2)))
    (hP : p.procs[f + 4]? = some pickProc)
    (hrel : X.H.Rel a X.ms) (hG : X.ms.abs.G.IsValid)
    (hu : u ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat) (hv : v ∈ X.ms.abs.G.verts \ X.ms.abs.Vhat)
    (hblock : b + X.encode.length ≤ inE) (hbuf : inE + X.queryCapacity ≤ inY)
    (hw : inY + X.queryCapacity < 2 ^ w) {mem regs : ℕ → ℕ} :
    let ss := Walk.steps (X.queryInputWalk u v)
    Triple w p (fun st => st.mem = mem ∧ st.regs = regs ∧
        ListAt mem b X.encode ∧ QueryFillRegs st X b u v inE inY)
      (queryFill f) (normalPost fun st =>
        ListAt st.mem inE (ss.map Prod.fst) ∧ ListAt st.mem inY (ss.map Prod.snd) ∧
        st.regs 18 = ss.length ∧
        (∀ i < 11, st.regs i = regs i) ∧
        ∀ x, x < inE ∨ inY + X.queryCapacity ≤ x → st.mem x = mem x)
      (fun _ => 60 * attachmentLength (X.H.entryAt X.ms.st u) +
        60 * attachmentLength (X.H.entryAt X.ms.st v) +
        700 * X.H.A.C.routeOps (groupOf X.H.A.x X.H.A.b) X.tablePick X.depth 0
          (X.H.A.C.entryTerm (X.H.entryAt X.ms.st u)) (X.H.A.C.entryTerm (X.H.entryAt X.ms.st v)) +
        3000) := by
  dsimp only
  intro s ω ⟨hm, hRegsEq, hL, hRegs⟩
  let cap := X.queryCapacity
  let ss := Walk.steps (X.queryInputWalk u v)
  let C := X.H.A.C
  let ex := X.H.A.x
  let br := X.H.A.b
  let eU := X.H.entryAt X.ms.st u
  let eV := X.H.entryAt X.ms.st v
  let tU := C.entryTerm eU
  let tV := C.entryTerm eV
  let left := Walk.steps (attachmentCopy C false eU)
  let right := Walk.steps (attachmentCopy C true eV)
  let middle := routeSteps C ex br X.tablePick X.depth 0 tU tV
  have hAs := hrel.spec.arrays
  obtain ⟨huN, huA, _, htU, _⟩ := X.query_support hrel hG hu
  obtain ⟨hvN, hvA, _, htV, _⟩ := X.query_support hrel hG hv
  have hleft : left.length = attachmentLength eU := length_attachmentCopy_steps C hAs.fits huA false
  have hright : right.length = attachmentLength eV := length_attachmentCopy_steps C hAs.fits hvA true
  have hss : ss = left ++ middle ++ right := by
    rw [List.append_assoc]; exact X.queryInputWalk_steps hrel hG hu hv
  have hTotal : left.length + middle.length + right.length ≤ cap := by
    have := (X.queryInputWalk_stepBounds hrel hG hu hv).1
    simpa only [← show ss = Walk.steps (X.queryInputWalk u v) from rfl, hss, List.length_append] using this
  have hhw : b + X.encode.length < 2 ^ w := by omega
  have hBmin : 25 ≤ X.encode.length := by simp [HierConcrete.encode, layoutList, csrList, csrOffsets]
  have hww : 25 < 2 ^ w := by omega
  have htermW : 2 ^ ex < 2 ^ w := by
    have hEnd := (block_sec hL (i := 1) (by decide)).2
    change _ + (tabList C.numTerm C.owner).length ≤ _ at hEnd
    rw [length_tabList, hAs.numTerm_eq] at hEnd
    change 2 ^ X.H.A.x < 2 ^ w
    omega
  have hnumTermW : C.numTerm < 2 ^ w := hAs.numTerm_eq ▸ htermW
  have htUw : tU < 2 ^ w := Nat.lt_trans ((X.H.A.mem_surv).mp htU).1 hnumTermW
  have htVw : tV < 2 ^ w := Nat.lt_trans ((X.H.A.mem_surv).mp htV).1 hnumTermW
  have hNw : X.n < 2 ^ w := by
    have hEnd := (block_sec hL (i := 20) (by decide)).2
    change _ + (tabList X.n X.ms.st.supCur).length ≤ _ at hEnd
    rw [length_tabList] at hEnd
    omega
  have hr0 := hRegs.block
  have hr1 := hRegs.source
  have hr2 := hRegs.target
  have hr4 := hRegs.depth
  have hr7 := hRegs.inputE
  have hr8 := hRegs.inputY
  have hRead := entryWordProc_meetsContract hE hhw
  have hAttachL := attachProc_meetsContract (p := p) (w := w) (cap := cap)
    hA hE hC (X := X) (v := u) (cnt := 0) (fwd := false) hAs.fits hblock
    (by rw [← hleft]; omega) hbuf hw
  have hchoice := X.tablePick_isConnectorChoice hAs hrel.spec.pairs hrel.inv
  have hReady := C.routeReady_of_choice _ _ hchoice X.depth 0 tU tV htU htV
    (X.query_same_root hrel htU htV)
  have hPick := pickProc_meetsContract (p := p) hP hhw htermW hAs.b_pos
  obtain ⟨hT2, hE2⟩ := block_sec hL (i := 2) (by decide)
  obtain ⟨hT3, hE3⟩ := block_sec hL (i := 3) (by decide)
  obtain ⟨hT10, hE10⟩ := block_sec hL (i := 10) (by decide)
  obtain ⟨hT11, hE11⟩ := block_sec hL (i := 11) (by decide)
  let ea := b + 25 + mem (b + 2)
  let eb := b + 25 + mem (b + 3)
  let wv := b + 25 + mem (b + 10)
  let we := b + 25 + mem (b + 11)
  change ea + (tabList C.numConn C.endA).length ≤ _ at hE2
  change eb + (tabList C.numConn C.endB).length ≤ _ at hE3
  change wv + (csrList C.numConn fun c => (C.walk c).verts).length ≤ _ at hE10
  change we + (csrList C.numConn fun c => (C.walk c).edges).length ≤ _ at hE11
  simp only [length_tabList] at hE2 hE3
  have hdepth : X.depth < 2 ^ w := by
    have hEnd := (block_sec hL (i := 12) (by decide)).2
    change _ + (csrList X.depth X.pairIdxTable).length ≤ _ at hEnd
    rw [length_csrList_q] at hEnd
    omega
  have hRoute := routeProc_meetsContract (p := p) (w := w) (C := C) (Lmax := X.depth)
    (eaA := ea) (ebA := eb) (wvA := wv) (weA := we) (cap := cap)
    (x := ex) (b := br) (outE := inE) (outY := inY)
    hR hC hPick (fun m m' hf h => mem_block_of_below h hblock hf)
    (hE2.trans hblock) (hE3.trans hblock) (hE10.trans hblock) (hE11.trans hblock)
    le_rfl hAs.b_pos htermW hbuf hw (by omega)
    (fun c hc => IsWalk.wellFormed (hAs.fits.2 c hc).2.2)
    (fun c hc => ⟨Nat.lt_trans (hAs.fits.2 c hc).1 hnumTermW,
      Nat.lt_trans (hAs.fits.2 c hc).2.1 hnumTermW⟩)
  have hReadPre : ∀ {m t k}, ListAt m b X.encode → t < X.n → k < 3 →
      (entryWordContract X b).pre [b, t, k] m :=
    fun hm ht hk => ⟨_, _, rfl, ht, hk, hm⟩
  have hEntryLen : ∀ v, X.entryWord v 2 = attachmentLength (X.H.entryAt X.ms.st v) := by
    intro t
    cases he : X.H.entryAt X.ms.st t <;> simp [HierConcrete.entryWord, he, attachmentLength, entryWords]
  have hMem : RouteMem C ea eb wv we (fun m => ListAt m b X.encode) mem :=
    ⟨hT2, hT3, hT10, hT11, hL⟩
  suffices hrun : ∃ o s' c, Runs w p ω (queryFill f) s o s' c ∧
      normalPost (fun s' =>
        ListAt s'.mem inE (ss.map Prod.fst) ∧ ListAt s'.mem inY (ss.map Prod.snd) ∧
        s'.regs 18 = ss.length ∧ (∀ i < 11, s'.regs i = s.regs i) ∧
        ∀ x, x < inE ∨ inY + cap ≤ x → s'.mem x = mem x) o s' ∧
      0 + c ≤ 60 * left.length + 60 * right.length +
        700 * C.routeOps (groupOf ex br) X.tablePick X.depth 0 tU tV + 3000 by
    obtain ⟨o, s', c, hr, hpost, hc⟩ := hrun
    cases o with
    | returned _ => exact False.elim hpost
    | normal =>
      obtain ⟨he, hy, hl, hregs, hf⟩ := hpost
      refine ⟨.normal, s', c, hr, ⟨he, hy, hl, ?_, hf⟩, by simpa [hleft, hright] using hc⟩
      intro i hi
      exact (hregs i hi).trans (congrFun hRegsEq i)
  unfold queryFill
  wram_step
  · exact hReadPre (hm ▸ hL) huN (by decide)
  intro kU m₀ pos₀ hread
  obtain ⟨hm₀, hread⟩ := hread
  have hkU : kU = left.length := (hread u 2 rfl).trans ((hEntryLen u).trans hleft.symm)
  subst kU
  have hL₀ : ListAt m₀ b X.encode := (hm₀.trans hm).symm ▸ hL
  wram_step
  · exact ⟨rfl, huN, huA, hL₀⟩
  intro t m₁ pos₁ hpost
  obtain ⟨ht, hEL, hYL, hf₁⟩ := hpost
  change t = tU at ht
  subst t
  rw [← hleft] at hf₁
  have hfLow₁ : ∀ x < inE, m₁ x = mem x := by
    intro x hx
    exact (hf₁ x (attach_frame (by omega) hbuf (Or.inl (by omega)))).trans (congrFun (hm₀.trans hm) x)
  have hL₁ := mem_block_of_below hL hblock hfLow₁
  wram_step
  · exact hReadPre hL₁ hvN (by decide)
  intro tag m₂ pos₂ hpost
  obtain ⟨hm₂, hTag⟩ := hpost
  subst m₂
  have ht := hTag v 0 rfl
  subst tag
  wram_step
  · exact hReadPre hL₁ hvN (by decide)
  intro ident m₃ pos₃ hpost
  obtain ⟨hm₃, hId⟩ := hpost
  subst m₃
  have hid := hId v 1 rfl
  subst ident
  refine runs_seq_triple_le
    (queryRightTerm_triple (p := p) hL₁ hhw (by simpa using hr0) (by simp) (by simp) hvA)
    ⟨rfl, rfl⟩ ?_
  intro sr ⟨hmemr, hVr, hregs⟩
  have ht0 : sr.regs 0 = b := (hregs 0 (by decide)).trans (by simpa using hr0)
  have ht4 : sr.regs 4 = X.depth := (hregs 4 (by decide)).trans (by simpa using hr4)
  have ht12 : sr.regs 12 = tU := by simp [hregs 12 (by decide)]
  have ht11 : sr.regs 11 = left.length := by simp [hregs 11 (by decide)]
  have ht7 : sr.regs 7 = inE := (hregs 7 (by decide)).trans (by simpa using hr7)
  have ht8 : sr.regs 8 = inY := (hregs 8 (by decide)).trans (by simpa using hr8)
  have ht1 : sr.regs 1 = u := (hregs 1 (by decide)).trans (by simpa using hr1)
  have ht2 : sr.regs 2 = v := (hregs 2 (by decide)).trans (by simpa using hr2)
  have hLowr : ∀ x < inE, sr.mem x = mem x := fun x hx =>
    (congrFun hmemr x).trans (hfLow₁ x hx)
  have hLr := mem_block_of_below hL hblock hLowr
  have hSec : ∀ {i}, i < 24 →
      (secExpr i).eval w sr = some (b + 25 + mem (b + i)) := by
    intro i hi
    rw [eval_querySection hLr ht0 hi hhw, section_of_below (by omega) hLowr]
  have hX := eval_queryHeader hLr ht0 (i := 5) (by simp [HierConcrete.header]) hhw
  have hB := eval_queryHeader hLr ht0 (i := 6) (by simp [HierConcrete.header]) hhw
  have hnC := eval_queryHeader hLr ht0 (i := 3) (by simp [HierConcrete.header]) hhw
  have hBranch := eval_queryBranchExpr hX hB (x := ex) (b := br) (ex.lt_two_pow_self.trans htermW)
  have hArgs : evalArgs w sr [.reg 4, .const 0, .reg 12, .reg 14, .reg 11,
      queryBranchExpr (queryHeaderExpr 5) (queryHeaderExpr 6), secExpr 2, secExpr 3, secExpr 10,
      secExpr 11, queryHeaderExpr 3, .reg 7, .reg 8, .reg 0, queryHeaderExpr 5] =
      some ([X.depth, 0, tU, tV, left.length] ++ routeFixed (min ex br) ea eb wv we C.numConn
        inE inY b ex) := by
    exact evalArgs_cons (Expr.eval_reg_of_eq ht4) <|
      evalArgs_cons (Expr.eval_const (by omega)) <| evalArgs_cons (Expr.eval_reg_of_eq ht12) <|
      evalArgs_cons (Expr.eval_reg_of_eq hVr) <| evalArgs_cons (Expr.eval_reg_of_eq ht11) <|
      evalArgs_cons hBranch <| evalArgs_cons (hSec (by decide : 2 < 24)) <|
      evalArgs_cons (hSec (by decide : 3 < 24)) <| evalArgs_cons (hSec (by decide : 10 < 24)) <|
      evalArgs_cons (hSec (by decide : 11 < 24)) <| evalArgs_cons hnC <|
      evalArgs_cons (Expr.eval_reg_of_eq ht7) <| evalArgs_cons (Expr.eval_reg_of_eq ht8) <|
      evalArgs_cons (Expr.eval_reg_of_eq ht0) <| evalArgs_cons hX (evalArgs_nil _ _)
  have hMw := hMem.congr (fun m m' hf h => mem_block_of_below h hblock hf)
    (hE2.trans hblock) (hE3.trans hblock) (hE10.trans hblock) (hE11.trans hblock) hLowr
  have hXw : ex < 2 ^ w := ex.lt_two_pow_self.trans htermW
  have hBrw : min ex br < 2 ^ w := lt_of_le_of_lt (Nat.min_le_left _ _) hXw
  have hRoutePre : (routeContract C ex br X.tablePick X.depth ea eb wv we inE inY cap b
      (fun m => ListAt m b X.encode) 400).pre _ sr.mem :=
    ⟨X.depth, 0, tU, tV, left.length, rfl, by omega,
      show left.length + middle.length ≤ cap from by omega, hMw, hReady⟩
  refine runs_seq_call_le hRoute hArgs ?_ hRoutePre ?_
  · simp only [routeFixed, List.cons_append, List.nil_append]
    wram_words
  intro nm m₄ pos₄ hpost
  obtain ⟨hnm, hEM, hYM, hf₄⟩ := hpost X.depth 0 tU tV left.length rfl
  change nm = left.length + middle.length at hnm
  subst nm
  have hLow₄ : ∀ x < inE, m₄ x = mem x := fun x hx =>
    (hf₄ x (Or.inl (by omega))).trans (hLowr x hx)
  have hL₄ := mem_block_of_below hL hblock hLow₄
  wram_step
  · exact hReadPre hL₄ hvN (by decide)
  intro kV m₅ pos₅ hpost
  obtain ⟨hm₅, hpos⟩ := hpost
  subst m₅
  have hkV : kV = right.length := (hpos v 2 rfl).trans ((hEntryLen v).trans hright.symm)
  subst kV
  have hAttachR := attachProc_meetsContract (p := p) (w := w) (cap := cap)
    hA hE hC (X := X) (v := v) (cnt := left.length + middle.length) (fwd := true)
    hAs.fits hblock (by rw [← hright]; omega) hbuf hw
  wram_step
  · exact ⟨rfl, hvN, hvA, hL₄⟩
  intro rr m₆ pos₆ hpost
  obtain ⟨_, hER, hYR, hf₆⟩ := hpost
  rw [← hright] at hf₆
  have hFrame : ∀ x, x < inE ∨ inY + cap ≤ x → m₆ x = mem x := by
    intro x hx
    have hf : m₆ x = m₄ x := hf₆ x (attach_frame hTotal hbuf (by omega))
    rcases hx with hx | hx
    · exact hf.trans (hLow₄ x hx)
    have h4 := hf₄ x (Or.inr (Or.inr hx))
    have h1 := hf₁ x (attach_frame (by omega) hbuf (Or.inr (Or.inr hx)))
    exact hf.trans (h4.trans ((congrFun hmemr x).trans (h1.trans (congrFun (hm₀.trans hm) x))))
  have hEL' : ListAt m₄ inE (left.map Prod.fst) := hEL.congr fun x _ hx =>
    (hf₄ x (Or.inl (by simpa using hx))).trans (congrFun hmemr x)
  have hYL' : ListAt m₄ inY (left.map Prod.snd) := hYL.congr fun x hx hx' =>
    (hf₄ x (Or.inr (Or.inl ⟨hbuf.trans hx, by simpa using hx'⟩))).trans (congrFun hmemr x)
  have hELM := scope_append hEL' hEM
  have hYLM := scope_append_snd hYL' hYM
  have hELM' := hELM.congr (mem' := m₆) fun x _ hx =>
    hf₆ x (attach_frame hTotal hbuf (Or.inl (by simpa using hx)))
  have hYLM' := hYLM.congr (mem' := m₆) fun x hx hx' =>
    hf₆ x (attach_frame hTotal hbuf (Or.inr (Or.inl ⟨hbuf.trans hx, by simpa using hx'⟩)))
  have hFinalE := scope_append hELM' (by simpa using hER)
  have hFinalY := scope_append_snd hYLM' (by simpa using hYR)
  have hstepsW : left.length + middle.length + right.length < 2 ^ w := by omega
  refine runs_assign_le
    (Expr.eval_add (x := left.length + middle.length) (y := right.length)
      (by eval_expr) (by eval_expr) hstepsW) ?_ ?_
  · refine ⟨hss ▸ hFinalE, hss ▸ hFinalY, ?_, ?_, hFrame⟩
    · simp [hss, Nat.add_assoc]
    · intro i hi
      have hne n (hn : 11 ≤ n) : i ≠ n := by omega
      have hg := hregs i (hne 14 (by decide))
      simp only [Function.update_of_ne (hne 15 (by decide)), Function.update_of_ne (hne 16 (by decide)),
        Function.update_of_ne (hne 17 (by decide)), Function.update_of_ne (hne 18 (by decide))]
      rw [hg]
      simp only [Function.update_of_ne (hne 11 (by decide)), Function.update_of_ne (hne 12 (by decide)),
        Function.update_of_ne (hne 13 (by decide)), Function.update_of_ne (hne 14 (by decide))]
  · change left.length = attachmentLength (X.H.entryAt X.ms.st u) at hleft
    change right.length = attachmentLength (X.H.entryAt X.ms.st v) at hright
    simp only [attachContract, entryWordContract, routeContract, routeCost, routeFixed, List.cons_append,
      List.nil_append, hleft, hright, queryBranchExpr, queryHeaderExpr, secExpr]
    wram_cost

end MinCostFlow.HierPaths
