module

public import MinCostFlow.LastLevelProgram.GuestWorkspace
public import MinCostFlow.LastLevelProgram.CanonicalTreeCall
public import MinCostFlow.LastLevelProgram.PackPrecision
public import WordRAM.LinkDefs
import WordRAM.Link
import MinCostFlow.Scaling.DeterministicExecution
import MinCostFlow.Scaling.CanonicalCallContract
import Mathlib.Tactic

/-!
# Relocation of the last-level LSST call

The host executes the canonical Theorem 2.2 call (page 7) with the
canonical word width and addresses. This preserves the tree returned
by the standalone program even when the host layout is different.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord

/-- Procedures for the canonical LSST guest, installed starting at
index `b + 1` in the host program. -/
@[expose] def relocatedTreeModule (Q : Program) (b : ℕ) : List Stmt :=
  let guest : Program := ⟨lsstModule Q 0 1⟩
  guest.procs.map (relocStmt guest.regBound b)

/-- The installed module resolves each relocated guest procedure call. -/
theorem relocatedTreeModule_lookup {Q p : Program} {b f : ℕ} {body : Stmt}
    (hp : p.HasAt (b + 1) (relocatedTreeModule Q b))
    (hf : (lsstModule Q 0 1)[f]? = some body) :
    p.procs[b + 1 + f]? =
      some (relocStmt (Program.mk (lsstModule Q 0 1)).regBound b body) := by
  have hlen : f < (lsstModule Q 0 1).length := by
    by_contra hn
    rw [List.getElem?_eq_none (Nat.le_of_not_gt hn)] at hf
    contradiction
  have hi : f < (relocatedTreeModule Q b).length := by
    simpa [relocatedTreeModule] using hlen
  have hat := hp f hi
  have hb : (lsstModule Q 0 1)[f]'hlen = body := by
    simpa only [List.getElem?_eq_getElem hlen, Option.some.injEq] using hf
  simpa [relocatedTreeModule, hb] using hat

/-- The relocated procedures are deterministic. -/
theorem relocatedTreeModule_noRand (Q : Program) (b : ℕ) :
    ∀ body ∈ relocatedTreeModule Q b, body.NoRand := by
  intro body hb
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
  exact Scaling.Machine.relocStmt_noRand _ _ s (lsstModule_noRand Q 0 1 s hs)

/-- Arguments for the copying and relocated LSST body. The first
`R` registers mirror the guest. The remaining input registers hold the
relocation base, guest modulus, source pointer, and copy length. -/
@[expose] def relocatedTreeArgs (R : ℕ) (guest : List ℕ)
    (base modulus src len : ℕ) : List ℕ :=
  (List.ofFn fun r : Fin R => guest.getD r 0) ++ [base, modulus, src, len]

/-- Form the padded guest arguments followed by the relocation words.
The modulus is computed from the selected guest word width at run time. -/
@[expose] def relocatedTreeArgsExpr (R : ℕ) (guest : List Expr)
    (base width src len : Expr) : List Expr :=
  (List.ofFn fun r : Fin R => guest.getD r (.const 0)) ++
    [base, .bin .shiftLeft (.const 1) width, src, len]

/-- Indexing an evaluated argument list preserves the default zero value. -/
theorem evalArgs_getD {w : ℕ} {st : State}
    {es : List Expr} {vs : List ℕ} (h : evalArgs w st es = some vs) (i : ℕ) :
    (es.getD i (.const 0)).eval w st = some (vs.getD i 0) := by
  induction es generalizing vs i with
  | nil =>
    simp only [evalArgs, Option.some.injEq] at h
    subst vs
    simp [Expr.eval]
  | cons e es ih =>
    cases he : e.eval w st <;> cases hv : evalArgs w st es <;>
      simp [evalArgs, he, hv] at h
    subst vs
    cases i with
    | zero => simpa using he
    | succ i => simpa using ih hv i

private theorem evalArgs_ofFn {w n : ℕ} {st : State} {es : Fin n → Expr}
    {vs : Fin n → ℕ} (h : ∀ i, (es i).eval w st = some (vs i)) :
    evalArgs w st (List.ofFn es) = some (List.ofFn vs) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact evalArgs_cons (h 0) (ih (fun i => h i.succ))

/-- Evaluating the relocation expressions gives the calling convention of
the translated Theorem 2.2 procedure (page 7). -/
theorem relocatedTreeArgsExpr_eval {w : ℕ} {st : State} {es : List Expr}
    {vs : List ℕ} {eb ew ea el : Expr} {base width src len : ℕ} (R : ℕ)
    (he : evalArgs w st es = some vs)
    (hb : eb.eval w st = some base) (hw : ew.eval w st = some width)
    (ha : ea.eval w st = some src) (hl : el.eval w st = some len)
    (hmod : 2^width < 2^w) :
    evalArgs w st (relocatedTreeArgsExpr R es eb ew ea el) =
      some (relocatedTreeArgs R vs base (2^width) src len) := by
  unfold relocatedTreeArgsExpr relocatedTreeArgs
  apply Link.evalArgs_append (evalArgs_ofFn (fun i => evalArgs_getD he i))
  have hone : 1 < 2^w := (Nat.one_le_pow _ _ (by decide)).trans_lt hmod
  have hshift : (1 : ℕ) <<< width = 2^width := by simp [Nat.shiftLeft_eq]
  simp [evalArgs, Expr.eval, BinOp.eval, hb, hw, ha, hl, hone, hshift, hmod]

/-- Starting the body with `relocatedTreeArgs` initializes all registers
used by the copy and by the relocation. The copy index is `R + 4`. -/
theorem relocatedTreeArgs_regs (R : ℕ) (guest : List ℕ)
    (base modulus src len pos : ℕ) (mem : ℕ → ℕ) :
    let st := startState (relocatedTreeArgs R guest base modulus src len) mem pos
    st.regs R = base ∧ st.regs (R + 1) = modulus ∧
      st.regs (R + 2) = src ∧ st.regs (R + 3) = len ∧
      ∀ r < R, st.regs r = (startState guest mem 0).regs r := by
  dsimp only [startState, relocatedTreeArgs]
  have hleft (r : ℕ) (hr : r < R) :
      ((List.ofFn fun i : Fin R => guest.getD i 0) ++ [base, modulus, src, len]).getD r 0 =
        guest.getD r 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hr)]
    simp [List.getD_eq_getElem?_getD, hr]
  have hright (k : ℕ) :
      ((List.ofFn fun i : Fin R => guest.getD i 0) ++ [base, modulus, src, len]).getD
        (R + k) 0 = [base, modulus, src, len].getD k 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp [List.getD_eq_getElem?_getD]
  exact ⟨hright 0, hright 1, hright 2, hright 3, hleft⟩

/-- The padded argument list fits in the host word when the guest
region fits, the source ends before it, and each guest register fits. -/
theorem relocatedTreeArgs_words {R guestWidth hostWidth base src len : ℕ}
    {guest : List ℕ}
    (hguest : ∀ r, guest.getD r 0 < 2 ^ guestWidth)
    (hbase : 0 < base) (hspace : base + 2 ^ guestWidth ≤ 2 ^ hostWidth)
    (hsource : src + len ≤ base) :
    ∀ a ∈ relocatedTreeArgs R guest base (2 ^ guestWidth) src len, a < 2 ^ hostWidth := by
  intro a ha
  have hpos : 0 < 2 ^ guestWidth := Nat.two_pow_pos _
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨r, rfl⟩ := List.mem_ofFn.mp ha
    exact (hguest r).trans_le (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega

/-- Entry body for the relocated LSST procedures. The copy uses the
source and length registers following the relocation arguments. -/
@[expose] def relocatedTreeEntry (Q : Program) (b : ℕ) : Stmt :=
  let R := (Program.mk (lsstModule Q 0 1)).regBound
  .seq (copyWordsStmt (R + 2) R (R + 3) (R + 4)) (relocStmt R b (lsstEntryProc 0 1))

/-- The copying entry and relocated LSST use no random instructions. -/
theorem relocatedTreeEntry_noRand (Q : Program) (b : ℕ) :
    (relocatedTreeEntry Q b).NoRand := by
  let guest : Program := ⟨lsstModule Q 0 1⟩
  have hat : guest.HasAt 0 (lsstModule Q 0 1) := by
    intro i hi
    simp [guest]
  have hm : lsstEntryProc 0 1 ∈ lsstModule Q 0 1 :=
    List.mem_of_getElem? (lsst_hasAt_entry hat)
  constructor
  · simp [copyWordsStmt, Stmt.NoRand]
  · exact Scaling.Machine.relocStmt_noRand _ _ _ (lsstModule_noRand Q 0 1 _ hm)

/-- Complete procedure block for calling the relocated tree routine. -/
@[expose] def relocatedTreeProcedures (Q : Program) (b : ℕ) : List Stmt :=
  relocatedTreeEntry Q b :: relocatedTreeModule Q b

/-- Installing the block supplies the entry and its internal dispatch table. -/
theorem relocatedTreeProcedures_hasAt {Q p : Program} {b : ℕ}
    (hp : p.HasAt b (relocatedTreeProcedures Q b)) :
    p.procs[b]? = some (relocatedTreeEntry Q b) ∧
      p.HasAt (b + 1) (relocatedTreeModule Q b) := by
  constructor
  · simpa [relocatedTreeProcedures] using hp 0 (by simp [relocatedTreeProcedures])
  · intro i hi
    have hat := hp (i + 1) (by simpa [relocatedTreeProcedures] using hi)
    rw [show b + (i + 1) = b + 1 + i by omega] at hat
    simpa [relocatedTreeProcedures] using hat

/-- Every procedure in the block is deterministic. -/
theorem relocatedTreeProcedures_noRand (Q : Program) (b : ℕ) :
    ∀ s ∈ relocatedTreeProcedures Q b, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact relocatedTreeEntry_noRand Q b
  · exact relocatedTreeModule_noRand Q b s hs

/-- Copy the packed input prefix into a fresh guest region. The zero
suffix of the host supplies the rest of the canonical input memory. -/
theorem copyCanonicalQuery_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {srcReg dstReg lenReg idxReg src dst : ℕ} (st : State)
    (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ)
    (hd : [srcReg, dstReg, lenReg, idxReg].Nodup)
    (hsrc : st.regs srcReg = src) (hdst : st.regs dstReg = dst)
    (hlen : st.regs lenReg = queryOriginals G L)
    (hpacked : ∀ i < queryOriginals G L, st.mem (src + i) = queryMemory G L len wt i)
    (hdisj : src + queryOriginals G L ≤ dst)
    (hroom : dst + queryOriginals G L < 2 ^ w)
    (hzero : ZeroFrom st.mem dst) (hw : 4 ≤ 2 ^ w) :
    ∃ out cost,
      Runs w p ω (copyWordsStmt srcReg dstReg lenReg idxReg) st .normal out cost ∧
      (∀ i, out.mem (dst + i) = queryMemory G L len wt i) ∧
      (∀ a < dst, out.mem a = st.mem a) ∧
      out.pos = st.pos ∧
      (∀ r, r ≠ idxReg → out.regs r = st.regs r) ∧
      cost ≤ 17 * (queryOriginals G L + 1) := by
  let words := List.ofFn fun i : Fin (queryOriginals G L) => queryMemory G L len wt i
  have hn : words.length = queryOriginals G L := List.length_ofFn
  have hat : ListAt st.mem src words := by
    intro i hi
    simpa only [words, List.getElem_ofFn] using hpacked i (hn ▸ hi)
  obtain ⟨out, cost, hr, hcopy, hframe, hpos, hregs, hc⟩ :=
    Link.copyWords_runs (p := p) (ω := ω) hd hsrc hdst (hlen.trans hn.symm) hat
      (hn.symm ▸ hdisj) (hn.symm ▸ hroom) hw
  refine ⟨out, cost, hr, ?_, fun a ha => hframe a (Or.inl ha), hpos, hregs, hn ▸ hc⟩
  intro i
  by_cases hi : i < queryOriginals G L
  · simpa only [words, List.getElem_ofFn] using hcopy i (hn.symm ▸ hi)
  · rw [hframe _ (Or.inr (by omega)), hzero _ (Nat.le_add_right _ _),
      queryMemory_zero_suffix G L len wt i (Nat.le_of_not_gt hi)]

/-- A relocated canonical LSST run has the same guest output memory and
preserves every address outside the guest region. -/
theorem relocatedTreeCall_runs {Q host : Program} {b heap guestWidth hostWidth : ℕ}
    {args : List ℕ} {mem : ℕ → ℕ} {st guestOut : State} {cost : ℕ}
    {ω : ℕ → Bool}
    (hmodule : ∀ f body, (lsstModule Q 0 1)[f]? = some body →
      host.procs[b + 1 + f]? =
        some (relocStmt (Program.mk (lsstModule Q 0 1)).regBound b body))
    (hw : guestWidth ≤ hostWidth)
    (hspace : heap + 1 + 2 ^ guestWidth ≤ 2 ^ hostWidth)
    (hfour : 4 ≤ 2 ^ hostWidth)
    (hbase : st.regs (Program.mk (lsstModule Q 0 1)).regBound = heap + 1)
    (hlimit : st.regs ((Program.mk (lsstModule Q 0 1)).regBound + 1) = 2 ^ guestWidth)
    (hregs : ∀ r < (Program.mk (lsstModule Q 0 1)).regBound,
      st.regs r = (startState args mem 0).regs r)
    (hargs : ∀ r, (startState args mem 0).regs r < 2 ^ guestWidth)
    (hvalues : ∀ a, mem a < 2 ^ guestWidth)
    (hmem : ∀ a < 2 ^ guestWidth, st.mem (heap + 1 + a) = mem a)
    (hr : Runs guestWidth ⟨lsstModule Q 0 1⟩ (fun _ => false) (lsstEntryProc 0 1)
      (startState args mem 0) (.returned 0) guestOut cost) :
    ∃ out hostCost,
      Runs hostWidth host ω
        (relocStmt (Program.mk (lsstModule Q 0 1)).regBound b (lsstEntryProc 0 1))
        st (.returned 0) out hostCost ∧
      hostCost ≤ ((Program.mk (lsstModule Q 0 1)).regBound + 6) * cost ∧
      (∀ a < 2 ^ guestWidth, out.mem (heap + 1 + a) = guestOut.mem a) ∧
      (∀ a, a < heap + 1 ∨ heap + 1 + 2 ^ guestWidth ≤ a → out.mem a = st.mem a) := by
  let guest : Program := ⟨lsstModule Q 0 1⟩
  have hat : guest.HasAt 0 (lsstModule Q 0 1) := by
    intro i hi
    simp [guest]
  have hentry := lsst_hasAt_entry hat
  have hmember := List.mem_of_getElem? hentry
  have hdet : guest.IsDeterministic := lsstModule_noRand Q 0 1
  obtain ⟨fuel, hfuel⟩ := Scaling.Machine.runs_of_deterministic hdet
    (ω' := subBits hostWidth guestWidth st.pos ω) (hdet _ hmember) hr
  obtain ⟨out, hostCost, _, hrun, hcost, _, _, _, _, _, _, hread, hframe, _, _⟩ :=
    Link.runs_relocStmt hmodule hw hspace hfour fuel (lsstEntryProc 0 1)
      (startState args mem 0) st 0 (.returned 0) guestOut cost
      (Link.regBound_le_of_mem hmember) hbase hlimit hregs hargs hvalues hmem
      (by simp [startState]) (by simp) hfuel
  exact ⟨out, hostCost, hrun, hcost, hread, hframe⟩

/-- Copy a canonical query into fresh memory and execute it there. The
copy loop uses an index register above both relocation registers, so
the relocated call starts with the canonical arguments still in place. -/
theorem copyRelocatedTreeCall_runs {Q host : Program} {b heap guestWidth hostWidth : ℕ}
    {args : List ℕ} {st guestOut : State} {guestCost : ℕ} {ω : ℕ → Bool}
    {srcReg dstReg lenReg idxReg src : ℕ}
    (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ)
    (hG : (indexedGraph G).Valid) (hn : G.n ≤ 2 ^ guestWidth) (hbit : 2 ≤ 2 ^ guestWidth)
    (hmodule : ∀ f body, (lsstModule Q 0 1)[f]? = some body →
      host.procs[b + 1 + f]? =
        some (relocStmt (Program.mk (lsstModule Q 0 1)).regBound b body))
    (hw : guestWidth ≤ hostWidth) (hspace : heap + 1 + 2 ^ guestWidth ≤ 2 ^ hostWidth)
    (hfour : 4 ≤ 2 ^ hostWidth)
    (hd : [srcReg, dstReg, lenReg, idxReg].Nodup)
    (hidx : (Program.mk (lsstModule Q 0 1)).regBound + 1 < idxReg)
    (hsrc : st.regs srcReg = src) (hdst : st.regs dstReg = heap + 1)
    (hlen : st.regs lenReg = queryOriginals G L)
    (hpacked : ∀ i < queryOriginals G L, st.mem (src + i) = queryMemory G L len wt i)
    (hdisj : src + queryOriginals G L ≤ heap + 1)
    (hprefix : queryOriginals G L < 2 ^ guestWidth)
    (hzero : ZeroFrom st.mem (heap + 1))
    (hbase : st.regs (Program.mk (lsstModule Q 0 1)).regBound = heap + 1)
    (hlimit : st.regs ((Program.mk (lsstModule Q 0 1)).regBound + 1) = 2 ^ guestWidth)
    (hregs : ∀ r < (Program.mk (lsstModule Q 0 1)).regBound,
      st.regs r = (startState args (queryMemory G L len wt) 0).regs r)
    (hargs : ∀ r, (startState args (queryMemory G L len wt) 0).regs r < 2 ^ guestWidth)
    (hr : Runs guestWidth ⟨lsstModule Q 0 1⟩ (fun _ => false) (lsstEntryProc 0 1)
      (startState args (queryMemory G L len wt) 0) (.returned 0) guestOut guestCost) :
    ∃ out cost,
      Runs hostWidth host ω
        (.seq (copyWordsStmt srcReg dstReg lenReg idxReg)
          (relocStmt (Program.mk (lsstModule Q 0 1)).regBound b (lsstEntryProc 0 1)))
        st (.returned 0) out cost ∧
      cost ≤ 17 * (queryOriginals G L + 1) +
        ((Program.mk (lsstModule Q 0 1)).regBound + 6) * guestCost + 1 ∧
      (∀ a < 2 ^ guestWidth, out.mem (heap + 1 + a) = guestOut.mem a) ∧
      (∀ a < heap + 1, out.mem a = st.mem a) ∧
      ZeroFrom out.mem (heap + 1 + 2 ^ guestWidth) := by
  obtain ⟨prepared, copyCost, hcopy, hmem, hlow, _, hsaved, hcopyCost⟩ :=
    copyCanonicalQuery_runs (p := host) (ω := ω) st G L len wt hd hsrc hdst hlen
      hpacked hdisj (by omega) hzero hfour
  obtain ⟨out, runCost, hrun, hrunCost, hread, hframe⟩ :=
    relocatedTreeCall_runs hmodule hw hspace hfour
      ((hsaved _ (by omega)).trans hbase) ((hsaved _ (by omega)).trans hlimit)
      (fun r hr => (hsaved r (by omega)).trans (hregs r hr)) hargs
      (queryMemory_fits hG L len wt hn hbit) (fun a _ => hmem a) hr
  refine ⟨out, copyCost + runCost + 1, runs_seq_iff.mpr
    (Or.inr ⟨prepared, copyCost, runCost, hcopy, hrun, rfl⟩), by omega, hread, ?_, ?_⟩
  · exact fun a ha => (hframe a (Or.inl ha)).trans (hlow a ha)
  · intro a ha
    have hbound : heap + 1 ≤ a := by omega
    rw [hframe a (Or.inr ha)]
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hbound
    rw [hmem, queryMemory_zero_suffix G L len wt i (by omega)]

/-- The prepared call returns the same compact tree as the canonical
oracle run. Restoring its names therefore gives the oracle's named tree. -/
theorem copyCanonicalTree_atWidth_runs {Q host : Program} {b heap hostWidth c₀ : ℕ} {K : ℝ}
    {guestOut : State} {guestCost pos src : ℕ} {ω : ℕ → Bool}
    (mem : ℕ → ℕ)
    (G : MGraph) (L W : ℕ) (len wt : ℕ → ℤ) (hc : 1 ≤ c₀) (hL : 1 ≤ L)
    (hG : (indexedGraph G).Valid) :
    let R := (Program.mk (lsstModule Q 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let minimum := max 5 (Nat.log 2 (queryHeap G L + lsstSpace Q K G.n G.m sim 1) + 1)
    let args := [G.n, G.m, 0, G.m, queryLengths G, queryWeights G L, L, sim,
      queryOriginals G L, queryBridges G L, queryHeader G L, queryHeap G L]
    let readTree := fun (mem : ℕ → ℕ) (base : ℕ) =>
      treeFromOutput G mem (base + queryOriginals G L)
        (base + queryBridges G L) (base + queryHeader G L)
    let st := startState
      (relocatedTreeArgs R args (heap + 1) (2 ^ W) src (queryOriginals G L)) mem pos
    host.HasAt (b + 1) (relocatedTreeModule Q b) →
    minimum ≤ W → W ≤ hostWidth → heap + 1 + 2 ^ W ≤ 2 ^ hostWidth → 4 ≤ 2 ^ hostWidth →
    (∀ i < queryOriginals G L, mem (src + i) = queryMemory G L len wt i) →
    src + queryOriginals G L ≤ heap + 1 → ZeroFrom mem (heap + 1) →
    Runs W ⟨lsstModule Q 0 1⟩ (fun _ => false) (lsstEntryProc 0 1)
      (startState args (queryMemory G L len wt) 0) (.returned 0) guestOut guestCost →
    (∀ base moved, (∀ a < 2 ^ W, moved (base + a) = guestOut.mem a) →
      readTree moved base = readTree guestOut.mem 0) →
    guestOut.mem (queryHeader G L) ≤ G.n →
    guestOut.mem (queryHeader G L + 1) ≤ G.n →
    ∃ out cost,
      Runs hostWidth host ω (relocatedTreeEntry Q b)
        st (.returned 0) out cost ∧
      cost ≤ 17 * (queryOriginals G L + 1) + (R + 6) * guestCost + 1 ∧
      readTree out.mem (heap + 1) = readTree guestOut.mem 0 ∧
      out.mem (heap + 1 + queryHeader G L) ≤ G.n ∧
      out.mem (heap + 1 + queryHeader G L + 1) ≤ G.n ∧
      (∀ a < heap + 1, out.mem a = st.mem a) ∧
      ZeroFrom out.mem (heap + 1 + 2 ^ W) := by
  intro R sim minimum args readTree st hp hmin hw hspace hfour hpacked hdisj hzero hr hdecode hcount hbridges
  obtain ⟨hbase, hlimit, hsrc, hlen, hregs⟩ :=
    relocatedTreeArgs_regs R args (heap + 1) (2 ^ W) src (queryOriginals G L) pos mem
  have hd : [R + 2, R, R + 3, R + 4].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
      List.nodup_nil]
    exact ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, id, True.intro⟩
  have hidx : R + 1 < R + 4 := by omega
  obtain ⟨hn, hbit, hprefix, hargs⟩ :=
    canonicalTreeCall_wordBounds Q c₀ K hc G L hL (queryMemory G L len wt)
  have hpow : 2^minimum ≤ (2:ℕ)^W := Nat.pow_le_pow_right (by decide) hmin
  obtain ⟨out, cost, hrun, hcost, hread, hlow, hfresh⟩ :=
    copyRelocatedTreeCall_runs G L len wt hG (hn.le.trans hpow) (hbit.trans hpow)
      (fun _ _ hf => relocatedTreeModule_lookup hp hf) hw hspace hfour
      hd hidx hsrc hbase hlen hpacked hdisj (hprefix.trans_le hpow) hzero hbase hlimit hregs
      (fun r => (hargs r).trans_le hpow) hr
  have hheader : queryHeader G L + 1 < 2 ^ W := by
    have hs := (lsst_param_selection Q c₀ K hc (indexedGraph G) L (queryHeap G L) hL).2.2.2.2.2
    change queryHeap G L + lsstSpace Q K G.n G.m sim 1 < 2 ^ minimum at hs
    have hs := hs.trans_le hpow
    unfold queryHeap at hs
    omega
  refine ⟨out, cost, hrun, hcost, hdecode _ _ hread, ?_, ?_, hlow, hfresh⟩
  · rw [hread _ ((Nat.lt_succ_self (queryHeader G L)).trans hheader)]
    exact hcount
  · rw [Nat.add_assoc (heap + 1), hread _ hheader]
    exact hbridges

/-- Copy the input and run the guest at its original canonical width. -/
theorem copyCanonicalTree_runs {Q host : Program} {b heap hostWidth c₀ : ℕ} {K : ℝ}
    {guestOut : State} {guestCost pos src : ℕ} {ω : ℕ → Bool}
    (mem : ℕ → ℕ)
    (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ) (hc : 1 ≤ c₀) (hL : 1 ≤ L)
    (hG : (indexedGraph G).Valid) :
    let R := (Program.mk (lsstModule Q 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let w := max 5 (Nat.log 2 (queryHeap G L + lsstSpace Q K G.n G.m sim 1) + 1)
    let args := [G.n, G.m, 0, G.m, queryLengths G, queryWeights G L, L, sim,
      queryOriginals G L, queryBridges G L, queryHeader G L, queryHeap G L]
    let readTree := fun (mem : ℕ → ℕ) (base : ℕ) =>
      treeFromOutput G mem (base + queryOriginals G L)
        (base + queryBridges G L) (base + queryHeader G L)
    let st := startState
      (relocatedTreeArgs R args (heap + 1) (2 ^ w) src (queryOriginals G L)) mem pos
    host.HasAt (b + 1) (relocatedTreeModule Q b) →
    w ≤ hostWidth → heap + 1 + 2 ^ w ≤ 2 ^ hostWidth → 4 ≤ 2 ^ hostWidth →
    (∀ i < queryOriginals G L, mem (src + i) = queryMemory G L len wt i) →
    src + queryOriginals G L ≤ heap + 1 → ZeroFrom mem (heap + 1) →
    Runs w ⟨lsstModule Q 0 1⟩ (fun _ => false) (lsstEntryProc 0 1)
      (startState args (queryMemory G L len wt) 0) (.returned 0) guestOut guestCost →
    (∀ base moved, (∀ a < 2 ^ w, moved (base + a) = guestOut.mem a) →
      readTree moved base = readTree guestOut.mem 0) →
    guestOut.mem (queryHeader G L) ≤ G.n →
    guestOut.mem (queryHeader G L + 1) ≤ G.n →
    ∃ out cost,
      Runs hostWidth host ω (relocatedTreeEntry Q b)
        st (.returned 0) out cost ∧
      cost ≤ 17 * (queryOriginals G L + 1) + (R + 6) * guestCost + 1 ∧
      readTree out.mem (heap + 1) = readTree guestOut.mem 0 ∧
      out.mem (heap + 1 + queryHeader G L) ≤ G.n ∧
      out.mem (heap + 1 + queryHeader G L + 1) ≤ G.n ∧
      (∀ a < heap + 1, out.mem a = st.mem a) ∧
      ZeroFrom out.mem (heap + 1 + 2 ^ w) := by
  intro R sim w args readTree st hp hw hspace hfour hpacked hdisj hzero hr hdecode hcount hbridges
  exact copyCanonicalTree_atWidth_runs (K := K) mem G L w len wt hc hL hG hp
    le_rfl hw hspace hfour hpacked hdisj hzero hr hdecode hcount hbridges

/-- Procedure contract for one canonical query of Definition 5.8
(pages 19–20). The input prefix is copied from an earlier allocation.
The output is the canonical compact tree in the translated result tables. -/
@[expose] noncomputable def relocatedTreeAtWidthContract (Q : Program) (c₀ W : ℕ)
    (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ) (heap src guestCost : ℕ)
    (tree : MGraph) : Contract :=
  let R := (Program.mk (lsstModule Q 0 1)).regBound
  let sim := lsstLSimMin c₀ G.n G.m L 1
  let args := [G.n, G.m, 0, G.m, queryLengths G, queryWeights G L, L, sim,
    queryOriginals G L, queryBridges G L, queryHeader G L, queryHeap G L]
  let base := heap + 1
  { pre := fun actual mem =>
      actual = relocatedTreeArgs R args base (2 ^ W) src (queryOriginals G L) ∧
        (∀ i < queryOriginals G L, mem (src + i) = queryMemory G L len wt i) ∧
        src + queryOriginals G L ≤ base ∧ ZeroFrom mem base
    post := fun _ mem ret out =>
      ret = 0 ∧ treeFromOutput G out (base + queryOriginals G L)
        (base + queryBridges G L) (base + queryHeader G L) = tree ∧
        out (base + queryHeader G L) ≤ G.n ∧ out (base + queryHeader G L + 1) ≤ G.n ∧
        (∀ a < base, out a = mem a) ∧ ZeroFrom out (base + 2 ^ W)
    cost := fun _ _ => 17 * (queryOriginals G L + 1) + (R + 6) * guestCost + 1 }

/-- Procedure contract for one canonical query of Definition 5.8
(pages 19–20). The input prefix is copied from an earlier allocation.
The output is the canonical compact tree in the translated result tables. -/
@[expose] noncomputable def relocatedTreeContract (Q : Program) (c₀ : ℕ) (K : ℝ)
    (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ) (heap src guestCost : ℕ)
    (tree : MGraph) : Contract :=
  let R := (Program.mk (lsstModule Q 0 1)).regBound
  let sim := lsstLSimMin c₀ G.n G.m L 1
  let w := max 5 (Nat.log 2 (queryHeap G L + lsstSpace Q K G.n G.m sim 1) + 1)
  let args := [G.n, G.m, 0, G.m, queryLengths G, queryWeights G L, L, sim,
    queryOriginals G L, queryBridges G L, queryHeader G L, queryHeap G L]
  let base := heap + 1
  { pre := fun actual mem =>
      actual = relocatedTreeArgs R args base (2 ^ w) src (queryOriginals G L) ∧
        (∀ i < queryOriginals G L, mem (src + i) = queryMemory G L len wt i) ∧
        src + queryOriginals G L ≤ base ∧ ZeroFrom mem base
    post := fun _ mem ret out =>
      ret = 0 ∧ treeFromOutput G out (base + queryOriginals G L)
        (base + queryBridges G L) (base + queryHeader G L) = tree ∧
        out (base + queryHeader G L) ≤ G.n ∧ out (base + queryHeader G L + 1) ≤ G.n ∧
        (∀ a < base, out a = mem a) ∧ ZeroFrom out (base + 2 ^ w)
    cost := fun _ _ => 17 * (queryOriginals G L + 1) + (R + 6) * guestCost + 1 }

/-- The staged arrays and fresh execution region discharge the relocated
tree call's memory premise. -/
theorem relocatedTree_pre_of_arrays (Q : Program) (c₀ : ℕ) (K : ℝ)
    (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ) (heap src guestCost : ℕ)
    (tree : MGraph) (mem : ℕ → ℕ) (hL : 0 < L)
    (ht : ∀ i < G.m, mem (src+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (src+(G.m+i)) = (indexedGraph G).head i)
    (hl : ∀ i < G.m, ListAt mem (src+queryLengths G+i*L)
      (Num.encodeLimbs 1 L (len (edgeName G i))))
    (hv : ∀ i < G.m, ListAt mem (src+queryWeights G L+i*L)
      (Num.encodeLimbs 1 L (wt (edgeName G i))))
    (hsep : src+queryOriginals G L ≤ heap+1) (hz : ZeroFrom mem (heap+1)) :
    let R := (Program.mk (lsstModule Q 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let w := max 5 (Nat.log 2 (queryHeap G L + lsstSpace Q K G.n G.m sim 1) + 1)
    let args := [G.n, G.m, 0, G.m, queryLengths G, queryWeights G L, L, sim,
      queryOriginals G L, queryBridges G L, queryHeader G L, queryHeap G L]
    (relocatedTreeContract Q c₀ K G L len wt heap src guestCost tree).pre
      (relocatedTreeArgs R args (heap+1) (2^w) src (queryOriginals G L)) mem :=
  ⟨rfl,queryMemory_prefix_of_arrays G hL len wt mem ht hh hl hv,hsep,hz⟩

/-- Packing the weights extends an existing endpoint and length prefix
to a complete canonical input, with zero memory after the staging arrays. -/
theorem queryPrefix_of_packedWeights {w P Q src stride L staging ret : ℕ}
    {G : MGraph} {mem out : ℕ → ℕ} (len wt : ℕ → ℤ) (hL : 0 < L)
    (hp : (packGuestWeightsContract w P Q).post
      [src,stride,L,G.m,Q-P,staging+queryWeights G L] mem ret out)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hl : ∀ i < G.m, ListAt mem (staging+queryLengths G+i*L)
      (Num.encodeLimbs 1 L (len (edgeName G i))))
    (hv : ∀ i < G.m, wt (edgeName G i) =
      queryNumerator Q (Num.fixVal mem (src+i*stride) 1 L P)) :
    ret = staging+queryOriginals G L ∧ ZeroFrom out ret ∧
      ∀ i < queryOriginals G L, out (staging+i) = queryMemory G L len wt i := by
  obtain ⟨a,S,N,m,heap,he,hret,hzero,hframe,hpack⟩ := hp
  simp only [List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he
  refine ⟨by simpa [queryOriginals,Nat.add_assoc] using hret,hzero,?_⟩
  apply queryMemory_prefix_of_arrays G hL len wt out
  · intro i hi
    exact (hframe _ (by unfold queryWeights queryLengths; omega)).trans (ht i hi)
  · intro i hi
    exact (hframe _ (by unfold queryWeights queryLengths; omega)).trans (hh i hi)
  · intro i hi j hj
    have hj' : j < L := by simpa using hj
    have hmul := Nat.mul_le_mul_right L hi
    rw [Nat.succ_mul] at hmul
    exact (hframe _ (by unfold queryWeights; omega)).trans (hl i hi j hj)
  · intro i hi
    rw [hv i hi]
    exact hpack i hi

/-- After packing weights, the end of the staging prefix can serve
as the host allocation pointer for the next call. -/
theorem relocatedTree_pre_of_packedWeights {hostWidth P Q src stride L staging ret : ℕ}
    {G : MGraph} {mem out : ℕ → ℕ} (guest : Program) (c₀ : ℕ) (K : ℝ)
    (len wt : ℕ → ℤ) (guestCost : ℕ) (tree : MGraph) (hL : 0 < L)
    (hp : (packGuestWeightsContract hostWidth P Q).post
      [src,stride,L,G.m,Q-P,staging+queryWeights G L] mem ret out)
    (ht : ∀ i < G.m, mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hl : ∀ i < G.m, ListAt mem (staging+queryLengths G+i*L)
      (Num.encodeLimbs 1 L (len (edgeName G i))))
    (hv : ∀ i < G.m, wt (edgeName G i) =
      queryNumerator Q (Num.fixVal mem (src+i*stride) 1 L P)) :
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let w := max 5 (Nat.log 2 (queryHeap G L + lsstSpace guest K G.n G.m sim 1) + 1)
    let args := [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,sim,
      queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L]
    (relocatedTreeContract guest c₀ K G L len wt ret staging guestCost tree).pre
      (relocatedTreeArgs R args (ret+1) (2^w) staging (queryOriginals G L)) out := by
  intro R sim w args
  obtain ⟨hret,hzero,hprefix⟩ := queryPrefix_of_packedWeights len wt hL hp ht hh hl hv
  exact ⟨rfl,hprefix,by omega,fun a ha => hzero a (by omega)⟩

/-- The installed entry meets the procedure contract for a canonical run
and its decoded tree. -/
theorem relocatedTreeAtWidth_meetsContract {Q host : Program} {b hostWidth : ℕ}
    (c₀ : ℕ) (K : ℝ) (G : MGraph) (L W : ℕ) (len wt : ℕ → ℤ)
    (heap src guestCost : ℕ) (guestOut : State)
    (hc : 1 ≤ c₀) (hL : 1 ≤ L) (hG : (indexedGraph G).Valid)
    (hp : host.HasAt b (relocatedTreeProcedures Q b)) :
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let minimum := max 5 (Nat.log 2 (queryHeap G L + lsstSpace Q K G.n G.m sim 1) + 1)
    let args := [G.n, G.m, 0, G.m, queryLengths G, queryWeights G L, L, sim,
      queryOriginals G L, queryBridges G L, queryHeader G L, queryHeap G L]
    let tree := treeFromOutput G guestOut.mem (queryOriginals G L)
      (queryBridges G L) (queryHeader G L)
    minimum ≤ W → W ≤ hostWidth → heap + 1 + 2 ^ W ≤ 2 ^ hostWidth → 4 ≤ 2 ^ hostWidth →
    Runs W ⟨lsstModule Q 0 1⟩ (fun _ => false) (lsstEntryProc 0 1)
      (startState args (queryMemory G L len wt) 0) (.returned 0) guestOut guestCost →
    (∀ base moved, (∀ a < 2 ^ W, moved (base + a) = guestOut.mem a) →
      treeFromOutput G moved (base + queryOriginals G L)
        (base + queryBridges G L) (base + queryHeader G L) = tree) →
    guestOut.mem (queryHeader G L) ≤ G.n →
    guestOut.mem (queryHeader G L + 1) ≤ G.n →
    MeetsContract hostWidth host b
      (relocatedTreeAtWidthContract Q c₀ W G L len wt heap src guestCost tree) := by
  intro sim minimum args tree hmin hw hspace hfour hrun hdecode hcount hbridges
  obtain ⟨hentry, hmodule⟩ := relocatedTreeProcedures_hasAt hp
  intro actual mem pos ω _ hpre
  let R := (Program.mk (lsstModule Q 0 1)).regBound
  change actual = relocatedTreeArgs R args (heap + 1) (2 ^ W) src (queryOriginals G L) ∧
    (∀ i < queryOriginals G L, mem (src + i) = queryMemory G L len wt i) ∧
    src + queryOriginals G L ≤ heap + 1 ∧ ZeroFrom mem (heap + 1) at hpre
  obtain ⟨hactual, hpacked, hdisj, hzero⟩ := hpre
  have hdecode' := fun base moved hm => hdecode base moved hm
  obtain ⟨out, cost, hr, hcst, htree, hcount', hbridges', hlow, hzero'⟩ :=
    copyCanonicalTree_atWidth_runs (K := K) (ω := ω) (pos := pos) mem G L W len wt hc hL hG
      hmodule hmin hw hspace hfour hpacked hdisj hzero hrun (by simpa using hdecode') hcount hbridges
  exact ⟨_, hentry, .returned 0, out, cost, hactual.symm ▸ hr,
    ⟨rfl, by simpa using htree, hcount', hbridges', hlow, hzero'⟩, hcst⟩

/-- The installed entry meets the procedure contract for a canonical run
and its decoded tree. -/
theorem relocatedTree_meetsContract {Q host : Program} {b hostWidth : ℕ}
    (c₀ : ℕ) (K : ℝ) (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ)
    (heap src guestCost : ℕ) (guestOut : State)
    (hc : 1 ≤ c₀) (hL : 1 ≤ L) (hG : (indexedGraph G).Valid)
    (hp : host.HasAt b (relocatedTreeProcedures Q b)) :
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let w := max 5 (Nat.log 2 (queryHeap G L + lsstSpace Q K G.n G.m sim 1) + 1)
    let args := [G.n, G.m, 0, G.m, queryLengths G, queryWeights G L, L, sim,
      queryOriginals G L, queryBridges G L, queryHeader G L, queryHeap G L]
    let tree := treeFromOutput G guestOut.mem (queryOriginals G L)
      (queryBridges G L) (queryHeader G L)
    w ≤ hostWidth → heap + 1 + 2 ^ w ≤ 2 ^ hostWidth → 4 ≤ 2 ^ hostWidth →
    Runs w ⟨lsstModule Q 0 1⟩ (fun _ => false) (lsstEntryProc 0 1)
      (startState args (queryMemory G L len wt) 0) (.returned 0) guestOut guestCost →
    (∀ base moved, (∀ a < 2 ^ w, moved (base + a) = guestOut.mem a) →
      treeFromOutput G moved (base + queryOriginals G L)
        (base + queryBridges G L) (base + queryHeader G L) = tree) →
    guestOut.mem (queryHeader G L) ≤ G.n →
    guestOut.mem (queryHeader G L + 1) ≤ G.n →
    MeetsContract hostWidth host b
      (relocatedTreeContract Q c₀ K G L len wt heap src guestCost tree) := by
  intro sim w args tree hw hspace hfour hrun hdecode hcount hbridges
  obtain ⟨hentry, hmodule⟩ := relocatedTreeProcedures_hasAt hp
  intro actual mem pos ω _ hpre
  let R := (Program.mk (lsstModule Q 0 1)).regBound
  change actual = relocatedTreeArgs R args (heap + 1) (2 ^ w) src (queryOriginals G L) ∧
    (∀ i < queryOriginals G L, mem (src + i) = queryMemory G L len wt i) ∧
    src + queryOriginals G L ≤ heap + 1 ∧ ZeroFrom mem (heap + 1) at hpre
  obtain ⟨hactual, hpacked, hdisj, hzero⟩ := hpre
  have hdecode' := fun base moved hm => hdecode base moved hm
  obtain ⟨out, cost, hr, hcst, htree, hcount', hbridges', hlow, hzero'⟩ :=
    copyCanonicalTree_runs (ω := ω) (pos := pos) mem G L len wt hc hL hG
      hmodule hw hspace hfour hpacked hdisj hzero hrun (by simpa using hdecode') hcount hbridges
  exact ⟨_, hentry, .returned 0, out, cost, hactual.symm ▸ hr,
    ⟨rfl, by simpa using htree, hcount', hbridges', hlow, hzero'⟩, hcst⟩

/-- The padded runtime width preserves the decoded canonical tree and
the cost of the guest run for Definition 5.8 (pages 19–20). -/
theorem relocatedTree_padded_meetsContract {Q host : Program} {b hostWidth : ℕ}
    (c₀ D : ℕ) (K : ℝ) (hK : max K 0 ≤ (D : ℝ)) (G : MGraph) (L : ℕ) (len wt : ℕ → ℤ)
    (heap src guestCost : ℕ) (guestOut : State)
    (hc : 1 ≤ c₀) (hL : 1 ≤ L) (hG : (indexedGraph G).Valid)
    (hp : host.HasAt b (relocatedTreeProcedures Q b)) :
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let w := max 5 (Nat.log 2 (queryHeap G L + lsstSpace Q K G.n G.m sim 1) + 1)
    let W := paddedGuestWidth Q D G.n G.m sim (queryHeap G L)
    let args := [G.n, G.m, 0, G.m, queryLengths G, queryWeights G L, L, sim,
      queryOriginals G L, queryBridges G L, queryHeader G L, queryHeap G L]
    let tree := treeFromOutput G guestOut.mem (queryOriginals G L)
      (queryBridges G L) (queryHeader G L)
    W ≤ hostWidth → heap + 1 + 2 ^ W ≤ 2 ^ hostWidth → 4 ≤ 2 ^ hostWidth →
    Runs w ⟨lsstModule Q 0 1⟩ (fun _ => false) (lsstEntryProc 0 1)
      (startState args (queryMemory G L len wt) 0) (.returned 0) guestOut guestCost →
    (∀ base moved, (∀ a < 2 ^ w, moved (base + a) = guestOut.mem a) →
      treeFromOutput G moved (base + queryOriginals G L)
        (base + queryBridges G L) (base + queryHeader G L) = tree) →
    guestOut.mem (queryHeader G L) ≤ G.n →
    guestOut.mem (queryHeader G L + 1) ≤ G.n →
    MeetsContract hostWidth host b
      (relocatedTreeAtWidthContract Q c₀ W G L len wt heap src guestCost tree) := by
  intro sim w W args tree hw hspace hfour hrun hdecode hcount hbridges
  have hmin : w ≤ W :=
    canonicalGuestWidth_le_padded Q K D G.n G.m sim (queryHeap G L) hK
  apply relocatedTreeAtWidth_meetsContract c₀ K G L W len wt heap src guestCost guestOut
    hc hL hG hp hmin hw hspace hfour
    (canonicalGuestRun_padded Q K D G.n G.m sim (queryHeap G L) hK hrun)
  · intro base moved hm
    have hpow : (2:ℕ)^w ≤ 2^W := Nat.pow_le_pow_right (by decide) hmin
    exact hdecode base moved (fun a ha => hm a (ha.trans_le hpow))
  · exact hcount
  · exact hbridges

/-- The twelve guest arguments derive all array offsets from the runtime
vertex count, edge count, and limb width. The simulation width is a word. -/
@[expose] def canonicalGuestArgsExpr (n m limbs sim : Expr) : List Expr :=
  let lengths : Expr := .bin .add m m
  let block : Expr := .bin .mul m limbs
  let weights : Expr := .bin .add lengths block
  let originals : Expr := .bin .add weights block
  let bridges : Expr := .bin .add originals n
  let header : Expr := .bin .add bridges (.bin .add n n)
  [n,m,.const 0,m,lengths,weights,limbs,sim,originals,bridges,header,
    .bin .add header (.const 2)]

/-- Evaluating the offset expressions gives the canonical guest arguments
at any word size with room for the input and result arrays. -/
theorem canonicalGuestArgsExpr_eval {w : ℕ} {st : State} {n m limbs sim : Expr}
    (G : MGraph) (L S : ℕ)
    (hn : n.eval w st = some G.n) (hm : m.eval w st = some G.m)
    (hL : limbs.eval w st = some L) (hS : sim.eval w st = some S)
    (hroom : queryHeap G L < 2^w) :
    evalArgs w st (canonicalGuestArgsExpr n m limbs sim) =
      some [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,S,
        queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L] := by
  have h0 : 0 < 2^w := Nat.two_pow_pos _
  have h2 : 2 < 2^w := by unfold queryHeap at hroom; omega
  have hh : queryHeader G L < 2^w := by unfold queryHeap at hroom; omega
  have hb : queryBridges G L < 2^w := by unfold queryHeader at hh; omega
  have ho : queryOriginals G L < 2^w := by unfold queryBridges at hb; omega
  have hv : queryWeights G L < 2^w := by unfold queryOriginals at ho; omega
  have hlen : queryLengths G < 2^w := by unfold queryWeights at hv; omega
  have hprod : G.m*L < 2^w := by unfold queryWeights at hv; omega
  have hnn : 2*G.n < 2^w := by unfold queryHeader at hh; omega
  have hlen' : G.m+G.m = queryLengths G := by unfold queryLengths; omega
  have hnn' : G.n+G.n = 2*G.n := by omega
  simp only [canonicalGuestArgsExpr,evalArgs,Expr.eval,BinOp.eval,hn,hm,hL,hS,
    h0,h2,hlen',hnn',hlen,hprod,hnn,hv,ho,hb,hh,hroom,ite_eq_left,
    show queryLengths G+G.m*L = queryWeights G L from rfl,
    show queryWeights G L+G.m*L = queryOriginals G L from rfl,
    show queryOriginals G L+G.n = queryBridges G L from rfl,
    show queryBridges G L+2*G.n = queryHeader G L from rfl,
    show queryHeader G L+2 = queryHeap G L from rfl]


/-- Build the translated tree-call arguments from runtime graph counts,
guest format, and staging addresses. The packer returns the heap word. -/
@[expose] def stagedTreeArgsExpr (R : ℕ)
    (n m limbs sim width staging heap : Expr) : List Expr :=
  let args := canonicalGuestArgsExpr n m limbs sim
  relocatedTreeArgsExpr R args (.bin .add heap (.const 1)) width staging
    (args.getD 8 (.const 0))

/-- The runtime arguments refer to the same staging prefix and padded
guest region as the relocation contract for Definition 5.8 (pages 19–20). -/
theorem stagedTreeArgsExpr_eval {w : ℕ} {st : State}
    {ne me le se we ae he : Expr} (R : ℕ) (G : MGraph)
    (L sim width staging heap : ℕ)
    (hn : ne.eval w st = some G.n) (hm : me.eval w st = some G.m)
    (hL : le.eval w st = some L) (hs : se.eval w st = some sim)
    (hw : we.eval w st = some width) (ha : ae.eval w st = some staging)
    (hh : he.eval w st = some heap)
    (hguest : queryHeap G L < 2^w)
    (hspace : heap+1+2^width ≤ 2^w) :
    evalArgs w st (stagedTreeArgsExpr R ne me le se we ae he) =
      some (relocatedTreeArgs R
        [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,sim,
          queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L]
        (heap+1) (2^width) staging (queryOriginals G L)) := by
  have hargs := canonicalGuestArgsExpr_eval G L sim hn hm hL hs hguest
  have hpos := Nat.two_pow_pos width
  have hbase : heap+1 < 2^w := by omega
  have hone : 1 < 2^w := by omega
  have hmod : 2^width < 2^w := by omega
  unfold stagedTreeArgsExpr
  apply relocatedTreeArgsExpr_eval R hargs _ hw ha _ hmod
  · simp [Expr.eval,BinOp.eval,hh,hone,hbase]
  · exact evalArgs_getD hargs 8

/-- Pack the staged weights, then call the tree procedure with the
allocation cursor in register `packed`. -/
@[expose] def packAndQueryTreeBody (pack query packed result : ℕ)
    (weightArgs treeArgs : List Expr) (finish : Expr) : Stmt :=
  .seq (.call packed pack weightArgs)
    (.seq (.call result query treeArgs) (.ret finish))

/-- The linked packing and tree calls return the canonical tree and
preserve the staging prefix. -/
theorem packAndQueryTree_atWidth_runs {w pack query packed result P Q : ℕ} {p : Program} {ω : ℕ → Bool}
    {weightArgs treeArgs : List Expr} {finish : Expr} {returned : ℕ} {G tree : MGraph}
    (st : State) (guest : Program) (c₀ width : ℕ) (len wt : ℕ → ℤ)
    (src stride L staging guestCost : ℕ)
    (hp : MeetsContract w p pack (packGuestWeightsContract w P Q)) :
    let wa := [src,stride,L,G.m,Q-P,staging+queryWeights G L]
    let heap := staging+queryOriginals G L
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let args := [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,sim,
      queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L]
    let ta := relocatedTreeArgs R args (heap+1) (2^width) staging (queryOriginals G L)
    let C := relocatedTreeAtWidthContract guest c₀ width G L len wt heap staging guestCost tree
    MeetsContract w p query C →
    evalArgs w st weightArgs = some wa → (∀ x ∈ wa, x < 2^w) →
    (packGuestWeightsContract w P Q).pre wa st.mem →
    (∀ mem pos, (packGuestWeightsContract w P Q).post wa st.mem heap mem →
      evalArgs w ⟨mem,Function.update st.regs packed heap,pos⟩ treeArgs = some ta) →
    (∀ mem pos, finish.eval w
      ⟨mem,Function.update (Function.update st.regs packed heap) result 0,pos⟩ =
        some returned) →
    (∀ x ∈ ta, x < 2^w) → 0 < L →
    (∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i) →
    (∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i) →
    (∀ i < G.m, ListAt st.mem (staging+queryLengths G+i*L)
      (Num.encodeLimbs 1 L (len (edgeName G i)))) →
    (∀ i < G.m, wt (edgeName G i) =
      queryNumerator Q (Num.fixVal st.mem (src+i*stride) 1 L P)) →
    ∃ o out cost, Runs w p ω (packAndQueryTreeBody pack query packed result weightArgs treeArgs finish)
      st o out cost ∧
      (o.value = returned ∧ out.mem (heap+1+queryHeader G L) ≤ G.n ∧
        out.mem (heap+1+queryHeader G L+1) ≤ G.n ∧
        treeFromOutput G out.mem (heap+1+queryOriginals G L)
          (heap+1+queryBridges G L) (heap+1+queryHeader G L) = tree ∧
        (∀ a < staging+queryWeights G L, out.mem a = st.mem a) ∧
        ZeroFrom out.mem (heap+1+2^width)) ∧
      cost ≤ argsSize weightArgs + argsSize treeArgs + (35*L+60)*G.m+10 +
        17*(queryOriginals G L+1)+(R+6)*guestCost+6+finish.size := by
  intro wa heap R sim args ta C ht hwa hww hpre hta hfinish htw hL htail hhead hlen hwt
  apply runs_start_le
  unfold packAndQueryTreeBody
  refine runs_seq_call_le hp hwa hww hpre ?_
  intro ret mid pos hm
  have hmCopy := hm
  obtain ⟨a,S,N,m,base,he,hret,_,hframe,_⟩ := hmCopy
  simp only [wa,List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he
  have he' : ret = heap := by simpa [heap,queryOriginals,Nat.add_assoc] using hret
  clear hret
  subst ret
  obtain ⟨hcursor,hzero,hprefix⟩ :=
    queryPrefix_of_packedWeights len wt hL hm htail hhead hlen hwt
  have hquery : C.pre ta mid :=
    ⟨rfl,hprefix,by omega,fun a ha => hzero a (by omega)⟩
  refine runs_seq_call_le ht (hta mid pos hm) htw hquery ?_
  intro r out next hout
  obtain ⟨hr,houtTree,hcount,hbridge,hprefix,hzero⟩ := hout
  subst r
  refine runs_ret_le (v := returned) (hfinish out next) ⟨rfl,hcount,hbridge,houtTree,?_,hzero⟩ ?_
  · intro a ha
    have hle : staging+queryWeights G L ≤ heap+1 := by
      unfold heap queryOriginals
      omega
    exact (hprefix a (ha.trans_le hle)).trans (hframe a ha)
  · simp only [wa, C, R, packGuestWeightsContract, relocatedTreeAtWidthContract,
      List.getD_cons_succ,List.getD_cons_zero,Nat.zero_add]
    omega

/-- Last cell reserved by the staged query, including the relocated guest. -/
@[expose] def stagedGuestCursorExpr : Expr :=
  .bin .add (.reg 6) (.bin .shiftLeft (.const 1) (.reg 4))

/-- The staged query uses fixed register positions for graph counts,
guest format and staging pointer, then takes the heap from the packer. -/
theorem packAndQueryStagedTree_runs {w pack query P Q : ℕ} {p : Program} {ω : ℕ → Bool}
    {weightArgs : List Expr} {G tree : MGraph}
    (st : State) (guest : Program) (c₀ width : ℕ) (len wt : ℕ → ℤ)
    (src stride L staging guestCost : ℕ)
    (hp : MeetsContract w p pack (packGuestWeightsContract w P Q)) :
    let wa := [src,stride,L,G.m,Q-P,staging+queryWeights G L]
    let heap := staging+queryOriginals G L
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let args := [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,sim,
      queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L]
    let treeArgs := stagedTreeArgsExpr R (.reg 0) (.reg 1) (.reg 2) (.reg 3)
      (.reg 4) (.reg 5) (.reg 6)
    let C := relocatedTreeAtWidthContract guest c₀ width G L len wt heap staging guestCost tree
    MeetsContract w p query C →
    evalArgs w st weightArgs = some wa → (∀ x ∈ wa, x < 2^w) →
    (packGuestWeightsContract w P Q).pre wa st.mem →
    st.regs 0 = G.n → st.regs 1 = G.m → st.regs 2 = L → st.regs 3 = sim →
    st.regs 4 = width → st.regs 5 = staging →
    queryHeap G L < 2^w → heap+1+2^width ≤ 2^w →
    (∀ r, args.getD r 0 < 2^width) → 0 < L →
    (∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i) →
    (∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i) →
    (∀ i < G.m, ListAt st.mem (staging+queryLengths G+i*L)
      (Num.encodeLimbs 1 L (len (edgeName G i)))) →
    (∀ i < G.m, wt (edgeName G i) =
      queryNumerator Q (Num.fixVal st.mem (src+i*stride) 1 L P)) →
    ∃ o out cost, Runs w p ω (packAndQueryTreeBody pack query 6 7 weightArgs treeArgs stagedGuestCursorExpr)
      st o out cost ∧
      (o.value = heap+2^width ∧ out.mem (heap+1+queryHeader G L) ≤ G.n ∧
        out.mem (heap+1+queryHeader G L+1) ≤ G.n ∧
        treeFromOutput G out.mem (heap+1+queryOriginals G L)
          (heap+1+queryBridges G L) (heap+1+queryHeader G L) = tree ∧
        (∀ a < staging+queryWeights G L, out.mem a = st.mem a) ∧
        ZeroFrom out.mem (heap+1+2^width)) ∧
      cost ≤ argsSize weightArgs + argsSize treeArgs + (35*L+60)*G.m+10 +
        17*(queryOriginals G L+1)+(R+6)*guestCost+6+stagedGuestCursorExpr.size := by
  intro wa heap R sim args treeArgs C ht hwa hww hpre hn hm hL hs hw ha
    hguest hspace hregs hpos htail hhead hlen hwt
  apply packAndQueryTree_atWidth_runs st guest c₀ width len wt src stride L staging guestCost
    hp ht hwa hww hpre _ _ _ hpos htail hhead hlen hwt
  · intro mem pos _
    apply stagedTreeArgsExpr_eval R G L sim width staging heap _ _ _ _ _ _ _ hguest hspace
    all_goals simp [Expr.eval, Function.update, hn, hm, hL, hs, hw, ha, heap]
  · intro mem pos
    have hmod : 2^width < 2^w := by omega
    have hone : 1 < 2^w := (Nat.one_le_pow _ _ (by decide)).trans_lt hmod
    have hfit : heap+2^width < 2^w := by omega
    simp [stagedGuestCursorExpr,Expr.eval,BinOp.eval,Function.update,hw,hmod,hone,hfit,
      Nat.shiftLeft_eq,heap]
  · apply relocatedTreeArgs_words hregs (by omega) hspace
    dsimp [heap]
    omega

/-- The staged host query returns the decoded tree of the canonical
guest run, using the padded modulus and runtime register arguments. -/
theorem packAndQueryPaddedTree_runs {w pack query P Q : ℕ} {p : Program} {ω : ℕ → Bool}
    {weightArgs : List Expr} {G : MGraph}
    (st : State) (guest : Program) (c₀ D : ℕ) (K : ℝ) (hK : max K 0 ≤ (D : ℝ)) (len wt : ℕ → ℤ)
    (src stride L staging guestCost : ℕ) (guestOut : State)
    (hc : 1 ≤ c₀) (hG : (indexedGraph G).Valid)
    (hinstalled : p.HasAt query (relocatedTreeProcedures guest query))
    (hp : MeetsContract w p pack (packGuestWeightsContract w P Q)) :
    let wa := [src,stride,L,G.m,Q-P,staging+queryWeights G L]
    let heap := staging+queryOriginals G L
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G L)
    let minimum := max 5 (Nat.log 2 (queryHeap G L + lsstSpace guest K G.n G.m sim 1) + 1)
    let args := [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,sim,
      queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L]
    let treeArgs := stagedTreeArgsExpr R (.reg 0) (.reg 1) (.reg 2) (.reg 3)
      (.reg 4) (.reg 5) (.reg 6)
    let tree := treeFromOutput G guestOut.mem (queryOriginals G L)
      (queryBridges G L) (queryHeader G L)
    Runs minimum ⟨lsstModule guest 0 1⟩ (fun _ => false) (lsstEntryProc 0 1)
      (startState args (queryMemory G L len wt) 0) (.returned 0) guestOut guestCost →
    (∀ base moved, (∀ a < 2^minimum, moved (base+a) = guestOut.mem a) →
      treeFromOutput G moved (base+queryOriginals G L)
        (base+queryBridges G L) (base+queryHeader G L) = tree) →
    guestOut.mem (queryHeader G L) ≤ G.n →
    guestOut.mem (queryHeader G L+1) ≤ G.n →
    evalArgs w st weightArgs = some wa → (∀ x ∈ wa, x < 2^w) →
    (packGuestWeightsContract w P Q).pre wa st.mem →
    st.regs 0 = G.n → st.regs 1 = G.m → st.regs 2 = L → st.regs 3 = sim →
    st.regs 4 = width → st.regs 5 = staging →
    queryHeap G L < 2^w → heap+1+2^width ≤ 2^w →
    width ≤ w → 4 ≤ 2^w → 0 < L →
    (∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i) →
    (∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i) →
    (∀ i < G.m, ListAt st.mem (staging+queryLengths G+i*L)
      (Num.encodeLimbs 1 L (len (edgeName G i)))) →
    (∀ i < G.m, wt (edgeName G i) =
      queryNumerator Q (Num.fixVal st.mem (src+i*stride) 1 L P)) →
    ∃ o out cost, Runs w p ω (packAndQueryTreeBody pack query 6 7 weightArgs treeArgs stagedGuestCursorExpr)
      st o out cost ∧
      (o.value = heap+2^width ∧ out.mem (heap+1+queryHeader G L) ≤ G.n ∧
        out.mem (heap+1+queryHeader G L+1) ≤ G.n ∧
        treeFromOutput G out.mem (heap+1+queryOriginals G L)
          (heap+1+queryBridges G L) (heap+1+queryHeader G L) = tree ∧
        (∀ a < staging+queryWeights G L, out.mem a = st.mem a) ∧
        ZeroFrom out.mem (heap+1+2^width)) ∧
      cost ≤ argsSize weightArgs + argsSize treeArgs + (35*L+60)*G.m+10 +
        17*(queryOriginals G L+1)+(R+6)*guestCost+6+stagedGuestCursorExpr.size := by
  intro wa heap R sim width minimum args treeArgs tree hrun hdecode hcount hbridges
    hwa hww hpre hn hm hL hs hw ha hguest hspace hwidth hfour hpos
    htail hhead hlen hwt
  have ht := relocatedTree_padded_meetsContract c₀ D K hK G L len wt heap staging guestCost
    guestOut hc hpos hG hinstalled hwidth hspace hfour hrun hdecode hcount hbridges
  obtain ⟨_,_,_,hregs⟩ :=
    canonicalTreeCall_wordBounds guest c₀ K hc G L hpos (queryMemory G L len wt)
  have hmin : minimum ≤ width :=
    canonicalGuestWidth_le_padded guest K D G.n G.m sim (queryHeap G L) hK
  have hpow : (2:ℕ)^minimum ≤ 2^width := Nat.pow_le_pow_right (by decide) hmin
  exact packAndQueryStagedTree_runs st guest c₀ width len wt src stride L staging guestCost hp
    ht hwa hww hpre hn hm hL hs hw ha hguest hspace (fun r => (hregs r).trans_le hpow)
    hpos htail hhead hlen hwt

/-- The linked packing and tree calls return the canonical tree and
preserve the staging prefix. -/
theorem packAndQueryTree_runs {w pack query packed result P Q : ℕ} {p : Program} {ω : ℕ → Bool}
    {weightArgs treeArgs : List Expr} {G tree : MGraph}
    (st : State) (guest : Program) (c₀ : ℕ) (K : ℝ) (len wt : ℕ → ℤ)
    (src stride L staging guestCost : ℕ)
    (hp : MeetsContract w p pack (packGuestWeightsContract w P Q)) :
    let wa := [src,stride,L,G.m,Q-P,staging+queryWeights G L]
    let heap := staging+queryOriginals G L
    let R := (Program.mk (lsstModule guest 0 1)).regBound
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let width := max 5 (Nat.log 2 (queryHeap G L + lsstSpace guest K G.n G.m sim 1) + 1)
    let args := [G.n,G.m,0,G.m,queryLengths G,queryWeights G L,L,sim,
      queryOriginals G L,queryBridges G L,queryHeader G L,queryHeap G L]
    let ta := relocatedTreeArgs R args (heap+1) (2^width) staging (queryOriginals G L)
    let C := relocatedTreeContract guest c₀ K G L len wt heap staging guestCost tree
    MeetsContract w p query C →
    evalArgs w st weightArgs = some wa → (∀ x ∈ wa, x < 2^w) →
    (packGuestWeightsContract w P Q).pre wa st.mem →
    (∀ mem pos, (packGuestWeightsContract w P Q).post wa st.mem heap mem →
      evalArgs w ⟨mem,Function.update st.regs packed heap,pos⟩ treeArgs = some ta) →
    (∀ x ∈ ta, x < 2^w) → 0 < L →
    (∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i) →
    (∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i) →
    (∀ i < G.m, ListAt st.mem (staging+queryLengths G+i*L)
      (Num.encodeLimbs 1 L (len (edgeName G i)))) →
    (∀ i < G.m, wt (edgeName G i) =
      queryNumerator Q (Num.fixVal st.mem (src+i*stride) 1 L P)) →
    ∃ o out cost, Runs w p ω (packAndQueryTreeBody pack query packed result weightArgs treeArgs (.reg result))
      st o out cost ∧
      (o.value = 0 ∧ out.mem (heap+1+queryHeader G L) ≤ G.n ∧
        out.mem (heap+1+queryHeader G L+1) ≤ G.n ∧
        treeFromOutput G out.mem (heap+1+queryOriginals G L)
          (heap+1+queryBridges G L) (heap+1+queryHeader G L) = tree ∧
        (∀ a < staging+queryWeights G L, out.mem a = st.mem a) ∧
        ZeroFrom out.mem (heap+1+2^width)) ∧
      cost ≤ argsSize weightArgs + argsSize treeArgs + (35*L+60)*G.m+10 +
        17*(queryOriginals G L+1)+(R+6)*guestCost+7 := by
  intro wa heap R sim width args ta C ht hwa hww hpre hta htw hL htail hhead hlen hwt
  exact packAndQueryTree_atWidth_runs st guest c₀ width len wt src stride L staging guestCost
    hp ht hwa hww hpre hta (by intro _ _; simp [Expr.eval,Function.update]) htw hL
    htail hhead hlen hwt

end MinCostFlow.LastLevelProgram
