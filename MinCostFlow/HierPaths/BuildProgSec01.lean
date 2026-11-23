module

public import MinCostFlow.HierPaths.BuildProgWalkCollect
public import MinCostFlow.HierPaths.BuildProgCopy
public import MinCostFlow.HierPaths.BuildProgLevelModel
import MinCostFlow.HierPaths.InitLayout

/-!
# Writing sections 0 and 1 of the level encoding

Pass B of the non-singleton level builder writes:
- Section 0 (`buildSec0Proc`): `csrList k (fun c => (D.host c).encode)` from the finished child
  graph slots `[slots, slots + k * slotWords)`, replacing vertex count `s` by `G.n` and shifting
  every edge endpoint by `start + c * s`.
- Section 1 (`buildSec1Proc`): `csrList k (fun c => csrList (D.host c).m (D.emb c))` from the
  collected per-child walk pointer table `WalkTableAt` using `buildCopyProc`.

Both procedures write sequentially above `dst`, preserve all memory below `dst`, leave `ZeroFrom`
above the returned end address, and incur cost independent of `G.n`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Section 0 word list for a child family `F`. -/
def sec0Words (gn start s k : ℕ) (F : ℕ → List ((ℕ × ℕ) × List ℕ)) : List ℕ :=
  csrList k fun c => (Graph.mk gn (shiftEdges (start + c * s) ((F c).map Prod.fst))).encode

/-- Section 1 word list for a child family `F`. -/
def sec1Words (k : ℕ) (F : ℕ → List ((ℕ × ℕ) × List ℕ)) : List ℕ :=
  csrList k fun c => csrList (F c).length fun e => ((F c).getD e ((0, 0), [])).2

/-- Write section 0 at `dst` and return `dst + (sec0Words ...).length`.
Args: `[gAddr, start, s, k, slots, slotWords, dst]`. -/
def buildSec0Proc : Stmt :=
  .assign 7 (.load (.reg 0)) ;;
  .assign 8 (.bin .add (.bin .add (.reg 6) (.reg 3)) (.const 1)) ;;
  .assign 9 (.reg 8) ;;
  forRange 10 (.const 0) (.reg 3)
    (.store (.bin .add (.reg 6) (.reg 10)) (.bin .sub (.reg 9) (.reg 8)) ;;
     .assign 11 (.bin .add (.reg 4) (.bin .mul (.reg 10) (.reg 5))) ;;
     .assign 12 (.bin .add (.reg 1) (.bin .mul (.reg 10) (.reg 2))) ;;
     .assign 13 (.load (.bin .add (.reg 11) (.const 1))) ;;
     .store (.reg 9) (.reg 7) ;;
     .store (.bin .add (.reg 9) (.const 1)) (.reg 13) ;;
     .assign 14 (.bin .add (.reg 13) (.reg 13)) ;;
     forRange 15 (.const 0) (.reg 14)
       (.store (.bin .add (.bin .add (.reg 9) (.const 2)) (.reg 15))
               (.bin .add (.load (.bin .add (.bin .add (.reg 11) (.const 2)) (.reg 15))) (.reg 12))) ;;
     .assign 9 (.bin .add (.bin .add (.reg 9) (.const 2)) (.reg 14))) ;;
  .store (.bin .add (.reg 6) (.reg 3)) (.bin .sub (.reg 9) (.reg 8)) ;;
  .ret (.reg 9)

theorem buildSec0Proc_noRand : buildSec0Proc.NoRand := by
  simp [buildSec0Proc, forRange, forUp, Stmt.NoRand]

/-- Contract for `buildSec0Proc`. -/
def buildSec0Contract (w gn start s k maxM : ℕ)
    (F : ℕ → List ((ℕ × ℕ) × List ℕ)) : Contract where
  pre args mem := ∃ gAddr slots slotWords dst,
    args = [gAddr, start, s, k, slots, slotWords, dst] ∧
    mem gAddr = gn ∧ gAddr < dst ∧ slots + k * slotWords ≤ dst ∧ 2 + 2 * maxM ≤ slotWords ∧
    (∀ c < k, GraphAt mem (slots + c * slotWords) ⟨s, (F c).map Prod.fst⟩ ∧
      (F c).length ≤ maxM ∧ (∀ e ∈ (F c).map Prod.fst, e.1 < s ∧ e.2 < s)) ∧
    ZeroFrom mem dst ∧ dst + (sec0Words gn start s k F).length < 2 ^ w ∧
    start + k * s < 2 ^ w ∧ gn < 2 ^ w ∧ 2 < 2 ^ w
  post args mem v after := ∃ gAddr slots slotWords dst,
    args = [gAddr, start, s, k, slots, slotWords, dst] ∧
    v = dst + (sec0Words gn start s k F).length ∧
    ListAt after dst (sec0Words gn start s k F) ∧
    (∀ a < dst, after a = mem a) ∧ ZeroFrom after v
  cost _ _ := k * (50 * maxM + 105) + 60

/-- Write section 1 at `dst` and return `dst + (sec1Words ...).length`.
Args: `[k, walkCnt, walkPtrs, cap, dst]`. -/
def buildSec1Proc (fCopy : ℕ) : Stmt :=
  .assign 5 (.bin .add (.bin .add (.reg 4) (.reg 0)) (.const 1)) ;;
  .assign 6 (.reg 5) ;;
  forRange 7 (.const 0) (.reg 0)
    (.store (.bin .add (.reg 4) (.reg 7)) (.bin .sub (.reg 6) (.reg 5)) ;;
     .assign 8 (.load (.bin .add (.reg 1) (.reg 7))) ;;
     .assign 9 (.bin .add (.reg 2) (.bin .mul (.reg 7) (.reg 3))) ;;
     .assign 10 (.bin .add (.bin .add (.reg 6) (.reg 8)) (.const 1)) ;;
     .assign 11 (.reg 10) ;;
     forRange 12 (.const 0) (.reg 8)
       (.store (.bin .add (.reg 6) (.reg 12)) (.bin .sub (.reg 11) (.reg 10)) ;;
        .assign 13 (.load (.bin .add (.reg 9) (.reg 12))) ;;
        .assign 14 (.load (.reg 13)) ;;
        .call 15 fCopy [.bin .add (.reg 13) (.const 1), .reg 14, .reg 11] ;;
        .assign 11 (.bin .add (.reg 11) (.reg 14))) ;;
     .store (.bin .add (.reg 6) (.reg 8)) (.bin .sub (.reg 11) (.reg 10)) ;;
     .assign 6 (.reg 11)) ;;
  .store (.bin .add (.reg 4) (.reg 0)) (.bin .sub (.reg 6) (.reg 5)) ;;
  .ret (.reg 6)

theorem buildSec1Proc_noRand (fCopy : ℕ) : (buildSec1Proc fCopy).NoRand := by
  simp [buildSec1Proc, forRange, forUp, Stmt.NoRand]

/-- Contract for `buildSec1Proc`. -/
def buildSec1Contract (w k d maxM : ℕ) (F : ℕ → List ((ℕ × ℕ) × List ℕ)) : Contract where
  pre args mem := ∃ walkCnt walkPtrs cap dst,
    args = [k, walkCnt, walkPtrs, cap, dst] ∧
    WalkTableAt k walkCnt walkPtrs cap (fun c => (F c).map Prod.snd) mem ∧
    walkPtrs + k * cap ≤ dst ∧
    (∀ c < k, (F c).length ≤ maxM ∧
      ∀ e < (F c).length, ((F c).getD e ((0, 0), [])).2.length ≤ d) ∧
    ZeroFrom mem dst ∧ dst + (sec1Words k F).length < 2 ^ w ∧ 2 < 2 ^ w
  post args mem v after := ∃ walkCnt walkPtrs cap dst,
    args = [k, walkCnt, walkPtrs, cap, dst] ∧
    v = dst + (sec1Words k F).length ∧
    ListAt after dst (sec1Words k F) ∧
    (∀ a < dst, after a = mem a) ∧ ZeroFrom after v
  cost _ _ := k * (maxM * (17 * d + 85) + 115) + 60

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

private theorem flatMap_shiftEdges (off : ℕ) (E : List (ℕ × ℕ)) :
    (shiftEdges off E).flatMap (fun e => [e.1, e.2]) =
      (E.flatMap fun e => [e.1, e.2]).map (· + off) := by
  induction E with
  | nil => simp [shiftEdges]
  | cons p rest ih =>
    simp only [shiftEdges, List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append,
      Nat.add_comm] at ih ⊢
    congr 2

private theorem length_flatMap_pair (E : List (ℕ × ℕ)) :
    (E.flatMap fun e => [e.1, e.2]).length = 2 * E.length := by
  induction E with
  | nil => simp
  | cons p rest ih => simp [ih]; omega

private theorem getElem_flatMap_pair_lt {s : ℕ} {E : List (ℕ × ℕ)}
    (hE : ∀ e ∈ E, e.1 < s ∧ e.2 < s) {i : ℕ} (hi : i < (E.flatMap fun e => [e.1, e.2]).length) :
    (E.flatMap fun e => [e.1, e.2])[i]'hi < s := by
  have hmem := List.getElem_mem hi
  obtain ⟨e, he, hmem2⟩ := List.mem_flatMap.mp hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rcases hmem2 with h1 | h2
  · rw [h1]; exact (hE e he).1
  · rw [h2]; exact (hE e he).2

private theorem encode_shiftEdges_eq (gn off : ℕ) (E : List (ℕ × ℕ)) :
    (Graph.mk gn (shiftEdges off E)).encode =
      gn :: E.length :: (E.flatMap fun e => [e.1, e.2]).map (· + off) := by
  rw [Graph.encode, Graph.m, flatMap_shiftEdges]
  simp [shiftEdges]

/-- Prefix sum of CSR row lengths. -/
private def csrPrefix (f : ℕ → List ℕ) (n : ℕ) : ℕ :=
  ((List.range n).map fun i => (f i).length).sum

private theorem csrPrefix_zero (f : ℕ → List ℕ) : csrPrefix f 0 = 0 := by
  simp [csrPrefix]

private theorem csrPrefix_succ (f : ℕ → List ℕ) (n : ℕ) :
    csrPrefix f (n + 1) = csrPrefix f n + (f n).length := by
  simp [csrPrefix, List.range_succ]

private theorem csrPrefix_le {f : ℕ → List ℕ} {n k : ℕ} (hn : n ≤ k) :
    csrPrefix f n ≤ csrPrefix f k := by
  have hgen : ∀ d, csrPrefix f n ≤ csrPrefix f (n + d) := by
    intro d; induction d with
    | zero => simp
    | succ d ih => rw [← Nat.add_assoc, csrPrefix_succ]; omega
  simpa [Nat.add_sub_of_le hn] using hgen (k - n)

private theorem length_csrList_eq (k : ℕ) (f : ℕ → List ℕ) :
    (csrList k f).length = k + 1 + csrPrefix f k := by
  rw [csrList, List.length_append, length_csrOffsets, length_csrData_eq]
  rfl

/-- Assemble `ListAt mem dst (csrList k f)` from offsets and rows. -/
private theorem listAt_csrList_of_parts {mem : ℕ → ℕ} {dst k : ℕ} {f : ℕ → List ℕ}
    (hOff : ∀ i ≤ k, mem (dst + i) = csrPrefix f i)
    (hRow : ∀ i < k, ListAt mem (dst + k + 1 + csrPrefix f i) (f i)) :
    ListAt mem dst (csrList k f) := by
  rw [csrList]
  refine listAt_append.mpr ⟨?_, ?_⟩
  · intro i hi
    rw [length_csrOffsets] at hi
    simpa [csrOffsets, csrPrefix] using hOff i (Nat.lt_succ_iff.mp hi)
  · rw [length_csrOffsets]
    have hgen : ∀ n ≤ k, ListAt mem (dst + (k + 1)) (csrData n f) := by
      intro n
      induction n with
      | zero => intro _ i hi; simp [csrData] at hi
      | succ n ih =>
        intro hn
        unfold csrData
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
        refine listAt_append.mpr ⟨ih (Nat.le_of_succ_le hn), ?_⟩
        change ListAt mem (dst + (k + 1) + (csrData n f).length) (f n)
        rw [length_csrData_eq]
        have h1 := hRow n hn
        rwa [Nat.add_assoc dst k 1] at h1
    exact hgen k le_rfl

/-- Length bound on section 0. -/
theorem sec0Words_length_le {gn start s k maxM : ℕ} {F : ℕ → List ((ℕ × ℕ) × List ℕ)}
    (hM : ∀ c < k, (F c).length ≤ maxM) :
    (sec0Words gn start s k F).length ≤ 3 * k + 1 + 2 * (k * maxM) := by
  unfold sec0Words
  rw [length_csrList_eq]
  have hgen : ∀ n ≤ k,
      csrPrefix (fun c => (Graph.mk gn (shiftEdges (start + c * s) ((F c).map Prod.fst))).encode) n ≤
        2 * n + 2 * (n * maxM) := by
    intro n
    induction n with
    | zero => intro _; simp [csrPrefix]
    | succ n ih =>
      intro hn
      rw [csrPrefix_succ, encode_shiftEdges_eq]
      have h1 := ih (Nat.le_of_succ_le hn)
      have h3 := hM n hn
      simp only [List.length_cons, List.length_map, length_flatMap_pair, Nat.succ_mul] at *
      omega
  have := hgen k le_rfl
  omega

/-- Length bound on section 1. -/
theorem sec1Words_length_le {k d maxM : ℕ} {F : ℕ → List ((ℕ × ℕ) × List ℕ)}
    (hM : ∀ c < k, (F c).length ≤ maxM)
    (hD : ∀ c < k, ∀ e < (F c).length, ((F c).getD e ((0, 0), [])).2.length ≤ d) :
    (sec1Words k F).length ≤ 2 * k + 1 + k * (maxM * (d + 1)) := by
  unfold sec1Words
  rw [length_csrList_eq]
  have hRowLen : ∀ c < k,
      (csrList (F c).length fun e => ((F c).getD e ((0, 0), [])).2).length ≤
        1 + maxM * (d + 1) := by
    intro c hc
    rw [length_csrList_eq]
    have hgen : ∀ n ≤ (F c).length,
        csrPrefix (fun e => ((F c).getD e ((0, 0), [])).2) n ≤ n * d := by
      intro n
      induction n with
      | zero => intro _; simp [csrPrefix]
      | succ n ih =>
        intro hn
        rw [csrPrefix_succ, Nat.succ_mul]
        have h1 := ih (Nat.le_of_succ_le hn)
        have h2 := hD c hc n hn
        omega
    have h1 := hgen (F c).length le_rfl
    have h2 := hM c hc
    have h3 : (F c).length * d ≤ maxM * d := Nat.mul_le_mul_right d h2
    have h4 : maxM * (d + 1) = maxM * d + maxM := by ring
    omega
  have hgen : ∀ n ≤ k,
      csrPrefix (fun c => csrList (F c).length fun e => ((F c).getD e ((0, 0), [])).2) n ≤
        n + n * (maxM * (d + 1)) := by
    intro n
    induction n with
    | zero => intro _; simp [csrPrefix]
    | succ n ih =>
      intro hn
      rw [csrPrefix_succ, Nat.succ_mul]
      have h1 := ih (Nat.le_of_succ_le hn)
      have h2 := hRowLen n hn
      omega
  have := hgen k le_rfl
  omega

/-- Connection between `sec0Words`/`sec1Words` and `levelDataOfFamily`. -/
theorem sec0Words_eq_levelHost (route : RouterFn) (G : Graph) (start s k Δ L : ℕ)
    (F : ℕ → List ((ℕ × ℕ) × List ℕ)) :
    sec0Words G.n start s k F =
      csrList k (fun c => ((levelDataOfFamily route G start s k Δ L F).host c).encode) := rfl

theorem sec1Words_eq_levelEmb (route : RouterFn) (G : Graph) (start s k Δ L : ℕ)
    (F : ℕ → List ((ℕ × ℕ) × List ℕ)) :
    sec1Words k F =
      csrList k (fun c => csrList ((levelDataOfFamily route G start s k Δ L F).host c).m
        ((levelDataOfFamily route G start s k Δ L F).emb c)) := by
  unfold sec1Words levelDataOfFamily
  congr 1; funext c
  simp [Graph.m, shiftEdges]

/-- `buildSec0Proc` meets `buildSec0Contract`. -/
theorem buildSec0Proc_meetsContract {w f gn start s k maxM : ℕ}
    {F : ℕ → List ((ℕ × ℕ) × List ℕ)} {p : Program}
    (hf : p.procs[f]? = some buildSec0Proc) :
    MeetsContract w p f (buildSec0Contract w gn start s k maxM F) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨gAddr, slots, slotWords, dst, rfl, hgn, hgLt, hSlotsLe, hSlotW, hSlots,
    hZF, htop, hstW, hgnW, hw2⟩ := hPre
  let row0 : ℕ → List ℕ := fun c =>
    (Graph.mk gn (shiftEdges (start + c * s) ((F c).map Prod.fst))).encode
  have hSecLen : (sec0Words gn start s k F).length = k + 1 + csrPrefix row0 k :=
    length_csrList_eq k row0
  let dataBase := dst + k + 1
  have hDBW : dataBase < 2 ^ w := by dsimp [dataBase]; omega
  refine runs_start_le ?_
  unfold buildSec0Proc
  refine runs_seq_assign_le (v := gn)
    (by rw [← hgn]; exact Expr.eval_load
          (Expr.eval_reg_of_eq (show (startState [gAddr, start, s, k, slots, slotWords, dst] mem pos).regs 0 = gAddr from rfl))) ?_
  refine runs_seq_assign_le (v := dataBase)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_reg_of_eq (by simp [startState])) (by dsimp [dataBase] at hDBW; omega))
      (Expr.eval_const (by omega)) hDBW) ?_
  refine runs_seq_assign_le (v := dataBase) (Expr.eval_reg_of_eq (by simp)) ?_
  have hOuter := Triple.forRange_const (w := w) (p := p) (r := 10) (lo := .const 0) (hi := .reg 3)
    (body :=
      .store (.bin .add (.reg 6) (.reg 10)) (.bin .sub (.reg 9) (.reg 8)) ;;
      .assign 11 (.bin .add (.reg 4) (.bin .mul (.reg 10) (.reg 5))) ;;
      .assign 12 (.bin .add (.reg 1) (.bin .mul (.reg 10) (.reg 2))) ;;
      .assign 13 (.load (.bin .add (.reg 11) (.const 1))) ;;
      .store (.reg 9) (.reg 7) ;;
      .store (.bin .add (.reg 9) (.const 1)) (.reg 13) ;;
      .assign 14 (.bin .add (.reg 13) (.reg 13)) ;;
      forRange 15 (.const 0) (.reg 14)
        (.store (.bin .add (.bin .add (.reg 9) (.const 2)) (.reg 15))
                (.bin .add (.load (.bin .add (.bin .add (.reg 11) (.const 2)) (.reg 15))) (.reg 12))) ;;
      .assign 9 (.bin .add (.bin .add (.reg 9) (.const 2)) (.reg 14)))
    (P := fun st =>
      st.regs 1 = start ∧ st.regs 2 = s ∧ st.regs 3 = k ∧ st.regs 4 = slots ∧
      st.regs 5 = slotWords ∧ st.regs 6 = dst ∧ st.regs 7 = gn ∧
      st.regs 8 = dataBase ∧ st.regs 9 = dataBase ∧ st.mem = mem)
    (Inv := fun c st =>
      st.regs 1 = start ∧ st.regs 2 = s ∧ st.regs 3 = k ∧ st.regs 4 = slots ∧
      st.regs 5 = slotWords ∧ st.regs 6 = dst ∧ st.regs 7 = gn ∧
      st.regs 8 = dataBase ∧ st.regs 9 = dataBase + csrPrefix row0 c ∧ st.regs 10 = c ∧
      (∀ i < c, st.mem (dst + i) = csrPrefix row0 i) ∧
      (∀ i < c, ListAt st.mem (dataBase + csrPrefix row0 i) (row0 i)) ∧
      (∀ a < dst, st.mem a = mem a) ∧ ZeroFrom st.mem (dataBase + csrPrefix row0 c))
    (50 * maxM + 95) 0 k (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      refine ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
        by simpa using h5, by simpa using h6, by simpa using h7, by simpa using h8,
        by simpa [csrPrefix_zero] using h9, by simp,
        fun _ hi => (Nat.not_lt_zero _ hi).elim,
        fun _ hi => (Nat.not_lt_zero _ hi).elim,
        fun _ _ => hm ▸ rfl,
        fun a ha => hm ▸ hZF a (by dsimp [dataBase] at ha; simp [csrPrefix_zero] at ha; omega)⟩)
    (fun _ st _ _ hi' => hi'.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi' => by simp [Expr.eval, hi'.2.2.1])
    (fun c _ hc => by
      intro st ω' ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hOffC, hRowC, hPresC, hZFC⟩
      obtain ⟨hGrC, hMC, hValidC⟩ := hSlots c hc
      set cur := dataBase + csrPrefix row0 c
      set src := slots + c * slotWords
      set off := start + c * s
      set m := (F c).length
      let rawEdges := ((F c).map Prod.fst).flatMap fun e => [e.1, e.2]
      have hRawLen : rawEdges.length = 2 * m := by
        dsimp [rawEdges, m]; rw [length_flatMap_pair, List.length_map]
      have hRowEq : row0 c = gn :: m :: rawEdges.map (· + off) := by
        dsimp [row0, rawEdges, m, off]
        rw [encode_shiftEdges_eq, List.length_map]
      have hRowLen : (row0 c).length = 2 + 2 * m := by
        rw [hRowEq]; simp [hRawLen]; omega
      have hPrefNext : csrPrefix row0 (c + 1) ≤ csrPrefix row0 k :=
        csrPrefix_le (Nat.succ_le_of_lt hc)
      have hPrefSucc : csrPrefix row0 (c + 1) = csrPrefix row0 c + (2 + 2 * m) := by
        rw [csrPrefix_succ, hRowLen]
      have hCurNextW : cur + 2 + 2 * m < 2 ^ w := by dsimp [cur, dataBase] at *; omega
      have hSrcEnd : src + 2 + 2 * m ≤ dst := by
        have h1' : (c + 1) * slotWords ≤ k * slotWords := Nat.mul_le_mul_right slotWords hc
        rw [Nat.succ_mul] at h1'; dsimp [src]; omega
      have hOffNextW : off + s ≤ start + k * s := by
        have h1' : (c + 1) * s ≤ k * s := Nat.mul_le_mul_right s hc
        rw [Nat.succ_mul] at h1'; dsimp [off]; omega
      have hSrcM : mem (src + 1) = m := by
        have hlen : 1 < (Graph.mk s ((F c).map Prod.fst)).encode.length := by simp [Graph.encode]
        simpa [Graph.encode, Graph.m, m] using hGrC 1 hlen
      have hSrcEdge : ∀ i (hi : i < 2 * m), mem (src + 2 + i) = rawEdges[i]'(hRawLen.symm ▸ hi) := by
        intro i hi
        have hEnc : (Graph.mk s ((F c).map Prod.fst)).encode = s :: m :: rawEdges := by
          simp [Graph.encode, Graph.m, m, rawEdges]
        have hlen : 2 + i < (Graph.mk s ((F c).map Prod.fst)).encode.length := by
          rw [hEnc]; simp [hRawLen]; omega
        have h1' := hGrC (2 + i) hlen
        rw [show src + (2 + i) = src + 2 + i by omega] at h1'
        have h2' : (Graph.mk s ((F c).map Prod.fst)).encode[2 + i]'hlen = rawEdges[i]'(hRawLen.symm ▸ hi) := by
          simp [hEnc, show 2 + i = i + 1 + 1 by omega]
        exact h1'.trans h2'
      refine runs_start_le ?_
      -- store offset at dst + c
      refine runs_seq_store_le (x := dst + c) (v := csrPrefix row0 c)
        (Expr.eval_add (Expr.eval_reg_of_eq h6) (Expr.eval_reg_of_eq h10) (by dsimp [dataBase] at hDBW; omega))
        (by have hsub : cur - dataBase = csrPrefix row0 c := by dsimp [cur]; omega
            rw [← hsub]; exact Expr.eval_sub (Expr.eval_reg_of_eq h9) (Expr.eval_reg_of_eq h8) (by dsimp [cur]; omega)) ?_
      -- r11 := src
      refine runs_seq_assign_le (v := src)
        (Expr.eval_add (Expr.eval_reg_of_eq h4)
          (Expr.eval_mul (Expr.eval_reg_of_eq h10) (Expr.eval_reg_of_eq h5) (by dsimp [src] at hSrcEnd; omega))
          (by dsimp [src] at hSrcEnd; omega)) ?_
      -- r12 := off
      refine runs_seq_assign_le (v := off)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h1))
          (Expr.eval_mul (Expr.eval_reg_of_eq (by simpa using h10)) (Expr.eval_reg_of_eq (by simpa using h2))
            (by dsimp [off] at hOffNextW; omega))
          (by dsimp [off] at hOffNextW; omega)) ?_
      -- r13 := m
      have hMst : Function.update st.mem (dst + c) (csrPrefix row0 c) (src + 1) = m := by
        rw [Function.update_of_ne (by omega), hPresC _ (by omega), hSrcM]
      refine runs_seq_assign_le (v := m)
        (by rw [← hMst]; exact Expr.eval_load (Expr.eval_add
              (Expr.eval_reg_of_eq (v := src) (by simp))
              (Expr.eval_const (by omega)) (by omega))) ?_
      -- mem[cur] := gn; mem[cur + 1] := m
      refine runs_seq_store_le (x := cur) (v := gn)
        (Expr.eval_reg_of_eq (by simpa using h9)) (Expr.eval_reg_of_eq (by simpa using h7)) ?_
      refine runs_seq_store_le (x := cur + 1) (v := m)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h9)) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (v := m) (by simp)) ?_
      -- r14 := 2 * m
      refine runs_seq_assign_le (v := m + m)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := m) (by simp)) (Expr.eval_reg_of_eq (v := m) (by simp))
          (by omega)) ?_
      -- inner loop copying shifted endpoints
      set mHead := Function.update (Function.update (Function.update st.mem (dst + c) (csrPrefix row0 c))
        cur gn) (cur + 1) m
      have hInner := Triple.forRange_const (w := w) (p := p) (r := 15) (lo := .const 0) (hi := .reg 14)
        (body := .store (.bin .add (.bin .add (.reg 9) (.const 2)) (.reg 15))
                        (.bin .add (.load (.bin .add (.bin .add (.reg 11) (.const 2)) (.reg 15))) (.reg 12)))
        (P := fun st' =>
          st'.regs 1 = start ∧ st'.regs 2 = s ∧ st'.regs 3 = k ∧ st'.regs 4 = slots ∧
          st'.regs 5 = slotWords ∧ st'.regs 6 = dst ∧ st'.regs 7 = gn ∧ st'.regs 8 = dataBase ∧
          st'.regs 9 = cur ∧ st'.regs 10 = c ∧ st'.regs 11 = src ∧ st'.regs 12 = off ∧
          st'.regs 14 = m + m ∧ st'.mem = mHead)
        (Inv := fun j st' =>
          st'.regs 1 = start ∧ st'.regs 2 = s ∧ st'.regs 3 = k ∧ st'.regs 4 = slots ∧
          st'.regs 5 = slotWords ∧ st'.regs 6 = dst ∧ st'.regs 7 = gn ∧ st'.regs 8 = dataBase ∧
          st'.regs 9 = cur ∧ st'.regs 10 = c ∧ st'.regs 11 = src ∧ st'.regs 12 = off ∧
          st'.regs 14 = m + m ∧ st'.regs 15 = j ∧
          (∀ i < j, ∃ hi : i < rawEdges.length, st'.mem (cur + 2 + i) = rawEdges[i]'hi + off) ∧
          (∀ a, (a < cur + 2 ∨ cur + 2 + j ≤ a) → st'.mem a = mHead a))
        16 0 (m + m) (Nat.zero_le _) (by omega) (fun _ => by omega)
        (fun st' ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, qm⟩ => by
          refine ⟨by eval_expr, ?_⟩
          refine ⟨by simpa using q1, by simpa using q2, by simpa using q3, by simpa using q4,
            by simpa using q5, by simpa using q6, by simpa using q7, by simpa using q8,
            by simpa using q9, by simpa using q10, by simpa using q11, by simpa using q12,
            by simpa using q14, by simp,
            fun _ hi => (Nat.not_lt_zero _ hi).elim, fun _ _ => qm ▸ rfl⟩)
        (fun _ st' _ _ hi' => hi'.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (fun _ st' _ _ hi' => by simp [Expr.eval, hi'.2.2.2.2.2.2.2.2.2.2.2.2.1])
        (fun j _ hj => by
          intro st' ω'' ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q14, q15, qWr, qFr⟩
          have hjRaw : j < rawEdges.length := by omega
          have hValLt : rawEdges[j]'hjRaw < s := getElem_flatMap_pair_lt hValidC hjRaw
          have hSrcJ : st'.mem (src + 2 + j) = rawEdges[j]'hjRaw := by
            rw [qFr _ (Or.inl (by dsimp [cur, dataBase]; omega))]
            dsimp only [mHead]
            rw [Function.update_of_ne (by dsimp [cur, dataBase]; omega),
              Function.update_of_ne (by dsimp [cur, dataBase]; omega),
              Function.update_of_ne (by omega), hPresC _ (by omega)]
            exact hSrcEdge j (by omega)
          refine runs_start_le ?_
          refine runs_store_le (x := cur + 2 + j) (v := rawEdges[j]'hjRaw + off)
            (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq q9) (Expr.eval_const (by omega)) (by omega))
              (Expr.eval_reg_of_eq q15) (by omega))
            (Expr.eval_add
              (by rw [← hSrcJ]; exact Expr.eval_load (Expr.eval_add
                    (Expr.eval_add (Expr.eval_reg_of_eq q11) (Expr.eval_const (by omega)) (by omega))
                    (Expr.eval_reg_of_eq q15) (by omega)))
              (Expr.eval_reg_of_eq q12) (by omega)) ?_ (by simp [Expr.size])
          refine ⟨⟨by simpa using q1, by simpa using q2, by simpa using q3, by simpa using q4,
            by simpa using q5, by simpa using q6, by simpa using q7, by simpa using q8,
            by simpa using q9, by simpa using q10, by simpa using q11, by simpa using q12,
            by simpa using q14, by simp, ?_, ?_⟩, q15⟩
          · intro i hi
            dsimp only
            by_cases hij : i = j
            · subst hij; exact ⟨hjRaw, Function.update_self _ _ _⟩
            · rw [Function.update_of_ne (by omega)]; exact qWr i (by omega)
          · intro a ha
            dsimp only
            rw [Function.update_of_ne (by omega)]
            exact qFr a (by omega))
      refine runs_seq_triple_le hInner
        ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
         by simpa using h5, by simpa using h6, by simpa using h7, by simpa using h8,
         by simpa using h9, by simpa using h10, by simp, by simp, by simp, rfl⟩ ?_
      intro st2 ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, _, _, q14, _, qWr, qFr⟩
      refine runs_assign_le (v := cur + 2 + (m + m))
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq q9) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_reg_of_eq q14) (by omega)) ?_ ?_
      · have hMemOut : ∀ a, a ≠ dst + c → (a < cur ∨ cur + 2 + 2 * m ≤ a) → st2.mem a = st.mem a := by
          intro a hne ha
          rw [qFr a (by rcases ha with h1' | h2' <;> omega)]
          dsimp only [mHead]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne hne]
        refine ⟨⟨by simpa using q1, by simpa using q2, by simpa using q3, by simpa using q4,
          by simpa using q5, by simpa using q6, by simpa using q7, by simpa using q8,
          by simp; dsimp [cur]; rw [hPrefSucc]; omega, by simp, ?_, ?_, ?_, ?_⟩, by simp [q10]⟩
        · intro i hi
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
          · rw [hMemOut _ (by omega) (Or.inl (by dsimp [cur, dataBase]; omega))]
            exact hOffC i hlt
          · rw [qFr _ (Or.inl (by dsimp [cur, dataBase]; omega))]
            dsimp only [mHead]
            rw [Function.update_of_ne (by dsimp [cur, dataBase]; omega),
              Function.update_of_ne (by dsimp [cur, dataBase]; omega),
              Function.update_self]
        · intro i hi
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
          · have hEndI : csrPrefix row0 i + (row0 i).length ≤ csrPrefix row0 c := by
              rw [← csrPrefix_succ]; exact csrPrefix_le (Nat.succ_le_of_lt hlt)
            exact WordRAM.ListAt.congr (hRowC i hlt) fun a ha hb =>
              hMemOut a (by dsimp [dataBase] at ha; omega) (Or.inl (by dsimp [cur]; omega))
          · rw [hRowEq]
            intro t ht
            match t with
            | 0 =>
              rw [Nat.add_zero]
              change st2.mem cur = _
              rw [qFr cur (Or.inl (by omega))]
              dsimp only [mHead]
              rw [Function.update_of_ne (by omega), Function.update_self]; rfl
            | 1 =>
              change st2.mem (cur + 1) = _
              rw [qFr (cur + 1) (Or.inl (by omega))]
              dsimp only [mHead]
              rw [Function.update_self]; rfl
            | idx + 2 =>
              have hidx : idx < m + m := by
                simp only [List.length_cons, List.length_map, hRawLen] at ht; omega
              obtain ⟨hiRaw, hEq⟩ := qWr idx hidx
              change st2.mem (cur + (idx + 2)) = _
              rw [show cur + (idx + 2) = cur + 2 + idx by omega, hEq]
              simp [List.getElem_map]
        · intro a ha
          exact (hMemOut a (by omega) (Or.inl (by dsimp [cur, dataBase]; omega))).trans (hPresC a ha)
        · intro a ha
          rw [hPrefSucc] at ha
          exact (hMemOut a (by dsimp [dataBase] at ha; omega) (Or.inr (by dsimp [cur]; omega))).trans
            (hZFC a (by omega))
      · simp only [Expr.size, Nat.sub_zero]
        have hnorm : 16 + 1 + 8 = 25 := by omega
        rw [hnorm]
        omega)
  refine runs_seq_triple_le hOuter
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp, by simp, by simp, rfl⟩ ?_
  intro stEnd ⟨_, _, h3, _, _, h6, _, h8, h9, _, hOffEnd, hRowEnd, hPresEnd, hZFEnd⟩
  refine runs_seq_store_le (x := dst + k) (v := csrPrefix row0 k)
    (Expr.eval_add (Expr.eval_reg_of_eq h6) (Expr.eval_reg_of_eq h3) (by dsimp [dataBase] at hDBW; omega))
    (by have hsub : dataBase + csrPrefix row0 k - dataBase = csrPrefix row0 k := by omega
        rw [← hsub]; exact Expr.eval_sub (Expr.eval_reg_of_eq h9) (Expr.eval_reg_of_eq h8) (by omega)) ?_
  refine runs_ret_le (v := dataBase + csrPrefix row0 k) (Expr.eval_reg_of_eq h9) ?_ ?_
  · refine ⟨gAddr, slots, slotWords, dst, rfl, by dsimp [Outcome.value, dataBase]; omega, ?_, ?_, ?_⟩
    · apply listAt_csrList_of_parts
      · intro i hi
        dsimp only
        rcases Nat.lt_or_eq_of_le hi with hlt | rfl
        · rw [Function.update_of_ne (by omega)]; exact hOffEnd i hlt
        · exact Function.update_self _ _ _
      · intro i hi
        exact WordRAM.ListAt.congr (hRowEnd i hi) fun a ha _ =>
          Function.update_of_ne (by omega) _ _
    · intro a ha
      dsimp only
      rw [Function.update_of_ne (by omega)]
      exact hPresEnd a ha
    · intro a ha
      dsimp only [Outcome.value] at ha ⊢
      rw [Function.update_of_ne (by dsimp [dataBase] at ha; omega)]
      exact hZFEnd a ha
  · simp only [buildSec0Contract, Expr.size, Nat.sub_zero]
    have hnorm : 50 * maxM + 95 + 1 + 8 = 50 * maxM + 104 := by omega
    rw [hnorm]
    have hle : k * (50 * maxM + 104) ≤ k * (50 * maxM + 105) := Nat.mul_le_mul_left _ (by omega)
    omega

private theorem buildSec1_inner_triple {w fCopy k walkCnt walkPtrs cap dst dataBase cur c m
    rowBase rowData d : ℕ} {p : Program} {walkF : ℕ → List ℕ} {mem m0 : ℕ → ℕ}
    (hfC : p.procs[fCopy]? = some buildCopyProc)
    (hRowData : rowData = cur + m + 1) (hCurGe : dst ≤ cur) (hRBEnd : rowBase + m ≤ dst)
    (hRowEndW : rowData + csrPrefix walkF m < 2 ^ w) (hw2 : 2 < 2 ^ w)
    (hM0Dst : ∀ a < dst, m0 a = mem a) (hZFM0 : ZeroFrom m0 rowData)
    (hPtrs : ∀ e < m,
      let ptr := mem (rowBase + e)
      ptr + 1 + (walkF e).length ≤ dst ∧ SeqAt mem ptr (walkF e) ∧ (walkF e).length ≤ d) :
    Triple w p
      (fun st =>
        st.regs 0 = k ∧ st.regs 1 = walkCnt ∧ st.regs 2 = walkPtrs ∧ st.regs 3 = cap ∧
        st.regs 4 = dst ∧ st.regs 5 = dataBase ∧ st.regs 6 = cur ∧ st.regs 7 = c ∧
        st.regs 8 = m ∧ st.regs 9 = rowBase ∧ st.regs 10 = rowData ∧ st.regs 11 = rowData ∧
        st.mem = m0)
      (forRange 12 (.const 0) (.reg 8)
        (.store (.bin .add (.reg 6) (.reg 12)) (.bin .sub (.reg 11) (.reg 10)) ;;
         .assign 13 (.load (.bin .add (.reg 9) (.reg 12))) ;;
         .assign 14 (.load (.reg 13)) ;;
         .call 15 fCopy [.bin .add (.reg 13) (.const 1), .reg 14, .reg 11] ;;
         .assign 11 (.bin .add (.reg 11) (.reg 14))))
      (normalPost fun st =>
        st.regs 0 = k ∧ st.regs 1 = walkCnt ∧ st.regs 2 = walkPtrs ∧ st.regs 3 = cap ∧
        st.regs 4 = dst ∧ st.regs 5 = dataBase ∧ st.regs 6 = cur ∧ st.regs 7 = c ∧
        st.regs 8 = m ∧ st.regs 9 = rowBase ∧ st.regs 10 = rowData ∧
        st.regs 11 = rowData + csrPrefix walkF m ∧ st.regs 12 = m ∧
        (∀ j < m, st.mem (cur + j) = csrPrefix walkF j) ∧
        (∀ j < m, ListAt st.mem (rowData + csrPrefix walkF j) (walkF j)) ∧
        (∀ a < cur, st.mem a = m0 a) ∧ ZeroFrom st.mem (rowData + csrPrefix walkF m))
      (fun _ => (m - 0) * (17 * d + 75 + (Expr.reg 8).size + 8) +
        ((Expr.const 0).size + (Expr.reg 8).size + 5)) := by
  refine Triple.forRange_const (w := w) (p := p) (r := 12) (lo := .const 0) (hi := .reg 8)
    (Inv := fun e st' =>
      st'.regs 0 = k ∧ st'.regs 1 = walkCnt ∧ st'.regs 2 = walkPtrs ∧ st'.regs 3 = cap ∧
      st'.regs 4 = dst ∧ st'.regs 5 = dataBase ∧ st'.regs 6 = cur ∧ st'.regs 7 = c ∧
      st'.regs 8 = m ∧ st'.regs 9 = rowBase ∧ st'.regs 10 = rowData ∧
      st'.regs 11 = rowData + csrPrefix walkF e ∧ st'.regs 12 = e ∧
      (∀ j < e, st'.mem (cur + j) = csrPrefix walkF j) ∧
      (∀ j < e, ListAt st'.mem (rowData + csrPrefix walkF j) (walkF j)) ∧
      (∀ a < cur, st'.mem a = m0 a) ∧ ZeroFrom st'.mem (rowData + csrPrefix walkF e))
    (17 * d + 75) 0 m (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st' ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, qm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      refine ⟨by simpa using q0, by simpa using q1, by simpa using q2, by simpa using q3,
        by simpa using q4, by simpa using q5, by simpa using q6, by simpa using q7,
        by simpa using q8, by simpa using q9, by simpa using q10,
        by simpa [csrPrefix_zero] using q11, by simp,
        fun _ hj => (Nat.not_lt_zero _ hj).elim,
        fun _ hj => (Nat.not_lt_zero _ hj).elim,
        fun _ _ => qm ▸ rfl,
        fun a ha => by rw [qm]; exact hZFM0 a (by simp [csrPrefix_zero] at ha; omega)⟩)
    (fun _ st' _ _ hi' => hi'.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st' _ _ hi' => by simp [Expr.eval, hi'.2.2.2.2.2.2.2.2.1])
    (fun e _ he => by
      intro st' ω'' ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, qOff, qRow, qPres, qZF⟩
      obtain ⟨hPtrEnd, hSeqAt, hLenD⟩ := hPtrs e he
      set ptr := mem (rowBase + e)
      set len := (walkF e).length
      have hPtrLen : mem ptr = len := hSeqAt.1
      have hPtrWord : ∀ j (hj : j < len), mem (ptr + 1 + j) = (walkF e)[j]'hj := fun j hj => by
        simpa [Nat.add_assoc] using hSeqAt.2 j hj
      have hPrefE : csrPrefix walkF (e + 1) ≤ csrPrefix walkF m := csrPrefix_le (Nat.succ_le_of_lt he)
      have hPrefESucc : csrPrefix walkF (e + 1) = csrPrefix walkF e + len := csrPrefix_succ walkF e
      set rcur := rowData + csrPrefix walkF e
      refine runs_start_le ?_
      refine runs_seq_store_le (x := cur + e) (v := csrPrefix walkF e)
        (Expr.eval_add (Expr.eval_reg_of_eq q6) (Expr.eval_reg_of_eq q12) (by omega))
        (by have hsub : rcur - rowData = csrPrefix walkF e := by dsimp [rcur]; omega
            rw [← hsub]; exact Expr.eval_sub (Expr.eval_reg_of_eq q11) (Expr.eval_reg_of_eq q10)
              (by dsimp [rcur]; omega)) ?_
      set m1 := Function.update st'.mem (cur + e) (csrPrefix walkF e)
      have hm1Dst : ∀ a < dst, m1 a = mem a := fun a ha => by
        dsimp only [m1]
        rw [Function.update_of_ne (by omega), qPres a (by omega), hM0Dst a ha]
      have hm1Ptr : m1 (rowBase + e) = ptr := hm1Dst _ (by omega)
      refine runs_seq_assign_le (v := ptr)
        (by rw [← hm1Ptr]; exact Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq q9)
              (Expr.eval_reg_of_eq q12) (by omega))) ?_
      have hm1Len : m1 ptr = len := (hm1Dst ptr (by omega)).trans hPtrLen
      refine runs_seq_assign_le (v := len)
        (by rw [← hm1Len]; exact Expr.eval_load (Expr.eval_reg_of_eq (v := ptr) (by simp))) ?_
      have hCopySpec := buildCopyProc_meetsContract (w := w) hfC
      have hCopyPre : (buildCopyContract w).pre [ptr + 1, len, rcur] m1 :=
        ⟨ptr + 1, len, rcur, rfl, by dsimp [rcur]; omega, by dsimp [rcur]; omega, by omega⟩
      refine runs_seq_call_le hCopySpec (vs := [ptr + 1, len, rcur])
        (by unfold evalArgs
            rw [Expr.eval_add (Expr.eval_reg_of_eq (v := ptr) (by simp))
                  (Expr.eval_const (by omega)) (by omega)]
            simp [evalArgs, Expr.eval, q11])
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl
            · omega
            · omega
            · dsimp [rcur]; omega)
        hCopyPre ?_
      intro _ mNext _ hPostC
      obtain ⟨_, _, _, heqC, hCopied, hFrCopy⟩ := hPostC
      simp only [List.cons.injEq, and_true] at heqC
      obtain ⟨rfl, rfl, rfl⟩ := heqC
      refine runs_assign_le (v := rcur + len)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using q11))
          (Expr.eval_reg_of_eq (v := len) (by simp)) (by dsimp [rcur]; omega)) ?_ ?_
      · have hOffNext : ∀ j < e + 1, mNext (cur + j) = csrPrefix walkF j := by
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heqJ
          · rw [hFrCopy _ (Or.inl (by dsimp [rcur]; omega))]
            dsimp only [m1]; rw [Function.update_of_ne (by omega)]; exact qOff j hlt
          · subst heqJ
            rw [hFrCopy _ (Or.inl (by dsimp [rcur]; omega))]
            dsimp only [m1]; exact Function.update_self _ _ _
        have hRowNext : ∀ j < e + 1, ListAt mNext (rowData + csrPrefix walkF j) (walkF j) := by
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heqJ
          · have hEndJ : csrPrefix walkF j + (walkF j).length ≤ csrPrefix walkF e := by
              rw [← csrPrefix_succ]; exact csrPrefix_le (Nat.succ_le_of_lt hlt)
            exact WordRAM.ListAt.congr (qRow j hlt) fun a ha hb => by
              rw [hFrCopy a (Or.inl (by dsimp [rcur]; omega))]
              dsimp only [m1]; exact Function.update_of_ne (by omega) _ _
          · subst heqJ
            intro j' hj'
            rw [hCopied j' hj']
            exact (hm1Dst _ (by omega)).trans (hPtrWord j' hj')
        have hPresNext : ∀ a < cur, mNext a = m0 a := fun a ha => by
          rw [hFrCopy a (Or.inl (by dsimp [rcur]; omega))]
          dsimp only [m1]; rw [Function.update_of_ne (by omega)]; exact qPres a ha
        have hZFNext : ZeroFrom mNext (rowData + csrPrefix walkF (e + 1)) := fun a ha => by
          rw [hPrefESucc] at ha
          rw [hFrCopy a (Or.inr (by dsimp [rcur]; omega))]
          dsimp only [m1]; rw [Function.update_of_ne (by omega)]; exact qZF a (by omega)
        refine ⟨⟨by simpa using q0, by simpa using q1, by simpa using q2, by simpa using q3,
          by simpa using q4, by simpa using q5, by simpa using q6, by simpa using q7,
          by simpa using q8, by simpa using q9, by simpa using q10,
          by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self, hPrefESucc]; dsimp [rcur]; omega,
          by simp, hOffNext, hRowNext, hPresNext, hZFNext⟩, by simp [q12]⟩
      · simp only [buildCopyContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size, argsSize]
        omega)

/-- `buildSec1Proc` meets `buildSec1Contract`. -/
theorem buildSec1Proc_meetsContract {w f fCopy k d maxM : ℕ}
    {F : ℕ → List ((ℕ × ℕ) × List ℕ)} {p : Program}
    (hf : p.procs[f]? = some (buildSec1Proc fCopy))
    (hfC : p.procs[fCopy]? = some buildCopyProc) :
    MeetsContract w p f (buildSec1Contract w k d maxM F) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨walkCnt, walkPtrs, cap, dst, rfl, hWT, hPtrLe, hFbound, hZF, htop, hw2⟩ := hPre
  have hWT1 : walkCnt + k ≤ walkPtrs := hWT.1
  let row1 : ℕ → List ℕ := fun c => csrList (F c).length fun e => ((F c).getD e ((0, 0), [])).2
  have hSecLen : (sec1Words k F).length = k + 1 + csrPrefix row1 k := length_csrList_eq k row1
  let dataBase := dst + k + 1
  have hDBW : dataBase < 2 ^ w := by dsimp [dataBase]; omega
  refine runs_start_le ?_
  unfold buildSec1Proc
  refine runs_seq_assign_le (v := dataBase)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_reg_of_eq (by simp [startState])) (by dsimp [dataBase] at hDBW; omega))
      (Expr.eval_const (by omega)) hDBW) ?_
  refine runs_seq_assign_le (v := dataBase) (Expr.eval_reg_of_eq (by simp)) ?_
  have hOuter := Triple.forRange_const (w := w) (p := p) (r := 7) (lo := .const 0) (hi := .reg 0)
    (body :=
      .store (.bin .add (.reg 4) (.reg 7)) (.bin .sub (.reg 6) (.reg 5)) ;;
      .assign 8 (.load (.bin .add (.reg 1) (.reg 7))) ;;
      .assign 9 (.bin .add (.reg 2) (.bin .mul (.reg 7) (.reg 3))) ;;
      .assign 10 (.bin .add (.bin .add (.reg 6) (.reg 8)) (.const 1)) ;;
      .assign 11 (.reg 10) ;;
      forRange 12 (.const 0) (.reg 8)
        (.store (.bin .add (.reg 6) (.reg 12)) (.bin .sub (.reg 11) (.reg 10)) ;;
         .assign 13 (.load (.bin .add (.reg 9) (.reg 12))) ;;
         .assign 14 (.load (.reg 13)) ;;
         .call 15 fCopy [.bin .add (.reg 13) (.const 1), .reg 14, .reg 11] ;;
         .assign 11 (.bin .add (.reg 11) (.reg 14))) ;;
      .store (.bin .add (.reg 6) (.reg 8)) (.bin .sub (.reg 11) (.reg 10)) ;;
      .assign 6 (.reg 11))
    (P := fun st =>
      st.regs 0 = k ∧ st.regs 1 = walkCnt ∧ st.regs 2 = walkPtrs ∧ st.regs 3 = cap ∧
      st.regs 4 = dst ∧ st.regs 5 = dataBase ∧ st.regs 6 = dataBase ∧ st.mem = mem)
    (Inv := fun c st =>
      st.regs 0 = k ∧ st.regs 1 = walkCnt ∧ st.regs 2 = walkPtrs ∧ st.regs 3 = cap ∧
      st.regs 4 = dst ∧ st.regs 5 = dataBase ∧ st.regs 6 = dataBase + csrPrefix row1 c ∧
      st.regs 7 = c ∧
      (∀ i < c, st.mem (dst + i) = csrPrefix row1 i) ∧
      (∀ i < c, ListAt st.mem (dataBase + csrPrefix row1 i) (row1 i)) ∧
      (∀ a < dst, st.mem a = mem a) ∧ ZeroFrom st.mem (dataBase + csrPrefix row1 c))
    (maxM * (17 * d + 85) + 105) 0 k (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, h4, h5, h6, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      refine ⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
        by simpa using h4, by simpa using h5, by simpa [csrPrefix_zero] using h6, by simp,
        fun _ hi => (Nat.not_lt_zero _ hi).elim,
        fun _ hi => (Nat.not_lt_zero _ hi).elim,
        fun _ _ => hm ▸ rfl,
        fun a ha => hm ▸ hZF a (by dsimp [dataBase] at ha; simp [csrPrefix_zero] at ha; omega)⟩)
    (fun _ st _ _ hi' => hi'.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi' => by simp [Expr.eval, hi'.1])
    (fun c _ hc => by
      intro st ω' ⟨h0, h1, h2, h3, h4, h5, h6, h7, hOffC, hRowC, hPresC, hZFC⟩
      obtain ⟨hCapC, hCntC, hPtrsC⟩ := hWT.2 c hc
      obtain ⟨hMC, hDC⟩ := hFbound c hc
      set cur := dataBase + csrPrefix row1 c
      set m := (F c).length
      set rowBase := walkPtrs + c * cap
      let walkF : ℕ → List ℕ := fun e => ((F c).getD e ((0, 0), [])).2
      have hRowLen : (row1 c).length = m + 1 + csrPrefix walkF m := length_csrList_eq m walkF
      have hPrefNext : csrPrefix row1 (c + 1) ≤ csrPrefix row1 k :=
        csrPrefix_le (Nat.succ_le_of_lt hc)
      have hPrefSucc : csrPrefix row1 (c + 1) = csrPrefix row1 c + (m + 1 + csrPrefix walkF m) := by
        rw [csrPrefix_succ, hRowLen]
      set rowData := cur + m + 1
      have hRowEndW : rowData + csrPrefix walkF m < 2 ^ w := by
        dsimp [rowData, cur, dataBase] at *; omega
      have hRBEnd : rowBase + m ≤ dst := by
        have h1' : (c + 1) * cap ≤ k * cap := Nat.mul_le_mul_right cap hc
        rw [Nat.succ_mul] at h1'; rw [List.length_map] at hCapC; dsimp [rowBase, m]; omega
      refine runs_start_le ?_
      -- mem[dst + c] := cur - dataBase
      refine runs_seq_store_le (x := dst + c) (v := csrPrefix row1 c)
        (Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_reg_of_eq h7) (by dsimp [dataBase] at hDBW; omega))
        (by have hsub : cur - dataBase = csrPrefix row1 c := by dsimp [cur]; omega
            rw [← hsub]; exact Expr.eval_sub (Expr.eval_reg_of_eq h6) (Expr.eval_reg_of_eq h5) (by dsimp [cur]; omega)) ?_
      -- r8 := m
      have hMst : Function.update st.mem (dst + c) (csrPrefix row1 c) (walkCnt + c) = m := by
        rw [Function.update_of_ne (by omega), hPresC _ (by omega), hCntC, List.length_map]
      refine runs_seq_assign_le (v := m)
        (by rw [← hMst]; exact Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq h1)
              (Expr.eval_reg_of_eq h7) (by omega))) ?_
      -- r9 := rowBase
      refine runs_seq_assign_le (v := rowBase)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h2))
          (Expr.eval_mul (Expr.eval_reg_of_eq (by simpa using h7)) (Expr.eval_reg_of_eq (by simpa using h3))
            (by dsimp [rowBase] at hRBEnd; omega))
          (by dsimp [rowBase] at hRBEnd; omega)) ?_
      -- r10 := rowData; r11 := rowData
      refine runs_seq_assign_le (v := rowData)
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using h6))
          (Expr.eval_reg_of_eq (v := m) (by simp)) (by dsimp [rowData] at hRowEndW; omega))
          (Expr.eval_const (by omega)) (by dsimp [rowData] at hRowEndW; omega)) ?_
      refine runs_seq_assign_le (v := rowData) (Expr.eval_reg_of_eq (v := rowData) (by simp)) ?_
      set m0 := Function.update st.mem (dst + c) (csrPrefix row1 c)
      have hInner := buildSec1_inner_triple (k := k) (walkCnt := walkCnt) (walkPtrs := walkPtrs)
        (cap := cap) (dst := dst) (dataBase := dataBase) (cur := cur) (c := c) (m := m)
        (rowBase := rowBase) (rowData := rowData) (d := d) (walkF := walkF) (mem := mem) (m0 := m0)
        hfC rfl (by dsimp [cur, dataBase]; omega) hRBEnd hRowEndW hw2
        (fun a ha => by
          dsimp only [m0]; rw [Function.update_of_ne (by omega)]; exact hPresC a ha)
        (fun a ha => by
          dsimp only [m0]
          rw [Function.update_of_ne (by dsimp [rowData, cur, dataBase] at ha; omega)]
          exact hZFC a (by dsimp [rowData, cur] at ha; omega))
        (fun e he => by
          have heMap : e < ((F c).map Prod.snd).length := by rw [List.length_map]; exact he
          obtain ⟨hPtrEnd, hSeqAt⟩ := hPtrsC e heMap
          have hGetW : ((F c).map Prod.snd).getD e [] = walkF e := by
            dsimp [walkF]
            rw [List.getD_eq_getElem _ _ heMap, List.getD_eq_getElem _ _ he, List.getElem_map]
          rw [hGetW] at hPtrEnd hSeqAt
          exact ⟨by omega, hSeqAt, hDC e he⟩)
      refine runs_seq_triple_le hInner
        ⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
         by simpa using h4, by simpa using h5, by simpa using h6, by simpa using h7,
         by simp, by simp, by simp, by simp, rfl⟩ ?_
      intro st2 ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, _, q10, q11, _, qOff, qRow, qPres, qZF⟩
      -- mem[cur + m] := csrPrefix walkF m
      refine runs_seq_store_le (x := cur + m) (v := csrPrefix walkF m)
        (Expr.eval_add (Expr.eval_reg_of_eq q6) (Expr.eval_reg_of_eq q8) (by dsimp [rowData] at hRowEndW; omega))
        (by have hsub : rowData + csrPrefix walkF m - rowData = csrPrefix walkF m := by omega
            rw [← hsub]; exact Expr.eval_sub (Expr.eval_reg_of_eq q11) (Expr.eval_reg_of_eq q10) (by omega)) ?_
      -- r6 := r11
      refine runs_assign_le (v := rowData + csrPrefix walkF m) (Expr.eval_reg_of_eq q11) ?_ ?_
      · refine ⟨⟨by simpa using q0, by simpa using q1, by simpa using q2, by simpa using q3,
          by simpa using q4, by simpa using q5,
          by simp; dsimp [rowData, cur]; rw [hPrefSucc]; omega, by simp, ?_, ?_, ?_, ?_⟩,
          by simp [q7]⟩
        · intro i hi
          dsimp only
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
          · rw [Function.update_of_ne (by dsimp [cur, dataBase]; omega),
              qPres _ (by dsimp [cur, dataBase]; omega)]
            dsimp only [m0]
            rw [Function.update_of_ne (by omega)]
            exact hOffC i hlt
          · rw [Function.update_of_ne (by dsimp [cur, dataBase]; omega),
              qPres _ (by dsimp [cur, dataBase]; omega)]
            dsimp only [m0]; exact Function.update_self _ _ _
        · intro i hi
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
          · have hEndI : csrPrefix row1 i + (row1 i).length ≤ csrPrefix row1 c := by
              rw [← csrPrefix_succ]; exact csrPrefix_le (Nat.succ_le_of_lt hlt)
            exact WordRAM.ListAt.congr (hRowC i hlt) fun a ha hb => by
              dsimp only
              rw [Function.update_of_ne (by dsimp [cur]; omega), qPres a (by dsimp [cur]; omega)]
              dsimp only [m0]
              exact Function.update_of_ne (by dsimp [dataBase] at ha; omega) _ _
          · apply listAt_csrList_of_parts
            · intro j hj
              dsimp only
              change Function.update st2.mem (cur + m) (csrPrefix walkF m) (cur + j) = _
              rcases Nat.lt_or_eq_of_le hj with hlt | rfl
              · rw [Function.update_of_ne (by omega)]; exact qOff j hlt
              · exact Function.update_self _ _ _
            · intro j hj
              exact WordRAM.ListAt.congr (qRow j hj) fun a ha _ =>
                Function.update_of_ne (by omega) _ _
        · intro a ha
          dsimp only
          rw [Function.update_of_ne (by dsimp [cur, dataBase]; omega),
            qPres a (by dsimp [cur, dataBase]; omega)]
          dsimp only [m0]
          rw [Function.update_of_ne (by omega)]
          exact hPresC a ha
        · intro a ha
          dsimp only
          rw [hPrefSucc] at ha
          rw [Function.update_of_ne (by dsimp [cur]; omega)]
          exact qZF a (by dsimp [rowData, cur]; omega)
      · simp only [Expr.size, Nat.sub_zero]
        have hnorm : 17 * d + 75 + 1 + 8 = 17 * d + 84 := by omega
        rw [hnorm]
        have hmul : m * (17 * d + 84) ≤ maxM * (17 * d + 84) := Nat.mul_le_mul_right _ hMC
        have hmul2 : maxM * (17 * d + 84) ≤ maxM * (17 * d + 85) := Nat.mul_le_mul_left _ (by omega)
        omega)
  refine runs_seq_triple_le hOuter
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp, by simp, rfl⟩ ?_
  intro stEnd ⟨h0, _, _, _, h4, h5, h6, _, hOffEnd, hRowEnd, hPresEnd, hZFEnd⟩
  refine runs_seq_store_le (x := dst + k) (v := csrPrefix row1 k)
    (Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_reg_of_eq h0) (by dsimp [dataBase] at hDBW; omega))
    (by have hsub : dataBase + csrPrefix row1 k - dataBase = csrPrefix row1 k := by omega
        rw [← hsub]; exact Expr.eval_sub (Expr.eval_reg_of_eq h6) (Expr.eval_reg_of_eq h5) (by omega)) ?_
  refine runs_ret_le (v := dataBase + csrPrefix row1 k) (Expr.eval_reg_of_eq h6) ?_ ?_
  · refine ⟨walkCnt, walkPtrs, cap, dst, rfl, by dsimp [Outcome.value, dataBase]; omega, ?_, ?_, ?_⟩
    · apply listAt_csrList_of_parts
      · intro i hi
        dsimp only
        rcases Nat.lt_or_eq_of_le hi with hlt | rfl
        · rw [Function.update_of_ne (by omega)]; exact hOffEnd i hlt
        · exact Function.update_self _ _ _
      · intro i hi
        exact WordRAM.ListAt.congr (hRowEnd i hi) fun a ha _ =>
          Function.update_of_ne (by omega) _ _
    · intro a ha
      dsimp only
      rw [Function.update_of_ne (by omega)]
      exact hPresEnd a ha
    · intro a ha
      dsimp only [Outcome.value] at ha ⊢
      rw [Function.update_of_ne (by dsimp [dataBase] at ha; omega)]
      exact hZFEnd a ha
  · simp only [buildSec1Contract, Expr.size, Nat.sub_zero]
    have hnorm : maxM * (17 * d + 85) + 105 + 1 + 8 = maxM * (17 * d + 85) + 114 := by omega
    rw [hnorm]
    have hle : k * (maxM * (17 * d + 85) + 114) ≤ k * (maxM * (17 * d + 85) + 115) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

end MinCostFlow.HierPaths
