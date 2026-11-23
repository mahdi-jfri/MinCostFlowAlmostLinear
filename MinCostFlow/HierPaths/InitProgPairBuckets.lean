module

public import MinCostFlow.HierPaths.InitProgBucketMove
public import MinCostFlow.HierPaths.InitProgConnWriter
public import MinCostFlow.LowStretch.ProgChildIota

/-!
# Writing the connectors of each pair

The pair-number column gives one key per connector, and the payload is its
connector number. Bucketing these records produces section 8.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.LowStretch

/-- Each connector is keyed by its pair number. -/
def initPairRecords (S : StaticData) : List (ℕ × ℕ) :=
  (List.range S.numConn).map fun i =>
    (pairNum S.x S.b ((connRecs S.H S.x S.b).getD i default), i)

theorem initPairRecords_length (S : StaticData) : (initPairRecords S).length = S.numConn := by
  simp [initPairRecords]

theorem initPairRecords_keys (S : StaticData) : (initPairRecords S).map Prod.fst = initEndpointWords S 2 := by
  rw [initEndpointWords_pairs_eq_map]
  apply List.ext_getElem (by simp [initPairRecords, StaticData.numConn])
  intro i hi _
  have hi' : i < S.numConn := by simpa only [List.length_map, initPairRecords_length] using hi
  simp [initPairRecords, List.getElem?_eq_getElem (show i < (connRecs S.H S.x S.b).length from hi')]

theorem initPairRecords_vals (S : StaticData) : (initPairRecords S).map Prod.snd = List.range S.numConn := by
  simp [initPairRecords, List.map_map, Function.comp_def]

theorem initPairRecords_key_lt (S : StaticData) {i : ℕ} (hi : i < (initPairRecords S).length) :
    initBucketKey (initPairRecords S) i < numPairsOf S.x S.b := by
  rw [initPairRecords_length] at hi
  unfold initBucketKey initPairRecords
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  exact pairNum_lt (getD_mem_connRecs hi)

/-- The buckets of the pair records are precisely the model's pair arrays. -/
theorem initPairRecords_buckets (S : StaticData) (k : ℕ) :
    buckets (initPairRecords S) k = (staticArrays S.H S.x S.b S.owner S.label).pairConns k := by
  simp [buckets, initPairRecords, List.filter_map, List.map_map, Function.comp_def, staticArrays,
    StaticData.numConn]

/-- The compressed pair lists written in section 8. -/
def initPairSection (S : StaticData) : List ℕ :=
  csrList (numPairsOf S.x S.b) (buckets (initPairRecords S))

theorem initPairSection_length (S : StaticData) :
    (initPairSection S).length = numPairsOf S.x S.b + 1 + S.numConn := by
  rw [initPairSection, csrList, List.length_append, length_csrOffsets,
    initBucket_data_length _ _ (fun _ hi => initPairRecords_key_lt S hi), initPairRecords_length]

theorem initPairSection_eq (S : StaticData) (a : ℕ) (s : PathDSAbsState) :
    (initConcrete S a s).sections.getD 8 [] = initPairSection S := by
  change csrList (numPairsOf S.x S.b) (staticArrays S.H S.x S.b S.owner S.label).pairConns = _
  unfold initPairSection
  congr 1
  funext k
  exact (initPairRecords_buckets S k).symm

/-- Produce the keys, produce consecutive payloads, and bucket them into the destination. -/
def initPairBucketWriter (endpoint iota finish : ℕ) : Stmt :=
  .call 7 endpoint secArgs ;;
  .assign 8 (.bin .sub (.reg 7) (.reg 6)) ;;
  .assign 9 numPairsExpr ;;
  .call 10 iota [.reg 8, .reg 7, .const 1, .const 0] ;;
  .call 11 finish [.reg 6, .reg 7, .reg 8, .reg 9, .bin .add (.reg 7) (.reg 8), .reg 6] ;;
  .ret (.reg 11)

theorem initPairBucketWriter_noRand (endpoint iota finish : ℕ) :
    (initPairBucketWriter endpoint iota finish).NoRand := by
  simp [initPairBucketWriter, Stmt.NoRand]

/-- Space for keys, payloads, and the counting-sort arrays above the final section. -/
def initPairBucketScratch (S : StaticData) : ℕ :=
  3 * S.numConn + 2 * numPairsOf S.x S.b + 2

def initPairBucketCost (S : StaticData) : ℕ :=
  initEndpointSectionCost S + 420 * (S.numConn + numPairsOf S.x S.b + 1)

private theorem initEndpointWords_pair_length (S : StaticData) :
    (initEndpointWords S 2).length = S.numConn := by
  rw [initEndpointWords_pairs_eq_map, List.length_map]
  rfl

theorem initPairBucketWriter_meetsContract {w a f endpoint iota finish : ℕ}
    {S : StaticData} {G : Graph} {p : Program}
    (hp : p.procs[f]? = some (initPairBucketWriter endpoint iota finish))
    (hEndpoint : MeetsContract w p endpoint (SecContract w (buildInv w S a G)
      ⟨endpoint, fun _ => initEndpointWords S 2, fun _ => initEndpointSectionCost S, fun _ => 0⟩))
    (hIota : p.HasAt iota [iotaP])
    (hFinish : MeetsContract w p finish
      (initBucketMoveContract w (numPairsOf S.x S.b) (initPairRecords S))) :
    MeetsContract w p f (SecContract w (buildInv w S a G)
      ⟨f, fun _ => initPairSection S, fun _ => initPairBucketCost S, fun _ => initPairBucketScratch S⟩) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, dst, rfl, hbl, hinv, hzero, hdst, hroom⟩ := hpre
  have ⟨h', hh', hx, hb, hh8, hxw, hb0, hkw⟩ := header_facts hinv hw
  obtain ⟨gAddr, phiNum, phiDen, M, h, h₁, hbase, hS, hlen, hG, hgh, hnum, hden, hgood, hbw⟩ := hinv
  have hI : buildInv w S a G base mem :=
    ⟨gAddr, phiNum, phiDen, M, h, h₁, hbase, hS, hlen, hG, hgh, hnum, hden, hgood, hbw⟩
  subst base
  change h = h' at hh'
  subst h'
  let base : List ℕ := [gAddr, phiNum, phiDen, M, h, h₁]
  let n := S.numConn
  let k := numPairsOf S.x S.b
  let keysEnd := dst + n
  let tmp := keysEnd + n
  let rs := initPairRecords S
  have hnl : rs.length = n := initPairRecords_length S
  have hroom' : dst + (k + 1 + n) + (3 * n + 2 * k + 2) < 2 ^ w := by
    simpa only [initPairSection_length, initPairBucketScratch] using hroom
  have h1 : 1 < 2 ^ w := by omega
  have hn : n < 2 ^ w := by omega
  have hk : k < 2 ^ w := hkw
  have hke : keysEnd < 2 ^ w := by dsimp [keysEnd]; omega
  have htmp : tmp < 2 ^ w := by dsimp [tmp, keysEnd]; omega
  have hbwidth : dst + (initEndpointWords S 2).length + 0 < 2 ^ w := by
    rw [initEndpointWords_pair_length]
    exact hke
  refine runs_start_le ?_
  unfold initPairBucketWriter
  refine runs_seq_call_le hEndpoint (vs := base ++ [dst]) rfl hw
    ⟨base, dst, rfl, hbl, hI, hzero, hdst, hbwidth⟩ ?_
  intro r mem₁ pos₁ hp₁
  obtain ⟨base', dst', ha, hr, hkeys, hzero₁, hf₁⟩ := hp₁
  have hd' : dst' = dst := List.singleton_inj.mp (List.append_inj_right' ha.symm rfl)
  subst dst'
  rw [initEndpointWords_pair_length] at hr
  subst r
  have hex : keysEnd - dst = n := Nat.add_sub_cancel_left _ _
  refine runs_seq_assign_le (v := n) (Expr.eval_eq_of_eq
    (Expr.eval_sub (Expr.eval_reg_of_eq (v := keysEnd) rfl)
      (Expr.eval_reg_of_eq (v := dst) rfl) hke) hex) ?_
  refine runs_seq_assign_le (v := k) (eval_numPairsExpr (h := h) rfl
    ((hf₁ _ (by change h₁ + 25 ≤ dst at hdst; omega)).trans hx)
    ((hf₁ _ (by change h₁ + 25 ≤ dst at hdst; omega)).trans hb)
    hh8 hxw hb0 hkw) ?_
  refine runs_seq_call_le (iotaP_spec (w := w) hIota)
    (vs := [n, keysEnd, 1, 0]) (by simp [evalArgs, Expr.eval, h1, keysEnd, n]) ?_
    ⟨n, keysEnd, 1, 0, rfl, by dsimp [keysEnd]; omega, by simpa using hn⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hn
    · exact hke
    · exact h1
    · exact Nat.two_pow_pos _
  intro v mem₂ pos₂ hp₂
  obtain ⟨hwords, hf₂⟩ := hp₂ n keysEnd 1 0 rfl
  have hKey : ListAt mem₂ dst (rs.map Prod.fst) := by
    rw [initPairRecords_keys]
    exact listAt_congr (fun i hi => (hf₂ _ (.inl (by rw [initEndpointWords_pair_length] at hi; omega))).symm)
      hkeys
  have hVal : ListAt mem₂ keysEnd (rs.map Prod.snd) := by
    rw [initPairRecords_vals]
    intro i hi
    simpa using hwords i (by simpa using hi)
  refine runs_seq_call_le hFinish (vs := [dst, keysEnd, n, k, tmp, dst]) ?_ ?_ ?_ ?_
  · have ht : dst + n + n < 2 ^ w := htmp
    simp [evalArgs, Expr.eval, startState, BinOp.eval, tmp, keysEnd, n] at ht ⊢
    simp [ht]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · exact hke
    · exact hn
    · exact hk
    · exact htmp
    · omega
  · refine ⟨dst, keysEnd, tmp, dst, by rw [initPairRecords_length], ⟨dst, keysEnd, tmp, by rw [initPairRecords_length], hKey, hVal, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · change _ + rs.length ≤ _
      rw [hnl]
      dsimp [tmp, keysEnd]; omega
    · change _ + rs.length ≤ _
      rw [hnl]
    · exact fun _ hi => initPairRecords_key_lt S hi
    · change tmp + (k + 1) + rs.length + k + rs.length + k + 2 < 2 ^ w
      rw [hnl]
      dsimp [tmp, keysEnd]; omega
    · dsimp [tmp, keysEnd]; omega
    · intro y hy
      exact (hf₂ _ (.inr (by dsimp [tmp, n] at *; omega))).trans (hzero₁ _ (by omega))
  intro r mem₃ pos₃ hp₃
  obtain ⟨dst', keysEnd', tmp', dst'', ha, hr, hres, hz, hf₃⟩ := hp₃
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, _, hd⟩ := ha
  subst dst''
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨base, dst, rfl, ?_, hres, hz, ?_⟩ ?_
  · change r = dst + (initPairSection S).length
    rw [initPairSection_length]
    simpa [initPairRecords_length, Nat.add_assoc] using hr
  · intro y hy
    exact (hf₃ y hy).trans ((hf₂ y (.inl (by dsimp [keysEnd]; omega))).trans (hf₁ y hy))
  · have hdist : tmp - dst = 2 * n := by dsimp [tmp, keysEnd]; omega
    simp [initPairBucketCost, initBucketMoveContract, iotaC, SecContract,
      numPairsExpr, depthExpr, secArgs, Expr.size, argsSize, initPairRecords_length, hdist]
    omega


/-- The helpers of the pair-section writer, using their final procedure indices. -/
def initPairBucketHelpers (k : ℕ) : List Stmt :=
  [initEndpointWriter 2 (k + 8), iotaP, initBucketMove (k + 3) (k + 4) (k + 5),
    initBucket (k + 6) (k + 7), initFillWord, moveDown, csrB, initBucketGather] ++
    endpointHelpers (k + 8)

/-- The section 8 writer. -/
def pairBucketW (a : ℕ) : SecW a where
  body k := initPairBucketWriter k (k + 1) (k + 2)
  helpers := initPairBucketHelpers
  l S _ _ := initPairSection S
  cost S _ _ := initPairBucketCost S
  scratch S _ _ := initPairBucketScratch S
  noRand k := ⟨initPairBucketWriter_noRand _ _ _, by
    simp [initPairBucketHelpers, endpointHelpers, initEndpointWriter, Stmt.NoRand,
      iotaP_noRand, initBucketMove_noRand, initBucket_noRand, initBucketGather_noRand,
      initFillWord_noRand, moveDown, forRange, forUp, csrB_noRand,
      initEndpointDepth_noRand, initEndpointLevel_noRand, initEndpointChild_noRand,
      initEndpointRange_noRand, initEndpointRow_noRand, initCSRSeek_noRand,
      initCSRCount_noRand, initEndpointCopy_noRand]⟩
  spec w p f k hp hh S G := by
    have hEndpoint : p.procs[k]? = some (initEndpointWriter 2 (k + 8)) := by
      simpa [initPairBucketHelpers] using hh 0 (by simp [initPairBucketHelpers])
    have hIota : p.HasAt (k + 1) [iotaP] := by
      intro i hi
      have : i = 0 := by simp at hi; omega
      subst i
      simpa [initPairBucketHelpers] using hh 1 (by simp [initPairBucketHelpers])
    have hSort : p.HasAt (k + 6) [csrB] := by
      intro i hi
      have : i = 0 := by simp at hi; omega
      subst i
      simpa [initPairBucketHelpers] using hh 6 (by simp [initPairBucketHelpers])
    have hFinish := hh 2 (by simp [initPairBucketHelpers])
    have hBucket := hh 3 (by simp [initPairBucketHelpers])
    have hClear := hh 4 (by simp [initPairBucketHelpers])
    have hMove := hh 5 (by simp [initPairBucketHelpers])
    have hGather := hh 7 (by simp [initPairBucketHelpers])
    refine initPairBucketWriter_meetsContract hp ?_ hIota
      (initBucketMove_meetsContract hFinish
        (initBucket_meetsContract hBucket hSort hGather)
        (initFillWord_meetsContract hClear) (moveDown_meetsContract hMove))
    exact initEndpointWriter_meetsContract (by decide) hEndpoint
      (hh 8 (by simp [initPairBucketHelpers, endpointHelpers]))
      (hh 9 (by simp [initPairBucketHelpers, endpointHelpers]))
      (hh 10 (by simp [initPairBucketHelpers, endpointHelpers]))
      (hh 11 (by simp [initPairBucketHelpers, endpointHelpers]))
      (hh 12 (by simp [initPairBucketHelpers, endpointHelpers]))
      (hh 13 (by simp [initPairBucketHelpers, endpointHelpers]))
      (hh 14 (by simp [initPairBucketHelpers, endpointHelpers]))
      (hh 15 (by simp [initPairBucketHelpers, endpointHelpers]))
      (hh 16 (by simp [initPairBucketHelpers, endpointHelpers]))

end MinCostFlow.HierPaths

end
