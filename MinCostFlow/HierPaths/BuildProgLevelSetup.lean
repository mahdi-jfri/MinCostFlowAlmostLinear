module

public import MinCostFlow.HierPaths.BuildProgLevelDefs
import MinCostFlow.HierPaths.InitLayout

/-!
# Setup and framing helpers for the non-singleton one-parent level builder

Proves `nonSingleton_setup_runs`, memory prefix framing across `ChoiceLoopTrace` and final
injection (`choiceLoopTrace_prefix_frame`, `injectEnd_prefix_frame`), child graph slot length
bounds (`injectEnd_child_le_slot`), and `buildInjectEnd_cost_eq`.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-! ### Non-singleton setup run (registers + `coreLevel` + `gameSetup`) -/

theorem nonSingleton_setup_runs {w K router core : ℕ}
    {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ}
    {coreCost : ℕ → ℕ → ℕ → Graph → ℕ} {sC : ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {g x start s k M r Δ L L' bh h : ℕ} {β : ℝ}
    {p : Program} {prior later : List Stmt} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hp : p.procs = prior ++ buildLevelProcs prior.length router core ++ later)
    (hArgW : ∀ a ∈ buildLevelArgs g x start s k M r Δ L L' bh h, a < 2 ^ w)
    (hG : GraphAt mem g G) (hX : ListAt mem x (finsetWords (buildLevelVerts start s k)))
    (hGE : g + G.encode.length ≤ h)
    (hXE : x + (finsetWords (buildLevelVerts start s k)).length ≤ h)
    (hZero : ZeroFrom mem h)
    (hHost : HostPre G (buildLevelVerts start s k) Δ L)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ))
    (hs : 1 < s) (hk : 2 ≤ k) (hsN : s ≤ (NOf M r) ^ r)
    (hSpace : h + buildLevelSpace sR sC G s k M r Δ L L' bh < 2 ^ w) :
    let D := levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h
    let d := routePathLen Δ bh L
    let limit := 49 * L' + 1
    let T := buildLevelDegree L'
    let slotWords := 2 + T * s
    let maxM := T * (s / 2)
    let saved := h + limit
    let graphs := saved + k
    let offsets := graphs + k
    let slots := offsets + k
    let replies := slots + k * slotWords
    let heap0 := replies + k + 1
    let q := coreLevel M r s
    ∃ st1 cSetup,
      Runs w p ω (buildLevelNonSingletonSetup (prior.length + 34) (prior.length + 35))
        (startState (buildLevelArgs g x start s k M r Δ L L' bh h) mem pos) .normal st1 cSetup ∧
      st1.regs 0 = g ∧ st1.regs 1 = x ∧ st1.regs 2 = start ∧ st1.regs 3 = s ∧
      st1.regs 4 = k ∧ st1.regs 5 = M ∧ st1.regs 6 = r ∧ st1.regs 7 = Δ ∧
      st1.regs 8 = L ∧ st1.regs 11 = h ∧ st1.regs 12 = d ∧ st1.regs 13 = limit ∧
      st1.regs 15 = slotWords ∧ st1.regs 16 = maxM ∧ st1.regs 17 = saved ∧
      st1.regs 18 = graphs ∧ st1.regs 19 = offsets ∧ st1.regs 20 = slots ∧
      st1.regs 21 = replies ∧ st1.regs 22 = heap0 ∧ st1.regs 23 = q ∧
      ChoiceGameMemory D D.addrs.heap (fun _ => ChildState.init) st1.mem ∧
      (∀ a < graphs, st1.mem a = mem a) ∧
      (∀ idx < D.limit, st1.mem (D.directory + idx) = 0) ∧
      cSetup ≤ (32 * ell M + 24 * s + 120) + (52 * k + 16) + 100 := by
  let b := prior.length
  let D := levelChoiceData K route routeCost sR coreCost (sC M r) G g x start s k M r Δ L L' bh h
  set d := routePathLen Δ bh L
  set limit := 49 * L' + 1
  set T := buildLevelDegree L'
  set slotWords := 2 + T * s
  set maxM := T * (s / 2)
  set saved := h + limit
  set graphs := saved + k
  set offsets := graphs + k
  set slots := offsets + k
  set replies := slots + k * slotWords
  set heap0 := replies + k + 1
  set q := coreLevel M r s
  have hLay : GameFixedLayout w D.geometry :=
    levelChoiceData_fixedLayout hGE hXE hHost hs hk hSpace
  have hR1 : 1 ≤ r := one_le_r_of_one_lt_s hs hsN
  have hBh2 : 2 ≤ bh := bh_ge_two hBh
  have hNonSing : h + ((T + 4 * k + 1 + k * slotWords) +
      T * (roundNonHoleCap s k d + k * (maxCoreSpace (sC M r) slotWords + 3 * s) +
        (s * k + 1) * maxRouteSpace sR G.n G.encode.length (2 * k + 1 + k * s)
          (Δ + L + max 2 (s * k)) + G.n) +
      (k + k * (T * s)) + (k + 1 + k * slotWords) + (k + 1 + k * (T * s + 1 + T * s * d)) + T +
      (maxCoreSpace (sC M r) slotWords +
        (s * k + 1) * maxRouteSpace sR G.n G.encode.length (2 * k + 1 + k * s)
          (Δ + L + max 2 (s * k)) +
        6 * (s * k) + 10 * k + 6 * s + 2 * d + G.n + 60) +
      connAllSpace sR G s k Δ L d +
      NOf M r + d + G.n + 100) < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add_left (le_max_right _ _) h) hSpace
  have hStartLe : start + k * s ≤ G.n := levelVerts_end_le_n hHost (by omega) (by omega)
  have hStartW : start < 2 ^ w := hArgW start (by simp [buildLevelArgs])
  have hSW : s < 2 ^ w := hArgW s (by simp [buildLevelArgs])
  have hKW : k < 2 ^ w := hArgW k (by simp [buildLevelArgs])
  have hMW : M < 2 ^ w := hArgW M (by simp [buildLevelArgs])
  have hRW : r < 2 ^ w := hArgW r (by simp [buildLevelArgs])
  have hDW : d < 2 ^ w := by omega
  have h32W : 32 < 2 ^ w := by omega
  have h49W : 49 < 2 ^ w := by omega
  have hΔ1 : 1 ≤ Δ := hHost.2.2.1
  have hL1 : 1 ≤ L := hHost.2.2.2.2.1
  have h32ΔW : 32 * Δ < 2 ^ w := by
    have h1 : 32 * Δ ≤ d := by
      dsimp [d]; unfold routePathLen
      have hbhL : 1 ≤ bh * L := Nat.mul_pos (by omega) hL1
      calc 32 * Δ = 32 * Δ * 1 := (Nat.mul_one _).symm
        _ ≤ 32 * Δ * (bh * L) := Nat.mul_le_mul_left _ hbhL
        _ = 32 * Δ * bh * L := by ring
    omega
  have h32ΔBhW : 32 * Δ * bh < 2 ^ w := by
    have h1 : 32 * Δ * bh ≤ d := by
      dsimp [d]; unfold routePathLen
      calc 32 * Δ * bh = 32 * Δ * bh * 1 := (Nat.mul_one _).symm
        _ ≤ 32 * Δ * bh * L := Nat.mul_le_mul_left _ hL1
    omega
  have hTW : T < 2 ^ w := by omega
  have h49L'W : 49 * L' < 2 ^ w := by dsimp [T, buildLevelDegree] at hTW; omega
  have hLimW : limit < 2 ^ w := by dsimp [limit, T, buildLevelDegree] at hTW ⊢; omega
  have hHeap0W : heap0 < 2 ^ w := by
    dsimp [heap0, replies, slots, offsets, graphs, saved, limit, T, buildLevelDegree] at hNonSing ⊢
    omega
  have hRepW : replies < 2 ^ w := by dsimp [heap0] at hHeap0W; omega
  have hSlotsW : slots < 2 ^ w := by dsimp [replies] at hRepW; omega
  have hOffsW : offsets < 2 ^ w := by dsimp [slots] at hSlotsW; omega
  have hGraphsW : graphs < 2 ^ w := by dsimp [offsets] at hOffsW; omega
  have hSavedW : saved < 2 ^ w := by dsimp [graphs] at hGraphsW; omega
  have hKSlotW : k * slotWords < 2 ^ w := by dsimp [replies] at hRepW; omega
  have hSlotW : slotWords < 2 ^ w := by
    have : 1 * slotWords ≤ k * slotWords := Nat.mul_le_mul_right slotWords (by omega); omega
  have hTSW : T * s < 2 ^ w := by dsimp [slotWords] at hSlotW; omega
  have hMaxMW : maxM < 2 ^ w := by
    have : maxM ≤ T * s := Nat.mul_le_mul_left T (Nat.div_le_self s 2); omega
  have ht0 := buildLevelProcs_lookup_tail hp 0 (by decide)
  have ht1 := buildLevelProcs_lookup_tail hp 1 (by decide)
  simp only [buildLevelTailProcs, List.getElem?_cons_succ, List.getElem?_cons_zero] at ht0 ht1
  have hSpecCoreLvl := buildCoreLevelProc_meetsContract (w := w) (by simpa [b] using ht0)
  have hSpecSetup := buildGameSetupProc_meetsContract (w := w) (by simpa [b] using ht1)
  have hRun : ∃ o st1 cSetup,
      Runs w p ω (buildLevelNonSingletonSetup (b + 34) (b + 35))
        (startState (buildLevelArgs g x start s k M r Δ L L' bh h) mem pos) o st1 cSetup ∧
      (o = .normal ∧
        st1.regs 0 = g ∧ st1.regs 1 = x ∧ st1.regs 2 = start ∧ st1.regs 3 = s ∧
        st1.regs 4 = k ∧ st1.regs 5 = M ∧ st1.regs 6 = r ∧ st1.regs 7 = Δ ∧
        st1.regs 8 = L ∧ st1.regs 11 = h ∧ st1.regs 12 = d ∧ st1.regs 13 = limit ∧
        st1.regs 15 = slotWords ∧ st1.regs 16 = maxM ∧ st1.regs 17 = saved ∧
        st1.regs 18 = graphs ∧ st1.regs 19 = offsets ∧ st1.regs 20 = slots ∧
        st1.regs 21 = replies ∧ st1.regs 22 = heap0 ∧ st1.regs 23 = q ∧
        ChoiceGameMemory D D.addrs.heap (fun _ => ChildState.init) st1.mem ∧
        (∀ a < graphs, st1.mem a = mem a) ∧
        (∀ idx < D.limit, st1.mem (D.directory + idx) = 0)) ∧
      cSetup ≤ (32 * ell M + 24 * s + 120) + (52 * k + 16) + 100 := by
    refine runs_start_le ?_
    unfold buildLevelNonSingletonSetup
    -- 12: d := 32 * Δ * bh * L
    refine runs_seq_assign_le (v := d)
      (Expr.eval_mul (Expr.eval_mul (Expr.eval_mul (Expr.eval_const h32W)
        (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs])) h32ΔW)
        (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs])) h32ΔBhW)
        (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs])) hDW) ?_
    -- 13: limit := 49 * L' + 1
    refine runs_seq_assign_le (v := limit)
      (Expr.eval_add (Expr.eval_mul (Expr.eval_const h49W)
        (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs])) h49L'W)
        (Expr.eval_const (by omega)) hLimW) ?_
    -- 14: T := limit + 1
    have hTEq : limit + 1 = T := rfl
    refine runs_seq_assign_le (v := T)
      (by rw [← hTEq]; exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_const (by omega)) (by rw [hTEq]; exact hTW)) ?_
    -- 15: slotWords := 2 + T * s
    refine runs_seq_assign_le (v := slotWords)
      (Expr.eval_add (Expr.eval_const (by omega))
        (Expr.eval_mul (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs])) hTSW) hSlotW) ?_
    -- 16: maxM := T * (s / 2)
    refine runs_seq_assign_le (v := maxM)
      (Expr.eval_mul (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_div (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs]))
          (Expr.eval_const (by omega)) (by omega)) hMaxMW) ?_
    -- 17: saved := h + limit
    refine runs_seq_assign_le (v := saved)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs]))
        (Expr.eval_reg_of_eq (by simp)) hSavedW) ?_
    -- 18: graphs := saved + k
    refine runs_seq_assign_le (v := graphs)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs])) hGraphsW) ?_
    -- 19: offsets := graphs + k
    refine runs_seq_assign_le (v := offsets)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs])) hOffsW) ?_
    -- 20: slots := offsets + k
    refine runs_seq_assign_le (v := slots)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs])) hSlotsW) ?_
    -- 21: replies := slots + k * slotWords
    refine runs_seq_assign_le (v := replies)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_mul (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs]))
          (Expr.eval_reg_of_eq (by simp)) hKSlotW) hRepW) ?_
    -- 22: heap0 := replies + k + 1
    refine runs_seq_assign_le (v := heap0)
      (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs])) (by dsimp [heap0] at hHeap0W; omega))
        (Expr.eval_const (by omega)) hHeap0W) ?_
    -- 23: q ← call fCoreLevel [M, r, s]
    have hCoreLvlPre : (buildCoreLevelContract w).pre [M, r, s] mem :=
      ⟨M, r, s, rfl, hR1, hs, by omega, by omega⟩
    refine runs_seq_call_le hSpecCoreLvl (vs := [M, r, s])
      (by simp [evalArgs, Expr.eval, startState, buildLevelArgs])
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> assumption)
      hCoreLvlPre ?_
    intro vQ mQ _ hPostQ
    obtain ⟨_, _, _, heqQ, hvQ, hmQ⟩ := hPostQ
    simp only [List.cons.injEq, and_true] at heqQ
    obtain ⟨rfl, rfl, rfl⟩ := heqQ
    change vQ = q at hvQ; subst hvQ
    subst mQ
    -- 24: call fSetup [graphs, offsets, slots, start, s, k, slotWords]
    have hSetupPre : (buildGameSetupContract w).pre [graphs, offsets, slots, start, s, k, slotWords] mem :=
      ⟨graphs, offsets, slots, start, s, k, slotWords, rfl, le_rfl, le_rfl,
       by dsimp [slotWords]; omega, by dsimp [replies] at hRepW; omega, by omega, by omega,
       fun a ha => hZero a (by dsimp [graphs, saved] at ha; omega)⟩
    refine runs_call_le hSpecSetup
      (vs := [graphs, offsets, slots, start, s, k, slotWords])
      (by simp [evalArgs, Expr.eval, startState, buildLevelArgs])
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
      hSetupPre ?_
    intro _ m1 _ hPost1
    have hInitMem : ChoiceGameMemory D D.addrs.heap (fun _ => ChildState.init) m1 :=
      choiceGameMemory_init (slot := slots) hLay hG hX (fun _ => rfl)
        (by change slots + k * slotWords ≤ heap0; dsimp [heap0, replies]; omega) hPost1
    have hM1BelowGraphs : ∀ a < graphs, m1 a = mem a := by
      obtain ⟨_, _, _, _, _, _, _, heq1, hAt1, _, _, _, _⟩ := hPost1
      simp only [List.cons.injEq, and_true] at heq1
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq1
      intro a ha
      exact hAt1.2 a (Or.inl ha) (Or.inl (by dsimp [offsets]; omega))
        (fun i _ => by dsimp [slots, offsets]; omega)
    have hDirZero : ∀ idx < D.limit, m1 (D.directory + idx) = 0 := fun idx hidx => by
      change m1 (h + idx) = 0
      rw [hM1BelowGraphs _ (by dsimp [graphs, saved]; change idx < limit at hidx; omega)]
      exact hZero _ (by omega)
    refine ⟨⟨rfl, by simp [startState, buildLevelArgs], by simp [startState, buildLevelArgs],
      by simp [startState, buildLevelArgs], by simp [startState, buildLevelArgs],
      by simp [startState, buildLevelArgs], by simp [startState, buildLevelArgs],
      by simp [startState, buildLevelArgs], by simp [startState, buildLevelArgs],
      by simp [startState, buildLevelArgs], by simp [startState, buildLevelArgs],
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, hInitMem, hM1BelowGraphs, hDirZero⟩, ?_⟩
    simp only [buildCoreLevelContract, buildGameSetupContract,
      List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
    omega
  obtain ⟨_, st1, cSetup, hR, ⟨rfl, hregs⟩, hC⟩ := hRun
  exact ⟨st1, cSetup, hR, hregs.1, hregs.2.1, hregs.2.2.1, hregs.2.2.2.1,
    hregs.2.2.2.2.1, hregs.2.2.2.2.2.1, hregs.2.2.2.2.2.2.1, hregs.2.2.2.2.2.2.2.1,
    hregs.2.2.2.2.2.2.2.2.1, hregs.2.2.2.2.2.2.2.2.2.1, hregs.2.2.2.2.2.2.2.2.2.2.1,
    hregs.2.2.2.2.2.2.2.2.2.2.2.1, hregs.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hregs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hC⟩

theorem choiceLoopTrace_prefix_frame {w tailBudget t heap bh : ℕ} {D : ChoiceLoopData}
    {β : ℝ} {initial mem : ℕ → ℕ} {sts : ℕ → ChildState}
    (ht : t ≤ D.limit) (hTr : ChoiceLoopTrace w D initial t heap sts mem)
    (hHyp : ChoiceGameHyp D β bh) (hLay : GameFixedLayout w D.geometry)
    (hInitMem : ChoiceGameMemory D D.addrs.heap (fun _ => ChildState.init) initial)
    (hRoomAll : ∀ t' heap' sts' mem', t' < D.limit →
      ChoiceLoopTrace w D initial t' heap' sts' mem' → (D.round sts').jobs.count ≠ 0 →
      ChoiceRoundBudget w tailBudget D heap' sts') :
    ∀ a < D.directory, mem a = initial a := by
  have hDS : D.directory + D.limit ≤ D.saved := hLay.directory
  have hSG : D.saved + D.count ≤ D.addrs.graphs := hLay.saved
  have hGO : D.addrs.graphs + D.count ≤ D.addrs.offsets := hLay.graphs
  have hOR : D.addrs.offsets + D.count ≤ D.addrs.replies := hLay.offsets
  induction hTr with
  | start => intro _ _; rfl
  | skip _ _ ih => exact ih (Nat.le_of_succ_le ht)
  | @run t'' heap'' sts'' mem'' v'' after'' tr'' hn'' ans'' bump'' rBump'' hCert'' hBump'' hRBump'' hPost'' ih =>
    have hM'' := tr''.memory (Nat.le_of_succ_le ht) hHyp hLay hInitMem hRoomAll
    have hPre'' := choiceStep_pre_of_memory hHyp hLay hM'' ht tr''
      (hRoomAll t'' heap'' sts'' mem'' ht tr'' hn'') (Nat.pos_of_ne_zero hn'')
    let B'' := (D.round sts'').withReplies ans'' bump'' rBump''
    let A'' := D.atHeap heap''
    have hFit'' : BuildRoundFit w B'' A'' mem'' :=
      (hPre''.2.1.2.2 ans'' bump'' hCert'' hBump'').1 rBump'' hRBump''
    have hLay0 := hPre''.2.2.1
    have hLay'' : GameStepLayout w B'' A'' D.first D.saved (D.active sts'') :=
      ⟨hLay0.active, hLay0.size, hLay0.childInj, hLay0.offsets, hLay0.offsetWord,
        hLay0.savedBelow, hLay0.graphsBelow, hLay0.offsetsBelow, hLay0.tableBelow⟩
    have hRows'' : ∀ Ms'' emb'', B''.indices.isEmpty = false → B''.result.1 = .matched Ms'' emb'' →
        Ms''.length = B''.indices.length := fun Ms'' emb'' hne'' hres'' =>
      (D.matchedRows hCert'' hHyp.router hHyp.host hHyp.positive hHyp.expansion
        hHyp.denominator hHyp.children hHyp.even hne'' hres'').1
    intro a ha
    have hSafe : B''.unchangedBelow a := by
      by_cases hem'' : B''.indices.isEmpty = true
      · exact Or.inl hem''
      · refine Or.inr fun Ms'' emb'' hm'' i hi'' => Or.inl ?_
        have hIdx := (mem_batchJobIndices.mp (rowIndex_mem (emb := emb'') hi''
          (hRows'' Ms'' emb'' (Bool.eq_false_iff.mpr hem'') hm''))).1
        have hSl := (hLay.slots _ (D.active_mem hIdx).1).1
        change D.addrs.offsets + D.count ≤ D.childAddr _ at hSl
        exact lt_of_lt_of_le (by omega) hSl
    have hDir : D.directory + t'' ≠ a := by omega
    rw [Function.update_of_ne hDir.symm]
    have hFr'' := gameStep_prefix_frame hFit'' hLay'' hRows'' hPost''
      (Or.inl ⟨by dsimp only [A'', ChoiceLoopData.atHeap]; omega, hSafe⟩)
      (Or.inl (by dsimp only [A'', ChoiceLoopData.atHeap]; omega))
      (Or.inl (by dsimp only [A'', ChoiceLoopData.atHeap]; omega))
      (fun i hi'' _ => by have := hLay''.savedBelow i hi''; omega)
    exact hFr''.trans (ih (Nat.le_of_succ_le ht) a ha)

theorem injectEnd_prefix_frame {w heap₁ slot injEnd bh runEnd : ℕ} {D : ChoiceLoopData}
    {β : ℝ} {initial mem₂ mem₃ : ℕ → ℕ} {sts : ℕ → ChildState}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hTrace : ChoiceLoopTrace w D initial D.limit heap₁ sts mem₂)
    (hHyp : ChoiceGameHyp D β bh) (hLay : GameFixedLayout w D.geometry)
    (hMem2 : ChoiceGameMemory D heap₁ sts mem₂)
    (hInjMatch : RouteMatchedSpec D.base.host D.base.verts
      (injPairs D.base.childSize D.count D.offset sts) D.base.Δ D.base.L runEnd 0 Ms emb)
    (hInjFull : ∀ i (hi : i < (injPairs D.base.childSize D.count D.offset sts).length),
      (Ms.getD i []).length = ((injPairs D.base.childSize D.count D.offset sts)[i]'hi).1.card)
    (hPost3 : (buildInjectEndContract w D heap₁ slot sts Ms emb).post
      (injectEndArgs D heap₁ slot) mem₂ injEnd mem₃) :
    ∀ a < D.directory, mem₃ a = mem₂ a := by
  have hDS : D.directory + D.limit ≤ D.saved := hLay.directory
  have hSG : D.saved + D.count ≤ D.addrs.graphs := hLay.saved
  have hGO : D.addrs.graphs + D.count ≤ D.addrs.offsets := hLay.graphs
  have hOR : D.addrs.offsets + D.count ≤ D.addrs.replies := hLay.offsets
  have hRH : D.addrs.replies + D.count + 1 ≤ D.addrs.heap := hLay.replies
  obtain ⟨top, mid, hTopLo, _, hPostR, hPostF⟩ := hPost3
  obtain ⟨_, _, _, _, _, heqR, _, _, _, _, hFrR, _⟩ := hPostR
  simp only [List.cons.injEq, and_true, true_and] at heqR
  obtain ⟨rfl, rfl, rfl, rfl, _, rfl⟩ := heqR
  obtain ⟨_, _, _, midT, heqF, hPostT, hPostFB⟩ := hPostF
  simp only [injectFinishArgs, List.cons.injEq, and_true, true_and] at heqF
  obtain ⟨rfl, rfl, rfl⟩ := heqF
  obtain ⟨_, _, _, _, _, _, _, _, heqT, hFrT, _, _, _⟩ := hPostT
  simp only [List.cons.injEq, and_true] at heqT
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heqT
  obtain ⟨_, _, _, _, _, _, _, heqFB, hPostAB⟩ := hPostFB
  simp only [List.cons.injEq, and_true] at heqFB
  obtain ⟨rfl, rfl, rfl, rfl, rfl, _, rfl, rfl, _⟩ := heqFB
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, heqAB, _, _, _, hFrAB, _⟩ := hPostAB
  simp only [finishBatchApplyArgs, List.cons.injEq, and_true, true_and] at heqAB
  obtain ⟨rfl, rfl, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heqAB
  intro a ha
  have hKept : (D.injectionData sts Ms emb).Kept top Ms.length a := by
    refine ⟨?_, fun j hj => Or.inl ?_⟩
    · have h1 : D.addrs.heap ≤ heap₁ := hMem2.heap
      have h2 : heap₁ ≤ injectReplyBase heap₁ D.count D.base.childSize := by
        unfold injectReplyBase buildBatchEnd; omega
      omega
    · have hC := (hTrace.injectRow hHyp hInjMatch hInjFull hj).1
      have hNm := D.injection_child sts Ms emb hC
      change a < D.childAddr ((D.injectionData sts Ms emb).child j)
      rw [hNm]
      have hSl := (hLay.slots j hC).1
      change D.addrs.offsets + D.count ≤ D.childAddr j at hSl
      omega
  have h1 : mem₃ a = midT a := hFrAB a hKept
  have h2 : midT a = mid a := hFrT.2 a (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
  have h3 : mid a = mem₂ a := hFrR a (by have := hMem2.heap; omega)
  exact h1.trans (h2.trans h3)

private theorem injectEnd_child_len {w heap₁ slot injEnd routeCap : ℕ} {D : ChoiceLoopData}
    {mem₂ mem₃ : ℕ → ℕ} {sts : ℕ → ChildState}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    {F : ℕ → List ((ℕ × ℕ) × List ℕ)}
    (hAffine : ∀ i, D.childAddr i = slot + i * D.geometry.slotWords)
    (hMlen : Ms.length = D.count)
    (hInjArch : InjArchive D.base.host D.base.childSize D.count D.base.pathBound routeCap
      slot D.geometry.slotWords heap₁ injEnd F (fun c => (sts c).rounds.flatten.map Prod.snd) mem₃)
    (hPost3 : (buildInjectEndContract w D heap₁ slot sts Ms emb).post
      (injectEndArgs D heap₁ slot) mem₂ injEnd mem₃) :
    ∀ c < D.count, (F c).length = (gameGraph D.base.childSize (sts c)).m + (Ms.getD c []).length := by
  intro c hc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hSlotF, _, _, _, _⟩ := hInjArch
  have hM1F : mem₃ (slot + c * D.geometry.slotWords + 1) = (F c).length := by
    have hAt1 := hSlotF c hc 1 (by rw [buildGraph_encode_length]; omega)
    simpa [Graph.encode, Graph.m] using hAt1
  obtain ⟨_, _, _, _, _, hPostF⟩ := hPost3
  obtain ⟨_, _, _, _, _, _, hFB⟩ := hPostF
  obtain ⟨_, _, _, _, _, _, _, _, hAB⟩ := hFB
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hRowAt⟩ := hAB
  have hGr := (hRowAt c (hMlen.symm ▸ hc)).1
  have hNm := D.injection_child sts Ms emb hc
  have hAddrEq : (D.injectionData sts Ms emb).addr c = slot + c * D.geometry.slotWords := by
    change D.childAddr ((D.injectionData sts Ms emb).child c) = _
    rw [hNm, hAffine c]
  rw [hAddrEq] at hGr
  have hM1G : mem₃ (slot + c * D.geometry.slotWords + 1) =
      (gameGraph D.base.childSize (sts c)).m + (Ms.getD c []).length := by
    have hAt1 := hGr 1 (by rw [buildGraph_encode_length]; omega)
    have hGraphC : (D.injectionData sts Ms emb).graph c = gameGraph D.base.childSize (sts c) := by
      unfold ApplyBatchData.graph; rw [hNm]; rfl
    simp only [Graph.encode, Graph.m, appendGameMatching,
      List.getElem_cons_succ, List.getElem_cons_zero, List.length_append, List.length_map] at hAt1
    rw [hGraphC] at hAt1
    simpa [Graph.m, ChoiceLoopData.injectionData] using hAt1
  exact hM1F.symm.trans hM1G

theorem injectEnd_child_le_slot {w heap₁ slot injEnd routeCap bh runEnd : ℕ} {D : ChoiceLoopData}
    {β : ℝ} {initial mem₂ mem₃ : ℕ → ℕ} {sts : ℕ → ChildState}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    {F : ℕ → List ((ℕ × ℕ) × List ℕ)}
    (hTrace : ChoiceLoopTrace w D initial D.limit heap₁ sts mem₂)
    (hHyp : ChoiceGameHyp D β bh)
    (hAffine : ∀ i, D.childAddr i = slot + i * D.geometry.slotWords)
    (hInjMatch : RouteMatchedSpec D.base.host D.base.verts
      (injPairs D.base.childSize D.count D.offset sts) D.base.Δ D.base.L runEnd 0 Ms emb)
    (hInjFull : ∀ i (hi : i < (injPairs D.base.childSize D.count D.offset sts).length),
      (Ms.getD i []).length = ((injPairs D.base.childSize D.count D.offset sts)[i]'hi).1.card)
    (hInjArch : InjArchive D.base.host D.base.childSize D.count D.base.pathBound routeCap
      slot D.geometry.slotWords heap₁ injEnd F (fun c => (sts c).rounds.flatten.map Prod.snd) mem₃)
    (hPost3 : (buildInjectEndContract w D heap₁ slot sts Ms emb).post
      (injectEndArgs D heap₁ slot) mem₂ injEnd mem₃) :
    ∀ c < D.count, 2 + 2 * (F c).length ≤ D.geometry.slotWords := by
  intro c hc
  have hMLen : Ms.length = D.count := by simpa [injPairs] using hInjMatch.1
  have hRow := hTrace.injectRow hHyp hInjMatch hInjFull (i := c) (hMLen.symm ▸ hc)
  have hCap := hRow.2.1
  have hNm := D.injection_child sts Ms emb hc
  have hCapEq : (D.injectionData sts Ms emb).cap c =
      D.childAddr c + 2 + 2 * ((gameGraph D.base.childSize (sts c)).m + (Ms.getD c []).length) := by
    unfold ApplyBatchData.cap ApplyBatchData.addr ApplyBatchData.graph ApplyBatchData.row
    rw [hNm]; rfl
  rw [hCapEq] at hCap
  have hFlenEq := injectEnd_child_len hAffine hMLen hInjArch hPost3 c hc
  omega

theorem buildInjectEnd_cost_eq (w heap₁ slot : ℕ) (D : ChoiceLoopData)
    (sts : ℕ → ChildState) (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ)
    (vs : List ℕ) (m : ℕ → ℕ) :
    (buildInjectEndContract w D heap₁ slot sts Ms emb).cost vs m =
      (D.count * (120 * D.base.childSize + 260) + 64) +
      (buildFullRouteContract w D.base.K D.base.route D.base.routeCost D.base.routeSpace
        D.base.host D.base.verts (injPairs D.base.childSize D.count D.offset sts)
        D.base.Δ D.base.L D.base.verts.card 2).cost [] (fun _ => 0) + 70 +
      (60 * D.count + 16 +
        (buildFinishBatchContract w (D.injectionData sts Ms emb)).cost [] (fun _ => 0) + 90) + 120 := by
  simp only [buildInjectEndContract, buildInjectRouteContract, buildInjectionContract,
    buildInjectFinishContract, buildFullRouteContract, buildFinishBatchContract]
  have hPL : (injPairs D.base.childSize D.count D.offset sts).length = D.count := by simp [injPairs]
  rw [hPL]


end MinCostFlow.HierPaths
