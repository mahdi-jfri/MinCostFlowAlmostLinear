module

public import MinCostFlow.SparseCore.Program.ReadRestartInitSetup

/-!
# Full branch initialization verification (`ReadRestartInit`)

Completes the verification of `readInitStmt` (`ReadRestartInitSetup.lean`) in two small lemmas:
* `readInitPart2a_runs`: copies the stretch tables and initializes the vertex sets of `live` and `frz`.
* `readInitPart2b_runs`: splits the edges of `T` into `liveT G T` and `frozenT G T` and returns `hEnd`.
* `readInit_runs`: combines Part 1, Part 2a, and Part 2b to establish `ReadRecAt`, `liveT`,
  `frozenT`, `ZeroFrom`, frame preservation, and the amortized cost + initial potential bound
  `c + 1000 * treePot v.G v.lsf.T ≤ 3100 * (readInitSize v + 1) * (L_w + 1)`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.SparseCore.Program.Restart

/-- Vertex-only initialization of `live` and `frz` (tail of `readInitPart2aStmt`). -/
private theorem readInitLiveFrz_runs {w vCap eCap tCap gD h Dt De live frz hEnd : ℕ} {p : Program}
    {bOps bEdge bSplit bBatch bLoop bInitOps bSelf : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpSelf : p.HasAt bSelf (readInitProcs bBatch bLoop bInitOps bSelf))
    {G : MGraph} {mem : ℕ → ℕ} {st6 : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hDt : dynGraphSize vCap tCap = Dt) (hDe : dynGraphSize vCap eCap = De)
    (h_le_live : h ≤ live) (hfrz : live + De = frz) (hhEnd : frz + Dt = hEnd)
    (hhEnd_lt : hEnd < 2 ^ w) (hgD_W : gD < 2 ^ w)
    (hExpG : ExportAt mem gD h G) (hGvCap : ∀ u ∈ G.V, u < vCap)
    (hr0 : st6.regs 0 = vCap) (hr1 : st6.regs 1 = eCap) (hr2 : st6.regs 2 = tCap)
    (hr4 : st6.regs 4 = gD) (hr23 : st6.regs 23 = live) (hr24 : st6.regs 24 = frz)
    (hz6 : ZeroFrom st6.mem live) (hbelow6 : ∀ a < h, st6.mem a = mem a) :
    ∃ st8 c,
      Runs w p ω
        (.call 28 (bSelf + 1) [.reg 23, .reg 0, .reg 1, .reg 4] ;;
         .call 28 (bSelf + 1) [.reg 24, .reg 0, .reg 2, .reg 4]) st6 .normal st8 c ∧
      (∀ r < 26, st8.regs r = st6.regs r) ∧
      DynGraphAt st8.mem live vCap eCap { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 } ∧
      DynGraphAt st8.mem frz vCap tCap { V := G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 } ∧
      ZeroFrom st8.mem hEnd ∧ (∀ a < live, st8.mem a = st6.mem a) ∧
      c ≤ 260 * G.n + 275 := by
  have hDt_pos : 4 + 7 * vCap + 9 * tCap = Dt := by rw [← hDt]; rfl
  have hDe_pos : 4 + 7 * vCap + 9 * eCap = De := by rw [← hDe]; rfl
  have hvCapW : vCap < 2 ^ w := by omega
  have heCapW : eCap < 2 ^ w := by omega
  have htCapW : tCap < 2 ^ w := by omega
  have hliveW : live < 2 ^ w := by omega
  have hfrzW : frz < 2 ^ w := by omega
  have hC7 := runs_call_of_meetsContract (r := 28)
    (initVertsFromExport_meetsContract (G := G) hpSelf hpBatch hpEdge hpOps)
    (show evalArgs w st6 [.reg 23, .reg 0, .reg 1, .reg 4] = some [live, vCap, eCap, gD] by
      simp [evalArgs, Expr.eval, hr23, hr0, hr1, hr4])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro z (rfl|rfl|rfl|rfl); exacts [hliveW, hvCapW, heCapW, hgD_W])
    ⟨live, gD, h, rfl, hw16, by omega, h_le_live, hz6, hGvCap,
      exportAt_of_agree hExpG hbelow6⟩ ω
  obtain ⟨st7, c7, _, hr7, ⟨_, _, hEq7, _, hL7, hfr7, hz7⟩, _, hregs7, hc7⟩ := hC7
  simp only [List.cons.injEq, true_and, and_true] at hEq7; obtain ⟨rfl, rfl⟩ := hEq7
  rw [hDe, hfrz] at hz7 hfr7
  have hbelow7 : ∀ a < h, st7.mem a = mem a := fun a ha => (hfr7 a (Or.inl (by omega))).trans (hbelow6 a ha)
  have hC8 := runs_call_of_meetsContract (r := 28)
    (initVertsFromExport_meetsContract (G := G) hpSelf hpBatch hpEdge hpOps)
    (show evalArgs w st7 [.reg 24, .reg 0, .reg 2, .reg 4] = some [frz, vCap, tCap, gD] by
      simp [evalArgs, Expr.eval, hregs7 24 (by decide), hregs7 0 (by decide),
        hregs7 2 (by decide), hregs7 4 (by decide), hr24, hr0, hr2, hr4])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro z (rfl|rfl|rfl|rfl); exacts [hfrzW, hvCapW, htCapW, hgD_W])
    ⟨frz, gD, h, rfl, hw16, by omega, by omega, hz7, hGvCap,
      exportAt_of_agree hExpG hbelow7⟩ ω
  obtain ⟨st8, c8, _, hr8, ⟨_, _, hEq8, _, hF8, hfr8, hz8⟩, _, hregs8, hc8⟩ := hC8
  simp only [List.cons.injEq, true_and, and_true] at hEq8; obtain ⟨rfl, rfl⟩ := hEq8
  rw [hDt, hhEnd] at hz8 hfr8
  refine ⟨st8, c7 + c8 + 1, runs_seq_iff.mpr (Or.inr ⟨st7, c7, c8, hr7, hr8, rfl⟩),
    fun r hr => (hregs8 r (by omega)).trans (hregs7 r (by omega)),
    hL7.of_agree fun a _ ha2 => hfr8 a (Or.inl (by omega)), hF8, hz8,
    fun a ha => (hfr8 a (Or.inl (by omega))).trans (hfr7 a (Or.inl ha)), ?_⟩
  dsimp only [initVertsFromExportContract, argsSize, Expr.size] at hc7 hc8
  omega

/-- Part 2a of `readInitStmt`: stretch copy and vertex-only init of `live` and `frz`. -/
private theorem readInitPart2a_runs {w vCap eCap tCap L_w : ℕ} {p : Program}
    {bOps bEdge bSplit bBatch bLoop bInitOps bSelf : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpInitOps : p.HasAt bInitOps (readInitOpsProcs bEdge))
    (hpSelf : p.HasAt bSelf (readInitProcs bBatch bLoop bInitOps bSelf))
    {gD tD fD rootsPtr nR numPtr denPtr sD h Dt De qt qf qroots qs qg qnum qden live frz hEnd : ℕ}
    {v : ReadView} {mem : ℕ → ℕ} {st5 : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hLwW : L_w < 2 ^ w)
    (hDt : dynGraphSize vCap tCap = Dt) (hDe : dynGraphSize vCap eCap = De)
    (hqt : h + 11 = qt) (hqf : qt + Dt = qf) (hqroots : qf + Dt = qroots)
    (hqs : qroots + vCap = qs) (hqg : qs + De = qg) (hqnum : qg + De = qnum)
    (hqden : qnum + eCap * L_w = qden) (hlive : qden + eCap * L_w = live)
    (hfrz : live + De = frz) (hhEnd : frz + Dt = hEnd) (hhEnd_lt : hEnd < 2 ^ w)
    (hgD_W : gD < 2 ^ w) (hnumP_W : numPtr < 2 ^ w) (hdenP_W : denPtr < 2 ^ w)
    (hExpG : ExportAt mem gD h v.G)
    (hStrB : ∀ e ∈ v.G.E, numPtr + (e + 1) * L_w ≤ h ∧ denPtr + (e + 1) * L_w ≤ h)
    (hGvCap : ∀ u ∈ v.G.V, u < vCap) (hGeCap : ∀ e ∈ v.G.E, e < eCap)
    (hregs5 : ReadInitRegs st5.regs vCap eCap tCap L_w gD tD fD rootsPtr nR numPtr denPtr sD h
      qt qf qroots qs qg qnum qden live frz hEnd)
    (hG5 : DynGraphAt st5.mem qg vCap eCap v.G) (hz5 : ZeroFrom st5.mem qnum)
    (hbelow5 : ∀ a < h, st5.mem a = mem a) :
    ∃ st8 c,
      Runs w p ω (readInitPart2aStmt bInitOps bSelf) st5 .normal st8 c ∧
      (∀ r < 26, st8.regs r = st5.regs r) ∧
      (∀ e ∈ v.G.E, ∀ k < L_w,
        st8.mem (qnum + e * L_w + k) = mem (numPtr + e * L_w + k) ∧
        st8.mem (qden + e * L_w + k) = mem (denPtr + e * L_w + k)) ∧
      DynGraphAt st8.mem qg vCap eCap v.G ∧
      DynGraphAt st8.mem live vCap eCap { V := v.G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 } ∧
      DynGraphAt st8.mem frz vCap tCap { V := v.G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 } ∧
      ZeroFrom st8.mem hEnd ∧ (∀ a < qnum, st8.mem a = st5.mem a) ∧
      c ≤ 55 * v.G.m * (L_w + 1) + 260 * v.G.n + 330 := by
  have hDt_pos : 4 + 7 * vCap + 9 * tCap = Dt := by rw [← hDt]; rfl
  have hDe_pos : 4 + 7 * vCap + 9 * eCap = De := by rw [← hDe]; rfl
  have ⟨heCapW, hqnumW, hqdenW, hqnum_le_qden, hqden_le_live, h_le_qnum, h_le_live, hqg_le_qnum⟩ :
      eCap < 2 ^ w ∧ qnum < 2 ^ w ∧ qden < 2 ^ w ∧ qnum ≤ qden ∧ qden ≤ live ∧
      h ≤ qnum ∧ h ≤ live ∧ qg + De ≤ qnum := by omega
  obtain ⟨eLG, heLG_len, _, heLG_mem, heLG_at, _⟩ := hG5.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmG_mem : st5.mem (qg + 3) = eLG.length :=
    (by simpa [dgMOff] using hG5.2.2.2.2.2.2.1 : st5.mem (qg + 3) = v.G.m).trans heLG_len.symm
  have hmG_le_eCap : eLG.length ≤ eCap := by
    rw [heLG_len]; exact (Finset.card_le_card (fun e he => Finset.mem_range.mpr (hGeCap e he))).trans (by simp)
  have heLG_W : eLG.length < 2 ^ w := by omega
  have heListW : dgEListBase qg vCap eCap < 2 ^ w := by dsimp only [dgEListBase]; omega
  have hr26 : Runs w p ω (.assign 26 (.bin .add (.bin .add (.bin .add (.reg 20) (.const 4))
      (.bin .mul (.const 7) (.reg 0))) (.reg 1))) st5 .normal
      { st5 with regs := Function.update st5.regs 26 (dgEListBase qg vCap eCap) } 10 :=
    runs_assign_iff.mpr ⟨dgEListBase qg vCap eCap,
      Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hregs5.r20)
        (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hregs5.r0) (by omega)) (by omega))
        (Expr.eval_reg_of_eq hregs5.r1) heListW, rfl, rfl, by simp [Expr.size]⟩
  set st5a := { st5 with regs := Function.update st5.regs 26 (dgEListBase qg vCap eCap) }
  have hr27 : Runs w p ω (.assign 27 (.load (.bin .add (.reg 20) (.const 3)))) st5a .normal
      { st5a with regs := Function.update st5a.regs 27 eLG.length } 5 :=
    runs_assign_iff.mpr ⟨eLG.length, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st5a, hregs5.r20])) (Expr.eval_const (by omega)) (by omega))
      hmG_mem, rfl, rfl, by simp [Expr.size]⟩
  set st5b := { st5a with regs := Function.update st5a.regs 27 eLG.length }
  have hC6 := runs_call_of_meetsContract (r := 28)
    (copyStretchPairs_meetsContract (eCap := eCap) (L_w := L_w) (eL := eLG) hpInitOps)
    (show evalArgs w st5b [.reg 26, .reg 27, .reg 3, .reg 9, .reg 10, .reg 21, .reg 22] =
        some [dgEListBase qg vCap eCap, eLG.length, L_w, numPtr, denPtr, qnum, qden] by
      simp [evalArgs, Expr.eval, st5b, st5a, hregs5.r3, hregs5.r9, hregs5.r10, hregs5.r21, hregs5.r22])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro z (rfl|rfl|rfl|rfl|rfl|rfl|rfl)
        exacts [heListW, heLG_W, hLwW, hnumP_W, hdenP_W, hqnumW, hqdenW])
    ⟨dgEListBase qg vCap eCap, numPtr, denPtr, qnum, qden, rfl, hw16, heLG_at,
      by dsimp [dgEListBase]; omega,
      fun e he => by
        have heG := (heLG_mem e).mp he; obtain ⟨h1, h2⟩ := hStrB e heG
        exact ⟨hGeCap e heG, by omega, by omega⟩, by omega, by omega⟩ ω
  obtain ⟨st6, c6, _, hr6, ⟨_, _, _, _, _, hEq6, _, hCopied, hfr6⟩, _, hregs6, hc6⟩ := hC6
  simp only [List.cons.injEq, true_and, and_true] at hEq6; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hEq6
  rw [hqden, hlive] at hfr6
  have hz6 : ZeroFrom st6.mem live := fun a ha => by
    rw [hfr6 a (Or.inr (le_trans hqden_le_live ha)) (Or.inr ha)]
    exact hz5 a (le_trans hqnum_le_qden (le_trans hqden_le_live ha))
  have hbelow6 : ∀ a < h, st6.mem a = mem a := fun a ha =>
    (hfr6 a (Or.inl (lt_of_lt_of_le ha h_le_qnum))
      (Or.inl (lt_of_lt_of_le ha (le_trans h_le_qnum hqnum_le_qden)))).trans (hbelow5 a ha)
  have hregs6_eq : ∀ r < 26, st6.regs r = st5.regs r := fun r hr => by
    rw [hregs6 r (by omega)]; simp [st5b, st5a, show r ≠ 27 by omega, show r ≠ 26 by omega]
  obtain ⟨st8, c78, hr78, hregs8_eq, hL8, hF8, hz8, hpres_live, hc78⟩ :=
    readInitLiveFrz_runs hpOps hpEdge hpBatch hpSelf hw16 hDt hDe h_le_live hfrz hhEnd hhEnd_lt
      hgD_W hExpG hGvCap
      ((hregs6_eq 0 (by decide)).trans hregs5.r0) ((hregs6_eq 1 (by decide)).trans hregs5.r1)
      ((hregs6_eq 2 (by decide)).trans hregs5.r2) ((hregs6_eq 4 (by decide)).trans hregs5.r4)
      ((hregs6_eq 23 (by decide)).trans hregs5.r23) ((hregs6_eq 24 (by decide)).trans hregs5.r24)
      hz6 hbelow6
  have hS8 := runs_seq_iff.mpr (Or.inr ⟨st6, c6, c78, hr6, hr78, rfl⟩)
  have hS7 := runs_seq_iff.mpr (Or.inr ⟨st5b, 5, _, hr27, hS8, rfl⟩)
  have hS6 := runs_seq_iff.mpr (Or.inr ⟨st5a, 10, _, hr26, hS7, rfl⟩)
  have hpres_qnum : ∀ a < qnum, st8.mem a = st5.mem a := fun a ha =>
    (hpres_live a (lt_of_lt_of_le ha (le_trans hqnum_le_qden hqden_le_live))).trans
      (hfr6 a (Or.inl ha) (Or.inl (lt_of_lt_of_le ha hqnum_le_qden)))
  refine ⟨st8, _, hS6,
    fun r hr => (hregs8_eq r hr).trans (hregs6_eq r hr),
    ?_, hG5.of_agree fun a _ ha2 => hpres_qnum a (lt_of_lt_of_le (hDe ▸ ha2) hqg_le_qnum),
    hL8, hF8, hz8, hpres_qnum, ?_⟩
  · intro e he k hk
    have heCap := hGeCap e he
    have he_mul : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right L_w (by omega)
    rw [Nat.add_mul, one_mul] at he_mul
    obtain ⟨hN_eq, hD_eq⟩ := hCopied e ((heLG_mem e).mpr he) k hk
    obtain ⟨hbN, hbD⟩ := hStrB e he
    rw [Nat.add_mul, one_mul] at hbN hbD
    rw [hpres_live _ (by omega), hpres_live _ (by omega), hN_eq, hD_eq,
      hbelow5 _ (by omega), hbelow5 _ (by omega)]
    exact ⟨rfl, rfl⟩
  · dsimp only [copyStretchPairsContract, argsSize, Expr.size] at hc6
    rw [heLG_len] at hc6; omega

/-- Part 2b of `readInitStmt`: split `T`'s edges into `liveT` and `frozenT` and return `hEnd`. -/
private theorem readInitPart2b_runs {w vCap eCap tCap L_w : ℕ} {p : Program}
    {bOps bEdge bInitOps : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpInitOps : p.HasAt bInitOps (readInitOpsProcs bEdge))
    {gD tD fD rootsPtr nR numPtr denPtr sD h Dt De qt qf qroots qs qg qnum qden live frz hEnd : ℕ}
    {v : ReadView} {mem : ℕ → ℕ} {st8 : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hDt : dynGraphSize vCap tCap = Dt) (hDe : dynGraphSize vCap eCap = De)
    (hqt : h + 11 = qt) (hqf : qt + Dt = qf) (hqroots : qf + Dt = qroots)
    (hqs : qroots + vCap = qs) (hqg : qs + De = qg) (hqnum : qg + De = qnum)
    (hqden : qnum + eCap * L_w = qden) (hlive : qden + eCap * L_w = live)
    (hfrz : live + De = frz) (hhEnd : frz + Dt = hEnd) (hhEnd_lt : hEnd < 2 ^ w)
    (hExpT : ExportAt mem tD h v.lsf.T) (hhW : h < 2 ^ w)
    (hAgree : TreeAgree v.G v.lsf.T) (hTeCap : ∀ e ∈ v.lsf.T.E, e < tCap)
    (hregs8 : ReadInitRegs st8.regs vCap eCap tCap L_w gD tD fD rootsPtr nR numPtr denPtr sD h
      qt qf qroots qs qg qnum qden live frz hEnd)
    (hG8 : DynGraphAt st8.mem qg vCap eCap v.G)
    (hL8 : DynGraphAt st8.mem live vCap eCap { V := v.G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 })
    (hF8 : DynGraphAt st8.mem frz vCap tCap { V := v.G.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 })
    (hz8 : ZeroFrom st8.mem hEnd) (hbelow8 : ∀ a < h, st8.mem a = mem a) :
    ∃ o st9 c,
      Runs w p ω (readInitPart2bStmt bInitOps) st8 o st9 c ∧
      o.value = hEnd ∧
      DynGraphAt st9.mem live vCap eCap (liveT v.G v.lsf.T) ∧
      DynGraphAt st9.mem frz vCap tCap (frozenT v.G v.lsf.T) ∧
      ZeroFrom st9.mem hEnd ∧ (∀ a < live, st9.mem a = st8.mem a) ∧
      c ≤ 540 * v.lsf.T.m + 65 := by
  have hqgW : qg < 2 ^ w := by omega
  have hliveW : live < 2 ^ w := by omega
  have hfrzW : frz < 2 ^ w := by omega
  obtain ⟨_, hTm, _, _, hTnd, hTspec, hTcov, hTd4, _, _, _, hTeEnd⟩ := hExpT
  set eT := readTriples mem (mem (tD + 3)) (mem (tD + 2))
  have heT_len_eq : eT.length = mem (tD + 2) := by simp [eT, readTriples]
  have hmT2 : st8.mem (tD + 2) = eT.length := by rw [hbelow8 (tD + 2) (by omega), heT_len_eq]
  have hmT3 : st8.mem (tD + 3) = mem (tD + 3) := hbelow8 (tD + 3) (by omega)
  have hr26b : Runs w p ω (.assign 26 (.load (.bin .add (.reg 5) (.const 2)))) st8 .normal
      { st8 with regs := Function.update st8.regs 26 eT.length } 5 :=
    runs_assign_iff.mpr ⟨eT.length, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq hregs8.r5) (Expr.eval_const (by omega)) (by omega)) hmT2,
      rfl, rfl, by simp [Expr.size]⟩
  set st8a := { st8 with regs := Function.update st8.regs 26 eT.length }
  have hr27b : Runs w p ω (.assign 27 (.load (.bin .add (.reg 5) (.const 3)))) st8a .normal
      { st8a with regs := Function.update st8a.regs 27 (mem (tD + 3)) } 5 :=
    runs_assign_iff.mpr ⟨mem (tD + 3), Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st8a, hregs8.r5])) (Expr.eval_const (by omega)) (by omega))
      hmT3, rfl, rfl, by simp [Expr.size]⟩
  set st8b := { st8a with regs := Function.update st8a.regs 27 (mem (tD + 3)) }
  have hC9 := runs_call_of_meetsContract (r := 28)
    (splitTreeEdges_meetsContract (vCap := vCap) (eCap := eCap) (tCap := tCap)
      (G := v.G) (T := v.lsf.T) (eT := eT) hpInitOps hpEdge hpOps)
    (show evalArgs w st8b [.reg 20, .reg 23, .reg 24, .reg 27, .reg 26] =
        some [qg, live, frz, mem (tD + 3), eT.length] by
      simp [evalArgs, Expr.eval, st8b, st8a, hregs8.r20, hregs8.r23, hregs8.r24])
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro z (rfl|rfl|rfl|rfl|rfl)
        exacts [hqgW, hliveW, hfrzW, by omega, by omega])
    ⟨qg, live, frz, mem (tD + 3), rfl, hw16, by omega, by omega, by omega, by omega,
      fun i hi => by
        have hi' : i < mem (tD + 2) := heT_len_eq ▸ hi
        simp only [eT, readTriples, List.getElem_map, List.getElem_range]
        exact ⟨hbelow8 _ (by omega), hbelow8 _ (by omega), hbelow8 _ (by omega)⟩,
      hTnd, hTspec, hTcov, hAgree, hTeCap, hG8, hL8, hF8⟩ ω
  obtain ⟨st9, c9, _, hr9, ⟨_, _, _, _, hEq9, _, hLive9, hFrz9, hfr9⟩, _, hregs9, hc9⟩ := hC9
  simp only [List.cons.injEq, and_true] at hEq9; obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq9
  rw [hDe, hfrz, hDt, hhEnd] at hfr9
  have hret9 : st9.regs 25 = hEnd := by rw [hregs9 25 (by decide)]; simp [st8b, st8a, hregs8.r25]
  have hrRet : Runs w p ω (.ret (.reg 25)) st9 (.returned hEnd) st9 2 :=
    runs_ret_iff.mpr ⟨hEnd, Expr.eval_reg_of_eq hret9, rfl, rfl, by simp [Expr.size]⟩
  have hS13 := runs_seq_iff.mpr (Or.inr ⟨st9, c9, 2, hr9, hrRet, rfl⟩)
  have hS12 := runs_seq_iff.mpr (Or.inr ⟨st8b, 5, _, hr27b, hS13, rfl⟩)
  have hS11 := runs_seq_iff.mpr (Or.inr ⟨st8a, 5, _, hr26b, hS12, rfl⟩)
  refine ⟨.returned hEnd, st9, _, hS11, rfl, hLive9, hFrz9,
    fun a ha => by rw [hfr9 a (Or.inr (by omega)) (Or.inr ha)]; exact hz8 a ha,
    fun a ha => hfr9 a (Or.inl ha) (Or.inl (by omega)), ?_⟩
  dsimp only [splitTreeEdgesContract, argsSize, Expr.size] at hc9
  rw [heT_len_eq, hTm] at hc9; omega

/-- **Branch initialization (`readInitStmt`).** From `ReadInitAt` below `h` and `v.Inv`, builds the
complete `11`-word record (`ReadRecAt`, `mem (h + 9) = live`, `mem (h + 10) = frz`, `liveT`,
`frozenT`) in contiguous layout `readInitPtrs h vCap eCap tCap L_w`, leaves `mem` untouched below
`h`, leaves `ZeroFrom` at `hEnd`, allocates `hEnd - h ≤ readSpace 60 vCap tCap L_w (readInitSize v)`,
and satisfies `c + 1000 * treePot v.G v.lsf.T ≤ 3100 * (readInitSize v + 1) * (L_w + 1)`. -/
theorem readInit_runs {w vCap eCap tCap L_w P : ℕ} {p : Program}
    {bOps bEdge bSplit bBatch bLoop bInitOps bSelf : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpLoop : p.HasAt bLoop (readLoopProcs bEdge))
    (hpInitOps : p.HasAt bInitOps (readInitOpsProcs bEdge))
    (hpSelf : p.HasAt bSelf (readInitProcs bBatch bLoop bInitOps bSelf))
    {gD tD fD rootsPtr nR numPtr denPtr sD h : ℕ} {v : ReadView}
    {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hLwW : L_w < 2 ^ w)
    (hargsW : ∀ a ∈ [gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h], a < 2 ^ w)
    (hInit : ReadInitAt mem h L_w gD tD fD rootsPtr nR numPtr denPtr sD v)
    (hInv : v.Inv vCap eCap tCap) (hz : ZeroFrom mem h)
    (hroom : h + (readInitPtrs 0 vCap eCap tCap L_w).2.2.2 < 2 ^ w) :
    let (q, live, frz, hEnd) := readInitPtrs h vCap eCap tCap L_w
    ∃ o st' c,
      Runs w p ω (readInitStmt bLoop bInitOps bSelf)
        (startState [vCap, eCap, tCap, L_w, gD, tD, fD, rootsPtr, nR, numPtr, denPtr, sD, h] mem pos)
        o st' c ∧
      o.value = hEnd ∧
      ReadRecAt st'.mem h vCap eCap tCap L_w P v q ∧
      st'.mem (h + 9) = live ∧ st'.mem (h + 10) = frz ∧
      DynGraphAt st'.mem live vCap eCap (liveT v.G v.lsf.T) ∧
      DynGraphAt st'.mem frz vCap tCap (frozenT v.G v.lsf.T) ∧
      ZeroFrom st'.mem hEnd ∧ (∀ a < h, st'.mem a = mem a) ∧
      c + 1000 * treePot v.G v.lsf.T ≤ 3100 * (readInitSize v + 1) * (L_w + 1) := by
  dsimp only [readInitPtrs]
  generalize hDt : dynGraphSize vCap tCap = Dt
  generalize hDe : dynGraphSize vCap eCap = De
  generalize hqt : h + 11 = qt
  generalize hqf : qt + Dt = qf
  generalize hqroots : qf + Dt = qroots
  generalize hqs : qroots + vCap = qs
  generalize hqg : qs + De = qg
  generalize hqnum : qg + De = qnum
  generalize hqden : qnum + eCap * L_w = qden
  generalize hlive : qden + eCap * L_w = live
  generalize hfrz : live + De = frz
  generalize hhEnd : frz + Dt = hEnd
  have hhEnd_lt : hEnd < 2 ^ w := by
    dsimp only [readInitPtrs] at hroom; rw [hDt, hDe] at hroom; omega
  clear hroom
  obtain ⟨st5, c1, hr1, hregs5, hhdr5, hT5, hF5, hR5, hS5, hG5, hz5, hbelow5, hc1⟩ :=
    readInitPart1_runs hpOps hpEdge hpBatch hpLoop hpSelf hw16 hDt hDe hqt hqf hqroots hqs hqg
      hqnum hqden hlive hfrz hhEnd hhEnd_lt hargsW hInit hInv hz (pos := pos) (ω := ω)
  obtain ⟨st8, c2a, hr2a, hregs8_eq, hcopy8, hG8, hL8, hF8, hz8, hpres8, hc2a⟩ :=
    readInitPart2a_runs hpOps hpEdge hpBatch hpInitOps hpSelf hw16 hLwW hDt hDe hqt hqf hqroots hqs
      hqg hqnum hqden hlive hfrz hhEnd hhEnd_lt (hargsW _ (by simp)) (hargsW _ (by simp))
      (hargsW _ (by simp)) hInit.1 hInit.2.2.2.2.2.1 hInv.2.1 hInv.2.2.1 hregs5 hG5 hz5 hbelow5
  have hregs8 : ReadInitRegs st8.regs vCap eCap tCap L_w gD tD fD rootsPtr nR numPtr denPtr sD h
      qt qf qroots qs qg qnum qden live frz hEnd :=
    ⟨(hregs8_eq 0 (by decide)).trans hregs5.r0, (hregs8_eq 1 (by decide)).trans hregs5.r1,
     (hregs8_eq 2 (by decide)).trans hregs5.r2, (hregs8_eq 3 (by decide)).trans hregs5.r3,
     (hregs8_eq 4 (by decide)).trans hregs5.r4, (hregs8_eq 5 (by decide)).trans hregs5.r5,
     (hregs8_eq 6 (by decide)).trans hregs5.r6, (hregs8_eq 7 (by decide)).trans hregs5.r7,
     (hregs8_eq 8 (by decide)).trans hregs5.r8, (hregs8_eq 9 (by decide)).trans hregs5.r9,
     (hregs8_eq 10 (by decide)).trans hregs5.r10, (hregs8_eq 11 (by decide)).trans hregs5.r11,
     (hregs8_eq 12 (by decide)).trans hregs5.r12, (hregs8_eq 16 (by decide)).trans hregs5.r16,
     (hregs8_eq 17 (by decide)).trans hregs5.r17, (hregs8_eq 18 (by decide)).trans hregs5.r18,
     (hregs8_eq 19 (by decide)).trans hregs5.r19, (hregs8_eq 20 (by decide)).trans hregs5.r20,
     (hregs8_eq 21 (by decide)).trans hregs5.r21, (hregs8_eq 22 (by decide)).trans hregs5.r22,
     (hregs8_eq 23 (by decide)).trans hregs5.r23, (hregs8_eq 24 (by decide)).trans hregs5.r24,
     (hregs8_eq 25 (by decide)).trans hregs5.r25⟩
  obtain ⟨o, st9, c2b, hr2b, ho, hLive9, hFrz9, hz9, hpres9, hc2b⟩ :=
    readInitPart2b_runs hpOps hpEdge hpInitOps hw16 hDt hDe hqt hqf hqroots hqs hqg hqnum hqden
      hlive hfrz hhEnd hhEnd_lt hInit.2.1 (hargsW _ (by simp))
      ⟨hInv.1, hInv.2.2.2.2.1, hInv.2.2.2.2.2.1, hInv.2.2.2.2.2.2.2.1⟩ hInv.2.2.2.2.2.2.1
      hregs8 hG8 hL8 hF8 hz8 (fun a ha => (hpres8 a (by omega)).trans (hbelow5 a ha))
  have hfull := runs_seq_iff.mpr (Or.inr ⟨st5, c1, _, hr1,
    runs_seq_iff.mpr (Or.inr ⟨st8, c2a, c2b, hr2a, hr2b, rfl⟩), rfl⟩)
  have hpres : ∀ a < qnum, st9.mem a = st5.mem a := fun a ha =>
    (hpres9 a (by omega)).trans (hpres8 a ha)
  have hcopy9 : ∀ e ∈ v.G.E, ∀ k < L_w,
      st9.mem (qnum + e * L_w + k) = mem (numPtr + e * L_w + k) ∧
      st9.mem (qden + e * L_w + k) = mem (denPtr + e * L_w + k) := by
    intro e he k hk
    have heCap := hInv.2.2.1 e he
    have he_mul : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right L_w (by omega)
    rw [Nat.add_mul, one_mul] at he_mul
    rw [hpres9 _ (by omega), hpres9 _ (by omega)]
    exact hcopy8 e he k hk
  obtain ⟨hStrV, hStrP⟩ := stretch_of_copy (P := P) (v := v)
    ((hpres (h + 7) (by omega)).trans hhdr5.h7) ((hpres (h + 8) (by omega)).trans hhdr5.h8)
    hInit.2.2.2.2.2.2 hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hcopy9
  have hR9 : RootsAt st9.mem qroots vCap v.lsf.F.R :=
    ⟨hR5.1, fun x hx => by rw [hpres (qroots + x) (by omega)]; exact hR5.2 x hx⟩
  have hRec9 : ReadRecAt st9.mem h vCap eCap tCap L_w P v ⟨qt, qf, qroots, qs, qg, qnum, qden⟩ :=
    ⟨(hpres h (by omega)).trans hhdr5.h0, (hpres (h + 1) (by omega)).trans hhdr5.h1,
     (hpres (h + 2) (by omega)).trans hhdr5.h2, (hpres (h + 3) (by omega)).trans hhdr5.h3,
     (hpres (h + 4) (by omega)).trans hhdr5.h4, (hpres (h + 5) (by omega)).trans hhdr5.h5,
     (hpres (h + 6) (by omega)).trans hhdr5.h6, (hpres (h + 7) (by omega)).trans hhdr5.h7,
     (hpres (h + 8) (by omega)).trans hhdr5.h8,
     hT5.of_agree fun a _ ha2 => hpres a (by omega),
     hF5.of_agree fun a _ ha2 => hpres a (by omega),
     hR9, hStrV, hStrP,
     hS5.of_agree fun a _ ha2 => hpres a (by omega),
     hG5.of_agree fun a _ ha2 => hpres a (by omega)⟩
  refine ⟨o, st9, _, hfull, ho, hRec9,
    (hpres (h + 9) (by omega)).trans hhdr5.h9, (hpres (h + 10) (by omega)).trans hhdr5.h10,
    hLive9, hFrz9, hz9, fun a ha => (hpres a (by omega)).trans (hbelow5 a ha), ?_⟩
  have hpot : 1000 * treePot v.G v.lsf.T ≤ 2000 * v.lsf.T.m := by
    have := treePot_le (T := v.lsf.T) hInv.1; dsimp [MGraph.m]; omega
  have hLw1 : 1 ≤ L_w + 1 := by omega
  have hGmul : 55 * v.G.m * (L_w + 1) ≤ 55 * readInitSize v * (L_w + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by dsimp [readInitSize]; omega))
  have hcomb : 3045 * (readInitSize v + 1) + 55 * readInitSize v * (L_w + 1) ≤
      3100 * (readInitSize v + 1) * (L_w + 1) := by
    have h1 : 3045 * (readInitSize v + 1) ≤ 3045 * (readInitSize v + 1) * (L_w + 1) :=
      Nat.le_mul_of_pos_right _ hLw1
    have h2 : 55 * readInitSize v * (L_w + 1) ≤ 55 * (readInitSize v + 1) * (L_w + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have h3 : 3045 * (readInitSize v + 1) * (L_w + 1) + 55 * (readInitSize v + 1) * (L_w + 1) =
        3100 * (readInitSize v + 1) * (L_w + 1) := by ring
    omega
  dsimp only [readInitSize] at hGmul hcomb ⊢
  omega

end MinCostFlow.SparseCore.Program.Read
