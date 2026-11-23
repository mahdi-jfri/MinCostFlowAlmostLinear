module

public import MinCostFlow.HierPaths.InitProgFlatChain
public import MinCostFlow.HierPaths.InitProgProject
public import MinCostFlow.HierPaths.InitProgMove

/-!
# Projecting one stored connector

Copy the local walk into a length-prefixed buffer, flatten it, and project one
column. Then move the column down to its destination and clear the temporary
lists. All work above the produced column is reclaimed before the next call.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- The arguments give the hierarchy, connector endpoints and local edge list,
the three root table addresses, and the destination. -/
def initConnProject (copy chain proj move : ℕ) : Stmt :=
  .call 15 copy [.bin .add (.reg 14) (.const 1), .reg 9, .reg 10] ;;
  .store (.reg 14) (.reg 10) ;;
  .call 16 chain [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
    .reg 14, .reg 15] ;;
  .assign 17 (.load (.reg 16)) ;;
  .assign 18 (.bin .add (.reg 15) (.bin .sub
    (.bin .add (.bin .add (.reg 16) (.const 1)) (.reg 17)) (.reg 15))) ;;
  .call 19 proj [.reg 11, .reg 12, .reg 13, .bin .add (.reg 16) (.const 1), .reg 17,
    .reg 7, .reg 18, .reg 8] ;;
  .call 20 move [.reg 14, .reg 18, .reg 19] ;;
  .ret (.reg 20)

theorem initConnProject_noRand (copy chain proj move : ℕ) :
    (initConnProject copy chain proj move).NoRand := by simp [initConnProject, Stmt.NoRand]

/-- The scratch includes the local walk, the successive ancestor walks, and
one projected column before the column is moved down. -/
def initConnProjectRoom (S : StaticData) (verts : Bool) (t g u : ℕ) (es : List ℕ) : ℕ :=
  let flat := flatWalk S.H S.x S.b t g u es
  1 + es.length + initFlatScratch S t g u es + (initProjectedColumn S verts u flat).length

/-- The root data required by both projections. -/
def InitRootAt (w : ℕ) (S : StaticData) (G : Graph) (mem : ℕ → ℕ)
    (host L O dst : ℕ) : Prop :=
  let J := S.H.host 0 0
  GraphAt mem host J ∧ host + J.encode.length ≤ dst ∧ L + J.m ≤ dst ∧
    O + S.numTerm ≤ dst ∧
    (∀ e < J.m, mem (L + e) = labelWord (S.label e)) ∧
    (∀ t < S.numTerm, mem (O + t) = S.owner t ∧ S.owner t < 2 ^ w) ∧
    IsProjection G J.edges S.owner S.label ∧ G.m < 2 ^ w

/-- The projected column is followed by zeros and all earlier cells are preserved. -/
def initConnProjectContract (w : ℕ) (S : StaticData) (G : Graph) (verts : Bool)
    (t g u v : ℕ) (es : List ℕ) : Contract where
  pre args mem := ∃ h src host L O dst, args =
    [h, S.numTerm, leafDepth S.x S.b, S.x, S.b, t, g, u, v, src, es.length, host, L, O, dst] ∧
    StaticOut mem h S ∧ ListAt mem src es ∧ src + es.length ≤ dst ∧ h + S.encode.length ≤ dst ∧
    InitRootAt w S G mem host L O dst ∧ ZeroFrom mem dst ∧
    dst + initConnProjectRoom S verts t g u es < 2 ^ w ∧ leafDepth S.x S.b + 1 < 2 ^ w ∧
    0 < S.b ∧ S.H.IsValid S.x S.b ∧ t ≤ leafDepth S.x S.b ∧ 1 < groupSize S.x S.b t ∧
    g < numGroups S.x S.b t ∧ u < S.numTerm ∧ v < S.numTerm ∧
    IsEdgeWalk (S.H.host t g).edges u v es
  post args mem r mem' := ∃ h src host L O dst, args =
    [h, S.numTerm, leafDepth S.x S.b, S.x, S.b, t, g, u, v, src, es.length, host, L, O, dst] ∧
    let col := initProjectedColumn S verts u (flatWalk S.H S.x S.b t g u es)
    r = dst + col.length ∧ ListAt mem' dst col ∧ ZeroFrom mem' r ∧
    ∀ y < dst, mem' y = mem y
  cost _ _ := initFlatChainCost S t g u es + 100 * (flatWalk S.H S.x S.b t g u es).length +
    40 * initConnProjectRoom S verts t g u es + 250

theorem initConnProject_meetsContract {w f copy chain proj move t g u v : ℕ}
    {S : StaticData} {G : Graph} {es : List ℕ} {verts : Bool} {p : Program}
    (hp : p.procs[f]? = some (initConnProject copy chain proj move))
    (hCopy : MeetsContract w p copy (copyUpContract w))
    (hChain : MeetsContract w p chain (initFlatChainContract w S t g u v es))
    (hProj : MeetsContract w p proj
      (initProjectContract w S G verts u v (flatWalk S.H S.x S.b t g u es)))
    (hMove : MeetsContract w p move (moveDownContract w)) :
    MeetsContract w p f (initConnProjectContract w S G verts t g u v es) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨h, src, host, L, O, dst, rfl, hS, hes, hsrc, hsep, hroot, hz, hroom, hD,
    hb, hH, ht, hgsize, hg, hu, hv, hW⟩ := hpre
  let D := leafDepth S.x S.b
  let J := S.H.host 0 0
  let flat := flatWalk S.H S.x S.b t g u es
  let col := initProjectedColumn S verts u flat
  let buf := dst + 1 + es.length
  let q := buf + initFlatScratch S t g u es
  let fin := q + col.length
  have hfinEq : fin = dst + initConnProjectRoom S verts t g u es := by
    simp [fin, q, buf, initConnProjectRoom, flat, col, Nat.add_assoc]
  rw [← hfinEq] at hroom
  have hdq : dst ≤ q := by dsimp [q, buf]; omega
  have hqf : q ≤ fin := Nat.le_add_right _ _
  have hqw : q < 2 ^ w := hqf.trans_lt hroom
  have hbq : buf ≤ q := Nat.le_add_right _ _
  have hbw : buf < 2 ^ w := hbq.trans_lt hqw
  have hd1 : dst + 1 < 2 ^ w := by dsimp [buf] at hbw; omega
  have h1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold initConnProject
  refine runs_seq_call_le hCopy (vs := [dst + 1, src, es.length]) ?_ ?_
    ⟨dst + 1, src, es.length, rfl, by omega, hbw, h1⟩ ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, h1, hd1]
  · intro z hz'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with rfl | rfl | rfl
    · exact hd1
    · exact hw _ (by simp)
    · exact hw _ (by simp)
  intro r mem₁ pos₁ hp₁
  obtain ⟨dst', src', len', ha, hr, hcp, hf₁⟩ := hp₁
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨hd', hs', hl'⟩ := ha
  subst dst' src' len' r
  let mem₂ := Function.update mem₁ dst es.length
  have hbuf : ListAt mem₂ dst (es.length :: es) := by
    apply listAt_cons.mpr
    refine ⟨Function.update_self .., fun i hi => ?_⟩
    rw [show mem₂ (dst + 1 + i) = mem₁ (dst + 1 + i) from Function.update_of_ne (by omega) _ _]
    exact (hcp i hi).trans (hes i hi)
  have hf₂ (y : ℕ) (hy : y < dst ∨ buf ≤ y) : mem₂ y = mem y := by
    have hd : dst + 1 ≤ buf := Nat.le_add_right _ _
    exact (Function.update_of_ne (by omega) _ _).trans (hf₁ y (by omega))
  have hS₂ : StaticOut mem₂ h S :=
    listAt_congr (fun k hk => (hf₂ _ (.inl (by omega))).symm) hS
  refine runs_seq_store_le (x := dst) (v := es.length)
    (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) ?_
  refine runs_seq_call_le hChain (vs := [h, S.numTerm, D, S.x, S.b, t, g, u, dst, buf]) rfl ?_
    ⟨h, dst, buf, rfl, hS₂, hbuf, hsep.trans (by dsimp [buf]; omega), le_rfl,
      hqw, hD, hb, hH, ht, hgsize, hg, hW⟩ ?_
  · intro z hz'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hbw | exact hw _ (by simp [D])
  intro r mem₃ pos₃ hp₃
  obtain ⟨h', src', buf', ha, hr, hflat, hf₃⟩ := hp₃
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, _, _, _, _, hd', hb'⟩ := ha
  subst src' buf'
  change ListAt mem₃ r (flat.length :: flat) at hflat
  change ∀ y, y < buf ∨ q ≤ y → mem₃ y = mem₂ y at hf₃
  have hrd : r + 1 + flat.length ≤ q := by
    by_cases h0 : t = 0
    · have hr' : r = dst := by simpa only [h0, ↓reduceIte] using hr
      subst r
      simp [q, buf, flat, h0, initFlatScratch, flatWalk]
    · have hr' : r + 1 + flat.length = q := by simpa only [h0, ↓reduceIte] using hr
      exact hr'.le
  have hmax : buf + (r + 1 + flat.length - buf) = q := by
    by_cases h0 : t = 0
    · simp [q, initFlatScratch, h0] at hrd ⊢
      omega
    · have hr' : r + 1 + flat.length = q := by simpa only [h0, ↓reduceIte] using hr
      omega
  have hflatList := (listAt_cons.mp hflat).2
  have hflatLen := (listAt_cons.mp hflat).1
  have hf₄ (y : ℕ) (hy : y < dst ∨ q ≤ y) : mem₃ y = mem y := by
    exact (hf₃ y (by dsimp [buf] at *; omega)).trans (hf₂ y (by omega))
  obtain ⟨hHost, hhst, hL, hO, hLabel, hOwners, hProjOk, hGm⟩ := hroot
  have hProjW : IsEdgeWalk J.edges u v flat := flatWalk_isEdgeWalk hH hgsize hg hW
  have hProjEdges : ∀ e ∈ flat, e < J.m ∧ labelWord (S.label e) < 2 ^ w ∧
      (edgeAt J.edges e).1 < S.numTerm ∧ (edgeAt J.edges e).2 < S.numTerm := by
    intro e he
    have hi := hProjW.lt_length e he
    have hzSize : 1 < groupSize S.x S.b 0 := hgsize.trans_le (groupSize_le_of_le (Nat.zero_le _))
    have hzGroup : 0 < numGroups S.x S.b 0 := Nat.two_pow_pos _
    have hin := hH.host_inside 0 0 hzSize hzGroup e hi
    simp only [insideB, Bool.and_eq_true, decide_eq_true_eq] at hin
    refine ⟨hi, ?_, Finset.mem_range.mp (members_subset_range hzGroup hin.1),
      Finset.mem_range.mp (members_subset_range hzGroup hin.2)⟩
    cases hl : S.label e with
    | none => exact Nat.two_pow_pos w
    | some k =>
      have hl' := ((hProjOk e hi).2.2.2 k hl).1
      change k + 1 < 2 ^ w
      exact lt_of_le_of_lt hl' hGm
  have hprefix : (initProjectWords S verts u flat).length ≤ col.length := by
    cases verts
    · change (initProjectWords S false u flat).length ≤ (projectWalk J.edges S.owner S.label u flat).edges.length
      rw [initProjectWords_edges, edges_projectWalk]
    · rw [show col = (projectWalk J.edges S.owner S.label u flat).verts from rfl,
        initProjectWords_verts hProjOk hProjW]
      split
      · rename_i he
        simp_all
      · simp
  have hcw : q + (initProjectWords S verts u flat).length < 2 ^ w :=
    (Nat.add_le_add_left hprefix q).trans_lt hroom
  have hProjPre : (initProjectPassContract w S verts u flat).pre
      [host, L, O, r + 1, flat.length, u, q] mem₃ := by
    refine ⟨host, L, O, r + 1, q, rfl,
      listAt_congr (fun i hi => (hf₄ _ (.inl (by omega))).symm) hHost,
      hflatList, hhst.trans hdq, hrd, hL.trans hdq, hO.trans hdq, ?_, ?_, hProjEdges,
      hu, h1, hcw⟩
    · intro e he
      exact (hf₄ _ (.inl (by omega))).trans (hLabel e he)
    · intro i hi
      exact ⟨(hf₄ _ (.inl (by omega))).trans (hOwners i hi).1, (hOwners i hi).2⟩
  have hr1 : r + 1 < 2 ^ w := by omega
  have hr2 : r + 1 + flat.length < 2 ^ w := hrd.trans_lt hqw
  have hflw : flat.length < 2 ^ w := by omega
  refine runs_seq_assign_le (v := flat.length) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq rfl) hflatLen) ?_
  refine runs_seq_assign_le (v := q) ?_ ?_
  · exact Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (v := buf) rfl)
        (Expr.eval_sub (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := r) rfl)
          (Expr.eval_const h1) hr1) (Expr.eval_reg_of_eq (v := flat.length) rfl) hr2)
          (Expr.eval_reg_of_eq (v := buf) rfl) hr2) (hmax ▸ hqw)) hmax
  refine runs_seq_call_le hProj (vs := [host, L, O, r + 1, flat.length, u, q, v]) ?_ ?_
    ⟨host, L, O, r + 1, q, rfl, hProjPre, hProjOk, hProjW, hv, hroom⟩ ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, h1, hr1]
  · intro z hz'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | exact hw _ (by simp)
  intro z mem₄ pos₄ hp₄
  obtain ⟨host', L', O', src', q', ha, hfin, hcol, hf₅⟩ := hp₄
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, _, _, hq', _⟩ := ha
  subst z
  change ∀ y, y < q ∨ fin ≤ y → mem₄ y = mem₃ y at hf₅
  refine runs_seq_call_le hMove (vs := [dst, q, fin]) rfl ?_
    ⟨dst, q, fin, rfl, hdq, hqf, hroom, h1⟩ ?_
  · intro z hz'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hqw
    · exact hroom
  intro out mem₅ pos₅ hp₅
  obtain ⟨dst', src', end', ha, hout, hres, hbelow, hzero, habove⟩ := hp₅
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨hd', hs', he'⟩ := ha
  subst dst' src' end'
  have hlen : fin - q = col.length := Nat.add_sub_cancel_left _ _
  rw [hlen] at hout hres hzero
  refine runs_ret_le (v := out) (Expr.eval_reg_of_eq rfl)
    ⟨h, src, host, L, O, dst, rfl, hout, ?_, ?_, ?_⟩ ?_
  · intro k hk
    exact (hres k hk).trans (hcol k hk)
  · intro y hy
    change out ≤ y at hy
    rcases Nat.lt_or_ge y fin with hy' | hy'
    · exact hzero y (hout ▸ hy) hy'
    · exact (habove y hy').trans ((hf₅ y (.inr hy')).trans
        ((hf₄ y (.inr (hqf.trans hy'))).trans (hz y (hdq.trans (hqf.trans hy')))))
  · intro y hy
    exact (hbelow y hy).trans ((hf₅ y (.inl (hy.trans_le hdq))).trans (hf₄ y (.inl hy)))
  · have he : fin - dst = initConnProjectRoom S verts t g u es := by
      dsimp [fin, q, buf, initConnProjectRoom, flat, col]
      omega
    have hs : es.length ≤ initConnProjectRoom S verts t g u es := by
      dsimp [initConnProjectRoom]
      omega
    simp [initConnProjectContract, copyUpContract, initFlatChainContract, initProjectContract,
      moveDownContract, argsSize, Expr.size, he, flat]
    omega

private theorem initProjectedColumn_length_le (S : StaticData) (verts : Bool) (u : ℕ)
    (es : List ℕ) : (initProjectedColumn S verts u es).length ≤ es.length + 1 := by
  cases verts
  · exact (length_projectWalk_le _ _ _ _ _).trans (Nat.le_succ _)
  · change (projectWalk (S.H.host 0 0).edges S.owner S.label u es).verts.length ≤ _
    induction es generalizing u with
    | nil => simp [projectWalk, Walk.empty]
    | cons e es ih =>
      rw [projectWalk]
      cases S.label e
      · exact (ih (otherEnd (S.H.host 0 0).edges e u)).trans (Nat.le_succ _)
      · simp only [Walk.append, Walk.single, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
        split
        · simp
        · simp only [List.cons_append, List.nil_append, List.length_cons, List.length_tail]
          have he := ih (otherEnd (S.H.host 0 0).edges e u)
          omega

private theorem initConnProject_input_le (S : StaticData) (t g u : ℕ) (es : List ℕ) :
    es.length ≤ flatSteps S.H S.x S.b t g u es +
      (flatWalk S.H S.x S.b t g u es).length := by
  cases t with
  | zero => simp [flatSteps, flatWalk]
  | succ j => rw [flatSteps, substSteps]; omega

/-- Scratch for one connector is at most a constant times its modeled edge work. -/
theorem initConnProjectRoom_le (S : StaticData) (verts : Bool) (t g u v : ℕ)
    (es : List ℕ) (hH : S.H.IsValid S.x S.b) (hs : 1 < groupSize S.x S.b t)
    (hg : g < numGroups S.x S.b t) (hne : u ≠ v)
    (hW : IsEdgeWalk (S.H.host t g).edges u v es) :
    initConnProjectRoom S verts t g u es ≤ 3 * flatSteps S.H S.x S.b t g u es +
      2 * (flatWalk S.H S.x S.b t g u es).length + 2 := by
  have hd := depth_le_flatSteps S hH hs hg hne hW
  have hscratch := initFlatScratch_le S t g u es
  have hin := initConnProject_input_le S t g u es
  have hcol := initProjectedColumn_length_le S verts u (flatWalk S.H S.x S.b t g u es)
  dsimp [initConnProjectRoom]
  omega

/-- The complete connector call uses a constant times the modeled edge work plus
one fixed charge per connector. -/
theorem initConnProject_cost_le (w : ℕ) (S : StaticData) (G : Graph) (verts : Bool)
    (t g u v : ℕ) (es args : List ℕ) (mem : ℕ → ℕ)
    (hH : S.H.IsValid S.x S.b) (hs : 1 < groupSize S.x S.b t)
    (hg : g < numGroups S.x S.b t) (hne : u ≠ v)
    (hW : IsEdgeWalk (S.H.host t g).edges u v es) :
    (initConnProjectContract w S G verts t g u v es).cost args mem ≤
      640 * (flatSteps S.H S.x S.b t g u es +
        (flatWalk S.H S.x S.b t g u es).length + 2) := by
  have hd := depth_le_flatSteps S hH hs hg hne hW
  have hr := initConnProjectRoom_le S verts t g u v es hH hs hg hne hW
  simp only [initConnProjectContract, initFlatChainCost]
  omega

end MinCostFlow.HierPaths

end
