module

public import MinCostFlow.HierPaths.BuildProgConnAll
public import MinCostFlow.HierPaths.BuildProgLevelTrace

/-!
# The level procedure for singleton children (`s = 1`)

When every child is a singleton, each child host has `G.n` vertices and no edges, and each child
embedding is empty. Write sections 0 and 1 in linear time in `k`, call `buildConnAllProc` to
write section 2, read `sec2.length` from its CSR header to fill the four top-level section
offsets, and return the bumped heap end.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Args are `buildLevelArgs gAddr xAddr start 1 k M r Δ L L' bh h`. -/
def buildSingletonProc (fConnAll : ℕ) : Stmt :=
  .assign 12 (.load (.reg 0)) ;;
  .assign 13 (.bin .add (.reg 11) (.const 4)) ;;
  .assign 14 (.bin .add (.bin .add (.reg 13) (.reg 4)) (.const 1)) ;;
  forRange 15 (.const 0) (.reg 4)
    (.store (.bin .add (.reg 13) (.reg 15)) (.bin .add (.reg 15) (.reg 15)) ;;
     .store (.bin .add (.reg 14) (.bin .add (.reg 15) (.reg 15))) (.reg 12)) ;;
  .store (.bin .add (.reg 13) (.reg 4)) (.bin .add (.reg 4) (.reg 4)) ;;
  .assign 16 (.bin .add (.reg 14) (.bin .add (.reg 4) (.reg 4))) ;;
  forRange 15 (.const 0) (.reg 4)
    (.store (.bin .add (.reg 16) (.reg 15)) (.reg 15)) ;;
  .store (.bin .add (.reg 16) (.reg 4)) (.reg 4) ;;
  .assign 17 (.bin .add (.bin .add (.bin .add (.reg 16) (.reg 4)) (.const 1)) (.reg 4)) ;;
  .assign 18 (.bin .mul (.bin .mul (.bin .mul (.const 32) (.reg 7)) (.reg 10)) (.reg 8)) ;;
  .call 19 fConnAll [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 7, .reg 8, .reg 18, .reg 17] ;;
  .assign 20 (.bin .mul (.reg 4) (.reg 4)) ;;
  .assign 20 (.bin .add (.bin .add (.bin .add (.reg 17) (.reg 20)) (.const 1))
    (.load (.bin .add (.reg 17) (.reg 20)))) ;;
  .store (.reg 11) (.const 0) ;;
  .store (.bin .add (.reg 11) (.const 1)) (.bin .sub (.reg 16) (.reg 13)) ;;
  .store (.bin .add (.reg 11) (.const 2)) (.bin .sub (.reg 17) (.reg 13)) ;;
  .store (.bin .add (.reg 11) (.const 3)) (.bin .sub (.reg 20) (.reg 13)) ;;
  .ret (.reg 19)

theorem buildSingletonProc_noRand (fConnAll : ℕ) : (buildSingletonProc fConnAll).NoRand := by
  simp [buildSingletonProc, forRange, forUp, Stmt.NoRand]

/-- Space needed by the singleton branch above `h`. -/
def singletonSpace (sR : ℕ → ℕ → ℕ → ℕ → ℕ) (G : Graph) (k Δ L bh : ℕ) : ℕ :=
  let d := routePathLen Δ bh L
  5 * k + 6 + connAllSpace sR G 1 k Δ L d + 1

/-- Contract for the singleton branch (`s = 1`). -/
def buildSingletonContract (w K C : ℕ) (route : RouterFn) (sR : ℕ → ℕ → ℕ → ℕ → ℕ)
    (G : Graph) (start k M r Δ L L' bh : ℕ) : Contract :=
  let X := buildLevelVerts start 1 k
  let D := levelDataOfFamily route G start 1 k Δ L (fun _ => [])
  { pre := fun args mem => ∃ g x h, args = buildLevelArgs g x start 1 k M r Δ L L' bh h ∧
      GraphAt mem g G ∧ ListAt mem x (finsetWords X) ∧
      g + G.encode.length ≤ h ∧ x + (finsetWords X).length ≤ h ∧ ZeroFrom mem h ∧
      G.IsValid ∧ HostPre G X Δ L ∧ 2 ≤ k ∧ start + k < 2 ^ w ∧ 32 < 2 ^ w ∧ G.n < 2 ^ w ∧
      h + singletonSpace sR G k Δ L bh < 2 ^ w ∧
      ∃ β : ℝ, 0 < β ∧ G.IsExpansionExpanderOn X β ∧ max 2 (2 / β) ≤ (bh : ℝ)
    post := fun args mem v after => ∃ g x h, args = buildLevelArgs g x start 1 k M r Δ L L' bh h ∧
      h + (D.encode k).length ≤ v ∧ v ≤ h + singletonSpace sR G k Δ L bh ∧
      ListAt after h (D.encode k) ∧
      (∀ j < h, after j = mem j) ∧ ZeroFrom after v ∧
      D.Good G start 1 k M r Δ L L' bh
    cost := fun _ _ => connAllCostBound K C G 1 k Δ L bh + 80 * k + 220 }

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

private theorem singleton_sec0_eq (route : RouterFn) (G : Graph) (start k Δ L : ℕ) :
    let D := levelDataOfFamily route G start 1 k Δ L (fun _ => [])
    csrList k (fun c => (D.host c).encode) = csrList k (fun _ => [G.n, 0]) := by
  simp [levelDataOfFamily, shiftEdges, Graph.encode, Graph.m]

private theorem singleton_sec1_eq (route : RouterFn) (G : Graph) (start k Δ L : ℕ) :
    let D := levelDataOfFamily route G start 1 k Δ L (fun _ => [])
    csrList k (fun c => csrList (D.host c).m (D.emb c)) = csrList k (fun _ => [0]) := by
  simp [levelDataOfFamily, shiftEdges, Graph.m, csrList, csrOffsets, csrData]

private theorem singleton_sec0_len (n k : ℕ) :
    (csrList k (fun _ => [n, 0])).length = 3 * k + 1 := by
  rw [csrList, List.length_append, length_csrOffsets, length_csrData_eq]
  simp [List.sum_replicate]; omega

private theorem singleton_sec1_len (k : ℕ) :
    (csrList k (fun _ => [0])).length = 2 * k + 1 := by
  rw [csrList, List.length_append, length_csrOffsets, length_csrData_eq]
  simp [List.sum_replicate]; omega

/-- `buildSingletonProc` builds the complete singleton-child level output at `h`. -/
theorem buildSingletonProc_meetsContract {w K C f fConnAll : ℕ} {p : Program}
    {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {start k M r Δ L L' bh : ℕ}
    (hf : p.procs[f]? = some (buildSingletonProc fConnAll))
    (hPlayer : IsMatchingPlayer route routeCost)
    (hConn : MeetsContract w p fConnAll (buildConnAllContract w K C route sR G start 1 k Δ L bh)) :
    MeetsContract w p f (buildSingletonContract w K C route sR G start k M r Δ L L' bh) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨g, x, h, rfl, hG, hX, hGE, hXE, hZ, hValid, hHost, hk2, hTermW, hw32, hGnW,
    hRoom, β, hPos, hExp, hBh⟩ := hPre
  let X := buildLevelVerts start 1 k
  let D := levelDataOfFamily route G start 1 k Δ L (fun _ => [])
  let d := routePathLen Δ bh L
  let sec0 := csrList k (fun _ => [G.n, 0])
  let sec1 := csrList k (fun _ => [0])
  let sec2 := csrList (k * k) (levelConnRow route G start 1 k Δ L)
  have hSec0Len : sec0.length = 3 * k + 1 := singleton_sec0_len G.n k
  have hSec1Len : sec1.length = 2 * k + 1 := singleton_sec1_len k
  let s0 := h + 4
  let d0 := s0 + k + 1
  let s1 := d0 + (k + k)
  let s2 := s1 + k + 1 + k
  have hS1eq : s1 = s0 + (3 * k + 1) := by dsimp [s1, d0, s0]; omega
  have hS2eq : s2 = s0 + (5 * k + 2) := by dsimp [s2, s1, d0, s0]; omega
  have hS2h : s2 = h + (5 * k + 6) := by dsimp [s2, s1, d0, s0]; omega
  have hRoomS2 : s2 + connAllSpace sR G 1 k Δ L d < 2 ^ w := by
    dsimp [singletonSpace] at hRoom
    change h + (5 * k + 6 + connAllSpace sR G 1 k Δ L d + 1) < 2 ^ w at hRoom
    omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hGHead : mem g = G.n := by
    have hlen : 0 < G.encode.length := by simp [Graph.encode]
    simpa [Graph.encode] using hG 0 hlen
  have hD_lt : d < 2 ^ w := by
    have hkk1 : 1 ≤ k * k := Nat.mul_pos (by omega) (by omega)
    have h1 : d ≤ (k * k) * connPairSpace sR G 1 k Δ L d := by
      have : d ≤ connPairSpace sR G 1 k Δ L d := by unfold connPairSpace; omega
      exact this.trans (Nat.le_mul_of_pos_left _ hkk1)
    dsimp [connAllSpace] at hRoomS2; omega
  have hΔpos : 1 ≤ Δ := hHost.2.2.1
  have hLpos : 1 ≤ L := hHost.2.2.2.2.1
  have hBhPos : 1 ≤ bh := by
    have : (2 : ℝ) ≤ (bh : ℝ) := (le_max_left 2 (2 / β)).trans hBh
    have h2 : 2 ≤ bh := by exact_mod_cast this
    omega
  have h32Δ : 32 * Δ < 2 ^ w := by
    have : 32 * Δ ≤ 32 * Δ * bh * L := by
      have h1 : 32 * Δ ≤ 32 * Δ * bh := Nat.le_mul_of_pos_right _ hBhPos
      exact h1.trans (Nat.le_mul_of_pos_right _ hLpos)
    exact lt_of_le_of_lt this hD_lt
  have h32Δb : 32 * Δ * bh < 2 ^ w := by
    have : 32 * Δ * bh ≤ 32 * Δ * bh * L := Nat.le_mul_of_pos_right _ hLpos
    exact lt_of_le_of_lt this hD_lt
  have hkW : k < 2 ^ w := hWords k (by simp [buildLevelArgs])
  have hS0W : s0 < 2 ^ w := by dsimp [s0, s2, s1, d0] at hRoomS2 ⊢; omega
  have hD0W : d0 < 2 ^ w := by dsimp [s0, s2, s1, d0] at hRoomS2 ⊢; omega
  have hS1W : s1 < 2 ^ w := by dsimp [s0, s2, s1, d0] at hRoomS2 ⊢; omega
  have hS2W : s2 < 2 ^ w := by dsimp [s0, s2, s1, d0] at hRoomS2 ⊢; omega
  have h2kW : k + k < 2 ^ w := by dsimp [s2, s1, d0, s0] at hRoomS2; omega
  -- Loop 1: write sec0
  let R1 (st : State) : Prop :=
    (∀ j < 12, st.regs j = (startState (buildLevelArgs g x start 1 k M r Δ L L' bh h) mem pos).regs j) ∧
    st.regs 12 = G.n ∧ st.regs 13 = s0 ∧ st.regs 14 = d0
  let Inv1 (i : ℕ) (st : State) : Prop :=
    R1 st ∧ st.regs 15 = i ∧
    (∀ j < i, st.mem (s0 + j) = 2 * j ∧ st.mem (d0 + 2 * j) = G.n ∧ st.mem (d0 + 2 * j + 1) = 0) ∧
    (∀ a < s0, st.mem a = mem a) ∧ ZeroFrom st.mem (d0 + 2 * i) ∧
    ∀ j, i ≤ j → j ≤ k → st.mem (s0 + j) = 0
  have hLoop1 := Triple.forRange_const (p := p) (r := 15) (lo := .const 0) (hi := .reg 4)
    (body :=
      .store (.bin .add (.reg 13) (.reg 15)) (.bin .add (.reg 15) (.reg 15)) ;;
      .store (.bin .add (.reg 14) (.bin .add (.reg 15) (.reg 15))) (.reg 12))
    (P := fun st => R1 st ∧ st.mem = mem) (Inv := Inv1) 24 0 k (Nat.zero_le _) hw1 (fun _ => hkW)
    (fun st ⟨hR, hm⟩ => by
      refine ⟨Expr.eval_const (Nat.two_pow_pos w), ?_, by simp, fun _ hj => (Nat.not_lt_zero _ hj).elim,
        fun _ _ => by simp [hm], fun y hy => by rw [hm]; exact hZ y (by dsimp [d0, s0] at hy; omega),
        fun j _ _ => by rw [hm]; exact hZ _ (by dsimp [s0]; omega)⟩
      refine ⟨fun j hj => ?_, by simp [hR.2.1], by simp [hR.2.2.1], by simp [hR.2.2.2]⟩
      have hne : j ≠ 15 := by omega
      simpa [Function.update_of_ne hne] using hR.1 j hj)
    (fun _ _ _ _ h => h.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using h.1.1 4 (by decide)))
    (fun i _ hi st ω' ⟨hR, h15, hAt, hFr, hZero, hRest⟩ => by
      have h2i : i + i < 2 ^ w := by omega
      have hs0i : s0 + i < 2 ^ w := by dsimp [s0, d0] at hD0W ⊢; omega
      have hd0i : d0 + (i + i) < 2 ^ w := by dsimp [s1, d0] at hS1W ⊢; omega
      refine runs_start_le ?_
      refine runs_seq_store_le (x := s0 + i) (v := i + i)
        (Expr.eval_add (Expr.eval_reg_of_eq hR.2.2.1) (Expr.eval_reg_of_eq h15) hs0i)
        (Expr.eval_add (Expr.eval_reg_of_eq h15) (Expr.eval_reg_of_eq h15) h2i) ?_
      refine runs_store_le (x := d0 + (i + i)) (v := G.n)
        (Expr.eval_add (Expr.eval_reg_of_eq hR.2.2.2)
          (Expr.eval_add (Expr.eval_reg_of_eq h15) (Expr.eval_reg_of_eq h15) h2i) hd0i)
        (Expr.eval_reg_of_eq hR.2.1) ?_ ?_
      · let m' := Function.update (Function.update st.mem (s0 + i) (i + i)) (d0 + (i + i)) G.n
        have hR' : R1 { mem := m', regs := Function.update st.regs 15 (i + 1), pos := st.pos } :=
          ⟨fun j hj => by simpa [Function.update_of_ne (by omega : j ≠ 15)] using hR.1 j hj,
            by simp [hR.2.1], by simp [hR.2.2.1], by simp [hR.2.2.2]⟩
        refine ⟨⟨hR', by simp, ?_, ?_, ?_, ?_⟩, by simp [h15]⟩
        · intro j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
          · obtain ⟨ha, hb, hc⟩ := hAt j hlt
            refine ⟨?_, ?_, ?_⟩
            · change m' (s0 + j) = 2 * j; dsimp only [m']
              rw [Function.update_of_ne (by dsimp [d0]; omega), Function.update_of_ne (by omega)]; exact ha
            · change m' (d0 + 2 * j) = G.n; dsimp only [m']
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by dsimp [d0]; omega)]; exact hb
            · change m' (d0 + 2 * j + 1) = 0; dsimp only [m']
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by dsimp [d0]; omega)]; exact hc
          · refine ⟨?_, ?_, ?_⟩
            · change m' (s0 + j) = 2 * j; dsimp only [m']
              rw [Function.update_of_ne (by dsimp [d0]; omega), Function.update_self]; omega
            · change m' (d0 + 2 * j) = G.n; dsimp only [m']
              rw [show d0 + 2 * j = d0 + (j + j) by omega, Function.update_self]
            · change m' (d0 + 2 * j + 1) = 0; dsimp only [m']
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by dsimp [d0]; omega)]
              exact hZero _ (by omega)
        · intro a ha
          change m' a = mem a; dsimp only [m']
          rw [Function.update_of_ne (by dsimp [d0]; omega), Function.update_of_ne (by omega)]
          exact hFr a ha
        · intro a ha
          change m' a = 0; dsimp only [m']
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by dsimp [d0]; omega)]
          exact hZero a (by omega)
        · intro j hj1 hj2
          change m' (s0 + j) = 0; dsimp only [m']
          rw [Function.update_of_ne (by dsimp [d0]; omega), Function.update_of_ne (by omega)]
          exact hRest j (by omega) hj2
      · simp [Expr.size])
  -- Loop 2: write sec1 offsets
  let Inv2 (i : ℕ) (st : State) : Prop :=
    R1 st ∧ st.regs 16 = s1 ∧ st.regs 15 = i ∧
    ListAt st.mem s0 sec0 ∧ (∀ a < s0, st.mem a = mem a) ∧
    (∀ j < i, st.mem (s1 + j) = j) ∧ ZeroFrom st.mem (s1 + i)
  have hLoop2 := Triple.forRange_const (p := p) (r := 15) (lo := .const 0) (hi := .reg 4)
    (body := .store (.bin .add (.reg 16) (.reg 15)) (.reg 15))
    (P := fun st => R1 st ∧ st.regs 16 = s1 ∧ ListAt st.mem s0 sec0 ∧
      (∀ a < s0, st.mem a = mem a) ∧ ZeroFrom st.mem s1)
    (Inv := Inv2) 10 0 k (Nat.zero_le _) hw1 (fun _ => hkW)
    (fun st ⟨hR, h16, hSec0, hFr, hZero⟩ => by
      refine ⟨Expr.eval_const (Nat.two_pow_pos w), ?_, by simp [h16], by simp, hSec0, hFr,
        fun _ hj => (Nat.not_lt_zero _ hj).elim, by simpa using hZero⟩
      refine ⟨fun j hj => ?_, by simp [hR.2.1], by simp [hR.2.2.1], by simp [hR.2.2.2]⟩
      have hne : j ≠ 15 := by omega
      simpa [Function.update_of_ne hne] using hR.1 j hj)
    (fun _ _ _ _ h => h.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using h.1.1 4 (by decide)))
    (fun i _ hi st ω' ⟨hR, h16, h15, hSec0, hFr, hAt, hZero⟩ => by
      have hs1i : s1 + i < 2 ^ w := by dsimp [s2] at hS2W; omega
      refine runs_start_le ?_
      refine runs_store_le (x := s1 + i) (v := i)
        (Expr.eval_add (Expr.eval_reg_of_eq h16) (Expr.eval_reg_of_eq h15) hs1i)
        (Expr.eval_reg_of_eq h15) ?_ ?_
      · have hR' : R1 ⟨Function.update st.mem (s1 + i) i, Function.update st.regs 15 (i + 1), st.pos⟩ :=
          ⟨fun j hj => by simpa [Function.update_of_ne (by omega : j ≠ 15)] using hR.1 j hj,
            by simp [hR.2.1], by simp [hR.2.2.1], by simp [hR.2.2.2]⟩
        refine ⟨⟨hR', by simp [h16], by simp, ?_, ?_, ?_, ?_⟩, by simp [h15]⟩
        · exact WordRAM.ListAt.congr hSec0 fun a _ ha =>
            Function.update_of_ne (by rw [hSec0Len] at ha; omega) _ _
        · intro a ha
          exact (Function.update_of_ne (by omega) _ _).trans (hFr a ha)
        · intro j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
          · exact (Function.update_of_ne (by omega) _ _).trans (hAt j hlt)
          · simp
        · intro a ha
          exact (Function.update_of_ne (by omega) _ _).trans (hZero a (by omega))
      · simp [Expr.size])
  -- Chain everything
  refine runs_start_le ?_
  unfold buildSingletonProc
  refine runs_seq_assign_le (v := G.n)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs])) hGHead) ?_
  refine runs_seq_assign_le (v := s0)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs]))
      (Expr.eval_const hw4) hS0W) ?_
  refine runs_seq_assign_le (v := d0)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_reg_of_eq (by simp [startState, buildLevelArgs])) (by dsimp [d0] at hD0W; omega))
      (Expr.eval_const hw1) hD0W) ?_
  refine runs_seq_triple_le hLoop1
    ⟨⟨fun j hj => by
        simp [Function.update_of_ne (by omega : j ≠ 14), Function.update_of_ne (by omega : j ≠ 13),
          Function.update_of_ne (by omega : j ≠ 12)],
      by simp, by simp, by simp⟩, rfl⟩ ?_
  intro st₁ ⟨hR₁, _, hAt₁, hFr₁, hZero₁, _⟩
  refine runs_seq_store_le (x := s0 + k) (v := k + k)
    (Expr.eval_add (Expr.eval_reg_of_eq hR₁.2.2.1)
      (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using hR₁.1 4 (by decide)))
      (by dsimp [d0] at hD0W; omega))
    (Expr.eval_add
      (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using hR₁.1 4 (by decide)))
      (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using hR₁.1 4 (by decide))) h2kW) ?_
  have hSec0At : ListAt (Function.update st₁.mem (s0 + k) (k + k)) s0 sec0 := by
    refine listAt_csrList_of (listAt_csrOffsets_of fun j hj => ?_) fun j hj => ?_
    · have hsum : ((List.range j).map fun _ => ([G.n, 0] : List ℕ).length).sum = 2 * j := by
        simp [List.sum_replicate]; omega
      rw [hsum]
      rcases Nat.lt_or_eq_of_le hj with hlt | rfl
      · exact (Function.update_of_ne (by omega) _ _).trans (hAt₁ j hlt).1
      · simp; omega
    · have hsum : ((List.range j).map fun _ => ([G.n, 0] : List ℕ).length).sum = 2 * j := by
        simp [List.sum_replicate]; omega
      rw [hsum]
      intro idx hidx
      have hcases : idx = 0 ∨ idx = 1 := by simp at hidx; omega
      rcases hcases with rfl | rfl
      · change Function.update st₁.mem (s0 + k) (k + k) (s0 + (k + 1) + 2 * j + 0) = G.n
        rw [show s0 + (k + 1) + 2 * j + 0 = d0 + 2 * j by dsimp [d0]; omega,
          Function.update_of_ne (by dsimp [d0]; omega)]
        exact (hAt₁ j hj).2.1
      · change Function.update st₁.mem (s0 + k) (k + k) (s0 + (k + 1) + 2 * j + 1) = 0
        rw [show s0 + (k + 1) + 2 * j + 1 = d0 + 2 * j + 1 by dsimp [d0]; omega,
          Function.update_of_ne (by dsimp [d0]; omega)]
        exact (hAt₁ j hj).2.2
  refine runs_seq_assign_le (v := s1)
    (Expr.eval_add (Expr.eval_reg_of_eq hR₁.2.2.2)
      (Expr.eval_add
        (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using hR₁.1 4 (by decide)))
        (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using hR₁.1 4 (by decide))) h2kW)
      hS1W) ?_
  refine runs_seq_triple_le hLoop2
    ⟨⟨fun j hj => by
        have hne : j ≠ 16 := by omega
        simpa [Function.update_of_ne hne] using hR₁.1 j hj,
      by simp [hR₁.2.1], by simp [hR₁.2.2.1], by simp [hR₁.2.2.2]⟩,
      by simp, hSec0At,
      fun a ha => (Function.update_of_ne (by omega) _ _).trans (hFr₁ a ha),
      fun a ha => (Function.update_of_ne (by dsimp [s1, d0] at ha ⊢; omega) _ _).trans
        (hZero₁ a (by dsimp [s1] at ha; omega))⟩ ?_
  intro st₂ ⟨hR₂, h16₂, _, hSec0₂, hFr₂, hAt₂, hZero₂⟩
  refine runs_seq_store_le (x := s1 + k) (v := k)
    (Expr.eval_add (Expr.eval_reg_of_eq h16₂)
      (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using hR₂.1 4 (by decide)))
      (by dsimp [s2] at hS2W; omega))
    (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using hR₂.1 4 (by decide))) ?_
  let mem₂ := Function.update st₂.mem (s1 + k) k
  have hSec0₂' : ListAt mem₂ s0 sec0 := WordRAM.ListAt.congr hSec0₂ fun a _ ha =>
    Function.update_of_ne (by rw [hSec0Len] at ha; omega) _ _
  have hSec1At : ListAt mem₂ s1 sec1 := by
    refine listAt_csrList_of (listAt_csrOffsets_of fun j hj => ?_) fun j hj => ?_
    · have hsum : ((List.range j).map fun _ => ([0] : List ℕ).length).sum = j := by
        simp [List.sum_replicate]
      rw [hsum]
      rcases Nat.lt_or_eq_of_le hj with hlt | rfl
      · exact (Function.update_of_ne (by omega) _ _).trans (hAt₂ j hlt)
      · simp [mem₂]
    · intro idx hidx
      have h0 : idx = 0 := by simp at hidx; omega
      subst h0
      have hsum : ((List.range j).map fun _ => ([0] : List ℕ).length).sum = j := by
        simp [List.sum_replicate]
      rw [hsum]
      change mem₂ (s1 + (k + 1) + j + 0) = 0
      exact (Function.update_of_ne (by omega) _ _).trans (hZero₂ _ (by omega))
  have hFr₂' : ∀ a < s0, mem₂ a = mem a := fun a ha =>
    (Function.update_of_ne (by omega) _ _).trans (hFr₂ a ha)
  have hZero₂' : ZeroFrom mem₂ s2 := fun a ha =>
    (Function.update_of_ne (by dsimp [s2] at ha; omega) _ _).trans
      (hZero₂ a (by dsimp [s2] at ha; omega))
  refine runs_seq_assign_le (v := s2)
    (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h16₂)
      (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using hR₂.1 4 (by decide)))
      (by dsimp [s2] at hS2W; omega)) (Expr.eval_const hw1) (by dsimp [s2] at hS2W; omega))
      (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using hR₂.1 4 (by decide))) hS2W) ?_
  refine runs_seq_assign_le (v := d)
    (Expr.eval_mul (Expr.eval_mul (Expr.eval_mul (Expr.eval_const hw32)
      (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using hR₂.1 7 (by decide))) h32Δ)
      (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using hR₂.1 10 (by decide))) h32Δb)
      (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs] using hR₂.1 8 (by decide))) hD_lt) ?_
  have hConnPre : (buildConnAllContract w K C route sR G start 1 k Δ L bh).pre
      [g, x, start, 1, k, Δ, L, d, s2] mem₂ := by
    refine ⟨g, x, s2, rfl, ?_, ?_, by omega, by omega, hZero₂', hValid, hHost, le_refl 1,
      by omega, by simpa using hTermW, hw4, hGnW, hRoomS2, β, hPos, hExp, hBh⟩
    · exact WordRAM.ListAt.congr hG fun a _ ha => hFr₂' a (by dsimp [s0]; omega)
    · exact WordRAM.ListAt.congr hX fun a _ ha => hFr₂' a (by dsimp [s0]; omega)
  refine runs_seq_call_le hConn (vs := [g, x, start, 1, k, Δ, L, d, s2]) ?_ ?_ hConnPre ?_
  · simp [evalArgs, Expr.eval, Function.update, startState, buildLevelArgs,
      hR₂.1 0 (by decide), hR₂.1 1 (by decide), hR₂.1 2 (by decide), hR₂.1 3 (by decide),
      hR₂.1 4 (by decide), hR₂.1 7 (by decide), hR₂.1 8 (by decide)]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hD_lt | exact hS2W | exact hWords _ (by simp [buildLevelArgs])
  intro v mem₃ pos₃ hPost
  obtain ⟨_, _, _, eq, hvLo, hvHi, hSec2At, hFr₃, hZero₃⟩ := hPost
  simp only [List.cons.injEq, and_true, true_and] at eq
  obtain ⟨rfl, rfl, _, rfl⟩ := eq
  have hvW : v < 2 ^ w := hvHi.trans_lt hRoomS2
  have hSec2EndW : s2 + sec2.length < 2 ^ w := hvLo.trans_lt hvW
  have hSec2LenEq : sec2.length = k * k + 1 + mem₃ (s2 + k * k) := by
    have hOff := csrList_offset hSec2At (le_refl (k * k))
    have hL : sec2.length = k * k + 1 + ((List.range (k * k)).map fun j =>
        (levelConnRow route G start 1 k Δ L j).length).sum := by
      rw [show sec2 = csrList (k * k) (levelConnRow route G start 1 k Δ L) from rfl,
        csrList, List.length_append, length_csrOffsets, length_csrData_eq]
    omega
  have hkkW : k * k < 2 ^ w := by omega
  have hS2kkW : s2 + k * k < 2 ^ w := by omega
  have hS2kk1W : s2 + k * k + 1 < 2 ^ w := by omega
  have hH1 : h + 1 < 2 ^ w := by dsimp [s0] at hS0W; omega
  have hH2 : h + 2 < 2 ^ w := by dsimp [s0] at hS0W; omega
  have hH3 : h + 3 < 2 ^ w := by dsimp [s0] at hS0W; omega
  refine runs_seq_assign_le (v := k * k)
    (Expr.eval_mul
      (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs, Function.update] using hR₂.1 4 (by decide)))
      (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs, Function.update] using hR₂.1 4 (by decide)))
      hkkW) ?_
  refine runs_seq_assign_le (v := s2 + sec2.length)
    (by have h1 : s2 + k * k + 1 + mem₃ (s2 + k * k) = s2 + sec2.length := by omega
        rw [← h1]
        exact Expr.eval_add
          (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_reg_of_eq (by simp)) hS2kkW) (Expr.eval_const hw1) hS2kk1W)
          (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_reg_of_eq (by simp)) hS2kkW))
          (by rw [h1]; exact hSec2EndW)) ?_
  refine runs_seq_store_le (x := h) (v := 0)
    (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs, Function.update] using hR₂.1 11 (by decide)))
    (Expr.eval_const (Nat.two_pow_pos w)) ?_
  refine runs_seq_store_le (x := h + 1) (v := s1 - s0)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs, Function.update] using hR₂.1 11 (by decide)))
      (Expr.eval_const hw1) hH1)
    (Expr.eval_sub (Expr.eval_reg_of_eq (by simp [h16₂])) (Expr.eval_reg_of_eq (by simp [hR₂.2.2.1])) hS1W) ?_
  refine runs_seq_store_le (x := h + 2) (v := s2 - s0)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs, Function.update] using hR₂.1 11 (by decide)))
      (Expr.eval_const (by omega)) hH2)
    (Expr.eval_sub (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [hR₂.2.2.1])) hS2W) ?_
  refine runs_seq_store_le (x := h + 3) (v := s2 + sec2.length - s0)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simpa [startState, buildLevelArgs, Function.update] using hR₂.1 11 (by decide)))
      (Expr.eval_const (by omega)) hH3)
    (Expr.eval_sub (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [hR₂.2.2.1])) hSec2EndW) ?_
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · let final := Function.update (Function.update (Function.update (Function.update mem₃ h 0)
        (h + 1) (s1 - s0)) (h + 2) (s2 - s0)) (h + 3) (s2 + sec2.length - s0)
    have hKeep (a : ℕ) (ha : a < h ∨ s0 ≤ a) : final a = mem₃ a := by
      dsimp [final]
      rw [Function.update_of_ne (by dsimp [s0] at ha; omega),
        Function.update_of_ne (by dsimp [s0] at ha; omega),
        Function.update_of_ne (by dsimp [s0] at ha; omega),
        Function.update_of_ne (by dsimp [s0] at ha; omega)]
    have hEnc : D.encode k = layoutList [sec0, sec1, sec2] := by
      unfold BuildLevelData.encode
      rw [singleton_sec0_eq route G start k Δ L, singleton_sec1_eq route G start k Δ L]
      rfl
    have hEncLen : (D.encode k).length = 4 + sec0.length + sec1.length + sec2.length := by
      rw [hEnc, length_layoutList]
      simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega
    refine ⟨g, x, h, rfl, ?_, ?_, ?_, ?_, ?_, levelData_singleton_good hPlayer hPos hExp hHost hBh⟩
    · change h + (D.encode k).length ≤ v
      rw [hEncLen, hSec0Len, hSec1Len]
      change s2 + sec2.length ≤ v at hvLo
      rw [hS2h] at hvLo
      omega
    · dsimp only [Outcome.value, singletonSpace]; omega
    · rw [hEnc]
      let e : ℕ → ℕ := fun i => match i with
        | 0 => 0
        | 1 => sec0.length
        | 2 => sec0.length + sec1.length
        | _ => sec0.length + sec1.length + sec2.length
      refine listAt_layoutList_of_starts (e := e) rfl ?_ ?_ ?_
      · intro i hi
        have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
        rcases hcases with rfl | rfl | rfl <;> simp [e]
      · intro i hi
        have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp at hi; omega
        rcases hcases with rfl | rfl | rfl | rfl
        · simp [e]
        · simp [e, hS1eq, hSec0Len]
        · simp [e, hS2eq, hSec0Len, hSec1Len]; omega
        · simp [e, hS2eq, hSec0Len, hSec1Len]; omega
      · intro i hi
        have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
        rcases hcases with rfl | rfl | rfl
        · refine WordRAM.ListAt.congr hSec0₂' fun a ha hb => ?_
          simp only [List.length_cons, List.length_nil, List.getD_cons_zero, e] at ha hb
          change final a = mem₂ a
          rw [hKeep a (Or.inr (by dsimp [s0]; omega)), hFr₃ a (by rw [hSec0Len] at hb; dsimp [s2, s1, d0, s0] at hb ⊢; omega)]
        · change ListAt final (s0 + sec0.length) sec1
          rw [show s0 + sec0.length = s1 by omega]
          refine WordRAM.ListAt.congr hSec1At fun a ha hb => ?_
          rw [hKeep a (Or.inr (by omega)), hFr₃ a (by rw [hSec1Len] at hb; omega)]
        · change ListAt final (s0 + (sec0.length + sec1.length)) sec2
          rw [show s0 + (sec0.length + sec1.length) = s2 by omega]
          refine WordRAM.ListAt.congr hSec2At fun a ha _ => hKeep a (Or.inr (by omega))
    · intro j hj
      change final j = mem j
      rw [hKeep j (Or.inl hj), hFr₃ j (by dsimp [s2, s1, d0, s0]; omega)]
      exact hFr₂' j (by dsimp [s0]; omega)
    · intro a ha
      have ha' : v ≤ a := ha
      change final a = 0
      rw [hKeep a (Or.inr (by dsimp [s2, s1, d0, s0] at hvLo ha' ⊢; omega))]
      exact hZero₃ a ha'
  · simp only [buildSingletonContract, buildConnAllContract, Expr.size, argsSize, Nat.sub_zero]
    omega

end MinCostFlow.HierPaths
