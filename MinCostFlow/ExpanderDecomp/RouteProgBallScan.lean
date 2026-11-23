module

public import MinCostFlow.ExpanderDecomp.RouteProgBallBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer Ball Growing Layer-Scan Verification (`RouteProgBallScan`)

Verifies `growBallProc` against `growBall`: executes two radius-`h * L` layered
BFS traversals (from `S` and `T`) via `bfsLayersProc`, selects the smaller ball, scans complete
layers via `ballAddLayer_triple` until `16 * b * bd ≤ ballCnt` or all layers are processed,
writes outputs `(ballCnt, outBfsGen, outBallGen)`, and runs in `≤ 150 * br.cost + 750`
deterministic Word-RAM steps.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Helper for Chaining `seqStmts` -/

lemma ball_runs_seqStmts_append {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {l1 l2 : List Stmt} {st0 st1 st2 : State} {o2 : Outcome} {c1 c2 : ℕ}
    (h1 : l1 ≠ []) (h2 : l2 ≠ [])
    (hr1 : Runs w p ω (seqStmts l1) st0 .normal st1 c1)
    (hr2 : Runs w p ω (seqStmts l2) st1 o2 st2 c2) :
    ∃ c, Runs w p ω (seqStmts (l1 ++ l2)) st0 o2 st2 c ∧ c ≤ c1 + c2 + l1.length := by
  induction l1 generalizing st0 c1 with
  | nil => exact absurd rfl h1
  | cons a rest ih =>
    cases rest with
    | nil =>
      cases l2 with
      | nil => exact absurd rfl h2
      | cons b rest2 =>
        exact ⟨c1 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, hr1, hr2, rfl⟩), by simp⟩
    | cons b rest1 =>
      dsimp only [seqStmts] at hr1
      rcases runs_seq_iff.mp hr1 with ⟨_, _, _, h, _⟩ | ⟨sa, ca, cb, hra, hrb, rfl⟩
      · cases h
      obtain ⟨c', hrc', hc'⟩ := ih (by simp) hrb
      refine ⟨ca + c' + 1, ?_, by simp only [List.length_cons] at hc' ⊢; omega⟩
      have hne : ((b :: rest1) ++ l2) ≠ [] := by simp
      cases heq : (b :: rest1) ++ l2 with
      | nil => exact absurd heq hne
      | cons x xs =>
        rw [List.cons_append, heq]
        dsimp only [seqStmts]
        rw [← heq]
        exact runs_seq_iff.mpr (Or.inr ⟨sa, ca, c', hra, hrc', rfl⟩)

/-! ## 2. Outer Layer Scan Loop (`ballScanLayers_triple`) -/

lemma layers_drop_nodup_and_disj {layers : List (List ℕ)} {k : ℕ}
    (hnd : layers.flatten.Nodup) (hk : k < layers.length) :
    (layers[k]'hk).Nodup ∧
    Disjoint (layers.take k).flatten.toFinset (layers[k]'hk).toFinset := by
  have hsplit : layers = layers.take k ++ (layers[k]'hk) :: layers.drop (k + 1) := by
    have h1 := (List.take_append_drop k layers).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  rw [hsplit, List.flatten_append, List.flatten_cons, List.nodup_append] at hnd
  rcases hnd with ⟨_, hnd2, hdisj⟩
  rw [List.nodup_append] at hnd2
  refine ⟨hnd2.1, ?_⟩
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  exact hdisj x (List.mem_toFinset.mp hx1) x (List.mem_append_left _ (List.mem_toFinset.mp hx2)) rfl

lemma ballScanLayers_triple {w : ℕ} {p : Program}
    {X V : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)}
    {cfg : BallCfg} {m2 ballGen selOff selData : ℕ} {layers : List (List ℕ)}
    (hVX : V ⊆ X)
    (hadj_X : ∀ x ∈ X, ∀ e ∈ adj x, e.1 ∈ X)
    (hm2 : adjCsrOff X adj X.card ≤ m2)
    (hl_nd : layers.flatten.Nodup)
    (hl_subV : ∀ x ∈ layers.flatten, x ∈ V)
    (hl_len : layers.length ≤ X.card)
    (hl_flat_len : layers.flatten.length ≤ X.card)
    (hdisj_bs_bl : DisjRange cfg.ballStampAddr X.card cfg.ballListAddr X.card)
    (hdisj_bs_off : DisjRange cfg.ballStampAddr X.card cfg.offAddr (X.card + 1))
    (hdisj_bs_nb : DisjRange cfg.ballStampAddr X.card cfg.nbAddr m2)
    (hdisj_bs_mask : DisjRange cfg.ballStampAddr X.card cfg.maskArrAddr X.card)
    (hdisj_bs_loff : DisjRange cfg.ballStampAddr X.card selOff (X.card + 1))
    (hdisj_bs_data : DisjRange cfg.ballStampAddr X.card selData X.card)
    (hdisj_bl_off : DisjRange cfg.ballListAddr X.card cfg.offAddr (X.card + 1))
    (hdisj_bl_nb : DisjRange cfg.ballListAddr X.card cfg.nbAddr m2)
    (hdisj_bl_mask : DisjRange cfg.ballListAddr X.card cfg.maskArrAddr X.card)
    (hdisj_bl_loff : DisjRange cfg.ballListAddr X.card selOff (X.card + 1))
    (hdisj_bl_data : DisjRange cfg.ballListAddr X.card selData X.card)
    (hw_off : cfg.offAddr + X.card + 5 < 2 ^ w)
    (hw_nb : cfg.nbAddr + m2 + 5 < 2 ^ w)
    (hw_mask : cfg.maskArrAddr + X.card + 5 < 2 ^ w)
    (hw_bs : cfg.ballStampAddr + X.card + 5 < 2 ^ w)
    (hw_bl : cfg.ballListAddr + X.card + 5 < 2 ^ w)
    (hw_loff : selOff + X.card + 5 < 2 ^ w)
    (hw_data : selData + X.card + 5 < 2 ^ w)
    (hw_m2 : m2 + 5 < 2 ^ w)
    (hw_nX : X.card + 5 < 2 ^ w)
    (hw_mb : cfg.maskBadVal < 2 ^ w)
    (hw_bg : ballGen < 2 ^ w)
    (hw_mul : 16 * cfg.b * m2 + 5 < 2 ^ w)
    (hw_b16 : 16 * cfg.b + 5 < 2 ^ w)
    (hw16 : 16 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (rem : ℕ) :
    ∀ (layerIdx : ℕ) (bd : ℕ) (bl : List ℕ) (st0 : State),
      layerIdx + rem = layers.length →
      let cur := (layers.take layerIdx).flatten.toFinset
      bd + ∑ v ∈ V \ cur, (adj v).length ≤ m2 →
      NbCsrAt st0.mem cfg.offAddr cfg.nbAddr X adj →
      (∀ v < X.card, st0.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V) →
      (∀ r ≤ layers.length, st0.mem (selOff + r) = ((layers.take r).map List.length).sum) →
      (∀ r (hr : r < layers.length),
        ListAt st0.mem (selData + ((layers.take r).map List.length).sum) ((layers[r]'hr).map (locOf X))) →
      (∀ v < X.card, st0.mem (cfg.ballStampAddr + v) = ballGen ↔ origOf X v ∈ cur) →
      (∀ v < X.card, st0.mem (cfg.ballStampAddr + v) ≤ ballGen) →
      bl.length = cur.card →
      bl.Nodup →
      (∀ x ∈ bl, x < X.card ∧ origOf X x ∈ cur) →
      (∀ v ∈ cur, v ∈ X ∧ locOf X v ∈ bl) →
      ListAt st0.mem cfg.ballListAddr bl →
      st0.regs 2 = cfg.offAddr →
      st0.regs 3 = cfg.nbAddr →
      st0.regs 4 = cfg.maskArrAddr →
      st0.regs 5 = cfg.maskBadVal →
      st0.regs 14 = cfg.ballStampAddr →
      st0.regs 15 = cfg.ballListAddr →
      st0.regs 18 = cfg.b →
      st0.regs 24 = selOff →
      st0.regs 25 = selData →
      st0.regs 26 = rem →
      st0.regs 27 = ballGen →
      st0.regs 28 = cur.card →
      st0.regs 29 = bd →
      st0.regs 30 = layerIdx →
      ∀ ω, ∃ st' c,
        Runs w p ω ballScanLayersStmt st0 .normal st' c ∧
        (let res := scanBallLayers adj V cfg.b (layers.drop layerIdx) cur bd 0
         (∀ k ≤ 27, k ≠ 26 → st'.regs k = st0.regs k) ∧
         st'.regs 28 = res.1.card ∧
         (∀ v < X.card, st'.mem (cfg.ballStampAddr + v) = ballGen ↔ origOf X v ∈ res.1) ∧
         (∀ v < X.card, st'.mem (cfg.ballStampAddr + v) ≤ ballGen) ∧
         (∃ bl' : List ℕ, bl'.length = res.1.card ∧ bl'.Nodup ∧
           (∀ x ∈ bl', x < X.card ∧ origOf X x ∈ res.1) ∧
           (∀ v ∈ res.1, v ∈ X ∧ locOf X v ∈ bl') ∧
           ListAt st'.mem cfg.ballListAddr bl') ∧
         (∀ addr,
           (addr < cfg.ballStampAddr ∨ cfg.ballStampAddr + X.card ≤ addr) →
           (addr < cfg.ballListAddr ∨ cfg.ballListAddr + X.card ≤ addr) →
           st'.mem addr = st0.mem addr)) ∧
        c ≤ 150 * (scanBallLayers adj V cfg.b (layers.drop layerIdx) cur bd 0).2 + 5 := by
  induction rem with
  | zero =>
    intro layerIdx bd bl st0 hidx cur hpot _ _ _ _ hbs hbs_le hbl_len hbl_nd hbl_sub hbl_cov hbl_at
      _ _ _ _ _ _ _ _ _ hr26 _ hr28 _ _ ω
    have hdrop : layers.drop layerIdx = [] := List.drop_eq_nil_of_le (by omega)
    have hrun : Runs w p ω ballScanLayersStmt st0 .normal st0 ((Expr.reg 26).size + 1) :=
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr26], rfl, rfl, rfl⟩)
    refine ⟨st0, _, hrun, ?_, by rw [hdrop]; simp [scanBallLayers, Expr.size]⟩
    rw [hdrop]; dsimp only [scanBallLayers]
    exact ⟨fun _ _ _ => rfl, hr28, hbs, hbs_le, ⟨bl, hbl_len, hbl_nd, hbl_sub, hbl_cov, hbl_at⟩,
      fun _ _ _ => rfl⟩
  | succ rem ih =>
    intro layerIdx bd bl st0 hidx cur hpot hcsr hmask hloff hldata hbs hbs_le hbl_len hbl_nd hbl_sub
      hbl_cov hbl_at hr2 hr3 hr4 hr5 hr14 hr15 hr18 hr24 hr25 hr26 hr27 hr28 hr29 hr30 ω
    have hk_lt : layerIdx < layers.length := by omega
    set L := layers[layerIdx]'hk_lt
    have hdrop_eq : layers.drop layerIdx = L :: layers.drop (layerIdx + 1) :=
      List.drop_eq_getElem_cons hk_lt
    have hnd_disj := layers_drop_nodup_and_disj hl_nd hk_lt
    have hcurV : cur ⊆ V := fun x hx =>
      hl_subV x (by
        have h1 : x ∈ (layers.take layerIdx).flatten := List.mem_toFinset.mp hx
        have h2 := List.take_append_drop layerIdx layers
        rw [← h2, List.flatten_append]; exact List.mem_append_left _ h1)
    have hL_subV : ∀ u ∈ L, u ∈ V := fun u hu =>
      hl_subV u (List.mem_flatten.mpr ⟨L, List.getElem_mem hk_lt, hu⟩)
    set lo := ((layers.take layerIdx).map List.length).sum
    have hhi_eq : ((layers.take (layerIdx + 1)).map List.length).sum = lo + L.length := by
      rw [List.take_succ_eq_append_getElem hk_lt, List.map_append, List.map_singleton,
        List.sum_append, List.sum_singleton]
    have hlo_hi_le : lo + L.length ≤ X.card := by
      have h1 : ((layers.take (layerIdx + 1)).map List.length).sum ≤ (layers.map List.length).sum := by
        have hsp := List.take_append_drop (layerIdx + 1) layers
        have hlen_sp : (layers.map List.length).sum =
            ((layers.take (layerIdx + 1)).map List.length).sum +
            ((layers.drop (layerIdx + 1)).map List.length).sum := by
          conv_lhs => rw [← hsp, List.map_append, List.sum_append]
        omega
      have hlen_fl : (layers.map List.length).sum = layers.flatten.length := by rw [List.length_flatten]
      rw [← hhi_eq]; omega
    have hlo_mem : st0.mem (selOff + layerIdx) = lo := hloff layerIdx (by omega)
    have hhi_mem : st0.mem (selOff + (layerIdx + 1)) = lo + L.length := by
      rw [← hhi_eq]; exact hloff (layerIdx + 1) (by omega)
    have hev_guard : (Expr.reg 26).eval w st0 = some (rem + 1) := by simp [Expr.eval, hr26]
    -- Step 1: r31 := mem[selOff + layerIdx], r32 := mem[selOff + layerIdx + 1]
    set st1 : State :=
      { mem := st0.mem
        regs := Function.update (Function.update st0.regs 31 lo) 32 (lo + L.length)
        pos := st0.pos }
    have hpre1 : ∃ c1,
        Runs w p ω
          (seqStmts
            [ .assign 31 (.load (.bin .add (.reg 24) (.reg 30)))
            , .assign 32 (.load (.bin .add (.reg 24) (.bin .add (.reg 30) (.const 1)))) ])
          st0 .normal st1 c1 ∧ c1 ≤ 15 := by
      have h0 : ∃ o s c,
          Runs w p ω
            (seqStmts
              [ .assign 31 (.load (.bin .add (.reg 24) (.reg 30)))
              , .assign 32 (.load (.bin .add (.reg 24) (.bin .add (.reg 30) (.const 1)))) ])
            st0 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 15 := by
        dsimp only [seqStmts]
        refine runs_seq_assign_le (v := lo) (by rw [← hlo_mem]; eval_expr) ?_
        refine runs_assign_le (v := lo + L.length) (by rw [← hhi_mem]; eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, c1, hrun1, ⟨rfl, rfl⟩, hc1⟩
      exact ⟨c1, hrun1, by omega⟩
    rcases hpre1 with ⟨c1, hrun1, hc1⟩
    -- Step 2: ballAddLayer_triple
    obtain ⟨st2, c2, hrun2, hpost2, hc2⟩ :=
      ballAddLayer_triple (p := p) (L := L) hVX hadj_X hm2
        hdisj_bs_bl hdisj_bs_off hdisj_bs_nb hdisj_bs_mask hdisj_bs_data
        hdisj_bl_off hdisj_bl_nb hdisj_bl_mask hdisj_bl_data
        hw_off hw_nb hw_mask hw_bs hw_bl hw_data hw_m2 hw_nX hw_mb hw_bg hw4 hlo_hi_le
        L lo cur bd bl st1 rfl hnd_disj.1 hL_subV hcurV hnd_disj.2 hpot
        hcsr hmask hbs hbs_le hbl_len hbl_nd hbl_sub hbl_cov hbl_at
        (hldata layerIdx hk_lt)
        (by simp [st1, hr2]) (by simp [st1, hr3]) (by simp [st1, hr4]) (by simp [st1, hr5])
        (by simp [st1, hr14]) (by simp [st1, hr15]) (by simp [st1, hr25]) (by simp [st1, hr27])
        (by simp [st1, hr28]) (by simp [st1, hr29]) (by simp [st1]) (by simp [st1]) ω
    set a := addLayerToBall adj V L cur bd 0
    rcases hpost2 with ⟨hregs2, h2_28, h2_29, ha1_eq, ha1V, hpot2, hbs2, hbs2_le, hbl2, hfr2⟩
    have hbd2_le_m2 : a.2.1 ≤ m2 := by omega
    have hmul_lt_w : 16 * cfg.b * a.2.1 < 2 ^ w := by
      have h1 : 16 * cfg.b * a.2.1 ≤ 16 * cfg.b * m2 := Nat.mul_le_mul_left _ hbd2_le_m2
      omega
    have ha1_card_lt_w : a.1.card < 2 ^ w := by
      have : a.1.card ≤ X.card := Finset.card_le_card (Finset.Subset.trans ha1V hVX); omega
    -- Step 3: r31 := 16 * r18 * r29
    set prodVal := 16 * cfg.b * a.2.1
    set st3 : State := { st2 with regs := Function.update st2.regs 31 prodVal }
    have hrun3 : Runs w p ω (.assign 31 (.bin .mul (.bin .mul (.const 16) (.reg 18)) (.reg 29)))
        st2 .normal st3 ((Expr.bin .mul (.bin .mul (.const 16) (.reg 18)) (.reg 29)).size + 1) := by
      have h2_18 : st2.regs 18 = cfg.b := by
        rw [hregs2 18 (by decide) (by decide) (by decide)]; simp [st1, hr18]
      have h16_lt : 16 < 2 ^ w := hw16
      have h16b_lt : 16 * cfg.b < 2 ^ w := by omega
      have hev : (Expr.bin .mul (.bin .mul (.const 16) (.reg 18)) (.reg 29)).eval w st2 = some prodVal := by
        simp [Expr.eval, BinOp.eval, h2_18, h2_29, h16_lt, h16b_lt, hmul_lt_w, prodVal]
      exact runs_assign_iff.mpr ⟨prodVal, hev, rfl, rfl, rfl⟩
    have hcur1_eq : (layers.take (layerIdx + 1)).flatten.toFinset = a.1 := by
      rw [List.take_succ_eq_append_getElem hk_lt, List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.toFinset_append, ha1_eq]
    have hadd_scan := scanBallLayers_cost_add adj V cfg.b (layers.drop (layerIdx + 1)) a.1 a.2.1 0 (a.2.2 + 1)
    simp only [Nat.zero_add] at hadd_scan
    -- Branch on 16 * b * bd' ≤ cur'.card
    by_cases hstop : prodVal ≤ a.1.card
    · -- Stopping branch: r26 := 0, exit loop immediately!
      have hev_cond : (Expr.bin .lt (.reg 28) (.reg 31)).eval w st3 = some 0 := by
        simp [Expr.eval, BinOp.eval, st3, h2_28, show ¬ a.1.card < prodVal by omega]
      set st4 : State := { st3 with regs := Function.update st3.regs 26 0 }
      have hrun_cond : Runs w p ω
          (.cond (.bin .lt (.reg 28) (.reg 31))
            (seqStmts
              [ .assign 30 (.bin .add (.reg 30) (.const 1))
              , .assign 26 (.bin .sub (.reg 26) (.const 1)) ])
            (.assign 26 (.const 0)))
          st3 .normal st4 ((Expr.bin .lt (.reg 28) (.reg 31)).size + ((Expr.const 0).size + 1) + 1) := by
        refine runs_cond_iff.mpr ⟨0, (Expr.const 0).size + 1, hev_cond, ?_, rfl⟩
        have ha : Runs w p ω (.assign 26 (.const 0)) st3 .normal st4 ((Expr.const 0).size + 1) :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
        simpa using ha
      have hrun_exit : Runs w p ω ballScanLayersStmt st4 .normal st4 ((Expr.reg 26).size + 1) :=
        runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, st4], rfl, rfl, rfl⟩)
      have hbody_tail : Runs w p ω
          (seqStmts
            [ ballAddLayerStmt
            , .assign 31 (.bin .mul (.bin .mul (.const 16) (.reg 18)) (.reg 29))
            , .cond (.bin .lt (.reg 28) (.reg 31))
                (seqStmts
                  [ .assign 30 (.bin .add (.reg 30) (.const 1))
                  , .assign 26 (.bin .sub (.reg 26) (.const 1)) ])
                (.assign 26 (.const 0)) ])
          st1 .normal st4 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2,
          runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hrun3, hrun_cond, rfl⟩), rfl⟩)
      obtain ⟨cB, hrunB, hcB⟩ := ball_runs_seqStmts_append (by simp) (by simp) hrun1 hbody_tail
      have hrun_tot : Runs w p ω ballScanLayersStmt st0 .normal st4
          ((Expr.reg 26).size + cB + ((Expr.reg 26).size + 1) + 1) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨rem + 1, st4, cB, _, hev_guard, by omega, hrunB, hrun_exit, rfl⟩))
      refine ⟨st4, _, hrun_tot, ?_, ?_⟩
      · rw [hdrop_eq]; dsimp only [scanBallLayers]
        change (∀ k ≤ 27, k ≠ 26 → st4.regs k = st0.regs k) ∧
          st4.regs 28 = (if prodVal ≤ a.1.card then (a.1, a.2.2 + 1) else _).1.card ∧
          (∀ v < X.card, st4.mem (cfg.ballStampAddr + v) = ballGen ↔
            origOf X v ∈ (if prodVal ≤ a.1.card then (a.1, a.2.2 + 1) else _).1) ∧
          (∀ v < X.card, st4.mem (cfg.ballStampAddr + v) ≤ ballGen) ∧
          (∃ bl' : List ℕ, bl'.length = (if prodVal ≤ a.1.card then (a.1, a.2.2 + 1) else _).1.card ∧
            bl'.Nodup ∧
            (∀ x ∈ bl', x < X.card ∧ origOf X x ∈ (if prodVal ≤ a.1.card then (a.1, a.2.2 + 1) else _).1) ∧
            (∀ v ∈ (if prodVal ≤ a.1.card then (a.1, a.2.2 + 1) else _).1, v ∈ X ∧ locOf X v ∈ bl') ∧
            ListAt st4.mem cfg.ballListAddr bl') ∧
          (∀ addr,
            (addr < cfg.ballStampAddr ∨ cfg.ballStampAddr + X.card ≤ addr) →
            (addr < cfg.ballListAddr ∨ cfg.ballListAddr + X.card ≤ addr) →
            st4.mem addr = st0.mem addr)
        simp only [hstop, ↓reduceIte]
        refine ⟨?_, by simp [st4, st3, h2_28], hbs2, hbs2_le, hbl2, hfr2⟩
        intro k hk h26
        simp only [st4, st3, Function.update_of_ne h26, Function.update_of_ne (by omega : k ≠ 31)]
        rw [hregs2 k (by omega) (by omega) (by omega)]
        simp [st1, Function.update_of_ne (by omega : k ≠ 32), Function.update_of_ne (by omega : k ≠ 31)]
      · rw [hdrop_eq]; dsimp only [scanBallLayers]
        change _ ≤ 150 * (if prodVal ≤ a.1.card then (a.1, a.2.2 + 1) else _).2 + 5
        simp only [hstop, ↓reduceIte, Expr.size, List.length_cons, List.length_nil] at hc1 hc2 hcB ⊢
        omega
    · -- Continue branch: r30 := layerIdx + 1, r26 := rem, invoke IH!
      have hlt : a.1.card < prodVal := by omega
      have hw_ne : w ≠ 0 := by intro hw0; subst hw0; simp at hw4
      have hev_cond : (Expr.bin .lt (.reg 28) (.reg 31)).eval w st3 = some 1 := by
        simp [Expr.eval, BinOp.eval, st3, h2_28, hlt, hw_ne]
      set st4 : State :=
        { mem := st3.mem
          regs := Function.update (Function.update st3.regs 30 (layerIdx + 1)) 26 rem
          pos := st3.pos }
      have h3_30 : st3.regs 30 = layerIdx := by
        simp [st3, hregs2 30 (by decide) (by decide) (by decide), st1, hr30]
      have h3_26 : st3.regs 26 = rem + 1 := by
        simp [st3, hregs2 26 (by decide) (by decide) (by decide), st1, hr26]
      have hcont_step : ∃ c4,
          Runs w p ω
            (seqStmts
              [ .assign 30 (.bin .add (.reg 30) (.const 1))
              , .assign 26 (.bin .sub (.reg 26) (.const 1)) ])
            st3 .normal st4 c4 ∧ c4 ≤ 12 := by
        have h0 : ∃ o s c,
            Runs w p ω
              (seqStmts
                [ .assign 30 (.bin .add (.reg 30) (.const 1))
                , .assign 26 (.bin .sub (.reg 26) (.const 1)) ])
              st3 o s c ∧ (o = .normal ∧ s = st4) ∧ 0 + c ≤ 12 := by
          dsimp only [seqStmts]
          refine runs_seq_assign_le (v := layerIdx + 1) (by eval_expr) ?_
          refine runs_assign_le (v := rem)
            (by simp [Expr.eval, BinOp.eval, h3_26, show 1 < 2 ^ w by omega]; omega)
            ⟨rfl, rfl⟩ (by wram_cost)
        rcases h0 with ⟨_, _, c4, hrun4, ⟨rfl, rfl⟩, hc4⟩
        exact ⟨c4, hrun4, by omega⟩
      rcases hcont_step with ⟨c4, hrun4, hc4⟩
      have hrun_cond : Runs w p ω
          (.cond (.bin .lt (.reg 28) (.reg 31))
            (seqStmts
              [ .assign 30 (.bin .add (.reg 30) (.const 1))
              , .assign 26 (.bin .sub (.reg 26) (.const 1)) ])
            (.assign 26 (.const 0)))
          st3 .normal st4 ((Expr.bin .lt (.reg 28) (.reg 31)).size + c4 + 1) :=
        runs_cond_iff.mpr ⟨1, c4, hev_cond, by simpa using hrun4, rfl⟩
      have hbody_tail : Runs w p ω
          (seqStmts
            [ ballAddLayerStmt
            , .assign 31 (.bin .mul (.bin .mul (.const 16) (.reg 18)) (.reg 29))
            , .cond (.bin .lt (.reg 28) (.reg 31))
                (seqStmts
                  [ .assign 30 (.bin .add (.reg 30) (.const 1))
                  , .assign 26 (.bin .sub (.reg 26) (.const 1)) ])
                (.assign 26 (.const 0)) ])
          st1 .normal st4 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hrun2,
          runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hrun3, hrun_cond, rfl⟩), rfl⟩)
      obtain ⟨cB, hrunB, hcB⟩ := ball_runs_seqStmts_append (by simp) (by simp) hrun1 hbody_tail
      -- Preserve CSR, mask, loff, ldata into st4 (st4.mem = st2.mem)
      have hcsr4 : NbCsrAt st4.mem cfg.offAddr cfg.nbAddr X adj := by
        refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
        · rw [show st4.mem _ = st2.mem _ from rfl,
              hfr2 _ (by rcases hdisj_bs_off with x | x <;> omega)
                     (by rcases hdisj_bl_off with x | x <;> omega)]
          exact hcsr.1 i hi
        · have hlt' : adjCsrOff X adj i + j < m2 := by
            have := adjCsrOff_mono X adj (show i + 1 ≤ X.card by omega)
            have := adjCsrOff_succ X adj i; omega
          rw [Nat.add_assoc, show st4.mem _ = st2.mem _ from rfl,
              hfr2 _ (by rcases hdisj_bs_nb with x | x <;> omega)
                     (by rcases hdisj_bl_nb with x | x <;> omega), ← Nat.add_assoc]
          exact hcsr.2 i hi j hj
      have hmask4 : ∀ v < X.card, st4.mem (cfg.maskArrAddr + v) ≠ cfg.maskBadVal ↔ origOf X v ∈ V := by
        intro v hv
        rw [show st4.mem _ = st2.mem _ from rfl,
            hfr2 _ (by rcases hdisj_bs_mask with x | x <;> omega)
                   (by rcases hdisj_bl_mask with x | x <;> omega)]
        exact hmask v hv
      have hloff4 : ∀ r ≤ layers.length, st4.mem (selOff + r) = ((layers.take r).map List.length).sum := by
        intro r hr
        rw [show st4.mem _ = st2.mem _ from rfl,
            hfr2 _ (by rcases hdisj_bs_loff with x | x <;> omega)
                   (by rcases hdisj_bl_loff with x | x <;> omega)]
        exact hloff r hr
      have hldata4 : ∀ r (hr : r < layers.length),
          ListAt st4.mem (selData + ((layers.take r).map List.length).sum) ((layers[r]'hr).map (locOf X)) := by
        intro r hr j hj
        have hlt_X : ((layers.take r).map List.length).sum + j < X.card := by
          have h1 : ((layers.take (r + 1)).map List.length).sum ≤ (layers.map List.length).sum := by
            have hsp := List.take_append_drop (r + 1) layers
            have hlen_sp : (layers.map List.length).sum =
                ((layers.take (r + 1)).map List.length).sum +
                ((layers.drop (r + 1)).map List.length).sum := by
              conv_lhs => rw [← hsp, List.map_append, List.sum_append]
            omega
          rw [List.take_succ_eq_append_getElem hr, List.map_append, List.map_singleton,
            List.sum_append, List.sum_singleton] at h1
          have hlen_fl : (layers.map List.length).sum = layers.flatten.length := by rw [List.length_flatten]
          simp only [List.length_map] at hj; omega
        rw [Nat.add_assoc, show st4.mem _ = st2.mem _ from rfl,
            hfr2 _ (by rcases hdisj_bs_data with x | x <;> omega)
                   (by rcases hdisj_bl_data with x | x <;> omega), ← Nat.add_assoc]
        exact hldata r hr j hj
      rcases hbl2 with ⟨bl2, hbl2_len, hbl2_nd, hbl2_sub, hbl2_cov, hbl2_at⟩
      -- Invoke IH on rem, layerIdx + 1, a.2.1, bl2, st4
      obtain ⟨stF, cIH, hrunIH, hpostIH, hcIH⟩ :=
        ih (layerIdx + 1) a.2.1 bl2 st4 (by omega)
          (by rw [hcur1_eq]; exact hpot2) hcsr4 hmask4 hloff4 hldata4
          (by intro v hv; rw [hcur1_eq]; exact hbs2 v hv) hbs2_le
          (by rw [hcur1_eq]; exact hbl2_len) hbl2_nd
          (by intro x hx; rw [hcur1_eq]; exact hbl2_sub x hx)
          (by intro v hv; rw [hcur1_eq] at hv; exact hbl2_cov v hv) hbl2_at
          (by simp [st4, st3, hregs2 2 (by decide) (by decide) (by decide), st1, hr2])
          (by simp [st4, st3, hregs2 3 (by decide) (by decide) (by decide), st1, hr3])
          (by simp [st4, st3, hregs2 4 (by decide) (by decide) (by decide), st1, hr4])
          (by simp [st4, st3, hregs2 5 (by decide) (by decide) (by decide), st1, hr5])
          (by simp [st4, st3, hregs2 14 (by decide) (by decide) (by decide), st1, hr14])
          (by simp [st4, st3, hregs2 15 (by decide) (by decide) (by decide), st1, hr15])
          (by simp [st4, st3, hregs2 18 (by decide) (by decide) (by decide), st1, hr18])
          (by simp [st4, st3, hregs2 24 (by decide) (by decide) (by decide), st1, hr24])
          (by simp [st4, st3, hregs2 25 (by decide) (by decide) (by decide), st1, hr25])
          (by simp [st4])
          (by simp [st4, st3, hregs2 27 (by decide) (by decide) (by decide), st1, hr27])
          (by rw [hcur1_eq]; simp [st4, st3, h2_28])
          (by simp [st4, st3, h2_29]) (by simp [st4]) ω
      have hrun_tot : Runs w p ω ballScanLayersStmt st0 .normal stF
          ((Expr.reg 26).size + cB + cIH + 1) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨rem + 1, st4, cB, cIH, hev_guard, by omega, hrunB, hrunIH, rfl⟩))
      rw [hcur1_eq] at hpostIH hcIH
      rcases hpostIH with ⟨hrF, h28F, hbsF, hbsF_le, hblF, hfrF⟩
      refine ⟨stF, _, hrun_tot, ?_, ?_⟩
      · rw [hdrop_eq]; dsimp only [scanBallLayers]
        change (∀ k ≤ 27, k ≠ 26 → stF.regs k = st0.regs k) ∧
          stF.regs 28 = (if prodVal ≤ a.1.card then _ else scanBallLayers adj V cfg.b (layers.drop (layerIdx + 1)) a.1 a.2.1 (a.2.2 + 1)).1.card ∧
          (∀ v < X.card, stF.mem (cfg.ballStampAddr + v) = ballGen ↔
            origOf X v ∈ (if prodVal ≤ a.1.card then _ else scanBallLayers adj V cfg.b (layers.drop (layerIdx + 1)) a.1 a.2.1 (a.2.2 + 1)).1) ∧
          (∀ v < X.card, stF.mem (cfg.ballStampAddr + v) ≤ ballGen) ∧
          (∃ bl' : List ℕ, bl'.length = (if prodVal ≤ a.1.card then _ else scanBallLayers adj V cfg.b (layers.drop (layerIdx + 1)) a.1 a.2.1 (a.2.2 + 1)).1.card ∧
            bl'.Nodup ∧
            (∀ x ∈ bl', x < X.card ∧ origOf X x ∈ (if prodVal ≤ a.1.card then _ else scanBallLayers adj V cfg.b (layers.drop (layerIdx + 1)) a.1 a.2.1 (a.2.2 + 1)).1) ∧
            (∀ v ∈ (if prodVal ≤ a.1.card then _ else scanBallLayers adj V cfg.b (layers.drop (layerIdx + 1)) a.1 a.2.1 (a.2.2 + 1)).1, v ∈ X ∧ locOf X v ∈ bl') ∧
            ListAt stF.mem cfg.ballListAddr bl') ∧
          (∀ addr,
            (addr < cfg.ballStampAddr ∨ cfg.ballStampAddr + X.card ≤ addr) →
            (addr < cfg.ballListAddr ∨ cfg.ballListAddr + X.card ≤ addr) →
            stF.mem addr = st0.mem addr)
        simp only [hstop, ↓reduceIte, hadd_scan.1]
        refine ⟨?_, h28F, hbsF, hbsF_le, hblF, fun addr h1 h2 => (hfrF addr h1 h2).trans (hfr2 addr h1 h2)⟩
        intro k hk h26
        rw [hrF k hk h26]
        simp only [st4, st3, Function.update_of_ne h26, Function.update_of_ne (by omega : k ≠ 30),
          Function.update_of_ne (by omega : k ≠ 31)]
        rw [hregs2 k (by omega) (by omega) (by omega)]
        simp [st1, Function.update_of_ne (by omega : k ≠ 32), Function.update_of_ne (by omega : k ≠ 31)]
      · rw [hdrop_eq]; dsimp only [scanBallLayers]
        change _ ≤ 150 * (if prodVal ≤ a.1.card then _ else scanBallLayers adj V cfg.b (layers.drop (layerIdx + 1)) a.1 a.2.1 (a.2.2 + 1)).2 + 5
        simp only [hstop, ↓reduceIte, hadd_scan.2, Expr.size, List.length_cons, List.length_nil] at hc1 hc2 hc4 hcB hcIH ⊢
        omega

/-! ## 3. Full `growBallProc` Triple and Contract -/

lemma bfsWriteSet_S_sub_ballWriteSet {nX : ℕ} {cfg : BallCfg} {bfsCfg : BfsCfg} {cfgAddr a : ℕ}
    (h : BfsWriteSet nX ({ bfsCfg with layerOffAddr := cfg.layerOffS, layerDataAddr := cfg.layerDataS }) cfg.bfsCfgAddr a) :
    BallWriteSet nX cfg bfsCfg cfgAddr a := by
  dsimp only [BfsWriteSet] at h
  rcases h with c | c | c | c | c | c
  · exact Or.inl c
  · exact Or.inr (Or.inl c)
  · exact Or.inr (Or.inr (Or.inr (Or.inl c)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))
  · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))

lemma bfsWriteSet_T_sub_ballWriteSet {nX : ℕ} {cfg : BallCfg} {bfsCfg : BfsCfg} {cfgAddr a : ℕ}
    (h : BfsWriteSet nX ({ bfsCfg with layerOffAddr := cfg.layerOffT, layerDataAddr := cfg.layerDataT }) cfg.bfsCfgAddr a) :
    BallWriteSet nX cfg bfsCfg cfgAddr a := by
  dsimp only [BfsWriteSet] at h
  rcases h with c | c | c | c | c | c
  · exact Or.inl c
  · exact Or.inr (Or.inl c)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))))
  · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))))))


end MinCostFlow.ExpanderDecomp
