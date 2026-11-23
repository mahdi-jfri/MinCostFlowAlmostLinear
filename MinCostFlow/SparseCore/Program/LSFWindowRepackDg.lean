module

public import MinCostFlow.SparseCore.Program.LSFWindowRepackDefs
import WordRAM.Tactic

/-!
# Sparse Repack Verification for `DynGraphAt`

Proves `dynGraphAt_shift` and `repackDynGraphProc_runs`, copying `DynGraphAt mem src vCap_s eCap_s H`
into fresh zeroed memory at `dst` with capacities `(vCap_d, eCap_d)` in time `≤ 100 * H.n + 150 * H.m + 100`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
open MinCostFlow.DynSpanner.Program

lemma dynGraphAt_shift {mem : ℕ → ℕ} {guestBase a vCap eCap : ℕ} {H : MGraph}
    (hdg : DynGraphAt (fun x => mem (guestBase + x)) a vCap eCap H) :
    DynGraphAt mem (guestBase + a) vCap eCap H := by
  rcases hdg with ⟨hH, hvlt, helt, h0, h1, h2, h3, hvP, ⟨vL, hvlen, hvnd, hvmem, hvLA, hvPos⟩,
    hext, hint, heP, ⟨eL, helen, hend, hemem, heLA, hePos⟩, heEnds, ⟨incL, hincL⟩⟩
  refine ⟨hH, hvlt, helt,
    by simpa [Nat.add_assoc] using h0, by simpa [Nat.add_assoc] using h1,
    by simpa [Nat.add_assoc] using h2, by simpa [Nat.add_assoc] using h3,
    fun v hv => by simpa [dgVPresBase, Nat.add_assoc] using hvP v hv,
    ⟨vL, hvlen, hvnd, hvmem,
      fun i hi => by simpa [dgVListBase, Nat.add_assoc] using hvLA i hi,
      fun i hi => by simpa [dgVPosBase, Nat.add_assoc] using hvPos i hi⟩,
    fun v hv => by simpa [dgExtToIntBase, dgIntToExtBase, Nat.add_assoc] using hext v hv,
    fun s hs => by simpa [dgExtToIntBase, dgIntToExtBase, Nat.add_assoc] using hint s hs,
    fun e he => by simpa [dgEPresBase, Nat.add_assoc] using heP e he,
    ⟨eL, helen, hend, hemem,
      fun i hi => by simpa [dgEListBase, Nat.add_assoc] using heLA i hi,
      fun i hi => by simpa [dgEPosBase, Nat.add_assoc] using hePos i hi⟩,
    fun e he => by
      simpa [dgETailSlotBase, dgEHeadSlotBase, dgExtToIntBase, Nat.add_assoc] using heEnds e he,
    ⟨incL, fun s hs => ?_⟩⟩
  obtain ⟨⟨hnd, hlt, hhd, hlinks⟩, hdeg, hmemL⟩ := hincL s hs
  refine ⟨⟨hnd, hlt, by simpa [dgIncHeadBase, Nat.add_assoc] using hhd,
      fun i hi => by simpa [dgHePrevBase, dgHeNextBase, Nat.add_assoc] using hlinks i hi⟩,
    by simpa [dgSlotDegBase, Nat.add_assoc] using hdeg,
    fun h => by simpa [dgETailSlotBase, dgEHeadSlotBase, Nat.add_assoc] using hmemL h⟩

/-- Helper: memory updated at `7` distinct vertex-array cells in `dst`. -/
private def dgUpdV (m : ℕ → ℕ) (dst vCap_d i v s degVal headVal : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update m
      (dgVPresBase dst + v) 1)
      (dgVListBase dst vCap_d + i) v)
      (dgVPosBase dst vCap_d + v) i)
      (dgExtToIntBase dst vCap_d + v) s)
      (dgIntToExtBase dst vCap_d + s) v)
      (dgSlotDegBase dst vCap_d + s) degVal)
      (dgIncHeadBase dst vCap_d + s) headVal

private lemma dgUpdV_ne {m : ℕ → ℕ} {dst vCap_d i v s degVal headVal a : ℕ}
    (h1 : a ≠ dgVPresBase dst + v) (h2 : a ≠ dgVListBase dst vCap_d + i)
    (h3 : a ≠ dgVPosBase dst vCap_d + v) (h4 : a ≠ dgExtToIntBase dst vCap_d + v)
    (h5 : a ≠ dgIntToExtBase dst vCap_d + s) (h6 : a ≠ dgSlotDegBase dst vCap_d + s)
    (h7 : a ≠ dgIncHeadBase dst vCap_d + s) :
    dgUpdV m dst vCap_d i v s degVal headVal a = m a := by
  unfold dgUpdV
  rw [Function.update_of_ne h7, Function.update_of_ne h6, Function.update_of_ne h5,
      Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
      Function.update_of_ne h1]

private lemma dgUpdV_at {m : ℕ → ℕ} {dst vCap_d i v s degVal headVal : ℕ}
    (hi : i < vCap_d) (hv : v < vCap_d) (hs : s < vCap_d) :
    let m' := dgUpdV m dst vCap_d i v s degVal headVal
    m' (dgVPresBase dst + v) = 1 ∧ m' (dgVListBase dst vCap_d + i) = v ∧
    m' (dgVPosBase dst vCap_d + v) = i ∧ m' (dgExtToIntBase dst vCap_d + v) = s ∧
    m' (dgIntToExtBase dst vCap_d + s) = v ∧ m' (dgSlotDegBase dst vCap_d + s) = degVal ∧
    m' (dgIncHeadBase dst vCap_d + s) = headVal := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold dgUpdV <;>
    repeat (first | exact Function.update_self _ _ _
                  | rw [Function.update_of_ne (by
                      dsimp [dgVPresBase, dgVListBase, dgVPosBase, dgExtToIntBase,
                        dgIntToExtBase, dgSlotDegBase, dgIncHeadBase]; omega)])

/-- Helper: memory updated at `9` distinct edge/half-edge cells in `dst`. -/
private def dgUpdE (m : ℕ → ℕ) (dst vCap_d eCap_d i e tVal hVal p0 p1 n0 n1 : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update m
      (dgEPresBase dst vCap_d + e) 1)
      (dgEListBase dst vCap_d eCap_d + i) e)
      (dgEPosBase dst vCap_d eCap_d + e) i)
      (dgETailSlotBase dst vCap_d eCap_d + e) tVal)
      (dgEHeadSlotBase dst vCap_d eCap_d + e) hVal)
      (dgHePrevBase dst vCap_d eCap_d + 2 * e) p0)
      (dgHePrevBase dst vCap_d eCap_d + (2 * e + 1)) p1)
      (dgHeNextBase dst vCap_d eCap_d + 2 * e) n0)
      (dgHeNextBase dst vCap_d eCap_d + (2 * e + 1)) n1

private lemma dgUpdE_ne {m : ℕ → ℕ} {dst vCap_d eCap_d i e tVal hVal p0 p1 n0 n1 a : ℕ}
    (h1 : a ≠ dgEPresBase dst vCap_d + e) (h2 : a ≠ dgEListBase dst vCap_d eCap_d + i)
    (h3 : a ≠ dgEPosBase dst vCap_d eCap_d + e) (h4 : a ≠ dgETailSlotBase dst vCap_d eCap_d + e)
    (h5 : a ≠ dgEHeadSlotBase dst vCap_d eCap_d + e) (h6 : a ≠ dgHePrevBase dst vCap_d eCap_d + 2 * e)
    (h7 : a ≠ dgHePrevBase dst vCap_d eCap_d + (2 * e + 1))
    (h8 : a ≠ dgHeNextBase dst vCap_d eCap_d + 2 * e)
    (h9 : a ≠ dgHeNextBase dst vCap_d eCap_d + (2 * e + 1)) :
    dgUpdE m dst vCap_d eCap_d i e tVal hVal p0 p1 n0 n1 a = m a := by
  unfold dgUpdE
  rw [Function.update_of_ne h9, Function.update_of_ne h8, Function.update_of_ne h7,
      Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4,
      Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]

private lemma dgUpdE_at {m : ℕ → ℕ} {dst vCap_d eCap_d i e tVal hVal p0 p1 n0 n1 : ℕ}
    (hi : i < eCap_d) (he : e < eCap_d) :
    let m' := dgUpdE m dst vCap_d eCap_d i e tVal hVal p0 p1 n0 n1
    m' (dgEPresBase dst vCap_d + e) = 1 ∧ m' (dgEListBase dst vCap_d eCap_d + i) = e ∧
    m' (dgEPosBase dst vCap_d eCap_d + e) = i ∧
    m' (dgETailSlotBase dst vCap_d eCap_d + e) = tVal ∧
    m' (dgEHeadSlotBase dst vCap_d eCap_d + e) = hVal ∧
    m' (dgHePrevBase dst vCap_d eCap_d + 2 * e) = p0 ∧
    m' (dgHePrevBase dst vCap_d eCap_d + (2 * e + 1)) = p1 ∧
    m' (dgHeNextBase dst vCap_d eCap_d + 2 * e) = n0 ∧
    m' (dgHeNextBase dst vCap_d eCap_d + (2 * e + 1)) = n1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold dgUpdE <;>
    repeat (first | exact Function.update_self _ _ _
                  | rw [Function.update_of_ne (by
                      dsimp [dgEPresBase, dgEListBase, dgEPosBase, dgETailSlotBase,
                        dgEHeadSlotBase, dgHePrevBase, dgHeNextBase]; omega)])

private lemma dgUpdE_pres_other {m : ℕ → ℕ} {dst vCap_d eCap_d i j e e' tVal hVal p0 p1 n0 n1 : ℕ}
    (hi : i < eCap_d) (hj : j < eCap_d) (he : e < eCap_d) (he' : e' < eCap_d)
    (hij : j ≠ i) (hee : e' ≠ e) :
    let m' := dgUpdE m dst vCap_d eCap_d i e tVal hVal p0 p1 n0 n1
    m' (dgEPresBase dst vCap_d + e') = m (dgEPresBase dst vCap_d + e') ∧
    m' (dgEListBase dst vCap_d eCap_d + j) = m (dgEListBase dst vCap_d eCap_d + j) ∧
    m' (dgEPosBase dst vCap_d eCap_d + e') = m (dgEPosBase dst vCap_d eCap_d + e') ∧
    m' (dgETailSlotBase dst vCap_d eCap_d + e') = m (dgETailSlotBase dst vCap_d eCap_d + e') ∧
    m' (dgEHeadSlotBase dst vCap_d eCap_d + e') = m (dgEHeadSlotBase dst vCap_d eCap_d + e') ∧
    m' (dgHePrevBase dst vCap_d eCap_d + 2 * e') = m (dgHePrevBase dst vCap_d eCap_d + 2 * e') ∧
    m' (dgHePrevBase dst vCap_d eCap_d + (2 * e' + 1)) = m (dgHePrevBase dst vCap_d eCap_d + (2 * e' + 1)) ∧
    m' (dgHeNextBase dst vCap_d eCap_d + 2 * e') = m (dgHeNextBase dst vCap_d eCap_d + 2 * e') ∧
    m' (dgHeNextBase dst vCap_d eCap_d + (2 * e' + 1)) = m (dgHeNextBase dst vCap_d eCap_d + (2 * e' + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact dgUpdE_ne
      (by dsimp [dgEPresBase, dgEListBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase, dgHeNextBase]; omega)
      (by dsimp [dgEPresBase, dgEListBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase, dgHeNextBase]; omega)
      (by dsimp [dgEPresBase, dgEListBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase, dgHeNextBase]; omega)
      (by dsimp [dgEPresBase, dgEListBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase, dgHeNextBase]; omega)
      (by dsimp [dgEPresBase, dgEListBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase, dgHeNextBase]; omega)
      (by dsimp [dgEPresBase, dgEListBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase, dgHeNextBase]; omega)
      (by dsimp [dgEPresBase, dgEListBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase, dgHeNextBase]; omega)
      (by dsimp [dgEPresBase, dgEListBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase, dgHeNextBase]; omega)
      (by dsimp [dgEPresBase, dgEListBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase, dgHeNextBase]; omega)

set_option maxHeartbeats 800000 in
lemma repackDynGraphProc_runs {w : ℕ} {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    {src dst vCap_s eCap_s vCap_d eCap_d : ℕ} {H : MGraph}
    (hw : 20 < 2 ^ w)
    (hMemW : ∀ a, src ≤ a → a < src + dynGraphSize vCap_s eCap_s → mem a < 2 ^ w)
    (hdg : DynGraphAt mem src vCap_s eCap_s H)
    (hvCap : vCap_s ≤ vCap_d) (heCap : eCap_s ≤ eCap_d)
    (hsrc_w : src + dynGraphSize vCap_s eCap_s < 2 ^ w)
    (hdst_w : dst + dynGraphSize vCap_d eCap_d < 2 ^ w)
    (hdisj : src + dynGraphSize vCap_s eCap_s ≤ dst ∨
             dst + dynGraphSize vCap_d eCap_d ≤ src)
    (hzero : ∀ a, dst ≤ a → a < dst + dynGraphSize vCap_d eCap_d → mem a = 0) :
    ∃ st' c,
      Runs w p ω repackDynGraphProc (startState [src, dst, vCap_d, eCap_d] mem pos)
        (.returned 0) st' c ∧
      DynGraphAt st'.mem dst vCap_d eCap_d H ∧
      (∀ a, a < dst ∨ dst + dynGraphSize vCap_d eCap_d ≤ a → st'.mem a = mem a) ∧
      c ≤ 115 * H.n + 175 * H.m + 160 := by
  suffices hmain : ∃ o st' c,
      Runs w p ω repackDynGraphProc (startState [src, dst, vCap_d, eCap_d] mem pos) o st' c ∧
      (o = .returned 0 ∧ DynGraphAt st'.mem dst vCap_d eCap_d H ∧
        (∀ a, a < dst ∨ dst + dynGraphSize vCap_d eCap_d ≤ a → st'.mem a = mem a)) ∧
      c ≤ 115 * H.n + 175 * H.m + 160 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, hc⟩
  rcases hdg with ⟨hH, hvlt, helt, hhdr0, hhdr1, hhdr2, hhdr3, hvPres,
    ⟨vL, hvL_len, hvL_nd, hvL_mem, hvL_at, hvPos⟩,
    hext, hint, hePres,
    ⟨eL, heL_len, heL_nd, heL_mem, heL_at, hePos⟩,
    heEnds, ⟨incL, hincL⟩⟩
  have hsz_s : dynGraphSize vCap_s eCap_s = 4 + 7 * vCap_s + 9 * eCap_s := rfl
  have hsz_d : dynGraphSize vCap_d eCap_d = 4 + 7 * vCap_d + 9 * eCap_d := rfl
  have hHn_le : H.n ≤ vCap_s := by
    have hsub : H.V ⊆ Finset.range vCap_s := fun v hv => Finset.mem_range.mpr (hvlt v hv)
    calc H.n = H.V.card := rfl
      _ ≤ (Finset.range vCap_s).card := Finset.card_le_card hsub
      _ = vCap_s := Finset.card_range vCap_s
  have hHm_le : H.m ≤ eCap_s := by
    have hsub : H.E ⊆ Finset.range eCap_s := fun e he => Finset.mem_range.mpr (helt e he)
    calc H.m = H.E.card := rfl
      _ ≤ (Finset.range eCap_s).card := Finset.card_le_card hsub
      _ = eCap_s := Finset.card_range eCap_s
  have hoffs : dgVCapOff = 0 ∧ dgECapOff = 1 ∧ dgNOff = 2 ∧ dgMOff = 3 := ⟨rfl, rfl, rfl, rfl⟩
  have hread_s : ∀ (m : ℕ → ℕ),
      (∀ a, a < dst ∨ dst + dynGraphSize vCap_d eCap_d ≤ a → m a = mem a) →
      ∀ off < dynGraphSize vCap_s eCap_s, m (src + off) = mem (src + off) :=
    fun m hfr off hoff => hfr (src + off) (by omega)
  refine runs_start_le ?_
  unfold repackDynGraphProc startState
  refine runs_seq_assign_flat (v := vCap_s) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := eCap_s) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := H.n) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := H.m) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + dgVCapOff) (v := vCap_d) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + dgECapOff) (v := eCap_d) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + dgNOff) (v := H.n) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := dst + dgMOff) (v := H.m) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := dgVListBase src vCap_s) (by dsimp [dgVListBase]; eval_expr) ?_
  refine runs_seq_assign_flat (v := dgExtToIntBase src vCap_s) (by dsimp [dgExtToIntBase]; eval_expr) ?_
  refine runs_seq_assign_flat (v := dgSlotDegBase src vCap_s) (by dsimp [dgSlotDegBase]; eval_expr) ?_
  refine runs_seq_assign_flat (v := dgIncHeadBase src vCap_s) (by dsimp [dgIncHeadBase]; eval_expr) ?_
  let VInv : ℕ → State → Prop := fun i st =>
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = vCap_d ∧ st.regs 3 = eCap_d ∧
    st.regs 4 = vCap_s ∧ st.regs 5 = eCap_s ∧ st.regs 6 = H.n ∧ st.regs 7 = H.m ∧
    st.regs 8 = dgVListBase src vCap_s ∧ st.regs 9 = dgExtToIntBase src vCap_s ∧
    st.regs 10 = dgSlotDegBase src vCap_s ∧ st.regs 11 = dgIncHeadBase src vCap_s ∧
    st.regs 12 = i ∧
    st.mem (dst + dgVCapOff) = vCap_d ∧ st.mem (dst + dgECapOff) = eCap_d ∧
    st.mem (dst + dgNOff) = H.n ∧ st.mem (dst + dgMOff) = H.m ∧
    (∀ a, a < dst ∨ dst + dynGraphSize vCap_d eCap_d ≤ a → st.mem a = mem a) ∧
    (∀ a, dgEPresBase dst vCap_d ≤ a → a < dst + dynGraphSize vCap_d eCap_d → st.mem a = 0) ∧
    (∀ j (hj : j < i), ∀ (hj' : j < vL.length),
      let v := vL[j]
      let s := mem (dgExtToIntBase src vCap_s + v)
      st.mem (dgVPresBase dst + v) = 1 ∧ st.mem (dgVListBase dst vCap_d + j) = v ∧
      st.mem (dgVPosBase dst vCap_d + v) = j ∧ st.mem (dgExtToIntBase dst vCap_d + v) = s ∧
      st.mem (dgIntToExtBase dst vCap_d + s) = v ∧
      st.mem (dgSlotDegBase dst vCap_d + s) = mem (dgSlotDegBase src vCap_s + s) ∧
      st.mem (dgIncHeadBase dst vCap_d + s) = mem (dgIncHeadBase src vCap_s + s)) ∧
    (∀ v < vCap_d, (∀ j (hj : j < i), ∀ (hj' : j < vL.length), vL[j] ≠ v) →
      st.mem (dgVPresBase dst + v) = 0) ∧
    (∀ s < vCap_d, (∀ j (hj : j < i), ∀ (hj' : j < vL.length),
        mem (dgExtToIntBase src vCap_s + vL[j]) ≠ s) →
      st.mem (dgSlotDegBase dst vCap_d + s) = 0 ∧ st.mem (dgIncHeadBase dst vCap_d + s) = 0)
  have hvLoop : Triple w p
      (fun st => st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = vCap_d ∧ st.regs 3 = eCap_d ∧
        st.regs 4 = vCap_s ∧ st.regs 5 = eCap_s ∧ st.regs 6 = H.n ∧ st.regs 7 = H.m ∧
        st.regs 8 = dgVListBase src vCap_s ∧ st.regs 9 = dgExtToIntBase src vCap_s ∧
        st.regs 10 = dgSlotDegBase src vCap_s ∧ st.regs 11 = dgIncHeadBase src vCap_s ∧
        st.mem (dst + dgVCapOff) = vCap_d ∧ st.mem (dst + dgECapOff) = eCap_d ∧
        st.mem (dst + dgNOff) = H.n ∧ st.mem (dst + dgMOff) = H.m ∧
        (∀ a, a < dst ∨ dst + dynGraphSize vCap_d eCap_d ≤ a → st.mem a = mem a) ∧
        (∀ a, dst + 4 ≤ a → a < dst + dynGraphSize vCap_d eCap_d → st.mem a = 0))
      (forRange 12 (.const 0) (.reg 6)
        (.assign 13 (.load (.bin .add (.reg 8) (.reg 12))) ;;
         .assign 14 (.load (.bin .add (.reg 9) (.reg 13))) ;;
         .store (.bin .add (.bin .add (.reg 1) (.const 4)) (.reg 13)) (.const 1) ;;
         .store (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.reg 2)) (.reg 12)) (.reg 13) ;;
         .store (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 2) (.reg 2))) (.reg 13)) (.reg 12) ;;
         .store (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 3) (.reg 2))) (.reg 13)) (.reg 14) ;;
         .store (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 4) (.reg 2))) (.reg 14)) (.reg 13) ;;
         .store (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 5) (.reg 2))) (.reg 14))
           (.load (.bin .add (.reg 10) (.reg 14))) ;;
         .store (.bin .add (.bin .add (.bin .add (.reg 1) (.const 4)) (.bin .mul (.const 6) (.reg 2))) (.reg 14))
           (.load (.bin .add (.reg 11) (.reg 14)))))
      (normalPost (VInv H.n)) (fun _ => 115 * H.n + 7) := by
    refine (Triple.forRange_const 105 0 H.n (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st hst => by
        rcases hst with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11,
          mh0, mh1, mh2, mh3, hfr, hze⟩
        refine ⟨by eval_expr, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, by simp,
          mh0, mh1, mh2, mh3, hfr,
          fun a ha1 ha2 => hze a (by dsimp [dgEPresBase] at ha1; omega) ha2,
          fun j hj _ => by omega,
          fun v hv _ => hze _ (by dsimp [dgVPresBase]; omega) (by dsimp [dgVPresBase]; omega),
          fun s hs _ => ⟨hze _ (by dsimp [dgSlotDegBase]; omega) (by dsimp [dgSlotDegBase]; omega),
            hze _ (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase]; omega)⟩⟩)
      (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h6 := hi.2.2.2.2.2.2.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12,
          mh0, mh1, mh2, mh3, hfr, hzeE, hdone, hv0, hs0⟩
        have hiL : i < vL.length := by omega
        set v := vL[i]
        have hv_mem : v ∈ H.V := (hvL_mem v).mp (List.getElem_mem hiL)
        have hv_lt : v < vCap_s := hvlt v hv_mem
        set s := mem (dgExtToIntBase src vCap_s + v)
        have hs_mem : s ∈ H.V := (hext v hv_mem).1
        have hs_lt : s < vCap_s := hvlt s hs_mem
        have hv_at : st.mem (dgVListBase src vCap_s + i) = v := by
          have := hread_s st.mem hfr (4 + vCap_s + i) (by omega)
          have heq : src + (4 + vCap_s + i) = dgVListBase src vCap_s + i := by dsimp [dgVListBase]; omega
          rw [← heq, this, heq]; exact hvL_at i hiL
        have hs_at : st.mem (dgExtToIntBase src vCap_s + v) = s := by
          have := hread_s st.mem hfr (4 + 3 * vCap_s + v) (by omega)
          have heq : src + (4 + 3 * vCap_s + v) = dgExtToIntBase src vCap_s + v := by dsimp [dgExtToIntBase]; omega
          rw [← heq, this, heq]
        set degVal := mem (dgSlotDegBase src vCap_s + s)
        set headVal := mem (dgIncHeadBase src vCap_s + s)
        have hdegW : degVal < 2 ^ w := hMemW _ (by dsimp [dgSlotDegBase]; omega) (by dsimp [dgSlotDegBase]; omega)
        have hheadW : headVal < 2 ^ w := hMemW _ (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase]; omega)
        have hv_ne_prev : ∀ j (hj : j < i), ∀ (hj' : j < vL.length), vL[j] ≠ v := by
          intro j hj hj' hEq
          have := (List.nodup_iff_injective_getElem.mp hvL_nd) (a₁ := ⟨j, hj'⟩) (a₂ := ⟨i, hiL⟩) hEq
          simp only [Fin.mk.injEq] at this; omega
        have hs_ne_prev : ∀ j (hj : j < i), ∀ (hj' : j < vL.length),
            mem (dgExtToIntBase src vCap_s + vL[j]) ≠ s := by
          intro j hj hj' hEq
          have h1 := (hext _ ((hvL_mem _).mp (List.getElem_mem hj'))).2
          have h2 := (hext _ hv_mem).2
          rw [hEq] at h1; exact hv_ne_prev j hj hj' (h1.symm.trans h2)
        refine runs_start_le ?_
        change ∃ o st' c, Runs w p ω' _ ⟨st.mem, st.regs, st.pos⟩ o st' c ∧ _
        refine runs_seq_assign_flat (v := v) (by
          have : dgVListBase src vCap_s + i < 2 ^ w := by dsimp [dgVListBase]; omega
          eval_expr) ?_
        refine runs_seq_assign_flat (v := s) (by
          have : dgExtToIntBase src vCap_s + v < 2 ^ w := by dsimp [dgExtToIntBase]; omega
          eval_expr) ?_
        refine runs_seq_store_flat (x := dgVPresBase dst + v) (v := 1)
          (by dsimp [dgVPresBase]; eval_expr) (by eval_expr) ?_
        refine runs_seq_store_flat (x := dgVListBase dst vCap_d + i) (v := v)
          (by dsimp [dgVListBase]; eval_expr) (by eval_expr) ?_
        refine runs_seq_store_flat (x := dgVPosBase dst vCap_d + v) (v := i)
          (by dsimp [dgVPosBase]; eval_expr) (by eval_expr) ?_
        refine runs_seq_store_flat (x := dgExtToIntBase dst vCap_d + v) (v := s)
          (by dsimp [dgExtToIntBase]; eval_expr) (by eval_expr) ?_
        refine runs_seq_store_flat (x := dgIntToExtBase dst vCap_d + s) (v := v)
          (by dsimp [dgIntToExtBase]; eval_expr) (by eval_expr) ?_
        have hfr5 : ∀ a, a < dst ∨ dst + dynGraphSize vCap_d eCap_d ≤ a →
            Function.update (Function.update (Function.update (Function.update
              (Function.update st.mem (dgVPresBase dst + v) 1)
              (dgVListBase dst vCap_d + i) v) (dgVPosBase dst vCap_d + v) i)
              (dgExtToIntBase dst vCap_d + v) s) (dgIntToExtBase dst vCap_d + s) v a = mem a :=
          fun a ha => by
            rw [Function.update_of_ne (by dsimp [dgIntToExtBase]; omega),
                Function.update_of_ne (by dsimp [dgExtToIntBase]; omega),
                Function.update_of_ne (by dsimp [dgVPosBase]; omega),
                Function.update_of_ne (by dsimp [dgVListBase]; omega),
                Function.update_of_ne (by dsimp [dgVPresBase]; omega)]
            exact hfr a ha
        have hdeg_rd : Function.update (Function.update (Function.update (Function.update
              (Function.update st.mem (dgVPresBase dst + v) 1)
              (dgVListBase dst vCap_d + i) v) (dgVPosBase dst vCap_d + v) i)
              (dgExtToIntBase dst vCap_d + v) s) (dgIntToExtBase dst vCap_d + s) v
              (dgSlotDegBase src vCap_s + s) = degVal := by
          have := hread_s _ hfr5 (4 + 5 * vCap_s + s) (by omega)
          have heq : src + (4 + 5 * vCap_s + s) = dgSlotDegBase src vCap_s + s := by dsimp [dgSlotDegBase]; omega
          rw [← heq, this, heq]
        refine runs_seq_store_flat (x := dgSlotDegBase dst vCap_d + s) (v := degVal)
          (by dsimp [dgSlotDegBase]; eval_expr)
          (by have : dgSlotDegBase src vCap_s + s < 2 ^ w := by dsimp [dgSlotDegBase]; omega
              eval_expr) ?_
        have hhead_rd : Function.update (Function.update (Function.update (Function.update
              (Function.update (Function.update st.mem (dgVPresBase dst + v) 1)
              (dgVListBase dst vCap_d + i) v) (dgVPosBase dst vCap_d + v) i)
              (dgExtToIntBase dst vCap_d + v) s) (dgIntToExtBase dst vCap_d + s) v)
              (dgSlotDegBase dst vCap_d + s) degVal (dgIncHeadBase src vCap_s + s) = headVal := by
          rw [Function.update_of_ne (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega)]
          have := hread_s _ hfr5 (4 + 6 * vCap_s + s) (by omega)
          have heq : src + (4 + 6 * vCap_s + s) = dgIncHeadBase src vCap_s + s := by dsimp [dgIncHeadBase]; omega
          rw [← heq, this, heq]
        refine runs_store_le (x := dgIncHeadBase dst vCap_d + s) (v := headVal)
          (by dsimp [dgIncHeadBase]; eval_expr)
          (by have : dgIncHeadBase src vCap_s + s < 2 ^ w := by dsimp [dgIncHeadBase]; omega
              eval_expr) ?_ (by wram_cost)
        change (VInv (i + 1) ⟨dgUpdV st.mem dst vCap_d i v s degVal headVal, _, _⟩ ∧ _)
        have hm'_out : ∀ a, a < dst + 4 ∨ dgEPresBase dst vCap_d ≤ a →
            dgUpdV st.mem dst vCap_d i v s degVal headVal a = st.mem a :=
          fun a ha => dgUpdV_ne
            (by dsimp [dgVPresBase, dgEPresBase] at ha ⊢; omega)
            (by dsimp [dgVListBase, dgEPresBase] at ha ⊢; omega)
            (by dsimp [dgVPosBase, dgEPresBase] at ha ⊢; omega)
            (by dsimp [dgExtToIntBase, dgEPresBase] at ha ⊢; omega)
            (by dsimp [dgIntToExtBase, dgEPresBase] at ha ⊢; omega)
            (by dsimp [dgSlotDegBase, dgEPresBase] at ha ⊢; omega)
            (by dsimp [dgIncHeadBase, dgEPresBase] at ha ⊢; omega)
        refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
          by simp [r5], by simp [r6], by simp [r7], by simp [r8], by simp [r9],
          by simp [r10], by simp [r11], by simp,
          (hm'_out _ (Or.inl (by dsimp [dgVCapOff]; omega))).trans mh0,
          (hm'_out _ (Or.inl (by dsimp [dgECapOff]; omega))).trans mh1,
          (hm'_out _ (Or.inl (by dsimp [dgNOff]; omega))).trans mh2,
          (hm'_out _ (Or.inl (by dsimp [dgMOff]; omega))).trans mh3,
          fun a ha => (hm'_out a (by dsimp [dgEPresBase]; omega)).trans (hfr a ha),
          fun a ha1 ha2 => (hm'_out a (Or.inr ha1)).trans (hzeE a ha1 ha2),
          ?_, ?_, ?_⟩, by simp [r12]⟩
        · intro j hj hj'
          by_cases hji : j = i
          · subst hji; exact dgUpdV_at (by omega) (by omega) (by omega)
          · have hltj : j < i := by omega
            have hvj_ne := hv_ne_prev j hltj hj'
            have hsj_ne := hs_ne_prev j hltj hj'
            have hvj_lt : vL[j] < vCap_s := hvlt _ ((hvL_mem _).mp (List.getElem_mem hj'))
            have hsj_lt : mem (dgExtToIntBase src vCap_s + vL[j]) < vCap_s :=
              hvlt _ (hext _ ((hvL_mem _).mp (List.getElem_mem hj'))).1
            have hd := hdone j hltj hj'
            refine ⟨(dgUpdV_ne (by dsimp [dgVPresBase]; omega) (by dsimp [dgVPresBase, dgVListBase]; omega)
                (by dsimp [dgVPresBase, dgVPosBase]; omega) (by dsimp [dgVPresBase, dgExtToIntBase]; omega)
                (by dsimp [dgVPresBase, dgIntToExtBase]; omega) (by dsimp [dgVPresBase, dgSlotDegBase]; omega)
                (by dsimp [dgVPresBase, dgIncHeadBase]; omega)).trans hd.1,
              (dgUpdV_ne (by dsimp [dgVListBase, dgVPresBase]; omega) (by dsimp [dgVListBase]; omega)
                (by dsimp [dgVListBase, dgVPosBase]; omega) (by dsimp [dgVListBase, dgExtToIntBase]; omega)
                (by dsimp [dgVListBase, dgIntToExtBase]; omega) (by dsimp [dgVListBase, dgSlotDegBase]; omega)
                (by dsimp [dgVListBase, dgIncHeadBase]; omega)).trans hd.2.1,
              (dgUpdV_ne (by dsimp [dgVPosBase, dgVPresBase]; omega) (by dsimp [dgVPosBase, dgVListBase]; omega)
                (by dsimp [dgVPosBase]; omega) (by dsimp [dgVPosBase, dgExtToIntBase]; omega)
                (by dsimp [dgVPosBase, dgIntToExtBase]; omega) (by dsimp [dgVPosBase, dgSlotDegBase]; omega)
                (by dsimp [dgVPosBase, dgIncHeadBase]; omega)).trans hd.2.2.1,
              (dgUpdV_ne (by dsimp [dgExtToIntBase, dgVPresBase]; omega) (by dsimp [dgExtToIntBase, dgVListBase]; omega)
                (by dsimp [dgExtToIntBase, dgVPosBase]; omega) (by dsimp [dgExtToIntBase]; omega)
                (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega) (by dsimp [dgExtToIntBase, dgSlotDegBase]; omega)
                (by dsimp [dgExtToIntBase, dgIncHeadBase]; omega)).trans hd.2.2.2.1,
              (dgUpdV_ne (by dsimp [dgIntToExtBase, dgVPresBase]; omega) (by dsimp [dgIntToExtBase, dgVListBase]; omega)
                (by dsimp [dgIntToExtBase, dgVPosBase]; omega) (by dsimp [dgIntToExtBase, dgExtToIntBase]; omega)
                (by dsimp [dgIntToExtBase]; omega) (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega)
                (by dsimp [dgIntToExtBase, dgIncHeadBase]; omega)).trans hd.2.2.2.2.1,
              (dgUpdV_ne (by dsimp [dgSlotDegBase, dgVPresBase]; omega) (by dsimp [dgSlotDegBase, dgVListBase]; omega)
                (by dsimp [dgSlotDegBase, dgVPosBase]; omega) (by dsimp [dgSlotDegBase, dgExtToIntBase]; omega)
                (by dsimp [dgSlotDegBase, dgIntToExtBase]; omega) (by dsimp [dgSlotDegBase]; omega)
                (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega)).trans hd.2.2.2.2.2.1,
              (dgUpdV_ne (by dsimp [dgIncHeadBase, dgVPresBase]; omega) (by dsimp [dgIncHeadBase, dgVListBase]; omega)
                (by dsimp [dgIncHeadBase, dgVPosBase]; omega) (by dsimp [dgIncHeadBase, dgExtToIntBase]; omega)
                (by dsimp [dgIncHeadBase, dgIntToExtBase]; omega) (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega)
                (by dsimp [dgIncHeadBase]; omega)).trans hd.2.2.2.2.2.2⟩
        · intro u hu hne
          have huv : u ≠ v := (hne i (by omega) hiL).symm
          exact (dgUpdV_ne (by dsimp [dgVPresBase]; omega) (by dsimp [dgVPresBase, dgVListBase]; omega)
              (by dsimp [dgVPresBase, dgVPosBase]; omega) (by dsimp [dgVPresBase, dgExtToIntBase]; omega)
              (by dsimp [dgVPresBase, dgIntToExtBase]; omega) (by dsimp [dgVPresBase, dgSlotDegBase]; omega)
              (by dsimp [dgVPresBase, dgIncHeadBase]; omega)).trans
            (hv0 u hu fun j hj hj' => hne j (by omega) hj')
        · intro s' hs' hne
          have hss : s' ≠ s := (hne i (by omega) hiL).symm
          have h0 := hs0 s' hs' fun j hj hj' => hne j (by omega) hj'
          refine ⟨(dgUpdV_ne (by dsimp [dgSlotDegBase, dgVPresBase]; omega) (by dsimp [dgSlotDegBase, dgVListBase]; omega)
              (by dsimp [dgSlotDegBase, dgVPosBase]; omega) (by dsimp [dgSlotDegBase, dgExtToIntBase]; omega)
              (by dsimp [dgSlotDegBase, dgIntToExtBase]; omega) (by dsimp [dgSlotDegBase]; omega)
              (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega)).trans h0.1,
            (dgUpdV_ne (by dsimp [dgIncHeadBase, dgVPresBase]; omega) (by dsimp [dgIncHeadBase, dgVListBase]; omega)
              (by dsimp [dgIncHeadBase, dgVPosBase]; omega) (by dsimp [dgIncHeadBase, dgExtToIntBase]; omega)
              (by dsimp [dgIncHeadBase, dgIntToExtBase]; omega) (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega)
              (by dsimp [dgIncHeadBase]; omega)).trans h0.2⟩)).mono_cost
      (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hvLoop ⟨by simp, by simp, by simp,
    by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
           Function.update_of_ne (by omega), Function.update_self],
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self],
    by dsimp only; exact Function.update_self _ _ _,
    fun a ha => by
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
    fun a ha1 ha2 => by
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hzero a (by omega) ha2⟩ (fun st₁ hV => ?_)
  rcases hV with ⟨r0, r1, r2, r3, r4, r5, r6, r7, _, _, _, _, _,
    mh0, mh1, mh2, mh3, hfr1, hzeE1, hVdone, hVv0, hVs0⟩
  change ∃ o st' c, Runs w p ω _ ⟨st₁.mem, st₁.regs, st₁.pos⟩ o st' c ∧ _
  refine runs_seq_assign_flat (v := dgEPresBase src vCap_s) (by dsimp [dgEPresBase]; eval_expr) ?_
  refine runs_seq_assign_flat (v := dgEPresBase dst vCap_d) (by dsimp [dgEPresBase]; eval_expr) ?_
  let EInv : ℕ → State → Prop := fun i st =>
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = vCap_d ∧ st.regs 3 = eCap_d ∧
    st.regs 4 = vCap_s ∧ st.regs 5 = eCap_s ∧ st.regs 6 = H.n ∧ st.regs 7 = H.m ∧
    st.regs 8 = dgEPresBase src vCap_s ∧ st.regs 9 = dgEPresBase dst vCap_d ∧ st.regs 12 = i ∧
    (∀ a, a < dgEPresBase dst vCap_d ∨ dst + dynGraphSize vCap_d eCap_d ≤ a → st.mem a = st₁.mem a) ∧
    (∀ j (hj : j < i), ∀ (hj' : j < eL.length),
      let e := eL[j]
      st.mem (dgEPresBase dst vCap_d + e) = 1 ∧ st.mem (dgEListBase dst vCap_d eCap_d + j) = e ∧
      st.mem (dgEPosBase dst vCap_d eCap_d + e) = j ∧
      st.mem (dgETailSlotBase dst vCap_d eCap_d + e) = mem (dgETailSlotBase src vCap_s eCap_s + e) ∧
      st.mem (dgEHeadSlotBase dst vCap_d eCap_d + e) = mem (dgEHeadSlotBase src vCap_s eCap_s + e) ∧
      st.mem (dgHePrevBase dst vCap_d eCap_d + 2 * e) = mem (dgHePrevBase src vCap_s eCap_s + 2 * e) ∧
      st.mem (dgHePrevBase dst vCap_d eCap_d + (2 * e + 1)) = mem (dgHePrevBase src vCap_s eCap_s + (2 * e + 1)) ∧
      st.mem (dgHeNextBase dst vCap_d eCap_d + 2 * e) = mem (dgHeNextBase src vCap_s eCap_s + 2 * e) ∧
      st.mem (dgHeNextBase dst vCap_d eCap_d + (2 * e + 1)) = mem (dgHeNextBase src vCap_s eCap_s + (2 * e + 1))) ∧
    (∀ e < eCap_d, (∀ j (hj : j < i), ∀ (hj' : j < eL.length), eL[j] ≠ e) →
      st.mem (dgEPresBase dst vCap_d + e) = 0)
  have heLoop : Triple w p
      (fun st => st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = vCap_d ∧ st.regs 3 = eCap_d ∧
        st.regs 4 = vCap_s ∧ st.regs 5 = eCap_s ∧ st.regs 6 = H.n ∧ st.regs 7 = H.m ∧
        st.regs 8 = dgEPresBase src vCap_s ∧ st.regs 9 = dgEPresBase dst vCap_d ∧ st.mem = st₁.mem)
      (forRange 12 (.const 0) (.reg 7)
        (.assign 13 (.load (.bin .add (.bin .add (.reg 8) (.reg 5)) (.reg 12))) ;;
         .store (.bin .add (.reg 9) (.reg 13)) (.const 1) ;;
         .store (.bin .add (.bin .add (.reg 9) (.reg 3)) (.reg 12)) (.reg 13) ;;
         .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 3))) (.reg 13)) (.reg 12) ;;
         .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 3) (.reg 3))) (.reg 13))
           (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 3) (.reg 5))) (.reg 13))) ;;
         .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 4) (.reg 3))) (.reg 13))
           (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 4) (.reg 5))) (.reg 13))) ;;
         .assign 14 (.bin .mul (.const 2) (.reg 13)) ;;
         .assign 15 (.bin .add (.reg 14) (.const 1)) ;;
         .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 5) (.reg 3))) (.reg 14))
           (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 5) (.reg 5))) (.reg 14))) ;;
         .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 5) (.reg 3))) (.reg 15))
           (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 5) (.reg 5))) (.reg 15))) ;;
         .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 7) (.reg 3))) (.reg 14))
           (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 7) (.reg 5))) (.reg 14))) ;;
         .store (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 7) (.reg 3))) (.reg 15))
           (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 7) (.reg 5))) (.reg 15)))))
      (normalPost (EInv H.m)) (fun _ => 175 * H.m + 7) := by
    refine (Triple.forRange_const 165 0 H.m (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st hst => by
        rcases hst with ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, hmeq⟩
        exact ⟨by eval_expr, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, by simp,
          fun _ _ => by rw [hmeq], fun j hj _ => by omega,
          fun e he _ => by rw [hmeq]; exact hzeE1 _ (by dsimp [dgEPresBase]; omega) (by dsimp [dgEPresBase]; omega)⟩)
      (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h7 := hi.2.2.2.2.2.2.2.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q12, hfrE, hEdone, he0⟩
        have hiL : i < eL.length := by omega
        set e := eL[i]
        have he_mem : e ∈ H.E := (heL_mem e).mp (List.getElem_mem hiL)
        have he_lt : e < eCap_s := helt e he_mem
        have he_ne_prev : ∀ j (hj : j < i), ∀ (hj' : j < eL.length), eL[j] ≠ e := by
          intro j hj hj' hEq
          have := (List.nodup_iff_injective_getElem.mp heL_nd) (a₁ := ⟨j, hj'⟩) (a₂ := ⟨i, hiL⟩) hEq
          simp only [Fin.mk.injEq] at this; omega
        have hsrc_at : ∀ off < dynGraphSize vCap_s eCap_s, st.mem (src + off) = mem (src + off) :=
          hread_s st.mem fun a ha => (hfrE a (by dsimp [dgEPresBase]; omega)).trans (hfr1 a ha)
        have he_at : st.mem (dgEListBase src vCap_s eCap_s + i) = e := by
          have := hsrc_at (4 + 7 * vCap_s + eCap_s + i) (by omega)
          have heq : src + (4 + 7 * vCap_s + eCap_s + i) = dgEListBase src vCap_s eCap_s + i := by dsimp [dgEListBase]; omega
          rw [← heq, this, heq]; exact heL_at i hiL
        set tVal := mem (dgETailSlotBase src vCap_s eCap_s + e)
        set hVal := mem (dgEHeadSlotBase src vCap_s eCap_s + e)
        set p0Val := mem (dgHePrevBase src vCap_s eCap_s + 2 * e)
        set p1Val := mem (dgHePrevBase src vCap_s eCap_s + (2 * e + 1))
        set n0Val := mem (dgHeNextBase src vCap_s eCap_s + 2 * e)
        set n1Val := mem (dgHeNextBase src vCap_s eCap_s + (2 * e + 1))
        have htW : tVal < 2 ^ w := hMemW _ (by dsimp [dgETailSlotBase]; omega) (by dsimp [dgETailSlotBase]; omega)
        have hhW : hVal < 2 ^ w := hMemW _ (by dsimp [dgEHeadSlotBase]; omega) (by dsimp [dgEHeadSlotBase]; omega)
        have hp0W : p0Val < 2 ^ w := hMemW _ (by dsimp [dgHePrevBase]; omega) (by dsimp [dgHePrevBase]; omega)
        have hp1W : p1Val < 2 ^ w := hMemW _ (by dsimp [dgHePrevBase]; omega) (by dsimp [dgHePrevBase]; omega)
        have hn0W : n0Val < 2 ^ w := hMemW _ (by dsimp [dgHeNextBase]; omega) (by dsimp [dgHeNextBase]; omega)
        have hn1W : n1Val < 2 ^ w := hMemW _ (by dsimp [dgHeNextBase]; omega) (by dsimp [dgHeNextBase]; omega)
        have hread_upd : ∀ (m : ℕ → ℕ),
            (∀ a, a < dgEPresBase dst vCap_d ∨ dst + dynGraphSize vCap_d eCap_d ≤ a → m a = st.mem a) →
            ∀ off < dynGraphSize vCap_s eCap_s, m (src + off) = mem (src + off) :=
          fun m hm off hoff => (hm (src + off) (by dsimp [dgEPresBase]; omega)).trans (hsrc_at off hoff)
        refine runs_start_le ?_
        change ∃ o st' c, Runs w p ω' _ ⟨st.mem, st.regs, st.pos⟩ o st' c ∧ _
        refine runs_seq_assign_flat (v := e) (by
          have : dgEPresBase src vCap_s + eCap_s + i = dgEListBase src vCap_s eCap_s + i := rfl
          have : dgEPresBase src vCap_s + eCap_s + i < 2 ^ w := by dsimp [dgEPresBase]; omega
          eval_expr) ?_
        refine runs_seq_store_flat (x := dgEPresBase dst vCap_d + e) (v := 1)
          (by dsimp [dgEPresBase]; eval_expr) (by eval_expr) ?_
        refine runs_seq_store_flat (x := dgEListBase dst vCap_d eCap_d + i) (v := e)
          (by dsimp [dgEPresBase, dgEListBase]; eval_expr) (by eval_expr) ?_
        refine runs_seq_store_flat (x := dgEPosBase dst vCap_d eCap_d + e) (v := i)
          (by dsimp [dgEPresBase, dgEPosBase]; eval_expr) (by eval_expr) ?_
        refine runs_seq_store_flat (x := dgETailSlotBase dst vCap_d eCap_d + e) (v := tVal)
          (by dsimp [dgEPresBase, dgETailSlotBase]; eval_expr)
          (by have heq : dgEPresBase src vCap_s + 3 * eCap_s + e = src + (4 + 7 * vCap_s + 3 * eCap_s + e) := by dsimp [dgEPresBase]; omega
              have hlt : dgEPresBase src vCap_s + 3 * eCap_s + e < 2 ^ w := by dsimp [dgEPresBase]; omega
              have hrd : Function.update (Function.update (Function.update st.mem
                  (dgEPresBase dst vCap_d + e) 1) (dgEListBase dst vCap_d eCap_d + i) e)
                  (dgEPosBase dst vCap_d eCap_d + e) i (dgEPresBase src vCap_s + 3 * eCap_s + e) = tVal := by
                rw [heq]; refine (hread_upd _ (fun a ha => by
                  rw [Function.update_of_ne (by dsimp [dgEPresBase, dgEPosBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEListBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase] at ha ⊢; omega)])
                  (4 + 7 * vCap_s + 3 * eCap_s + e) (by omega)).trans (by simp [tVal, dgETailSlotBase, Nat.add_assoc])
              eval_expr) ?_
        refine runs_seq_store_flat (x := dgEHeadSlotBase dst vCap_d eCap_d + e) (v := hVal)
          (by dsimp [dgEPresBase, dgEHeadSlotBase]; eval_expr)
          (by have heq : dgEPresBase src vCap_s + 4 * eCap_s + e = src + (4 + 7 * vCap_s + 4 * eCap_s + e) := by dsimp [dgEPresBase]; omega
              have hlt : dgEPresBase src vCap_s + 4 * eCap_s + e < 2 ^ w := by dsimp [dgEPresBase]; omega
              have hrd : Function.update (Function.update (Function.update (Function.update st.mem
                  (dgEPresBase dst vCap_d + e) 1) (dgEListBase dst vCap_d eCap_d + i) e)
                  (dgEPosBase dst vCap_d eCap_d + e) i) (dgETailSlotBase dst vCap_d eCap_d + e) tVal
                  (dgEPresBase src vCap_s + 4 * eCap_s + e) = hVal := by
                rw [heq]; refine (hread_upd _ (fun a ha => by
                  rw [Function.update_of_ne (by dsimp [dgEPresBase, dgETailSlotBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEPosBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEListBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase] at ha ⊢; omega)])
                  (4 + 7 * vCap_s + 4 * eCap_s + e) (by omega)).trans (by simp [hVal, dgEHeadSlotBase, Nat.add_assoc])
              eval_expr) ?_
        refine runs_seq_assign_flat (v := 2 * e) (by eval_expr) ?_
        refine runs_seq_assign_flat (v := 2 * e + 1) (by eval_expr) ?_
        refine runs_seq_store_flat (x := dgHePrevBase dst vCap_d eCap_d + 2 * e) (v := p0Val)
          (by dsimp [dgEPresBase, dgHePrevBase]; eval_expr)
          (by have heq : dgEPresBase src vCap_s + 5 * eCap_s + 2 * e = src + (4 + 7 * vCap_s + 5 * eCap_s + 2 * e) := by dsimp [dgEPresBase]; omega
              have hlt : dgEPresBase src vCap_s + 5 * eCap_s + 2 * e < 2 ^ w := by dsimp [dgEPresBase]; omega
              have hrd : Function.update (Function.update (Function.update (Function.update (Function.update st.mem
                  (dgEPresBase dst vCap_d + e) 1) (dgEListBase dst vCap_d eCap_d + i) e)
                  (dgEPosBase dst vCap_d eCap_d + e) i) (dgETailSlotBase dst vCap_d eCap_d + e) tVal)
                  (dgEHeadSlotBase dst vCap_d eCap_d + e) hVal (dgEPresBase src vCap_s + 5 * eCap_s + 2 * e) = p0Val := by
                rw [heq]; refine (hread_upd _ (fun a ha => by
                  rw [Function.update_of_ne (by dsimp [dgEPresBase, dgEHeadSlotBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgETailSlotBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEPosBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEListBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase] at ha ⊢; omega)])
                  (4 + 7 * vCap_s + 5 * eCap_s + 2 * e) (by omega)).trans (by simp [p0Val, dgHePrevBase, Nat.add_assoc])
              eval_expr) ?_
        refine runs_seq_store_flat (x := dgHePrevBase dst vCap_d eCap_d + (2 * e + 1)) (v := p1Val)
          (by dsimp [dgEPresBase, dgHePrevBase]; eval_expr)
          (by have heq : dgEPresBase src vCap_s + 5 * eCap_s + (2 * e + 1) = src + (4 + 7 * vCap_s + 5 * eCap_s + (2 * e + 1)) := by dsimp [dgEPresBase]; omega
              have hlt : dgEPresBase src vCap_s + 5 * eCap_s + (2 * e + 1) < 2 ^ w := by dsimp [dgEPresBase]; omega
              have hrd : Function.update (Function.update (Function.update (Function.update (Function.update (Function.update st.mem
                  (dgEPresBase dst vCap_d + e) 1) (dgEListBase dst vCap_d eCap_d + i) e)
                  (dgEPosBase dst vCap_d eCap_d + e) i) (dgETailSlotBase dst vCap_d eCap_d + e) tVal)
                  (dgEHeadSlotBase dst vCap_d eCap_d + e) hVal) (dgHePrevBase dst vCap_d eCap_d + 2 * e) p0Val
                  (dgEPresBase src vCap_s + 5 * eCap_s + (2 * e + 1)) = p1Val := by
                rw [heq]; refine (hread_upd _ (fun a ha => by
                  rw [Function.update_of_ne (by dsimp [dgEPresBase, dgHePrevBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEHeadSlotBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgETailSlotBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEPosBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEListBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase] at ha ⊢; omega)])
                  (4 + 7 * vCap_s + 5 * eCap_s + (2 * e + 1)) (by omega)).trans (by simp [p1Val, dgHePrevBase, Nat.add_assoc])
              eval_expr) ?_
        refine runs_seq_store_flat (x := dgHeNextBase dst vCap_d eCap_d + 2 * e) (v := n0Val)
          (by dsimp [dgEPresBase, dgHeNextBase]; eval_expr)
          (by have heq : dgEPresBase src vCap_s + 7 * eCap_s + 2 * e = src + (4 + 7 * vCap_s + 7 * eCap_s + 2 * e) := by dsimp [dgEPresBase]; omega
              have hlt : dgEPresBase src vCap_s + 7 * eCap_s + 2 * e < 2 ^ w := by dsimp [dgEPresBase]; omega
              have hrd : Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update st.mem
                  (dgEPresBase dst vCap_d + e) 1) (dgEListBase dst vCap_d eCap_d + i) e)
                  (dgEPosBase dst vCap_d eCap_d + e) i) (dgETailSlotBase dst vCap_d eCap_d + e) tVal)
                  (dgEHeadSlotBase dst vCap_d eCap_d + e) hVal) (dgHePrevBase dst vCap_d eCap_d + 2 * e) p0Val)
                  (dgHePrevBase dst vCap_d eCap_d + (2 * e + 1)) p1Val
                  (dgEPresBase src vCap_s + 7 * eCap_s + 2 * e) = n0Val := by
                rw [heq]; refine (hread_upd _ (fun a ha => by
                  rw [Function.update_of_ne (by dsimp [dgEPresBase, dgHePrevBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgHePrevBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEHeadSlotBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgETailSlotBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEPosBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEListBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase] at ha ⊢; omega)])
                  (4 + 7 * vCap_s + 7 * eCap_s + 2 * e) (by omega)).trans (by simp [n0Val, dgHeNextBase, Nat.add_assoc])
              eval_expr) ?_
        refine runs_store_le (x := dgHeNextBase dst vCap_d eCap_d + (2 * e + 1)) (v := n1Val)
          (by dsimp [dgEPresBase, dgHeNextBase]; eval_expr)
          (by have heq : dgEPresBase src vCap_s + 7 * eCap_s + (2 * e + 1) = src + (4 + 7 * vCap_s + 7 * eCap_s + (2 * e + 1)) := by dsimp [dgEPresBase]; omega
              have hlt : dgEPresBase src vCap_s + 7 * eCap_s + (2 * e + 1) < 2 ^ w := by dsimp [dgEPresBase]; omega
              have hrd : Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update st.mem
                  (dgEPresBase dst vCap_d + e) 1) (dgEListBase dst vCap_d eCap_d + i) e)
                  (dgEPosBase dst vCap_d eCap_d + e) i) (dgETailSlotBase dst vCap_d eCap_d + e) tVal)
                  (dgEHeadSlotBase dst vCap_d eCap_d + e) hVal) (dgHePrevBase dst vCap_d eCap_d + 2 * e) p0Val)
                  (dgHePrevBase dst vCap_d eCap_d + (2 * e + 1)) p1Val) (dgHeNextBase dst vCap_d eCap_d + 2 * e) n0Val
                  (dgEPresBase src vCap_s + 7 * eCap_s + (2 * e + 1)) = n1Val := by
                rw [heq]; refine (hread_upd _ (fun a ha => by
                  rw [Function.update_of_ne (by dsimp [dgEPresBase, dgHeNextBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgHePrevBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgHePrevBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEHeadSlotBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgETailSlotBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEPosBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase, dgEListBase] at ha ⊢; omega),
                      Function.update_of_ne (by dsimp [dgEPresBase] at ha ⊢; omega)])
                  (4 + 7 * vCap_s + 7 * eCap_s + (2 * e + 1)) (by omega)).trans (by simp [n1Val, dgHeNextBase, Nat.add_assoc])
              eval_expr) ?_ (by wram_cost)
        change (EInv (i + 1) ⟨dgUpdE st.mem dst vCap_d eCap_d i e tVal hVal p0Val p1Val n0Val n1Val, _, _⟩ ∧ _)
        refine ⟨⟨by simp [q0], by simp [q1], by simp [q2], by simp [q3], by simp [q4],
          by simp [q5], by simp [q6], by simp [q7], by simp [q8], by simp [q9], by simp,
          fun a ha => (dgUpdE_ne (by dsimp [dgEPresBase] at ha ⊢; omega)
            (by dsimp [dgEPresBase, dgEListBase] at ha ⊢; omega) (by dsimp [dgEPresBase, dgEPosBase] at ha ⊢; omega)
            (by dsimp [dgEPresBase, dgETailSlotBase] at ha ⊢; omega) (by dsimp [dgEPresBase, dgEHeadSlotBase] at ha ⊢; omega)
            (by dsimp [dgEPresBase, dgHePrevBase] at ha ⊢; omega) (by dsimp [dgEPresBase, dgHePrevBase] at ha ⊢; omega)
            (by dsimp [dgEPresBase, dgHeNextBase] at ha ⊢; omega) (by dsimp [dgEPresBase, dgHeNextBase] at ha ⊢; omega)).trans
            (hfrE a ha),
          ?_, ?_⟩, by simp [q12]⟩
        · intro j hj hj'
          by_cases hji : j = i
          · subst hji; exact dgUpdE_at (by omega) (by omega)
          · have hltj : j < i := by omega
            have hej_ne := he_ne_prev j hltj hj'
            have hej_lt : eL[j] < eCap_s := helt _ ((heL_mem _).mp (List.getElem_mem hj'))
            have hd := hEdone j hltj hj'
            have hp := dgUpdE_pres_other (m := st.mem) (dst := dst) (vCap_d := vCap_d)
              (eCap_d := eCap_d) (i := i) (j := j) (e := e) (e' := eL[j])
              (tVal := tVal) (hVal := hVal) (p0 := p0Val) (p1 := p1Val) (n0 := n0Val) (n1 := n1Val)
              (by omega) (by omega) (by omega) (by omega) hji hej_ne
            exact ⟨hp.1.trans hd.1, hp.2.1.trans hd.2.1, hp.2.2.1.trans hd.2.2.1,
              hp.2.2.2.1.trans hd.2.2.2.1, hp.2.2.2.2.1.trans hd.2.2.2.2.1,
              hp.2.2.2.2.2.1.trans hd.2.2.2.2.2.1, hp.2.2.2.2.2.2.1.trans hd.2.2.2.2.2.2.1,
              hp.2.2.2.2.2.2.2.1.trans hd.2.2.2.2.2.2.2.1,
              hp.2.2.2.2.2.2.2.2.trans hd.2.2.2.2.2.2.2.2⟩
        · intro e' he' hne
          have hee' : e' ≠ e := (hne i (by omega) hiL).symm
          exact (dgUpdE_ne (by dsimp [dgEPresBase]; omega) (by dsimp [dgEPresBase, dgEListBase]; omega)
              (by dsimp [dgEPresBase, dgEPosBase]; omega) (by dsimp [dgEPresBase, dgETailSlotBase]; omega)
              (by dsimp [dgEPresBase, dgEHeadSlotBase]; omega) (by dsimp [dgEPresBase, dgHePrevBase]; omega)
              (by dsimp [dgEPresBase, dgHePrevBase]; omega) (by dsimp [dgEPresBase, dgHeNextBase]; omega)
              (by dsimp [dgEPresBase, dgHeNextBase]; omega)).trans
            (he0 e' he' fun j hj hj' => hne j (by omega) hj'))).mono_cost
      (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le heLoop ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3],
    by simp [r4], by simp [r5], by simp [r6], by simp [r7], by simp, by simp, rfl⟩
    (fun st₂ hE => ?_)
  rcases hE with ⟨_, _, _, _, _, _, _, _, _, _, _, hfr2, hEdone, hEe0⟩
  refine runs_ret_le (by eval_expr) ⟨rfl, ?_, fun a ha =>
    (hfr2 a (by dsimp [dgEPresBase]; omega)).trans (hfr1 a ha)⟩
    (by dsimp [Expr.size]; omega)
  have hv_pres : ∀ a < dgEPresBase dst vCap_d, st₂.mem a = st₁.mem a := fun a ha => hfr2 a (Or.inl ha)
  have hv_idx : ∀ v ∈ H.V, ∃ j, ∃ (hj : j < vL.length), vL[j] = v :=
    fun v hv => List.mem_iff_getElem.mp ((hvL_mem v).mpr hv)
  have he_idx : ∀ e ∈ H.E, ∃ j, ∃ (hj : j < eL.length), eL[j] = e :=
    fun e he => List.mem_iff_getElem.mp ((heL_mem e).mpr he)
  have hext_eq : ∀ v ∈ H.V,
      st₂.mem (dgExtToIntBase dst vCap_d + v) = mem (dgExtToIntBase src vCap_s + v) := by
    intro v hv; obtain ⟨j, hj, rfl⟩ := hv_idx v hv; have hv_lt := hvlt _ hv
    exact (hv_pres _ (by dsimp [dgExtToIntBase, dgEPresBase]; omega)).trans (hVdone j (by omega) hj).2.2.2.1
  have hint_eq : ∀ s ∈ H.V,
      st₂.mem (dgIntToExtBase dst vCap_d + s) = mem (dgIntToExtBase src vCap_s + s) := by
    intro s hs; set v := mem (dgIntToExtBase src vCap_s + s)
    obtain ⟨j, hj, hjEq⟩ := hv_idx v (hint s hs).1; have hs_lt := hvlt s hs
    have hd := (hVdone j (by omega) hj).2.2.2.2.1; rw [hjEq, (hint s hs).2] at hd
    exact (hv_pres _ (by dsimp [dgIntToExtBase, dgEPresBase]; omega)).trans hd
  have htail_eq : ∀ e ∈ H.E,
      st₂.mem (dgETailSlotBase dst vCap_d eCap_d + e) = mem (dgETailSlotBase src vCap_s eCap_s + e) := by
    intro e he; obtain ⟨j, hj, rfl⟩ := he_idx e he; exact (hEdone j (by omega) hj).2.2.2.1
  have hhead_eq : ∀ e ∈ H.E,
      st₂.mem (dgEHeadSlotBase dst vCap_d eCap_d + e) = mem (dgEHeadSlotBase src vCap_s eCap_s + e) := by
    intro e he; obtain ⟨j, hj, rfl⟩ := he_idx e he; exact (hEdone j (by omega) hj).2.2.2.2.1
  refine ⟨hH, fun v hv => lt_of_lt_of_le (hvlt v hv) hvCap, fun e he => lt_of_lt_of_le (helt e he) heCap,
    (hv_pres _ (by dsimp [dgVCapOff, dgEPresBase]; omega)).trans mh0,
    (hv_pres _ (by dsimp [dgECapOff, dgEPresBase]; omega)).trans mh1,
    (hv_pres _ (by dsimp [dgNOff, dgEPresBase]; omega)).trans mh2,
    (hv_pres _ (by dsimp [dgMOff, dgEPresBase]; omega)).trans mh3,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    split_ifs with hmem
    · obtain ⟨j, hj, rfl⟩ := hv_idx v hmem
      exact (hv_pres _ (by dsimp [dgVPresBase, dgEPresBase]; omega)).trans (hVdone j (by omega) hj).1
    · exact (hv_pres _ (by dsimp [dgVPresBase, dgEPresBase]; omega)).trans
        (hVv0 v hv fun j _ hj' hEq => hmem (hEq ▸ (hvL_mem _).mp (List.getElem_mem hj')))
  · refine ⟨vL, hvL_len, hvL_nd, hvL_mem,
      fun i hi => (hv_pres _ (by dsimp [dgVListBase, dgEPresBase]; omega)).trans (hVdone i (by omega) hi).2.1,
      fun i hi => by
        have := hvlt _ ((hvL_mem _).mp (List.getElem_mem hi))
        exact (hv_pres _ (by dsimp [dgVPosBase, dgEPresBase]; omega)).trans (hVdone i (by omega) hi).2.2.1⟩
  · intro v hv; rw [hext_eq v hv, hint_eq _ (hext v hv).1]; exact hext v hv
  · intro s hs; rw [hint_eq s hs, hext_eq _ (hint s hs).1]; exact hint s hs
  · intro e he
    split_ifs with hmem
    · obtain ⟨j, hj, rfl⟩ := he_idx e hmem; exact (hEdone j (by omega) hj).1
    · exact hEe0 e he fun j _ hj' hEq => hmem (hEq ▸ (heL_mem _).mp (List.getElem_mem hj'))
  · exact ⟨eL, heL_len, heL_nd, heL_mem, fun i hi => (hEdone i (by omega) hi).2.1,
      fun i hi => (hEdone i (by omega) hi).2.2.1⟩
  · intro e he; rw [htail_eq e he, hhead_eq e he, hext_eq _ (hH e he).1, hext_eq _ (hH e he).2]; exact heEnds e he
  · refine ⟨fun s => if s ∈ H.V then incL s else [], fun s hs => ?_⟩
    by_cases hsV : s ∈ H.V
    · dsimp only; rw [ite_eq_left hsV]
      have hs_lt : s < vCap_s := hvlt s hsV
      obtain ⟨hdll, hdeg, hmemL⟩ := hincL s hs_lt
      obtain ⟨j, hj, hjEq⟩ := hv_idx _ (hint s hsV).1
      have hd := hVdone j (by omega) hj
      have hdeg_s : st₂.mem (dgSlotDegBase dst vCap_d + s) = mem (dgSlotDegBase src vCap_s + s) := by
        have h1 := hd.2.2.2.2.2.1; rw [hjEq, (hint s hsV).2] at h1
        exact (hv_pres _ (by dsimp [dgSlotDegBase, dgEPresBase]; omega)).trans h1
      have hhead_s : st₂.mem (dgIncHeadBase dst vCap_d + s) = mem (dgIncHeadBase src vCap_s + s) := by
        have h1 := hd.2.2.2.2.2.2; rw [hjEq, (hint s hsV).2] at h1
        exact (hv_pres _ (by dsimp [dgIncHeadBase, dgEPresBase]; omega)).trans h1
      have hprev_ag : ∀ h ∈ incL s,
          st₂.mem (dgHePrevBase dst vCap_d eCap_d + h) = mem (dgHePrevBase src vCap_s eCap_s + h) := by
        intro h hh; have hhe := (hmemL h).mp hh
        obtain ⟨k, hk, hkEq⟩ := he_idx (h / 2) hhe.2.1
        rcases Nat.mod_two_eq_zero_or_one h with hmod | hmod
        · rw [show h = 2 * eL[k] by omega]; exact (hEdone k (by omega) hk).2.2.2.2.2.1
        · rw [show h = 2 * eL[k] + 1 by omega]; exact (hEdone k (by omega) hk).2.2.2.2.2.2.1
      have hnext_ag : ∀ h ∈ incL s,
          st₂.mem (dgHeNextBase dst vCap_d eCap_d + h) = mem (dgHeNextBase src vCap_s eCap_s + h) := by
        intro h hh; have hhe := (hmemL h).mp hh
        obtain ⟨k, hk, hkEq⟩ := he_idx (h / 2) hhe.2.1
        rcases Nat.mod_two_eq_zero_or_one h with hmod | hmod
        · rw [show h = 2 * eL[k] by omega]; exact (hEdone k (by omega) hk).2.2.2.2.2.2.2.1
        · rw [show h = 2 * eL[k] + 1 by omega]; exact (hEdone k (by omega) hk).2.2.2.2.2.2.2.2
      refine ⟨⟨hdll.1, fun h hh => lt_of_lt_of_le (hdll.2.1 h hh) (by omega),
          hhead_s.trans hdll.2.2.1, fun i hi => ⟨(hprev_ag _ (List.getElem_mem hi)).trans (hdll.2.2.2 i hi).1,
            (hnext_ag _ (List.getElem_mem hi)).trans (hdll.2.2.2 i hi).2⟩⟩,
        hdeg_s.trans hdeg, fun h => ?_⟩
      rw [hmemL h]
      constructor
      · rintro ⟨hlt, heG, hend⟩; refine ⟨by omega, heG, ?_⟩
        split_ifs at hend ⊢
        · rw [htail_eq _ heG]; exact hend
        · rw [hhead_eq _ heG]; exact hend
      · rintro ⟨hlt, heG, hend⟩; refine ⟨by have := helt _ heG; omega, heG, ?_⟩
        split_ifs at hend ⊢
        · rw [htail_eq _ heG] at hend; exact hend
        · rw [hhead_eq _ heG] at hend; exact hend
    · dsimp only; rw [ite_eq_right hsV]
      have h0 := hVs0 s hs fun j _ hj' hEq => hsV (hEq ▸ (hext _ ((hvL_mem _).mp (List.getElem_mem hj'))).1)
      refine ⟨IsDoublyLinkedList.nil ((hv_pres _ (by dsimp [dgIncHeadBase, dgEPresBase]; omega)).trans h0.2),
        (hv_pres _ (by dsimp [dgSlotDegBase, dgEPresBase]; omega)).trans h0.1, fun h => ?_⟩
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨_, heG, hend⟩
      split_ifs at hend
      · rw [htail_eq _ heG, (heEnds _ heG).1] at hend; exact hsV (hend ▸ (hext _ (hH _ heG).1).1)
      · rw [hhead_eq _ heG, (heEnds _ heG).2] at hend; exact hsV (hend ▸ (hext _ (hH _ heG).2).1)

end MinCostFlow.SparseCore.Program
