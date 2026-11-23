module

public import MinCostFlow.MinRatio.DetectTreeSearch
import WordRAM.Tactic
import MinCostFlow.MinRatio.PathTreeExpose

/-!
# Searching and reading one Detect slot

The proof of Theorem 5.1 (pages 29–30) finds a ready edge, then
resets its detector. When a ready slot exists, a point read obtains
the record needed for the reset. The read uses the heap above the
reserved search workspace.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM LinkCut

/-- Use the bound in register 4 as the point-read heap. Register 3
keeps the selected slot and register 5 receives the point-read heap. -/
@[expose] def detectSearchRead (find read : ℕ) : Stmt :=
  detectTreeSearch find ;;
  .cond (.reg 3) (.call 5 read [.reg 0, .reg 3, .reg 4]) .nop

/-- The search and optional read have no random statements. -/
theorem detectSearchRead_noRand (find read : ℕ) : (detectSearchRead find read).NoRand := by
  simp [detectSearchRead, detectTreeSearch_noRand, Stmt.NoRand]

/-- On success, the linked calls leave the exact point record. At
exhaustion the read is skipped. Both branches retain amortized accounting. -/
theorem detectSearchRead_runs {w L constant init handle heap top : ℕ}
    {fmt : Num.Format w} {p : Program} {st : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hregs : st.regs 0 = handle ∧ st.regs 1 = heap)
    (hh : handle < 2 ^ w)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 6 s [handle, heap] st.mem)
    (hrep : R.rep handle s x st.mem)
    (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hz : ZeroFrom st.mem heap) :
    heap + allocation 6 s.n [handle, heap] ≤ top →
    st.regs 4 = top → top < 2 ^ w →
    (∀ slot mem, pathTreeReady s slot →
      (pathTreeMachineContract fmt L constant allocation).pre 4
        (lctExpose pathPayload s slot) [handle, slot, top] mem ∧
      top + allocation 4 (lctExpose pathPayload s slot).n [handle, slot, top] < 2 ^ w) →
    ∃ (s' : PathTreeState) (cost ret slot : ℕ) (out : State) (y : R.τ),
      Runs w p ω (detectSearchRead (op 6) (op 4)) st .normal out cost ∧
      out.regs 3 = slot ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 5 → out.regs r = st.regs r) ∧
      R.rep handle s' y out.mem ∧ ZeroFrom out.mem ret ∧ heap ≤ ret ∧
      (∀ a < heap, ¬ R.foot handle x a → out.mem a = st.mem a) ∧
      (∀ a, R.foot handle y a → R.foot handle x a ∨ (heap ≤ a ∧ a < ret)) ∧
      (if slot = 0 then s' = s ∧ ret ≤ top ∧ out.regs 2 = ret ∧ ¬ ∃ a, pathTreeReady s a
        else pathTreeReady s slot ∧ s' = lctExpose pathPayload (lctExpose pathPayload s slot) slot ∧
          out.regs 5 = ret ∧ top ≤ ret ∧
          ret ≤ top + allocation 4 (lctExpose pathPayload s slot).n [handle, slot, top] ∧
          PathEdgeAt out.mem top fmt.limbBits L ((lctExpose pathPayload s slot).splay.nodes slot).val) ∧
      cost + R.phi handle y out.mem ≤
        2 * pathTreeBudget constant L s.n + R.phi handle x st.mem + 14 := by
  intro htopSpace htopReg htop hread
  obtain ⟨s₁, c, ptr, slot, mid, y, hsearch, hptr, hslot, hregisters, hrep₁, hm, hresult, hc⟩ :=
    detectTreeSearch_runs (ω := ω) himpl hregs hh hpre hrep hfoot hz (htopSpace.trans_lt htop)
  have hcond : (Expr.reg 3).eval w mid = some slot := by simp [Expr.eval, hslot]
  by_cases hzero : slot = 0
  · have hnone := (ite_eq_left hzero).mp hresult
    have hnop : Runs w p ω .nop mid .normal mid 1 := runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
    have hbranch : Runs w p ω
        (.cond (.reg 3) (.call 5 (op 4) [.reg 0, .reg 3, .reg 4]) .nop)
        mid .normal mid 3 :=
      runs_cond_iff.mpr ⟨slot, 1, hcond, by simpa only [ite_eq_left hzero] using hnop, rfl⟩
    exact ⟨s₁, c + 3 + 1, ptr, slot, mid, y,
      runs_seq_iff.mpr (Or.inr ⟨mid, c, 3, hsearch, hbranch, rfl⟩),
      hslot, (fun r h₂ h₃ _ => hregisters r h₂ h₃), hrep₁, hm.2.2.1, hm.1,
      hm.2.2.2.1, hm.2.2.2.2, (ite_eq_left hzero).mpr ⟨hnone.1, hm.2.1.trans htopSpace, hptr, hnone.2⟩, by omega⟩
  · obtain ⟨hready, hs⟩ := (ite_eq_right hzero).mp hresult
    subst s₁
    have he := pathTreeReady_bounds hready
    have hslotw : slot < 2 ^ w := by
      obtain ⟨_, _, hn, _, _⟩ := hpre
      omega
    have hmid₀ : mid.regs 0 = handle := (hregisters 0 (by decide) (by decide)).trans hregs.1
    have hmid₄ : mid.regs 4 = top := (hregisters 4 (by decide) (by decide)).trans htopReg
    have hfoot₁ : ∀ a, R.foot handle y a → a < top := by
      intro a ha
      rcases hm.2.2.2.2 a ha with ho | ⟨_, hhi⟩
      · have := hfoot a ho
        omega
      · have hle : ptr ≤ top := hm.2.1.trans htopSpace
        exact hhi.trans_le hle
    have hzero₁ : ZeroFrom mid.mem top := fun a ha => hm.2.2.1 a ((hm.2.1.trans htopSpace).trans ha)
    obtain ⟨hp, hroom⟩ := hread slot mid.mem hready
    obtain ⟨s₂, d, after, z, ret, hcall, hrep₂, hpost, hm₂, hd⟩ :=
      pathTree_runs_call (i := 4) (reg := 5) (st := mid) (ω := ω)
        (args := [.reg 0, .reg 3, .reg 4]) (vs := [handle, slot, top])
        himpl (by simp [evalArgs, Expr.eval, hmid₀, hslot, hmid₄])
        (by wram_words) rfl hrep₁ hp hfoot₁ hzero₁ hroom
    let out := { after with regs := Function.update mid.regs 5 ret }
    have hbranch : Runs w p ω
        (.cond (.reg 3) (.call 5 (op 4) [.reg 0, .reg 3, .reg 4]) .nop)
        mid .normal out (d + 2) :=
      runs_cond_iff.mpr ⟨slot, d, hcond, by simpa only [ite_eq_right hzero] using hcall, by simp [Expr.size]; omega⟩
    have hrecord : PathEdgeAt after.mem top fmt.limbBits L (s₂.splay.nodes slot).val := hpost.2
    have hn : (lctExpose pathPayload s slot).n = s.n := rfl
    refine ⟨s₂, c + (d + 2) + 1, ret, slot, out, z,
      runs_seq_iff.mpr (Or.inr ⟨mid, c, _, hsearch, hbranch, rfl⟩),
      by simp [out, hslot], ?_, hrep₂, hm₂.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · intro r h₂ h₃ h₅
      simpa only [out, Function.update_of_ne h₅] using hregisters r h₂ h₃
    · exact (Nat.le_add_right _ _).trans (htopSpace.trans hm₂.1)
    · intro a ha houtside
      have hmidOutside : ¬ R.foot handle y a := by
        intro h
        rcases hm.2.2.2.2 a h with hold | ⟨hlo, _⟩
        · exact houtside hold
        · exact (Nat.not_le_of_gt ha) hlo
      exact (hm₂.2.2.2.1 a (by change a < top; omega) hmidOutside).trans
        (hm.2.2.2.1 a ha houtside)
    · intro a ha
      have hptrTop : ptr ≤ top := hm.2.1.trans htopSpace
      have htopRet : top ≤ ret := hm₂.1
      rcases hm₂.2.2.2.2 a ha with hold | ⟨hlo, hhi⟩
      · rcases hm.2.2.2.2 a hold with hbefore | ⟨hlo, hhi⟩
        · exact Or.inl hbefore
        · exact Or.inr ⟨hlo, hhi.trans_le (hptrTop.trans htopRet)⟩
      · exact Or.inr ⟨Nat.le_trans ((Nat.le_add_right _ _).trans htopSpace) hlo, hhi⟩
    · have hvalue := (pathTree_expose_twice_value s slot hready.2.1).2.2
      have hs₂ : s₂ = lctExpose pathPayload (lctExpose pathPayload s slot) slot := hpost.1
      rw [hs₂, hvalue] at hrecord
      exact (ite_eq_right hzero).mpr ⟨hready, hs₂, by simp [out], hm₂.1, hm₂.2.1, hrecord⟩
    · change d + R.phi handle z after.mem ≤
        pathTreeBudget constant L (lctExpose pathPayload s slot).n + R.phi handle y mid.mem + 4 at hd
      rw [hn] at hd
      change c + (d + 2) + 1 + R.phi handle z after.mem ≤ _
      omega

end MinCostFlow.MinRatio
