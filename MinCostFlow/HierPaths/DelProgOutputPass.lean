module

public import MinCostFlow.HierPaths.DelProgOutputWalk

/-!
# Reporting from the newly ineligible connector work list

Read each connector and scan its walk in order. The pruned bits suppress repeats within
a walk and across different walks, including vertices reported during the owner pass.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Report from the connector work list at register 67, with length in register 68. -/
def delOutputConns : Stmt :=
  forRange 69 (.const 0) (.reg 68)
    (.seq (.assign 63 (.load (.bin .add (.reg 67) (.reg 69)))) delOutputWalk)

theorem delOutputConns_noRand : delOutputConns.NoRand := by
  simp [delOutputConns, forRange, forUp, Stmt.NoRand, delOutputWalk_noRand]

/-- Prefix of the output pass over connector walks. -/
def DelOutputConnInv (x : HierConcrete) (b base src : ℕ) (cs L : List ℕ)
    (mem0 : ℕ → ℕ) (i : ℕ) (s : State) : Prop :=
  let seen := x.walkPassVerts (cs.take i)
  let out := L ++ x.delReports seen
  s.regs 0 = b ∧ s.regs 58 = base ∧ s.regs 59 = out.length ∧
  s.regs 67 = src ∧ s.regs 68 = cs.length ∧ s.regs 69 = i ∧
  ListAt s.mem b (x.afterReports seen).encode ∧ ListAt s.mem base out ∧
  ListAt s.mem src cs ∧
  ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
    (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j

/-- A connector adds time proportional to its stored vertex list. -/
def delOutputConnCost (x : HierConcrete) (cs : List ℕ) (i : ℕ) : ℕ :=
  200 * (x.H.A.C.walk (cs.getD i 0)).verts.length + 106

/-- One iteration appends reports from the next connector's walk. -/
theorem delOutputConnBody_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base src i : ℕ} {cs L : List ℕ} {mem0 : ℕ → ℕ}
    (hb : b + x.encode.length ≤ base) (hsep : base + L.length + x.n ≤ src)
    (hw : base + L.length + 2 * x.n + 1 < 2 ^ w) (hsw : src + cs.length < 2 ^ w)
    (hc : ∀ c ∈ cs, c < x.H.A.C.numConn)
    (hv : ∀ c ∈ cs, ∀ v ∈ (x.H.A.C.walk c).verts, v < x.n)
    (hi : i < cs.length) :
    Triple w p (DelOutputConnInv x b base src cs L mem0 i)
      (.seq (.assign 63 (.load (.bin .add (.reg 67) (.reg 69)))) delOutputWalk)
      (normalPost fun s => DelOutputConnInv x b base src cs L mem0 (i + 1)
        { s with regs := Function.update s.regs 69 (i + 1) } ∧ s.regs 69 = i)
      (fun _ => delOutputConnCost x cs i) := by
  let c := cs[i]
  let seen := x.walkPassVerts (cs.take i)
  let y := x.afterReports seen
  let vs := (x.H.A.C.walk c).verts
  let next := x.walkPassVerts (cs.take (i + 1))
  let out := L ++ x.delReports seen
  let out' := L ++ x.delReports next
  have hcm : c ∈ cs := List.getElem_mem hi
  have hvisit : next = seen ++ vs := by
    simp only [next, HierConcrete.walkPassVerts, List.take_succ_eq_append_getElem hi,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl
  have hstate : x.afterReports next = y.afterReports vs := by
    rw [hvisit, x.afterReports_append]
  have hout : out' = out ++ y.delReports vs := by
    simp only [out', hvisit, x.delReports_append, ← List.append_assoc]
    rfl
  have hv' : ∀ j, ∀ v ∈ x.walkPassVerts (cs.take j), v < x.n := by
    intro j v hm
    obtain ⟨d, hd, hvd⟩ := List.mem_flatMap.mp hm
    exact hv d (List.mem_of_mem_take hd) v hvd
  have hcap : out.length ≤ L.length + x.n := by
    simp only [out, List.length_append]
    exact Nat.add_le_add_left (x.delReports_length_le (hv' i)) _
  have hcap' : out'.length ≤ L.length + x.n := by
    simp only [out', List.length_append]
    exact Nat.add_le_add_left (x.delReports_length_le (hv' (i + 1))) _
  have hlen : y.encode.length = x.encode.length := x.length_encode_withVhat _
  have hblk : b + y.encode.length ≤ base := (congrArg (b + ·) hlen).le.trans hb
  have hfit : base + out.length + y.n + 1 < 2 ^ w := by
    change base + out.length + x.n + 1 < 2 ^ w
    omega
  intro s ω hs
  obtain ⟨h0, h58, h59, h67, h68, h69, hB, hL, hSrc, hf⟩ := hs
  let R := Function.update s.regs 63 c
  let M := fun mem => ListAt mem b y.encode ∧ ListAt mem base out ∧ mem = s.mem
  have hread : Triple w p (fun t => t.regs = s.regs ∧ M t.mem)
      (.assign 63 (.load (.bin .add (.reg 67) (.reg 69))))
      (normalPost fun t => t.regs = R ∧ M t.mem) (fun _ => 5) := by
    exact triple_assign_exact fun t hr hm =>
      Expr.eval_load_of_eq (Expr.eval_add
        (Expr.eval_reg_of_eq (hr ▸ h67)) (Expr.eval_reg_of_eq (hr ▸ h69)) (by omega))
        (by rw [hm.2.2]; exact hSrc i hi)
  have H := delOutputWalk_triple (w := w) (p := p) (mem0 := s.mem) (R := R)
    (L := out) (c := c) y (by simpa [R] using h0) (by simpa [R] using h58)
    (by change (Function.update s.regs 63 c) 59 = out.length; exact h59) (by simp [R]) hblk hfit (hc c hcm) (hv c hcm)
  have HF := Triple.regs_frame delOutputWalk_writesBelow H s.regs
  have HT := Triple.seq_normal_const hread
    (HF.weaken_pre (fun t ht => ⟨ht, fun j hj => by rw [ht.1]; simp [R,
      Function.update_of_ne (show j ≠ 63 by omega)]⟩))
  obtain ⟨o, s', k, hrun, hp, hk⟩ := HT s ω ⟨rfl, hB, hL, rfl⟩
  cases o <;> try exact False.elim hp.1
  obtain ⟨⟨h0', h58', h59', hB', hL', hf'⟩, hregs⟩ := hp
  change s'.regs 59 = (out ++ y.delReports vs).length at h59'
  rw [← hout] at h59'
  change ∀ j, (j < b ∨ b + y.encode.length ≤ j) →
    (j < base + out.length ∨ base + (out ++ y.delReports vs).length ≤ j) →
      s'.mem j = s.mem j at hf'
  rw [hlen, ← hout] at hf'
  have hle : out.length ≤ out'.length := by rw [hout]; simp
  change ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
    (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j at hf
  refine ⟨_, s', k, hrun, ?_, ?_⟩
  · have hB'' : ListAt s'.mem b (x.afterReports next).encode := by rw [hstate]; exact hB'
    have hL'' : ListAt s'.mem base out' := by rw [hout]; exact hL'
    have hSrc' : ListAt s'.mem src cs := by
      refine listAt_congr (fun j _ => ?_) hSrc
      exact (hf' (src + j) (Or.inr (by omega)) (Or.inr (by omega))).symm
    have hfr : ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
        (j < base + L.length ∨ base + out'.length ≤ j) → s'.mem j = mem0 j := by
      intro j hj hs'
      have hpre : L.length ≤ out.length := by simp [out]
      exact (hf' j hj (by omega)).trans (hf j hj (by omega))
    change DelOutputConnInv x b base src cs L mem0 (i + 1) _ ∧ _
    refine ⟨⟨by simpa using h0', by simpa using h58',
      by simpa only [Function.update_of_ne (by decide : 59 ≠ 69)] using h59',
      by simpa using (hregs 67 (by decide)).trans h67,
      by simpa using (hregs 68 (by decide)).trans h68, by simp, hB'', hL'', hSrc', hfr⟩,
      (hregs 69 (by decide)).trans h69⟩
  · unfold delOutputConnCost
    rw [List.getD_eq_getElem _ _ hi]
    dsimp only
    change k ≤ 5 + (200 * (x.H.A.C.walk cs[i]).verts.length + 100) + 1 at hk
    omega

/-- Scan all connector walks and append their first reports to the output. -/
theorem delOutputConns_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base src : ℕ} {cs L : List ℕ} {mem0 R : ℕ → ℕ}
    (h0 : R 0 = b) (h58 : R 58 = base) (h59 : R 59 = L.length)
    (h67 : R 67 = src) (h68 : R 68 = cs.length)
    (hb : b + x.encode.length ≤ base) (hsep : base + L.length + x.n ≤ src)
    (hw : base + L.length + 2 * x.n + 1 < 2 ^ w) (hsw : src + cs.length < 2 ^ w)
    (hc : ∀ c ∈ cs, c < x.H.A.C.numConn)
    (hv : ∀ c ∈ cs, ∀ v ∈ (x.H.A.C.walk c).verts, v < x.n) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ ListAt s.mem base L ∧
      ListAt s.mem src cs ∧ s.mem = mem0) delOutputConns
      (normalPost fun s =>
        let vs := x.walkPassVerts cs
        let out := L ++ x.delReports vs
        s.regs 0 = b ∧ s.regs 58 = base ∧ s.regs 59 = out.length ∧
        ListAt s.mem b (x.afterReports vs).encode ∧ ListAt s.mem base out ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j)
      (fun _ => rangeCost (delOutputConnCost x cs) 0 cs.length + cs.length * 9 + 7) := by
  have hone : 1 < 2 ^ w := by omega
  have H := Triple.forRange_le (w := w) (p := p) (r := 69) (lo := .const 0)
    (hi := .reg 68) (Inv := DelOutputConnInv x b base src cs L mem0)
    (delOutputConnCost x cs) 0 cs.length (Nat.zero_le _) hone (fun _ => by omega)
    (P := fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ ListAt s.mem base L ∧
      ListAt s.mem src cs ∧ s.mem = mem0)
    (fun s hs => ⟨Expr.eval_const (by omega), ?_⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.2.2.1)
    (fun _ _ hi => delOutputConnBody_triple x hb hsep hw hsw hc hv hi)
  · refine (H.strengthen_post fun o s h => ?_).mono_cost (fun _ _ => by simp [Expr.size])
    cases o <;> try contradiction
    change DelOutputConnInv x b base src cs L mem0 cs.length s at h
    simp only [DelOutputConnInv, List.take_length] at h
    obtain ⟨h0', h58', h59', _, _, _, hB, hL, _, hf⟩ := h
    exact ⟨h0', h58', h59', hB, hL, hf⟩
  · obtain ⟨hr, hB, hL, hSrc, hm⟩ := hs
    simp only [DelOutputConnInv, List.take_zero]
    have hn : x.walkPassVerts [] = [] := rfl
    have ho : x.delReports [] = [] := rfl
    rw [hn, ho, List.append_nil, x.afterReports_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_, by simp, hB, hL, hSrc, fun j _ _ => congrFun hm j⟩
    · simpa [hr] using h0
    · simpa [hr] using h58
    · simpa [hr] using h59
    · simpa [hr] using h67
    · simpa [hr] using h68

end MinCostFlow.HierPaths

end
