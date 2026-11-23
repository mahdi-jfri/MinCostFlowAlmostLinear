module

public import MinCostFlow.HierPaths.BuildProgCoreCall

/-!
# Reading the tag of a certified core reply

Each call returns a cut or an expander from the core contract. The tag is
read only after the reply has been written.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Read the tag of whichever certified answer the core writes. -/
theorem buildCoreChoice_triple
    {w K M r q g h saved : ℕ} {G : Graph} {p : Program} {f : ℕ}
    {coreCost : ℕ → Graph → ℕ} {sC : ℕ → ℕ} {mem : ℕ → ℕ}
    (hCore : ProvidesCore w K M r coreCost sC p f)
    (hPre : (CoreProcContract w K M r coreCost sC q G).pre [q,g,M,r,h] mem)
    (hWords : ∀ i ∈ [q,g,M,r,h], i < 2^w) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = q ∧ st.regs 1 = g ∧
        st.regs 2 = M ∧ st.regs 3 = r ∧ st.regs 4 = h ∧ st.regs 12 = saved)
      (buildCoreCall f)
      (normalPost fun st => st.regs 0 = q ∧ st.regs 1 = g ∧ st.regs 2 = M ∧
        st.regs 3 = r ∧ st.regs 4 = h ∧ st.regs 12 = saved ∧
        h ≤ st.regs 5 ∧ st.regs 5 ≤ h+sC G.encode.length ∧
        (∀ a<h, st.mem a = mem a) ∧ ZeroFrom st.mem (st.regs 5) ∧
        ∃ res, CoreOutcomeSpec ParamConfig.default M q G res ∧
          ListAt st.mem h (coreResultWords res) ∧ h + (coreResultWords res).length ≤ st.regs 5 ∧
          st.regs 6 = coreTag res)
      (fun _ => K * (coreCost q G + G.encode.length + 1) + 12) := by
  intro st ω ⟨hm,hq,hg,hM,hr,hh,hs⟩
  have hSpace : h + sC G.encode.length < 2^w := hPre.2.2
  refine runs_start_le ?_
  unfold buildCoreCall
  refine runs_seq_call_le (hCore q G) (vs := [q,g,M,r,h])
    (by simp [evalArgs,Expr.eval,hq,hg,hM,hr,hh]) hWords (hm ▸ hPre) ?_
  intro v after pos' hPost
  obtain ⟨⟨hLo,hHi,hBelow,hZero,_⟩,_,_,res,he,hAt,hv,hSpec⟩ := hPost
  simp only [List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl⟩ := he
  change h ≤ v at hLo
  change v ≤ h + sC G.encode.length at hHi
  have hvw : v < 2^w := hHi.trans_lt hSpace
  have hLenW : h + (coreResultWords res).length < 2^w := lt_of_le_of_lt hv hvw
  refine runs_assign_le (eval_coreTag (by simpa using hh) hAt hLenW) ?_ ?_
  · refine ⟨by simpa using hq,by simpa using hg,by simpa using hM,by simpa using hr,
        by simpa using hh,by simpa using hs,?_,?_,?_,?_,res,hSpec,hAt,?_,by simp⟩
    · simpa using hLo
    · simpa using hHi
    · intro a ha
      exact (hBelow a ha).trans (congrFun hm a)
    · simpa using hZero
    · simpa using hv
  · simp [CoreProcContract,heapContract,argsSize,Expr.size]; omega

end MinCostFlow.HierPaths
