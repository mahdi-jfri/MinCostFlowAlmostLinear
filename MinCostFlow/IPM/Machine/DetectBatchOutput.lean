module

public import MinCostFlow.IPM.Machine.DetectBatchProgram

/-!
# Word bounds and exact extent of the prepared Update batch

The shared source graph supplies word-sized vertex and edge counts.
Each reported name denotes an existing edge, so the serialized deletion
and insertion words fit too. The fresh output extent bounds its count
header. These are the remaining batch premises of the machine Update.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Decode the actual batch writer's result, including every batch word
bound required by Update, without assuming a separate encoded-batch
oracle. The primitive update count is twice the Detect set size. -/
theorem detectBatch_output {w source report heap v : ℕ} {I : Instance}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hpre : (detectBatchContract w I S).pre [source,report,heap] mem)
    (hout : (detectBatchContract w I S).post [source,report,heap] mem v mem')
    (hvWord : v<2^w) :
    ∃ es : List ℕ,es.Nodup ∧ es.toFinset=S ∧ es.length=S.card ∧
      BatchAt mem' heap (refreshEdges (namedInstance I) es) ∧
      RefreshBatch (namedInstance I) (refreshEdges (namedInstance I) es) ∧
      (∀ z∈batchWords (refreshEdges (namedInstance I) es),z<2^w) ∧
      (batchWords (refreshEdges (namedInstance I) es)).length=1+6*S.card ∧
      (refreshEdges (namedInstance I) es).length=2*S.card ∧ heap+1+6*S.card=v := by
  obtain ⟨⟨source',report',heap',heq,hI,_,_,hsubset,_,_,hinput⟩,_,_⟩ := hpre
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  have hnWord : I.n<2^w := hinput I.n (by simp [zeroLowerWords])
  have hmWord : I.m<2^w := hinput I.m (by simp [zeroLowerWords])
  obtain ⟨⟨_,_,_,_,es,hnd,hset,hbatch,hrefresh⟩,hv⟩ := hout
  change v=heap+(1+6*S.card) at hv
  have hlen : es.length=S.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
  have hes (e : ℕ) (he : e∈es) : e<I.m := by
    apply Finset.mem_range.mp
    apply hsubset
    rw [← hset]
    exact List.mem_toFinset.mpr he
  have hheader : 2*es.length<2^w := by omega
  have hwords : ∀ z∈batchWords (refreshEdges (namedInstance I) es),z<2^w := by
    rw [batchWords_refreshEdges]
    intro z hz
    simp only [List.mem_cons,List.mem_flatMap] at hz
    rcases hz with rfl | ⟨e,he,hz⟩
    · exact hheader
    · have heM := hes e he
      have heWord := heM.trans hmWord
      have hends := hI.1 (I.edge ⟨e,heM⟩) (List.getElem_mem heM)
      have htWord := hends.1.trans hnWord
      have hhWord := hends.2.trans hnWord
      simp only [namedInstance,heM,↓reduceDIte] at hz
      simp only [List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hsize : (batchWords (refreshEdges (namedInstance I) es)).length=1+6*S.card := by
    rw [batchWords_refreshEdges]
    simp only [List.length_cons,List.length_flatMap,List.length_cons,List.length_nil]
    simp [hlen]
    omega
  have hupdates : (refreshEdges (namedInstance I) es).length=2*S.card := by
    have hh := congrArg List.head? (batchWords_refreshEdges (namedInstance I) es)
    change some (refreshEdges (namedInstance I) es).length=some (2*es.length) at hh
    exact (Option.some.inj hh).trans (congrArg (2*·) hlen)
  exact ⟨es,hnd,hset,hlen,hbatch,hrefresh,hwords,hsize,hupdates,by omega⟩

end MinCostFlow.IPM.Machine
